use std::error::Error;

use log::error;

use llvm::builder::Builder;
use llvm::context::Context;
use llvm::module::Module;
use llvm::types::AddressSpace;
use llvm::values::Value;

use simple_error::{bail, simple_error};

use crate::env::Env;
use crate::execution_session::EnvValue;
use crate::exp;
use crate::exp::Exp;
use crate::symbol::symbol;
use crate::types::{AlphaType, AlphaTypeDef};

pub struct Compiler<'a, 'ctx> {
    context: &'ctx Context,
    builder: Builder,
    module: &'a Module,
    global_env: &'a Env<'a, EnvValue>,
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    /// # Pre-defined symbols
    ///
    /// The compiler assumes the following pre-defined symbols already exist in the module.
    /// ```norust
    /// %Any = type opaque
    /// %DataType = type opaque
    ///
    /// @i64 = external global %DataType*
    /// @f64 = external global %DataType*
    ///
    /// declare %Any* @gc_allocate(i64 %size)
    ///
    /// declare %Any* @dispatch(%Any* %fun, i64 %n_args, %Any** %args)
    /// ```
    ///
    /// The following symbols should be resolve-able via env:
    /// - `i64` — type for integer literals
    /// - `f64` — type for floating point literals
    pub fn compile(
        context: &'ctx Context,
        module: &'a Module,
        env: &'a Env<'a, EnvValue>,
        f: &exp::Function,
    ) -> Result<Value, Box<dyn Error>> {
        let mut compiler = Compiler {
            context,
            builder: context.create_builder(),
            module,
            global_env: env,
        };

        compiler.compile_fn(f)
    }

    pub fn compile_constructor(
        context: &'ctx Context,
        module: &'a Module,
        env: &'a Env<'a, EnvValue>,
        def: &AlphaType,
    ) -> Result<Value, Box<dyn Error>> {
        let mut compiler = Compiler {
            context,
            builder: context.create_builder(),
            module,
            global_env: env,
        };

        compiler.compile_constr(def)
    }

    pub fn compile_accessor(
        context: &'ctx Context,
        module: &'a Module,
        env: &'a Env<'a, EnvValue>,
        def: &AlphaType,
        i: usize,
        name: &str,
    ) -> Result<Value, Box<dyn Error>> {
        let mut compiler = Compiler {
            context,
            builder: context.create_builder(),
            module,
            global_env: env,
        };

        compiler.compile_access(def, i, name)
    }

    fn build_allocate(&mut self, size: u64, name: &str) -> Value {
        self.build_dyn_allocate(self.context.int_type(64).const_int(size, false), name)
    }

    fn build_dyn_allocate(&mut self, size: Value, name: &str) -> Value {
        self.builder.build_call(
            self.module.get_function("gc_allocate").unwrap(),
            &[size],
            name,
        )
    }

    fn build_set_typetag(&mut self, ptr: Value, tag: Value) {
        let datatype_ptr_t = self
            .context
            .get_named_struct("DataType")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let tag = self.builder.build_pointer_cast(tag, datatype_ptr_t, "tag");

        let pptr = self.builder.build_pointer_cast(
            ptr,
            datatype_ptr_t.pointer_type(AddressSpace::Generic),
            "as_datatype_ptr",
        );
        let typetag_ptr = self.builder.build_gep(
            pptr,
            &[self
                .context
                .int_type(64)
                .const_int((-1 as i64) as u64, true)],
            "typetag_ptr",
        );
        self.builder.build_store(typetag_ptr, tag);
    }

    fn compile_constr(&mut self, def: &AlphaType) -> Result<Value, Box<dyn Error>> {
        let fields = match &def.typedef {
            AlphaTypeDef::Struct { fields } => fields,
            _ => panic!("Compiler::compile_constr() called on non-struct"),
        };

        let proto = exp::FunctionPrototype {
            name: def.name,
            params: fields
                .iter()
                .map(|(name, typ)| exp::FunctionParameter {
                    name: *name,
                    typ: typ.name,
                })
                .collect(),
            result_type: def.name,
        };

        let function = self.compile_prototype(&proto)?;
        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);
        let env = self.build_fn_prologue(self.global_env, &proto, function)?;

        let t = self.context.get_named_struct(def.name.as_str()).unwrap();
        let res = self.build_dyn_allocate(t.size(), "result");

        let type_ = self.compile_exp(self.global_env, &Exp::Symbol(def.name))?;
        self.build_set_typetag(res, type_);

        let result_as_t = self.builder.build_pointer_cast(
            res,
            t.pointer_type(AddressSpace::Generic),
            "result_as_t",
        );

        for (i, (name, typ)) in fields.iter().enumerate() {
            let value = self.compile_exp(&env, &Exp::Symbol(*name))?;
            let value = if typ.typedef.is_inlinable() {
                let field_t = self.context.get_named_struct(typ.name.as_str()).unwrap();
                let field_as_t = self.builder.build_pointer_cast(
                    value,
                    field_t.pointer_type(AddressSpace::Generic),
                    "field_as_t",
                );
                self.builder.build_load(field_as_t, "field_value")
            } else {
                value
            };
            let field_ptr = self
                .builder
                .build_struct_gep(result_as_t, i as u32, "field_ptr");
            self.builder.build_store(field_ptr, value);
        }

        self.builder.build_ret(res);

        if function.verify_function() {
            Ok(function)
        } else {
            error!("\ninvalid constructor generated:");
            self.module.dump_to_stderr();

            unsafe {
                function.delete_function();
            }
            bail!("invalid generated function")
        }
    }

    fn compile_access(
        &mut self,
        def: &AlphaType,
        i: usize,
        name: &str,
    ) -> Result<Value, Box<dyn Error>> {
        let fields = match &def.typedef {
            AlphaTypeDef::Struct { fields } => fields,
            _ => panic!("Compiler::compile_constr() called on non-struct"),
        };

        let (_name, typ) = &fields[i];

        let this_s = symbol("this");

        let proto = exp::FunctionPrototype {
            name: symbol(name),
            params: vec![exp::FunctionParameter {
                name: this_s,
                typ: def.name,
            }],
            result_type: typ.name,
        };

        let function = self.compile_prototype(&proto)?;
        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);
        let env = self.build_fn_prologue(self.global_env, &proto, function)?;

        let t = self.context.get_named_struct(def.name.as_str()).unwrap();

        let this = self.compile_exp(&env, &Exp::Symbol(this_s))?;
        let this_as_t = self.builder.build_pointer_cast(
            this,
            t.pointer_type(AddressSpace::Generic),
            "this_as_t",
        );
        let field_ptr = self
            .builder
            .build_struct_gep(this_as_t, i as u32, "field_ptr");
        let field = self.builder.build_load(field_ptr, "field");
        let field = if typ.typedef.is_inlinable() {
            // box value
            let field_t = self.context.get_named_struct(typ.name.as_str()).unwrap();
            let res = self.build_dyn_allocate(field_t.size(), "result");
            let field_type = self.compile_exp(self.global_env, &Exp::Symbol(typ.name))?;
            self.build_set_typetag(res, field_type);
            let res_as_t = self.builder.build_pointer_cast(
                res,
                field_t.pointer_type(AddressSpace::Generic),
                "res_as_t",
            );
            self.builder.build_store(res_as_t, field);
            res
        } else {
            field
        };

        self.builder.build_ret(field);

        if function.verify_function() {
            Ok(function)
        } else {
            error!("invalid constructor generated:\n{}", self.module);

            unsafe {
                function.delete_function();
            }
            bail!("invalid generated function")
        }
    }

    fn compile_fn(&mut self, f: &exp::Function) -> Result<Value, Box<dyn Error>> {
        let function = self.compile_prototype(&f.prototype)?;

        let body_exp = match f.body.as_ref() {
            None => return Ok(function),
            Some(body) => body,
        };

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let env = self.build_fn_prologue(self.global_env, &f.prototype, function)?;

        let body = self.compile_exp(&env, &body_exp).map_err(|err| {
            unsafe { function.delete_function() };
            err
        })?;
        let any_ptr = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let result = self.builder.build_pointer_cast(body, any_ptr, "result");
        self.builder.build_ret(result);

        if function.verify_function() {
            Ok(function)
        } else {
            error!("invalid function generated:\n{}", self.module);

            unsafe {
                function.delete_function();
            }
            bail!("invalid generated function")
        }
    }

    fn compile_prototype<'e>(
        &mut self,
        proto: &exp::FunctionPrototype,
    ) -> Result<Value, Box<dyn Error>> {
        let name = proto.name.as_str();

        let ptr_t = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let i64_t = self.context.int_type(64);

        let ret_type = ptr_t;
        let params_types = vec![
            /* n_args: */ i64_t,
            /* args: */ ptr_t.pointer_type(AddressSpace::Generic),
        ];
        let fn_type = ret_type.function_type(&params_types, false);

        let fn_val = self.module.add_function(&name, fn_type);

        Ok(fn_val)
    }

    fn build_fn_prologue<'e>(
        &mut self,
        env: &'e Env<'e, EnvValue>,
        proto: &exp::FunctionPrototype,
        fn_val: Value,
    ) -> Result<Env<'e, EnvValue>, Box<dyn Error>> {
        let mut params = fn_val.get_param_iter();
        let n_args = params.next().unwrap();
        let args = params.next().unwrap();

        n_args.set_name("n_args");
        args.set_name("args");

        let any_ptr_t = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let i64_t = self.context.int_type(64);

        let args = self.builder.build_pointer_cast(
            args,
            i64_t.pointer_type(AddressSpace::Generic),
            "args_cells",
        );

        let mut env = Env::new(Some(env));
        for (i, param) in proto.params.iter().enumerate() {
            let param_symbol = param.name;
            let param_name = param_symbol.as_str();
            let p =
                self.builder
                    .build_gep(args, &[i64_t.const_int((i + 1) as u64, false)], param_name);
            let p = self.builder.build_pointer_cast(
                p,
                any_ptr_t.pointer_type(AddressSpace::Generic),
                param_name,
            );
            let p = self.builder.build_load(p, param_name);
            env.insert(param_symbol, EnvValue::Local(p));
        }

        Ok(env)
    }

    fn compile_exp(&mut self, env: &Env<EnvValue>, exp: &Exp) -> Result<Value, Box<dyn Error>> {
        let result = match exp {
            Exp::Type(_) => panic!("compile_exp is called with Exp::Type"),
            Exp::Symbol(s) => match env.lookup(*s) {
                Some(EnvValue::Local(value)) => *value,
                Some(EnvValue::Global(name)) => {
                    let global = self.module.get_global(name).unwrap();
                    let value = self.builder.build_load(global, name);
                    self.builder.build_pointer_cast(
                        value,
                        self.context
                            .get_named_struct("Any")
                            .unwrap()
                            .pointer_type(AddressSpace::Generic),
                        &(name.to_string() + "_any"),
                    )
                }
                None => {
                    bail!("unable to find binding for {}", (*s).as_str());
                }
            },
            Exp::Float(n) => {
                let ptr = self.build_allocate(8, "fptr_any");
                let fptr = self.builder.build_pointer_cast(
                    ptr,
                    self.context.f64_type().pointer_type(AddressSpace::Generic),
                    "fptr",
                );
                let value = self.context.f64_type().const_float(*n);
                self.builder.build_store(fptr, value);

                let f64_symbol = symbol("f64");
                let f64t = self.compile_exp(env, &Exp::Symbol(f64_symbol))?;
                self.build_set_typetag(ptr, f64t);

                ptr.into()
            }
            Exp::Integer(n) => {
                let ptr = self.build_allocate(8, "iptr_any");
                let iptr = self.builder.build_pointer_cast(
                    ptr,
                    self.context
                        .int_type(64)
                        .pointer_type(AddressSpace::Generic),
                    "iptr",
                );
                let value = self.context.int_type(64).const_int(*n as u64, true);
                self.builder.build_store(iptr, value);

                let i64_symbol = symbol("i64");
                let i64t = self.compile_exp(env, &Exp::Symbol(i64_symbol))?;
                self.build_set_typetag(ptr, i64t);

                ptr.into()
            }
            Exp::Call(call) => {
                let f = self.compile_exp(env, &call.fun)?;

                let mut args = Vec::new();
                for arg in &call.args {
                    args.push(self.compile_exp(env, arg)?);
                }

                self.build_call(f, &args, "tmp")?
            }
            Exp::Block(block) => {
                let mut result = None;
                for e in block {
                    result = Some(self.compile_exp(env, e)?);
                }

                result.ok_or_else(|| simple_error!("empty blocks are not supported yet"))?
            }
            Exp::Function(_) => {
                bail!("function definition is not expected here")
            }
        };
        Ok(result)
    }

    fn build_call(
        &mut self,
        f: Value,
        args: &[Value],
        name: &str,
    ) -> Result<Value, Box<dyn Error>> {
        let any_ptr_t = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let i64_t = self.context.int_type(64);

        let size = i64_t.const_int((args.len() + 1) as u64, false);
        let args_ptr = self.builder.build_array_alloca(any_ptr_t, size, "args");

        self.builder.build_store(
            self.builder
                .build_gep(args_ptr, &[i64_t.const_int(0 as u64, false)], "arg_ptr"),
            self.builder.build_pointer_cast(f, any_ptr_t, "f_ptr"),
        );

        for (i, arg) in args.iter().enumerate() {
            let a_ptr = self.builder.build_gep(
                args_ptr,
                &[i64_t.const_int((i + 1) as u64, false)],
                "arg_ptr",
            );
            self.builder.build_store(a_ptr, *arg);
        }

        let dispatch = self.module.get_function("dispatch").unwrap();

        let result = self.builder.build_call(dispatch, &[size, args_ptr], name);

        Ok(result)
    }
}
