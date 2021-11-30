use tracing::error;

use llvm::builder::Builder;
use llvm::context::Context;
use llvm::module::Module;
use llvm::types::AddressSpace;
use llvm::values::Value;

use anyhow::{anyhow, bail, Result};

use crate::ast::exp::{self, Exp};
use crate::ast::types::{TypeDef, TypeDescriptor};
use crate::env::Env;
use crate::execution_session::EnvValue;
use crate::symbol;
use crate::types::*;

use std::mem::size_of;

pub struct Compiler<'a, 'ctx> {
    context: &'ctx Context,
    module: &'a Module,
    prologue_builder: Builder,
    builder: Builder,
    epilogue_builder: Builder,
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
    /// declare %Any* @dispatch(%SVec* %args)
    ///
    /// declare %Any* @mk_str(i8* %ptr, i64 len)
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
    ) -> Result<Value> {
        let mut compiler = Compiler {
            context,
            prologue_builder: context.create_builder(),
            builder: context.create_builder(),
            epilogue_builder: context.create_builder(),
            module,
            global_env: env,
        };

        compiler.compile_fn(f)
    }

    pub fn compile_constructor(
        context: &'ctx Context,
        module: &'a Module,
        env: &'a Env<'a, EnvValue>,
        def: &TypeDef,
    ) -> Result<Value> {
        let mut compiler = Compiler {
            context,
            prologue_builder: context.create_builder(),
            builder: context.create_builder(),
            epilogue_builder: context.create_builder(),
            module,
            global_env: env,
        };

        compiler.compile_constr(def)
    }

    pub fn compile_accessor(
        context: &'ctx Context,
        module: &'a Module,
        env: &'a Env<'a, EnvValue>,
        def: &TypeDef,
        i: usize,
        name: &str,
    ) -> Result<Value> {
        let mut compiler = Compiler {
            context,
            prologue_builder: context.create_builder(),
            builder: context.create_builder(),
            epilogue_builder: context.create_builder(),
            module,
            global_env: env,
        };

        compiler.compile_access(def, i, name)
    }

    fn get_llvm_gcroot(&mut self) -> Value {
        self.module.get_function("llvm.gcroot").unwrap_or_else(|| {
            let ptr_t = self.context.int_type(8).pointer_type(AddressSpace::Generic);
            self.module.add_function(
                "llvm.gcroot",
                self.context
                    .void_type()
                    .function_type(&[ptr_t.pointer_type(AddressSpace::Generic), ptr_t], false),
            )
        })
    }

    fn build_gcroot(&mut self, name: &str) -> Value {
        let any_ptr_t = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);

        let alloca = self.prologue_builder.build_alloca(any_ptr_t, name);

        let ptr_t = self
            .context
            .int_type(8)
            .pointer_type(AddressSpace::Generic)
            .pointer_type(AddressSpace::Generic);
        let gcroot =
            self.prologue_builder
                .build_pointer_cast(alloca, ptr_t, &format!("{}.gcroot", name));

        let llvm_gcroot = self.get_llvm_gcroot();
        self.prologue_builder.build_call(
            llvm_gcroot,
            &[
                gcroot,
                self.context
                    .int_type(8)
                    .pointer_type(AddressSpace::Generic)
                    .const_null(),
            ],
            "",
        );

        alloca
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

    fn compile_constr(&mut self, def: &TypeDef) -> Result<Value> {
        let fields = match &def.typedef {
            TypeDescriptor::Struct { fields } => fields,
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
        self.enter_function(function);
        let env = self.build_fn_prologue(self.global_env, &proto, function)?;

        let t = self.context.get_named_struct(def.name.as_str()).unwrap();
        let res = self.build_dyn_allocate(t.size(), "result");

        let ty = self.compile_exp(self.global_env, &Exp::Symbol(def.name))?;
        let ty = self.load_value(ty);
        self.build_set_typetag(res, ty);

        let result_as_t = self.builder.build_pointer_cast(
            res,
            t.pointer_type(AddressSpace::Generic),
            "result_as_t",
        );

        for (i, (name, typ)) in fields.iter().enumerate() {
            let value = self.compile_exp(&env, &Exp::Symbol(*name))?;
            let value = self.load_value(value);
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

        self.epilogue_builder.build_ret(res);

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

    fn compile_access(&mut self, def: &TypeDef, i: usize, name: &str) -> Result<Value> {
        let fields = match &def.typedef {
            TypeDescriptor::Struct { fields } => fields,
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
        self.enter_function(function);
        let env = self.build_fn_prologue(self.global_env, &proto, function)?;

        let t = self.context.get_named_struct(def.name.as_str()).unwrap();

        let this = self.compile_exp(&env, &Exp::Symbol(this_s))?;
        let field = if typ.typedef.is_inlinable() {
            // box value
            let field_t = self.context.get_named_struct(typ.name.as_str()).unwrap();
            let res = self.build_dyn_allocate(field_t.size(), "result"); // safepoint!
            let field_type = self.compile_exp(self.global_env, &Exp::Symbol(typ.name))?; // this must not allocate
            let field_type = self.load_value(field_type);

            self.build_set_typetag(res, field_type);
            let res_as_t = self.builder.build_pointer_cast(
                res,
                field_t.pointer_type(AddressSpace::Generic),
                "res_as_t",
            );

            let this = self.load_value(this);
            let this_as_t = self.builder.build_pointer_cast(
                this,
                t.pointer_type(AddressSpace::Generic),
                "this_as_t",
            );
            let field_ptr = self
                .builder
                .build_struct_gep(this_as_t, i as u32, "field_ptr");
            let field = self.builder.build_load(field_ptr, "field");

            self.builder.build_store(res_as_t, field);
            res
        } else {
            let this = self.load_value(this);
            let this_as_t = self.builder.build_pointer_cast(
                this,
                t.pointer_type(AddressSpace::Generic),
                "this_as_t",
            );
            let field_ptr = self
                .builder
                .build_struct_gep(this_as_t, i as u32, "field_ptr");
            self.builder.build_load(field_ptr, "field")
        };

        self.epilogue_builder.build_ret(field);

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

    fn compile_fn(&mut self, f: &exp::Function) -> Result<Value> {
        let function = self.compile_prototype(&f.prototype)?;

        let body_exp = match f.body.as_ref() {
            None => return Ok(function),
            Some(body) => body,
        };

        self.enter_function(function);

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
        let body = self.load_value(body);
        let result = self
            .epilogue_builder
            .build_pointer_cast(body, any_ptr, "result");
        self.epilogue_builder.build_ret(result);

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

    fn compile_prototype<'e>(&mut self, proto: &exp::FunctionPrototype) -> Result<Value> {
        let name = proto.name.as_str();

        let ptr_t = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);

        let fn_t = ptr_t.function_type(&[ptr_t], false);

        let fn_val = self.module.add_function(&name, fn_t);
        fn_val.set_gc("shadow-stack");

        Ok(fn_val)
    }

    fn enter_function(&mut self, f: Value) {
        let prologue = self.context.append_basic_block(f, "prologue");
        let main = self.context.append_basic_block(f, "main");
        let epilogue = self.context.append_basic_block(f, "epilogue");

        self.prologue_builder.position_at_end(prologue);
        let br_main = self.prologue_builder.build_br(main);
        self.prologue_builder.position_before(br_main);

        self.builder.position_at_end(main);
        let br_epi = self.builder.build_br(epilogue);
        self.builder.position_before(br_epi);

        self.epilogue_builder.position_at_end(epilogue);
    }

    fn build_fn_prologue<'e>(
        &mut self,
        env: &'e Env<'e, EnvValue>,
        proto: &exp::FunctionPrototype,
        fn_val: Value,
    ) -> Result<Env<'e, EnvValue>> {
        let mut params = fn_val.get_param_iter();
        let args = params.next().unwrap();

        args.set_name("args");

        let any_ptr_t = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let i64_t = self.context.int_type(64);

        let args = self.prologue_builder.build_pointer_cast(
            args,
            any_ptr_t.pointer_type(AddressSpace::Generic),
            "args.elements.-1",
        );

        let mut env = Env::new(Some(env));
        for (i, param) in proto.params.iter().enumerate() {
            let param_symbol = param.name;
            let param_name = param_symbol.as_str();
            let p = self.prologue_builder.build_gep(
                args,
                &[i64_t.const_int((i + 2) as u64, false)],
                &format!("args.{}", i + 1),
            );
            let p = self
                .prologue_builder
                .build_load(p, &format!("{}.in", param_name));
            let gcroot = self.build_gcroot(param_name);
            self.prologue_builder.build_store(gcroot, p);
            env.insert(param_symbol, EnvValue::Local(gcroot));
        }

        Ok(env)
    }

    fn load_value(&mut self, value: Value) -> Value {
        let ptr = self.builder.build_pointer_cast(
            value,
            self.context
                .get_named_struct("Any")
                .unwrap()
                .pointer_type(AddressSpace::Generic)
                .pointer_type(AddressSpace::Generic),
            "",
        );
        self.builder.build_load(ptr, "")
    }

    fn compile_exp(&mut self, env: &Env<EnvValue>, exp: &Exp) -> Result<Value> {
        let result = match exp {
            Exp::Type(_) => panic!("compile_exp is called with Exp::Type"),
            Exp::Symbol(s) => match env.lookup(*s) {
                Some(EnvValue::Local(value)) => *value,
                Some(EnvValue::Global(name)) => {
                    let global = self.module.get_global(name).unwrap();
                    global
                    // let value = self.builder.build_load(global, name);
                    // self.builder.build_pointer_cast(
                    //     value,
                    //     self.context
                    //         .get_named_struct("Any")
                    //         .unwrap()
                    //         .pointer_type(AddressSpace::Generic),
                    //     &(name.to_string() + "_any"),
                    // )
                }
                None => {
                    bail!("unable to find binding for {}", (*s).as_str());
                }
            },
            Exp::Float(n) => {
                let place = self.build_gcroot("fptr_place");
                let ptr = self.build_allocate(8, "fptr_any");
                self.builder.build_store(place, ptr);
                let fptr = self.builder.build_pointer_cast(
                    ptr,
                    self.context.f64_type().pointer_type(AddressSpace::Generic),
                    "fptr",
                );
                let value = self.context.f64_type().const_float(*n);
                self.builder.build_store(fptr, value);

                let f64_symbol = symbol("f64");
                let f64t = self.compile_exp(env, &Exp::Symbol(f64_symbol))?;
                let f64t = self.load_value(f64t);
                self.build_set_typetag(ptr, f64t);

                place
            }
            Exp::Integer(n) => {
                let place = self.build_gcroot("iptr_place");
                let ptr = self.build_allocate(8, "iptr_any");
                self.builder.build_store(place, ptr);
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
                let i64t = self.load_value(i64t);
                self.build_set_typetag(ptr, i64t);

                place
            }
            Exp::String(s) => {
                let place = self.build_gcroot("str_root");

                let len = s.len();
                let s = self.builder.build_global_string_ptr(s, "str_literal");
                let mk_str = self.module.get_function("mk_str").unwrap();
                let r = self.builder.build_call(
                    mk_str,
                    &[s, self.context.int_type(64).const_int(len as u64, false)],
                    "string",
                );

                self.builder.build_store(place, r);

                place
            }
            Exp::Call(call) => {
                let place = self.build_gcroot("call_root");
                let f = self.compile_exp(env, &call.fun)?;

                let mut args = Vec::new();
                for arg in &call.args {
                    args.push(self.compile_exp(env, arg)?);
                }

                let res = self.build_call(f, &args, "tmp")?;
                self.builder.build_store(place, res);

                place
            }
            Exp::Block(block) => {
                let mut result = None;
                for e in block {
                    result = Some(self.compile_exp(env, e)?);
                }

                result.ok_or_else(|| anyhow!("empty blocks are not supported yet"))?
            }
            Exp::Function(_) => {
                bail!("function definition is not expected here")
            }
        };
        Ok(result)
    }

    fn build_svec(&mut self, elements: &[Value], name: &str) -> Result<Value> {
        let i64_t = self.context.int_type(64);
        let any_ptr_t = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);

        let svec = self.build_allocate(
            (size_of::<SVec>() + size_of::<AnyPtr>() * elements.len()) as u64,
            name,
        );

        let svec_t = self.module.get_global("SVec").unwrap();
        let svec_t = self.builder.build_load(svec_t, "SVec");
        self.build_set_typetag(svec, svec_t);

        let len_ptr = self.builder.build_pointer_cast(
            svec,
            i64_t.pointer_type(AddressSpace::Generic),
            &(name.to_string() + ".len"),
        );
        self.builder
            .build_store(len_ptr, i64_t.const_int(elements.len() as u64, false));

        let elements_ptr = self.builder.build_pointer_cast(
            svec,
            any_ptr_t.pointer_type(AddressSpace::Generic),
            &(name.to_string() + ".elements"),
        );
        for (i, v) in elements.iter().enumerate() {
            let field_ptr = self.builder.build_gep(
                elements_ptr,
                &[i64_t.const_int((i + 1) as u64, false)],
                &(format!("{}.{}", name, i)),
            );
            let value = self.load_value(*v);
            self.builder.build_store(field_ptr, value);
        }

        Ok(svec)
    }

    fn build_call(&mut self, f: Value, args: &[Value], name: &str) -> Result<Value> {
        let mut actual_arguments = Vec::new();
        actual_arguments.push(f);
        actual_arguments.extend_from_slice(args);

        let svec = self.build_svec(&actual_arguments, &format!("{}.args", name))?;

        let dispatch = self.module.get_function("dispatch").unwrap();

        let result = self.builder.build_call(dispatch, &[svec], name);

        Ok(result)
    }
}
