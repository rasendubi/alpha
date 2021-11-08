use std::error::Error;

use llvm::builder::Builder;
use llvm::context::Context;
use llvm::module::Module;
use llvm::types::AddressSpace;
use llvm::values::Value;

use simple_error::{bail, simple_error};

use crate::env::Env;
use crate::symbol::SymbolInterner;

use crate::execution_session::EnvValue;
use crate::exp;
use crate::exp::Exp;

pub struct Compiler<'a, 'ctx> {
    interner: &'a mut SymbolInterner,
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
        interner: &'a mut SymbolInterner,
        context: &'ctx Context,
        module: &'a Module,
        env: &'a Env<'a, EnvValue>,
        f: &exp::Function,
    ) -> Result<Value, Box<dyn Error>> {
        let mut compiler = Compiler {
            interner,
            context,
            builder: context.create_builder(),
            module,
            global_env: env,
        };

        compiler.compile_fn(f)
    }

    fn build_allocate(&mut self, size: u64, name: &str) -> Value {
        self.builder.build_call(
            self.module.get_function("gc_allocate").unwrap(),
            &[self.context.int_type(64).const_int(size, false)],
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
            eprintln!("\ninvalid function generated:");
            self.module.dump_to_stderr();
            eprintln!();

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
        let name = self.interner.resolve(proto.name).unwrap();

        let ptr_t = self
            .context
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let i64_t = self.context.int_type(64);

        let ret_type = ptr_t;
        let params_types = vec![
            /* self: */ ptr_t,
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
        let this = params.next().unwrap();
        let n_args = params.next().unwrap();
        let args = params.next().unwrap();

        this.set_name("this");
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
            let param_name = self.interner.resolve(param_symbol).unwrap();
            let p = self
                .builder
                .build_gep(args, &[i64_t.const_int(i as u64, false)], param_name);
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
                Some(EnvValue::Function(name)) => self.module.get_function(name).unwrap(),
                None => {
                    bail!(
                        "unable to find binding for {}",
                        self.interner.resolve(*s).unwrap()
                    );
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

                let f64_symbol = self.interner.intern("f64");
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

                let i64_symbol = self.interner.intern("i64");
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

        let size = i64_t.const_int(args.len() as u64, false);
        let args_ptr = self.builder.build_array_alloca(any_ptr_t, size, "args");

        for (i, arg) in args.iter().enumerate() {
            let a_ptr =
                self.builder
                    .build_gep(args_ptr, &[i64_t.const_int(i as u64, false)], "arg_ptr");
            self.builder.build_store(a_ptr, *arg);
        }

        let dispatch = self.module.get_function("dispatch").unwrap();

        let result = self.builder.build_call(
            dispatch,
            &[
                self.builder.build_pointer_cast(f, any_ptr_t, "f_ptr"),
                size,
                args_ptr,
            ],
            name,
        );

        Ok(result)
    }
}
