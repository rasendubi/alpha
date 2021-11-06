use std::error::Error;

use llvm::builder::Builder;
use llvm::context::Context;
use llvm::module::Module;
use llvm::pass_manager::FunctionPassManager;
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
    fpm: &'a FunctionPassManager,
    module: &'a Module,
    global_env: &'a Env<'a, EnvValue>,
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    pub fn compile(
        interner: &'a mut SymbolInterner,
        context: &'ctx Context,
        module: &'a Module,
        pass_manager: &'a FunctionPassManager,
        env: &'a Env<'a, EnvValue>,
        f: &exp::Function,
    ) -> Result<Value, Box<dyn Error>> {
        let mut compiler = Compiler {
            interner,
            context,
            builder: context.create_builder(),
            fpm: pass_manager,
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
        let pptr = self.builder.build_pointer_cast(
            ptr,
            self.context
                .int_type(8)
                .pointer_type(AddressSpace::Generic)
                .pointer_type(AddressSpace::Generic),
            "pptr",
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
        let (function, mut env) = self.compile_prototype(self.global_env, &f.prototype)?;

        if f.body.is_none() {
            return Ok(function);
        }

        let body_exp = f.body.as_ref().unwrap();

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let body = self.compile_exp(&mut env, &body_exp).map_err(|err| {
            unsafe { function.delete_function() };
            err
        })?;
        self.builder.build_ret(body);

        if function.verify_function() {
            self.fpm.run(function);
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
        env: &'e Env<'e, EnvValue>,
        proto: &exp::FunctionPrototype,
    ) -> Result<(Value, Env<'e, EnvValue>), Box<dyn Error>> {
        let name = self.interner.resolve(proto.name).unwrap();

        let ptr_t = self.context.int_type(8).pointer_type(AddressSpace::Generic);
        let ret_type = ptr_t;
        let param_type = ptr_t;
        let params_types = std::iter::repeat(param_type)
            .take(proto.params.len())
            .collect::<Vec<_>>();
        let fn_type = ret_type.function_type(&params_types, false);
        let fn_val = self.module.add_function(&name, fn_type);

        let mut env = Env::new(Some(env));
        for (i, param) in fn_val.get_param_iter().enumerate() {
            let param_symbol = proto.params[i].name;
            let param_name = self.interner.resolve(param_symbol).unwrap();
            param.set_name(&param_name);
            env.insert(param_symbol, EnvValue::Local(param));
        }

        Ok((fn_val, env))
    }

    fn compile_exp(&mut self, env: &mut Env<EnvValue>, exp: &Exp) -> Result<Value, Box<dyn Error>> {
        let result = match exp {
            Exp::Type(_) => panic!("compile_exp is called with Exp::Type"),
            Exp::Symbol(s) => match env.lookup(*s) {
                Some(EnvValue::Local(value)) => *value,
                Some(EnvValue::Global(name)) => {
                    let global = self.module.get_global(name).unwrap();
                    self.builder.build_load(global, name)
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

                self.builder.build_call(f, &args, "tmp")
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
}
