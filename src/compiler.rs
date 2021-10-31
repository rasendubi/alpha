use std::convert::TryFrom;
use std::error::Error;

use inkwell::context::Context;
use inkwell::builder::Builder;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, CallableValue};

use simple_error::bail;

use crate::symbol::SymbolInterner;
use crate::env::Env;

use crate::exp;
use crate::exp::Exp;

pub struct Compiler<'a, 'ctx> {
    interner: &'a SymbolInterner,
    context: &'ctx Context,
    builder: Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    global_env: &'a Env<'a, BasicValueEnum<'ctx>>,
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    pub fn compile(
        interner: &'a SymbolInterner,
        context: &'ctx Context,
        module: &'a Module<'ctx>,
        pass_manager: &'a PassManager<FunctionValue<'ctx>>,
        env: &'a Env<'a, BasicValueEnum<'ctx>>,
        f: &exp::Function,
    ) -> Result<FunctionValue<'ctx>, Box<dyn Error>> {
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

    fn compile_fn(&mut self, f: &exp::Function) -> Result<FunctionValue<'ctx>, Box<dyn Error>> {
        let (function, env) = self.compile_prototype(self.global_env, &f.prototype)?;

        if f.body.is_none() {
            return Ok(function);
        }

        let body_exp = f.body.as_ref().unwrap();

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let body = self.compile_exp(&env, &body_exp).map_err(|err| {
            unsafe { function.delete() };
            err
        })?;
        self.builder.build_return(Some(&body));

        if function.verify(true) {
            self.fpm.run_on(&function);
            Ok(function)
        } else {
            unsafe {
                function.delete();
            }
            bail!("invalid generated function")
        }
    }

    // expects (:call function_name param1 param2 …)
    fn compile_prototype<'e>(
        &mut self,
        env: &'e Env<'e, BasicValueEnum<'ctx>>,
        proto: &exp::FunctionPrototype,
    ) -> Result<(FunctionValue<'ctx>, Env<'e, BasicValueEnum<'ctx>>), Box<dyn Error>> {
        let name = self.interner.resolve(proto.name).unwrap();

        let ret_type = self.context.f64_type();
        let params_types = std::iter::repeat(ret_type)
            .take(proto.params.len())
            .map(|f| f.into())
            .collect::<Vec<BasicTypeEnum>>();
        let fn_type = self.context.f64_type().fn_type(&params_types, false);
        let fn_val = self.module.add_function(&name, fn_type, None);

        let mut env = Env::new(Some(env));
        for (i, param) in fn_val.get_param_iter().enumerate() {
            let param_symbol = proto.params[i].name;
            let param_name = self.interner.resolve(param_symbol).unwrap();
            let value = param.into_float_value();
            value.set_name(&param_name);
            env.insert(param_symbol, value.as_basic_value_enum());
        }

        Ok((fn_val, env))
    }

    fn compile_exp(
        &mut self,
        env: &Env<BasicValueEnum<'ctx>>,
        exp: &Exp
    ) -> Result<BasicValueEnum<'ctx>, Box<dyn Error>> {
        let result = match exp {
            Exp::Type(_) => panic!("compile_exp() is called on Type"),
            Exp::Symbol(s) => {
                match env.lookup(*s) {
                    Some(value) => value.as_basic_value_enum(),
                    None => {
                        bail!("unable to find binding for {}", self.interner.resolve(*s).unwrap());
                    }
                }
            }
            Exp::Float(n) => {
                self.context.f64_type().const_float(*n).as_basic_value_enum()
            }
            Exp::Integer(n) => {
                self.context.i64_type().const_int(*n as u64, true).as_basic_value_enum()
            }
            Exp::Call(call) => {
                if let &Exp::Symbol(s) = &*call.fun {
                    if Some(s) == self.interner.get("+") {
                        let mut acc = self.context.f64_type().const_float(0.0);
                        if call.args.len() == 0 {
                            return Ok(acc.into());
                        }

                        acc = self.compile_exp(env, &call.args[0])?.into_float_value();
                        for arg in &call.args[1..] {
                            let arg = self.compile_exp(env, arg)?;
                            acc = self.builder.build_float_add(acc, arg.into_float_value(), "add");
                        }
                        return Ok(acc.into());
                    }
                }

                let f = CallableValue::try_from(self.compile_exp(env, &call.fun)?.into_pointer_value())
                    .map_err(|_| "unable to call function")?;
                let mut args = Vec::new();
                for arg in &call.args {
                    args.push(self.compile_exp(env, arg)?);
                }

                match self.builder.build_call(f, &args, "tmp").try_as_basic_value().left() {
                    Some(value) => value,
                    None => {
                        bail!("invalid call produced");
                    }
                }
            }
            Exp::Function(_) => {
                bail!("function definition is not expected here")
            }
        };
        Ok(result)
    }
}
