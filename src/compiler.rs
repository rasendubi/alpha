use std::convert::TryFrom;

use inkwell::context::Context;
use inkwell::builder::Builder;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, CallableValue};

use crate::parser::Expr;
use crate::env::Env;

pub struct Compiler<'a, 'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    global_env: &'a Env<'a, BasicValueEnum<'ctx>>
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    pub fn compile(
        context: &'ctx Context,
        module: &'a Module<'ctx>,
        pass_manager: &'a PassManager<FunctionValue<'ctx>>,
        env: &'a Env<'a, BasicValueEnum<'ctx>>,
        expr: &Expr
    ) -> Result<FunctionValue<'ctx>, &'static str> {
        let mut compiler = Compiler {
            context,
            builder: context.create_builder(),
            fpm: pass_manager,
            module,
            global_env: env,
        };

        match expr {
            Expr::List(v) if v.get(0) == Some(&Expr::Symbol("fn".to_string())) => {
                compiler.compile_fn(expr)
            }
            _ => {
                compiler.compile_anonymous_fn(expr)
            }
        }
    }

    fn compile_fn(&mut self, expr: &Expr) -> Result<FunctionValue<'ctx>, &'static str> {
        let v = expr.as_list().expect("compile_fn called with non-list");

        let proto = v.get(1).ok_or("function prototype is missing")?;
        let (function, env) = self.compile_prototype(self.global_env, proto)?;

        let body_expr = v.get(2);
        if body_expr.is_none() {
            return Ok(function);
        }

        let body_expr = body_expr.unwrap();

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let body = self.compile_expr(&env, body_expr).map_err(|err| {
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
            Err("Invalid generated function.")
        }
    }

    fn compile_anonymous_fn(&mut self, expr: &Expr) -> Result<FunctionValue<'ctx>, &'static str> {
        let expr = Expr::List(vec![Expr::Symbol("fn".into()),
                                   Expr::List(vec![Expr::Symbol("call".into()),
                                                   Expr::Symbol("*anonymous*".into())]),
                                   (*expr).clone()
        ]);
        self.compile_fn(&expr)
    }

    // expects (:call function_name param1 param2 …)
    fn compile_prototype<'e>(
        &mut self,
        env: &'e Env<'e, BasicValueEnum<'ctx>>,
        expr: &Expr
    ) -> Result<(FunctionValue<'ctx>, Env<'e, BasicValueEnum<'ctx>>), &'static str> {
        let v = expr.as_list().ok_or("compile_prototype is called with non-list")?;
        let name = v[1].as_symbol().ok_or("function name is not a symbol")?;

        let ret_type = self.context.f64_type();
        let args_types = std::iter::repeat(ret_type).take(v.len() - 2).map(|f| f.into()).collect::<Vec<BasicTypeEnum>>();
        let fn_type = self.context.f64_type().fn_type(&args_types, false);
        let fn_val = self.module.add_function(&name, fn_type, None);

        let mut env = Env::new(Some(env));
        for (i, param) in fn_val.get_param_iter().enumerate() {
            let param_name = v[i + 2].as_symbol().ok_or("param name is not a symbol")?;
            let value = param.into_float_value();
            value.set_name(&param_name);
            env.insert(&param_name, value.as_basic_value_enum());
        }

        Ok((fn_val, env))
    }

    fn compile_expr(
        &mut self,
        env: &Env<BasicValueEnum<'ctx>>,
        expr: &Expr
    ) -> Result<BasicValueEnum<'ctx>, &'static str> {
        match expr {
            Expr::Symbol(s) => {
                match env.lookup(&s) {
                    Some(value) => Ok(value.as_basic_value_enum()),
                    None => {
                        return Err("unable to find a binding")
                    }
                }
            }
            Expr::Number(s) => {
                Ok(self.context.f64_type().const_float(s.parse().unwrap()).as_basic_value_enum())
            }
            Expr::List(v) => {
                match v[0].as_symbol().unwrap() {
                    "call" => {
                        if let Some(s) = v[1].as_symbol() {
                            if s == "+" {
                                let mut acc = self.context.f64_type().const_float(0.0);
                                for arg in &v[2..] {
                                    let arg = self.compile_expr(env, arg)?;
                                    acc = self.builder.build_float_add(acc, arg.into_float_value(), "add");
                                }
                                return Ok(acc.into());
                            }
                        };

                        let f = CallableValue::try_from(self.compile_expr(env, &v[1])?.into_pointer_value())
                            .map_err(|_| "unable to call function")?;
                        let mut args = Vec::new();
                        for arg in &v[2..] {
                            args.push(self.compile_expr(env, arg)?);
                        }

                        match self.builder.build_call(f, &args, "tmp").try_as_basic_value().left() {
                            Some(value) => Ok(value),
                            None => Err("Invalid call produced.")
                        }
                    }
                    _ => {
                        Err("unknown AST list type")
                    }
                }
            }
        }
    }
}
