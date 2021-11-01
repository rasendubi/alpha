use std::error::Error;

use inkwell::OptimizationLevel;
use inkwell::context::Context;
use inkwell::passes::PassManager;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue};
use inkwell::module::Module;

use crate::symbol::SymbolInterner;
use crate::env::Env;
use crate::parser::Parser;
use crate::compiler::Compiler;
use crate::sexp::SExp;
use crate::exp;
use crate::exp::{Exp, lower_sexp};

pub struct ExecutionSession<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    fpm: PassManager<FunctionValue<'ctx>>,
    interner: SymbolInterner,
    global_env: Env<'ctx, BasicValueEnum<'ctx>>,
}

impl<'ctx> ExecutionSession<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        let module = context.create_module("user");

        let fpm = PassManager::create(&module);
        fpm.add_cfg_simplification_pass();
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_basic_alias_analysis_pass();
        fpm.initialize();

        let mut interner = SymbolInterner::new();
        let mut global_env = Env::new(None);

        let f64_t = context.f64_type();
        let f64_mul_ = module.add_function("f64_mul", f64_t.fn_type(&[f64_t.into(), f64_t.into()], false), None);
        let f64_println_ = module.add_function("f64_println", f64_t.fn_type(&[f64_t.into()], false), None);
        global_env.insert(interner.intern("f64_mul"), f64_mul_.as_global_value().as_basic_value_enum());
        global_env.insert(interner.intern("f64_println"), f64_println_.as_global_value().as_basic_value_enum());

        ExecutionSession {
            context,
            module,
            fpm,
            interner,
            global_env,
        }
    }

    pub fn run_line(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        let mut parser = Parser::new(line);
        while parser.has_input() {
            self.run_sexp(&parser.parse()?)?;
        }

        Ok(())
    }

    fn run_sexp(&mut self, sexp: &SExp) -> Result<(), Box<dyn Error>> {
        let exp = lower_sexp(&sexp, &mut self.interner)?;
        println!("lowered: {:?}", &exp);

        let (def, is_anonymous) = match exp {
            Exp::Type(_) => return Ok(()),
            Exp::Function(f) => (f, false),
            e => (
                exp::Function {
                    prototype: exp::FunctionPrototype {
                        name: self.interner.intern("*anonymous*"),
                        params: vec![],
                    },
                    body: Some(Box::new(e)),
                },
                true
            ),
        };

        let f = Compiler::compile(&self.interner, &self.context, &self.module, &self.fpm, &self.global_env, &def)?;
        f.print_to_stderr();

        let name = f.get_name().to_string_lossy();
        if is_anonymous {
            unsafe {
                let ee = self.module.create_jit_execution_engine(OptimizationLevel::None).unwrap();
                // ee.add_global_mapping(&f64_mul_, f64_mul as usize);
                // ee.add_global_mapping(&f64_println_, f64_println as usize);
                let fun = ee.get_function::<unsafe extern "C" fn() -> f64>(&name)?;
                println!("{}", fun.call());
                ee.remove_module(&self.module).unwrap();
                f.delete();
            }
        } else {
            self.global_env.insert(def.prototype.name, f.as_global_value().as_basic_value_enum());
        }

        Ok(())
    }
}
