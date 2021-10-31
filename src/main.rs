mod symbol;
mod sexp;
mod exp;
mod parser;
mod lexer;
mod compiler;
mod env;

use inkwell::OptimizationLevel;
use inkwell::context::Context;
use inkwell::passes::PassManager;
use inkwell::values::BasicValue;

use parser::Parser;
use compiler::Compiler;
use env::Env;
use exp::{Exp, lower_sexp};
use symbol::SymbolInterner;

const HISTORY_FILE: &str = "history.txt";

extern "C" fn f64_mul(x: f64, y: f64) -> f64 {
    x * y
}

extern "C" fn f64_println(x: f64) -> f64 {
    println!("{}", x);
    x
}

fn main() {
    let mut rl = rustyline::Editor::<()>::new();
    let _ = rl.load_history(HISTORY_FILE);

    let context = Context::create();
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
    global_env.insert(interner.get_or_intern("f64_mul"), f64_mul_.as_global_value().as_basic_value_enum());
    global_env.insert(interner.get_or_intern("f64_println"), f64_println_.as_global_value().as_basic_value_enum());

    // TODO: properly split into modules, so we do not re-create execution engine on every input
    // let ee = module.create_jit_execution_engine(OptimizationLevel::None).unwrap();

    loop {
        let mline = rl.readline("user> ");
        match mline {
            Err(_x) => {
                break
            }
            Ok(line) => {
                let mut parser = Parser::new(&line);
                while parser.has_input() {
                    match parser.parse() {
                        Err(e) => {
                            println!("Error: {}", e);
                            break
                        },
                        Ok(sexp) => {
                            match lower_sexp(&sexp, &mut interner) {
                                Err(err) => {
                                    println!("Error: {}", err);
                                }
                                Ok(exp) => {
                                    let (def, is_anonymous) = match exp {
                                        Exp::Function(f) => (f, false),
                                        e => (
                                            exp::Function {
                                                prototype: exp::FunctionPrototype {
                                                    name: interner.get_or_intern("*anonymous*"),
                                                    params: vec![],
                                                },
                                                body: Some(Box::new(e)),
                                            },
                                            true
                                        ),
                                    };

                                    match Compiler::compile(&interner, &context, &module, &fpm, &global_env, &def) {
                                        Err(err) => {
                                            println!("Error compiling function: {}", err);
                                        }
                                        Ok(f) => {
                                            f.print_to_stderr();
                                            let name = f.get_name().to_string_lossy();
                                            if is_anonymous {
                                                unsafe {
                                                    let ee = module.create_jit_execution_engine(OptimizationLevel::None).unwrap();
                                                    ee.add_global_mapping(&f64_mul_, f64_mul as usize);
                                                    ee.add_global_mapping(&f64_println_, f64_println as usize);
                                                    match ee.get_function::<unsafe extern "C" fn() -> f64>(&name) {
                                                        Ok(f) => {
                                                            println!("{}", f.call());
                                                        }
                                                        Err(err) => {
                                                            println!("Error getting function: {}", err);
                                                        }
                                                    }
                                                    ee.remove_module(&module).unwrap();
                                                    f.delete();
                                                }
                                            } else {
                                                global_env.insert(def.prototype.name, f.as_global_value().as_basic_value_enum());
                                            }
                                        }
                                    }

                                }
                            }
                        }
                    }
                }
            }
        }

        // println!("\nModule:");
        // module.print_to_stderr();
    }
    rl.save_history(HISTORY_FILE).unwrap();
}