mod symbol;
mod sexp;
mod exp;
mod parser;
mod lexer;
mod compiler;
mod env;
mod execution_session;

use inkwell::context::Context;

use crate::execution_session::ExecutionSession;

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
    let mut es = ExecutionSession::new(&context);

    // poor man's standard library
    es.run_line("type i64 = integer(64)");
    es.run_line("type f64 = float(64)");

    loop {
        let mline = rl.readline("user> ");
        match mline {
            Err(_x) => {
                break
            }
            Ok(line) => {
                es.run_line(&line);
            }
        }

        // println!("\nModule:");
        // module.print_to_stderr();
    }
    rl.save_history(HISTORY_FILE).unwrap();
}
