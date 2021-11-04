mod symbol;
mod sexp;
mod exp;
mod parser;
mod lexer;
mod compiler;
mod env;
mod execution_session;
mod gc;

use llvm::context::Context;

use crate::execution_session::ExecutionSession;

const HISTORY_FILE: &str = "history.txt";

fn main() {
    let mut rl = rustyline::Editor::<()>::new();
    let _ = rl.load_history(HISTORY_FILE);

    let context = Context::new();
    let mut es = ExecutionSession::new(&context);

    let mut run_line = |line: &str| {
        match es.run_line(line) {
            Ok(()) => {},
            Err(err) => println!("Error: {}", err),
        }
    };

    loop {
        match rl.readline("user> ") {
            Err(_) => break,
            Ok(line) => run_line(&line),
        }
    }
    rl.save_history(HISTORY_FILE).unwrap();
}
