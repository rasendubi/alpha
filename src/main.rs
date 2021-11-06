mod compiler;
mod env;
mod execution_session;
mod exp;
mod gc;
mod lexer;
mod parser;
mod sexp;
mod symbol;
mod types;

use crate::execution_session::ExecutionSession;

const HISTORY_FILE: &str = "history.txt";

fn main() {
    let mut rl = rustyline::Editor::<()>::new();
    let _ = rl.load_history(HISTORY_FILE);

    let mut es = ExecutionSession::new();

    let mut run_line = |line: &str| match es.run_line(line) {
        Ok(()) => {}
        Err(err) => println!("Error: {}", err),
    };

    loop {
        match rl.readline("user> ") {
            Err(_) => break,
            Ok(line) => run_line(&line),
        }
    }
    rl.save_history(HISTORY_FILE).unwrap();
}
