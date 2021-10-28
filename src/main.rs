mod parser;
mod lexer;

use parser::Parser;

const HISTORY_FILE: &str = "history.txt";

fn main() {
    let mut rl = rustyline::Editor::<()>::new();
    let _ = rl.load_history(HISTORY_FILE);
    loop {
        let mline = rl.readline("user> ");
        match mline {
            Ok(line) => {
                let mut parser = Parser::new(&line);
                while parser.has_input() {
                    match parser.parse() {
                        Ok(expr) => println!("{}", expr),
                        Err(e) => {
                            println!("Error: {}", e);
                            break
                        },
                    }
                }
            }
            Err(_x) => {
                break
            }
        }
    }
    rl.save_history(HISTORY_FILE).unwrap();
}
