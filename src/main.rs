use alpha::ExecutionSession;

use rustyline::validate::{
    MatchingBracketValidator, ValidationContext, ValidationResult, Validator,
};
use rustyline::{Editor, Result};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext) -> Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

const HISTORY_FILE: &str = "history.txt";

fn main() {
    tracing_subscriber::fmt()
        .without_time()
        .with_target(false)
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_writer(std::io::stderr)
        // disable colors for non-terminal output
        .with_ansi(atty::is(atty::Stream::Stderr))
        .init();
    alpha::init();

    let h = InputValidator {
        brackets: MatchingBracketValidator::new(),
    };
    let mut rl = Editor::<InputValidator>::new();
    rl.set_helper(Some(h));
    let _ = rl.load_history(HISTORY_FILE);

    let mut es = ExecutionSession::new();

    loop {
        match rl.readline("user> ") {
            Err(_) => break,
            Ok(line) => match es.eval(&line) {
                Ok(()) => {
                    rl.add_history_entry(line);
                }
                Err(err) => println!("Error: {}", err),
            },
        }
    }
    rl.save_history(HISTORY_FILE).unwrap();
}
