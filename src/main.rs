use anyhow::Result;

use alpha::ExecutionSession;

use clap::Parser;
use rustyline::validate::{
    MatchingBracketValidator, ValidationContext, ValidationResult, Validator,
};
use rustyline::{Editor, Result as RustylineResult};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext) -> RustylineResult<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

const HISTORY_FILE: &str = "history.txt";

#[derive(Parser)]
#[clap(version = "0.1")]
struct Opts {
    file: Option<String>,
}

fn main() -> Result<()> {
    let opts = Opts::parse();

    tracing_subscriber::fmt()
        .without_time()
        .with_target(false)
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_writer(std::io::stderr)
        // disable colors for non-terminal output
        .with_ansi(atty::is(atty::Stream::Stderr))
        .init();
    alpha::init();

    let mut es = ExecutionSession::new();

    if let Some(file) = opts.file {
        let input = std::fs::read_to_string(file)?;
        es.eval(&input)?;
        return Ok(());
    }

    es.set_print_results(true);

    let h = InputValidator {
        brackets: MatchingBracketValidator::new(),
    };
    let mut rl = Editor::<InputValidator>::new();
    rl.set_helper(Some(h));
    let _ = rl.load_history(HISTORY_FILE);

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

    Ok(())
}
