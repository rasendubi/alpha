use logos::{Logos, Lexer};

#[derive(Logos, Debug, PartialEq)]
pub enum Token<'a> {
    #[regex(r"-?[0-9]+", slice)]
    Integer(&'a str),

    #[regex(r"-?[0-9]+\.[0-9]+", slice)]
    Float(&'a str),

    // TODO: separate (){}[],;. into a separate token class so that they are not parsed as symbol
    // lookup. : is fine as symbol?
    #[regex(r"[(){}\[\],;:.]", slice)] // single-char
    #[regex(r"[\pL_][\pL\pN_]*", slice)]
    #[regex(r"[\pS!%&*/?@-]+", slice)]
    Symbol(&'a str),

    #[regex(r#""([^"]|\\")*""#, slice)]
    String(&'a str),

    #[regex(r"'(.|\\')'", |lex| lex.slice().chars().last().unwrap() )]
    Char(char),

    #[error]
    #[regex(r"#.*\n", logos::skip)] // comments
    #[regex(r"\s+", logos::skip)] // whitespace
    Error,
}

fn slice<'a>(lex: &mut Lexer<'a, Token<'a>>) -> &'a str {
    lex.slice()
}
