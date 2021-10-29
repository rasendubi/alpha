use logos::{Logos, Lexer};

#[derive(Logos, Debug, PartialEq)]
pub enum Token<'a> {
    #[regex(r"-?[0-9]+", slice)]
    Integer(&'a str),

    #[regex(r"-?[0-9]+\.[0-9]+", slice)]
    Float(&'a str),

    #[regex(r"[(){}\[\],]", slice)]
    Punctuation(&'a str),

    #[token(":", slice)]
    #[token(".", slice)]
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
