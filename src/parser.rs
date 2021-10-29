use std::iter::Peekable;
use std::collections::HashMap;

use logos::{Logos, Lexer};
use crate::lexer::Token;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a> {
    List(Vec<Expr<'a>>),
    Symbol(String),
    Number(&'a str),
}

impl<'a> Expr<'a> {
    pub fn as_list(&self) -> Option<&[Expr]> {
        match self {
            Expr::List(v) => Some(&v),
            _ => None,
        }
    }

    pub fn as_symbol(&self) -> Option<&str> {
        if let Expr::Symbol(s) = self {
            Some(&s)
        } else {
            None
        }
    }
}

impl<'a> std::fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Expr::List(v) => {
                write!(f, "(")?;
                let mut first = true;
                for i in v {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", i)?;
                    first = false;
                }
                write!(f, ")")
            }
            Expr::Symbol(s) => {
                write!(f, ":{}", s)
            }
            Expr::Number(n) => {
                write!(f, "{}", n)
            }
        }
    }
}

type ParseError = &'static str;

type ReadMacro<'a> = dyn Fn(&mut Parser<'a>) -> Result<Expr<'a>, ParseError>;

pub struct Parser<'a> {
    pub lexer: Peekable<Lexer<'a, Token<'a>>>,
    read_macros: HashMap<&'a str, &'a ReadMacro<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Parser<'a> {
        let mut read_macros = HashMap::<&'a str, &'a ReadMacro<'a>>::new();
        read_macros.insert("fn", &parse_fn);
        read_macros.insert("type", &parse_type);
        Parser {
            lexer: Token::lexer(input).peekable(),
            read_macros,
        }
    }

    pub fn has_input(&mut self) -> bool {
        self.lexer.peek().is_some()
    }

    pub fn parse(&mut self) -> Result<Expr<'a>, ParseError> {
        self.parse_expr()
    }

    pub fn parse_expr(&mut self) -> Result<Expr<'a>, ParseError> {
        Ok(match self.lexer.next().ok_or("unexpected end of input")? {
            Token::Error => return Err("lexing error"),
            Token::Char(_) => unimplemented!("chars are not implemented"),
            Token::String(_) => unimplemented!("strings are not implemented"),
            Token::Integer(s) => Expr::Number(s),
            Token::Float(s) => Expr::Number(s),
            Token::Punctuation(_) => return Err("unexpected punctuation"),
            Token::Symbol(s) => {
                match self.read_macros.get(s) {
                    Some(&reader) => {
                        return reader(self)
                    }
                    None => {
                        // TODO: intern symbols
                        let expr = Expr::Symbol(s.to_string());
                        if self.lexer.peek() != Some(&Token::Punctuation("(")) {
                            expr
                        } else {
                            // parse function call
                            self.lexer.next();

                            let mut v = Vec::new();
                            v.push(Expr::Symbol("call".to_string()));
                            v.push(expr);

                            while self.lexer.peek().is_some() && self.lexer.peek() != Some(&Token::Punctuation(")")) {
                                v.push(self.parse_expr()?);
                                if self.lexer.peek() == Some(&Token::Punctuation(",")) {
                                    self.lexer.next();
                                }
                            }
                            if self.lexer.peek().is_none() {
                                return Err(") is expected")
                            }
                            self.lexer.next();

                            Expr::List(v)
                        }
                    }
                }
            }
        })
    }

    fn parse_symbol(&mut self) -> Result<Expr<'a>, ParseError> {
        match self.lexer.next().ok_or("identifier expected")? {
            Token::Symbol(s) => Ok(Expr::Symbol(s.to_string())),
            _ => Err("identifier expected")
        }
    }
}

fn parse_fn<'a>(p: &mut Parser<'a>) -> Result<Expr<'a>, ParseError> {
    let mut expr = Vec::new();
    expr.push(Expr::Symbol("fn".to_string()));
    expr.push(p.parse_expr()?);

    if p.lexer.peek() == Some(&Token::Symbol("=")) {
        p.lexer.next();
        expr.push(p.parse_expr()?);
    }

    Ok(Expr::List(expr))
}

fn parse_type<'a>(p: &mut Parser<'a>) -> Result<Expr<'a>, ParseError> {
    let mut expr = Vec::new();
    expr.push(Expr::Symbol("type".to_string()));
    expr.push(p.parse_symbol()?); // type name
    if p.lexer.next() != Some(Token::Symbol("=")) {
        return Err("expected '=' after type identifier")
    }
    expr.push(parse_type_specifier(p)?);

    Ok(Expr::List(expr))
}

fn parse_type_specifier<'a>(p: &mut Parser<'a>) -> Result<Expr<'a>, ParseError> {
    Ok(match p.lexer.next().ok_or("type specifier expected")? {
        Token::Symbol("bits") => {
            let size = p.parse_expr()?;
            Expr::List(vec![Expr::Symbol("bits".to_string()), size])
        }
        _ => return Err("only bits types specifier is currently supported")
    })
}
