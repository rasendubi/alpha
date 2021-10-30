use std::iter::Peekable;
use std::collections::HashMap;

use logos::{Logos, Lexer};

use crate::lexer::Token;
use crate::sexp::SExp;

type ParseError = &'static str;

type ReadMacro<'a> = dyn Fn(&mut Parser<'a>) -> Result<SExp<'a>, ParseError>;

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

    pub fn parse(&mut self) -> Result<SExp<'a>, ParseError> {
        self.parse_expr()
    }

    pub fn parse_expr(&mut self) -> Result<SExp<'a>, ParseError> {
        Ok(match self.lexer.next().ok_or("unexpected end of input")? {
            Token::Error => return Err("lexing error"),
            Token::Char(_) => unimplemented!("chars are not implemented"),
            Token::String(_) => unimplemented!("strings are not implemented"),
            Token::Integer(s) => SExp::Number(s),
            Token::Float(s) => SExp::Number(s),
            Token::Punctuation(_) => return Err("unexpected punctuation"),
            Token::Symbol(s) => {
                match self.read_macros.get(s) {
                    Some(&reader) => {
                        return reader(self)
                    }
                    None => {
                        // TODO: intern symbols
                        let expr = SExp::Symbol(s);
                        if self.lexer.peek() != Some(&Token::Punctuation("(")) {
                            expr
                        } else {
                            // parse function call
                            self.lexer.next();

                            let mut v = Vec::new();
                            v.push(SExp::Symbol("call"));
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

                            SExp::List(v)
                        }
                    }
                }
            }
        })
    }

    fn parse_symbol(&mut self) -> Result<SExp<'a>, ParseError> {
        match self.lexer.next().ok_or("identifier expected")? {
            Token::Symbol(s) => Ok(SExp::Symbol(s)),
            _ => Err("identifier expected")
        }
    }
}

fn parse_fn<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>, ParseError> {
    let mut expr = Vec::new();
    expr.push(SExp::Symbol("fn"));
    expr.push(p.parse_expr()?);

    if p.lexer.peek() == Some(&Token::Symbol("=")) {
        p.lexer.next();
        expr.push(p.parse_expr()?);
    }

    Ok(SExp::List(expr))
}

fn parse_type<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>, ParseError> {
    let mut expr = Vec::new();
    expr.push(SExp::Symbol("type"));
    expr.push(p.parse_symbol()?); // type name
    if p.lexer.next() != Some(Token::Symbol("=")) {
        return Err("expected '=' after type identifier")
    }
    expr.push(parse_type_specifier(p)?);

    Ok(SExp::List(expr))
}

fn parse_type_specifier<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>, ParseError> {
    Ok(match p.lexer.next().ok_or("type specifier expected")? {
        Token::Symbol("bits") => {
            let size = p.parse_expr()?;
            SExp::List(vec![SExp::Symbol("bits"), size])
        }
        _ => return Err("only bits types specifier is currently supported")
    })
}
