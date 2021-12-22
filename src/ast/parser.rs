//! Parser converts a string into [`SExp`].
use std::array::IntoIter;
use std::collections::HashMap;
use std::iter::{FromIterator, Peekable};

use anyhow::{anyhow, bail, Result};
use logos::{Lexer, Logos};
use tracing::trace;

use crate::ast::lexer::Token;
use crate::ast::sexp::SExp;

pub struct Parser<'a> {
    pub lexer: Peekable<Lexer<'a, Token<'a>>>,
    parse_table: ParseTable<'a>,
}

type ParseTable<'a> = HashMap<ParseKey<'a>, ParseRule<'a>>;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum ParseKey<'a> {
    Integer,
    Float,
    Symbol(&'a str),
    String,
    Char,
}
impl<'a> From<&Token<'a>> for ParseKey<'a> {
    fn from(token: &Token<'a>) -> Self {
        use ParseKey::*;
        match token {
            Token::Integer(_) => Integer,
            Token::Float(_) => Float,
            Token::Symbol(s) => Symbol(s),
            Token::String(_) => String,
            Token::Char(_) => Char,
            Token::Error => panic!("error token"),
        }
    }
}

type ParseFn<'a> = dyn Fn(&mut Parser<'a>) -> Result<SExp<'a>>;
type InfixParseFn<'a> = dyn Fn(&mut Parser<'a>, SExp<'a>) -> Result<SExp<'a>>;

pub struct ParseRule<'a> {
    prefix: Option<&'a ParseFn<'a>>,
    infix: Option<Infix<'a>>,
}
pub struct Infix<'a> {
    precedence: usize,
    parser: &'a InfixParseFn<'a>,
}
impl<'a> Infix<'a> {
    fn new(precedence: usize, parser: &'a InfixParseFn<'a>) -> Self {
        Infix { precedence, parser }
    }
}

macro_rules! parse_rules {
    ( $( { $key:expr => $($body:tt)* } ),* $(,)? ) => {
        HashMap::from_iter(IntoIter::new([
            $( ($key, parse_rules!{ @rule $($body)* }) ),*
        ]))
    };
    ( @rule ) => {
        ParseRule{ prefix: None, infix: None }
    };
    ( @rule prefix: $f:expr ) => {
        ParseRule{ prefix: Some(&$f), infix: None }
    };
    ( @rule infix: $prec:expr, $f:expr ) => {
        ParseRule{ prefix: None, infix: Some(Infix::new($prec, &$f)) }
    };
    ( @rule prefix: $prefix:expr, infix: $prec:expr, $infix:expr ) => {
        ParseRule{ prefix: Some(&$prefix), infix: Some(Infix::new($prec, &$infix)) }
    };
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Parser<'a> {
        use ParseKey::*;
        let parse_table = parse_rules! {
            { Integer          => prefix: parse_integer                        },
            { Float            => prefix: parse_float                          },
            { String           => prefix: parse_string                         },
            { Symbol("@")      => prefix: parse_annotation                     },
            { Symbol("fn")     => prefix: parse_fn                             },
            { Symbol("type")   => prefix: parse_type                           },
            { Symbol("{")      => prefix: parse_block                          },

            { Symbol("=")      =>                      infix: 10, parse_binary },

            { Symbol("==")     =>                      infix: 40, parse_binary },
            { Symbol("!=")     =>                      infix: 40, parse_binary },

            { Symbol("<")      =>                      infix: 70, parse_binary },
            { Symbol(">")      =>                      infix: 70, parse_binary },
            { Symbol("<=")     =>                      infix: 70, parse_binary },
            { Symbol(">=")     =>                      infix: 70, parse_binary },

            { Symbol("+")      =>                      infix: 60, parse_binary },
            { Symbol("-")      =>                      infix: 60, parse_binary },

            { Symbol("*")      =>                      infix: 70, parse_binary },
            { Symbol("/")      =>                      infix: 70, parse_binary },

            { Symbol(":")      =>                      infix: 80, parse_binary },

            { Symbol("(")      => prefix: parse_group, infix: 90, parse_call   },
            { Symbol(".")      =>                      infix: 90, parse_dot    },
        };
        Parser {
            lexer: Token::lexer(input).peekable(),
            parse_table,
        }
    }

    pub fn has_input(&mut self) -> bool {
        self.lexer.peek().is_some()
    }

    pub fn parse(&mut self) -> Result<SExp<'a>> {
        self.parse_expr()
    }

    pub fn parse_expr(&mut self) -> Result<SExp<'a>> {
        self.parse_precedence(0)
    }

    #[tracing::instrument(skip(self))]
    pub fn parse_precedence(&mut self, precedence: usize) -> Result<SExp<'a>> {
        let token = self
            .lexer
            .peek()
            .ok_or_else(|| anyhow!("unexpected end of input"))?;
        trace!("prefix: {:?}", token);
        let prefix_parser = self
            .parse_table
            .get(&token.into())
            .and_then(|r| r.prefix)
            .unwrap_or(&parse_fallback);

        let mut left = prefix_parser(self)?;

        loop {
            let token = match self.lexer.peek() {
                Some(token) => token,
                _ => return Ok(left),
            };
            trace!("infix: {:?}", token);
            let infix = match self
                .parse_table
                .get(&token.into())
                .and_then(|r| r.infix.as_ref())
            {
                Some(infix) => infix,
                _ => return Ok(left),
            };
            if infix.precedence < precedence {
                break;
            }
            left = (infix.parser)(self, left)?;
        }

        Ok(left)
    }

    fn parse_symbol(&mut self) -> Result<SExp<'a>> {
        match self
            .lexer
            .next()
            .ok_or_else(|| anyhow!("identifier expected"))?
        {
            Token::Symbol(s) => Ok(SExp::Symbol(s)),
            _ => bail!("identifier expected"),
        }
    }
}

fn parse_annotation<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    p.lexer.next(); // @

    Ok(SExp::List(vec![
        SExp::Symbol("annotation"),
        p.parse_precedence(90)?,
        p.parse_precedence(90)?,
    ]))
}

fn parse_fn<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    p.lexer.next(); // fn

    Ok(SExp::List(vec![SExp::Symbol("fn"), p.parse_expr()?]))
}

fn parse_type<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    p.lexer.next(); // type
    let mut expr = Vec::with_capacity(3);
    expr.push(SExp::Symbol("type"));
    expr.push(p.parse_expr()?);

    Ok(SExp::List(expr))
}

fn parse_integer<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    match p.lexer.next().unwrap() {
        Token::Integer(s) => Ok(SExp::Integer(s)),
        _ => unreachable!(),
    }
}

fn parse_float<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    match p.lexer.next().unwrap() {
        Token::Float(s) => Ok(SExp::Float(s)),
        _ => unreachable!(),
    }
}

fn parse_string<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    match p.lexer.next().unwrap() {
        Token::String(s) => Ok(SExp::String(unescape_string(s))),
        _ => unreachable!(),
    }
}

fn parse_group<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    p.lexer.next(); // (
    let expr = p.parse_expr()?;
    match p.lexer.next() {
        Some(Token::Symbol(")")) => {}
        _ => bail!("expected )"),
    }
    Ok(expr)
}

fn parse_block<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    p.lexer.next(); // {
    let mut v = vec![SExp::Symbol("block")];

    while p.lexer.peek().is_some() && p.lexer.peek() != Some(&Token::Symbol("}")) {
        v.push(p.parse_expr()?);

        let peek = p.lexer.peek();
        if peek == Some(&Token::Symbol(",")) || peek == Some(&Token::Symbol(";")) {
            p.lexer.next();
        }
    }
    if p.lexer.peek().is_none() {
        bail!("}} is expected")
    }
    p.lexer.next(); // }

    Ok(SExp::List(v))
}

fn parse_fallback<'a>(p: &mut Parser<'a>) -> Result<SExp<'a>> {
    let token = p.lexer.next().unwrap();
    match token {
        Token::Symbol(s) => Ok(SExp::Symbol(s)),
        t => bail!("unexpected token: {:?}", t),
    }
}

fn parse_binary<'a>(p: &mut Parser<'a>, left: SExp<'a>) -> Result<SExp<'a>> {
    let token = p.lexer.next().unwrap();
    let precedence = p
        .parse_table
        .get(&(&token).into())
        .unwrap()
        .infix
        .as_ref()
        .unwrap()
        .precedence;

    let operator = match token {
        Token::Symbol(s) => s,
        _ => unreachable!(),
    };

    let right = p.parse_precedence(precedence + 1)?;

    Ok(SExp::List(vec![
        SExp::Symbol("call"),
        SExp::Symbol(operator),
        left,
        right,
    ]))
}

fn parse_dot<'a>(p: &mut Parser<'a>, left: SExp<'a>) -> Result<SExp<'a>> {
    p.lexer.next(); // .
    let symbol = p.parse_symbol()?;
    if p.lexer.peek() == Some(&Token::Symbol("(")) {
        // parse as a function call:
        // x.f(y) => f(x, y)
        let mut v = vec![SExp::Symbol("call"), symbol, left];

        p.lexer.next(); // (
        while p.lexer.peek().is_some() && p.lexer.peek() != Some(&Token::Symbol(")")) {
            v.push(p.parse_expr()?);
            if p.lexer.peek() == Some(&Token::Symbol(",")) {
                p.lexer.next();
            }
        }
        if p.lexer.peek().is_none() {
            bail!(") is expected")
        }
        p.lexer.next(); // )

        Ok(SExp::List(v))
    } else {
        // parse as a function call:
        // x.f => f(x)
        Ok(SExp::List(vec![SExp::Symbol("call"), symbol, left]))
    }
}

fn parse_call<'a>(p: &mut Parser<'a>, left: SExp<'a>) -> Result<SExp<'a>> {
    p.lexer.next(); // (

    let mut v = vec![SExp::Symbol("call"), left];

    while p.lexer.peek().is_some() && p.lexer.peek() != Some(&Token::Symbol(")")) {
        v.push(p.parse_expr()?);
        if p.lexer.peek() == Some(&Token::Symbol(",")) {
            p.lexer.next();
        }
    }
    if p.lexer.peek().is_none() {
        bail!(") is expected")
    }
    p.lexer.next();

    Ok(SExp::List(v))
}

fn unescape_string(s: &str) -> String {
    let mut result = String::new();

    let mut chars = s.chars();
    chars.next(); // "
    loop {
        let c = chars.next();
        match c {
            None => panic!("unexpected end of input while parsing string"),
            Some('"') => {
                if chars.next().is_some() {
                    panic!("unexpected \" in the middle of the string");
                }
                break;
            }
            Some('\\') => match chars.next() {
                None => panic!("unexpected end of input while parsing string (after \\)"),
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('n') => result.push('\n'),
                Some(c) => {
                    result.push('\\');
                    result.push(c);
                }
            },
            Some(c) => result.push(c),
        }
    }

    result
}
