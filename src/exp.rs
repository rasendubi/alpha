//! Untyped AST
use std::error::Error;

use simple_error::{simple_error, bail};

use crate::symbol::{Symbol, SymbolInterner};
use crate::sexp::SExp;

#[derive(Debug, PartialEq, Clone)]
pub enum Exp {
    /// Function declaration/definition
    Function(Function),
    Call(Call),
    /// Symbol (variable) reference.
    Symbol(Symbol),
    Number(f64),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub prototype: FunctionPrototype,
    pub body: Option<Box<Exp>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionPrototype {
    pub name: Symbol,
    pub params: Vec<FunctionParameter>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionParameter {
    pub name: Symbol,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Call {
    pub fun: Box<Exp>,
    pub args: Vec<Exp>,
}

/// Lower possibly malformed sexp AST into an untyped AST.
pub fn lower_sexp(sexp: &SExp, interner: &mut SymbolInterner) -> Result<Exp, Box<dyn Error>> {
    let exp = match sexp {
        SExp::Number(n) => Exp::Number(n.parse().expect("cannot parse f64")),
        SExp::Symbol(s) => Exp::Symbol(interner.get_or_intern(s)),
        SExp::List(v) => {
            match v[0].as_symbol().expect("List head is not symbol") {
                "fn" => {
                    let prototype = lower_function_prototype(&v[1], interner)?;
                    let body = Some(Box::new(lower_sexp(&v[2], interner)?));
                    Exp::Function(Function{ prototype, body })
                }
                "call" => {
                    let fun = Box::new(lower_sexp(&v[1], interner)?);
                    let mut args = Vec::new();
                    for arg in &v[2..] {
                        args.push(lower_sexp(arg, interner)?);
                    }
                    Exp::Call(Call{ fun, args })
                }
                x => {
                    panic!("Invalid list head: {}", x);
                }
            }
        }
    };
    Ok(exp)
}

fn lower_function_prototype(sexp: &SExp, interner: &mut SymbolInterner) -> Result<FunctionPrototype, Box<dyn Error>> {
    // (:fn (:call name params...) body)
    let proto = sexp.as_list().ok_or_else(|| simple_error!("function definition should start with call-like sexp, given: {}", sexp))?;
    if proto[0].as_symbol().unwrap() != "call" {
        bail!("function definition should start with call-like sexp, it starts with: {}", proto[0]);
    }

    let name = interner.get_or_intern(proto[1].as_symbol().ok_or_else(|| simple_error!("function name should be a symbol, given: {}", proto[1]))?);
    let mut params = Vec::new();
    for param in &proto[2..] {
        params.push(lower_function_parameter(param, interner)?);
    }

    Ok(FunctionPrototype{ name, params })
}

fn lower_function_parameter(sexp: &SExp, interner: &mut SymbolInterner) -> Result<FunctionParameter, Box<dyn Error>> {
    let name = sexp.as_symbol().ok_or_else(|| simple_error!("function parameter must be a symbol, given: {}", sexp))?;
    let name = interner.get_or_intern(name);
    Ok(FunctionParameter{ name })
}
