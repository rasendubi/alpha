//! Untyped AST
use std::convert::TryInto;
use std::error::Error;

use simple_error::{simple_error, bail};

use crate::symbol::{Symbol, SymbolInterner};
use crate::sexp::SExp;

#[derive(Debug, PartialEq, Clone)]
pub enum Exp {
    Type(TypeDefinition),
    /// Function declaration/definition
    Function(Function),
    Call(Call),
    /// Symbol (variable) reference.
    Symbol(Symbol),
    Integer(i64),
    Float(f64),
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDefinition {
    pub name: Symbol,
    pub specifier: TypeSpecifier,
}

#[derive(Debug, PartialEq, Clone)]
pub enum TypeSpecifier {
    Integer(usize),
    Float(usize),
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
        SExp::Integer(n) => Exp::Integer(n.parse().expect("cannot parse i64")),
        SExp::Float(n) => Exp::Float(n.parse().expect("cannot parse f64")),
        SExp::Symbol(s) => Exp::Symbol(interner.get_or_intern(s)),
        SExp::List(v) => {
            match v[0].as_symbol().expect("List head is not symbol") {
                "type" => {
                    let name = v[1].as_symbol()
                        .ok_or_else(|| simple_error!("type name should be a symbol, {} given", v[1]))?;
                    let name = interner.get_or_intern(name);
                    let specifier = lower_type_specifier(&v[2], interner)?;
                    Exp::Type(TypeDefinition{ name, specifier })
                }
                "fn" => {
                    Exp::Function(lower_function(&v[1], interner)?)
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

fn lower_type_specifier(sexp: &SExp, interner: &mut SymbolInterner) -> Result<TypeSpecifier, Box<dyn Error>> {
    let specifier = match lower_sexp(sexp, interner)? {
        Exp::Call(Call{ fun, args }) => {
            match *fun {
                Exp::Symbol(s) if s == interner.get_or_intern("integer") => {
                    if args.len() != 1 {
                        bail!("integer() takes exactly 1 argument, {} given", args.len());
                    }
                    let n = match &args[0] {
                        Exp::Integer(n) => *n,
                        e => bail!("integer() argument must be an integer constant, given: {:?}", e),
                    };
                    TypeSpecifier::Integer(n.try_into().unwrap())
                }
                Exp::Symbol(s) if s == interner.get_or_intern("float") => {
                    if args.len() != 1 {
                        bail!("float() takes exactly 1 argument, {} given", args.len());
                    }
                    let n = match &args[0] {
                        Exp::Integer(n) => *n,
                        e => bail!("float() argument must be an integer constant, given: {:?}", e),
                    };
                    if n != 16 && n != 32 && n != 64 && n != 128 {
                        bail!("float() only supports 16, 32, 64, and 128-bit sizes, given: {}", n);
                    }
                    TypeSpecifier::Float(n.try_into().unwrap())
                }
                _ => bail!("unknown type specifier")
            }
        }
        _ => bail!("type specifier should be a call, given: {}", sexp)
    };
    Ok(specifier)
}


fn lower_function(sexp: &SExp, interner: &mut SymbolInterner) -> Result<Function, Box<dyn Error>> {
    let v = match sexp {
        SExp::List(v) if v[0] == SExp::Symbol("call") && v[1] == SExp::Symbol("=") => v,
        _ => bail!("'fn' should be followed by function assignment"),
    };

    let prototype = lower_function_prototype(&v[2], interner)?;
    let body = Some(Box::new(lower_sexp(&v[3], interner)?));
    Ok(Function{ prototype, body })
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
