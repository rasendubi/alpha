//! Untyped AST
use std::convert::TryInto;
use std::error::Error;

use simple_error::{bail, simple_error};

use crate::sexp::SExp;
use crate::symbol::{Symbol, SymbolInterner};

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
    Block(Vec<Exp>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeDefinition {
    pub name: Symbol,
    pub supertype: Symbol,
    pub specifier: TypeSpecifier,
}

#[derive(Debug, PartialEq, Clone)]
pub enum TypeSpecifier {
    Integer(usize),
    Float(usize),
    Struct(Vec<StructFieldSpecifier>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct StructFieldSpecifier {
    pub name: Symbol,
    pub typ: Symbol,
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
    pub result_type: Symbol,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionParameter {
    pub name: Symbol,
    pub typ: Symbol,
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
        SExp::Symbol(s) => Exp::Symbol(interner.intern(s)),
        SExp::List(v) => match v[0].as_symbol().expect("list head is not a symbol") {
            "type" => Exp::Type(lower_type_definition(&v[1], interner)?),
            "fn" => Exp::Function(lower_function(&v[1], interner)?),
            "call" => {
                let fun = Box::new(lower_sexp(&v[1], interner)?);
                let mut args = Vec::new();
                for arg in &v[2..] {
                    args.push(lower_sexp(arg, interner)?);
                }
                Exp::Call(Call { fun, args })
            }
            "block" => {
                let mut block = Vec::new();
                for sexp in &v[1..] {
                    block.push(lower_sexp(sexp, interner)?);
                }
                Exp::Block(block)
            }
            x => {
                panic!("unknown sexp list head: {}", x);
            }
        },
    };
    Ok(exp)
}

fn lower_type_definition(
    sexp: &SExp,
    interner: &mut SymbolInterner,
) -> Result<TypeDefinition, Box<dyn Error>> {
    match lower_sexp(sexp, interner)? {
        Exp::Call(Call { fun, args }) if *fun == Exp::Symbol(interner.intern("=")) => {
            let (name, supertype) = match &args[0] {
                Exp::Symbol(s) => (*s, interner.intern("Any")),
                Exp::Call(Call { fun, args }) if **fun == Exp::Symbol(interner.intern(":")) => {
                    let name = match &args[0] {
                        Exp::Symbol(s) => *s,
                        e => bail!("type name must be a symbol, {:?} given", e),
                    };
                    let supertype = match &args[1] {
                        Exp::Symbol(s) => *s,
                        e => bail!("supertype must be a symbol, {:?} given", e),
                    };
                    (name, supertype)
                }
                e => bail!("type name must be a symbol, {:?} given", e),
            };
            let specifier = lower_type_specifier(&args[1], interner)?;
            Ok(TypeDefinition {
                name,
                supertype,
                specifier,
            })
        }
        e => bail!(
            "type definition should have a form of: TypeName = <type specifier>, {:?} given",
            e
        ),
    }
}

fn lower_type_specifier(
    exp: &Exp,
    interner: &mut SymbolInterner,
) -> Result<TypeSpecifier, Box<dyn Error>> {
    let specifier = match exp {
        Exp::Call(Call { fun, args }) => match **fun {
            Exp::Symbol(s) if s == interner.intern("integer") => {
                if args.len() != 1 {
                    bail!("integer() takes exactly 1 argument, {} given", args.len());
                }
                let n = match &args[0] {
                    Exp::Integer(n) => *n,
                    e => bail!(
                        "integer() argument must be an integer constant, given: {:?}",
                        e
                    ),
                };
                TypeSpecifier::Integer(n.try_into().unwrap())
            }
            Exp::Symbol(s) if s == interner.intern("float") => {
                if args.len() != 1 {
                    bail!("float() takes exactly 1 argument, {} given", args.len());
                }
                let n = match &args[0] {
                    Exp::Integer(n) => *n,
                    e => bail!(
                        "float() argument must be an integer constant, given: {:?}",
                        e
                    ),
                };
                if n != 16 && n != 32 && n != 64 && n != 128 {
                    bail!(
                        "float() only supports 16, 32, 64, and 128-bit sizes, given: {}",
                        n
                    );
                }
                TypeSpecifier::Float(n.try_into().unwrap())
            }
            _ => bail!("unknown type specifier"),
        },
        Exp::Block(block) => {
            let mut fields = Vec::new();
            for f in block {
                let (name, typ) = match f {
                    Exp::Symbol(s) => (*s, interner.intern("Any")),

                    Exp::Call(Call { fun, args })
                        if &**fun == &Exp::Symbol(interner.intern(":")) =>
                    {
                        let name = match args.get(0) {
                            Some(Exp::Symbol(s)) => s,
                            e => bail!("parameter name must be a symbol, {:?} given", e),
                        };
                        let typ = match args.get(1) {
                            Some(Exp::Symbol(s)) => s,
                            e => bail!("parameter type must be a symbol, {:?} given", e),
                        };

                        (*name, *typ)
                    }

                    e => bail!("unable to parse struct field: {:?}", e),
                };

                fields.push(StructFieldSpecifier { name, typ });
            }

            TypeSpecifier::Struct(fields)
        }
        e => bail!("type specifier should be a call, given: {:?}", e),
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
    Ok(Function { prototype, body })
}

fn lower_function_prototype(
    sexp: &SExp,
    interner: &mut SymbolInterner,
) -> Result<FunctionPrototype, Box<dyn Error>> {
    // (:fn (:call name params...) body)
    // (:fn (:call :: (:call name params...) result_type) body)
    let proto = sexp.as_list().ok_or_else(|| {
        simple_error!(
            "function definition should start with call-like sexp, given: {}",
            sexp
        )
    })?;
    if proto[0].as_symbol().unwrap() != "call" {
        bail!(
            "function definition should start with call-like sexp, it starts with: {}",
            proto[0]
        );
    }

    let head = proto[1]
        .as_symbol()
        .ok_or_else(|| simple_error!("function name should be a symbol, given: {}", proto[1]))?;
    let (proto, result_type) = if head == ":" {
        let result_type = proto[3].as_symbol().ok_or_else(|| {
            simple_error!(
                "function return types should be a symbol, {} given",
                proto[3]
            )
        })?;
        let proto = proto[2].as_list().ok_or_else(|| {
            simple_error!(
                "function definition should start with call-like sexp, given: {}",
                sexp
            )
        })?;
        if proto[0].as_symbol().unwrap() != "call" {
            bail!(
                "function definition should start with call-like sexp, it starts with: {}",
                proto[0]
            );
        }
        if proto[1].as_symbol().is_none() {
            bail!("function name should be a symbol, given: {}", proto[1]);
        }

        (proto, interner.intern(result_type))
    } else {
        (proto, interner.intern("Any"))
    };

    let name = interner.intern(head);
    let mut params = Vec::new();
    for param in &proto[2..] {
        params.push(lower_function_parameter(param, interner)?);
    }

    Ok(FunctionPrototype {
        name,
        params,
        result_type,
    })
}

fn lower_function_parameter(
    sexp: &SExp,
    interner: &mut SymbolInterner,
) -> Result<FunctionParameter, Box<dyn Error>> {
    let param = match sexp {
        SExp::Symbol(s) => FunctionParameter {
            name: interner.intern(s),
            typ: interner.intern("Any"),
        },
        SExp::List(v)
            if v[0] == SExp::Symbol("call")
                && v[1] == SExp::Symbol(":")
                && v[2].as_symbol().is_some()
                && v[3].as_symbol().is_some() =>
        {
            FunctionParameter {
                name: interner.intern(v[2].as_symbol().unwrap()),
                typ: interner.intern(v[3].as_symbol().unwrap()),
            }
        }
        e => bail!("cannot parse function parameter: {}", e),
    };
    Ok(param)
}
