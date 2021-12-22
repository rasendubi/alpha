//! High-level Intermediate Representation (HIR) types.
// CLIPPY: using write! everywhere in the Debug implementation makes mode consistent.
#![allow(clippy::write_with_newline)]

use crate::Symbol;

use std::fmt::Write;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Decl {
    Global {
        /// Optional user-defined external name of the global. Necessary to link modules together.
        name: Option<Symbol>,
        v: Var,
        ty: Type,
        /// Initializer. If `None`, the global is assumed to be external.
        value: Option<Exp>,
    },
    AddMethod {
        ty: Var,
        method: Var,
    },
    /// Specifies the main function for the module. Might be absent.
    Main(Var),
}

/// Vars are globally-unique single-assignment variables.
///
/// The only way to create a new `Var` is via [`genglobal()`] or [`genvar()`].
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum Var {
    Global(usize),
    Local(usize),
}
static NEXT: AtomicUsize = AtomicUsize::new(0);
/// Generate a new global [Var].
pub fn genglobal() -> Var {
    Var::Global(NEXT.fetch_add(1, Ordering::Relaxed))
}
/// Generate a new local [Var].
pub fn genvar() -> Var {
    Var::Local(NEXT.fetch_add(1, Ordering::Relaxed))
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Type {
    /// Regular struct type. Var must be statically-known variable pointing to a DataType.
    T(Var),
    /// Built-in integer type.
    I(usize),
    /// Built-in float type.
    F(usize),
    /// Function type.
    Fn(Vec<Type>, Box<Type>),
    /// A type specifier that only matches a value of Var.
    ///
    /// e.g., `Type(X)` only matches **the value `X`**, not values of type `X`.
    Type(Var),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Exp {
    StringLiteral(String),
    NumberLiteral(Type, String),

    /// Create a new vector.
    Vector(Vec<Var>),
    /// Create a new object.
    Object {
        /// Type of the object. Must be a statically-known var of type DataType.
        ty: Var,
        fields: Vec<Var>,
    },
    Select {
        /// Must be of statically-known type.
        value: Var,
        field: usize,
    },

    MethodSelect {
        args: Var,
    },

    /// Create a new DataType definition.
    DataType(TypeDef),

    Let {
        v: Var,
        ty: Type,
        value: Box<Exp>,
        e: Box<Exp>,
    },
    /// Local variables reference.
    Var(Var),

    Fn(Fn),
    Apply {
        f: Var,
        args: Vec<Var>,
    },

    GlobalRef(Type, String),
}
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Fn {
    pub params: Vec<(Var, Type)>,
    pub retty: Type,
    pub body: Box<Exp>,
}

/// Type definition. It takes a form of struct and user-defined types (even primitive) are lowered
/// to it.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TypeDef {
    pub name: Symbol,
    pub superty: Var,
    pub is_abstract: bool,
    pub fields: Vec<(Symbol, Type)>,
}

//// Debug implementations.

impl std::fmt::Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "module {{")?;

        if f.alternate() {
            write!(f, "\n")?;
        }

        for decl in &self.decls {
            if f.alternate() {
                write!(indented(f), "{:#?}\n", decl)?;
            } else {
                write!(f, " {:?},", decl)?;
            }
        }

        if !f.alternate() {
            write!(f, " ")?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}
impl std::fmt::Debug for Decl {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Decl::Global { name, v, ty, value } => {
                write!(f, "global")?;
                if let Some(name) = name {
                    write!(f, "({:?})", name)?;
                }
                write!(f, " {:?}: {:?}", v, ty)?;
                if let Some(value) = value {
                    if f.alternate() {
                        write!(f, " =\n")?;
                        write!(indented(f), "{:#?}", value)?;
                    } else {
                        write!(f, " = {:?}", value)?;
                    }
                }
            }
            Decl::AddMethod { ty, method } => {
                write!(f, "addmethod {:?} {:?}", ty, method)?;
            }
            Decl::Main(v) => {
                write!(f, "main {:?}", v)?;
            }
        }
        Ok(())
    }
}
impl std::fmt::Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Var::Global(n) => write!(f, "@{}", n),
            Var::Local(n) => write!(f, "%{}", n),
        }
    }
}
impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Type::T(v) => write!(f, "${:?}", v),
            Type::I(n) => write!(f, "$i{}", n),
            Type::F(n) => write!(f, "$f{}", n),
            Type::Fn(params, ret) => {
                write!(f, "$(")?;
                let mut first_param = true;
                for p in params {
                    if first_param {
                        first_param = false;
                    } else {
                        write!(f, ", ")?;
                    }

                    write!(f, "{:?}", p)?;
                }
                write!(f, ") -> {:?}", ret)
            }
            Type::Type(v) => write!(f, "$Type{{{:?}}}", v),
        }
    }
}
impl std::fmt::Debug for Exp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let _ = match self {
            Exp::StringLiteral(s) => {
                write!(f, "{:?}", s)?;
            }
            Exp::NumberLiteral(ty, n) => {
                write!(f, "{:?} {}", ty, n)?;
            }
            Exp::Vector(vars) => {
                write!(f, "{:?}", vars)?;
            }
            Exp::Object { ty, fields } => {
                write!(f, "{:?}{{", ty)?;
                for v in fields {
                    write!(f, " {:?},", v)?;
                }
                write!(f, " }}")?;
            }
            Exp::Select { value, field } => {
                write!(f, "{:?}.{:?}", value, field)?;
            }
            Exp::MethodSelect { args } => {
                write!(f, "method_select {:?}", args)?;
            }
            Exp::DataType(typedef) => {
                if f.alternate() {
                    write!(f, "datatype {:#?}", typedef)?;
                } else {
                    write!(f, "datatype {:?}", typedef)?;
                }
            }
            Exp::Let { v, ty, value, e } => {
                if f.alternate() {
                    write!(f, "let {:#?}: {:#?} =\n", v, ty)?;
                    write!(indented(f), "{:#?}", value)?;
                    write!(f, "\nin\n")?;
                    write!(indented(f), "{:#?}", e)?;
                } else {
                    write!(f, "let {:?}: {:?} = {:?} in {:?}", v, ty, value, e)?;
                }
            }
            Exp::Var(v) => write!(f, "{:?}", v)?,
            Exp::Fn(fun) => {
                if f.alternate() {
                    write!(f, "{:#?}", fun)?;
                } else {
                    write!(f, "{:?}", fun)?;
                }
            }
            Exp::Apply { f: fun, args } => {
                write!(f, "{:?}(", fun)?;
                let mut first_arg = true;
                for a in args {
                    if first_arg {
                        first_arg = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", a)?;
                }
                write!(f, ")")?;
            }
            Exp::GlobalRef(ty, name) => {
                write!(f, "global_ref {:?}: {:?}", name, ty)?;
            }
        };

        Ok(())
    }
}
impl std::fmt::Debug for Fn {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let Fn {
            params,
            retty,
            body,
        } = self;

        write!(f, "fn(")?;
        let mut first_param = true;
        for (v, t) in params {
            if first_param {
                first_param = false;
            } else {
                write!(f, ", ")?;
            }

            write!(f, "{:?}: {:?}", v, t)?;
        }
        write!(f, "): {:?} ->", retty)?;
        if f.alternate() {
            write!(f, "\n")?;
            write!(indented(f), "{:#?}", body)?;
        } else {
            write!(f, " {:?}", body)?;
        }

        Ok(())
    }
}

fn indented<D>(f: &mut D) -> indenter::Indented<D> {
    indenter::indented(f).with_str("  ")
}
