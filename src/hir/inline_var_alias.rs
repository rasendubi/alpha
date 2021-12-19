//! Rewrite
//!
//! ```norust
//! let vX = vY
//! in E
//! ```
//!
//! to
//!
//! ```norust
//! E[vY/vX]
//! ```
use crate::hir::*;

use std::collections::HashMap;

pub fn inline_var_alias(m: &Module) -> Module {
    InlineVarAlias {
        renames: HashMap::new(),
    }
    .process_module(m)
}

struct InlineVarAlias {
    renames: HashMap<Var, Var>,
}

impl InlineVarAlias {
    fn process_module(&mut self, m: &Module) -> Module {
        for d in &m.decls {
            self.collect_decl(d);
        }
        self.traverse_module(m)
    }

    fn collect_decl(&mut self, d: &Decl) {
        match d {
            Decl::Global {
                // Only nameless global vars are eligible for inlining. Otherwise, a user might find
                // a variable missing.
                name: None,
                v,
                ty: _,
                value: Some(Exp::Var(v2)),
            } if v == v2 => {
                self.renames.insert(*v, *v2);
            }
            Decl::Global {
                name: _,
                v: _,
                ty: _,
                value: Some(value),
            } => {
                self.collect_exp(value);
            }
            _ => {}
        }
    }

    fn collect_exp(&mut self, e: &Exp) {
        match e {
            Exp::StringLiteral(_) => {}
            Exp::NumberLiteral(_, _) => {}
            Exp::Vector(_) => {}
            Exp::Object { .. } => {}
            Exp::Select { .. } => {}
            Exp::MethodSelect { .. } => {}
            Exp::DataType(_) => {}
            Exp::Let { v, ty: _, value, e } => {
                if let Exp::Var(v2) = &**value {
                    self.renames.insert(*v, *v2);
                }
                self.collect_exp(value);
                self.collect_exp(e);
            }
            Exp::Var(_) => {}
            Exp::Fn(f) => {
                self.collect_exp(&f.body);
            }
            Exp::Apply { .. } => {}
        }
    }

    fn traverse_module(&self, m: &Module) -> Module {
        Module {
            decls: m
                .decls
                .iter()
                .filter_map(|d| self.traverse_decl(d))
                .collect(),
        }
    }

    fn traverse_decl(&self, d: &Decl) -> Option<Decl> {
        let d = match d {
            Decl::Global { v, .. } if self.renames.contains_key(v) => {
                return None;
            }
            Decl::Global { name, v, ty, value } => Decl::Global {
                name: *name,
                v: *v,
                ty: self.traverse_type(ty),
                value: value.as_ref().map(|e| self.traverse_exp(e)),
            },
            Decl::AddMethod { ty, method } => Decl::AddMethod {
                ty: self.traverse_var(*ty),
                method: self.traverse_var(*method),
            },
            Decl::Main(v) => Decl::Main(self.traverse_var(*v)),
        };
        Some(d)
    }

    fn traverse_exp(&self, e: &Exp) -> Exp {
        match e {
            Exp::StringLiteral(_) => e.clone(),
            Exp::NumberLiteral(ty, s) => Exp::NumberLiteral(self.traverse_type(ty), s.clone()),
            Exp::Vector(xs) => Exp::Vector(xs.iter().map(|v| self.traverse_var(*v)).collect()),
            Exp::Object { ty, fields } => Exp::Object {
                ty: self.traverse_var(*ty),
                fields: fields.iter().map(|v| self.traverse_var(*v)).collect(),
            },
            Exp::Select { value, field } => Exp::Select {
                value: self.traverse_var(*value),
                field: *field,
            },
            Exp::MethodSelect { args } => Exp::MethodSelect {
                args: self.traverse_var(*args),
            },
            Exp::DataType(typedef) => Exp::DataType(self.traverse_typedef(typedef)),
            Exp::Let { v, e, .. } if self.renames.contains_key(v) => self.traverse_exp(e),
            Exp::Let { v, ty, value, e } => Exp::Let {
                v: *v,
                ty: self.traverse_type(ty),
                value: Box::new(self.traverse_exp(value)),
                e: Box::new(self.traverse_exp(e)),
            },
            Exp::Var(v) => Exp::Var(self.traverse_var(*v)),
            Exp::Fn(Fn {
                params,
                retty,
                body,
            }) => Exp::Fn(Fn {
                params: params.clone(),
                retty: self.traverse_type(retty),
                body: Box::new(self.traverse_exp(body)),
            }),
            Exp::Apply { f, args } => Exp::Apply {
                f: self.traverse_var(*f),
                args: args.iter().map(|a| self.traverse_var(*a)).collect(),
            },
        }
    }

    fn traverse_typedef(&self, typedef: &TypeDef) -> TypeDef {
        let TypeDef {
            name,
            superty,
            is_abstract,
            fields,
        } = typedef;
        TypeDef {
            name: *name,
            superty: self.traverse_var(*superty),
            is_abstract: *is_abstract,
            fields: fields
                .iter()
                .map(|(s, t)| (*s, self.traverse_type(t)))
                .collect(),
        }
    }

    fn traverse_type(&self, t: &Type) -> Type {
        match t {
            Type::T(v) => Type::T(self.traverse_var(*v)),
            Type::I(n) => Type::I(*n),
            Type::F(n) => Type::F(*n),
            Type::Fn(params, retty) => Type::Fn(
                params.iter().map(|t| self.traverse_type(t)).collect(),
                Box::new(self.traverse_type(retty)),
            ),
            Type::Type(v) => Type::Type(self.traverse_var(*v)),
        }
    }

    fn traverse_var(&self, v: Var) -> Var {
        self.renames.get(&v).copied().unwrap_or(v)
    }
}
