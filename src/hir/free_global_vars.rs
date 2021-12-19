//! An analysis pass that collects any *external* global referenced in the module. (i.e., a global
//! that is not declared in the module.)
use crate::hir::*;

use std::collections::HashSet;

pub fn free_global_vars(m: &Module) -> HashSet<Var> {
    let mut free_vars = HashSet::new();

    for d in &m.decls {
        traverse_decl(&mut free_vars, d);
    }
    for d in &m.decls {
        if let Decl::Global { v, .. } = d {
            free_vars.remove(v);
        }
    }

    free_vars
}

fn traverse_decl(free_vars: &mut HashSet<Var>, d: &Decl) {
    match d {
        Decl::Global {
            name: _,
            v: _,
            ty,
            value,
        } => {
            traverse_type(free_vars, ty);
            value.iter().for_each(|e| traverse_exp(free_vars, e));
        }
        Decl::AddMethod { ty, method } => {
            traverse_var(free_vars, *ty);
            traverse_var(free_vars, *method);
        }
        Decl::Main(v) => {
            traverse_var(free_vars, *v);
        }
    }
}

fn traverse_type(free_vars: &mut HashSet<Var>, t: &Type) {
    match t {
        Type::T(v) => traverse_var(free_vars, *v),
        Type::I(_) => {}
        Type::F(_) => {}
        Type::Fn(params, retty) => {
            params.iter().for_each(|t| traverse_type(free_vars, t));
            traverse_type(free_vars, retty);
        }
        Type::Type(v) => traverse_var(free_vars, *v),
    };
}

fn traverse_exp(free_vars: &mut HashSet<Var>, e: &Exp) {
    match e {
        Exp::StringLiteral(_) => {}
        Exp::NumberLiteral(ty, _) => {
            traverse_type(free_vars, ty);
        }
        Exp::Vector(vars) => {
            vars.iter().for_each(|v| traverse_var(free_vars, *v));
        }
        Exp::Object { ty, fields } => {
            traverse_var(free_vars, *ty);
            fields.iter().for_each(|v| traverse_var(free_vars, *v));
        }
        Exp::Select { value, field: _ } => {
            traverse_var(free_vars, *value);
        }
        Exp::MethodSelect { args } => {
            traverse_var(free_vars, *args);
        }
        Exp::DataType(typedef) => {
            traverse_typedef(free_vars, typedef);
        }
        Exp::Let { v, ty, value, e } => {
            traverse_var(free_vars, *v);
            traverse_type(free_vars, ty);
            traverse_exp(free_vars, value);
            traverse_exp(free_vars, e);
        }
        Exp::Var(v) => traverse_var(free_vars, *v),
        Exp::Fn(f) => traverse_fn(free_vars, f),
        Exp::Apply { f, args } => {
            traverse_var(free_vars, *f);
            args.iter().for_each(|v| traverse_var(free_vars, *v));
        }
    }
}

fn traverse_typedef(free_vars: &mut HashSet<Var>, typedef: &TypeDef) {
    let TypeDef {
        name: _,
        superty,
        is_abstract: _,
        fields,
    } = typedef;
    traverse_var(free_vars, *superty);
    fields
        .iter()
        .for_each(|(_name, ty)| traverse_type(free_vars, ty));
}

fn traverse_fn(free_vars: &mut HashSet<Var>, f: &Fn) {
    let Fn {
        params,
        retty,
        body,
    } = f;
    params.iter().for_each(|(v, ty)| {
        traverse_var(free_vars, *v);
        traverse_type(free_vars, ty);
    });
    traverse_type(free_vars, retty);
    traverse_exp(free_vars, body);
}

fn traverse_var(free_vars: &mut HashSet<Var>, v: Var) {
    if matches!(v, Var::Global(_)) {
        free_vars.insert(v);
    }
}
