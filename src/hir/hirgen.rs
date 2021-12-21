//! AST -> HIR conversion.
use crate::ast::exp::{self, Exp as EExp};
use crate::hir::free_global_vars::*;
use crate::hir::inline_var_alias::*;
use crate::hir::*;
use crate::{symbol, Symbol};

use anyhow::{anyhow, Result};
use once_cell::sync::Lazy;
use std::collections::HashMap;

macro_rules! known_vars {
    ( $($i:ident : $ty:expr ),* ) => {
        $(
            pub static $i: Lazy<Var> = Lazy::new(genglobal);
        )*
        static DEFAULT_TYPES: Lazy<HashMap<Var, Type>> = Lazy::new(|| {
            let mut map = HashMap::new();
            $(
                map.insert(*$i, $ty);
            )*
            map
        });
    };
}
known_vars![
    ANY_T_V: Type::T(*DATATYPE_T_V),
    TYPE_T_V: Type::T(*DATATYPE_T_V),
    DATATYPE_T_V: Type::T(*DATATYPE_T_V),
    SVEC_T_V: Type::T(*DATATYPE_T_V),
    SVEC_EMPTY: Type::T(*SVEC_T_V),
    SYMBOL_T_V: Type::T(*DATATYPE_T_V),
    STRING_T_V: Type::T(*DATATYPE_T_V),
    VOID_T_V: Type::T(*DATATYPE_T_V),
    VOID_V: Type::T(*VOID_T_V),
    I64_T_V: Type::T(*DATATYPE_T_V),
    F64_T_V: Type::T(*DATATYPE_T_V)
];

pub type Env<'a> = crate::env::Env<'a, Var>;

/// Global HirGen context that should be preserved between invocations to hirgen.
#[derive(Debug)]
pub struct HirGen {
    global_env: Env<'static>,
    global_var_types: HashMap<Var, Type>,
}
impl HirGen {
    pub fn new() -> Self {
        HirGen {
            global_env: Env::new(None),
            global_var_types: DEFAULT_TYPES.clone(),
        }
    }

    /// Compile a top-level AST expression to a module.
    ///
    /// The module does not influence future compilations until it is committed with
    /// `HirGen::commit()`. This should be done after the module is compiled to LLVM IR and is
    /// loaded.
    pub fn compile_top_level(&self, e: &exp::Exp) -> Result<Module> {
        Ctx::new(self)
            .exp_to_hir(&self.global_env, e)
            .map(|m| self.close_module(m))
            .map(|m| inline_var_alias(&m))
    }

    /// This function augments the module with type declarations for every referenced external
    /// global.
    ///
    /// So that the module becomes “closed” and LLVM IR gen does not need any further information
    /// from other modules.
    fn close_module(&self, mut m: Module) -> Module {
        let free_vars = free_global_vars(&m);
        for v in free_vars.into_iter() {
            let ty = self
                .global_var_types
                .get(&v)
                .cloned()
                .expect("a free variable to unknown global generated");
            m.decls.push(Decl::Global {
                name: None,
                v,
                ty,
                value: None,
            })
        }
        m
    }

    /// Insert symbol `name` into the global environment and associate it with `v` and type `ty`.
    pub fn insert_global(&mut self, name: Symbol, v: Var, ty: Type) {
        assert!(matches!(v, Var::Global(_)));
        assert!(matches!(ty, Type::T(Var::Global(_))));
        self.global_env.insert(name, v);
        self.insert_global_type(v, ty);
    }

    /// Insert a global variable `v` with type `ty`. Note that it won’t have a symbol name
    /// associated, so the user cannot reference it.
    fn insert_global_type(&mut self, v: Var, ty: Type) {
        match self.global_var_types.insert(v, ty.clone()) {
            None => {}
            Some(prev_ty) => assert_eq!(prev_ty, ty),
        }
    }

    /// Add [`Module`] to the global scope. This should be called for all modules that have been
    /// successfully loaded by JIT.
    pub fn commit(&mut self, module: &Module) {
        for d in &module.decls {
            match d {
                Decl::Global {
                    name: Some(name),
                    v,
                    ty,
                    value: _,
                } => {
                    self.insert_global(*name, *v, ty.clone());
                }
                Decl::Global {
                    name: None,
                    v,
                    ty,
                    value: _,
                } => {
                    self.insert_global_type(*v, ty.clone());
                }
                Decl::AddMethod { .. } => {}
                Decl::Main(..) => {}
            }
        }
    }
}

/// A compilation context for a single [`Module`] (top-level expression in Alpha).
#[derive(Debug)]
struct Ctx<'a> {
    hirgen: &'a HirGen,
    module: Module,
}

impl<'a> Ctx<'a> {
    fn new(hirgen: &'a HirGen) -> Self {
        Ctx {
            hirgen,
            module: Module { decls: Vec::new() },
        }
    }

    fn exp_to_hir(mut self, global_env: &Env, exp: &EExp) -> Result<Module> {
        let mut env = Env::new(Some(global_env));
        self.compile_top_level(&mut env, exp)?;
        Ok(self.module)
    }

    fn compile_top_level(&mut self, global_env: &mut Env, exp: &EExp) -> Result<()> {
        match exp {
            EExp::Type(def) => {
                let v = self.compile_type(global_env, def)?;
                global_env.insert(def.name, v);
            }
            EExp::Function(f) => {
                // global fn -> add method
                let fn_t = self.ensure_fn_t(global_env, f.prototype.name)?;
                if f.body.is_some() {
                    // if there is no body -> declare the function, but do not attach any methods
                    let method = self.compile_global_fn(global_env, f)?;
                    self.module.decls.push(Decl::AddMethod { ty: fn_t, method });
                }
            }
            e => {
                // some expression -> compile anonymous fn
                let v = genglobal();
                self.module.decls.push(Decl::Global {
                    name: None,
                    v,
                    ty: Type::Fn(vec![], Box::new(Type::T(*ANY_T_V))),
                    value: Some(Exp::Fn(Fn {
                        params: vec![],
                        retty: Type::T(*ANY_T_V),
                        body: Box::new(self.compile_exp(global_env, e)?),
                    })),
                });
                self.module.decls.push(Decl::Main(v));
            }
        }
        Ok(())
    }

    fn compile_global_fn(&mut self, global_env: &mut Env, f: &exp::Function) -> Result<Var> {
        let exp::Function {
            prototype:
                exp::FunctionPrototype {
                    name: _,
                    params,
                    result_type,
                },
            body,
        } = f;

        let v = genglobal();

        // TODO: if we're adding a constructor, this has to be a Type::Type
        let this_t = Type::T(*ANY_T_V);
        let fn_params = std::iter::once(Ok((genvar(), this_t)))
            .chain(
                params
                    .iter()
                    .map(|p| Ok((genvar(), self.lookup_type(global_env, p.typ)?))),
            )
            .collect::<Result<Vec<_>>>()?;
        let retty = self.lookup_type(global_env, *result_type)?;

        let ty = Type::Fn(
            fn_params.iter().map(|(_v, ty)| ty.clone()).collect(),
            Box::new(retty.clone()),
        );

        let value = body
            .as_ref()
            .map(|body| -> Result<_> {
                let mut env = Env::new(Some(global_env));
                for (p, (v, _t)) in params.iter().zip(fn_params.iter().skip(1)) {
                    env.insert(p.name, *v);
                }

                let body = Box::new(self.compile_exp(&env, &body)?);

                let f = Fn {
                    params: fn_params,
                    retty,
                    body,
                };

                Ok(Exp::Fn(f))
            })
            .transpose()?;

        self.module.decls.push(Decl::Global {
            name: None,
            v,
            ty,
            value,
        });

        Ok(v)
    }

    fn compile_exp(&self, env: &Env, e: &exp::Exp) -> Result<Exp> {
        let res = match e {
            exp::Exp::Call(exp::Call { fun, args }) => {
                let f_v = genvar();
                let f_value = Box::new(self.compile_exp(env, fun)?);
                Exp::Let {
                    v: f_v,
                    ty: Type::T(*ANY_T_V),
                    value: f_value,
                    e: Box::new(self.compile_exps(env, args, |_env, args| {
                        let mut actual_args = Vec::new();
                        actual_args.push(f_v);
                        actual_args.extend_from_slice(args);

                        let args_v = genvar();
                        let method_instance_v = genvar();

                        Ok(Exp::Let {
                            v: args_v,
                            ty: Type::T(*SVEC_T_V),
                            value: Box::new(Exp::Vector(actual_args)),
                            e: Box::new(Exp::Let {
                                v: method_instance_v,
                                ty: Type::Fn(vec![Type::T(*SVEC_T_V)], Box::new(Type::T(*ANY_T_V))),
                                value: Box::new(Exp::MethodSelect { args: args_v }),
                                e: Box::new(Exp::Apply {
                                    f: method_instance_v,
                                    args: vec![args_v],
                                }),
                            }),
                        })
                    })?),
                }
            }
            exp::Exp::Symbol(name) => {
                let v = env
                    .lookup(*name)
                    .ok_or_else(|| anyhow!("unable to lookup symbol {}", name))?;
                Exp::Var(*v)
            }
            exp::Exp::Integer(n) => {
                let v = genvar();
                Exp::Let {
                    v,
                    ty: Type::I(64),
                    value: Box::new(Exp::NumberLiteral(Type::I(64), n.to_string())),
                    e: Box::new(Exp::Object {
                        ty: *I64_T_V,
                        fields: vec![v],
                    }),
                }
            }
            exp::Exp::Float(n) => {
                let v = genvar();
                Exp::Let {
                    v,
                    ty: Type::F(64),
                    value: Box::new(Exp::NumberLiteral(Type::F(64), n.to_string())),
                    e: Box::new(Exp::Object {
                        ty: *F64_T_V,
                        fields: vec![v],
                    }),
                }
            }
            exp::Exp::String(s) => Exp::StringLiteral(s.clone()),
            exp::Exp::Block(es) => self.compile_block(env, es)?,

            exp::Exp::Type(_) => todo!("non-top-level types are not supported yet"),
            exp::Exp::Function(_) => todo!("non-top-level functions are not supported yet"),
        };

        Ok(res)
    }

    fn compile_exps<F>(&self, env: &Env, es: &[exp::Exp], and_then: F) -> Result<Exp>
    where
        F: FnOnce(&Env, &[Var]) -> Result<Exp>,
    {
        let es = es
            .iter()
            .map(|e| self.compile_exp(env, e))
            .collect::<Result<Vec<_>>>()?;
        let vars = es.iter().map(|_| genvar()).collect::<Vec<_>>();
        let e = and_then(env, &vars)?;

        let result = vars
            .into_iter()
            .zip(es.into_iter())
            .rfold(e, |result, (v, value)| Exp::Let {
                v,
                ty: Type::T(*ANY_T_V),
                value: Box::new(value),
                e: Box::new(result),
            });
        Ok(result)
    }

    fn compile_exps_rest(&self, env: &Env, es: &[exp::Exp], or_else: Var) -> Result<Exp> {
        match es {
            [] => Ok(Exp::Var(or_else)),
            [e, rest @ ..] => {
                let v = genvar();
                let value = Box::new(self.compile_exp(env, e)?);
                let e = Box::new(self.compile_exps_rest(env, rest, v)?);
                Ok(Exp::Let {
                    v,
                    // TODO: typing
                    ty: Type::T(*ANY_T_V),
                    value,
                    e,
                })
            }
        }
    }
    fn compile_block(&self, env: &Env, es: &[exp::Exp]) -> Result<Exp> {
        let v = genvar();
        let value = Box::new(Exp::Var(*VOID_V));
        let e = Box::new(self.compile_exps_rest(env, es, v)?);
        Ok(Exp::Let {
            v,
            ty: Type::T(*VOID_T_V),
            value,
            e,
        })
    }

    fn compile_type(&mut self, env: &mut Env, def: &exp::TypeDefinition) -> Result<Var> {
        // global type -> allocate type object + constructors and accessor functions
        let v = genglobal();

        let typedef = self.to_typedef(env, def)?;

        self.module.decls.push(Decl::Global {
            name: Some(def.name),
            v,
            ty: Type::T(*DATATYPE_T_V),
            value: Some(Exp::DataType(typedef.clone())),
        });

        self.compile_constructor(env, v, &typedef)?;
        self.compile_accessors(env, v, &typedef)?;

        Ok(v)
    }

    fn compile_constructor(&mut self, _env: &mut Env, ty: Var, typedef: &TypeDef) -> Result<Var> {
        let f = genglobal();
        let fields = typedef
            .fields
            .iter()
            .map(|field| (genvar(), field))
            .collect::<Vec<_>>();
        self.module.decls.push(Decl::Global {
            name: None,
            v: f,
            ty: Type::Fn(
                std::iter::once(Type::Type(ty))
                    .chain(typedef.fields.iter().map(|(_name, ty)| ty).cloned())
                    .collect(),
                Box::new(Type::T(ty)),
            ),
            value: Some(Exp::Fn(Fn {
                params: std::iter::once((genvar(), Type::Type(ty)))
                    .chain(fields.iter().map(|(v, (_name, ty))| (*v, ty.clone())))
                    .collect(),
                retty: Type::T(ty),
                body: Box::new(Exp::Object {
                    ty,
                    fields: fields.iter().map(|(v, (_name, _ty))| *v).collect(),
                }),
            })),
        });
        self.module.decls.push(Decl::AddMethod {
            ty: *DATATYPE_T_V,
            method: f,
        });
        Ok(f)
    }

    fn compile_accessors(&mut self, env: &mut Env, ty: Var, typedef: &TypeDef) -> Result<()> {
        for (i, (name, t)) in typedef.fields.iter().enumerate() {
            let fn_t = self.ensure_fn_t(env, *name)?;

            let v = genglobal();
            let this = genvar();
            self.module.decls.push(Decl::Global {
                name: None,
                v,
                ty: Type::Fn(vec![Type::T(*ANY_T_V), Type::T(ty)], Box::new(t.clone())),
                value: Some(Exp::Fn(Fn {
                    params: vec![(genvar(), Type::T(*ANY_T_V)), (this, Type::T(ty))],
                    retty: t.clone(),
                    body: Box::new(Exp::Select {
                        value: this,
                        field: i,
                    }),
                })),
            });

            self.module.decls.push(Decl::AddMethod {
                ty: fn_t,
                method: v,
            });
        }

        Ok(())
    }

    fn var_type(&self, var: Var) -> Result<Type> {
        self.hirgen
            .global_var_types
            .get(&var)
            .or_else(|| {
                self.module.decls.iter().find_map(|d| match d {
                    Decl::Global { v, ty, .. } if *v == var => Some(ty),
                    _ => None,
                })
            })
            .cloned()
            .ok_or_else(|| anyhow!("unable to get var type for {:?}", var))
    }

    fn ensure_fn_t(&mut self, env: &mut Env, name: Symbol) -> Result<Var> {
        let fn_obj = match env.lookup(name).cloned() {
            Some(fn_obj) => fn_obj,
            None => {
                let fn_t = genglobal();
                self.module.decls.push(Decl::Global {
                    name: None,
                    v: fn_t,
                    ty: Type::T(*DATATYPE_T_V),
                    value: Some(Exp::DataType(TypeDef {
                        name: symbol(&format!("typeof({})", name)),
                        superty: *ANY_T_V,
                        is_abstract: false,
                        fields: vec![],
                    })),
                });

                let fn_obj = genglobal();
                self.module.decls.push(Decl::Global {
                    name: Some(name),
                    v: fn_obj,
                    ty: Type::T(fn_t),
                    value: Some(Exp::Object {
                        ty: fn_t,
                        fields: vec![],
                    }),
                });
                env.insert(name, fn_obj);

                fn_obj
            }
        };

        let fn_ty = self.var_type(fn_obj)?;
        let fn_t = match fn_ty {
            Type::T(v) => v,
            _ => panic!("ensure_fn_t: wrong function type: {:?}", fn_ty),
        };

        Ok(fn_t)
    }

    fn to_typedef(&self, env: &Env, def: &exp::TypeDefinition) -> Result<TypeDef> {
        let name = def.name;
        let superty = env
            .lookup(def.supertype)
            .copied()
            .ok_or_else(|| anyhow!("unable to lookup: {}", def.supertype))?;
        let typedef = match &def.specifier {
            exp::TypeSpecifier::Abstract => TypeDef {
                name,
                superty,
                is_abstract: true,
                fields: vec![],
            },
            exp::TypeSpecifier::Integer(bits) => TypeDef {
                name,
                superty,
                is_abstract: false,
                fields: vec![(symbol("value"), Type::I(*bits))],
            },
            exp::TypeSpecifier::Float(bits) => TypeDef {
                name,
                superty,
                is_abstract: false,
                fields: vec![(symbol("value"), Type::F(*bits))],
            },
            exp::TypeSpecifier::Struct(field_specs) => {
                let fields = field_specs
                    .iter()
                    .map(|exp::StructFieldSpecifier { name, typ }| -> Result<_> {
                        Ok((*name, self.lookup_type(env, *typ)?))
                    })
                    .collect::<Result<_>>()?;
                TypeDef {
                    name,
                    superty,
                    is_abstract: false,
                    fields,
                }
            }
        };
        Ok(typedef)
    }

    fn lookup_type(&self, env: &Env, name: Symbol) -> Result<Type> {
        env.lookup(name)
            .map(|ev| Type::T(*ev))
            .ok_or_else(|| anyhow!("unable to find type: {}", name))
    }
}
