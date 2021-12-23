//! HIR -> LLVM IR generator.
use crate::hir::{self, *};
use crate::types::*;

use anyhow::{anyhow, bail, Context as AnyhowContext, Result};
use llvm::builder::Builder;
use llvm::context::Context;
use llvm::module::Module;
use llvm::types::{AddressSpace, Type, TypeKind};
use llvm::values::Value;
use std::collections::HashMap;
use std::mem::size_of;
use tracing::{self, error, trace};

/// A single-module HIR to LLVM IR compiler.
pub struct IrGen<'a, 'ctx> {
    context: &'ctx Context,
    input: &'a hir::Module,
    module: Module,
}

/// A single-function compiler context.
struct FnGen<'a, 'ctx> {
    irgen: &'a IrGen<'a, 'ctx>,
    context: &'ctx Context,
    module: &'a Module,
    prologue_builder: Builder,
    builder: Builder,
    epilogue_builder: Builder,
    vars: HashMap<Var, Value>,
}

impl<'a, 'ctx> IrGen<'a, 'ctx> {
    pub fn bootstrap_context(context: &'ctx Context) {
        let any_t = context.create_named_struct_type(&Self::var_to_type_name(*hir::ANY_T_V));
        let type_t = context.create_named_struct_type(&Self::var_to_type_name(*hir::TYPE_T_V));
        let symbol_t = context.create_named_struct_type(&Self::var_to_type_name(*hir::SYMBOL_T_V));
        let datatype_t =
            context.create_named_struct_type(&Self::var_to_type_name(*hir::DATATYPE_T_V));
        let svec_t = context.create_named_struct_type(&Self::var_to_type_name(*hir::SVEC_T_V));
        let string_t = context.create_named_struct_type(&Self::var_to_type_name(*hir::STRING_T_V));
        let void_t = context.create_named_struct_type(&Self::var_to_type_name(*hir::VOID_T_V));
        let i64_t = context.create_named_struct_type(&Self::var_to_type_name(*hir::I64_T_V));
        let f64_t = context.create_named_struct_type(&Self::var_to_type_name(*hir::F64_T_V));

        datatype_t.struct_set_body(
            &[
                /* size: */ context.int_type(64),
                /* name: */ symbol_t.pointer_type(AddressSpace::Generic),
                /* supertype: */ datatype_t.pointer_type(AddressSpace::Generic),
                /* is_abstract: */ context.int_type(1),
                /* methods: */ svec_t.pointer_type(AddressSpace::Generic),
                /* n_ptrs: */ context.int_type(64),
                /* pointers: */ context.int_type(64).array_type(0),
            ],
            false,
        );
        type_t.struct_set_body(
            &[/* t: */ datatype_t.pointer_type(AddressSpace::Generic)],
            false,
        );
        symbol_t.struct_set_body(
            &[
                /* hash: */ context.int_type(64),
                /* left: */ symbol_t.pointer_type(AddressSpace::Generic),
                /* right: */ symbol_t.pointer_type(AddressSpace::Generic),
                /* len: */ context.int_type(64),
                /* name: */ context.int_type(8).array_type(0),
            ],
            false,
        );
        svec_t.struct_set_body(
            &[
                /* size: */ context.int_type(64),
                /* elements: */ any_t.pointer_type(AddressSpace::Generic).array_type(0),
            ],
            false,
        );
        string_t.struct_set_body(
            &[
                /* size: */ context.int_type(64),
                /* bytes: */ context.int_type(8).array_type(0),
            ],
            false,
        );
        void_t.struct_set_body(&[], false);
        i64_t.struct_set_body(&[/* #value: */ context.int_type(64)], false);
        f64_t.struct_set_body(&[/* #value: */ context.float_type(64)], false);
    }

    #[tracing::instrument(skip_all)]
    pub fn compile(context: &'ctx Context, input: &'a hir::Module) -> Result<(Module, String)> {
        IrGen {
            context,
            input,
            module: context.create_module(""),
        }
        .compile_module()
    }

    fn compile_module(mut self) -> Result<(Module, String)> {
        self.declare_types()?;
        self.declare_well_knowns()?;
        self.declare_globals()?;
        self.compile_functions()?;
        let entry_var = self.compile_entry_point()?;
        let entry_name = Self::var_to_global_name(entry_var);

        trace!("compiled module: {:?}", self.module);
        match self.module.verify() {
            Ok(()) => Ok((self.module, entry_name)),
            Err(err) => {
                error!("module verification failed: {:?}", err);
                bail!("module verification failed");
            }
        }
    }

    fn declare_well_knowns(&mut self) -> Result<()> {
        let any_t = self.resolve_type(&hir::Type::T(*ANY_T_V))?;
        let svec_t = self.resolve_type(&hir::Type::T(*SVEC_T_V))?;
        let string_t = self.resolve_type(&hir::Type::T(*STRING_T_V))?;
        let datatype_t = self.resolve_type(&hir::Type::T(*DATATYPE_T_V))?;

        self.module
            .add_global(&Self::var_to_global_name(*hir::TYPE_T_V), datatype_t);
        self.module
            .add_global(&Self::var_to_global_name(*hir::SVEC_T_V), datatype_t);
        self.module
            .add_global(&Self::var_to_global_name(*hir::SVEC_EMPTY), svec_t);
        self.module.add_function(
            "gc_allocate",
            any_t.function_type(&[self.context.int_type(64)], false),
        );
        self.module.add_function(
            "select_method",
            any_t
                .function_type(&[svec_t], false)
                .pointer_type(AddressSpace::Generic)
                .function_type(&[svec_t], false),
        );
        self.module.add_function(
            "mk_str",
            string_t.function_type(
                &[
                    self.context.int_type(8).pointer_type(AddressSpace::Generic),
                    self.context.int_type(64),
                ],
                false,
            ),
        );
        self.module.add_function(
            "add_global_root",
            self.context
                .void_type()
                .function_type(&[any_t.pointer_type(AddressSpace::Generic)], false),
        );
        self.module.add_function(
            "add_method",
            self.context.void_type().function_type(
                &[
                    datatype_t,
                    svec_t,
                    any_t
                        .function_type(&[svec_t], false)
                        .pointer_type(AddressSpace::Generic),
                ],
                false,
            ),
        );

        Ok(())
    }

    fn declare_types(&mut self) -> Result<()> {
        for d in &self.input.decls {
            if let hir::Decl::Global {
                name: _,
                v,
                ty,
                value: Some(hir::Exp::DataType(typedef)),
            } = d
            {
                assert_eq!(ty, &hir::Type::T(*hir::DATATYPE_T_V));
                self.declare_type(*v, typedef)?;
            }
        }
        Ok(())
    }

    fn declare_globals(&mut self) -> Result<()> {
        for d in &self.input.decls {
            if let hir::Decl::Global {
                name: _,
                v,
                ty,
                value,
            } = d
            {
                let name = Self::var_to_global_name(*v);
                if get_any_global(&self.module, &name).is_some() {
                    // already declared
                } else {
                    let ty = self.resolve_type(ty)?;
                    match value {
                        Some(hir::Exp::Fn(..)) => {
                            let f = self.module.add_function(&name, ty);
                            f.set_gc("shadow-stack");
                        }
                        Some(hir::Exp::GlobalRef(..)) => {
                            // Do nothing.
                            //
                            // GlobalRef is used to declare an alias—they are resolved in
                            // `var_place()`.
                        }
                        value => {
                            let g = self.module.add_global(&name, ty);
                            if value.is_some() {
                                g.global_set_initializer(ty.const_null());
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn compile_functions(&mut self) -> Result<()> {
        for d in &self.input.decls {
            if let hir::Decl::Global {
                name: _,
                v,
                ty: _,
                value: Some(Exp::Fn(f)),
            } = d
            {
                let llvm_fn = self
                    .module
                    .get_function(&Self::var_to_global_name(*v))
                    .expect("unable to get function");
                self.compile_fn(llvm_fn, f)?;
            }
        }
        Ok(())
    }

    fn compile_entry_point(&mut self) -> Result<Var> {
        let v = hir::genglobal();
        let f = self.module.add_function(
            &Self::var_to_global_name(v),
            self.resolve_type(&hir::Type::Fn(vec![], Box::new(hir::Type::T(*ANY_T_V))))?,
        );
        f.set_gc("shadow-stack");

        FnGen {
            irgen: self,
            context: self.context,
            module: &self.module,
            prologue_builder: self.context.create_builder(),
            builder: self.context.create_builder(),
            epilogue_builder: self.context.create_builder(),
            vars: HashMap::new(),
        }
        .compile_entry_point(f)?;

        Ok(v)
    }

    fn compile_fn(&mut self, llvm_fn: Value, f: &hir::Fn) -> Result<()> {
        FnGen {
            irgen: self,
            context: self.context,
            module: &self.module,
            prologue_builder: self.context.create_builder(),
            builder: self.context.create_builder(),
            epilogue_builder: self.context.create_builder(),
            vars: HashMap::new(),
        }
        .compile_fn(llvm_fn, f)
    }

    #[tracing::instrument(skip(self))]
    fn declare_type(&mut self, v: Var, typedef: &TypeDef) -> Result<()> {
        let ty = self
            .context
            .create_named_struct_type(&Self::var_to_type_name(v));
        if typedef.is_abstract {
            // abstract types remain opaque
        } else {
            let fields = self.typedef_to_fields(typedef)?;
            ty.struct_set_body(&fields, false);
        }
        trace!("declared type: {:?}", ty);
        Ok(())
    }
    fn typedef_to_fields(&self, typedef: &TypeDef) -> Result<Vec<Type>> {
        let mut fields = vec![];
        for (_name, field_type) in &typedef.fields {
            // TODO: handle fields inlining
            fields.push(self.resolve_type(field_type)?);
        }
        Ok(fields)
    }

    fn resolve_type(&self, t: &hir::Type) -> Result<Type> {
        let ty = match t {
            hir::Type::T(v) => self
                .context
                .get_named_struct(&Self::var_to_type_name(*v))
                .with_context(|| format!("Failed to lookup type for {:?}", v))?
                // all user types are currently boxed
                .pointer_type(AddressSpace::Generic),
            hir::Type::I(n) => self.context.int_type(*n as u32),
            hir::Type::F(n) => self.context.float_type(*n as u32),
            hir::Type::Fn(
                // We do not care about parameter and return types, because in Alpha calling
                // convention every function receives a single SVec and returns Any.
                _params,
                _retty,
            ) => {
                let any_t = self
                    .context
                    .get_named_struct(&Self::var_to_type_name(*hir::ANY_T_V))
                    .expect("unable to lookup Any")
                    .pointer_type(AddressSpace::Generic);
                let svec_t = self
                    .context
                    .get_named_struct(&Self::var_to_type_name(*hir::SVEC_T_V))
                    .expect("unable to lookup SVec")
                    .pointer_type(AddressSpace::Generic);
                any_t.function_type(&[svec_t], false)
            }
            hir::Type::Type(_) => self.resolve_type(&hir::Type::T(*hir::DATATYPE_T_V))?,
        };
        Ok(ty)
    }

    fn var_to_type_name(v: Var) -> String {
        match v {
            Var::Global(n) => format!("t{}", n),
            Var::Local(_) => panic!("var_to_type_name(): called on local var {:?}", v),
        }
    }
    pub fn var_to_global_name(v: Var) -> String {
        match v {
            Var::Global(n) => format!("g{}", n),
            Var::Local(_) => panic!("var_to_global_name(): called on local var {:?}", v),
        }
    }
}

impl<'a, 'ctx> FnGen<'a, 'ctx> {
    fn compile_fn(mut self, fn_val: Value, f: &hir::Fn) -> Result<()> {
        self.init_function(fn_val);
        self.build_prologue(fn_val, f)?;
        let result = self.compile_exp(&f.body, "result")?;
        let any_t = self.irgen.resolve_type(&hir::Type::T(*ANY_T_V))?;
        let result = self
            .builder
            .build_pointer_cast(result, any_t, "result.as_any");
        self.epilogue_builder.build_ret(result);

        Ok(())
    }

    fn compile_entry_point(mut self, fn_val: Value) -> Result<()> {
        self.init_function(fn_val);

        let any_t = self.irgen.resolve_type(&hir::Type::T(*ANY_T_V))?;
        let svec_t = self.irgen.resolve_type(&hir::Type::T(*SVEC_T_V))?;

        // add global roots
        let add_global_root = self.module.get_function("add_global_root").unwrap();
        for d in &self.irgen.input.decls {
            if let hir::Decl::Global { v, ty, value, .. } = d {
                if !matches!(ty, hir::Type::Fn(..)) && value.is_some() {
                    let g = self
                        .module
                        .get_global(&IrGen::var_to_global_name(*v))
                        .unwrap();
                    let g = self.builder.build_pointer_cast(
                        g,
                        any_t.pointer_type(AddressSpace::Generic),
                        "",
                    );
                    self.builder.build_call(add_global_root, &[g], "");
                }
            }
        }

        // initialize globals
        for d in &self.irgen.input.decls {
            match d {
                hir::Decl::Global {
                    name: _,
                    v,
                    ty: _,
                    value: Some(value),
                } if !matches!(value, hir::Exp::Fn(..))
                    && !matches!(value, hir::Exp::GlobalRef(..)) =>
                {
                    let v_name = Self::var_name(*v);
                    let value = self.compile_exp(value, &format!("{}.in", v_name))?;
                    let g = self.var_place(*v);
                    // TODO: remove this cast when hirgen can generate proper types for global vars
                    let value = self.builder.build_pointer_cast(
                        value,
                        g.get_type().element_type(),
                        &format!("{}.in.as_target", v_name),
                    );
                    self.builder.build_store(g, value);
                }
                _ => {}
            }
        }

        // register methods
        for d in &self.irgen.input.decls {
            if let hir::Decl::AddMethod { ty, method } = d {
                let signature = self.compile_signature(*method)?;
                let datatype = self.var_value(*ty);
                let method = self.var_value(*method);
                let add_method = self.module.get_function("add_method").unwrap();
                self.builder
                    .build_call(add_method, &[datatype, signature, method], "");
            }
        }

        // call main
        let main = self.irgen.input.decls.iter().find_map(|d| match d {
            hir::Decl::Main(v) => Some(*v),
            _ => None,
        });
        match main {
            Some(v) => {
                let f = self
                    .module
                    .get_function(&IrGen::var_to_global_name(v))
                    .unwrap();
                let result = self.builder.build_call(f, &[svec_t.const_null()], "result");
                self.epilogue_builder.build_ret(result);
            }
            None => {
                self.epilogue_builder.build_ret(any_t.const_null());
            }
        }

        Ok(())
    }

    fn init_function(&mut self, f: Value) {
        let prologue = self.context.append_basic_block(f, "prologue");
        let main = self.context.append_basic_block(f, "main");
        let epilogue = self.context.append_basic_block(f, "epilogue");

        self.prologue_builder.position_at_end(prologue);
        let br_main = self.prologue_builder.build_br(main);
        self.prologue_builder.position_before(br_main);

        self.builder.position_at_end(main);
        let br_epi = self.builder.build_br(epilogue);
        self.builder.position_before(br_epi);

        self.epilogue_builder.position_at_end(epilogue);
    }

    fn build_prologue(&mut self, fn_val: Value, f: &hir::Fn) -> Result<()> {
        let mut params = fn_val.get_param_iter();
        let args = params.next().unwrap();
        args.set_name("args");

        let args =
            self.prologue_builder
                .build_struct_gep(args, 1 /* elements */, "args.elements");
        for (i, (v, ty)) in f.params.iter().enumerate() {
            let name = Self::var_name(*v);
            let p = self.prologue_builder.build_gep(
                args,
                &[
                    self.context.int_type(64).const_int(0, false),
                    self.context.int_type(64).const_int(i as u64, false),
                ],
                &format!("args.{}", i),
            );
            let p = self.prologue_builder.build_load(p, &format!("{}.in", name));
            let ty = self.irgen.resolve_type(ty)?;
            let p = self.prologue_builder.build_pointer_cast(p, ty, "");
            let gcroot = self.build_gcroot(ty, &name);
            self.prologue_builder.build_store(gcroot, p);
            self.vars.insert(*v, gcroot);
        }

        Ok(())
    }

    fn compile_signature(&mut self, f: Var) -> Result<Value> {
        let params = self
            .irgen
            .input
            .decls
            .iter()
            .find_map(|d| match d {
                hir::Decl::Global {
                    v,
                    ty: hir::Type::Fn(params, _retty),
                    ..
                } if *v == f => Some(params),
                _ => None,
            })
            .unwrap();

        let params = params
            .iter()
            .map(|p| {
                let e = match p {
                    hir::Type::T(v) => hir::Exp::Var(*v),
                    hir::Type::Type(v) => hir::Exp::Object {
                        ty: *hir::TYPE_T_V,
                        fields: vec![*v],
                    },
                    t => panic!("unexpected type specifier: {:?}", t),
                };
                (hir::genvar(), e)
            })
            .collect::<Vec<_>>();

        let last = hir::Exp::Vector(params.iter().map(|(v, _e)| *v).collect());
        let exp = params
            .into_iter()
            .rfold(last, |and_then, (v, value)| hir::Exp::Let {
                v,
                ty: hir::Type::T(*hir::ANY_T_V),
                value: Box::new(value),
                e: Box::new(and_then),
            });

        trace!("compiling signature: {:?}", exp);

        self.compile_exp(&exp, &format!("{}.signature", Self::var_name(f)))
    }

    fn compile_exp(&mut self, e: &Exp, name: &str) -> Result<Value> {
        let result = match e {
            Exp::StringLiteral(s) => self.build_string_literal(s, name)?,
            Exp::NumberLiteral(ty, s) => match ty {
                hir::Type::I(n) => self
                    .context
                    .int_type(*n as u32)
                    .const_int(s.parse::<u64>().unwrap(), false),
                hir::Type::F(n) => self
                    .context
                    .float_type(*n as u32)
                    .const_float(s.parse::<f64>().unwrap()),
                ty => panic!("wrong type specified for number literal: {:?}", ty),
            },
            Exp::Vector(elements) => self.build_svec(elements, name)?,
            Exp::Object { ty, fields } => {
                let t = self
                    .context
                    .get_named_struct(&IrGen::var_to_type_name(*ty))
                    .ok_or_else(|| anyhow!("unable to find type {:?}", ty))?;

                let value = self.build_dyn_allocate(t.size(), &format!("{}.alloc", name));
                let value = self.builder.build_pointer_cast(
                    value,
                    t.pointer_type(AddressSpace::Generic),
                    name,
                );

                let ty = self.var_value(*ty);
                self.build_set_typetag(value, ty)?;

                for (i, f) in fields.iter().enumerate() {
                    let field_ptr =
                        self.builder
                            .build_struct_gep(value, i as u32, &format!("{}.{}", name, i));
                    let field_value = self.var_value(*f);
                    self.builder.build_store(field_ptr, field_value);
                }

                value
            }
            Exp::Select { value, field } => {
                let value = self.var_value(*value);
                let ptr = self.builder.build_struct_gep(value, *field as u32, "");
                self.builder.build_load(ptr, name)
            }
            Exp::MethodSelect { args } => {
                let select_method = self.module.get_function("select_method").unwrap();
                let args = self.var_value(*args);
                self.builder.build_call(select_method, &[args], name)
            }
            Exp::DataType(typedef) => self.compile_datatype(typedef, name)?,
            Exp::Let { v, ty: _, value, e } => {
                let v_name = Self::var_name(*v);
                let value = self.compile_exp(value, &format!("{}.in", v_name))?;

                let ty = value.get_type();
                let value = if ty.kind() == TypeKind::LLVMPointerTypeKind
                    && ty.element_type().kind() != TypeKind::LLVMFunctionTypeKind
                {
                    let root = self.build_gcroot(value.get_type(), &v_name);
                    self.builder.build_store(root, value);
                    root
                } else {
                    value
                };

                self.vars.insert(*v, value);

                self.compile_exp(e, name)?
            }
            Exp::Var(v) => {
                let value = self.var_value(*v);
                value.set_name(name);
                value
            }
            Exp::Apply { f, args } => {
                let f = self.var_value(*f);
                let args = args.iter().map(|v| self.var_value(*v)).collect::<Vec<_>>();
                self.builder.build_call(f, &args, name)
            }
            Exp::Fn(_) => bail!("non-top-level fn are not supported yet"),
            Exp::GlobalRef(ty, gname) => {
                let ty = self.irgen.resolve_type(ty)?;
                let g = get_any_global(self.module, gname).map_or_else::<Result<_>, _, _>(
                    || {
                        let g = if ty.kind() == TypeKind::LLVMFunctionTypeKind {
                            self.module.add_function(gname, ty)
                        } else {
                            self.module.add_global(gname, ty)
                        };
                        Ok(g)
                    },
                    Ok,
                )?;
                if ty.kind() == TypeKind::LLVMFunctionTypeKind {
                    g
                } else {
                    self.builder.build_load(g, name)
                }
            }
        };
        Ok(result)
    }

    /// Get or declare a global reference with `name` and type `ty`.
    fn global_ref(&mut self, name: &str, ty: Type) -> Value {
        get_any_global(self.module, name).unwrap_or_else(|| {
            if ty.kind() == TypeKind::LLVMFunctionTypeKind {
                self.module.add_function(name, ty)
            } else {
                self.module.add_global(name, ty)
            }
        })
    }

    fn compile_datatype(&mut self, typedef: &hir::TypeDef, name: &str) -> Result<Value> {
        let datatype_t = self
            .context
            .get_named_struct(&IrGen::var_to_type_name(*hir::DATATYPE_T_V))
            .unwrap();
        let symbol_t = self
            .context
            .get_named_struct(&IrGen::var_to_type_name(*hir::SYMBOL_T_V))
            .unwrap();

        let size = datatype_t.size();
        let size = size.const_add(
            self.context
                .int_type(64)
                .const_int((typedef.fields.len() * size_of::<u64>()) as u64, false),
        );
        let v = self.build_dyn_allocate(size, &format!("{}.alloc", name));
        let v = self.builder.build_pointer_cast(
            v,
            datatype_t.pointer_type(AddressSpace::Generic),
            name,
        );

        let datatype = self.var_value(*hir::DATATYPE_T_V);
        self.build_set_typetag(v, datatype)?;

        let fields = self.irgen.typedef_to_fields(typedef)?;
        let llvm_ty = self.context.struct_type(&fields, false);

        let size = llvm_ty.size();
        let size_ptr = self
            .builder
            .build_struct_gep(v, 0, &format!("{}.size", name));
        self.builder.build_store(size_ptr, size);

        // TODO: this embeds the pointer value into the LLVM IR, which makes IR unportable. It might
        // be better to use some intrinsic for symbols.
        let name_s = self
            .context
            .int_type(64)
            .const_int(typedef.name.node as usize as u64, false)
            .const_int_to_pointer(symbol_t.pointer_type(AddressSpace::Generic));
        let name_ptr = self
            .builder
            .build_struct_gep(v, 1, &format!("{}.name", name));
        self.builder.build_store(name_ptr, name_s);

        let supertype = self.var_value(typedef.superty);
        let supertype_ptr = self
            .builder
            .build_struct_gep(v, 2, &format!("{}.supertype", name));
        self.builder.build_store(supertype_ptr, supertype);

        let is_abstract = self
            .context
            .int_type(1)
            .const_int(typedef.is_abstract as u64, false);
        let is_abstract_ptr = self
            .builder
            .build_struct_gep(v, 3, &format!("{}.is_abstract", name));
        self.builder.build_store(is_abstract_ptr, is_abstract);

        let methods = self.var_value(*hir::SVEC_EMPTY);
        let methods_ptr = self
            .builder
            .build_struct_gep(v, 4, &format!("{}.methods", name));
        self.builder.build_store(methods_ptr, methods);

        let n_ptrs = self
            .context
            .int_type(64)
            .const_int(fields.len() as u64, false);
        let n_ptrs_ptr = self
            .builder
            .build_struct_gep(v, 5, &format!("{}.n_ptrs", name));
        self.builder.build_store(n_ptrs_ptr, n_ptrs);

        let pointers_ptr = self
            .builder
            .build_struct_gep(v, 6, &format!("{}.pointers", name));
        for (i, _f) in fields.iter().enumerate() {
            let ptr_offset = llvm_ty
                .pointer_type(AddressSpace::Generic)
                .const_null()
                .const_in_bounds_gep(
                    llvm_ty,
                    &[
                        self.context.int_type(32).const_int(0, false),
                        self.context.int_type(32).const_int(i as u64, false),
                    ],
                )
                .const_ptr_to_int(self.context.int_type(64));
            let ptr_ptr = self.builder.build_gep(
                pointers_ptr,
                &[
                    self.context.int_type(64).const_int(0, false),
                    self.context.int_type(64).const_int(i as u64, false),
                ],
                &format!("{}.pointers.{}", name, i),
            );
            self.builder.build_store(ptr_ptr, ptr_offset);
        }

        Ok(v)
    }

    fn build_string_literal(&mut self, s: &str, name: &str) -> Result<Value> {
        let len = s.len();
        let s = self
            .builder
            .build_global_string_ptr(s, &format!("{}.literal", name));
        let mk_str = self.module.get_function("mk_str").unwrap();
        let result = self.builder.build_call(
            mk_str,
            &[s, self.context.int_type(64).const_int(len as u64, false)],
            name,
        );
        Ok(result)
    }

    fn build_svec(&mut self, elements: &[Var], name: &str) -> Result<Value> {
        let svec = self.build_allocate(
            (size_of::<SVec>() + size_of::<AnyPtr>() * elements.len()) as u64,
            &format!("{}.in", name),
        );
        let svec_ty = self.irgen.resolve_type(&hir::Type::T(*SVEC_T_V))?;

        let svec = self.builder.build_pointer_cast(svec, svec_ty, name);
        let svec_t = self.var_value(*SVEC_T_V);
        self.build_set_typetag(svec, svec_t)?;

        let i64_t = self.context.int_type(64);
        let any_t = self.irgen.resolve_type(&hir::Type::T(*ANY_T_V))?;

        let len_ptr = self
            .builder
            .build_struct_gep(svec, 0, &format!("{}.len", name));
        self.builder
            .build_store(len_ptr, i64_t.const_int(elements.len() as u64, false));
        let elements_ptr = self
            .builder
            .build_struct_gep(svec, 1, &format!("{}.elements", name));

        for (i, v) in elements.iter().enumerate() {
            let field_ptr = self.builder.build_gep(
                elements_ptr,
                &[i64_t.const_int(0, false), i64_t.const_int(i as u64, false)],
                &format!("{}.{}", name, i),
            );
            let value = self.var_value(*v);
            let value =
                self.builder
                    .build_pointer_cast(value, any_t, &format!("{}.{}.in", name, i));
            self.builder.build_store(field_ptr, value);
        }

        Ok(svec)
    }

    fn build_allocate(&mut self, size: u64, name: &str) -> Value {
        self.build_dyn_allocate(self.context.int_type(64).const_int(size, false), name)
    }
    fn build_dyn_allocate(&mut self, size: Value, name: &str) -> Value {
        self.builder.build_call(
            self.module.get_function("gc_allocate").unwrap(),
            &[size],
            name,
        )
    }

    fn build_set_typetag(&mut self, ptr: Value, tag: Value) -> Result<()> {
        let datatype_t = self.irgen.resolve_type(&hir::Type::T(*DATATYPE_T_V))?;

        let pptr = self.builder.build_pointer_cast(
            ptr,
            datatype_t.pointer_type(AddressSpace::Generic),
            "",
        );
        let typetag_ptr = self.builder.build_gep(
            pptr,
            &[self.context.int_type(64).const_int(-1_i64 as u64, true)],
            &format!("{}.typetag", ptr.get_name()),
        );
        self.builder.build_store(typetag_ptr, tag);

        Ok(())
    }

    fn var_value(&mut self, var: Var) -> Value {
        let place = self.var_place(var);

        let ty = place.get_type();
        if ty.kind() == TypeKind::LLVMPointerTypeKind
            && ty.element_type().kind() != TypeKind::LLVMFunctionTypeKind
        {
            let name = Self::var_name(var);
            self.builder.build_load(place, &format!("{}.value", name))
        } else {
            place
        }
    }
    fn var_place(&mut self, var: Var) -> Value {
        match var {
            Var::Local(_) => *self.vars.get(&var).unwrap(),
            Var::Global(_) => {
                let name = IrGen::var_to_global_name(var);
                get_any_global(self.module, &name)
                    .or_else(|| {
                        self.irgen.input.decls.iter().find_map(|d| match d {
                            hir::Decl::Global {
                                name: _,
                                v,
                                ty: _,
                                value: Some(hir::Exp::GlobalRef(ty, name)),
                            } if *v == var => {
                                let ty = self.irgen.resolve_type(ty).unwrap();
                                Some(self.global_ref(name, ty))
                            }
                            _ => None,
                        })
                    })
                    .ok_or_else(|| anyhow!("var_place(): unable to find place for {:?}", var))
                    .unwrap()
            }
        }
    }

    fn build_gcroot(&mut self, ty: Type, name: &str) -> Value {
        debug_assert_eq!(ty.kind(), TypeKind::LLVMPointerTypeKind);
        let alloca = self.prologue_builder.build_alloca(ty, name);
        let i8_ptr_ptr_t = self
            .context
            .int_type(8)
            .pointer_type(AddressSpace::Generic)
            .pointer_type(AddressSpace::Generic);
        let gcroot = self.prologue_builder.build_pointer_cast(
            alloca,
            i8_ptr_ptr_t,
            &format!("{}.gcroot", name),
        );

        let llvm_gcroot = self.module.get_function("llvm.gcroot").unwrap_or_else(|| {
            let ptr_t = self.context.int_type(8).pointer_type(AddressSpace::Generic);
            self.module.add_function(
                "llvm.gcroot",
                self.context
                    .void_type()
                    .function_type(&[ptr_t.pointer_type(AddressSpace::Generic), ptr_t], false),
            )
        });
        self.prologue_builder.build_call(
            llvm_gcroot,
            &[
                gcroot,
                self.context
                    .int_type(8)
                    .pointer_type(AddressSpace::Generic)
                    .const_null(),
            ],
            "",
        );

        alloca
    }

    fn var_name(v: Var) -> String {
        match v {
            Var::Global(v) => format!("g{}", v),
            Var::Local(v) => format!("v{}", v),
        }
    }
}

fn get_any_global(module: &Module, name: &str) -> Option<Value> {
    module
        .get_global(name)
        .or_else(|| module.get_function(name))
}
