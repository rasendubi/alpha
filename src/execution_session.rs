use std::collections::HashSet;
use std::error::Error;
use std::io::Write;
use std::sync::Mutex;

use once_cell::sync::Lazy;
use simple_error::simple_error;
use tracing::{error, trace};

use llvm::module::Module;
use llvm::orc::lljit::{LLJITBuilder, ResourceTracker, LLJIT};
use llvm::orc::thread_safe::ThreadSafeContext;
use llvm::types::{AddressSpace, Type as LLVMType};
use llvm::values::{LLVMLinkage, Value};

use crate::ast::exp::{self, lower_sexp, Exp};
use crate::ast::parser::Parser;
use crate::ast::types::{TypeDef, TypeDescriptor};
use crate::compiler::Compiler;
use crate::env::Env;
use crate::gc::{self, GcRoot, GcRootChain, GC_ROOT_CHAIN};
use crate::gc_box;
use crate::types::*;

static STDOUT: Lazy<Mutex<Box<dyn Write + Sync + Send>>> =
    Lazy::new(|| Mutex::new(Box::new(std::io::stdout())));

pub fn set_stdout(out: Box<dyn Write + Sync + Send>) {
    let mut stdout = STDOUT.lock().unwrap();
    *stdout = out;
}

// Another option: libunwind provides this function
unsafe extern "C" fn _unwind_resume() {
    panic!("_Unwind_Resume");
}
unsafe extern "C" fn __gcc_personality_v0() {
    panic!("__gcc_personality_v0");
}

unsafe extern "C" fn gc_allocate(size: u64) -> *mut u8 {
    gc::allocate(size as usize)
}

unsafe extern "C" fn mk_str(p: *const u8, len: u64) -> AnyPtr {
    let bytes = std::slice::from_raw_parts(p, len as usize);
    let s = std::str::from_utf8(&bytes).unwrap();
    AlphaString::new(s) as AnyPtr
}

unsafe fn type_of(x: AnyPtr) -> *const DataType {
    let result = *(x as *const *const DataType).sub(1);
    // println!("type_of({:p}) = {:p} (typetag @ {:p})", x, result, x.sub(1));
    result
}

#[tracing::instrument]
unsafe extern "C" fn alpha_f64_mul(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x: *const AlphaF64 = *args.add(1).cast();
    let y: *const AlphaF64 = *args.add(2).cast();
    trace!("alpha_f64_mul({:?}, {:?})", *x, *y);
    let result = (*x).value * (*y).value;
    AlphaF64::allocate(result).cast()
}

#[tracing::instrument]
unsafe extern "C" fn alpha_i64_mul(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x: *const AlphaI64 = *args.add(1).cast();
    let y: *const AlphaI64 = *args.add(2).cast();
    trace!("alpha_i64_mul({:?}, {:?})", *x, *y);
    let result = (*x).value * (*y).value;
    AlphaI64::allocate(result).cast()
}

#[tracing::instrument]
unsafe extern "C" fn alpha_type_of(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x = *args.add(1);
    trace!("alpha_type_of({:?})", x);
    type_of(x) as AnyPtr
}

#[tracing::instrument]
unsafe extern "C" fn alpha_print_any(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = *args.add(1) as AnyPtr;
    trace!("alpha_print_any({:?})", x);
    let type_ = type_of(x);
    write!(stdout, "<{}@{:p}>", (*type_).name, x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
unsafe extern "C" fn alpha_print_void(_n_args: i64, _args: *const AnyPtr) -> AnyPtr {
    trace!("alpha_print_void()");
    // print nothing
    VOID.load() as AnyPtr
}

#[tracing::instrument]
unsafe extern "C" fn alpha_print_i64(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = *(*args.add(1) as *const i64);
    trace!("alpha_print_i64({:?})", x);
    write!(stdout, "{}", x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
unsafe extern "C" fn alpha_print_f64(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = *(*args.add(1) as *const AlphaF64);
    trace!("alpha_print_f64({:?})", x);
    write!(stdout, "{}", x.value).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
unsafe extern "C" fn alpha_print_string(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = *args.add(1) as *const AlphaString;
    trace!("alpha_print_string({:?})", x);
    trace!("x = {:?}", *x);
    write!(stdout, "{}", *x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
unsafe extern "C" fn alpha_print_datatype(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = &*(*args.add(1) as *const DataType);
    trace!("alpha_print_datatype({:?})", x);
    write!(stdout, "{:#?}", x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
unsafe extern "C" fn dispatch(n_args: i64, args: *const AnyPtr) -> AnyPtr {
    // trace!("LLVM_GC_ROOT_CHAIN: {:p}", GC_ROOT_CHAIN);
    // llvm::gc::shadow_stack::visit_roots(GC_ROOT_CHAIN, |ptr, _meta| {
    //     trace!("LLVM ROOT: {:p}", ptr);
    //     gc::debug_ptr(ptr.cast());
    // });
    // trace!("dispatch from:\n{:?}", backtrace::Backtrace::new());

    let args_slice = std::slice::from_raw_parts(args, n_args as usize);
    trace!("dispatch: {:?}", args_slice);

    let f = args_slice[0];

    let typetag = get_typetag(f);
    let methods = &(*(*typetag).methods);

    let mut selected_method: Option<&Method> = None;
    for method in methods.elements() {
        let method = &*(*method as *const Method);
        if !method.is_applicable(args_slice) {
            continue;
        }

        // this method is applicable

        selected_method = Some(match selected_method {
            None => method,
            Some(current) => {
                // check if it is strictly more specific
                if current.is_subtype_of(method) {
                    // selected method remains selected, skip this one
                    current
                } else if method.is_subtype_of(current) {
                    // the new method is more specific
                    method
                } else {
                    // Both methods are applicable but neither is more specific — ambiguity.
                    // let args_cpls = args_slice
                    //     .iter()
                    //     .map(|x| get_cpl(type_of(*x)))
                    //     .collect::<Vec<_>>();
                    let signature = args_slice.iter().map(|a| type_of(*a)).collect::<Vec<_>>();
                    error!("ambiguity finding matching method for: {:?}", signature);
                    error!("available methods: {:?}", methods);
                    // error!("cpls: {:?}", args_cpls);
                    panic!("ambiguity! between {:?} and {:?}", current, method);
                }
            }
        });
    }

    match selected_method {
        Some(method) => {
            trace!("calling found method: {:?}", *method);
            (method.instance)(n_args, args)
        }
        None => {
            // let args_cpls = args_slice
            //     .iter()
            //     .map(|x| get_cpl(type_of(*x)))
            //     .collect::<Vec<_>>();
            let signature = args_slice.iter().map(|a| type_of(*a)).collect::<Vec<_>>();
            error!("unable to find matching method: {:?}", signature);
            error!("available methods: {:?}", methods);
            // error!("cpls: {:?}", args_cpls);
            panic!("unable to find matching method");
        }
    }
}

#[derive(Debug)]
pub enum EnvValue {
    Global(String),
    Local(Value),
}

impl EnvValue {
    fn as_global(&self) -> &str {
        match self {
            EnvValue::Global(s) => s,
            _ => panic!("EnvValue::as_global() called on non-global"),
        }
    }
}

pub struct ExecutionSession<'ctx> {
    /// A global counter to make function names unique.
    counter: usize,
    /// A module that contains global declarations to be copied into each new module. The module
    /// itself is never passed into JIT.
    globals: Module,
    /// These need to be removed from global roots when ExecutionSession is destroyed. Otherwise, GC
    /// will try to scavenge them and will segfault.
    global_gc_roots: HashSet<GcRoot<'static, AlphaValue>>,
    jit: LLJIT,
    global_env: Env<'ctx, EnvValue>,
    types: Env<'ctx, TypeDef>,
    // Context should be the last field, so that other fields (globals, jit) are disposed _before_
    // module is disposed.
    context: ThreadSafeContext,
}

impl<'ctx> ExecutionSession<'ctx> {
    pub fn new() -> Self {
        let context = ThreadSafeContext::new();
        let globals = context.context().create_module("globals");
        let jit = LLJITBuilder::new().build().unwrap();

        let global_env = Env::new(None);
        let types = Env::new(None);

        let mut es = ExecutionSession {
            counter: 0,
            context,
            global_env,
            global_gc_roots: HashSet::new(),
            jit,
            globals,
            types,
        };

        es.build_stdlib().unwrap();

        es
    }

    /// Initialize new module with common definitions copied from `self.globals` module.
    fn new_module(&self, name: &str) -> Module {
        let module = self.context.context().create_module(name);

        for v in self.globals.functions() {
            module.add_function(v.get_name(), v.get_type().element_type());
        }
        for v in self.globals.globals() {
            module.add_global(v.get_name(), v.get_type().element_type());
        }

        module
    }

    fn load_module(&mut self, module: Module) -> Result<(), Box<dyn Error>> {
        trace!("loading module:\n{}", module);
        let module = self.context.create_module(module);
        self.jit.add_module(module)?;
        Ok(())
    }

    fn load_module_with_tracker(
        &mut self,
        module: Module,
    ) -> Result<ResourceTracker, Box<dyn Error>> {
        trace!("loading module:\n{}", module);
        let module = self.context.create_module(module);
        let tracker = self.jit.add_module_with_tracker(module)?;
        Ok(tracker)
    }

    /// Build Alpha standard library.
    ///
    /// This function initializes `self.globals` module and loads LLVM definitions that are required
    /// for compiler to work.
    ///
    /// This functions must be called once before any other operation on ExecutionSession.
    fn build_stdlib(&mut self) -> Result<(), Box<dyn Error>> {
        // If that's a second instantiation of ExecutionSession, delete previously stored
        // constructors.
        // TODO: not thread-safe
        unsafe {
            DataType::reset_methods(DATATYPE_T.load_mut());
        }

        let any_t = self.context.context().create_named_struct_type("Any"); // opaque
        let datatype_t = self.context.context().create_named_struct_type("DataType"); // to be defined
        let datatype_ptr_t = datatype_t.pointer_type(AddressSpace::Generic);

        self.jit
            .define_symbol("_Unwind_Resume", _unwind_resume as usize)?;
        self.jit
            .define_symbol("__gcc_personality_v0", __gcc_personality_v0 as usize)?;
        self.jit.define_symbol("llvm_gc_root_chain", unsafe {
            &mut GC_ROOT_CHAIN as *mut GcRootChain as usize
        })?;

        self.types.insert(
            symbol("Any"),
            TypeDef {
                name: symbol("Any"),
                supertype: symbol("Any"),
                typedef: TypeDescriptor::Abstract,
            },
        );

        let i64_typedef = TypeDef {
            name: symbol("i64"),
            supertype: symbol("Any"),
            typedef: TypeDescriptor::Int(64),
        };
        self.build_type_specifier(&i64_typedef)?;
        self.types.insert(symbol("i64"), i64_typedef);

        let f64_typedef = TypeDef {
            name: symbol("f64"),
            supertype: symbol("Any"),
            typedef: TypeDescriptor::Float(64),
        };
        self.build_type_specifier(&f64_typedef)?;
        self.types.insert(symbol("f64"), f64_typedef);

        let void_typedef = TypeDef {
            name: symbol("Void"),
            supertype: symbol("Any"),
            typedef: TypeDescriptor::Struct { fields: vec![] },
        };
        let void_t = self.build_type_specifier(&void_typedef)?;
        let datatype_typedef = TypeDef {
            name: symbol("DataType"),
            supertype: symbol("Any"),
            typedef: TypeDescriptor::Struct {
                fields: vec![
                    // TODO:
                    // (symbol("supertype"), abstracttype_typedef.clone()),
                    // (
                    //     symbol("size"),
                    //     TypeDef {
                    //         name: symbol("i64"),
                    //         supertype: symbol("Number"),
                    //         typedef: TypeDescriptor::Int(64),
                    //     },
                    // ),
                    // (
                    //     symbol("n_ptrs"),
                    //     TypeDef {
                    //         name: symbol("i64"),
                    //         supertype: symbol("Number"),
                    //         typedef: TypeDescriptor::Int(64),
                    //     },
                    // ),
                    // (
                    //     symbol("methods"),
                    //     TypeDef {
                    //         // actually: pointer to Vec<Method>
                    //         name: symbol("i64"),
                    //         supertype: symbol("Number"),
                    //         typedef: TypeDescriptor::Int(64),
                    //     },
                    // ),
                ],
            },
        };
        self.types
            .insert(symbol("DataType"), datatype_typedef.clone());

        let any_ptr_t = any_t.pointer_type(AddressSpace::Generic);
        let i8_t = self.context.context().int_type(8);
        let i64_t = self.context.context().int_type(64);
        let fn_t = any_ptr_t.function_type(
            &[
                /* n_args: */ i64_t,
                /* args: */ any_ptr_t.pointer_type(AddressSpace::Generic),
            ],
            false,
        );

        self.globals.add_function(
            "gc_allocate",
            any_ptr_t.function_type(&[i64_t.into()], false),
        );
        self.jit
            .define_symbol("gc_allocate", gc_allocate as usize)?;

        self.globals.add_function(
            "mk_str",
            any_ptr_t.function_type(&[i8_t.pointer_type(AddressSpace::Generic), i64_t], false),
        );
        self.jit.define_symbol("mk_str", mk_str as usize)?;

        self.globals.add_function("dispatch", fn_t);
        self.jit.define_symbol("dispatch", dispatch as usize)?;

        self.globals.add_global("DataType", datatype_ptr_t);
        self.jit
            .define_symbol("DataType", DATATYPE_T.as_ref() as *const _ as usize)?;
        self.global_env
            .insert(symbol("DataType"), EnvValue::Global("DataType".to_string()));

        self.globals.add_global("Any", datatype_ptr_t);
        self.jit
            .define_symbol("Any", ANY_T.as_ref() as *const _ as usize)?;
        self.global_env
            .insert(symbol("Any"), EnvValue::Global("Any".to_string()));

        self.globals.add_global("Void", datatype_ptr_t);
        self.jit
            .define_symbol("Void", VOID_T.as_ref() as *const _ as usize)?;
        self.global_env
            .insert(symbol("Void"), EnvValue::Global("Void".to_string()));

        self.globals
            .add_global("void", void_t.pointer_type(AddressSpace::Generic));
        self.jit
            .define_symbol("void", VOID.as_ref() as *const _ as usize)?;
        self.global_env
            .insert(symbol("void"), EnvValue::Global("void".to_string()));

        self.globals.add_global("i64", datatype_ptr_t);
        self.jit
            .define_symbol("i64", I64_T.as_ref() as *const _ as usize)?;
        self.global_env
            .insert(symbol("i64"), EnvValue::Global("i64".to_string()));

        self.globals.add_global("f64", datatype_ptr_t);
        self.jit
            .define_symbol("f64", F64_T.as_ref() as *const _ as usize)?;
        self.global_env
            .insert(symbol("f64"), EnvValue::Global("f64".to_string()));

        // Add a copy of the globals module to jit, so globals with initializers are defined.
        self.load_module(self.globals.clone())?;

        // poor man's standard library
        self.eval(
            r#"
              # type i64: Number = integer(64)
              # type f64: Number = float(64)
            "#,
        )?;

        // DataType type specifier can only be built after i64 and f64 are defined in alpha.
        // let t = self.build_type_specifier(&datatype_typedef)?;
        // trace!("defined type: {}", t);

        {
            let type_of_s = symbol("type_of");
            let type_of_f = self.define_function(type_of_s)?;
            trace!("type_of_f: {:?}", type_of_f);
            unsafe {
                gc::debug_ptr(type_of_f.cast());
            }
            gc_box!(type_of_f);
            let signature = unsafe { SVec::new(&[ANY_T.load() as AnyPtr, ANY_T.load() as AnyPtr]) };
            let m = unsafe { Method::new(signature, alpha_type_of) };
            gc_box!(m);
            trace!("type_of_f after allocations: {:?}", type_of_f.load());
            unsafe {
                gc::debug_ptr(type_of_f.load().cast());
            }
            self.function_add_method(type_of_f.load(), m.load());
        }

        {
            let f64_mul_s = symbol("f64_mul");
            let f64_mul_f = self.define_function(f64_mul_s)?;
            gc_box!(f64_mul_f);
            let signature = unsafe {
                SVec::new(&[
                    ANY_T.load() as AnyPtr,
                    F64_T.load() as AnyPtr,
                    F64_T.load() as AnyPtr,
                ])
            };
            let m = unsafe { Method::new(signature, alpha_f64_mul) };
            self.function_add_method(f64_mul_f.load(), m);
        }

        {
            let i64_mul_s = symbol("i64_mul");
            let i64_mul_f = self.define_function(i64_mul_s)?;
            gc_box!(i64_mul_f);
            let signature = unsafe {
                SVec::new(&[
                    ANY_T.load() as AnyPtr,
                    I64_T.load() as AnyPtr,
                    I64_T.load() as AnyPtr,
                ])
            };
            let m = unsafe { Method::new(signature, alpha_i64_mul) };
            self.function_add_method(i64_mul_f.load(), m);
        }

        let print_s = symbol("print");
        let print_f = self.define_function(print_s)?;
        gc_box!(print_f);
        {
            let signature = unsafe { SVec::new(&[ANY_T.load() as AnyPtr, ANY_T.load() as AnyPtr]) };
            let m = unsafe { Method::new(signature, alpha_print_any) };
            gc_box!(m);
            self.function_add_method(print_f.load(), m.load());
        }
        {
            let signature =
                unsafe { SVec::new(&[ANY_T.load() as AnyPtr, VOID_T.load() as AnyPtr]) };
            let m = unsafe { Method::new(signature, alpha_print_void) };
            gc_box!(m);
            self.function_add_method(print_f.load(), m.load());
        }
        {
            let signature = unsafe { SVec::new(&[ANY_T.load() as AnyPtr, I64_T.load() as AnyPtr]) };
            let m = unsafe { Method::new(signature, alpha_print_i64) };
            gc_box!(m);
            self.function_add_method(print_f.load(), m.load());
        }
        {
            let signature = unsafe { SVec::new(&[ANY_T.load() as AnyPtr, F64_T.load() as AnyPtr]) };
            let m = unsafe { Method::new(signature, alpha_print_f64) };
            self.function_add_method(print_f.load(), m);
        }
        {
            let signature =
                unsafe { SVec::new(&[ANY_T.load() as AnyPtr, STRING_T.load() as AnyPtr]) };
            let m = unsafe { Method::new(signature, alpha_print_string) };
            self.function_add_method(print_f.load(), m);
        }
        {
            let signature =
                unsafe { SVec::new(&[ANY_T.load() as AnyPtr, DATATYPE_T.load() as AnyPtr]) };
            let m = unsafe { Method::new(signature, alpha_print_datatype) };
            self.function_add_method(print_f.load(), m);
        }

        self.eval(
            r#"
              fn *(x: f64, y: f64) = f64_mul(x, y)
              fn *(x: i64, y: i64) = i64_mul(x, y)

              fn println(x) = { print(x); print("\n") }
            "#,
        )?;

        Ok(())
    }

    pub fn eval(&mut self, s: &str) -> Result<(), Box<dyn Error>> {
        trace!("eval: {}", s);
        let mut parser = Parser::new(s);
        while parser.has_input() {
            let sexp = parser.parse()?;
            trace!("sexp: {}", sexp);

            let exp = lower_sexp(&sexp)?;
            trace!("exp: {:?}", &exp);

            self.eval_exp(exp)?;
        }

        Ok(())
    }

    fn eval_exp(&mut self, exp: Exp) -> Result<(), Box<dyn Error>> {
        match exp {
            Exp::Type(t) => {
                let alpha_type = TypeDef::from_exp(&t, &self.types)?;
                self.eval_type(&alpha_type)?;
            }
            Exp::Function(f) => self.eval_function_definition(f)?,
            e => self.eval_anonymous_expression(e)?,
        }
        Ok(())
    }

    // Build a global type binding and initialize it. This does not execute any code inside the JIT.
    fn eval_type(&mut self, alpha_type: &TypeDef) -> Result<*const DataType, Box<dyn Error>> {
        trace!("type lowered to {:?}", alpha_type);

        let name = alpha_type.name;
        let module = self.context.context().create_module(name.as_str());

        let supertype_t = self
            .global_env
            .lookup(alpha_type.supertype)
            .ok_or_else(|| {
                simple_error!("unable to find type: {}", alpha_type.supertype.as_str())
            })?;

        trace!("found supertype_t: {:?}", supertype_t);
        trace!("env: {:?}", self.global_env);

        let supertype = unsafe {
            *self
                .jit
                .lookup::<*const *const DataType>(supertype_t.as_global())?
        };
        gc_box!(supertype);
        // TODO: verify the supertype is abstract

        let type_ptr = if alpha_type.typedef == TypeDescriptor::Abstract {
            unsafe { DataType::new_abstract(name, supertype.load()) }
        } else {
            let type_size = alpha_type
                .typedef
                .size()
                .expect("unsized types are not supported yet");
            let ptrs = alpha_type.typedef.pointer_offsets().unwrap();

            unsafe { DataType::new(name, supertype.load(), type_size, &ptrs) }
        };
        gc_box!(type_ptr);

        let ptr_t = self
            .context
            .context()
            .get_named_struct("DataType")
            .unwrap()
            .pointer_type(AddressSpace::Generic);

        self.inject_global(&module, name.as_str(), ptr_t, type_ptr.load());

        self.globals.add_global(name.as_str(), ptr_t); // without initializer here
        self.global_env
            .insert(alpha_type.name, EnvValue::Global(name.to_string()));
        self.types.insert(alpha_type.name, alpha_type.clone());

        self.load_module(module)?;

        let type_ptr_place = self.jit.lookup::<*mut AnyPtr>(name.as_str())?;
        unsafe {
            self.register_gc_root(type_ptr_place);
        }

        if alpha_type.typedef != TypeDescriptor::Abstract {
            let t = self.build_type_specifier(&alpha_type)?;
            trace!(
                "defined type: {} size={:?}, n_ptrs={:?}, is_inlinable={}, has_ptrs={}, is_ptr={}",
                t,
                alpha_type.typedef.size(),
                alpha_type.typedef.n_ptrs(),
                alpha_type.typedef.is_inlinable(),
                alpha_type.typedef.has_ptrs(),
                alpha_type.typedef.is_ptr(),
            );

            if let TypeDescriptor::Struct { .. } = alpha_type.typedef {
                self.build_constructor(type_ptr.load(), &alpha_type)?;
                self.build_accessors(type_ptr.load(), &alpha_type)?;
            }
        }

        Ok(type_ptr.load())
    }

    /// Build LLVM IR type for `type_`.
    fn build_type_specifier(&mut self, type_: &TypeDef) -> Result<LLVMType, Box<dyn Error>> {
        let name = type_.name.as_str();
        let t = match &type_.typedef {
            TypeDescriptor::Abstract => panic!("build_type_specifier is called for Abstract type"),
            TypeDescriptor::Int(size) => {
                let i = self.context.context().int_type(*size as u32);
                let t = self
                    .context
                    .context()
                    .create_named_struct_type(name)
                    .struct_set_body(&[i], false);
                t
            }
            TypeDescriptor::Float(size) => {
                let i = self.context.context().float_type(*size as u32);
                let t = self
                    .context
                    .context()
                    .create_named_struct_type(name)
                    .struct_set_body(&[i], false);
                t
            }
            TypeDescriptor::Struct { fields } => {
                let v = fields
                    .iter()
                    .map(|(_name, type_)| {
                        let name = type_.name.as_str();
                        if type_.typedef == TypeDescriptor::Abstract {
                            // Even though typ can be more concrete than Any, we still define the
                            // field as %Any* in LLVM. %Any in LLVM IR means that specific DataType
                            // is unknown.
                            self.context
                                .context()
                                .get_named_struct("Any")
                                .unwrap()
                                .pointer_type(AddressSpace::Generic)
                        } else {
                            let field_t = self.context.context().get_named_struct(name).unwrap();
                            if type_.typedef.is_inlinable() {
                                field_t
                            } else {
                                field_t.pointer_type(AddressSpace::Generic)
                            }
                        }
                    })
                    .collect::<Vec<_>>();
                let t = self
                    .context
                    .context()
                    .get_named_struct(name)
                    .unwrap_or_else(|| self.context.context().create_named_struct_type(name))
                    .struct_set_body(&v, false);
                t
            }
        };

        Ok(t)
    }

    fn build_constructor(
        &mut self,
        type_ptr: *const DataType,
        def: &TypeDef,
    ) -> Result<(), Box<dyn Error>> {
        gc_box!(type_ptr);

        let fields = match &def.typedef {
            TypeDescriptor::Struct { fields } => fields,
            _ => return Ok(()),
        };

        let module = self.new_module("constructor");
        let constructor =
            Compiler::compile_constructor(self.context.context(), &module, &self.global_env, def)?;
        Self::optimize_function(&module, constructor);
        let name = constructor.get_name();
        self.load_module(module)?;

        let constructor_code = self.jit.lookup::<GenericFn>(&name)?;
        let t = unsafe { Type::new(type_ptr.load()) };
        gc_box!(t);
        let signature = std::iter::once(t.load() as AnyPtr)
            .chain(fields.iter().map(|(_name, type_)| {
                let llvm_name = match self.global_env.lookup(type_.name) {
                    Some(EnvValue::Global(s)) => s,
                    _ => panic!("unable to lookup: {:?}", type_.name),
                };
                trace!("build_constructor: jit.lookup({})", llvm_name);
                unsafe { *self.jit.lookup::<*const AnyPtr>(llvm_name).unwrap() }
            }))
            .collect::<Vec<_>>();
        let signature = unsafe { SVec::new(&signature) };
        let method = unsafe { Method::new(signature, constructor_code) };
        trace!(
            "build_constructor(): allocated method {:?} (ty={:?}), signature: {:?}",
            unsafe { &*method },
            unsafe { get_typetag(method) },
            unsafe { &*(*method).signature }
        );

        // This actually adds a method to the DataType class.
        self.function_add_method(type_ptr.load().cast(), method);

        Ok(())
    }

    fn build_accessors(
        &mut self,
        type_ptr: *const DataType,
        def: &TypeDef,
    ) -> Result<(), Box<dyn Error>> {
        gc_box!(type_ptr);
        let fields = match &def.typedef {
            TypeDescriptor::Struct { fields } => fields,
            _ => return Ok(()),
        };

        for (i, (name, _typ)) in fields.iter().enumerate() {
            let f_name = self.unique_name(*name);
            let module = self.new_module("accessor");
            let accessor = Compiler::compile_accessor(
                self.context.context(),
                &module,
                &self.global_env,
                def,
                i,
                &f_name,
            )?;
            Self::optimize_function(&module, accessor);
            let instance_name = accessor.get_name();
            self.load_module(module)?;

            let instance = self.jit.lookup::<GenericFn>(&instance_name)?;

            let fn_obj = self.ensure_function(*name)?;
            gc_box!(fn_obj);
            let t = unsafe { Type::new(fn_obj.load() as *const DataType) };
            gc_box!(t);
            let signature = unsafe { SVec::new(&[t.load().cast(), type_ptr.load().cast()]) };
            let method = unsafe { Method::new(signature, instance) };
            gc_box!(method);
            self.function_add_method(fn_obj.load(), method.load());
        }

        Ok(())
    }

    fn eval_function_definition(&mut self, mut def: exp::Function) -> Result<(), Box<dyn Error>> {
        let fn_name_s = def.prototype.name;
        let method_name = self.unique_name(fn_name_s);
        let method_name_s = symbol(&method_name);

        def.prototype.name = method_name_s;

        let fn_obj = self.ensure_function(fn_name_s)?;
        gc_box!(fn_obj);

        // compile method
        let module = self.new_module(&method_name);
        let instance = Compiler::compile(self.context.context(), &module, &self.global_env, &def)?;
        Self::optimize_function(&module, instance);
        let instance_fn_name = instance.get_name();
        self.load_module(module)?;
        let instance = self.jit.lookup::<GenericFn>(instance_fn_name)?;

        let t = unsafe { Type::new(fn_obj.load().cast()) };
        let signature = std::iter::once(t.cast())
            .chain(def.prototype.params.iter().map(|p| {
                let llvm_name = match self.global_env.lookup(p.typ) {
                    Some(EnvValue::Global(s)) => s,
                    _ => panic!("unable to lookup: {:?}", p.typ),
                };
                unsafe { *self.jit.lookup::<*const AnyPtr>(llvm_name).unwrap() }
            }))
            .collect::<Vec<_>>();
        let signature = unsafe { SVec::new(&signature) };
        let method = unsafe { Method::new(signature, instance) };
        self.function_add_method(fn_obj.load(), method);

        Ok(())
    }

    /// Ensure a function `name` is defined. Defines it if it does not exist.
    fn ensure_function(&mut self, name: Symbol) -> Result<AnyPtr, Box<dyn Error>> {
        match self.global_env.lookup(name) {
            Some(EnvValue::Global(name)) => unsafe {
                return Ok(*self.jit.lookup::<*const AnyPtr>(name)?);
            },
            _ => {}
        }

        self.define_function(name)
    }

    fn define_function(&mut self, symbol: Symbol) -> Result<AnyPtr, Box<dyn Error>> {
        let fn_t = self.define_function_type(symbol.as_str())?;
        let fn_obj = self.define_function_object(symbol, fn_t)?;

        Ok(fn_obj)
    }

    fn define_function_type(&mut self, fn_name: &str) -> Result<*const DataType, Box<dyn Error>> {
        let any_s = symbol("Any");
        let fn_t_name = symbol(&("fn_".to_string() + fn_name + "_t"));
        let fn_t = self.eval_type(&TypeDef {
            name: fn_t_name,
            supertype: any_s,
            typedef: TypeDescriptor::Struct { fields: Vec::new() },
        })?;
        Ok(fn_t)
    }

    fn define_function_object(
        &mut self,
        symbol: Symbol,
        fn_t: *const DataType,
    ) -> Result<AnyPtr, Box<dyn Error>> {
        gc_box!(fn_t);
        let name = symbol.as_str();

        // allocate function object
        let fn_obj = unsafe {
            let fn_obj = gc_allocate(0) as AnyPtrMut;
            set_typetag(fn_obj, fn_t.load());
            fn_obj
        };
        gc_box!(fn_obj);
        let module = self.new_module(&(name.to_string() + "_fn_object"));
        let any_ptr_t = self
            .context
            .context()
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let f_global = self.inject_global(
            &module,
            &("fn_".to_string() + &name),
            any_ptr_t,
            fn_obj.load(),
        );
        let f_global_name = f_global.get_name();
        self.global_env
            .insert(symbol, EnvValue::Global(f_global_name.to_string()));
        self.save_global_declarations(&module);
        self.load_module(module)?;

        unsafe {
            let fn_place = self.jit.lookup::<*mut AnyPtr>(f_global_name)?;
            self.register_gc_root(fn_place);
        }

        Ok(fn_obj.load().cast())
    }

    fn function_add_method(&mut self, fn_obj: AnyPtr, method: *const Method) {
        debug_assert!(!fn_obj.is_null());
        debug_assert!(!method.is_null());
        unsafe {
            let fn_t = type_of(fn_obj) as *mut DataType;
            DataType::add_method(fn_t, method);
        }
    }

    fn eval_anonymous_expression(&mut self, e: Exp) -> Result<(), Box<dyn Error>> {
        let def = exp::Function {
            prototype: exp::FunctionPrototype {
                name: symbol("*anonymous*"),
                params: vec![],
                result_type: symbol("Any"),
            },
            body: Some(Box::new(Exp::Call(exp::Call {
                fun: Box::new(Exp::Symbol(symbol("println"))),
                args: vec![e],
            }))),
        };

        let module = self.new_module("user");

        let f = Compiler::compile(self.context.context(), &module, &self.global_env, &def)?;

        Self::optimize_function(&module, f);

        let name = f.get_name();

        self.save_global_declarations(&module);
        // We don't save function declarations as the only new function here is *anonymous* and
        // we don't need to save it.

        let tracker = self.load_module_with_tracker(module)?;
        let fun = self.jit.lookup::<GenericFn>(&name)?;
        unsafe {
            fun(0, std::ptr::null());
        }

        // This was just an anonymous function. We can unload the module as it is no longer
        // useful.
        tracker.remove()?;

        Ok(())
    }

    fn save_global_declarations(&mut self, module: &Module) {
        for v in module.globals() {
            if self.globals.get_global(v.get_name()).is_none() {
                let linkage = v.global_get_linkage();
                if linkage == LLVMLinkage::LLVMExternalLinkage {
                    self.globals
                        .add_global(v.get_name(), v.get_type().element_type());
                }
            }
        }
    }

    /// Add a global named `name` to the `module` and set initializer to point to `value`.
    fn inject_global<T>(
        &self,
        module: &Module,
        name: &str,
        typ: LLVMType,
        value: *const T,
    ) -> Value {
        let i64_t = self.context.context().int_type(64);
        let global = module.add_global(name, typ);
        global.global_set_initializer(
            i64_t
                .const_int(value as u64, false)
                .const_int_to_pointer(typ),
        );
        global
    }

    fn next_counter(&mut self) -> usize {
        self.counter += 1;
        self.counter
    }

    fn unique_name(&mut self, symbol: Symbol) -> String {
        let i = self.next_counter();
        format!("{}.{}_", symbol.as_str(), i)
    }

    fn optimize_function(_module: &Module, _f: Value) {
        // use llvm::pass_manager::*;
        // let mut fpm = FunctionPassManager::new_for_module(module);
        // fpm.add_instruction_combining_pass();
        // fpm.add_cfg_simplification_pass();
        // fpm.run(f);

        // let pm = ModulePassManager::new();
        // pm.run(module);
    }

    unsafe fn register_gc_root(&mut self, ptr: *const AnyPtr) {
        let root = GcRoot::from_ptr_ref(ptr);
        self.global_gc_roots.insert(root.clone());
        gc::add_global_root(root);
    }
}

impl<'ctx> Drop for ExecutionSession<'ctx> {
    fn drop(&mut self) {
        for root in self.global_gc_roots.iter() {
            unsafe {
                gc::remove_global_root(root);
            }
        }
    }
}
