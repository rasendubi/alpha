use std::cell::RefCell;
use std::error::Error;

use simple_error::simple_error;

use llvm::module::Module;
use llvm::orc::lljit::{LLJITBuilder, ResourceTracker, LLJIT};
use llvm::orc::thread_safe::ThreadSafeContext;
use llvm::types::{AddressSpace, Type};
use llvm::values::Value;

use crate::compiler::Compiler;
use crate::env::Env;
use crate::exp;
use crate::exp::{lower_sexp, Exp};
use crate::gc::Gc;
use crate::parser::Parser;
use crate::symbol::{Symbol, SymbolInterner};
use crate::types::{AlphaType, AlphaTypeDef};

thread_local! {
    static GC: RefCell<Gc> = RefCell::new(unsafe { Gc::new_uninit() });
}

unsafe extern "C" fn gc_allocate(size: u64) -> *mut u8 {
    GC.with(|gc| gc.borrow_mut().allocate(size as usize))
}

type AnyPtr = *const u64;
type AnyPtrMut = *mut u64;
type GenericFn = unsafe extern "C" fn(AnyPtr, i64, *const AnyPtr) -> AnyPtr;

// type DataType = { size: i64, n_ptrs: i64, methods: i64 }
#[derive(Debug)]
#[repr(C)]
struct DataType {
    supertype: *const AbstractType,
    size: u64,
    n_ptrs: u64,
    methods: Vec<Method>,
    name: String,
}

#[derive(Debug)]
#[repr(C)]
struct AbstractType {
    supertype: *const AbstractType,
    name: String,
}

#[derive(Debug)]
struct Method {
    signature: Vec<*const DataType>,
    // compiled instance of the method
    instance: GenericFn,
}

unsafe fn dump_value(name: &str, value: AnyPtr) {
    println!("{} @ {:#?}", name, value);
    if !value.is_null() {
        println!("  type= {:p}", type_of(value as AnyPtr));
        println!("  f64= {:.5}", *(value as *const f64));
        println!("  u64= {}", *(value as *const u64));
        println!("  ptr= {:p}", *(value as *const *const ()));
    }
}

unsafe fn set_typetag<T>(ptr: *mut T, typetag: *const DataType) {
    let typetag_ptr = (ptr as *mut u64).sub(1) as *mut *const DataType;
    *typetag_ptr = typetag;
}
unsafe fn get_typetag<T>(ptr: *const T) -> *const DataType {
    let typetag_ptr = (ptr as *mut u64).sub(1) as *mut *const DataType;
    *typetag_ptr
}

unsafe fn type_of(x: AnyPtr) -> AnyPtr {
    let result = *x.sub(1) as AnyPtr;
    // println!("type_of({:p}) = {:p} (typetag @ {:p})", x, result, x.sub(1));
    result
}

unsafe extern "C" fn alpha_type_of(_this: AnyPtr, _n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x = *args.add(0);
    type_of(x)
}

unsafe extern "C" fn alpha_print_i64(_this: AnyPtr, _n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x = *(*args.add(0) as *const i64);
    println!("{}", x);
    std::ptr::null()
}

unsafe extern "C" fn alpha_print_f64(_this: AnyPtr, _n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x = *(*args.add(0) as *const f64);
    println!("{}", x);
    std::ptr::null()
}

unsafe extern "C" fn alpha_print_datatype(
    _this: AnyPtr,
    _n_args: i64,
    args: *const AnyPtr,
) -> AnyPtr {
    let x = &*(*args.add(0) as *const DataType);
    println!("{:?}", x);
    std::ptr::null()
}

unsafe extern "C" fn alpha_print_abstracttype(
    _this: AnyPtr,
    _n_args: i64,
    args: *const AnyPtr,
) -> AnyPtr {
    let x = &*(*args.add(0) as *const AbstractType);
    println!("{:?}", x);
    std::ptr::null()
}

unsafe extern "C" fn dispatch(f: AnyPtr, n_args: i64, args: *const AnyPtr) -> AnyPtr {
    println!("dispatch: {:p} {}", f, n_args);
    let typetag = get_typetag(f);
    let methods = &*(*typetag).methods;

    let args_slice = std::slice::from_raw_parts(args, n_args as usize);
    let signature = args_slice
        .iter()
        .map(|a| type_of(*a) as *const DataType)
        .collect::<Vec<_>>();

    for method in methods {
        if signature == method.signature {
            return (method.instance)(f, n_args, args);
        }
    }

    eprintln!("unable to find matching method: {:?}", signature);
    eprintln!("available methods: {:?}", methods);
    panic!("unable to find matching method");
}

// TODO: generating all primitive operations as IR from Rust code might be easier to implement (less
// duplication).
const STDLIB_LL: &str = r#"
  %Any = type opaque
  %DataType = type opaque

  @f64 = external global %DataType*
  @i64 = external global %DataType*

  declare %Any* @gc_allocate(i64 %0)

  define %Any* @gc_allocate_with_typetag(i64 %size, %DataType* %type) {
    %result_any = call %Any* @gc_allocate(i64 8)
    %result_cells = bitcast %Any* %result_any to %DataType**
    %typetag = getelementptr %DataType*, %DataType** %result_cells, i64 -1
    store %DataType* %type, %DataType** %typetag
    ret %Any* %result_any
  }

  define %Any* @f64_mul(%Any* %this, i64 %n_args, %Any** %args) {
  entry:
    %a_ptr = getelementptr %Any*, %Any** %args, i64 0
    %a = load %Any*, %Any** %a_ptr, align 4
    %b_ptr = getelementptr %Any*, %Any** %args, i64 1
    %b = load %Any*, %Any** %b_ptr, align 4

    %f64_t = load %DataType*, %DataType** @f64
    %result_any = call %Any* @gc_allocate_with_typetag(i64 8, %DataType* %f64_t)

    %a_float_ptr = bitcast %Any* %a to double*
    %a_value = load double, double* %a_float_ptr
    %b_float_ptr = bitcast %Any* %b to double*
    %b_value = load double, double* %b_float_ptr

    %result = fmul double %a_value, %b_value
    %result_ptr = bitcast %Any* %result_any to double*
    store double %result, double* %result_ptr
    ret %Any* %result_any
  }

  define %Any* @i64_mul(%Any* %this, i64 %n_args, %Any** %args) {
  entry:
    %a_ptr = getelementptr %Any*, %Any** %args, i64 0
    %a = load %Any*, %Any** %a_ptr, align 4
    %b_ptr = getelementptr %Any*, %Any** %args, i64 1
    %b = load %Any*, %Any** %b_ptr, align 4

    %i64_t = load %DataType*, %DataType** @i64
    %result_any = call %Any* @gc_allocate_with_typetag(i64 8, %DataType* %i64_t)

    %a_int_ptr = bitcast %Any* %a to i64*
    %a_value = load i64, i64* %a_int_ptr
    %b_int_ptr = bitcast %Any* %b to i64*
    %b_value = load i64, i64* %b_int_ptr

    %result = mul i64 %a_value, %b_value
    %result_ptr = bitcast %Any* %result_any to i64*
    store i64 %result, i64* %result_ptr
    ret %Any* %result_any
  }
"#;

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
    jit: LLJIT,
    interner: SymbolInterner,
    global_env: Env<'ctx, EnvValue>,
    types: Env<'ctx, AlphaType>,
    // Context should be the last field, so that other fields (globals, jit) are disposed _before_
    // module is disposed.
    context: ThreadSafeContext,
}

impl<'ctx> ExecutionSession<'ctx> {
    pub fn new() -> Self {
        unsafe {
            llvm_sys::target::LLVM_InitializeNativeTarget();
            llvm_sys::target::LLVM_InitializeNativeAsmPrinter();
        }

        GC.with(|gc| unsafe {
            gc.borrow_mut().init();
        });

        let context = ThreadSafeContext::new();
        let globals = context.context().create_module("globals");
        let jit = LLJITBuilder::new().build().unwrap();

        let interner = SymbolInterner::new();
        let global_env = Env::new(None);
        let types = Env::new(None);

        let mut es = ExecutionSession {
            counter: 0,
            context,
            interner,
            global_env,
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
        module.dump_to_stderr();
        let module = self.context.create_module(module);
        self.jit.add_module(module)?;
        Ok(())
    }

    fn load_module_with_tracker(
        &mut self,
        module: Module,
    ) -> Result<ResourceTracker, Box<dyn Error>> {
        module.dump_to_stderr();
        let module = self.context.create_module(module);
        let tracker = self.jit.add_module_with_tracker(module)?;
        Ok(tracker)
    }

    /// Load IR module using an independent context. This way, the module can (re)define any types
    /// or functions without clogging the global context.
    ///
    /// The side effect of using a new context is that global functions/types defined in the IR
    /// module are not added to the `self.context` and must be added explicitly.
    fn load_ir_module(&mut self, name: &str, ir: &str) -> Result<(), Box<dyn Error>> {
        let tsc = ThreadSafeContext::new();
        let module = tsc.context().parse_ir_module(name, ir)?;
        module.dump_to_stderr();
        let module = tsc.create_module(module);
        self.jit.add_module(module)?;
        Ok(())
    }

    /// Build Alpha standard library.
    ///
    /// This function initializes `self.globals` module and loads LLVM definitions that are required
    /// for compiler to work.
    ///
    /// This functions must be called once before any other operation on ExecutionSession.
    fn build_stdlib(&mut self) -> Result<(), Box<dyn Error>> {
        let any_t = self.context.context().create_named_struct_type("Any"); // opaque
        let datatype_t = self.context.context().create_named_struct_type("DataType"); // to be defined
        let datatype_ptr_t = datatype_t.pointer_type(AddressSpace::Generic);
        let abstracttype_t = self
            .context
            .context()
            .create_named_struct_type("AbstractType"); // to be defined
        let abstracttype_ptr_t = abstracttype_t.pointer_type(AddressSpace::Generic);

        self.types.insert(
            self.interner.intern("Any"),
            AlphaType {
                name: self.interner.intern("Any"),
                supertype: self.interner.intern("Any"),
                typedef: AlphaTypeDef::Abstract,
            },
        );
        let type_typedef = AlphaType {
            name: self.interner.intern("Type"),
            supertype: self.interner.intern("Any"),
            typedef: AlphaTypeDef::Abstract,
        };
        self.types
            .insert(self.interner.intern("Type"), type_typedef.clone());
        let abstracttype_typedef = AlphaType {
            name: self.interner.intern("AbstractType"),
            supertype: self.interner.intern("Type"),
            typedef: AlphaTypeDef::Struct {
                fields: vec![(
                    self.interner.intern("supertype"),
                    // this is supertype: Type, but in reality it should be supertype: AbstractType
                    type_typedef,
                )],
            },
        };
        self.types.insert(
            self.interner.intern("AbstractType"),
            abstracttype_typedef.clone(),
        );
        let datatype_typedef = AlphaType {
            name: self.interner.intern("DataType"),
            supertype: self.interner.intern("Type"),
            typedef: AlphaTypeDef::Struct {
                fields: vec![
                    (
                        self.interner.intern("supertype"),
                        abstracttype_typedef.clone(),
                    ),
                    (
                        self.interner.intern("size"),
                        AlphaType {
                            name: self.interner.intern("i64"),
                            supertype: self.interner.intern("Any"),
                            typedef: AlphaTypeDef::Int(64),
                        },
                    ),
                    (
                        self.interner.intern("n_ptrs"),
                        AlphaType {
                            name: self.interner.intern("i64"),
                            supertype: self.interner.intern("Any"),
                            typedef: AlphaTypeDef::Int(64),
                        },
                    ),
                    (
                        self.interner.intern("methods"),
                        AlphaType {
                            // actually: pointer to Vec<Method>
                            name: self.interner.intern("i64"),
                            supertype: self.interner.intern("Any"),
                            typedef: AlphaTypeDef::Int(64),
                        },
                    ),
                ],
            },
        };
        self.types
            .insert(self.interner.intern("DataType"), datatype_typedef.clone());

        let any_ptr_t = any_t.pointer_type(AddressSpace::Generic);
        let i64_t = self.context.context().int_type(64);
        let fn_t = any_ptr_t.function_type(
            &[
                /* this: */ any_ptr_t,
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

        self.globals.add_function("dispatch", fn_t);
        self.jit.define_symbol("dispatch", dispatch as usize)?;

        let any = unsafe {
            let any = gc_allocate(std::mem::size_of::<AbstractType>() as u64) as *mut AbstractType;
            *any = AbstractType {
                supertype: any,
                name: "Any".to_string(),
            };
            any
        };
        let type_ = unsafe {
            let type_ =
                gc_allocate(std::mem::size_of::<AbstractType>() as u64) as *mut AbstractType;
            *type_ = AbstractType {
                supertype: any,
                name: "Type".to_string(),
            };
            type_
        };

        let datatype = unsafe {
            let datatype = gc_allocate(std::mem::size_of::<DataType>() as u64) as *mut DataType;
            // Type is self-referencial:
            // typeof(DataType) == DataType
            set_typetag(datatype, datatype);
            *datatype = DataType {
                supertype: type_,
                size: std::mem::size_of::<DataType>() as u64,
                n_ptrs: 0,
                methods: Vec::new(),
                name: "DataType".to_string(),
            };
            datatype
        };
        self.inject_global(&self.globals, "DataType", datatype_ptr_t, datatype);
        self.global_env.insert(
            self.interner.intern("DataType"),
            EnvValue::Global("DataType".to_string()),
        );

        let abstracttype = unsafe {
            let abstracttype = gc_allocate(std::mem::size_of::<DataType>() as u64) as *mut DataType;
            set_typetag(abstracttype, datatype);
            *abstracttype = DataType {
                supertype: type_,
                size: std::mem::size_of::<AbstractType>() as u64,
                n_ptrs: 0,
                methods: Vec::new(),
                name: "AbstractType".to_string(),
            };
            abstracttype
        };
        self.inject_global(&self.globals, "AbstractType", datatype_ptr_t, abstracttype);
        self.global_env.insert(
            self.interner.intern("AbstractType"),
            EnvValue::Global("AbstractType".to_string()),
        );

        unsafe {
            set_typetag(any, abstracttype);
            set_typetag(type_, abstracttype);
        }
        self.inject_global(&self.globals, "Any", abstracttype_ptr_t, any);
        self.global_env.insert(
            self.interner.intern("Any"),
            EnvValue::Global("Any".to_string()),
        );
        self.inject_global(&self.globals, "Type", abstracttype_ptr_t, type_);
        self.global_env.insert(
            self.interner.intern("Type"),
            EnvValue::Global("Type".to_string()),
        );

        // Add a copy of the globals module to jit, so globals with initializers are defined.
        self.load_module(self.globals.clone())?;

        // poor man's standard library
        self.eval(
            r#"
              type i64 = integer(64)
              type f64 = float(64)
            "#,
        )?;

        // DataType type specifier can only be built after i64 and f64 are defined in alpha.
        let t = self.build_type_specifier(&datatype_typedef)?;
        eprint!("defined type: ");
        t.dump_to_stderr();
        eprintln!();
        let t = self.build_type_specifier(&abstracttype_typedef)?;
        eprint!("defined type: ");
        t.dump_to_stderr();
        eprintln!();

        let i64_t = unsafe { *self.jit.lookup::<*const *const DataType>("i64")? };
        let f64_t = unsafe { *self.jit.lookup::<*const *const DataType>("f64")? };

        let type_of_s = self.interner.intern("type_of");
        // TODO: support generic methods
        // self.add_method(
        //     self.define_function(type_of_s)?,
        //     Method {
        //         signature: vec![any_t],
        //         instance: alpha_type_of,
        //     },
        // );

        // stdlib.ll defines primitive operations
        self.load_ir_module("stdlib.ll", STDLIB_LL)?;
        let f64_mul_s = self.interner.intern("f64_mul");
        let f64_mul_t = self.define_function(f64_mul_s)?;
        self.add_method(
            f64_mul_t,
            Method {
                signature: vec![f64_t, f64_t],
                instance: self.jit.lookup::<GenericFn>("f64_mul")?,
            },
        );
        let i64_mul_s = self.interner.intern("i64_mul");
        let i64_mul_t = self.define_function(i64_mul_s)?;
        self.add_method(
            i64_mul_t,
            Method {
                signature: vec![i64_t, i64_t],
                instance: self.jit.lookup::<GenericFn>("i64_mul")?,
            },
        );

        let print_s = self.interner.intern("print");
        let print_t = self.define_function(print_s)?;
        self.add_method(
            print_t,
            Method {
                signature: vec![i64_t],
                instance: alpha_print_i64,
            },
        );
        self.add_method(
            print_t,
            Method {
                signature: vec![f64_t],
                instance: alpha_print_f64,
            },
        );
        self.add_method(
            print_t,
            Method {
                signature: vec![datatype],
                instance: alpha_print_datatype,
            },
        );
        self.add_method(
            print_t,
            Method {
                signature: vec![abstracttype],
                instance: alpha_print_abstracttype,
            },
        );

        self.eval(
            r#"
              fn *(x: f64, y: f64) = f64_mul(x, y)
              fn *(x: i64, y: i64) = i64_mul(x, y)
            "#,
        )?;

        Ok(())
    }

    pub fn eval(&mut self, s: &str) -> Result<(), Box<dyn Error>> {
        println!("eval: {}", s);
        let mut parser = Parser::new(s);
        while parser.has_input() {
            let sexp = parser.parse()?;
            println!("sexp: {}", sexp);
            println!();

            let exp = lower_sexp(&sexp, &mut self.interner)?;
            println!("exp: {:?}\n", &exp);

            self.eval_exp(exp)?;
        }

        Ok(())
    }

    fn eval_exp(&mut self, exp: Exp) -> Result<(), Box<dyn Error>> {
        match exp {
            Exp::Type(t) => {
                let alpha_type = AlphaType::from_exp(&t, &self.types)?;
                self.eval_type(&alpha_type)?;
            }
            Exp::Function(f) => self.eval_function_definition(f)?,
            e => self.eval_anonymous_expression(e)?,
        }
        Ok(())
    }

    // Build a global type binding and initialize it. This does not execute any code inside the JIT.
    fn eval_type(&mut self, alpha_type: &AlphaType) -> Result<AnyPtrMut, Box<dyn Error>> {
        println!("type lowered to {:?}", alpha_type);

        let name = self.interner.resolve(alpha_type.name).unwrap().to_string();
        let module = self.context.context().create_module(&name);

        let supertype_t = self
            .global_env
            .lookup(alpha_type.supertype)
            .ok_or_else(|| {
                simple_error!(
                    "unable to find type: {}",
                    self.interner.resolve(alpha_type.supertype).unwrap()
                )
            })?;
        let supertype_ptr = self
            .jit
            .lookup::<*const *const AbstractType>(supertype_t.as_global())?;

        let type_ptr = if alpha_type.typedef == AlphaTypeDef::Abstract {
            // TODO: verify the type is abstract
            let abstracttype_t = self.jit.lookup::<*const *const DataType>("AbstractType")?;
            let type_ptr = unsafe {
                let type_ptr =
                    gc_allocate(std::mem::size_of::<AbstractType>() as u64) as *mut AbstractType;
                set_typetag(type_ptr, *abstracttype_t);
                *type_ptr = AbstractType {
                    supertype: *supertype_ptr,
                    name: name.to_string(),
                };
                type_ptr
            };

            type_ptr as AnyPtrMut
        } else {
            let type_size = alpha_type
                .typedef
                .size()
                .expect("unsized types are not supported yet");
            let n_ptrs = alpha_type
                .typedef
                .n_ptrs()
                .expect("abstract types are not supported yet");

            let datatype_t = self.jit.lookup::<*const *const DataType>("DataType")?;
            let type_ptr = unsafe {
                let type_ptr = gc_allocate(std::mem::size_of::<DataType>() as u64) as *mut DataType;
                set_typetag(type_ptr, *datatype_t);
                *type_ptr = DataType {
                    supertype: *supertype_ptr,
                    size: type_size as u64,
                    n_ptrs: n_ptrs as u64,
                    methods: Vec::new(),
                    name: name.to_string(),
                };
                type_ptr
            };

            let t = self.build_type_specifier(&alpha_type)?;
            eprint!("defined type: ");
            t.dump_to_stderr();
            eprint!(
                " size={}, n_ptrs={}, is_inlinable={}, has_ptrs={}, is_ptr={}",
                type_size,
                n_ptrs,
                alpha_type.typedef.is_inlinable(),
                alpha_type.typedef.has_ptrs(),
                alpha_type.typedef.is_ptr(),
            );
            eprintln!();

            type_ptr as AnyPtrMut
        };

        let ptr_t = self
            .context
            .context()
            .get_named_struct(if alpha_type.typedef == AlphaTypeDef::Abstract {
                "AbstractType"
            } else {
                "DataType"
            })
            .unwrap()
            .pointer_type(AddressSpace::Generic);

        self.inject_global(&module, &name, ptr_t, type_ptr);

        self.globals.add_global(&name, ptr_t); // without initializer here
        self.global_env
            .insert(alpha_type.name, EnvValue::Global(name.to_string()));
        self.types.insert(alpha_type.name, alpha_type.clone());

        self.load_module(module)?;

        Ok(type_ptr as AnyPtrMut)
    }

    fn build_type_specifier(&mut self, type_: &AlphaType) -> Result<Type, Box<dyn Error>> {
        let name = self.interner.resolve(type_.name).unwrap();
        let t = match &type_.typedef {
            AlphaTypeDef::Abstract => panic!("build_type_specifier is called for Abstract type"),
            AlphaTypeDef::Int(size) => {
                let i = self.context.context().int_type(*size as u32);
                let t = self
                    .context
                    .context()
                    .create_named_struct_type(name)
                    .struct_set_body(&[i], false);
                t
            }
            AlphaTypeDef::Float(size) => {
                let i = self.context.context().float_type(*size as u32);
                let t = self
                    .context
                    .context()
                    .create_named_struct_type(name)
                    .struct_set_body(&[i], false);
                t
            }
            AlphaTypeDef::Struct { fields } => {
                let v = fields
                    .iter()
                    .map(|(_name, type_)| {
                        let name = self.interner.resolve(type_.name).unwrap();
                        if type_.typedef == AlphaTypeDef::Abstract {
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

    fn eval_function_definition(&mut self, mut def: exp::Function) -> Result<(), Box<dyn Error>> {
        let fn_name_s = def.prototype.name;
        let fn_name = self.interner.resolve(fn_name_s).unwrap().to_string();
        let method_name = format!("{}.method.{}", fn_name, self.next_counter());
        let method_name_s = self.interner.intern(&method_name);

        def.prototype.name = method_name_s;

        let fn_t = self.ensure_function(fn_name_s)?;

        // compile method
        let module = self.new_module(&method_name);
        let instance = Compiler::compile(
            &mut self.interner,
            self.context.context(),
            &module,
            &self.global_env,
            &def,
        )?;
        let instance_fn_name = instance.get_name();
        self.load_module(module)?;
        let instance = self.jit.lookup::<GenericFn>(instance_fn_name)?;

        self.add_method(
            fn_t,
            Method {
                signature: def
                    .prototype
                    .params
                    .iter()
                    .map(|p| {
                        let llvm_name = match self.global_env.lookup(p.typ) {
                            Some(EnvValue::Global(s)) => s,
                            _ => panic!("unable to lookup: {:?}", p.typ),
                        };
                        unsafe {
                            *self
                                .jit
                                .lookup::<*const *const DataType>(llvm_name)
                                .unwrap()
                        }
                    })
                    .collect(),
                instance,
            },
        );

        Ok(())
    }

    /// Ensure a function `name` is defined. Defines it if it does not exist.
    fn ensure_function(&mut self, name: Symbol) -> Result<*mut DataType, Box<dyn Error>> {
        match self.global_env.lookup(name) {
            Some(EnvValue::Global(name)) => unsafe {
                return Ok(type_of(*self.jit.lookup::<*const AnyPtr>(name)?) as *mut DataType);
            },
            _ => {}
        }

        self.define_function(name)
    }

    fn define_function(&mut self, symbol: Symbol) -> Result<*mut DataType, Box<dyn Error>> {
        let name = self.interner.resolve(symbol).unwrap().to_string();

        let fn_t = self.define_function_type(&name)?;
        self.define_function_object(symbol, fn_t)?;

        Ok(fn_t)
    }

    fn define_function_type(&mut self, fn_name: &str) -> Result<*mut DataType, Box<dyn Error>> {
        let any_s = self.interner.intern("Any");
        let fn_t_name = self.interner.intern(&(fn_name.to_string() + "_t"));
        let fn_t = self.eval_type(&AlphaType {
            name: fn_t_name,
            supertype: any_s,
            typedef: AlphaTypeDef::Struct { fields: Vec::new() },
        })?;
        Ok(fn_t as *mut DataType)
    }

    fn define_function_object(
        &mut self,
        symbol: Symbol,
        fn_t: *const DataType,
    ) -> Result<(), Box<dyn Error>> {
        let name = self.interner.resolve(symbol).unwrap();

        // allocate function object
        let f = unsafe {
            let f = gc_allocate(0);
            set_typetag(f, fn_t);
            f
        };
        let module = self.new_module(&(name.to_string() + "_fn_object"));
        let any_ptr_t = self
            .context
            .context()
            .get_named_struct("Any")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let f_global = self.inject_global(&module, &("fn_".to_string() + &name), any_ptr_t, f);
        let f_global_name = f_global.get_name();
        self.global_env
            .insert(symbol, EnvValue::Global(f_global_name.to_string()));
        self.save_global_declarations(&module);
        self.load_module(module)?;

        Ok(())
    }

    fn add_method(&mut self, fn_t: *mut DataType, method: Method) {
        unsafe {
            (*fn_t).methods.push(method);
        }
    }

    fn eval_anonymous_expression(&mut self, e: Exp) -> Result<(), Box<dyn Error>> {
        let def = exp::Function {
            prototype: exp::FunctionPrototype {
                name: self.interner.intern("*anonymous*"),
                params: vec![],
                result_type: self.interner.intern("Any"),
            },
            body: Some(Box::new(e)),
        };

        let module = self.new_module("user");

        let f = Compiler::compile(
            &mut self.interner,
            self.context.context(),
            &module,
            &self.global_env,
            &def,
        )?;

        let name = f.get_name();

        self.save_global_declarations(&module);
        // We don't save function declarations as the only new function here is *anonymous* and
        // we don't need to save it.

        let tracker = self.load_module_with_tracker(module)?;
        let fun = self.jit.lookup::<GenericFn>(&name)?;
        unsafe {
            let result = fun(std::ptr::null(), 0, std::ptr::null());
            dump_value("result", result);
        }

        // This was just an anonymous function. We can unload the module as it is no longer
        // useful.
        tracker.remove()?;

        Ok(())
    }

    fn save_global_declarations(&mut self, module: &Module) {
        for v in module.globals() {
            if self.globals.get_global(v.get_name()).is_none() {
                self.globals
                    .add_global(v.get_name(), v.get_type().element_type());
            }
        }
    }

    /// Add a global named `name` to the `module` and set initializer to point to `value`.
    fn inject_global<T>(&self, module: &Module, name: &str, typ: Type, value: *const T) -> Value {
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
}
