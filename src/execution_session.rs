use std::cell::RefCell;
use std::error::Error;

use llvm::module::Module;
use llvm::orc::lljit::{LLJITBuilder, ResourceTracker, LLJIT};
use llvm::orc::thread_safe::ThreadSafeContext;
use llvm::pass_manager::FunctionPassManager;
use llvm::types::{AddressSpace, Type};
use llvm::values::Value;

use crate::compiler::Compiler;
use crate::env::Env;
use crate::exp;
use crate::exp::{lower_sexp, Exp};
use crate::gc::Gc;
use crate::parser::Parser;
use crate::sexp::SExp;
use crate::symbol::SymbolInterner;
use crate::types::{AlphaType, AlphaTypeDef};

thread_local! {
    static GC: RefCell<Gc> = RefCell::new(unsafe { Gc::new_uninit() });
}

unsafe extern "C" fn gc_allocate(size: u64) -> *mut u8 {
    GC.with(|gc| gc.borrow_mut().allocate(size as usize))
}

type AnyPtr = *const u64;

unsafe fn dump_value(name: &str, value: AnyPtr) {
    println!("{} @ {:#?}", name, value);
    if !value.is_null() {
        println!("  type= {:p}", type_of(value as AnyPtr));
        println!("  f64= {:.5}", *(value as *const f64));
        println!("  u64= {}", *(value as *const u64));
        println!("  ptr= {:p}", *(value as *const *const ()));
    }
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

unsafe extern "C" fn dispatch(f: AnyPtr, n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let f_fn: unsafe extern "C" fn(AnyPtr, i64, *const AnyPtr) -> AnyPtr =
        std::mem::transmute_copy(&f);
    f_fn(f, n_args, args)
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
    Function(String),
    Local(Value),
}

pub struct ExecutionSession<'ctx> {
    // A module that contains global declarations to be copied into each new module. The module
    // itself is never passed into JIT.
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

    fn new_pass_manager(module: &Module) -> FunctionPassManager {
        let fpm = FunctionPassManager::new_for_module(module);
        // fpm.add_cfg_simplification_pass();
        // fpm.add_instruction_combining_pass();
        // fpm.add_reassociate_pass();
        // fpm.add_gvn_pass();
        // fpm.add_basic_alias_analysis_pass();
        // fpm.initialize();
        fpm
    }

    fn build_stdlib(&mut self) -> Result<(), Box<dyn Error>> {
        let any_t = self.context.context().create_named_struct_type("Any"); // opaque
        let datatype_t = self.context.context().create_named_struct_type("DataType"); // to be defined
        let datatype_ptr_t = datatype_t.pointer_type(AddressSpace::Generic);

        self.types.insert(
            self.interner.intern("Any"),
            AlphaType {
                name: self.interner.intern("Any"),
                typedef: AlphaTypeDef::Abstract,
            },
        );
        let datatype_typedef = AlphaType {
            name: self.interner.intern("DataType"),
            typedef: AlphaTypeDef::Struct {
                fields: vec![
                    (
                        self.interner.intern("size"),
                        AlphaType {
                            name: self.interner.intern("i64"),
                            typedef: AlphaTypeDef::Int(64),
                        },
                    ),
                    (
                        self.interner.intern("n_ptrs"),
                        AlphaType {
                            name: self.interner.intern("i64"),
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

        // assumed: type DataType = { size: i64, n_ptrs: i64 }
        // so that: let DataType = DataType { size: 16, n_ptrs: 16 }
        let datatype = unsafe {
            let datatype = gc_allocate(16) as *mut u64;
            // Type is self-referencial:
            // typeof(DataType) == DataType
            Self::set_typetag(datatype, datatype as *const ());
            *datatype.add(0) = 16;
            *datatype.add(1) = 0;
            datatype
        };
        self.globals
            .add_global("DataType", datatype_ptr_t)
            .global_set_initializer(
                i64_t
                    .const_int(datatype as u64, false)
                    .const_int_to_pointer(datatype_ptr_t),
            );
        self.global_env.insert(
            self.interner.intern("DataType"),
            EnvValue::Global("DataType".to_string()),
        );

        let type_of_ = self.globals.add_function("type_of", fn_t);
        self.jit.define_symbol("type_of", alpha_type_of as usize)?;
        self.global_env.insert(
            self.interner.intern("type_of"),
            EnvValue::Function(type_of_.get_name().to_string()),
        );

        // Add a copy of the globals module to jit, so globals with initializers are defined.
        self.load_module(self.globals.clone())?;

        // poor man's standard library
        self.run_line(
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

        // stdlib.ll defines primitive operations
        self.load_ir_module("stdlib.ll", STDLIB_LL)?;
        self.globals.add_function("f64_mul", fn_t);
        self.global_env.insert(
            self.interner.intern("f64_mul"),
            EnvValue::Function("f64_mul".to_string()),
        );
        self.globals.add_function("i64_mul", fn_t);
        self.global_env.insert(
            self.interner.intern("i64_mul"),
            EnvValue::Function("i64_mul".to_string()),
        );

        self.run_line(
            r#"
              fn *(x: f64, y: f64) = f64_mul(x, y)
            "#,
        )?;

        Ok(())
    }

    pub fn run_line(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        let mut parser = Parser::new(line);
        while parser.has_input() {
            let sexp = parser.parse()?;
            println!("sexp: {}", sexp);
            self.run_sexp(&sexp)?;
        }

        Ok(())
    }

    unsafe fn set_typetag<T>(ptr: *mut T, typetag: *const ()) {
        let typetag_ptr = (ptr as *mut u64).sub(1) as *mut *const ();
        *typetag_ptr = typetag;
    }

    // Build a global type binding and initialize it. This does not execute any code inside the JIT.
    fn build_type(&mut self, alpha_type: &AlphaType) -> Result<(), Box<dyn Error>> {
        println!("type lowered to {:?}", alpha_type);

        let type_size = alpha_type
            .typedef
            .size()
            .expect("unsized types are not supported yet");
        let n_ptrs = alpha_type
            .typedef
            .n_ptrs()
            .expect("abstract types are not supported yet");

        // assumed: type DataType = { size: i64, n_ptrs: i64 }
        // so that: let DataType = DataType { size: 16, n_ptrs: 0 }
        let datatype_t = self.jit.lookup::<*const *const ()>("DataType")?;
        let type_ptr = unsafe {
            let type_ptr = gc_allocate(8) as *mut u64;
            Self::set_typetag(type_ptr, *datatype_t);
            *type_ptr.add(0) = type_size as u64;
            *type_ptr.add(1) = n_ptrs as u64;

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

        let name = self.interner.resolve(alpha_type.name).unwrap();
        let module = self.context.context().create_module(name);

        let ptr_t = self
            .context
            .context()
            .get_named_struct("DataType")
            .unwrap()
            .pointer_type(AddressSpace::Generic);
        let i64_t = self.context.context().int_type(64);
        let type_global = module.add_global(name, ptr_t);
        type_global.global_set_initializer(
            i64_t
                .const_int(type_ptr as u64, false)
                .const_int_to_pointer(ptr_t),
        );

        self.globals.add_global(name, ptr_t); // without initializer here
        self.global_env
            .insert(alpha_type.name, EnvValue::Global(name.to_string()));
        self.types.insert(alpha_type.name, alpha_type.clone());

        self.load_module(module)?;

        Ok(())
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
                    .map(|(_name, typ)| {
                        let name = self.interner.resolve(typ.name).unwrap();
                        let field_t = self.context.context().get_named_struct(name).unwrap();
                        if typ.typedef.is_inlinable() {
                            field_t
                        } else {
                            field_t.pointer_type(AddressSpace::Generic)
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

    /// Load IR module using a standalone context. This way, the module can (re)define any types or
    /// functions without clogging the global context.
    ///
    /// The side effect is that global functions/types defined in the IR module must be explicitly
    /// added to the default context for them to be available.
    fn load_ir_module(&mut self, name: &str, ir: &str) -> Result<(), Box<dyn Error>> {
        let context = ThreadSafeContext::new();
        let module = context.context().parse_ir_module(name, ir)?;
        module.dump_to_stderr();
        let module = context.create_module(module);
        self.jit.add_module(module)?;
        Ok(())
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

    fn run_sexp(&mut self, sexp: &SExp) -> Result<(), Box<dyn Error>> {
        let exp = lower_sexp(&sexp, &mut self.interner)?;
        println!("\nexp: {:?}\n", &exp);

        if let Exp::Type(t) = &exp {
            let alpha_type = AlphaType::from_exp(t, &self.types)?;
            return self.build_type(&alpha_type);
        }

        let (def, is_anonymous) = match exp {
            Exp::Function(f) => (f, false),
            e => (
                exp::Function {
                    prototype: exp::FunctionPrototype {
                        name: self.interner.intern("*anonymous*"),
                        params: vec![],
                        result_type: None,
                    },
                    body: Some(Box::new(e)),
                },
                true,
            ),
        };

        let module = self.new_module("user");
        let fpm = Self::new_pass_manager(&module);

        let f = Compiler::compile(
            &mut self.interner,
            self.context.context(),
            &module,
            &fpm,
            &self.global_env,
            &def,
        )?;

        let name = f.get_name();
        if is_anonymous {
            self.save_global_declarations(&module);
            // We don't save function declarations as the only new function here is *anonymous* and
            // we don't need to save it.

            let tracker = self.load_module_with_tracker(module)?;
            let fun = self
                .jit
                .lookup::<extern "C" fn(AnyPtr, i64, *const AnyPtr) -> AnyPtr>(&name)?;
            unsafe {
                let result = fun(std::ptr::null(), 0, std::ptr::null());
                dump_value("result", result);
            }

            // This was just an anonymous function. We can unload the module as it is no longer
            // useful.
            tracker.remove()?;
        } else {
            self.global_env
                .insert(def.prototype.name, EnvValue::Function(name.to_string()));

            self.save_global_declarations(&module);
            self.save_function_declarations(&module);

            self.load_module(module)?;
        }

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

    fn save_function_declarations(&mut self, module: &Module) {
        for v in module.functions() {
            if self.globals.get_function(v.get_name()).is_none() {
                self.globals
                    .add_function(v.get_name(), v.get_type().element_type());
            }
        }
    }
}
