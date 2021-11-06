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

thread_local! {
    static GC: RefCell<Gc> = RefCell::new(unsafe { Gc::new_uninit() });
}

unsafe extern "C" fn gc_allocate(size: u64) -> *mut u8 {
    GC.with(|gc| gc.borrow_mut().allocate(size as usize))
}

unsafe extern "C" fn type_of(x: *const *const u8) -> *const u8 {
    let result = *x.sub(1);
    // println!(
    //     "type_of({:#?}) = {:#?} (typetag @ {:#?})",
    //     x,
    //     result,
    //     x.sub(1)
    // );
    result
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

  define %Any* @f64_mul(%Any* %a, %Any* %b) {
  entry:
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

  define %Any* @i64_mul(%Any* %a, %Any* %b) {
  entry:
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

        let mut es = ExecutionSession {
            context,
            interner,
            global_env,
            jit,
            globals,
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
        let any = self.context.context().create_named_struct_type("Any"); // opaque
        let datatype = self.context.context().create_named_struct_type("DataType"); // to be defined
        let datatype_ptr_t = datatype.pointer_type(AddressSpace::Generic);

        let ptr_t = any.pointer_type(AddressSpace::Generic);
        let i64_t = self.context.context().int_type(64);

        self.globals
            .add_function("gc_allocate", ptr_t.function_type(&[i64_t.into()], false));
        self.jit
            .define_symbol("gc_allocate", gc_allocate as usize)?;

        let datatype_type = unsafe {
            // Type is self-referencial:
            // typeof(DataType) == DataType
            let type_type = gc_allocate(0);
            let typetag = type_type.sub(8) as *mut *const _;
            *typetag = type_type;
            type_type
        };
        self.globals
            .add_global("DataType", datatype_ptr_t)
            .global_set_initializer(
                i64_t
                    .const_int(datatype_type as u64, false)
                    .const_int_to_pointer(datatype_ptr_t),
            );
        self.global_env.insert(
            self.interner.intern("DataType"),
            EnvValue::Global("DataType".to_string()),
        );

        let type_of_ = self
            .globals
            .add_function("type_of", ptr_t.function_type(&[ptr_t.into()], false));
        self.jit.define_symbol("type_of", type_of as usize)?;
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

        // stdlib.ll defines primitive operations
        self.load_ir_module("stdlib.ll", STDLIB_LL)?;
        self.globals
            .add_function("f64_mul", ptr_t.function_type(&[ptr_t, ptr_t], false));
        self.global_env.insert(
            self.interner.intern("f64_mul"),
            EnvValue::Function("f64_mul".to_string()),
        );
        self.globals
            .add_function("i64_mul", ptr_t.function_type(&[ptr_t, ptr_t], false));
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

    // Build a global type binding and initialize it. This does not execute any code inside the JIT.
    fn build_type(&mut self, type_: &exp::TypeDefinition) -> Result<(), Box<dyn Error>> {
        let type_t = self.jit.lookup::<*const *const u8>("DataType")?;
        let type_ptr = unsafe { gc_allocate(0) as *mut *const u8 };
        unsafe {
            // TODO: set_typetag() function
            let typetag_ptr = type_ptr.sub(1);
            *typetag_ptr = *type_t;
        }

        let name = self.interner.resolve(type_.name).unwrap();
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
            .insert(type_.name, EnvValue::Global(name.to_string()));

        let t = self.build_type_specifier(type_)?;
        eprint!("defined type: ");
        t.dump_to_stderr();
        eprintln!();

        self.load_module(module)?;

        Ok(())
    }

    fn build_type_specifier(
        &mut self,
        type_: &exp::TypeDefinition,
    ) -> Result<Type, Box<dyn Error>> {
        let name = self.interner.resolve(type_.name).unwrap();
        let t = match &type_.specifier {
            exp::TypeSpecifier::Integer(size) => {
                let i = self.context.context().int_type(*size as u32);
                let t = self
                    .context
                    .context()
                    .create_named_struct_type(name)
                    .struct_set_body(&[i], false);
                t
            }
            exp::TypeSpecifier::Float(size) => {
                let i = self.context.context().float_type(*size as u32);
                let t = self
                    .context
                    .context()
                    .create_named_struct_type(name)
                    .struct_set_body(&[i], false);
                t
            }
            exp::TypeSpecifier::Struct(fields) => {
                let any = self
                    .context
                    .context()
                    .get_named_struct("Any")
                    .unwrap()
                    .pointer_type(AddressSpace::Generic);
                let v = fields.iter().map(|_| any).collect::<Vec<_>>();
                let t = self
                    .context
                    .context()
                    .create_named_struct_type(name)
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
            return self.build_type(t);
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
            let fun = self.jit.lookup::<extern "C" fn() -> *const ()>(&name)?;
            unsafe {
                let result = fun();
                println!("result @ {:#?}", result);
                if !result.is_null() {
                    println!("type= {:p}", type_of(result as *const *const u8));
                    println!("f64= {:.5}", *(result as *const f64));
                    println!("u64= {}", *(result as *const u64));
                    println!("ptr= {:p}", *(result as *const *const ()));
                }
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
