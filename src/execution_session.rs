use std::cell::RefCell;
use std::error::Error;

use llvm::module::Module;
use llvm::orc::lljit::{LLJITBuilder, ResourceTracker, LLJIT};
use llvm::orc::thread_safe::ThreadSafeContext;
use llvm::pass_manager::FunctionPassManager;
use llvm::types::AddressSpace;
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

unsafe extern "C" fn f64_mul(x: *const f64, y: *const f64) -> *const u8 {
    let value = *x * *y;
    let ptr = gc_allocate(std::mem::size_of::<f64>() as u64);
    *(ptr as *mut f64) = value;
    // println!("f64_mul({}, {}) = {} (@{:#?})", *x, *y, value, ptr);
    ptr
}

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
        let ptr_t = self
            .context
            .context()
            .int_type(8)
            .pointer_type(AddressSpace::Generic);
        let i64_t = self.context.context().int_type(64);

        self.globals
            .add_function("gc_allocate", ptr_t.function_type(&[i64_t.into()], false));
        self.jit
            .define_symbol("gc_allocate", gc_allocate as usize)?;

        let type_type = unsafe {
            // Type is self-referencial:
            // typeof(Type) == Type
            let type_type = gc_allocate(0);
            let typetag = type_type.sub(8) as *mut *const _;
            *typetag = type_type;
            type_type
        };
        self.globals
            .add_global("Type", ptr_t)
            .global_set_initializer(
                i64_t
                    .const_int(type_type as u64, false)
                    .const_int_to_pointer(ptr_t),
            );
        self.global_env.insert(
            self.interner.intern("Type"),
            EnvValue::Global("Type".to_string()),
        );

        let type_of_ = self
            .globals
            .add_function("type_of", ptr_t.function_type(&[ptr_t.into()], false));
        self.jit.define_symbol("type_of", type_of as usize)?;
        self.global_env.insert(
            self.interner.intern("type_of"),
            EnvValue::Function(type_of_.get_name().to_string()),
        );

        let f64_mul_ = self.globals.add_function(
            "f64_mul",
            ptr_t.function_type(&[ptr_t.into(), ptr_t.into()], false),
        );
        self.jit
            .define_symbol("f64_mul", f64_mul as usize)
            .unwrap_or_else(|err| panic!("{}", err.message()));
        self.global_env.insert(
            self.interner.intern("f64_mul"),
            EnvValue::Function(f64_mul_.get_name().to_string()),
        );

        // Add a copy of the globals module to jit, so globals with initializers are defined.
        let stdlib = self.globals.clone();
        stdlib.dump_to_stderr();
        let stdlib = self.context.create_module(stdlib);
        self.jit.add_module(stdlib)?;

        // poor man's standard library
        self.run_line(
            r#"
              type i64 = integer(64)
              type f64 = float(64)
              fn *(x: f64, y: f64) = f64_mul(x, y)
            "#,
        )?;

        Ok(())
    }

    pub fn run_line(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        let mut parser = Parser::new(line);
        while parser.has_input() {
            self.run_sexp(&parser.parse()?)?;
        }

        Ok(())
    }

    // Build a global type binding and initialize it. This does not execute any code inside the JIT.
    fn build_type(&mut self, type_: &exp::TypeDefinition) -> Result<(), Box<dyn Error>> {
        let type_t = self.jit.lookup::<*const *const u8>("Type")?;
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
            .int_type(8)
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

        self.load_module(module)?;

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
        println!("\nlowered: {:?}", &exp);

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
