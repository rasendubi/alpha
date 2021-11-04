use std::cell::RefCell;
use std::error::Error;

use llvm::context::Context;
use llvm::module::Module;
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
    *x.sub(1)
}

unsafe extern "C" fn f64_mul(x: *const f64, y: *const f64) -> *const u8 {
    let value = *x * *y;
    let ptr = gc_allocate(std::mem::size_of::<f64>() as u64);
    *(ptr as *mut f64) = value;
    ptr
}

pub enum EnvValue {
    Global(String),
    Function(String),
    Local(Value),
}

pub struct ExecutionSession<'ctx> {
    context: &'ctx Context,
    // fpm: PassManager<FunctionValue<'ctx>>,
    interner: SymbolInterner,
    // ee: ExecutionEngine<'ctx>,
    global_env: Env<'ctx, EnvValue>,
    // a module that contains global declarations to be copied into each new module
    globals: Module,
}

impl<'ctx> ExecutionSession<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        GC.with(|gc| unsafe {
            gc.borrow_mut().init();
        });

        let globals = context.create_module("globals");
        // let ee = globals.create_jit_execution_engine(OptimizationLevel::None).unwrap();
        // ee.remove_module(&module).unwrap();

        let interner = SymbolInterner::new();
        let global_env = Env::new(None);

        let mut es = ExecutionSession {
            context,
            interner,
            global_env,
            // ee,
            globals,
        };

        es.build_stdlib().unwrap();

        es
    }

    fn new_module(&self, name: &str) -> Module {
        let module = self.context.create_module(name);

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
        let ptr_t = self.context.int_type(8).pointer_type(AddressSpace::Generic);
        let i64_t = self.context.int_type(64);

        let gc_allocate_ = self
            .globals
            .add_function("gc_allocate", ptr_t.function_type(&[i64_t.into()], false));
        // gc_allocate_.set_initializer(i64_t.const_int(gc_allocate as u64).const_to_pointer(ptr_t));
        // self.ee.add_global_mapping(&gc_allocate_, gc_allocate as usize);

        let type_type = unsafe {
            // Type is self-referencial:
            // typeof(Type) == Type
            let type_type = gc_allocate(0);
            let typetag = type_type.sub(8) as *mut *const _;
            *typetag = type_type;
            type_type
        };
        let type_ = self.globals.add_global("type", ptr_t);
        self.global_env.insert(
            self.interner.intern("type"),
            EnvValue::Global(type_.get_name().to_string()),
        );
        // type_.set_constant(true);
        // type_.set_initializer(&i64_t.const_int(type_type as u64, false).const_to_pointer(ptr_t).as_basic_value_enum());
        // self.ee.add_global_mapping(&type_, type_type as usize);

        let type_of_ = self
            .globals
            .add_function("type_of", ptr_t.function_type(&[ptr_t.into()], false));
        self.global_env.insert(
            self.interner.intern("type_of"),
            EnvValue::Function(type_of_.get_name().to_string()),
        );
        // self.ee.add_global_mapping(&type_of_, type_of as usize);

        let f64_mul_ = self.globals.add_function(
            "f64_mul",
            ptr_t.function_type(&[ptr_t.into(), ptr_t.into()], false),
        );
        self.global_env.insert(
            self.interner.intern("f64_mul"),
            EnvValue::Function(f64_mul_.get_name().to_string()),
        );
        // self.ee.add_global_mapping(&f64_mul_, f64_mul as usize);

        self.globals.dump_to_stderr();

        // poor man's standard library
        self.run_line(
            r#"
              type i64 = integer(64)
              type f64 = float(64)
              fn *(x: f64, y: f64) = f64_mul(x, y)
            "#,
        )
        .unwrap();

        Ok(())
    }

    pub fn run_line(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        let mut parser = Parser::new(line);
        while parser.has_input() {
            self.run_sexp(&parser.parse()?)?;
        }

        Ok(())
    }

    fn run_sexp(&mut self, sexp: &SExp) -> Result<(), Box<dyn Error>> {
        let exp = lower_sexp(&sexp, &mut self.interner)?;
        println!("\nlowered: {:?}", &exp);

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
            &self.context,
            &module,
            &fpm,
            &self.global_env,
            &def,
        )?;
        eprintln!("\ncompiled:");
        module.dump_to_stderr();

        // self.ee.add_module(&module).unwrap();

        let name = f.get_name();
        if is_anonymous {
            for v in module.globals() {
                if self.globals.get_global(v.get_name()).is_none() {
                    self.globals
                        .add_global(v.get_name(), v.get_type().element_type());
                }
            }
            // unsafe {
            //     // let ee = self.module.create_jit_execution_engine(OptimizationLevel::None).unwrap();
            //     // ee.add_global_mapping(&self.module.get_function("gc_allocate").unwrap(), gc_allocate as usize);
            //     // ee.add_global_mapping(&self.module.get_function("type_of").unwrap(), type_of as usize);
            //     // ee.add_global_mapping(&self.module.get_function("f64_mul").unwrap(), f64_mul as usize);
            //     let fun = self.ee.get_function::<unsafe extern "C" fn() -> *const i8>(&name)?;
            //     let result = fun.call();
            //     println!("{}", *result);
            //     self.ee.remove_module(&module).unwrap();
            //     f.delete();
            // }
        } else {
            self.global_env
                .insert(def.prototype.name, EnvValue::Function(name.to_string()));
            for v in module.functions() {
                if self.globals.get_function(v.get_name()).is_none() {
                    self.globals
                        .add_function(v.get_name(), v.get_type().element_type());
                }
            }
            for v in module.globals() {
                if self.globals.get_global(v.get_name()).is_none() {
                    self.globals
                        .add_global(v.get_name(), v.get_type().element_type());
                }
            }
        }

        Ok(())
    }
}
