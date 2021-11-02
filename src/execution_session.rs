use std::error::Error;
use std::cell::RefCell;

use inkwell::OptimizationLevel;
use inkwell::AddressSpace;
use inkwell::context::Context;
use inkwell::passes::PassManager;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue};
use inkwell::module::Module;

use crate::symbol::SymbolInterner;
use crate::env::Env;
use crate::parser::Parser;
use crate::compiler::Compiler;
use crate::sexp::SExp;
use crate::exp;
use crate::exp::{Exp, lower_sexp};
use crate::gc::Gc;

thread_local! {
    static GC: RefCell<Gc> = RefCell::new(unsafe { Gc::new_uninit() });
}

unsafe extern "C" fn gc_allocate(size: u64) -> *mut u8 {
    GC.with(|gc| {
        gc.borrow_mut().allocate(size as usize)
    })
}

unsafe extern "C" fn f64_mul(x: *const f64, y: *const f64) -> *const u8 {
    let value = *x * *y;
    let ptr = gc_allocate(std::mem::size_of::<f64>() as u64);
    *(ptr as *mut f64) = value;
    ptr
}

pub struct ExecutionSession<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    fpm: PassManager<FunctionValue<'ctx>>,
    interner: SymbolInterner,
    global_env: Env<'ctx, BasicValueEnum<'ctx>>,
}

impl<'ctx> ExecutionSession<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        GC.with(|gc| unsafe {
            gc.borrow_mut().init();
        });

        let module = context.create_module("user");

        let fpm = PassManager::create(&module);
        fpm.add_cfg_simplification_pass();
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_basic_alias_analysis_pass();
        fpm.initialize();

        let mut interner = SymbolInterner::new();
        let mut global_env = Env::new(None);

        let ptr_t = context.i8_type().ptr_type(AddressSpace::Generic);
        let i64_t = context.i64_type();

        module.add_function(
            "gc_allocate",
            ptr_t.fn_type(&[i64_t.into()], false),
            None
        );

        let f64_mul_ = module.add_function("f64_mul", ptr_t.fn_type(&[ptr_t.into(), ptr_t.into()], false), None);
        global_env.insert(interner.intern("f64_mul"), f64_mul_.as_global_value().as_basic_value_enum());

        let mut es = ExecutionSession {
            context,
            module,
            fpm,
            interner,
            global_env,
        };

        // poor man's standard library
        es.run_line(r#"
          type i64 = integer(64)
          type f64 = float(64)
          fn *(x: f64, y: f64) = f64_mul(x, y)
        "#).unwrap();

        es
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
        println!("lowered: {:?}", &exp);

        let (def, is_anonymous) = match exp {
            Exp::Type(_) => return Ok(()),
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
                true
            ),
        };

        let f = Compiler::compile(&self.interner, &self.context, &self.module, &self.fpm, &self.global_env, &def)?;
        f.print_to_stderr();

        let name = f.get_name().to_string_lossy();
        if is_anonymous {
            unsafe {
                let ee = self.module.create_jit_execution_engine(OptimizationLevel::None).unwrap();
                ee.add_global_mapping(&self.module.get_function("gc_allocate").unwrap(), gc_allocate as usize);
                ee.add_global_mapping(&self.module.get_function("f64_mul").unwrap(), f64_mul as usize);
                let fun = ee.get_function::<unsafe extern "C" fn() -> *const f64>(&name)?;
                println!("{}", *fun.call());
                ee.remove_module(&self.module).unwrap();
                f.delete();
            }
        } else {
            self.global_env.insert(def.prototype.name, f.as_global_value().as_basic_value_enum());
        }

        Ok(())
    }

    pub fn dump_module(&self) {
        self.module.print_to_stderr();
    }
}
