use crate::ast::exp::lower_sexp;
use crate::ast::parser::Parser;
use crate::dispatch::*;
use crate::gc::{self, GcRoot, GcRootChain, GC_ROOT_CHAIN};
use crate::gc_box;
use crate::hir;
use crate::irgen::*;
use crate::stdlib::*;
use crate::types::*;

use llvm::orc::lljit::{LLJITBuilder, LLJIT};
use llvm::orc::thread_safe::ThreadSafeContext;

use anyhow::Result;
use tracing::trace;

unsafe extern "C" fn alpha_add_global_root(root: *mut AnyPtr) {
    gc::add_global_root(GcRoot::from_ptr_ref(root));
}
unsafe extern "C" fn alpha_add_method(
    datatype: *mut DataType,
    signature: *const SVec,
    instance: GenericFn,
) {
    gc_box!(datatype);
    let method = Method::new(signature, instance);
    DataType::add_method(datatype.load_mut(), method);
}

pub struct ExecutionSession {
    print_results: bool,

    jit: LLJIT,
    hirgen: hir::HirGen,

    // Context should be the last field, so that other fields (jit) are disposed _before_ context is
    // disposed.
    context: ThreadSafeContext,
}

impl<'ctx> ExecutionSession {
    pub fn new() -> Self {
        let context = ThreadSafeContext::new();
        let jit = LLJITBuilder::new().build().unwrap();

        let mut es = ExecutionSession {
            print_results: false,
            context,
            hirgen: hir::HirGen::new(),
            jit,
        };

        es.build_stdlib().unwrap();

        es
    }

    pub fn set_print_results(&mut self, print_results: bool) {
        self.print_results = print_results;
    }

    /// Build Alpha standard library.
    ///
    /// This functions must be called once before any other operation on ExecutionSession.
    fn build_stdlib(&mut self) -> Result<()> {
        use hir::*;

        // If that's a second instantiation of ExecutionSession, delete previously stored
        // constructors.
        // TODO: not thread-safe
        unsafe {
            DataType::reset_methods(DATATYPE_T.load_mut());
        }

        self.hirgen
            .insert_global(symbol("Any"), *ANY_T_V, Type::T(*DATATYPE_T_V));
        self.hirgen
            .insert_global(symbol("DataType"), *DATATYPE_T_V, Type::T(*DATATYPE_T_V));
        self.hirgen
            .insert_global(symbol("Void"), *VOID_T_V, Type::T(*DATATYPE_T_V));
        self.hirgen
            .insert_global(symbol("void"), *VOID_V, Type::T(*VOID_T_V));
        self.hirgen
            .insert_global(symbol("i64"), *I64_T_V, Type::T(*DATATYPE_T_V));
        self.hirgen
            .insert_global(symbol("f64"), *F64_T_V, Type::T(*DATATYPE_T_V));
        self.hirgen
            .insert_global(symbol("String"), *STRING_T_V, Type::T(*DATATYPE_T_V));

        IrGen::bootstrap_context(self.context.context());

        self.jit
            .define_symbol("_Unwind_Resume", _Unwind_Resume as usize)?;
        self.jit
            .define_symbol("__gcc_personality_v0", __gcc_personality_v0 as usize)?;
        self.jit.define_symbol("llvm_gc_root_chain", unsafe {
            &mut GC_ROOT_CHAIN as *mut GcRootChain as usize
        })?;

        self.jit
            .define_symbol("gc_allocate", gc_allocate as usize)?;
        self.jit.define_symbol("mk_str", mk_str as usize)?;
        self.jit
            .define_symbol("select_method", dispatch_select as usize)?;
        self.jit
            .define_symbol("add_global_root", alpha_add_global_root as usize)?;
        self.jit
            .define_symbol("add_method", alpha_add_method as usize)?;

        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::ANY_T_V),
            ANY_T.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::TYPE_T_V),
            TYPE_T.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::DATATYPE_T_V),
            DATATYPE_T.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::SYMBOL_T_V),
            SYMBOL_T.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::SVEC_T_V),
            SVEC_T.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::SVEC_EMPTY),
            crate::types::SVEC_EMPTY.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::STRING_T_V),
            STRING_T.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::VOID_T_V),
            VOID_T.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::VOID_V),
            VOID.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::F64_T_V),
            F64_T.as_ref() as *const _ as usize,
        )?;
        self.jit.define_symbol(
            &IrGen::var_to_global_name(*hir::I64_T_V),
            I64_T.as_ref() as *const _ as usize,
        )?;

        self.jit.define_symbol("type_of", alpha_type_of as usize)?;
        self.jit.define_symbol("i64_mul", alpha_i64_mul as usize)?;
        self.jit.define_symbol("f64_mul", alpha_f64_mul as usize)?;
        self.jit
            .define_symbol("print_any", alpha_print_any as usize)?;
        self.jit
            .define_symbol("print_void", alpha_print_void as usize)?;
        self.jit
            .define_symbol("print_i64", alpha_print_i64 as usize)?;
        self.jit
            .define_symbol("print_f64", alpha_print_f64 as usize)?;
        self.jit
            .define_symbol("print_string", alpha_print_string as usize)?;
        self.jit
            .define_symbol("print_datatype", alpha_print_datatype as usize)?;

        // poor man's standard library
        self.eval(
            r#"
              # type i64: Number = integer(64)
              # type f64: Number = float(64)

              @intrinsic("type_of")
              fn type_of(x: Any): DataType

              @intrinsic("f64_mul")
              fn *(x: f64, y: f64): f64
              @intrinsic("i64_mul")
              fn *(x: i64, y: i64): i64

              @intrinsic("print_any")
              fn print(x: Any): Void
              @intrinsic("print_datatype")
              fn print(x: DataType): Void
              @intrinsic("print_void")
              fn print(x: Void): Void
              @intrinsic("print_i64")
              fn print(x: i64): Void
              @intrinsic("print_f64")
              fn print(x: f64): Void
              @intrinsic("print_string")
              fn print(x: String): Void

              fn println(x) = { print(x); print("\n") }
            "#,
        )?;

        Ok(())
    }

    pub fn eval(&mut self, s: &str) -> Result<()> {
        trace!("eval: {}", s);
        let mut parser = Parser::new(s);
        while parser.has_input() {
            let sexp = parser.parse()?;
            trace!("sexp: {}", sexp);

            let exp = lower_sexp(&sexp)?;
            trace!("exp: {:?}", &exp);

            let hir = self.hirgen.compile_top_level(&exp)?;
            trace!("env: {:#?}", &self.hirgen);
            trace!("hir: {:#?}", hir);

            let (module, entry_name) = IrGen::compile(self.context.context(), &hir)?;
            trace!("LLVM IR: {:?}", module);

            self.jit.add_module(self.context.create_module(module))?;

            let entry = self.jit.lookup::<GenericFn>(&entry_name)?;
            unsafe {
                let result = entry(std::ptr::null());
                if self.print_results && !result.is_null() && result != VOID.load().cast() {
                    println!("{:?}", *result);
                }
            }

            self.hirgen.commit(&hir);
        }

        Ok(())
    }
}
