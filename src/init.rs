use llvm::pass_registry::PassRegistry;

pub fn init() {
    crate::types::init();

    init_llvm();
}

fn init_llvm() {
    unsafe {
        alpha_llvm_link_all_builtin_gcs();
    }

    let pass_registry = PassRegistry::global();
    pass_registry.initialize_core();
    pass_registry.initialize_codegen();
    pass_registry.initialize_target();

    unsafe {
        llvm_sys::target::LLVM_InitializeNativeTarget();
        llvm_sys::target::LLVM_InitializeNativeAsmPrinter();
    }
}

extern "C" {
    fn alpha_llvm_link_all_builtin_gcs();
}
