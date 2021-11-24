use llvm::pass_registry::PassRegistry;

pub fn init() {
    crate::types::init();

    init_llvm();
}

fn init_llvm() {
    llvm::gc::link_all_builtin_gcs();

    let pass_registry = PassRegistry::global();
    pass_registry.initialize_core();
    pass_registry.initialize_codegen();
    pass_registry.initialize_target();

    llvm::init::initialize_native_target();
    llvm::init::initialize_native_asm_printer();
}
