pub fn init() {
    crate::types::init();

    init_llvm();
}

fn init_llvm() {
    unsafe {
        llvm_sys::target::LLVM_InitializeNativeTarget();
        llvm_sys::target::LLVM_InitializeNativeAsmPrinter();
    }
}
