pub fn initialize_native_target() {
    unsafe {
        llvm_sys::target::LLVM_InitializeNativeTarget();
    }
}

pub fn initialize_native_asm_printer() {
    unsafe {
        llvm_sys::target::LLVM_InitializeNativeAsmPrinter();
    }
}
