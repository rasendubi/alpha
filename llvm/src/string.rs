use std::os::raw::c_char;

use llvm_sys::core;

pub struct LLVMString(*mut c_char);

impl LLVMString {
    #[allow(dead_code)]
    pub(crate) unsafe fn new(str: *mut c_char) -> Self {
        LLVMString(str)
    }
}

impl Drop for LLVMString {
    fn drop(&mut self) {
        unsafe { core::LLVMDisposeMessage(self.0) }
    }
}
