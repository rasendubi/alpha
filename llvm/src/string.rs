use std::ffi::CStr;
use std::fmt;
use std::os::raw::c_char;

use llvm_sys::core;

pub struct LLVMString(*mut c_char);

impl LLVMString {
    pub(crate) unsafe fn new(str: *mut c_char) -> Self {
        LLVMString(str)
    }
}

impl Drop for LLVMString {
    fn drop(&mut self) {
        unsafe { core::LLVMDisposeMessage(self.0) }
    }
}

impl fmt::Display for LLVMString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", unsafe {
            CStr::from_ptr(self.0 as *const c_char).to_str().unwrap()
        })
    }
}

impl fmt::Debug for LLVMString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "LLVMString({})", self)
    }
}

impl std::error::Error for LLVMString {}
