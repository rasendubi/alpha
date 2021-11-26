use std::ffi::CStr;
use std::fmt;

use llvm_sys::error::*;

#[derive(Debug)]
pub struct LLVMError {
    type_id: LLVMErrorTypeId,
    message: String,
}

impl LLVMError {
    pub(crate) fn new(error: LLVMErrorRef) -> Self {
        assert!(!error.is_null());
        unsafe {
            let type_id = LLVMGetErrorTypeId(error);
            let llvm_message = LLVMGetErrorMessage(error); // transfers ownership of error
            let message = CStr::from_ptr(llvm_message).to_str().unwrap().to_string();
            LLVMDisposeErrorMessage(llvm_message);

            LLVMError { type_id, message }
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for LLVMError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "LLVMError({:#?}): {}", self.type_id, self.message)
    }
}

impl std::error::Error for LLVMError {}

unsafe impl Sync for LLVMError {}
unsafe impl Send for LLVMError {}
