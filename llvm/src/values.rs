use llvm_sys::core;
use llvm_sys::prelude::*;

use crate::types::Type;

pub use llvm_sys::LLVMValueKind as ValueKind;

#[derive(Clone, Copy)]
pub struct Value(pub(crate) LLVMValueRef);

impl Value {
    pub(crate) fn new(value_ref: LLVMValueRef) -> Self {
        Value(value_ref)
    }

    pub fn get_type(&self) -> Type {
        unsafe { Type::new(core::LLVMTypeOf(self.0)) }
    }

    pub fn kind(&self) -> ValueKind {
        unsafe { core::LLVMGetValueKind(self.0) }
    }

    pub fn set_name(&self, name: &str) {
        unsafe {
            core::LLVMSetValueName2(self.0, name.as_ptr() as *const i8, name.len());
        }
    }
    pub fn get_name(&self) -> &str {
        unsafe {
            let mut len: usize = 0;
            let s = core::LLVMGetValueName2(self.0, &mut len as *mut usize);
            let bytes = std::slice::from_raw_parts(s as *const u8, len);
            std::str::from_utf8(bytes).unwrap()
        }
    }

    pub unsafe fn delete_function(self) {
        assert_eq!(self.kind(), ValueKind::LLVMFunctionValueKind);
        core::LLVMDeleteFunction(self.0);
    }
    /// Returns `true` if function is valid, `false` otherwise.
    pub fn verify_function(&self) -> bool {
        assert_eq!(self.kind(), ValueKind::LLVMFunctionValueKind);
        unsafe {
            use llvm_sys::analysis::*;
            LLVMVerifyFunction(self.0, LLVMVerifierFailureAction::LLVMPrintMessageAction) == 0
        }
    }
    pub fn get_param_iter(&self) -> ParamValueIter {
        assert_eq!(self.kind(), ValueKind::LLVMFunctionValueKind);
        ParamValueIter {
            value: self.0,
            start: true,
        }
    }

    pub fn dump_to_stderr(&self) {
        unsafe {
            core::LLVMDumpValue(self.0);
        }
    }
}

pub struct ParamValueIter {
    value: LLVMValueRef,
    start: bool,
}

impl Iterator for ParamValueIter {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.value.is_null() {
            return None;
        }

        self.value = if self.start {
            self.start = false;
            unsafe { core::LLVMGetFirstParam(self.value) }
        } else {
            unsafe { core::LLVMGetNextParam(self.value) }
        };

        if self.value.is_null() {
            None
        } else {
            Some(Value::new(self.value))
        }
    }
}
