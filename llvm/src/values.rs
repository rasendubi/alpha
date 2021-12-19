use std::ffi::CString;

use llvm_sys::core;
use llvm_sys::prelude::*;
pub use llvm_sys::LLVMLinkage;

use crate::basic_block::BasicBlock;
use crate::string::LLVMString;
use crate::types::Type;

pub use llvm_sys::LLVMValueKind as ValueKind;

#[derive(Clone, Copy)]
pub struct Value(pub(crate) LLVMValueRef);

impl Value {
    pub(crate) fn new(value_ref: LLVMValueRef) -> Self {
        assert!(!value_ref.is_null());
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
    pub fn set_gc(&self, name: &str) {
        let name = CString::new(name).unwrap();
        unsafe {
            core::LLVMSetGC(self.0, name.as_ptr());
        }
    }
    pub fn get_entry_block(&self) -> BasicBlock {
        assert_eq!(self.kind(), ValueKind::LLVMFunctionValueKind);
        unsafe { BasicBlock::new(core::LLVMGetEntryBasicBlock(self.0)) }
    }
    pub fn get_param_iter(&self) -> ParamValueIter {
        assert_eq!(self.kind(), ValueKind::LLVMFunctionValueKind);
        ParamValueIter {
            value: self.0,
            start: true,
        }
    }

    /// Convert constant integer to pointer.
    pub fn const_int_to_pointer(&self, type_: Type) -> Value {
        assert_eq!(self.kind(), ValueKind::LLVMConstantIntValueKind);
        unsafe { Value::new(core::LLVMConstIntToPtr(self.0, type_.0)) }
    }
    pub fn const_ptr_to_int(&self, to_type: Type) -> Value {
        unsafe { Value::new(core::LLVMConstPtrToInt(self.0, to_type.0)) }
    }

    pub fn const_add(&self, rhs: Value) -> Value {
        unsafe { Value::new(core::LLVMConstAdd(self.0, rhs.0)) }
    }
    pub fn const_gep(&self, indices: &[Value]) -> Value {
        let mut indices = indices.iter().map(|v| v.0).collect::<Vec<_>>();
        let num_indices = indices.len() as u32;
        let indices = indices.as_mut_ptr();
        unsafe { Value::new(core::LLVMConstGEP(self.0, indices, num_indices)) }
    }

    pub fn global_set_initializer(&self, init: Value) {
        assert_eq!(self.kind(), ValueKind::LLVMGlobalVariableValueKind);
        unsafe {
            core::LLVMSetInitializer(self.0, init.0);
        }
    }

    pub fn global_get_linkage(&self) -> LLVMLinkage {
        unsafe { core::LLVMGetLinkage(self.0) }
    }

    pub fn dump_to_stderr(&self) {
        unsafe {
            core::LLVMDumpValue(self.0);
        }
    }
    pub fn dump(&self) -> LLVMString {
        unsafe { LLVMString::new(core::LLVMPrintValueToString(self.0)) }
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

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "Value({})", self.dump())
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.dump())
    }
}
