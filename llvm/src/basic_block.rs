use llvm_sys::core::*;
use llvm_sys::prelude::*;

use crate::values::Value;

#[derive(Debug, Clone, Copy)]
pub struct BasicBlock(pub(crate) LLVMBasicBlockRef);

impl BasicBlock {
    pub(crate) fn new(bb_ref: LLVMBasicBlockRef) -> Self {
        assert!(!bb_ref.is_null());
        BasicBlock(bb_ref)
    }

    pub fn get_parent(&self) -> Value {
        unsafe { Value::new(LLVMGetBasicBlockParent(self.0)) }
    }
}
