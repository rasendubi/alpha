use llvm_sys::prelude::*;

pub struct BasicBlock(pub(crate) LLVMBasicBlockRef);

impl BasicBlock {
    pub(crate) fn new(bb_ref: LLVMBasicBlockRef) -> Self {
        BasicBlock(bb_ref)
    }
}
