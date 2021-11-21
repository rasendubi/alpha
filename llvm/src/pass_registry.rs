use llvm_sys::core::*;
use llvm_sys::prelude::*;

pub struct PassRegistry(pub(crate) LLVMPassRegistryRef);

impl PassRegistry {
    pub fn global() -> Self {
        unsafe {
            let registry = LLVMGetGlobalPassRegistry();
            assert!(!registry.is_null());
            PassRegistry(registry)
        }
    }

    pub fn initialize_core(&self) {
        unsafe {
            llvm_sys::initialization::LLVMInitializeCore(self.0);
        }
    }

    pub fn initialize_codegen(&self) {
        unsafe {
            llvm_sys::initialization::LLVMInitializeCodeGen(self.0);
        }
    }

    pub fn initialize_target(&self) {
        unsafe {
            llvm_sys::initialization::LLVMInitializeTarget(self.0);
        }
    }
}
