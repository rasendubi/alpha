use llvm_sys::core;
use llvm_sys::prelude::*;

use crate::module::Module;
use crate::values::{Value, ValueKind};

pub struct FunctionPassManager(pub(crate) LLVMPassManagerRef);

impl Drop for FunctionPassManager {
    fn drop(&mut self) {
        unsafe {
            core::LLVMDisposePassManager(self.0);
        }
    }
}

impl FunctionPassManager {
    pub fn new_for_module(module: &Module) -> Self {
        unsafe { FunctionPassManager(core::LLVMCreateFunctionPassManagerForModule(module.0)) }
    }

    /// Executes all of the function passes scheduled in the function pass manager on the provided
    /// function.
    ///
    /// Returns `true` if any of the passes modified the function, `false` otherwise.
    ///
    /// # Safety
    /// Panics if `f` is not a function.
    pub fn run(&self, f: Value) -> bool {
        assert_eq!(f.kind(), ValueKind::LLVMFunctionValueKind);
        unsafe { core::LLVMRunFunctionPassManager(self.0, f.0) != 0 }
    }

    pub fn add_instruction_combining_pass(&mut self) {
        unsafe {
            llvm_sys::transforms::scalar::LLVMAddInstructionCombiningPass(self.0);
        }
    }

    pub fn add_cfg_simplification_pass(&mut self) {
        unsafe {
            llvm_sys::transforms::scalar::LLVMAddCFGSimplificationPass(self.0);
        }
    }
}

pub struct ModulePassManager(pub(crate) LLVMPassManagerRef);

impl Drop for ModulePassManager {
    fn drop(&mut self) {
        unsafe {
            core::LLVMDisposePassManager(self.0);
        }
    }
}

impl ModulePassManager {
    pub fn new() -> ModulePassManager {
        unsafe { ModulePassManager(core::LLVMCreatePassManager()) }
    }

    pub fn run(&self, module: &Module) -> bool {
        unsafe { core::LLVMRunPassManager(self.0, module.0) != 0 }
    }
}
