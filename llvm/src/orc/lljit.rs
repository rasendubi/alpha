use std::ffi::CString;

use llvm_sys::orc2::lljit::*;
use llvm_sys::orc2::*;

use crate::error::LLVMError;
use crate::orc::thread_safe::ThreadSafeModule;

pub struct LLJITBuilder(pub(crate) LLVMOrcLLJITBuilderRef);

pub struct LLJIT(pub(crate) LLVMOrcLLJITRef);

impl LLJITBuilder {
    pub fn new() -> Self {
        unsafe { LLJITBuilder(LLVMOrcCreateLLJITBuilder()) }
    }

    /// Build [`LLJIT`] from the builder.
    ///
    /// # Examples
    /// ```
    /// # use llvm::orc::lljit::LLJITBuilder;
    /// let jit = LLJITBuilder::new().build();
    /// ```
    pub fn build(self) -> Result<LLJIT, LLVMError> {
        let mut result = std::ptr::null_mut();
        let error = unsafe { LLVMOrcCreateLLJIT(&mut result as *mut _, self.0) };
        std::mem::forget(self);

        if error.is_null() {
            Ok(LLJIT(result))
        } else {
            Err(LLVMError::new(error))
        }
    }
}

impl LLJIT {
    pub fn add_module(&self, module: ThreadSafeModule) -> Result<(), LLVMError> {
        unsafe {
            let dylib = LLVMOrcLLJITGetMainJITDylib(self.0);
            let err = LLVMOrcLLJITAddLLVMIRModule(self.0, dylib, module.0);
            std::mem::forget(module);
            if err.is_null() {
                Ok(())
            } else {
                Err(LLVMError::new(err))
            }
        }
    }

    pub fn add_module_with_tracker(
        &self,
        module: ThreadSafeModule,
    ) -> Result<ResourceTracker, LLVMError> {
        unsafe {
            let dylib = LLVMOrcLLJITGetMainJITDylib(self.0);
            let tracker = LLVMOrcJITDylibCreateResourceTracker(dylib);
            let err = LLVMOrcLLJITAddLLVMIRModuleWithRT(self.0, tracker, module.0);
            std::mem::forget(module);
            if err.is_null() {
                Ok(ResourceTracker(tracker))
            } else {
                Err(LLVMError::new(err))
            }
        }
    }

    pub fn lookup<T>(&self, name: &str) -> Result<T, LLVMError> {
        assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<usize>());
        unsafe {
            let name = CString::new(name).unwrap();
            let mut result: u64 = 0;
            let err = LLVMOrcLLJITLookup(self.0, &mut result as *mut _, name.as_ptr());

            if err.is_null() {
                Ok(std::mem::transmute_copy(&result))
            } else {
                Err(LLVMError::new(err))
            }
        }
    }

    pub fn define_symbol(&self, name: &str, addr: usize) -> Result<(), LLVMError> {
        unsafe {
            let name = CString::new(name).unwrap();
            let es = LLVMOrcLLJITGetExecutionSession(self.0);
            let name = LLVMOrcExecutionSessionIntern(es, name.as_ptr());
            let symbols = [LLVMJITCSymbolMapPair {
                Name: name,
                Sym: LLVMJITEvaluatedSymbol {
                    Address: addr as u64,
                    Flags: LLVMJITSymbolFlags {
                        GenericFlags: 0,
                        TargetFlags: 0,
                    },
                },
            }];
            let mu = LLVMOrcAbsoluteSymbols(symbols.as_ptr() as *mut _, symbols.len());

            let dylib = LLVMOrcLLJITGetMainJITDylib(self.0);
            let err = LLVMOrcJITDylibDefine(dylib, mu);
            if err.is_null() {
                Ok(())
            } else {
                Err(LLVMError::new(err))
            }
        }
    }
}

// These three are copied from llvm_sys because it does not expose fields, so we could not construct
// them.
#[repr(C)]
#[derive(Debug)]
#[allow(non_snake_case)]
pub struct LLVMJITCSymbolMapPair {
    Name: LLVMOrcSymbolStringPoolEntryRef,
    Sym: LLVMJITEvaluatedSymbol,
}
#[repr(C)]
#[derive(Debug)]
#[allow(non_snake_case)]
pub struct LLVMJITEvaluatedSymbol {
    Address: LLVMOrcExecutorAddress,
    Flags: LLVMJITSymbolFlags,
}
#[repr(C)]
#[derive(Debug)]
#[allow(non_snake_case)]
pub struct LLVMJITSymbolFlags {
    GenericFlags: u8,
    TargetFlags: u8,
}

impl Drop for LLJITBuilder {
    fn drop(&mut self) {
        unsafe {
            LLVMOrcDisposeLLJITBuilder(self.0);
        }
    }
}

impl Drop for LLJIT {
    fn drop(&mut self) {
        unsafe {
            LLVMOrcDisposeLLJIT(self.0);
        }
    }
}

pub struct ResourceTracker(LLVMOrcResourceTrackerRef);

impl ResourceTracker {
    pub fn remove(&self) -> Result<(), LLVMError> {
        unsafe {
            let err = LLVMOrcResourceTrackerRemove(self.0);
            if err.is_null() {
                Ok(())
            } else {
                Err(LLVMError::new(err))
            }
        }
    }
}

impl Drop for ResourceTracker {
    fn drop(&mut self) {
        unsafe {
            LLVMOrcReleaseResourceTracker(self.0);
        }
    }
}
