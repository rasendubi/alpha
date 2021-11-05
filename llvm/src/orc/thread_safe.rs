use std::mem::ManuallyDrop;

use llvm_sys::orc2;

use crate::context::Context;
use crate::module::Module;

pub struct ThreadSafeContext {
    pub(crate) tsc: orc2::LLVMOrcThreadSafeContextRef,
    // This context is owned by tsc, so we never drop it.
    context: ManuallyDrop<Context>,
}

impl ThreadSafeContext {
    /// Create a [`ThreadSafeContext`] containing a new [`Context`].
    pub fn new() -> Self {
        unsafe {
            let tsc = orc2::LLVMOrcCreateNewThreadSafeContext();
            let context = ManuallyDrop::new(Context::from_ref(
                orc2::LLVMOrcThreadSafeContextGetContext(tsc),
            ));
            ThreadSafeContext { tsc, context }
        }
    }

    pub fn context(&self) -> &Context {
        &self.context
    }

    /// Create [`ThreadSafeModule`] from [`Module`] instance.
    pub fn create_module(&self, module: Module) -> ThreadSafeModule {
        let tsm =
            ThreadSafeModule(unsafe { orc2::LLVMOrcCreateNewThreadSafeModule(module.0, self.tsc) });
        // `module` is now owned by thread safe module.
        std::mem::forget(module);
        tsm
    }
}

// impl Deref for ThreadSafeContext {
//     type Target = Context;
//
//     fn deref(&self) -> &Context {
//         self.context()
//     }
// }

impl Drop for ThreadSafeContext {
    fn drop(&mut self) {
        unsafe {
            orc2::LLVMOrcDisposeThreadSafeContext(self.tsc);
        }
    }
}

pub struct ThreadSafeModule(pub(crate) orc2::LLVMOrcThreadSafeModuleRef);

impl ThreadSafeModule {}

impl Drop for ThreadSafeModule {
    fn drop(&mut self) {
        unsafe {
            orc2::LLVMOrcDisposeThreadSafeModule(self.0);
        }
    }
}
