use std::ffi::CString;

use llvm_sys::core;
use llvm_sys::prelude::*;

use crate::context::Context;
use crate::string::LLVMString;
use crate::types::Type;
use crate::values::Value;

pub struct Module(pub(crate) LLVMModuleRef);

impl Module {
    fn new(module: LLVMModuleRef) -> Self {
        Module(module)
    }

    pub(crate) fn from_ir_string(
        context: &Context,
        name: &str,
        s: &str,
    ) -> Result<Module, LLVMString> {
        unsafe {
            let name = CString::new(name).unwrap();
            let buffer = core::LLVMCreateMemoryBufferWithMemoryRangeCopy(
                s.as_ptr() as *const i8,
                s.len(),
                name.as_ptr(),
            );
            let mut module: LLVMModuleRef = std::ptr::null_mut();
            let mut message: *mut std::os::raw::c_char = std::ptr::null_mut();
            let err = llvm_sys::ir_reader::LLVMParseIRInContext(
                context.0,
                buffer,
                &mut module as *mut _,
                &mut message as *mut _,
            );
            // Buffer seems to be captured by LLVMParseIRInContext
            // core::LLVMDisposeMemoryBuffer(buffer);
            if err == 0 {
                Ok(Module(module))
            } else {
                Err(LLVMString::new(message))
            }
        }
    }

    pub fn new_in_context(context: &Context, name: &str) -> Self {
        let name = CString::new(name).unwrap();
        unsafe {
            Module::new(core::LLVMModuleCreateWithNameInContext(
                name.as_ptr(),
                context.0,
            ))
        }
    }

    /// Add a function to a module under a specified name.
    ///
    /// # Examples
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::TypeKind;
    /// # let ctx = Context::new();
    /// let module = ctx.create_module("user");
    /// let f = ctx.int_type(1).function_type(&[ctx.int_type(1)], false);
    /// module.add_function("not", f);
    /// ```
    pub fn add_function(&self, name: &str, type_: Type) -> Value {
        let name = CString::new(name).unwrap();
        unsafe { Value::new(core::LLVMAddFunction(self.0, name.as_ptr(), type_.0)) }
    }

    pub fn get_function(&self, name: &str) -> Option<Value> {
        let name = CString::new(name).unwrap();
        unsafe {
            let f = core::LLVMGetNamedFunction(self.0, name.as_ptr());
            if f.is_null() {
                None
            } else {
                Some(Value::new(f))
            }
        }
    }

    pub fn functions(&self) -> ModuleFunctionsIter {
        ModuleFunctionsIter {
            module: self.0,
            f: std::ptr::null_mut(),
            start: true,
        }
    }

    pub fn add_alias(&self, name: &str, ty: Type, aliasee: Value) -> Value {
        let name = CString::new(name).unwrap();
        eprintln!("add_alias({:?}, {:?}, {:?})", name, ty, aliasee);
        unsafe { Value::new(core::LLVMAddAlias(self.0, ty.0, aliasee.0, name.as_ptr())) }
    }
    pub fn get_alias(&self, name: &str) -> Option<Value> {
        unsafe {
            // IMPORTANT: even though `LLVMGetNamedGlobalAlias` accepts a pointer and length, the
            // length is actually not used and name must be NUL-terminated.
            let len = name.len();
            let name = CString::new(name).unwrap();
            let res = core::LLVMGetNamedGlobalAlias(self.0, name.as_ptr(), len);
            if res.is_null() {
                None
            } else {
                Some(Value::new(res))
            }
        }
    }

    pub fn add_global(&self, name: &str, type_: Type) -> Value {
        let name = CString::new(name).unwrap();
        unsafe { Value::new(core::LLVMAddGlobal(self.0, type_.0, name.as_ptr())) }
    }

    pub fn get_global(&self, name: &str) -> Option<Value> {
        let name = CString::new(name).unwrap();
        unsafe {
            let ptr = core::LLVMGetNamedGlobal(self.0, name.as_ptr());
            if ptr.is_null() {
                None
            } else {
                Some(Value::new(ptr))
            }
        }
    }

    pub fn globals(&self) -> ModuleGlobalsIter {
        ModuleGlobalsIter {
            module: self.0,
            g: std::ptr::null_mut(),
            start: true,
        }
    }

    /// Verify the module and return a string description on error.
    pub fn verify(&self) -> Result<(), LLVMString> {
        unsafe {
            use llvm_sys::analysis::*;
            use std::os::raw::c_char;

            let mut msg: *mut c_char = std::ptr::null_mut();
            let res = LLVMVerifyModule(
                self.0,
                LLVMVerifierFailureAction::LLVMReturnStatusAction,
                &mut msg,
            );

            if res == 0 {
                Ok(())
            } else {
                Err(LLVMString::new(msg))
            }
        }
    }

    /// Dump a representation of a module to stderr.
    ///
    /// ```
    /// use llvm::context::Context;
    /// let context = Context::new();
    /// let module = context.create_module("user");
    /// module.dump_to_stderr();
    /// ```
    pub fn dump_to_stderr(&self) {
        unsafe {
            core::LLVMDumpModule(self.0);
        }
    }

    pub fn dump(&self) -> LLVMString {
        unsafe { LLVMString::new(core::LLVMPrintModuleToString(self.0)) }
    }
}

impl Clone for Module {
    fn clone(&self) -> Self {
        unsafe { Module::new(core::LLVMCloneModule(self.0)) }
    }
}

impl Drop for Module {
    fn drop(&mut self) {
        unsafe {
            core::LLVMDisposeModule(self.0);
        }
    }
}

impl std::fmt::Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "Module({})", self.dump())
    }
}

impl std::fmt::Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.dump())
    }
}

pub struct ModuleFunctionsIter {
    module: LLVMModuleRef,
    f: LLVMValueRef,
    start: bool,
}

impl Iterator for ModuleFunctionsIter {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.f = if self.start {
                self.start = false;
                core::LLVMGetFirstFunction(self.module)
            } else if self.f.is_null() {
                self.f
            } else {
                core::LLVMGetNextFunction(self.f)
            };
        }

        if self.f.is_null() {
            None
        } else {
            Some(Value::new(self.f))
        }
    }
}

pub struct ModuleGlobalsIter {
    module: LLVMModuleRef,
    g: LLVMValueRef,
    start: bool,
}

impl Iterator for ModuleGlobalsIter {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.g = if self.start {
                self.start = false;
                core::LLVMGetFirstGlobal(self.module)
            } else if self.g.is_null() {
                self.g
            } else {
                core::LLVMGetNextGlobal(self.g)
            };
        }

        if self.g.is_null() {
            None
        } else {
            Some(Value::new(self.g))
        }
    }
}
