use std::ffi::CString;

use llvm_sys::core;
use llvm_sys::prelude::*;

use crate::basic_block::BasicBlock;
use crate::builder::Builder;
use crate::module::Module;
use crate::string::LLVMString;
use crate::types::Type;
use crate::values::{Value, ValueKind};

pub struct Context(pub(crate) LLVMContextRef);

impl Context {
    /// Create new LLVM context.
    ///
    /// # Examples
    ///
    /// ```
    /// # use llvm::context::Context;
    /// let context = Context::new();
    /// ```
    pub fn new() -> Self {
        unsafe { Context(core::LLVMContextCreate()) }
    }

    pub(crate) unsafe fn from_ref(context: LLVMContextRef) -> Self {
        Context(context)
    }

    /// Create a new, empty [`Module`] in the current context.
    ///
    /// # Examples
    ///
    /// ```
    /// # use llvm::context::Context;
    /// # let context = Context::new();
    /// let module = context.create_module("user");
    /// ```
    pub fn create_module(&self, name: &str) -> Module {
        Module::new_in_context(self, name)
    }

    pub fn parse_ir_module(&self, name: &str, ir: &str) -> Result<Module, LLVMString> {
        Module::from_ir_string(self, name, ir)
    }

    /// Create new IR [`Builder`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use llvm::context::Context;
    /// # let context = Context::new();
    /// let builder = context.create_builder();
    /// ```
    pub fn create_builder(&self) -> Builder {
        Builder::new_in_context(self)
    }

    // /// Create i1 type.
    // ///
    // /// ```
    // /// # use llvm::context::Context;
    // /// # use llvm::types::*;
    // /// # let context = Context::new();
    // /// let i1 = context.i1_type();
    // /// assert_eq!(i1.kind(), TypeKind::LLVMIntegerTypeKind);
    // /// assert_eq!(i1.int_width(), 1);
    // /// ```
    // pub fn i1_type(&self) -> Type {
    //     unsafe {
    //         Type::new(core::LLVMInt1TypeInContext(self.0))
    //     }
    // }

    // /// Create i8 type.
    // ///
    // /// ```
    // /// # use llvm::context::Context;
    // /// # use llvm::types::*;
    // /// # let context = Context::new();
    // /// let i8 = context.i8_type();
    // /// assert_eq!(i8.kind(), TypeKind::LLVMIntegerTypeKind);
    // /// assert_eq!(i8.int_width(), 8);
    // /// ```
    // pub fn i8_type(&self) -> Type {
    //     unsafe {
    //         Type::new(core::LLVMInt8TypeInContext(self.0))
    //     }
    // }

    /// Create integer [Type] with the specified width.
    ///
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::*;
    /// # let context = Context::new();
    /// let i8 = context.int_type(8);
    /// assert_eq!(i8.kind(), TypeKind::LLVMIntegerTypeKind);
    /// assert_eq!(i8.int_width(), 8);
    /// ```
    pub fn int_type(&self, num_bits: u32) -> Type {
        unsafe { Type::new(core::LLVMIntTypeInContext(self.0, num_bits)) }
    }

    pub fn f64_type(&self) -> Type {
        unsafe { Type::new(core::LLVMDoubleTypeInContext(self.0)) }
    }

    /// Create void [Type].
    ///
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::*;
    /// # let context = Context::new();
    /// let void = context.void_type();
    /// assert_eq!(void.kind(), TypeKind::LLVMVoidTypeKind);
    /// ```
    pub fn void_type(&self) -> Type {
        unsafe { Type::new(core::LLVMVoidTypeInContext(self.0)) }
    }

    /// Append a basic block to the end of a function.
    ///
    /// # Examples
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::TypeKind;
    /// # let ctx = Context::new();
    /// let module = ctx.create_module("user");
    /// let f_type = ctx.int_type(1).function_type(&[ctx.int_type(1)], false);
    /// let f = module.add_function("not", f_type);
    /// let bb = ctx.append_basic_block(f, "entry");
    /// ```
    ///
    /// # Safety
    /// Panics if `f` is not a function value.
    pub fn append_basic_block(&self, f: Value, name: &str) -> BasicBlock {
        assert_eq!(f.kind(), ValueKind::LLVMFunctionValueKind);
        let name = CString::new(name).unwrap();
        unsafe { BasicBlock::new(core::LLVMAppendBasicBlock(f.0, name.as_ptr())) }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe {
            core::LLVMContextDispose(self.0);
        }
    }
}
