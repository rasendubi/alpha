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

    pub fn float_type(&self, num_bits: u32) -> Type {
        match num_bits {
            32 => self.f32_type(),
            64 => self.f64_type(),
            _ => panic!(
                "Context.float_type called with unsupported size {}",
                num_bits
            ),
        }
    }

    pub fn f32_type(&self) -> Type {
        unsafe { Type::new(core::LLVMFloatTypeInContext(self.0)) }
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

    /// Get an anonymous structure type.
    ///
    /// # Examples
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::*;
    /// # let context = Context::new();
    /// let st = context.struct_type(&[context.int_type(64)], false);
    /// assert_eq!(st.kind(), TypeKind::LLVMStructTypeKind);
    /// ```
    pub fn struct_type(&self, elements: &[Type], packed: bool) -> Type {
        Type::struct_type_in_context(self, elements, packed)
    }

    /// Create an empty structure [`Type`] in a context having a specified name.
    ///
    /// Structure body can be set with [`Type.struct_set_body()`].
    ///
    /// # Examples
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::*;
    /// # let context = Context::new();
    /// let st = context.create_named_struct_type("my_struct");
    /// st.struct_set_body(&[context.int_type(64)], false);
    /// assert_eq!(st.kind(), TypeKind::LLVMStructTypeKind);
    /// ```
    pub fn create_named_struct_type(&self, name: &str) -> Type {
        let name = CString::new(name).unwrap();
        unsafe { Type::new(core::LLVMStructCreateNamed(self.0, name.as_ptr())) }
    }

    pub fn get_named_struct(&self, name: &str) -> Option<Type> {
        let name = CString::new(name).unwrap();
        unsafe {
            let s = core::LLVMGetTypeByName2(self.0, name.as_ptr());
            if s.is_null() {
                None
            } else {
                Some(Type::new(s))
            }
        }
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
