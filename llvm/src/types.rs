use llvm_sys::core;
use llvm_sys::prelude::*;

pub use llvm_sys::LLVMTypeKind as TypeKind;

use crate::context::Context;
use crate::values::Value;

#[derive(Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum AddressSpace {
    Generic = 0,
    Global = 1,
    Shared = 3,
    Const = 4,
    Local = 5,
    /// NVVM Internal
    Param = 101,
}

#[derive(Clone, Copy)]
pub struct Type(pub(crate) LLVMTypeRef);

impl Type {
    pub(crate) fn new(type_ref: LLVMTypeRef) -> Self {
        assert!(!type_ref.is_null());
        Type(type_ref)
    }

    /// Return type kind.
    ///
    /// # Examples
    /// ```
    /// # use llvm::types::TypeKind;
    /// # let context = llvm::context::Context::new();
    /// let i8 = context.int_type(8);
    /// assert_eq!(i8.kind(), TypeKind::LLVMIntegerTypeKind);
    /// ```
    pub fn kind(&self) -> TypeKind {
        unsafe { core::LLVMGetTypeKind(self.0) }
    }

    pub fn is_sized(&self) -> bool {
        unsafe { core::LLVMTypeIsSized(self.0) != 0 }
    }

    /// Return width of integer type.
    ///
    /// # Examples
    /// ```
    /// # use llvm::types::TypeKind;
    /// # let context = llvm::context::Context::new();
    /// let i8 = context.int_type(8);
    /// assert_eq!(i8.int_width(), 8);
    /// ```
    ///
    /// # Safety
    /// Panics if type is not integer.
    pub fn int_width(&self) -> u32 {
        assert_eq!(
            self.kind(),
            TypeKind::LLVMIntegerTypeKind,
            "int_width() is called on non-integer"
        );
        unsafe { core::LLVMGetIntTypeWidth(self.0) }
    }

    pub fn const_int(&self, n: u64, sign_extend: bool) -> Value {
        assert_eq!(
            self.kind(),
            TypeKind::LLVMIntegerTypeKind,
            "const_int() is called on non-integer"
        );
        unsafe { Value::new(core::LLVMConstInt(self.0, n, sign_extend as i32)) }
    }

    pub fn const_float(&self, f: f64) -> Value {
        assert!(
            {
                use TypeKind::*;
                let kind = self.kind();
                kind == LLVMHalfTypeKind
                    || kind == LLVMFloatTypeKind
                    || kind == LLVMDoubleTypeKind
                    || kind == LLVMX86_FP80TypeKind
                    || kind == LLVMFP128TypeKind
                    || kind == LLVMPPC_FP128TypeKind
            },
            "const_float() is called on non-float"
        );
        unsafe { Value::new(core::LLVMConstReal(self.0, f)) }
    }

    /// # Examples
    /// ```
    /// # use llvm::types::{TypeKind, AddressSpace};
    /// # let context = llvm::context::Context::new();
    /// let ptr_t = context.int_type(8).pointer_type(AddressSpace::Generic);
    /// assert_eq!(ptr_t.kind(), TypeKind::LLVMPointerTypeKind);
    /// assert_eq!(ptr_t.pointer_address_space(), AddressSpace::Generic);
    /// ```
    pub fn pointer_type(&self, address_space: AddressSpace) -> Type {
        unsafe { Type::new(core::LLVMPointerType(self.0, address_space as u32)) }
    }
    pub fn pointer_address_space(&self) -> AddressSpace {
        assert_eq!(self.kind(), TypeKind::LLVMPointerTypeKind);
        unsafe { std::mem::transmute(core::LLVMGetPointerAddressSpace(self.0)) }
    }
    pub fn element_type(&self) -> Type {
        unsafe { Type::new(core::LLVMGetElementType(self.0)) }
    }

    pub fn const_null(&self) -> Value {
        assert_eq!(self.kind(), TypeKind::LLVMPointerTypeKind);
        unsafe { Value::new(core::LLVMConstNull(self.0)) }
    }

    pub(crate) fn struct_type_in_context(
        context: &Context,
        elements: &[Type],
        packed: bool,
    ) -> Type {
        let mut elements = elements.iter().map(|x| x.0).collect::<Vec<_>>();
        unsafe {
            Type::new(core::LLVMStructTypeInContext(
                context.0,
                elements.as_mut_ptr(),
                elements.len() as u32,
                packed as i32,
            ))
        }
    }

    /// Set the contents of a structure type.
    ///
    /// # Panics
    /// Panics if self is not a structure type.
    pub fn struct_set_body(&self, elements: &[Type], packed: bool) -> Type {
        assert_eq!(self.kind(), TypeKind::LLVMStructTypeKind);
        let mut elements = elements.iter().map(|x| x.0).collect::<Vec<_>>();
        unsafe {
            core::LLVMStructSetBody(
                self.0,
                elements.as_mut_ptr(),
                elements.len() as u32,
                packed as i32,
            );
        }
        *self
    }

    /// Obtain a function type consisting of a specified signature.
    ///
    /// # Examples
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::TypeKind;
    /// # let ctx = Context::new();
    /// let f = ctx.int_type(1).function_type(&[ctx.int_type(1)], false);
    /// assert_eq!(f.kind(), TypeKind::LLVMFunctionTypeKind);
    /// ```
    pub fn function_type(&self, params: &[Type], is_var_arg: bool) -> Type {
        let params = params.iter().map(|x| x.0).collect::<Vec<_>>();
        unsafe {
            Type::new(core::LLVMFunctionType(
                self.0,
                // this is casting *const _ to *mut _. Not sure if that is fine.
                params.as_ptr() as *mut _,
                params.len() as u32,
                is_var_arg as i32,
            ))
        }
    }
    /// Obtain the [Type] this function Type returns.
    ///
    /// # Examples
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::TypeKind;
    /// # let ctx = Context::new();
    /// let f = ctx.int_type(1).function_type(&[], false);
    /// let ret_type = f.return_type();
    /// assert_eq!(ret_type.kind(), TypeKind::LLVMIntegerTypeKind);
    /// assert_eq!(ret_type.int_width(), 1);
    /// ```
    ///
    /// # Safety
    /// Panics if [`kind()`] is not [TypeKind::LLVMFunctionTypeKind].
    pub fn return_type(&self) -> Type {
        assert_eq!(self.kind(), TypeKind::LLVMFunctionTypeKind);
        unsafe { Type::new(core::LLVMGetReturnType(self.0)) }
    }

    pub fn dump_to_stderr(&self) {
        unsafe {
            core::LLVMDumpType(self.0);
        }
    }
}
