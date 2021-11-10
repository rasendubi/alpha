use std::ffi::CString;

use llvm_sys::core;
use llvm_sys::prelude::*;

use crate::basic_block::BasicBlock;
use crate::context::Context;
use crate::types::Type;
use crate::values::Value;

pub struct Builder(pub(crate) LLVMBuilderRef);

impl Builder {
    fn new(builder: LLVMBuilderRef) -> Self {
        Builder(builder)
    }

    pub fn new_in_context(context: &Context) -> Self {
        unsafe { Builder::new(core::LLVMCreateBuilderInContext(context.0)) }
    }

    /// # Examples
    /// ```
    /// # use llvm::context::Context;
    /// # use llvm::types::TypeKind;
    /// # let ctx = Context::new();
    /// let module = ctx.create_module("user");
    /// let f_type = ctx.int_type(1).function_type(&[ctx.int_type(1)], false);
    /// let f = module.add_function("not", f_type);
    /// let bb = ctx.append_basic_block(f, "entry");
    /// let builder = ctx.create_builder();
    /// builder.position_at_end(bb);
    /// ```
    pub fn position_at_end(&self, bb: BasicBlock) {
        unsafe { core::LLVMPositionBuilderAtEnd(self.0, bb.0) }
    }

    pub fn build_ret_void(&self) -> Value {
        unsafe { Value::new(core::LLVMBuildRetVoid(self.0)) }
    }

    pub fn build_ret(&self, value: Value) -> Value {
        unsafe { Value::new(core::LLVMBuildRet(self.0, value.0)) }
    }

    pub fn build_alloca(&self, typ: Type, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        unsafe { Value::new(core::LLVMBuildAlloca(self.0, typ.0, name.as_ptr())) }
    }

    pub fn build_array_alloca(&self, typ: Type, num_elements: Value, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        unsafe {
            Value::new(core::LLVMBuildArrayAlloca(
                self.0,
                typ.0,
                num_elements.0,
                name.as_ptr(),
            ))
        }
    }

    pub fn build_load(&self, pointer: Value, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        unsafe { Value::new(core::LLVMBuildLoad(self.0, pointer.0, name.as_ptr())) }
    }

    pub fn build_store(&self, ptr: Value, value: Value) -> Value {
        unsafe { Value::new(core::LLVMBuildStore(self.0, value.0, ptr.0)) }
    }

    pub fn build_call(&self, f: Value, args: &[Value], name: &str) -> Value {
        let name = CString::new(name).unwrap();
        let args = args.iter().map(|x| x.0).collect::<Vec<_>>();
        unsafe {
            Value::new(core::LLVMBuildCall(
                self.0,
                f.0,
                args.as_ptr() as *mut _,
                args.len() as u32,
                name.as_ptr(),
            ))
        }
    }

    pub fn build_pointer_cast(&self, value: Value, dest_type: Type, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        unsafe {
            Value::new(core::LLVMBuildPointerCast(
                self.0,
                value.0,
                dest_type.0,
                name.as_ptr(),
            ))
        }
    }

    pub fn build_gep(&self, ptr: Value, indices: &[Value], name: &str) -> Value {
        let name = CString::new(name).unwrap();
        let indices = indices.iter().map(|x| x.0).collect::<Vec<_>>();
        unsafe {
            Value::new(core::LLVMBuildGEP(
                self.0,
                ptr.0,
                indices.as_ptr() as *mut _,
                indices.len() as u32,
                name.as_ptr(),
            ))
        }
    }

    pub fn build_struct_gep(&self, ptr: Value, index: u32, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        unsafe {
            Value::new(core::LLVMBuildStructGEP(
                self.0,
                ptr.0,
                index,
                name.as_ptr(),
            ))
        }
    }
}

impl Drop for Builder {
    fn drop(&mut self) {
        unsafe {
            core::LLVMDisposeBuilder(self.0);
        }
    }
}
