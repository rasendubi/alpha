use crate::gc;
use crate::types::*;

use std::mem::size_of;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(C)]
pub struct AlphaI64 {
    pub value: i64,
}

impl AlphaI64 {
    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    pub unsafe fn allocate(value: i64) -> *const Self {
        let result: *mut Self = gc::allocate(size_of::<Self>()).cast();
        set_typetag(result, Self::typetag());
        (*result).value = value;
        result
    }
}

impl AlphaValue for AlphaI64 {
    fn typetag() -> *const DataType {
        I64_T.load()
    }

    fn datatype() -> DataType {
        DataType {
            name: symbol("i64"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: size_of::<Self>(),
            methods: SVEC_EMPTY.load(),
            n_ptrs: <Self as AlphaValue>::pointers().len(),
            pointers: [],
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
#[repr(C)]
pub struct AlphaF64 {
    pub value: f64,
}

impl AlphaF64 {
    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    pub unsafe fn allocate(value: f64) -> *const Self {
        let result: *mut Self = gc::allocate(size_of::<Self>()).cast();
        set_typetag(result, Self::typetag());
        (*result).value = value;
        result
    }
}

impl AlphaValue for AlphaF64 {
    fn typetag() -> *const DataType {
        F64_T.load()
    }

    fn datatype() -> DataType {
        DataType {
            name: symbol("f64"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: size_of::<Self>(),
            methods: SVEC_EMPTY.load(),
            n_ptrs: <Self as AlphaValue>::pointers().len(),
            pointers: [],
        }
    }
}
