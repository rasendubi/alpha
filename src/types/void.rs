use crate::types::*;

/// `Void` is the unit type in the Alpha type hierarchy. It has only one value — `void`.
#[derive(Debug)]
#[repr(C)]
pub struct Void {}

impl AlphaValue for Void {
    fn typetag() -> *const DataType {
        VOID_T.load()
    }
    fn datatype() -> DataType {
        DataType {
            name: symbol("Void"),
            supertype: ANY_T.load(),
            is_abstract: false,
            methods: SVEC_EMPTY.load(),
            size: 0,
            n_ptrs: 0,
            pointers: [],
        }
    }
    fn size(_ptr: *const Self) -> usize {
        0
    }
}
