use crate::types::*;

pub struct Any;

impl AlphaType for Any {
    fn typetag() -> *const DataType {
        ANY_T.load()
    }
    fn datatype() -> DataType {
        DataType {
            name: symbol("Any"),
            supertype: ANY_T.load(),
            is_abstract: true,
            size: usize::MAX, // Any is abstract and should never be allocated
            methods: SVEC_EMPTY.load(),
            n_ptrs: 0,
            pointers: [],
        }
    }
}
