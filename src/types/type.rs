pub use crate::types::*;

use crate::gc_box;

/// Type{T} is a type whose only value is a type object T.
///
/// Ideally, it should be a polymorphic type, but Alpha does not yet support polymorphic types.
#[derive(Debug)]
#[repr(C)]
pub struct Type {
    pub t: *const DataType,
}
impl Type {
    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    pub unsafe fn new(t: *const DataType) -> *const Type {
        gc_box!(t);
        let this = gc::allocate(std::mem::size_of::<Self>()) as *mut Self;
        set_typetag(this, Self::typetag());
        *this = Type { t: t.load() };
        this
    }
}
impl AlphaValue for Type {
    fn typetag() -> *const DataType {
        TYPE_T.load()
    }
    fn datatype() -> DataType {
        DataType {
            name: symbol("Type"),
            supertype: ANY_T.load(),
            is_abstract: false,
            methods: SVEC_EMPTY.load(),
            size: std::mem::size_of::<Type>(),
            n_ptrs: 1,
            pointers: [],
        }
    }
    fn size(_ptr: *const Self) -> usize {
        std::mem::size_of::<Type>()
    }
    fn pointers() -> &'static [usize] {
        static PTRS: [usize; 1] = [
            0, // t
        ];
        &PTRS
    }
}
