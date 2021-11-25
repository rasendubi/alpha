pub use crate::types::*;

use tracing::trace;

use crate::gc_box;

/// Type{T} is a type whose only value is a type object T.
///
/// Ideally, it should be a polymorphic type, but Alpha does not yet support polymorphic types.
#[repr(C)]
pub struct Type {
    pub t: *const DataType,
}
impl Type {
    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    #[tracing::instrument("Type::new")]
    pub unsafe fn new(t: *const DataType) -> *const Type {
        assert_ne!(t, std::ptr::null());
        debug_assert_eq!(get_typetag(t), DATATYPE_T.load());

        gc_box!(t);
        let this = gc::allocate(std::mem::size_of::<Self>()) as *mut Self;
        set_typetag(this, Self::typetag());
        *this = Type { t: t.load() };
        trace!("= {:?}", this);
        this
    }
}

impl AlphaType for Type {
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
    fn pointers() -> &'static [usize] {
        static PTRS: [usize; 1] = [
            0, // t
        ];
        &PTRS
    }
}

impl AlphaDataType for Type {
    fn size(&self) -> usize {
        std::mem::size_of::<Type>()
    }
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        unsafe { f.debug_struct("Type").field("t", &*self.t).finish() }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        unsafe { write!(f, "Type{{{}}}", &*self.t) }
    }
}
