//! Runtime type information.
mod alpha_value;
mod any;
mod datatype;
mod init;
mod method;
mod primitive;
mod string;
mod svec;
mod symbol;
mod r#type;
mod void;

pub use self::alpha_value::*;
pub use self::any::*;
pub use self::datatype::*;
pub use self::init::*;
pub use self::method::*;
pub use self::primitive::*;
pub use self::r#type::*;
pub use self::string::*;
pub use self::svec::*;
pub use self::symbol::*;
pub use self::void::*;

use crate::gc;

pub type AnyPtr = *const AlphaValue;
pub type AnyPtrMut = *mut AlphaValue;
pub type GenericFn = unsafe extern "C" fn(i64, *const AnyPtr) -> AnyPtr;

/// AlphaType should be implemented for all Rust types that are exposed to Alpha.
///
/// The type can be either abstract or a data type. Data types should additionally implement
/// [`AlphaDataType`].
pub trait AlphaType {
    fn typetag() -> *const DataType;

    fn datatype() -> DataType;

    fn pointers() -> &'static [usize] {
        static PTRS: [usize; 0] = [];
        &PTRS
    }
}

/// AlphaDataType are types that can occur in GC-managed memory.
pub trait AlphaDataType: std::fmt::Debug {
    fn size(&self) -> usize;

    fn trace_pointers(&mut self, trace_ptr: unsafe fn(*mut AnyPtrMut) -> bool) {
        unsafe {
            let ptr = self as *mut Self;
            let ty = get_typetag(ptr); // self datatype
            let ptr_offsets = (*ty).pointers();
            for offset in ptr_offsets {
                let field = (ptr as *mut u8).add(*offset) as *mut AnyPtrMut;
                trace_ptr(field);
            }
        }
    }
}

pub unsafe fn set_typetag<T>(ptr: *mut T, typetag: *const DataType) {
    *typetag_ptr(ptr) = typetag;
    debug_assert_ne!(
        (typetag as usize),
        0x1,
        "set_typetag(): trying to move out {:p} -> 0x0",
        ptr
    );
    debug_assert!(
        // early init yet
        DATATYPE_T.load().is_null() ||
            // moved out
            (typetag as usize) & 0x1 == 0x1 ||
            (get_typetag(typetag) as usize) & 0x1 == 0x1 ||
            get_typetag(typetag) == DATATYPE_T.load(),
        "set_typetag() is used to set invalid tag: {:p}",
        typetag
    )
}

pub unsafe fn get_typetag<T: ?Sized>(ptr: *const T) -> *const DataType {
    let typetag = *typetag_ptr(ptr);
    if !((typetag as usize) & 0x1 == 0x1
        || (*typetag_ptr(typetag) as usize) & 0x1 == 0x1
        || *typetag_ptr(typetag) == DATATYPE_T.load())
    {
        let ty = typetag;
        let ty_ty = *typetag_ptr(ty);
        tracing::error!("get_typetag({:p}), ty={:p}, ty_ty={:p}", ptr, ty, ty_ty);
        // gc::debug_ptr(ptr.cast());
        // gc::debug_ptr(ty.cast());
        // gc::debug_ptr(ty_ty.cast());
        panic!(
            "typetag is neither moved out nor a type: typetag={:p}",
            typetag
        )
    }
    typetag
}

pub unsafe fn typetag_ptr<T: ?Sized>(ptr: *const T) -> *mut *const DataType {
    debug_assert_eq!(
        (ptr as *const () as usize) % 8,
        0,
        "typetag_ptr() is called on unaligned pointer: {:p}",
        ptr
    );
    (ptr as *mut *const DataType).sub(1)
}
