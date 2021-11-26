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

pub use crate::gc::{set_type, type_of};

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
pub trait AlphaDataType: std::fmt::Debug + std::fmt::Display {
    fn size(&self) -> usize;

    fn trace_pointers(&mut self, trace_ptr: unsafe fn(*mut AnyPtrMut) -> bool) {
        unsafe {
            let ptr = self as *mut Self;
            let ty = type_of(ptr); // self datatype
            let ptr_offsets = (*ty).pointers();
            for offset in ptr_offsets {
                let field = (ptr as *mut u8).add(*offset) as *mut AnyPtrMut;
                trace_ptr(field);
            }
        }
    }
}
