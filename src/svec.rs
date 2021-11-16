//! SVec is a simple vector — a variable-length array of pointers.
use std::mem::size_of;

use crate::gc;
use crate::symbol::symbol;
use crate::types::{set_typetag, AlphaValue, AnyPtr, DataType, ANY_T, SVEC_EMPTY, SVEC_T};

#[repr(C)]
pub struct SVec {
    /// Number of elements.
    len: usize,
    // follows directly after this struct:
    // elements: [AnyPtr; len]
}

impl SVec {
    pub fn new(elements: &[AnyPtr]) -> *const Self {
        unsafe {
            let this = Self::alloc(elements.len());
            let this = &mut *this;
            this.elements_mut().copy_from_slice(elements);
            this
        }
    }

    /// Appends an element to the back of a collection.
    ///
    /// This is O(n) as it allocates a new SVec and copies elements over.
    pub fn push(this: *const Self, value: AnyPtr) -> *const Self {
        unsafe {
            let new_len = (*this).len + 1;
            let new = Self::alloc(new_len);
            let this_elements = (*this).elements();
            let new_elements = (*new).elements_mut();
            new_elements[0..new_len - 1].copy_from_slice(this_elements);
            new_elements[new_len - 1] = value;
            new
        }
    }

    pub fn set(this: *const Self, index: usize, value: AnyPtr) -> *const Self {
        unsafe {
            let new = Self::clone_mut(this);
            (*new).elements_mut()[index] = value;
            new
        }
    }

    unsafe fn clone_mut(this: *const Self) -> *mut Self {
        let len = (*this).len;
        let new = Self::alloc(len);
        let this_elements = (*this).elements();
        let new_elements = (*new).elements_mut();
        new_elements.copy_from_slice(this_elements);
        new
    }

    unsafe fn alloc(len: usize) -> *mut Self {
        let size = (len + 1) * size_of::<usize>();
        let this = gc::allocate(size) as *mut Self;
        set_typetag(this, SVEC_T.load());
        (*this).len = len;
        this
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn elements(&self) -> &[AnyPtr] {
        let len = self.len;
        let this = self as *const SVec as *const AnyPtr;
        unsafe { std::slice::from_raw_parts(this.add(1), len) }
    }

    pub fn elements_mut(&mut self) -> &mut [AnyPtr] {
        let len = self.len;
        let this = self as *mut SVec as *mut AnyPtr;
        unsafe { std::slice::from_raw_parts_mut(this.add(1), len) }
    }
}

impl std::fmt::Debug for SVec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{:?}", self.elements())
    }
}

impl std::cmp::PartialEq<SVec> for SVec {
    fn eq(&self, other: &SVec) -> bool {
        self.elements().eq(other.elements())
    }
}

impl AlphaValue for SVec {
    fn typetag() -> *const DataType {
        SVEC_T.load()
    }

    fn datatype() -> DataType {
        DataType {
            name: symbol("SVec"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: 0, // dynamically-sized
            n_ptrs: 0,
            methods: SVEC_EMPTY.load(),
        }
    }

    fn as_anyptr(&self) -> AnyPtr {
        self as *const Self as AnyPtr
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::symbol;

    #[test]
    fn test_new() {
        let hello = symbol("hello");
        let world = symbol("world");
        let elements = [hello.as_anyptr(), std::ptr::null_mut(), world.as_anyptr()];
        let v = SVec::new(&elements);
        unsafe {
            assert_eq!((*v).elements(), &elements);
        }
    }
}
