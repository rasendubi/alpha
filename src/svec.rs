//! SVec is a simple vector — a variable-length array of pointers.
use std::mem::size_of;

use crate::gc;
use crate::types::{set_typetag, AnyPtr, SVEC_T};

#[repr(C)]
pub struct SVec {
    /// Number of elements.
    len: usize,
    // follows directly after this struct:
    // elements: [AnyPtr; len]
}

impl SVec {
    pub fn new(elements: &[AnyPtr]) -> *const Self {
        let this = Self::alloc(elements.len());
        unsafe {
            let this = &mut *this;
            this.elements_mut().copy_from_slice(elements);
        }
        this
    }

    fn alloc(len: usize) -> *mut Self {
        let size = (len + 1) * size_of::<usize>();
        unsafe {
            let this = gc::allocate(size) as *mut Self;
            set_typetag(this, SVEC_T.load());
            (*this).len = len;
            this
        }
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
