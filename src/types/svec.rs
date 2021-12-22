//! SVec is a simple vector — a variable-length array of pointers.
use std::mem::size_of;

use tracing::trace;

use crate::gc::{self, Gc};
use crate::gc_frame;

use crate::types::*;

#[repr(C)]
pub struct SVec {
    /// Number of elements.
    len: usize,
    /// Variable-sized
    elements: [AnyPtr; 0],
}

impl SVec {
    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    #[tracing::instrument("SVec::new")]
    pub unsafe fn new(elements: &[AnyPtr]) -> *const Self {
        trace!("SVec::new({:?})", elements);
        for (i, e) in elements.iter().enumerate() {
            trace!("{} = @{:p}", i, *e);
            trace!("{} = ty {:?}", i, &*type_of(*e));
            trace!("{} = {:?}", i, &**e);
        }
        gc::with_gc_box_slice(elements, |elements| {
            let this = Self::alloc(elements.len());
            let this = &mut *this;
            let new_elements = elements.iter().map(|x| x.ptr()).collect::<Vec<_>>();
            this.elements_mut().copy_from_slice(&new_elements);
            trace!("allocated = {:?}", &*this);
            this
        })
    }

    /// Appends an element to the back of a collection.
    ///
    /// This is O(n) as it allocates a new SVec and copies elements over.
    ///
    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    #[tracing::instrument("SVec::push")]
    pub unsafe fn push(this: *const Self, value: AnyPtr) -> *const Self {
        trace!(
            "SVec::push({:p}, {:p} ty={:p})",
            this,
            value,
            type_of(value)
        );
        debug_assert!(!this.is_null());
        debug_assert!(!value.is_null());

        let this = Gc::new(this);
        let value = Gc::new(value);
        gc_frame![this, value];

        let new_len = (*this.load()).len + 1;
        let new = Self::alloc(new_len);
        let this_elements = (*this.load()).elements();
        let new_elements = (*new).elements_mut();
        new_elements[0..new_len - 1].copy_from_slice(this_elements);
        new_elements[new_len - 1] = value.load();
        new
    }

    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    #[tracing::instrument("SVec::set")]
    pub unsafe fn set(this: *const Self, index: usize, value: AnyPtr) -> *const Self {
        let this = Gc::new(this);
        let value = Gc::new(value);
        gc_frame![this, value];

        let new = Self::clone_mut(this.load());
        (*new).elements_mut()[index] = value.load();
        new
    }

    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    unsafe fn clone_mut(this: *const Self) -> *mut Self {
        let this = Gc::new(this);
        gc_frame![this];

        let len = (*this.load()).len;
        let new = Self::alloc(len);
        let this_elements = (*this.load()).elements();
        let new_elements = (*new).elements_mut();
        new_elements.copy_from_slice(this_elements);
        new
    }

    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    unsafe fn alloc(len: usize) -> *mut Self {
        let size = (len + 1) * size_of::<usize>();
        let this = gc::allocate(size) as *mut Self;
        set_type(this, SVEC_T.load());
        (*this).len = len;
        this
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn elements(&self) -> &[AnyPtr] {
        unsafe { std::slice::from_raw_parts(self.elements.as_ptr(), self.len) }
    }

    pub fn elements_mut(&mut self) -> &mut [AnyPtr] {
        unsafe { std::slice::from_raw_parts_mut(self.elements.as_mut_ptr(), self.len) }
    }
}

impl std::fmt::Debug for SVec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "SVec<{}> ", self.len)?;
        f.debug_list().entries(self.elements()).finish()?;
        write!(f, "=")?;
        f.debug_list()
            .entries(self.elements().iter().map(|x| unsafe { &**x }))
            .finish()
    }
}

impl std::fmt::Display for SVec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "[")?;
        let mut first = true;
        for i in self.elements() {
            if !first {
                write!(f, ", ")?;
            } else {
                first = false;
            }
            write!(f, "{}", unsafe { &**i })?;
        }
        write!(f, "]")
    }
}

impl std::cmp::PartialEq<SVec> for SVec {
    fn eq(&self, other: &SVec) -> bool {
        self.elements().eq(other.elements())
    }
}

impl AlphaType for SVec {
    fn typetag() -> *const DataType {
        SVEC_T.load()
    }
    fn datatype() -> DataType {
        DataType {
            name: symbol("SVec"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: usize::MAX, // dynamically-sized
            n_ptrs: 0,
            methods: SVEC_EMPTY.load(),
            pointers: [], // not true. special-cased in GC to call trace_pointers()
        }
    }
}
impl AlphaDataType for SVec {
    fn size(&self) -> usize {
        size_of::<Self>() + self.len * size_of::<AnyPtr>()
    }

    fn trace_pointers(&mut self, trace_ptr: unsafe fn(*mut AnyPtrMut) -> bool) {
        unsafe {
            for element in self.elements_mut() {
                // TODO: remove transmute
                trace_ptr(std::mem::transmute(element as *mut AnyPtr));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    #[test]
    #[serial]
    fn test_new() {
        crate::init();

        let hello = symbol("hello");
        let world = symbol("world");
        let elements = [hello.node.cast(), world.node.cast()];
        let v = unsafe { SVec::new(&elements) };
        unsafe {
            assert_eq!((*v).elements(), &elements);
        }
    }
}
