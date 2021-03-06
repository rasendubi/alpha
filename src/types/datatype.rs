use std::mem::size_of;

use tracing::trace;

use crate::gc_box;
use crate::types::*;

#[derive(Debug)]
#[repr(C)]
pub struct DataType {
    pub size: usize,
    pub name: Symbol,
    pub supertype: *const DataType,
    pub is_abstract: bool,
    /// SVec<Method>
    pub methods: *const SVec,
    pub n_ptrs: usize,
    /// Byte offsets into value to fields that are gc pointers.
    ///
    /// Variable-sized: [usize; n_ptrs]. Use [DataType::pointers()] to access it.
    pub pointers: [usize; 0],
}

impl DataType {
    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    // DEAD CODE: this used to be useful before HIR refactoring. Unused since 2021-12-22.
    #[allow(dead_code)]
    #[tracing::instrument("DataType::new")]
    pub unsafe fn new(
        name: Symbol,
        supertype: *const DataType,
        size: usize,
        ptrs: &[usize],
    ) -> *const DataType {
        trace!(
            "DataType::new(name={:?}, supertype={:?}, size={:?}, ptrs={:?})",
            name,
            &*supertype,
            size,
            ptrs
        );

        gc_box!(supertype);
        let this = Self::allocate(ptrs.len());
        *this = DataType {
            size,
            name,
            supertype: supertype.load(),
            is_abstract: false,
            methods: SVEC_EMPTY.load(),
            n_ptrs: ptrs.len(),
            pointers: [],
        };
        (*this).pointers_mut().copy_from_slice(ptrs);
        this
    }

    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    // DEAD CODE: this used to be useful before HIR refactoring. Unused since 2021-12-22.
    #[allow(dead_code)]
    #[tracing::instrument("DataType::new_abstract")]
    pub unsafe fn new_abstract(name: Symbol, supertype: *const DataType) -> *const DataType {
        gc_box!(supertype);
        let this = Self::allocate(0);
        *this = DataType {
            size: usize::MAX, // sentinel value because abstract types never appear as typetags
            name,
            supertype: supertype.load(),
            is_abstract: true,
            methods: SVEC_EMPTY.load(),
            n_ptrs: 0,
            pointers: [],
        };
        this
    }

    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    ///
    /// This function returns uninitialized DataType.
    unsafe fn allocate(n_ptrs: usize) -> *mut DataType {
        let this = gc::allocate(size_of::<DataType>() + n_ptrs * size_of::<usize>());
        set_type(this, DATATYPE_T.load());
        this.cast()
    }

    pub(super) unsafe fn allocate_perm(n_ptrs: usize) -> *mut DataType {
        let this = gc::allocate_perm(size_of::<DataType>() + n_ptrs * size_of::<usize>());
        set_type(this, DATATYPE_T.load());
        this.cast()
    }

    pub fn pointers(&self) -> &[usize] {
        unsafe { std::slice::from_raw_parts(self.pointers.as_ptr(), self.n_ptrs) }
    }

    pub fn pointers_mut(&mut self) -> &mut [usize] {
        unsafe { std::slice::from_raw_parts_mut(self.pointers.as_mut_ptr(), self.n_ptrs) }
    }

    pub unsafe fn reset_methods(this: *mut Self) {
        (*this).methods = SVEC_EMPTY.load();
    }

    pub unsafe fn add_method(this: *mut Self, method: *const Method) {
        debug_assert!(!this.is_null());
        debug_assert!(!method.is_null());
        debug_assert_eq!(type_of(this), DATATYPE_T.load());
        debug_assert_eq!(type_of(method), METHOD_T.load());

        trace!(
            "add_method({:p}:{:?} {:p}:{:?})",
            this,
            *this,
            method,
            *method
        );
        gc_box!(this);

        let override_pos = (&*(*this.load()).methods)
            .elements()
            .iter()
            .position(|m: &AnyPtr| {
                let m = m.cast::<Method>();

                let a_signature = (*m).signature;
                let b_signature = (*method).signature;
                trace!("add_method(): comparing {:?} and {:?}", *m, *method);

                method::signature_equal(a_signature, b_signature)
            });

        let new_methods = match override_pos {
            Some(pos) => {
                eprintln!("warning: re-defining method");
                SVec::set((*this.load()).methods, pos, method as AnyPtr)
            }
            None => SVec::push((*this.load()).methods, method as AnyPtr),
        };

        trace!(
            "add_method(): new_methods: {:p}:{:?}",
            new_methods,
            *new_methods
        );

        (*this.load_mut()).methods = new_methods;
    }
}

impl AlphaType for DataType {
    fn typetag() -> *const DataType {
        DATATYPE_T.load()
    }

    fn datatype() -> DataType {
        DataType {
            name: symbol("DataType"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: size_of::<DataType>() + 3 * size_of::<usize>(),
            methods: SVEC_EMPTY.load(),
            n_ptrs: <Self as AlphaType>::pointers().len(),
            pointers: [],
        }
    }

    fn pointers() -> &'static [usize] {
        #[allow(clippy::identity_op)]
        static PTRS: [usize; 3] = [
            // very much unsafe and relies on me knowing how repr(C) works
            1 * 8, // name
            2 * 8, // supertype
            4 * 8, // methods
        ];
        &PTRS
    }
}

impl AlphaDataType for DataType {
    fn size(&self) -> usize {
        // note that this should return the size of the DataType itself.
        std::mem::size_of::<Self>() + self.n_ptrs * size_of::<usize>()
    }
}

impl std::fmt::Display for DataType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        assert_ne!(self as *const Self, std::ptr::null());
        write!(f, "{}", self.name.as_str())
    }
}
