use std::mem::size_of;

use log::trace;

use crate::gc_box;
use crate::types::*;

#[derive(Debug)]
#[repr(C)]
pub struct Method {
    /// Values can be either types (type=DataType) or a Type{T} (type=Type).
    ///
    /// If parameter specifier is a type, any subtype is accepted.
    ///
    /// If parameter specifier is a Type{T}, only type value T is accepted.
    pub signature: *const SVec,
    // compiled instance of the method
    pub instance: GenericFn,
}

impl Method {
    /// # Safety
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    #[tracing::instrument("Method::new")]
    pub unsafe fn new(signature: *const SVec, instance: GenericFn) -> *const Self {
        gc_box!(signature);
        let this = gc::allocate(size_of::<Method>()) as *mut Self;
        set_typetag(this, METHOD_T.load());
        *this = Method {
            signature: signature.load(),
            instance,
        };
        this
    }
}
impl AlphaValue for Method {
    fn typetag() -> *const DataType {
        METHOD_T.load()
    }
    fn datatype() -> DataType {
        DataType {
            name: symbol("Method"),
            supertype: ANY_T.load(),
            is_abstract: false,
            methods: SVEC_EMPTY.load(),
            size: size_of::<Self>(),
            n_ptrs: 1,
            pointers: [],
        }
    }

    fn size(_ptr: *const Self) -> usize {
        size_of::<Self>()
    }

    fn pointers() -> &'static [usize] {
        static PTRS: [usize; 1] = [
            0 * 8, // signature
        ];
        &PTRS
    }
}

impl Method {
    pub fn is_applicable(&self, args: &[AnyPtr]) -> bool {
        unsafe {
            if (*self.signature).len() != args.len() {
                return false;
            }

            for (v, spec) in args.iter().zip((*self.signature).elements()) {
                if !param_specifier_is_applicable(*spec, *v) {
                    return false;
                }
            }

            true
        }
    }

    pub fn is_subtype_of(&self, other: &Self) -> bool {
        unsafe {
            // find an element that is strictly more specific
            let mut subtype_index = None;
            for (i, (a, b)) in (*self.signature)
                .elements()
                .iter()
                .zip((*other.signature).elements())
                .enumerate()
            {
                if param_specifier_is_more_specific(*a, *b) {
                    subtype_index = Some(i);
                    break;
                }
            }

            let subtype_index = match subtype_index {
                Some(i) => i,
                None => return false,
            };

            // all other elements should have more or equal specificity
            for (i, (a, b)) in (*self.signature)
                .elements()
                .iter()
                .zip((*other.signature).elements())
                .enumerate()
            {
                if i != subtype_index {
                    if param_specifier_is_more_specific(*b, *a) {
                        return false;
                    }
                }
            }

            true
        }
    }
}

pub(super) fn signature_equal(a_signature: *const SVec, b_signature: *const SVec) -> bool {
    debug_assert!(!a_signature.is_null());
    debug_assert!(!b_signature.is_null());
    unsafe {
        trace!("signature_equal({:?}, {:?})", *a_signature, *b_signature);
        (*a_signature).len() == (*b_signature).len()
            && (*a_signature)
                .elements()
                .iter()
                .zip((*b_signature).elements())
                .all(|(a, b)| param_specifier_equal(*a, *b))
    }
}

fn param_specifier_equal(a: AnyPtr, b: AnyPtr) -> bool {
    unsafe {
        let a_kind = get_typetag(a);
        let b_kind = get_typetag(b);
        if a_kind != b_kind {
            false
        } else if a_kind == TYPE_T.load() {
            (*(a as *const Type)).t == (*(b as *const Type)).t
        } else if a_kind == DATATYPE_T.load() {
            a == b
        } else {
            panic!("wrong type for parameter specifiers: {:?}", a_kind);
        }
    }
}

fn param_specifier_is_applicable(ps: AnyPtr, v: AnyPtr) -> bool {
    unsafe {
        let ps_kind = get_typetag(ps);
        if ps_kind == TYPE_T.load() {
            let t = ps as *const Type;
            v == (*t).t as AnyPtr
        } else if ps_kind == DATATYPE_T.load() {
            let cpls = get_cpl(get_typetag(v));
            cpls.contains(&ps)
        } else {
            panic!("wrong type for parameter specifier: {:?}", ps_kind);
        }
    }
}

/// Returns `true` if `a` is more specific than `b`.
fn param_specifier_is_more_specific(a: AnyPtr, b: AnyPtr) -> bool {
    unsafe {
        let a_kind = get_typetag(a);
        let b_kind = get_typetag(b);
        if a_kind == TYPE_T.load() {
            // might be not true, but good enough for the Method::is_subtype_of().
            true
        } else if b_kind == TYPE_T.load() {
            false
        } else if a_kind == DATATYPE_T.load() && b_kind == DATATYPE_T.load() {
            let a_cpls = get_cpl(a as *const DataType);
            a_cpls.contains(&b)
        } else {
            panic!(
                "wrong type for parameter specifiers: {:?} {:?}",
                a_kind, b_kind
            );
        }
    }
}

// CPL = class precedence list
unsafe fn get_cpl(t: *const DataType) -> Vec<AnyPtr> {
    let mut cpl = Vec::new();
    cpl.push(t as AnyPtr);
    let mut supertype = (*t).supertype;
    cpl.push(supertype as AnyPtr);
    while supertype != (*supertype).supertype {
        supertype = (*supertype).supertype;
        cpl.push(supertype as AnyPtr);
    }
    cpl
}