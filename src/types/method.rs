use std::mem::size_of;

use tracing::trace;

use crate::gc_box;
use crate::types::*;

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

impl AlphaType for Method {
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
    fn pointers() -> &'static [usize] {
        static PTRS: [usize; 1] = [
            0 * 8, // signature
        ];
        &PTRS
    }
}

impl AlphaDataType for Method {
    fn size(&self) -> usize {
        size_of::<Self>()
    }
}

impl Method {
    #[tracing::instrument]
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

    #[tracing::instrument]
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

#[tracing::instrument]
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

#[tracing::instrument]
fn param_specifier_is_applicable(ps: AnyPtr, v: AnyPtr) -> bool {
    let result = unsafe {
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
    };
    unsafe {
        trace!(
            "param_specifier_is_applicable({}, {}) = {}",
            *ps,
            *v,
            result
        );
    }
    result
}

/// Returns `true` if `a` is strictly more specific than `b`.
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
            // Use offset 1 — they must not be the same type
            a_cpls[1..].contains(&b)
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
    let mut ty = t;
    while ty != (*ty).supertype {
        ty = (*ty).supertype;
        cpl.push(ty as AnyPtr);
    }
    cpl
}

impl std::fmt::Debug for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        unsafe {
            f.debug_struct("Method")
                .field("signature", &(*self.signature))
                .finish()
        }
    }
}

impl std::fmt::Display for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        unsafe { write!(f, "Method{}", (*self.signature)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_more_specific_any_any() {
        crate::types::init();
        assert!(!param_specifier_is_more_specific(
            ANY_T.load() as *const AlphaValue,
            ANY_T.load() as *const AlphaValue
        ));
    }

    #[test]
    fn test_more_specific_f64_any() {
        crate::types::init();
        assert!(param_specifier_is_more_specific(
            F64_T.load() as *const AlphaValue,
            ANY_T.load() as *const AlphaValue
        ));
    }

    #[test]
    fn test_more_specific_any_f64() {
        crate::types::init();
        assert!(!param_specifier_is_more_specific(
            ANY_T.load().cast(),
            F64_T.load().cast()
        ));
    }

    #[test]
    fn test_cpl_f64() {
        crate::types::init();
        unsafe {
            let cpls = get_cpl(F64_T.load().cast());
            assert_eq!(cpls[0], F64_T.load().cast());
            assert_eq!(cpls[1], ANY_T.load().cast());
        }
    }
}
