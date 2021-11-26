use crate::types::*;

use tracing::{error, trace};

#[tracing::instrument]
pub unsafe extern "C" fn dispatch(n_args: i64, args: *const AnyPtr) -> AnyPtr {
    #[allow(unused_must_use)] // ignore write!() errors
    fn format_signature(args_slice: &[*const AlphaValue]) -> String {
        use std::fmt::Write;
        let mut sig = String::new();

        write!(sig, "[");
        let mut first = true;
        for arg in args_slice.iter() {
            if !first {
                write!(sig, ", ");
            } else {
                first = false;
            }
            write!(sig, "{}", unsafe { &*type_of(*arg) });
        }
        write!(sig, "]");

        sig
    }

    let args_slice = std::slice::from_raw_parts(args, n_args as usize);
    trace!("dispatch: {:?}", args_slice);

    let f = args_slice[0];

    let typetag = type_of(f);
    let methods = &(*(*typetag).methods);

    let mut selected_method: Option<&Method> = None;
    for method in methods.elements() {
        let method = &*(*method as *const Method);
        if !method.is_applicable(args_slice) {
            continue;
        }

        // this method is applicable

        selected_method = Some(match selected_method {
            None => method,
            Some(current) => {
                // check if it is strictly more specific
                if current.is_subtype_of(method) {
                    // selected method remains selected, skip this one
                    current
                } else if method.is_subtype_of(current) {
                    // the new method is more specific
                    method
                } else {
                    // Both methods are applicable but neither is more specific — ambiguity.
                    error!(
                        "ambiguity finding matching method for signature: {}",
                        &format_signature(args_slice)
                    );
                    error!("available methods: {}", methods);
                    panic!("ambiguity! between {} and {}", current, method);
                }
            }
        });
    }

    match selected_method {
        Some(method) => {
            trace!("calling found method: {:?}", *method);
            (method.instance)(n_args, args)
        }
        None => {
            error!(
                "unable to find matching method for: {}",
                &format_signature(args_slice)
            );
            error!("available methods: {}", methods);
            panic!("unable to find matching method");
        }
    }
}
