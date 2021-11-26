use crate::types::*;

/// AlphaValue is a typedef for values stored on GC-heap. It must be used via pointers or
/// `Gc<AlphaValue>`.
///
/// The type provides some helpers to handle the value based on its typetag.
pub struct AlphaValue;

impl AlphaValue {
    fn as_builtin_datatype(&self) -> Option<&dyn AlphaDataType> {
        unsafe {
            let ty = type_of(self);
            let data: &dyn AlphaDataType = if ty == DataType::typetag() {
                &*(self as *const Self as *const DataType)
            } else if ty == Method::typetag() {
                &*(self as *const Self as *const Method)
            } else if ty == Type::typetag() {
                &*(self as *const Self as *const Type)
            } else if ty == AlphaString::typetag() {
                &*(self as *const Self as *const AlphaString)
            } else if ty == SVec::typetag() {
                &*(self as *const Self as *const SVec)
            } else if ty == SymbolNode::typetag() {
                &*(self as *const Self as *const SymbolNode)
            } else if ty == Void::typetag() {
                &*(self as *const Self as *const Void)
            } else {
                return None;
            };
            Some(data)
        }
    }

    fn as_builtin_datatype_mut(&mut self) -> Option<&mut dyn AlphaDataType> {
        unsafe {
            let ty = type_of(self);
            let data: &mut dyn AlphaDataType = if ty == DataType::typetag() {
                &mut *(self as *mut Self as *mut DataType)
            } else if ty == Method::typetag() {
                &mut *(self as *mut Self as *mut Method)
            } else if ty == Type::typetag() {
                &mut *(self as *mut Self as *mut Type)
            } else if ty == AlphaString::typetag() {
                &mut *(self as *mut Self as *mut AlphaString)
            } else if ty == SVec::typetag() {
                &mut *(self as *mut Self as *mut SVec)
            } else if ty == SymbolNode::typetag() {
                &mut *(self as *mut Self as *mut SymbolNode)
            } else if ty == Void::typetag() {
                &mut *(self as *mut Self as *mut Void)
            } else {
                return None;
            };
            Some(data)
        }
    }
}

impl AlphaDataType for AlphaValue {
    fn size(&self) -> usize {
        self.as_builtin_datatype().map_or_else(
            || unsafe {
                // generic datatype
                let ty = type_of(self);
                (*ty).size
            },
            |datatype| datatype.size(),
        )
    }

    fn trace_pointers(&mut self, trace_ptr: unsafe fn(*mut AnyPtrMut) -> bool) {
        if let Some(datatype) = self.as_builtin_datatype_mut() {
            datatype.trace_pointers(trace_ptr)
        } else {
            unsafe {
                // trace as generic datatype
                let ty = type_of(self); // self datatype
                let ptr = self as *mut Self;
                let ptr_offsets = (*ty).pointers();
                for offset in ptr_offsets {
                    let field = (ptr as *mut u8).add(*offset) as *mut AnyPtrMut;
                    trace_ptr(field);
                }
            }
        }
    }
}

impl std::fmt::Debug for AlphaValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        use pretty_hex::{HexConfig, PrettyHex};

        if let Some(datatype) = self.as_builtin_datatype() {
            std::fmt::Debug::fmt(&datatype, f)
        } else {
            unsafe {
                let ty = type_of(self);
                let ptr = self as *const Self as *const u8;
                f.debug_struct("AlphaValue")
                    .field("type", &(*ty))
                    .field(
                        "data",
                        &std::slice::from_raw_parts(ptr, (*ty).size).hex_conf(HexConfig {
                            title: false,
                            ascii: false,
                            width: 0,
                            group: 8,
                            ..HexConfig::default()
                        }),
                    )
                    .finish()
            }
        }
    }
}

impl std::fmt::Display for AlphaValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        if let Some(datatype) = self.as_builtin_datatype() {
            std::fmt::Display::fmt(&datatype, f)
        } else {
            unsafe {
                let ty = type_of(self);
                write!(f, "<{}>", &*ty)
            }
        }
    }
}
