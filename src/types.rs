use std::error::Error;
use std::mem::size_of;
use std::sync::Once;

use crate::env::Env;
use crate::exp::{TypeDefinition, TypeSpecifier};
use crate::gc;
use crate::gc_global;
use crate::symbol::Symbol;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AlphaType {
    pub name: Symbol,
    pub supertype: Symbol,
    pub typedef: AlphaTypeDef,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AlphaTypeDef {
    Abstract,
    Int(usize),
    Float(usize),
    Struct { fields: Vec<(Symbol, AlphaType)> },
}

impl AlphaType {
    pub fn from_exp(
        e: &TypeDefinition,
        types: &Env<AlphaType>,
    ) -> Result<AlphaType, Box<dyn Error>> {
        let name = e.name;
        let supertype = e.supertype;
        let typedef = match &e.specifier {
            TypeSpecifier::Abstract => AlphaTypeDef::Abstract,
            TypeSpecifier::Integer(n) => AlphaTypeDef::Int(*n),
            TypeSpecifier::Float(n) => AlphaTypeDef::Float(*n),
            TypeSpecifier::Struct(fields) => {
                let fs = fields
                    .iter()
                    .map(|f| {
                        (
                            f.name,
                            types.lookup(f.typ).cloned().expect("unable to lookup type"),
                        )
                    })
                    .collect::<Vec<_>>();
                // fs.sort_by(|a, b| a.1.typedef.is_ptr().cmp(&b.1.typedef.is_ptr()).reverse());
                AlphaTypeDef::Struct { fields: fs }
            }
        };

        Ok(AlphaType {
            name,
            supertype,
            typedef,
        })
    }
}

impl AlphaTypeDef {
    /// Returns `true` if this type can be inlined as a field. i.e. size of the type is known and <
    /// 8 bytes.
    pub fn is_inlinable(&self) -> bool {
        match self {
            AlphaTypeDef::Abstract => false,
            AlphaTypeDef::Int(_) => true,
            AlphaTypeDef::Float(_) => true,
            AlphaTypeDef::Struct { fields } => fields.len() <= 1,
        }
    }

    /// Returns `true` if values of that type can contain pointers.
    pub fn has_ptrs(&self) -> bool {
        match self {
            AlphaTypeDef::Abstract => true,
            AlphaTypeDef::Int(_) => false,
            AlphaTypeDef::Float(_) => false,
            AlphaTypeDef::Struct { fields } => {
                fields.iter().any(|(_name, typ)| typ.typedef.is_ptr())
            }
        }
    }

    /// Returns `true` if fields of that type (potentially inlined) contain pointers that GC needs
    /// to traverse.
    pub fn is_ptr(&self) -> bool {
        if self.is_inlinable() {
            self.has_ptrs()
        } else {
            // if types is not inlinable, we store it as ptr → this type has pointers
            true
        }
    }

    pub fn size(&self) -> Option<usize> {
        let size = match self {
            AlphaTypeDef::Abstract => return None,
            AlphaTypeDef::Int(bits) => (bits + 7) / 8,
            AlphaTypeDef::Float(bits) => (bits + 7) / 8,
            AlphaTypeDef::Struct { fields } => fields.len() * 8,
        };
        let size = ((size + 7) / 8) * 8;
        Some(size)
    }

    pub fn n_ptrs(&self) -> Option<usize> {
        let n = match self {
            AlphaTypeDef::Abstract => return None,
            AlphaTypeDef::Int(_) => 0,
            AlphaTypeDef::Float(_) => 0,
            AlphaTypeDef::Struct { fields } => fields
                .iter()
                .take_while(|(_, typ)| typ.typedef.is_ptr())
                .count(),
        };
        Some(n)
    }
}

pub type AnyPtr = *const u64;
pub type AnyPtrMut = *mut u64;
pub type GenericFn = unsafe extern "C" fn(i64, *const AnyPtr) -> AnyPtr;

// type DataType = { size: i64, n_ptrs: i64, methods: i64 }
#[derive(Debug)]
#[repr(C)]
pub struct DataType {
    pub supertype: *const AbstractType,
    pub size: u64,
    pub n_ptrs: u64,
    pub methods: Vec<Method>,
    pub name: String,
}

// type DataType = { size: i64, n_ptrs: i64, methods: i64 }
#[derive(Debug)]
#[repr(C)]
pub struct AbstractType {
    pub supertype: *const AbstractType,
    pub name: String,
}

#[derive(Debug)]
pub enum ParamSpecifier {
    Eq(AnyPtr),
    SubtypeOf(AnyPtr),
}

#[derive(Debug)]
pub struct Method {
    pub signature: Vec<ParamSpecifier>,
    // compiled instance of the method
    pub instance: GenericFn,
}

gc_global!(pub ANY_T: AbstractType);
gc_global!(pub TYPE_T: AbstractType);
gc_global!(pub DATATYPE_T: DataType);
gc_global!(pub ABSTRACTTYPE_T: DataType);

static INIT: Once = Once::new();

pub fn init() {
    INIT.call_once(|| unsafe {
        {
            let any_t = gc::allocate(size_of::<AbstractType>()) as *mut AbstractType;
            ANY_T.store(any_t);
            *any_t = AbstractType {
                supertype: any_t,
                name: "Any".to_string(),
            };
        }

        {
            let type_t = gc::allocate(size_of::<AbstractType>()) as *mut AbstractType;
            TYPE_T.store(type_t);
            *type_t = AbstractType {
                supertype: ANY_T.load(),
                name: "Type".to_string(),
            };
        }

        {
            let datatype_t = gc::allocate(size_of::<DataType>()) as *mut DataType;
            DATATYPE_T.store(datatype_t);
            set_typetag(datatype_t, datatype_t);
            *datatype_t = DataType {
                supertype: TYPE_T.load(),
                size: std::mem::size_of::<DataType>() as u64,
                n_ptrs: 0,
                methods: Vec::new(),
                name: "DataType".to_string(),
            };
        }

        {
            let abstracttype_t = gc::allocate(size_of::<DataType>()) as *mut DataType;
            set_typetag(abstracttype_t, DATATYPE_T.load());
            *abstracttype_t = DataType {
                supertype: TYPE_T.load(),
                size: std::mem::size_of::<AbstractType>() as u64,
                n_ptrs: 0,
                methods: Vec::new(),
                name: "AbstractType".to_string(),
            };

            set_typetag(ANY_T.load(), abstracttype_t);
            set_typetag(TYPE_T.load(), abstracttype_t);
        }
    });
}

unsafe fn set_typetag<T>(ptr: *mut T, typetag: *const DataType) {
    let typetag_ptr = (ptr as *mut u64).sub(1) as *mut *const DataType;
    *typetag_ptr = typetag;
}
