use std::error::Error;
use std::mem::size_of;
use std::sync::Once;

use crate::env::Env;
use crate::exp::{TypeDefinition, TypeSpecifier};
use crate::gc;
use crate::gc::GcBox;
use crate::gc_global;
use crate::svec::SVec;
use crate::symbol::{symbol, Symbol};

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
    pub name: Symbol,
    pub supertype: *const DataType,
    pub is_abstract: bool,
    pub size: u64,
    pub n_ptrs: u64,
    pub methods: Vec<Method>,
}

impl AlphaValue for DataType {
    fn typetag() -> *const DataType {
        DATATYPE_T.load()
    }

    fn datatype() -> DataType {
        DataType {
            name: symbol("DataType"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: size_of::<DataType>() as u64,
            n_ptrs: 0, // TODO: symbol is ptr?
            methods: Vec::new(),
        }
    }

    fn as_anyptr(&self) -> *const u64 {
        self as *const DataType as AnyPtr
    }
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

gc_global!(pub ANY_T: DataType);
gc_global!(pub DATATYPE_T: DataType);
gc_global!(pub SYMBOL_T: DataType);
gc_global!(pub SVEC_T: DataType);

#[inline]
unsafe fn initialize_global_type<T: AlphaValue>(global: &GcBox<DataType>) {
    *global.load() = T::datatype();
}

pub fn init() {
    static INIT: Once = Once::new();
    INIT.call_once(|| unsafe {
        let globals = [&ANY_T, &DATATYPE_T, &SYMBOL_T, &SVEC_T];
        // SYMBOL_T must be allocated first because `symbol()` functions requires it to be set. The
        // DataType itself can be initialized later though.
        //
        // SVEC_T must be allocated before any SVec creation. The DataType itself can be initialized
        // later.
        for global in &globals {
            global.store(gc::allocate(size_of::<DataType>()) as *mut DataType);
        }
        let datatype_t = DATATYPE_T.load();
        for global in &globals {
            set_typetag(global.load(), datatype_t);
        }

        {
            let any_t = ANY_T.load();
            *any_t = DataType {
                name: symbol("Any"),
                supertype: any_t,
                is_abstract: true,
                methods: Vec::new(),
                size: 0,
                n_ptrs: 0,
            };
        }

        initialize_global_type::<DataType>(&DATATYPE_T);
        initialize_global_type::<Symbol>(&SYMBOL_T);
        initialize_global_type::<SVec>(&SVEC_T);
    });
}

pub unsafe fn set_typetag<T>(ptr: *mut T, typetag: *const DataType) {
    *typetag_ptr(ptr) = typetag;
}
pub unsafe fn get_typetag<T>(ptr: *const T) -> *const DataType {
    *typetag_ptr(ptr)
}
unsafe fn typetag_ptr<T>(ptr: *const T) -> *mut *const DataType {
    (ptr as *mut *const DataType).sub(1)
}

pub trait AlphaValue {
    fn typetag() -> *const DataType;
    fn datatype() -> DataType;
    fn as_anyptr(&self) -> AnyPtr;
}
