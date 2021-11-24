mod datatype;
mod method;
mod primitive;
mod string;
mod svec;
mod symbol;
mod r#type;
mod void;

pub use self::datatype::*;
pub use self::method::*;
pub use self::primitive::*;
pub use self::r#type::*;
pub use self::string::*;
pub use self::svec::*;
pub use self::symbol::*;
pub use self::void::*;

use crate::env::Env;
use crate::exp::{TypeDefinition, TypeSpecifier};
use crate::gc;
use crate::gc::GcRoot;
use crate::gc_global;

use std::error::Error;
use std::sync::Once;

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

    pub fn pointer_offsets(&self) -> Option<Vec<usize>> {
        let pointers = match self {
            AlphaTypeDef::Abstract => return None,
            AlphaTypeDef::Int(_) => Vec::new(),
            AlphaTypeDef::Float(_) => Vec::new(),
            AlphaTypeDef::Struct { fields } => {
                let mut ptrs = Vec::new();
                for (i, (_, typ)) in fields.iter().enumerate() {
                    if typ.typedef.is_ptr() {
                        ptrs.push(i * 8);
                    }
                }
                ptrs
            }
        };
        Some(pointers)
    }
}

pub type AnyPtr = *const u64;
pub type AnyPtrMut = *mut u64;
pub type GenericFn = unsafe extern "C" fn(i64, *const AnyPtr) -> AnyPtr;

gc_global!(pub ANY_T: DataType);
gc_global!(pub TYPE_T: DataType);
gc_global!(pub DATATYPE_T: DataType);
gc_global!(pub SYMBOL_T: DataType);
gc_global!(pub SVEC_T: DataType);
gc_global!(pub SVEC_EMPTY: SVec);
gc_global!(pub VOID_T: DataType);
gc_global!(pub VOID: Void);
gc_global!(pub METHOD_T: DataType);
gc_global!(pub STRING_T: DataType);
gc_global!(pub F64_T: DataType);
gc_global!(pub I64_T: DataType);

#[inline]
unsafe fn allocate_global_type<T: AlphaValue>(global: &GcRoot<DataType>) {
    let ptrs = T::pointers();
    let t = DataType::allocate_perm(ptrs.len());
    set_typetag(t, DATATYPE_T.load());
    (*t).n_ptrs = ptrs.len();
    (*t).pointers_mut().copy_from_slice(ptrs);
    global.store(t);
}

#[inline]
unsafe fn initialize_global_type<T: AlphaValue>(global: &GcRoot<DataType>) {
    *global.load_mut() = T::datatype();
}

pub fn init() {
    static INIT: Once = Once::new();
    INIT.call_once(|| unsafe {
        {
            let ptrs = <DataType as AlphaValue>::pointers();
            let datatype_t = DataType::allocate_perm(ptrs.len());
            DATATYPE_T.store(datatype_t);
            // gc::allocate_perm(
            //     size_of::<DataType>()
            //         + <DataType as AlphaValue>::pointers().len() * size_of::<usize>(),
            // ) as *mut DataType;
            set_typetag(datatype_t, datatype_t);
            (*datatype_t).size = std::mem::size_of::<DataType>();
            (*datatype_t).n_ptrs = ptrs.len();
            (*datatype_t).pointers_mut().copy_from_slice(ptrs);
        }

        ANY_T.store(DataType::allocate_perm(0));
        allocate_global_type::<Type>(&TYPE_T);
        // SYMBOL_T must be allocated first because `symbol()` functions requires it to be set. The
        // DataType itself can be initialized later though.
        allocate_global_type::<SymbolNode>(&SYMBOL_T);
        // SVEC_T must be allocated before any SVec creation. The DataType itself can be initialized
        // later.
        allocate_global_type::<SVec>(&SVEC_T);
        allocate_global_type::<Void>(&VOID_T);
        allocate_global_type::<Method>(&METHOD_T);
        allocate_global_type::<AlphaString>(&STRING_T);
        allocate_global_type::<AlphaI64>(&I64_T);
        allocate_global_type::<AlphaF64>(&F64_T);

        // SVEC_EMPTY must be initialized before calling initialize_global_type() as many
        // implementations of AlphaValue::datatype() use SVEC_EMPTY to initialize methods field.
        SVEC_EMPTY.store(SVec::new(&[]) as *mut _);
        {
            let void = gc::allocate_perm(0) as *mut Void;
            set_typetag(void, VOID_T.load());
            VOID.store(void);
        }

        {
            let any_t = ANY_T.load_mut();
            *any_t = DataType {
                name: symbol("Any"),
                supertype: any_t,
                is_abstract: true,
                methods: SVEC_EMPTY.load(),
                size: usize::MAX,
                n_ptrs: 0,
                pointers: [],
            };
        }

        initialize_global_type::<DataType>(&DATATYPE_T);
        initialize_global_type::<SymbolNode>(&SYMBOL_T);
        initialize_global_type::<SVec>(&SVEC_T);
        initialize_global_type::<Void>(&VOID_T);
        initialize_global_type::<Method>(&METHOD_T);
        initialize_global_type::<AlphaString>(&STRING_T);
        initialize_global_type::<Type>(&TYPE_T);
        initialize_global_type::<AlphaI64>(&I64_T);
        initialize_global_type::<AlphaF64>(&F64_T);
    });
}

pub unsafe fn set_typetag<T>(ptr: *mut T, typetag: *const DataType) {
    *typetag_ptr(ptr) = typetag;
    debug_assert_ne!(
        (typetag as usize),
        0x1,
        "set_typetag(): trying to move out {:p} -> 0x0",
        ptr
    );
    debug_assert!(
        // early init yet
        DATATYPE_T.load().is_null() ||
            // moved out
            (typetag as usize) & 0x1 == 0x1 ||
            (get_typetag(typetag) as usize) & 0x1 == 0x1 ||
            get_typetag(typetag) == DATATYPE_T.load(),
        "set_typetag() is used to set invalid tag: {:p}",
        typetag
    )
}
pub unsafe fn get_typetag<T>(ptr: *const T) -> *const DataType {
    let typetag = *typetag_ptr(ptr);
    if !((typetag as usize) & 0x1 == 0x1
        || (*typetag_ptr(typetag) as usize) & 0x1 == 0x1
        || *typetag_ptr(typetag) == DATATYPE_T.load())
    {
        let ty = typetag;
        let ty_ty = *typetag_ptr(ty);
        tracing::error!("get_typetag({:p}), ty={:p}, ty_ty={:p}", ptr, ty, ty_ty);
        // gc::debug_ptr(ptr.cast());
        gc::debug_ptr(ty.cast());
        gc::debug_ptr(ty_ty.cast());
        panic!(
            "typetag is neither moved out nor a type: typetag={:p}",
            typetag
        )
    }
    typetag
}
pub unsafe fn typetag_ptr<T>(ptr: *const T) -> *mut *const DataType {
    debug_assert_eq!(
        (ptr as usize) % 8,
        0,
        "typetag_ptr() is called on unaligned pointer: {:p}",
        ptr
    );
    (ptr as *mut *const DataType).sub(1)
}

pub trait AlphaValue: Sized {
    fn typetag() -> *const DataType;

    fn datatype() -> DataType;
    fn pointers() -> &'static [usize] {
        static PTRS: [usize; 0] = [];
        &PTRS
    }

    fn size(_ptr: *const Self) -> usize {
        std::mem::size_of::<Self>()
    }

    fn trace_pointers<F>(ptr: *mut Self, mut trace_ptr: F)
    where
        F: FnMut(*mut AnyPtrMut) -> bool,
    {
        unsafe {
            let ty = get_typetag(ptr); // self datatype
            let ptr_offsets = (*ty).pointers();
            for offset in ptr_offsets {
                let field = (ptr as *mut u8).add(*offset) as *mut AnyPtrMut;
                trace_ptr(field);
            }
        }
    }
}
