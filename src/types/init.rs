pub use crate::types::*;

use crate::gc;
use crate::gc::GcRoot;
use crate::gc_global;

use std::sync::Once;

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
unsafe fn allocate_global_type<T: AlphaType>(global: &GcRoot<DataType>) {
    let ptrs = T::pointers();
    let t = DataType::allocate_perm(ptrs.len());
    set_typetag(t, DATATYPE_T.load());
    (*t).n_ptrs = ptrs.len();
    (*t).pointers_mut().copy_from_slice(ptrs);
    global.store(t);
}

#[inline]
unsafe fn initialize_global_type<T: AlphaType>(global: &GcRoot<DataType>) {
    *global.load_mut() = T::datatype();
}

pub fn init() {
    static INIT: Once = Once::new();
    INIT.call_once(|| unsafe {
        {
            let ptrs = <DataType as AlphaType>::pointers();
            let datatype_t = DataType::allocate_perm(ptrs.len());
            DATATYPE_T.store(datatype_t);
            set_typetag(datatype_t, datatype_t);
            (*datatype_t).size = std::mem::size_of::<DataType>();
            (*datatype_t).n_ptrs = ptrs.len();
            (*datatype_t).pointers_mut().copy_from_slice(ptrs);
        }

        allocate_global_type::<Any>(&ANY_T);
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

        initialize_global_type::<Any>(&ANY_T);
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
