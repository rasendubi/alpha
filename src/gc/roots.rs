//! Macros and functions for managing GC roots and “smart” Gc types.
use std::collections::HashSet;
use std::marker::PhantomData;
use std::sync::Mutex;

use once_cell::sync::Lazy;
use tracing::trace;

use crate::types::*;

pub use llvm::gc::shadow_stack::{pop_gcframe, push_gcframe, FrameMap, GcRootChain, StackEntry};

// TODO: this has to be thread-local when Alpha supports multi-threading.
pub static mut GC_ROOT_CHAIN: GcRootChain = std::ptr::null_mut();

static GC_GLOBAL_ROOTS: Lazy<Mutex<HashSet<GcRoot<'static, AlphaValue>>>> =
    Lazy::new(|| Mutex::new(HashSet::new()));

pub(super) fn visit_roots<Visitor>(mut visit: Visitor)
where
    Visitor: FnMut(*mut *const u8, *const u8),
{
    {
        let globals = GC_GLOBAL_ROOTS.lock().unwrap();
        for root in globals.iter() {
            visit(root.as_anyptr().cast(), std::ptr::null());
        }
    }

    unsafe {
        llvm::gc::shadow_stack::visit_roots(GC_ROOT_CHAIN, visit);
    }
}

#[tracing::instrument]
pub unsafe fn add_global_root(root: GcRoot<'static, AlphaValue>) {
    let mut roots = GC_GLOBAL_ROOTS.lock().unwrap();
    trace!(
        "adding root: {:?} -> {:?}",
        root.as_anyptr(),
        *root.as_anyptr()
    );
    roots.insert(root);
}

#[tracing::instrument]
pub unsafe fn remove_global_root(root: &GcRoot<'static, AlphaValue>) {
    let mut roots = GC_GLOBAL_ROOTS.lock().unwrap();
    trace!("removing root: {:?}", root.as_anyptr(),);
    let removed = roots.remove(root);
    debug_assert!(removed);
}

#[macro_export]
macro_rules! gc_global {
    ( $vis:vis $i:ident : $t:ty ) => {
        paste::paste! {
            static mut [<$i _GC>]: $crate::gc::Gc<$t> = $crate::gc::Gc::null();
            $vis static $i: $crate::gc::roots::GcRoot<'static, $t> = $crate::gc::roots::GcRoot::new(unsafe {&[<$i _GC>]});
            #[::ctor::ctor]
            fn [<$i:lower _register>]() {
                unsafe {
                    $crate::gc::roots::add_global_root((&$i).as_alpha_value().clone());
                }
            }
        }
    };
}

#[macro_export]
macro_rules! gc_box {
    ( $i:ident ) => {
        let $i = $crate::gc::Gc::new($i);
        $crate::gc_frame![$i];
    };
}

#[macro_export]
macro_rules! count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + $crate::count!($($xs)*));
}

pub unsafe fn gcroot_of_type<T: AlphaDataType>(ptr: &*const u8, _to: Gc<T>) -> GcRoot<T> {
    GcRoot::from_ptr_ref(ptr as *const *const u8 as *const *const T)
}

#[macro_export]
macro_rules! gc_frame {
    ( $( $i:ident ),* ) => {
        // Ideally, should be static.
        let frame_map: ::llvm::gc::shadow_stack::FrameMap<0> = ::llvm::gc::shadow_stack::FrameMap::new($crate::count!( $($i)* ) as u32, []);
        #[allow(unused_unsafe)]
        let stack_entry = unsafe {::llvm::gc::shadow_stack::StackEntry::new($crate::gc::roots::GC_ROOT_CHAIN, &frame_map, [
            $( $i.ptr().cast() ),*
        ])};
        #[allow(unused_unsafe)]
        let _stack_entry_registration = unsafe{$crate::gc::roots::GcFrameRegistration::new(&stack_entry)};
        $crate::gc_frame!(@ stack_entry, 0, $($i)*)
    };
    ( @ $stack_entry:ident, $n:expr, $i:ident $($is:ident)* ) => {
        #[allow(unused_unsafe)]
        let $i = unsafe {$crate::gc::roots::gcroot_of_type(&($stack_entry).roots[$n], $i)};
        $crate::gc_frame!(@ $stack_entry, ($n + 1), $($is)*)
    };
    ( @ $stack_entry:ident, $n:expr, ) => {
    };
}

pub fn with_gc_box_slice<T, R, F: FnOnce(&[Gc<T>]) -> R>(elements: &[*const T], f: F) -> R {
    let frame_map = FrameMap::new(elements.len() as u32, []);
    alloca::with_alloca(
        std::mem::size_of::<StackEntry<0>>() + std::mem::size_of::<*const T>() * elements.len(),
        |mem| unsafe {
            let ptr = mem.as_mut_ptr().cast::<StackEntry<0>>();
            *ptr = StackEntry::new(GC_ROOT_CHAIN, &frame_map, []);
            let elements_ptr = ptr.add(1).cast::<*const T>();
            let new_elements = std::slice::from_raw_parts_mut(elements_ptr, elements.len());
            new_elements.copy_from_slice(elements);
            let _registration = GcFrameRegistration::new::<0>(&*ptr);
            f(std::slice::from_raw_parts(
                elements_ptr.cast::<Gc<T>>(),
                elements.len(),
            ))
        },
    )
}

/// A pointer to GC-managed value.
///
/// Must be rooted at safepoints.
#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Gc<T>(*const T);

impl<T> Gc<T> {
    pub const fn new(ptr: *const T) -> Self {
        Self(ptr)
    }

    pub const fn null() -> Self {
        Self(std::ptr::null_mut())
    }

    pub fn ptr(&self) -> *const T {
        self.0
    }
}

#[derive(Debug)]
#[repr(C)]
pub struct GcRoot<'a, T> {
    ptr: *mut Gc<T>,
    _phantom: PhantomData<&'a Gc<T>>,
}

// TODO: these are not Send/Sync currently, but should be if GC implements stop-the-world.
unsafe impl<'a, T> Sync for GcRoot<'a, T> {}
unsafe impl<'a, T> Send for GcRoot<'a, T> {}

impl<'a, T: AlphaDataType> Clone for GcRoot<'a, T> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            _phantom: self._phantom,
        }
    }
}

impl<'a, T: AlphaDataType> PartialEq for GcRoot<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.ptr, other.ptr)
    }
}

impl<'a, T: AlphaDataType> Eq for GcRoot<'a, T> {}

impl<'a, T: AlphaDataType> std::hash::Hash for GcRoot<'a, T> {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: std::hash::Hasher,
    {
        hasher.write_usize(self.ptr as usize);
    }
}

impl<'a, T> GcRoot<'a, T> {
    pub const fn new(ptr: &'a Gc<T>) -> Self {
        GcRoot {
            ptr: ptr as *const Gc<T> as *mut Gc<T>,
            _phantom: PhantomData,
        }
    }

    pub const fn from_ptr_ref(ptr: *const *const T) -> Self {
        Self {
            ptr: (ptr as *const *const T) as *mut Gc<T>,
            _phantom: PhantomData,
        }
    }

    // TODO: deprecate
    // #[deprecated]
    pub fn load(&self) -> *const T {
        self.ptr()
    }

    pub fn load_mut(&self) -> *mut T {
        unsafe { (*self.ptr).0 as *mut T }
    }

    pub fn store(&self, ptr: *const T) {
        unsafe {
            (*self.ptr).0 = ptr;
        }
    }

    pub fn as_ref(&self) -> &*const T {
        unsafe { &(*self.ptr).0 }
    }

    pub fn ptr(&self) -> *const T {
        unsafe { (*self.ptr).ptr() }
    }

    pub fn as_alpha_value(&self) -> &GcRoot<AlphaValue> {
        unsafe { std::mem::transmute_copy::<&Self, &GcRoot<AlphaValue>>(&self) }
    }

    fn as_anyptr(&self) -> *mut AnyPtrMut {
        self.ptr.cast()
    }
}

#[derive(Debug)]
pub struct GcFrameRegistration<'a> {
    frame: *mut StackEntry<0>,
    _phantom: PhantomData<&'a StackEntry<0>>,
}
impl<'a> GcFrameRegistration<'a> {
    pub fn new<const N: usize>(frame: &'a StackEntry<N>) -> Self {
        let frame = StackEntry::as_unsized(frame) as *mut StackEntry<0>;
        unsafe {
            push_gcframe(&mut GC_ROOT_CHAIN, frame);
        }
        Self {
            frame,
            _phantom: PhantomData,
        }
    }
}
impl<'a> Drop for GcFrameRegistration<'a> {
    fn drop(&mut self) {
        unsafe {
            pop_gcframe(&mut GC_ROOT_CHAIN, self.frame);
        }
    }
}
