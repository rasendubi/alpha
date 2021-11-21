use std::alloc;
use std::collections::HashSet;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Mutex;
use std::sync::Once;

use once_cell::sync::Lazy;
use pretty_hex::{HexConfig, PrettyHex};
use tracing::{debug, trace};

use crate::types::*;

// TODO: this has to be thread-local when Alpha supports multi-threading.
static mut GC_ROOTS: *const GcFrame = std::ptr::null();

static mut GC_GLOBAL_ROOTS: MaybeUninit<Mutex<HashSet<GcRoot<'static>>>> = MaybeUninit::uninit();
fn gc_init() {
    static GC_INIT: Once = Once::new();
    GC_INIT.call_once(|| unsafe {
        GC_GLOBAL_ROOTS.write(Mutex::new(HashSet::new()));
    })
}
pub fn add_global_root(root: GcRoot<'static>) {
    gc_init();
    unsafe {
        let mut roots = GC_GLOBAL_ROOTS.assume_init_ref().lock().unwrap();
        roots.insert(root);
    }
}

static mut BLOCK: Block = Block {
    start: std::ptr::null_mut(),
    cur: AtomicPtr::new(std::ptr::null_mut()),
    end: std::ptr::null_mut(),
    allocation: MaybeUninit::uninit(),
};
static mut PREV: Block = Block {
    start: std::ptr::null_mut(),
    cur: AtomicPtr::new(std::ptr::null_mut()),
    end: std::ptr::null_mut(),
    allocation: MaybeUninit::uninit(),
};

const GC_THRESHOLD: isize = 256;

const TESTING_GC: bool = true;

#[macro_export]
macro_rules! gc_global {
    ( $vis:vis $i:ident : $t:ty ) => {
        $vis static $i: $crate::gc::GcBox<$t> = $crate::gc::GcBox::new();
        paste::paste! {
            #[ctor::ctor]
            fn [<$i:lower _register>]() {
                $crate::gc::add_global_root($crate::gc::GcRoot::new(&$i));
            }
        }
    };
}

#[macro_export]
macro_rules! gc_box {
    ( $i:ident ) => {
        let $i = $crate::gc::GcBox::from_const_ptr($i);
        $crate::gc_frame![$i];
    };
}

#[macro_export]
macro_rules! gc_frame {
    ( $( $e:expr ),* ) => {
        #[allow(unused_unsafe)]
        let roots = unsafe { [ $( ::std::mem::transmute::<&::std::sync::atomic::AtomicPtr<_>, &::std::sync::atomic::AtomicPtr<()>>($e.as_ref()), )* ] };
        let gc_frame = $crate::gc::GcFrame::new(&roots);
        let _registration = $crate::gc::GcFrameRegistration::new(&gc_frame);
    }
}

#[macro_export]
macro_rules! gc_box_slice {
    ( $i:ident ) => {
        let $i = $i
            .iter()
            .map(|x| $crate::gc::GcBox::from_const_ptr(*x))
            .collect::<Vec<_>>();
        #[allow(unused_unsafe)]
        let roots = $i
            .iter()
            .map(|x| unsafe {
                ::std::mem::transmute::<
                    &::std::sync::atomic::AtomicPtr<_>,
                    &::std::sync::atomic::AtomicPtr<()>,
                >(x.as_ref())
            })
            .collect::<Vec<_>>();
        let gc_frame = $crate::gc::GcFrame::new(&roots);
        let _registration = $crate::gc::GcFrameRegistration::new(&gc_frame);
    };
}

#[derive(Debug)]
#[repr(C)]
pub struct GcBox<T> {
    ptr: AtomicPtr<T>,
}

impl<T> GcBox<T> {
    pub const fn new() -> GcBox<T> {
        GcBox {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    #[allow(dead_code)]
    pub const fn from_ptr(ptr: *mut T) -> Self {
        GcBox {
            ptr: AtomicPtr::new(ptr),
        }
    }

    pub const fn from_const_ptr(ptr: *const T) -> Self {
        GcBox {
            ptr: AtomicPtr::new(ptr as *mut T),
        }
    }

    pub fn as_ref(&self) -> &AtomicPtr<T> {
        &self.ptr
    }

    pub fn load(&self) -> *mut T {
        self.ptr.load(Ordering::SeqCst)
    }

    pub fn store(&self, ptr: *mut T) {
        self.ptr.store(ptr, Ordering::SeqCst);
    }
}

#[derive(Debug)]
pub struct GcFrame<'a> {
    prev: *const GcFrame<'static>,
    roots: &'a [&'a AtomicPtr<()>],
}
impl<'a> GcFrame<'a> {
    pub fn new(roots: &'a [&'a AtomicPtr<()>]) -> Self {
        Self {
            prev: unsafe { GC_ROOTS },
            roots,
        }
    }
}

#[derive(Debug)]
pub struct GcFrameRegistration<'a> {
    frame: *const GcFrame<'a>,
}
impl<'a> GcFrameRegistration<'a> {
    pub fn new(frame: &'a GcFrame<'a>) -> Self {
        let frame = frame as _;
        unsafe {
            let frame = std::mem::transmute::<*const GcFrame<'a>, *const GcFrame<'static>>(frame);
            // The cast is obviously unsafe, but we rely on the Drop implementation of
            // GcFrameRegistration to remove the frame from GC_ROOTS when it comes out of scope.
            GC_ROOTS = frame
        }
        Self { frame }
    }
}
impl<'a> Drop for GcFrameRegistration<'a> {
    fn drop(&mut self) {
        unsafe {
            debug_assert!(!GC_ROOTS.is_null());
            debug_assert!(GC_ROOTS == self.frame);
            GC_ROOTS = (*GC_ROOTS).prev;
        }
    }
}

#[derive(Debug)]
#[repr(C)]
pub struct GcRoot<'a> {
    ptr: *const AtomicPtr<()>,
    _phantom: PhantomData<&'a AtomicPtr<()>>,
}

unsafe impl<'a> Sync for GcRoot<'a> {}

impl<'a> std::cmp::PartialEq<GcRoot<'a>> for GcRoot<'a> {
    fn eq(&self, other: &Self) -> bool {
        (self.ptr as *const _) == other.ptr
    }
}

impl<'a> std::cmp::Eq for GcRoot<'a> {}

impl<'a> std::hash::Hash for GcRoot<'a> {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: std::hash::Hasher,
    {
        (self.ptr as *const AtomicPtr<_>).hash(hasher);
    }
}

impl<'a> GcRoot<'a> {
    pub fn new<T>(b: &'a GcBox<T>) -> Self {
        // trace!("New gc root at: {:p}", b);
        GcRoot {
            ptr: (&b.ptr as *const AtomicPtr<T>).cast::<AtomicPtr<()>>(),
            _phantom: PhantomData,
        }
    }

    pub unsafe fn from_ptr_unchecked<T>(ptr: *mut *mut T) -> Self {
        GcRoot {
            ptr: ptr.cast::<AtomicPtr<()>>(),
            _phantom: PhantomData,
        }
    }

    fn as_anyptr(&self) -> *mut AnyPtrMut {
        (self.ptr as *mut AtomicPtr<()>).cast()
        // unsafe { std::mem::transmute::<_, *mut AnyPtrMut>(self.ptr as *const AtomicPtr<()>) }
    }
}

struct Block {
    start: *mut u8,
    end: *mut u8,
    cur: AtomicPtr<u8>,
    allocation: MaybeUninit<region::Allocation>,
}

unsafe impl Sync for Block {}

impl Block {
    fn new() -> Block {
        let page_size = region::page::size();
        let mut allocation = region::alloc(page_size, region::Protection::READ_WRITE).unwrap();
        let std::ops::Range { start, end } = allocation.as_mut_ptr_range::<u8>();
        Block {
            start,
            end,
            cur: AtomicPtr::new(start),
            allocation: MaybeUninit::new(allocation),
        }
    }

    unsafe fn protect(&self) {
        if !self.start.is_null() {
            region::protect(
                self.start,
                self.allocation.assume_init_ref().len(),
                region::Protection::NONE,
            )
            .unwrap();
        }
    }

    fn bump(&self, size: usize) -> Option<*mut u8> {
        let res = self
            .cur
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |cur| {
                let next = unsafe { cur.add(size) };
                if next > self.end {
                    None
                } else {
                    Some(next)
                }
            });
        res.ok()
    }
}
impl Drop for Block {
    fn drop(&mut self) {
        unsafe {
            if !self.start.is_null() {
                std::ptr::drop_in_place(self.allocation.as_mut_ptr());
            }
        }
    }
}

fn align_size(size: usize) -> usize {
    const ALIGNMENT: usize = 8;
    (size + ALIGNMENT - 1) / ALIGNMENT * ALIGNMENT
}

#[tracing::instrument]
pub unsafe fn allocate(size: usize) -> *mut u8 {
    maybe_collect_garbage();
    // TODO: handle alignment
    let size = align_size(size);
    let start = BLOCK.bump(size + 8 /* typetag */);
    let start = start.unwrap_or_else(|| panic!("gc: out of memory"));
    let result = start.add(8 /* typetag */);
    trace!("allocting from:\n{:?}", backtrace::Backtrace::new());
    trace!("allocate({}) = {:#?}", size, result);
    result
}

/// Allocate permanent memory block. It is guaranteed to never be freed up by garbage collector.
pub unsafe fn allocate_perm(size: usize) -> *mut u8 {
    let start = alloc::alloc(alloc::Layout::from_size_align_unchecked(size + 8, 16));
    std::slice::from_raw_parts_mut(start, size + 8).fill(0);
    start.add(8 /* typetag */)
}

pub unsafe fn maybe_collect_garbage() {
    if TESTING_GC || BLOCK.end.offset_from(BLOCK.cur.load(Ordering::SeqCst)) < GC_THRESHOLD {
        collect_garbage();
    }
}

#[tracing::instrument]
pub unsafe fn data_size(ptr: AnyPtr) -> usize {
    let ty = get_typetag(ptr);
    debug_assert_eq!((ty as usize) & 0x1, 0x0); // value should not be moved out
    let ty = resolve_moved_out(ty as AnyPtr) as *const DataType; // type can be though
    let size = if ty == STRING_T.load() {
        AlphaString::size(ptr as *const AlphaString)
    } else if ty == SYMBOL_T.load() {
        SymbolNode::size(ptr as *const SymbolNode)
    } else if ty == SVEC_T.load() {
        SVec::size(ptr as *const SVec)
    } else if ty == METHOD_T.load() {
        Method::size(ptr as *const Method)
    } else {
        // regular datatype
        let ty_ty = get_typetag(ty);
        let ty_ty_ty = get_typetag(ty_ty);
        if ty_ty_ty == DATATYPE_T.load() {
            eprintln!("ty_ty: {:?}", *ty_ty);
            if ty_ty == METHOD_T.load() {
                eprintln!("ty: {:?}", *ty.cast::<Method>());
            } else if ty_ty == SVEC_T.load() {
                eprintln!("ty: SVec {:?}", *ty.cast::<SVec>());
            }
        }
        debug_assert_eq!(get_typetag(ty), DATATYPE_T.load());
        (*ty).size
    };
    let size = align_size(size);

    trace!(
        "size={} (ty={:p}, type_of(ty)={:p})",
        size,
        ty,
        get_typetag(ty),
    );

    size
}

pub unsafe fn is_moved_out(p: AnyPtr) -> Option<AnyPtr> {
    let ty = get_typetag(p);
    if (ty as usize) & 0x1 == 0x1 {
        Some(((ty as usize) & !0x1) as AnyPtr)
    } else {
        None
    }
}
pub unsafe fn resolve_moved_out(p: AnyPtr) -> AnyPtr {
    match is_moved_out(p) {
        Some(new_p) => new_p,
        None => p,
    }
}

#[tracing::instrument]
pub unsafe fn collect_garbage() {
    let hex_conf = HexConfig {
        ascii: false,
        width: 32,
        group: 8,
        // chunk: 1,
        ..HexConfig::default()
    };
    let block_to_slice = |block: &Block| {
        std::slice::from_raw_parts(
            block.start as *const u8,
            block.cur.load(Ordering::Relaxed).offset_from(block.start) as usize,
        )
    };

    debug!("collecting garbage");
    trace!(
        "  from@{:p}: {:x?}",
        BLOCK.start,
        block_to_slice(&BLOCK).hex_conf(hex_conf)
    );

    // let from = &mut BLOCK;
    let to = Block::new();
    let debug_trace_blocks = || {
        trace!(
            "  from@{:p}:\n{:x?}",
            BLOCK.start,
            block_to_slice(&BLOCK).hex_conf(hex_conf)
        );
        trace!(
            "  to  @{:p}:\n{:x?}",
            to.start,
            block_to_slice(&to).hex_conf(hex_conf)
        );
    };

    // trace_gcroots();

    // Returns `false` if pointer wasn't traced (null or unmanaged);
    let trace_ptr = |ptr_loc: *mut AnyPtrMut| {
        let span = tracing::trace_span!("trace_ptr", "{:p}", ptr_loc);
        let _guard = span.enter();

        trace!(
            "{:p} -> {:p}",
            ptr_loc,
            if ptr_loc.is_null() {
                std::ptr::null()
            } else {
                *ptr_loc
            },
        );
        let ptr = *ptr_loc;
        if ptr.is_null() {
            return false;
        }
        debug_trace_ptr(ptr);
        // BLOCK.end is inclusive because ptr can be zero-sized object.
        if (ptr as *const u8) < BLOCK.start || (ptr as *const u8) > BLOCK.end {
            // Not in the from block — likely a permanent object.
            trace!("<- unmanaged");
            return false;
        }

        let ty = get_typetag(ptr);
        trace!("ty: {:p}", ty);

        *ptr_loc = if (ty as usize) & 0x1 == 0x1 {
            // moved out
            let new = ((ty as usize) & !0x1) as AnyPtrMut;
            trace!("moved out: {:p} -> {:p}", ptr, new);
            new
        } else {
            let size = data_size(ptr);
            let new = to.bump(size + 8 /* typetag */).unwrap().add(8) as AnyPtrMut;
            trace!(
                "copying: {:p} -> {:p} (ty={:p}, size={})",
                ptr,
                new,
                ty,
                size
            );

            set_typetag(new, ty);
            set_typetag(ptr, ((new as usize) | 0x1) as *const DataType); // mark it as moved out
            std::ptr::copy_nonoverlapping(ptr as *const u8, new as *mut u8, size);
            new
        };

        debug_assert!(
            (*ptr_loc as *const u8) >= to.start && (*ptr_loc as *const u8) <= to.end,
            "{:p} should be inside to region: [{:p}, {:p}]",
            *ptr_loc,
            to.start,
            to.end
        );
        true
    };

    let trace_value = |ptr: AnyPtrMut| {
        let span = tracing::trace_span!("trace_value", "{:p}", ptr);
        let _guard = span.enter();

        if ptr.is_null() {
            return;
        }
        let ty = get_typetag(ptr);
        trace!("tracing: {:p} (ty={:p})", ptr, ty);
        if ty == SYMBOL_T.load() {
            // trace!("tracing as symbol");
            // SymbolNode::trace_pointers(ptr as _, trace_ptr);

            // Symbols are always perm-allocated and do not need to be traced.
        } else if ty == SVEC_T.load() {
            trace!("tracing as svec");
            SVec::trace_pointers(ptr as _, trace_ptr);
        } else {
            // trace generic DataType
            let ptr_offsets = (*ty).pointers();
            if ((*ty).name.node as *const _ as *const u8).is_null() {
                trace!(
                    "tracing as generic DataType {:?}, ptrs={:?}",
                    std::slice::from_raw_parts(ty as *const u8, DataType::size(ty)).hex_conf(
                        HexConfig {
                            title: false,
                            width: 0,
                            ..hex_conf
                        }
                    ),
                    ptr_offsets
                );
            } else {
                trace!("tracing as generic {:?}, ptrs={:?}", *ty, ptr_offsets);
            }
            for offset in ptr_offsets {
                let field = ptr.cast::<u8>().add(*offset).cast::<AnyPtrMut>();
                trace_ptr(field);
            }
        }
    };

    {
        let span = tracing::trace_span!("trace_globals");
        let _guard = span.enter();

        let globals = GC_GLOBAL_ROOTS.assume_init_ref().lock().unwrap();
        for root in globals.iter() {
            // TODO: global roots are mostly perm-alloced. Trace values instead?
            if !trace_ptr(root.as_anyptr()) {
                trace_value(*root.as_anyptr());
            }
        }
    }

    trace!("after globals");
    debug_trace_blocks();

    {
        let span = tracing::trace_span!("trace_roots");
        let _guard = span.enter();

        let mut cur = GC_ROOTS;
        while !cur.is_null() {
            for root in (*cur).roots.iter() {
                let root: &AtomicPtr<()> = *root;
                static_assertions::assert_eq_size!(AtomicPtr<()>, *mut ());
                let root = (root as *const AtomicPtr<()> as *mut AtomicPtr<()>).cast::<AnyPtrMut>();
                // This is stated in the AtomicPtr doc, but good to re-check.
                if !trace_ptr(root) {
                    trace_value(*root);
                }
            }
            cur = (*cur).prev;
        }
    }

    trace!("after roots");
    debug_trace_blocks();

    let mut cur = to.start;
    while cur < to.cur.load(Ordering::Relaxed) {
        cur = cur.add(8); // skip typetag

        let span = tracing::trace_span!("traverse_to", "{:p}", cur);
        let _guard = span.enter();

        let ty_ptr = typetag_ptr(cur);
        trace_ptr(ty_ptr as _);
        trace_value(cur as AnyPtrMut);
        let size = data_size(cur as _);
        cur = cur.add(size);
    }

    trace!("after traverse");
    debug_trace_blocks();
    PREV = std::mem::replace(&mut BLOCK, to);
    PREV.protect();
}

static mut TRACED_PTRS: Lazy<Mutex<HashSet<AnyPtr>>> = Lazy::new(|| Mutex::new(HashSet::new()));

unsafe fn debug_trace_ptr(ptr: AnyPtr) {
    if ptr.is_null() {
        return;
    }

    if log::log_enabled!(log::Level::Trace) {
        let mut traced_ptrs = TRACED_PTRS.lock().unwrap();
        if !traced_ptrs.contains(&ptr) {
            debug_ptr(ptr);

            traced_ptrs.insert(ptr);
        }
    }
}

#[tracing::instrument]
pub unsafe fn debug_ptr(ptr: AnyPtr) {
    let ty = get_typetag(ptr);
    let ty = resolve_moved_out(ty.cast()).cast();

    assert!(
        is_moved_out(ptr).is_none(),
        "debug_ptr() value is moved out: {:p} -> {:p}",
        ptr,
        resolve_moved_out(ptr)
    );
    // assert!(
    //     is_moved_out(ty.cast()).is_none(),
    //     "debug_ptr() type is moved out: {:p} -> {:p}",
    //     ty,
    //     resolve_moved_out(ty.cast())
    // );
    assert_eq!(
        get_typetag(ty),
        DATATYPE_T.load(),
        "debug_ptr() type of type is not DataType"
    );
    if ty == DATATYPE_T.load() {
        let ptr = ptr.cast::<DataType>();
        if ((*ptr).name.node as *const _ as *const u8).is_null() {
            // datatype is not completely initialized
            return;
        }
        trace!(target: "alpha::gc::debug_value", "{:?}", *ptr);
    } else if ty == TYPE_T.load() {
        trace!(target: "alpha::gc::debug_value", "{:?}", *ptr.cast::<Type>());
    } else if ty == SYMBOL_T.load() {
        trace!(target: "alpha::gc::debug_value", "Symbol {:?}", *ptr.cast::<SymbolNode>());
    } else if ty == SVEC_T.load() {
        trace!(target: "alpha::gc::debug_value", "SVec {:?}", *ptr.cast::<SVec>());
    } else if ty == VOID_T.load() {
        trace!(target: "alpha::gc::debug_value", "{:?}", *ptr.cast::<Void>());
    } else if ty == METHOD_T.load() {
        trace!(target: "alpha::gc::debug_value", "{:?}", *ptr.cast::<Method>());
    } else if ty == STRING_T.load() {
        trace!(target: "alpha::gc::debug_value", "AlphaString {:?}", *ptr.cast::<AlphaString>());
    } else {
        let size = data_size(ptr);
        trace!(target: "alpha::gc::debug_value", "ty={:p} generic {:?}, {:?}", ty, *ty, std::slice::from_raw_parts(ptr.cast::<u8>(), size).hex_dump());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    #[test]
    #[serial]
    fn collect_nothing() {
        crate::types::init();
        unsafe {
            collect_garbage();
        }
    }

    #[test]
    #[serial]
    fn collect_svec() {
        crate::types::init();
        unsafe {
            let s = SVEC_EMPTY.load();
            let _s = SVec::push(s, ANY_T.load().cast());
            collect_garbage();
        }
    }

    #[test]
    #[serial]
    fn collect_survive_gcbox() {
        crate::types::init();
        unsafe {
            let s = SVEC_EMPTY.load();
            let s = SVec::push(s, ANY_T.load().cast());
            gc_box!(s);
            collect_garbage();
            assert_eq!(get_typetag(s.load()), SVEC_T.load());
            assert_eq!((*s.load()).len(), 1);
        }
    }

    unsafe extern "C" fn nothing(_n_args: i64, _args: *const AnyPtr) -> AnyPtr {
        VOID.load().cast()
    }

    #[test]
    #[serial]
    fn collect_method_new() {
        crate::types::init();
        unsafe {
            let signature = SVec::push(SVEC_EMPTY.load(), ANY_T.load().cast());
            gc_box!(signature);
            let m = Method::new(signature.load(), nothing);
            gc_box!(m);
            collect_garbage();
            assert_eq!(get_typetag(m.load()), METHOD_T.load());
            assert_eq!((*m.load()).signature, signature.load());
            assert!((*m.load()).instance == nothing, "instance does not match");
        }
    }

    #[test]
    #[serial]
    fn datatype_new() {
        crate::types::init();
        unsafe {
            let ty = DataType::new(symbol("TestDataType"), ANY_T.load(), 0, &[]);
            gc_box!(ty);
            collect_garbage();
        }
    }

    #[test]
    #[serial]
    fn datatype_add_method() {
        crate::types::init();
        unsafe {
            let ty = DataType::new(symbol("TestDataType"), ANY_T.load(), 0, &[]);
            gc_box!(ty);
            collect_garbage();

            let signature = SVec::push(SVEC_EMPTY.load(), ANY_T.load().cast());
            gc_box!(signature);
            let m = Method::new(signature.load(), nothing);
            gc_box!(m);
            collect_garbage();

            DataType::add_method(ty.load(), m.load());

            assert_eq!((*(*ty.load()).methods).len(), 1);

            debug_ptr(ty.load().cast());
            debug_ptr((*ty.load()).methods.cast());
        }
    }

    #[test]
    #[serial]
    fn type_t() {
        crate::types::init();
        unsafe {
            let ty = DataType::new(symbol("TestDataType"), ANY_T.load(), 0, &[]);
            gc_box!(ty);
            let t = Type::new(ty.load());
            gc_box!(t);
            collect_garbage();

            assert_eq!((*t.load()).t, ty.load());
        }
    }
}
