pub mod roots;
pub use self::roots::{
    add_global_root, remove_global_root, with_gc_box_slice, Gc, GcRoot, GcRootChain, GC_ROOT_CHAIN,
};

use std::alloc;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicPtr, Ordering};

use pretty_hex::{HexConfig, PrettyHex};
use tracing::{info, trace};

use crate::types::*;

static mut TO: Block = Block::empty();
static mut FROM: Block = Block::empty();

#[cfg_attr(feature = "gc_debug", allow(dead_code))]
const GC_THRESHOLD: usize = 256;

/// All values in Alpha are tagged with `Tag`, which resides before any value in memory.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
struct Tag {
    // This can either be a (*const DataType) or (*const AlphaValue | 0x1)
    ty: *const DataType,
}
const TAG_SIZE: usize = std::mem::size_of::<Tag>();

pub unsafe fn type_of<T: ?Sized>(ptr: *const T) -> *const DataType {
    let ty = Tag::of(ptr).get_type();
    debug_assert_eq!(
        Tag::of(ty).get_type(),
        DATATYPE_T.load(),
        "type_of(): type of type is not DataType"
    );
    ty
}

pub unsafe fn set_type<T: ?Sized>(ptr: *const T, ty: *const DataType) {
    *get_tag_ptr(ptr) = Tag::new(ty);
}

unsafe fn get_tag_ptr<T: ?Sized>(ptr: *const T) -> *mut Tag {
    debug_assert!(!ptr.is_null(), "get_tag_ptr() is called on null");
    debug_assert_eq!(
        (ptr as *const () as usize) % 8,
        0,
        "get_tag_ptr() is called on unaligned pointer: {:p}",
        ptr
    );
    (ptr as *mut Tag).sub(1)
}

impl Tag {
    unsafe fn of<T: ?Sized>(ptr: *const T) -> Tag {
        *get_tag_ptr(ptr)
    }

    unsafe fn set<T: ?Sized>(ptr: *const T, tag: Tag) {
        *get_tag_ptr(ptr) = tag;
    }

    fn new(ty: *const DataType) -> Tag {
        Self { ty: ty }
    }

    fn moved_out<T>(ptr: *const T) -> Tag {
        Self {
            ty: ((ptr as usize) | 0x1) as *const DataType,
        }
    }

    fn get_type(&self) -> *const DataType {
        debug_assert!(
            !self.is_moved_out(),
            "Tag::get_type() is called on moved out tag"
        );
        self.ty as *const DataType
    }

    fn is_moved_out(&self) -> bool {
        (self.ty as usize) & 0x1 != 0x0
    }

    fn as_moved_out(&self) -> Option<AnyPtr> {
        let ty = self.ty as usize;
        if ty & 0x1 == 0x1 {
            Some((ty & !0x1) as AnyPtr)
        } else {
            None
        }
    }
}

/// `Block` is a thread-safe bump allocator.
struct Block {
    start: *mut u8,
    end: *mut u8,
    cur: AtomicPtr<u8>,
    allocation: MaybeUninit<region::Allocation>,
}

impl std::fmt::Debug for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let hex_conf = HexConfig {
            ascii: false,
            width: 32,
            group: 8,
            ..HexConfig::default()
        };
        write!(
            f,
            "Block@{:p} {:?}",
            self.start,
            self.as_slice().hex_conf(hex_conf)
        )
    }
}

unsafe impl Sync for Block {}

impl Block {
    const fn empty() -> Block {
        Block {
            start: std::ptr::null_mut(),
            cur: AtomicPtr::new(std::ptr::null_mut()),
            end: std::ptr::null_mut(),
            allocation: MaybeUninit::uninit(),
        }
    }

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

    /// Make memory block non-readable.
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

    fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.start, self.allocated_size()) }
    }

    fn allocated_size(&self) -> usize {
        unsafe { self.cur.load(Ordering::Relaxed).offset_from(self.start) as usize }
    }
}
impl Drop for Block {
    fn drop(&mut self) {
        if !self.start.is_null() {
            unsafe {
                std::ptr::drop_in_place(self.allocation.as_mut_ptr());
            }
        }
    }
}

fn align_to(size: usize, alignment: usize) -> usize {
    (size + alignment - 1) / alignment * alignment
}
fn align_size(size: usize) -> usize {
    const ALIGNMENT: usize = 8;
    align_to(size, ALIGNMENT)
}

#[tracing::instrument]
pub unsafe fn allocate(size: usize) -> *mut u8 {
    maybe_collect_garbage();
    let size = align_size(size);
    let start = TO.bump(TAG_SIZE + size);
    let start = start.unwrap_or_else(|| panic!("gc: out of memory"));
    let result = start.add(TAG_SIZE);
    trace!("allocting from:\n{:?}", backtrace::Backtrace::new());
    trace!("allocate({}) = {:#?}", size, result);
    result
}

/// Allocate permanent memory block. It is guaranteed to never be freed up by garbage collector.
pub unsafe fn allocate_perm(size: usize) -> *mut u8 {
    let start = alloc::alloc(alloc::Layout::from_size_align_unchecked(
        TAG_SIZE + size,
        16,
    ));
    std::slice::from_raw_parts_mut(start, TAG_SIZE + size).fill(0);
    start.add(TAG_SIZE)
}

pub unsafe fn maybe_collect_garbage() {
    // When gc_debug is enabled, collect garbage as often as possible to detect unrooted pointers.
    #[cfg(feature = "gc_debug")]
    collect_garbage();

    #[cfg(not(feature = "gc_debug"))]
    if TO.end.offset_from(TO.cur.load(Ordering::SeqCst)) < (GC_THRESHOLD as isize) {
        collect_garbage();
    }
}

#[tracing::instrument]
unsafe fn data_size(ptr: AnyPtr) -> usize {
    let size = (*ptr).size();
    let size = align_size(size);
    size
}

unsafe fn resolve_moved_out<T>(p: *const T) -> *const T {
    match Tag::of(p).as_moved_out() {
        Some(new_p) => new_p as *const T,
        None => p,
    }
}

#[tracing::instrument]
pub unsafe fn collect_garbage() {
    FROM = std::mem::replace(&mut TO, Block::new());
    trace!("collecting garbage from: {:?}", FROM);

    #[inline]
    fn debug_trace_blocks() {
        unsafe {
            trace!("  from: {:?}", FROM);
            trace!("  to:   {:?}", TO);
        }
    }

    {
        let span = tracing::trace_span!("tracing_roots");
        let _guard = span.enter();

        trace!("tracing roots");

        roots::visit_roots(|root, _meta| {
            let root = root.cast();
            trace!("tracing root: {:p}", root);
            if !trace_ptr(root) {
                trace_value(*root);
            }
        });
    }

    trace!("after roots");
    debug_trace_blocks();

    let mut cur = TO.start;
    while cur < TO.cur.load(Ordering::Relaxed) {
        cur = cur.add(8); // skip typetag

        let span = tracing::trace_span!("traverse_to", "{:p}", cur);
        let _guard = span.enter();

        let ty_ptr = get_tag_ptr(cur);
        trace_ptr((&mut (*ty_ptr).ty as *mut *const DataType).cast());
        trace_value(cur as AnyPtrMut);
        let size = data_size(cur as _);
        cur = cur.add(size);
    }

    trace!("after traverse");
    debug_trace_blocks();

    let before = FROM.allocated_size();
    let after = TO.allocated_size();
    let collected = before - after;
    info!(before, after, collected);

    FROM.protect();
}

/// Returns `false` if pointer wasn't traced (null or unmanaged);
#[tracing::instrument]
unsafe fn trace_ptr(ptr_loc: *mut AnyPtrMut) -> bool {
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

    // FROM.end is inclusive because ptr can be zero-sized object.
    if (ptr as *const u8) < FROM.start || (ptr as *const u8) > FROM.end {
        // Not in the from block — likely a permanent object.
        trace!("<- unmanaged");
        return false;
    }

    let tag = Tag::of(ptr);
    trace!("tag: {:?}", tag);

    *ptr_loc = match tag.as_moved_out() {
        Some(new) => {
            trace!("moved out: {:p} -> {:p}", ptr, new);
            new as *mut _
        }
        None => {
            // Check if the type of ptr has been moved out. Without this, we might calculate the
            // size incorrectly.
            let ty = resolve_moved_out(tag.get_type());
            let tag = Tag::new(ty);
            Tag::set(ptr, tag);

            let size = data_size(ptr);
            let new = TO.bump(TAG_SIZE + size).unwrap().add(TAG_SIZE) as AnyPtrMut;
            trace!(
                "copying: {:p} -> {:p} (tag={:?}, size={})",
                ptr,
                new,
                tag,
                size
            );

            Tag::set(new, tag);
            Tag::set(ptr, Tag::moved_out(new));

            std::ptr::copy_nonoverlapping(ptr as *const u8, new as *mut u8, size);
            new
        }
    };

    debug_assert!(
        (*ptr_loc as *const u8) > TO.start && (*ptr_loc as *const u8) <= TO.end,
        "{:p} should be inside the TO region: [{:p}, {:p}]",
        *ptr_loc,
        TO.start,
        TO.end
    );
    true
}

#[tracing::instrument]
unsafe fn trace_value(ptr: *mut AlphaValue) {
    if ptr.is_null() {
        return;
    }

    (*ptr).trace_pointers(trace_ptr);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gc_box;
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
            assert_eq!(type_of(s.load()), SVEC_T.load());
            assert_eq!((*s.load()).len(), 1);
        }
    }

    unsafe extern "C" fn nothing(_args: *const SVec) -> AnyPtr {
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
            assert_eq!(type_of(m.load()), METHOD_T.load());
            assert_eq!((*m.load()).signature, signature.load());
            assert!((*m.load()).instance == nothing, "instance does not match");
        }
    }

    #[test]
    #[serial]
    fn datatype_new() {
        crate::types::init();
        unsafe {
            let _ty = DataType::new(symbol("TestDataType"), ANY_T.load(), 0, &[]);
            gc_box!(_ty);
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

            DataType::add_method(ty.load_mut(), m.load());

            assert_eq!((*(*ty.load()).methods).len(), 1);

            println!("{:?}", ty.load());
            println!("{:?}", (*ty.load()).methods);
        }
    }

    #[test]
    #[serial]
    fn type_t() {
        crate::types::init();
        unsafe {
            let ty = DataType::new(symbol("TestDataType"), ANY_T.load(), 0, &[]);
            gc_box!(ty);
            let t = Type::new(ty.load().cast());
            gc_box!(t);
            collect_garbage();

            assert_eq!((*t.load()).t, ty.load().cast());
        }
    }

    #[test]
    #[serial]
    fn type_t_method() {
        crate::types::init();
        unsafe {
            let ty = DataType::new(symbol("TestDataType"), ANY_T.load(), 0, &[]);
            gc_box!(ty);
            let t = Type::new(ty.load().cast());
            gc_box!(t);
            collect_garbage();

            assert_eq!((*t.load()).t, ty.load().cast());

            let signature = SVec::push(SVEC_EMPTY.load(), t.load().cast());
            gc_box!(signature);
            let m = Method::new(signature.load(), nothing);
            gc_box!(m);
            collect_garbage();

            DataType::add_method(ty.load_mut(), m.load());

            let methods = (*ty.load()).methods;
            assert_eq!((*methods).len(), 1);
            let method = (*methods).elements()[0].cast::<Method>();
            assert_eq!(method, m.load());
            assert_eq!((*(*method).signature).elements()[0], t.load().cast());
            assert_eq!((*t.load()).t, ty.load().cast());
        }
    }
}
