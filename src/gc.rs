use std::alloc;
use std::sync::atomic::{AtomicPtr, Ordering};

use log::trace;

#[macro_export]
macro_rules! gc_global {
    ( pub $i:ident : $t:ty ) => {
        pub static $i: $crate::gc::GcBox<$t> = $crate::gc::GcBox::new();
        paste::paste! {
            #[used]
            #[ctor::ctor]
            static [<$i _ROOT>]: $crate::gc::GcRoot<'static> = $crate::gc::GcRoot::new(&$i);
        }
    };
    ( $i:ident : $t:ty ) => {
        static $i: $crate::gc::GcBox<$t> = $crate::gc::GcBox::new();
        paste::paste! {
            #[used]
            #[ctor::ctor]
            static [<$i _ROOT>]: $crate::gc::GcRoot<'static> = $crate::gc::GcRoot::new(&$i);
        }
    };
}

#[derive(Debug)]
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
pub struct GcRoot<'a> {
    ptr: &'a AtomicPtr<()>,
}

unsafe impl<'a> Sync for GcRoot<'a> {}

impl<'a> GcRoot<'a> {
    pub fn new<T>(b: &'a GcBox<T>) -> Self {
        trace!("New gc root at: {:p}", b);
        GcRoot {
            ptr: unsafe {
                // cast &'a AtomicPtr<T> to &'a AtomicPtr<()>
                std::mem::transmute(&b.ptr)
            },
        }
    }
}

#[ctor::ctor]
static BLOCK: Block = Block::new(BLOCK_SIZE, BLOCK_ALIGN);

struct Block {
    // required to deallocate the block later
    #[allow(dead_code)]
    start: *mut u8,
    end: *mut u8,
    cur: AtomicPtr<u8>,
}

unsafe impl Sync for Block {}

impl Block {
    fn new(size: usize, align: usize) -> Block {
        unsafe {
            let block = alloc::alloc(alloc::Layout::from_size_align_unchecked(size, align));
            Block {
                start: block,
                end: block.add(size),
                cur: AtomicPtr::new(block),
            }
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

const BLOCK_SIZE: usize = 1024 * 4 * 1024;
const BLOCK_ALIGN: usize = 4 * 1024;

pub unsafe fn allocate(size: usize) -> *mut u8 {
    // TODO: handle alignment
    let start = BLOCK.bump(size + 8 /* typetag */);
    let start = start.unwrap_or_else(|| panic!("gc: out of memory"));
    let result = start.add(8 /* typetag */);
    trace!("allocate({}) = {:#?}", size, result);
    result
}
