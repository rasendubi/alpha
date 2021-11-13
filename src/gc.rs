use std::alloc;
use std::sync::atomic::{AtomicPtr, Ordering};

use log::trace;

pub struct GcBox<T> {
    ptr: AtomicPtr<T>,
}

impl<T> GcBox<T> {
    pub const fn new() -> GcBox<T> {
        GcBox {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
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

static mut BLOCK: Option<Block> = None;

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

const BLOCK_SIZE: usize = 4 * 1024;
const BLOCK_ALIGN: usize = 4 * 1024;

pub unsafe fn init() {
    // TODO: move this into allocate and protect with a global lock
    BLOCK = Some(Block::new(BLOCK_SIZE, BLOCK_ALIGN));
}

pub unsafe fn allocate(size: usize) -> *mut u8 {
    // TODO: handle alignment
    let start = BLOCK.as_mut().unwrap().bump(size + 8 /* typetag */);
    let start = start.unwrap_or_else(|| panic!("gc: out of memory"));
    let result = start.add(8 /* typetag */);
    trace!("allocate({}) = {:#?}", size, result);
    result
}
