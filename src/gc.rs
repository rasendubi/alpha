use std::alloc;
use std::sync::atomic::{AtomicPtr, Ordering};

use log::trace;

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

    fn bump(&mut self, size: usize) -> Option<*mut u8> {
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
        let start = BLOCK.as_mut().unwrap().bump(size + 8 /* typetag */);
        let start = start.unwrap_or_else(|| panic!("gc: out of memory"));
        let result = start.add(8 /* typetag */);
        trace!("allocate({}) = {:#?}", size, result);
        result
}
