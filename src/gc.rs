use std::alloc;

pub struct Gc {
    #[allow(unused)]
    start: *mut u8,
    end: *mut u8,
    cur: *mut u8,
}

const BLOCK_SIZE: usize = 4 * 1024;
const BLOCK_ALIGN: usize = 4 * 1024;

impl Gc {
    pub const unsafe fn new_uninit() -> Self {
        Gc {
            start: std::ptr::null_mut(),
            end: std::ptr::null_mut(),
            cur: std::ptr::null_mut(),
        }
    }

    pub unsafe fn init(&mut self) {
        let block = alloc::alloc(alloc::Layout::from_size_align_unchecked(
            BLOCK_SIZE,
            BLOCK_ALIGN,
        ));
        *self = Gc {
            start: block,
            end: block.add(BLOCK_SIZE),
            cur: block,
        };
    }

    #[allow(unused)]
    pub fn new() -> Self {
        unsafe {
            let mut me = Gc::new_uninit();
            me.init();
            me
        }
    }

    pub fn allocate(&mut self, size: usize) -> *mut u8 {
        unsafe {
            let result = self.cur.add(8); // typetag

            let next = result.add(size);
            if next > self.end {
                panic!("gc: out of memory");
            } else {
                self.cur = next;
                println!("allocate({}) = {:#?}", size, result);
                result
            }
        }
    }
}
