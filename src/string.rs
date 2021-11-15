use crate::gc;
use crate::symbol::symbol;
use crate::types::*;

pub struct AlphaString {
    /// Length of the string in bytes, not counting the final NUL.
    len: usize,
    // follows directly after this struct:
    // bytes: [u8; len + 1], // NULL-terminated
}

impl AlphaString {
    pub fn new(s: &str) -> *const AlphaString {
        unsafe {
            let len = s.len();
            let this = Self::allocate_uninit(len);

            let bytes = (*this).bytes_mut();
            bytes[0..len].copy_from_slice(s.as_bytes());
            bytes[len] = 0;

            this
        }
    }

    /// # Safety
    ///
    /// `bytes` after returned string are initialized. They should be initialized and string
    /// converted to *const before it can be released to outside world.
    pub unsafe fn allocate_uninit(len: usize) -> *mut AlphaString {
        let this = gc::allocate(std::mem::size_of::<AlphaString>() + len + 1) as *mut AlphaString;
        set_typetag(this, STRING_T.load());
        *this = AlphaString { len };
        this
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn as_bytes(&self) -> &[u8] {
        let bytes = self.bytes();
        &bytes[0..bytes.len() - 1]
    }

    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }

    fn bytes(&self) -> &[u8] {
        unsafe {
            let len = self.len;
            let ptr = (self as *const Self).add(1) as *const u8;
            std::slice::from_raw_parts(ptr, len + 1)
        }
    }

    fn bytes_mut(&mut self) -> &mut [u8] {
        unsafe {
            let len = self.len;
            let ptr = (self as *mut Self).add(1) as *mut u8;
            std::slice::from_raw_parts_mut(ptr, len + 1)
        }
    }
}

impl AlphaValue for AlphaString {
    fn typetag() -> *const DataType {
        STRING_T.load()
    }
    fn datatype() -> DataType {
        DataType {
            name: symbol("String"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: 0, // dynamically-sized
            n_ptrs: 0,
            methods: SVEC_EMPTY.load(),
        }
    }
}

impl std::fmt::Debug for AlphaString {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.as_str().fmt(f)
        // write!(f, "{:?}", self.as_str())
    }
}

impl std::fmt::Display for AlphaString {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        self.as_str().fmt(f)
        // write!(f, "{}", self.as_str())
    }
}
