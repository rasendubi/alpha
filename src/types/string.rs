use crate::gc;
use crate::symbol;
use crate::types::*;

#[repr(C)]
pub struct AlphaString {
    /// Length of the string in bytes, not counting the final NUL.
    len: usize,
    /// Dynamically-sized and NULL terminated. Actual type is [u8; len + 1]
    bytes: [u8; 0],
}

impl AlphaString {
    /// # Safety
    ///
    /// This function allocates GC memory. Therefore all GC values must be rooted before calling
    /// this function.
    pub unsafe fn new(s: &str) -> *const AlphaString {
        let len = s.len();
        let this = Self::allocate_uninit(len);

        let bytes = (*this).bytes_mut();
        bytes[0..len].copy_from_slice(s.as_bytes());
        bytes[len] = 0;

        this
    }

    /// # Safety
    ///
    /// `bytes` after returned string are initialized. They should be initialized and string
    /// converted to *const before it can be released to outside world.
    unsafe fn allocate_uninit(len: usize) -> *mut AlphaString {
        let this = gc::allocate(std::mem::size_of::<AlphaString>() + len + 1) as *mut AlphaString;
        set_type(this, STRING_T.load());
        *this = AlphaString { len, bytes: [] };
        this
    }

    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Access the underlying bytes *without* the NUL-terminator.
    pub fn as_bytes(&self) -> &[u8] {
        let bytes = self.bytes();
        &bytes[0..bytes.len() - 1]
    }

    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// The underlying bytes *with* the NUL-terminator.
    fn bytes(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.bytes.as_ptr(), self.len + 1) }
    }

    fn bytes_mut(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.bytes.as_mut_ptr(), self.len + 1) }
    }
}

impl AlphaType for AlphaString {
    fn typetag() -> *const DataType {
        STRING_T.load()
    }
    fn datatype() -> DataType {
        DataType {
            name: symbol("String"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: usize::MAX, // dynamically-sized
            n_ptrs: 0,
            methods: SVEC_EMPTY.load(),
            pointers: [],
        }
    }
}
impl AlphaDataType for AlphaString {
    fn size(&self) -> usize {
        std::mem::size_of::<AlphaString>() + self.len + 1
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
