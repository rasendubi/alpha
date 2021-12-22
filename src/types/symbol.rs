use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::ffi::CStr;
use std::hash::{Hash, Hasher};
use std::mem::size_of;
use std::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};
use std::sync::Mutex;

use once_cell::sync::Lazy;
use tracing::trace;

use crate::gc;
use crate::types::*;

/// `SYMBOLS_MUTEX` protects [`SYMBOLS_ROOT`] for writes.
static SYMBOLS_MUTEX: Lazy<Mutex<()>> = Lazy::new(|| Mutex::new(()));
// SYMBOLS_ROOT is not gc_global because all symbols are perm-allocated. GC does not need to
// traverse it.
static SYMBOLS_ROOT: AtomicPtr<SymbolNode> = AtomicPtr::new(std::ptr::null_mut());

// TODO: this whole module is probably not safe when GC kicks in. Symbol captures SymbolNode by
// reference, however GC is allowed to relocate the SymbolNode making the reference invalid.
//
// One of the possible workaround is to allocate symbols in the permanent heap, so they are never
// re-allocated.
/// Return a [`Symbol`] associated with `name`.
pub fn symbol(name: &str) -> Symbol {
    let node = {
        let res = SymbolNode::search(&SYMBOLS_ROOT, name);
        match res {
            Ok(node) => node.load(AtomicOrdering::SeqCst),
            Err(_place) => {
                let _lock = SYMBOLS_MUTEX.lock().unwrap();
                // We call search again because someone might have modified the tree between
                // previous search and now.
                let res = SymbolNode::search(&SYMBOLS_ROOT, name);
                match res {
                    Ok(node) => node.load(AtomicOrdering::SeqCst),
                    Err(place) => {
                        trace!("allocating symbol: {}", name);
                        let node = SymbolNode::allocate(name);
                        place.store(node as *mut _, AtomicOrdering::SeqCst);
                        node
                    }
                }
            }
        }
    };

    Symbol::new(node)
}

#[allow(unused)] // might be useful to debugging
fn dump_symbols() {
    fn dump(level: usize, node: *const SymbolNode) {
        if node.is_null() {
            return;
        }
        let node = unsafe { &*node };
        eprintln!(
            "{:indent$}{} ({:x})",
            "",
            node.name(),
            node.hash,
            indent = level * 2
        );
        dump(level + 1, node.left.load(AtomicOrdering::SeqCst));
        dump(level + 1, node.right.load(AtomicOrdering::SeqCst));
    }

    dump(0, SYMBOLS_ROOT.load(AtomicOrdering::SeqCst))
}

#[derive(Clone, Copy, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Symbol {
    pub(crate) node: *const SymbolNode,
}

impl Symbol {
    fn new(node: *const SymbolNode) -> Self {
        assert_ne!(node, std::ptr::null(), "Symbol::new: node is null");
        Symbol { node }
    }

    pub fn as_str(&self) -> &str {
        assert_ne!(self.node, std::ptr::null());
        unsafe { (*self.node).as_str() }
    }

    #[allow(dead_code)]
    pub fn as_cstr(&self) -> &CStr {
        unsafe { (*self.node).as_cstr() }
    }

    pub fn as_anyptr(&self) -> AnyPtr {
        self.node.cast()
    }
}

impl PartialEq<Symbol> for Symbol {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.node, other.node)
    }
}

impl Eq for Symbol {}

impl Hash for Symbol {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: std::hash::Hasher,
    {
        unsafe {
            hasher.write_u64((*self.node).hash);
        }
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        assert_ne!(self as *const Self, std::ptr::null());
        assert_ne!(self.node, std::ptr::null(), "Symbol.node is null");
        if self.node.is_null() {
            Ok(())
        } else {
            write!(f, "#{}", self)
        }
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        assert_ne!(self as *const Self, std::ptr::null());
        assert_ne!(self.node, std::ptr::null(), "Symbol.node is null");
        write!(f, "{}", self.as_str())
    }
}

#[repr(C)]
pub struct SymbolNode {
    hash: u64,
    left: AtomicPtr<SymbolNode>,
    right: AtomicPtr<SymbolNode>,
    len: usize,
    /// Dynamically-sized and NUL-terminated. Actual type is [u8; len + 1].
    name: [u8; 0],
}

impl std::fmt::Debug for SymbolNode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        assert_ne!(self as *const Self, std::ptr::null());
        f.debug_struct("SymbolNode")
            .field("hash", &self.hash)
            .field("left", &self.left)
            .field("right", &self.right)
            .field("name", &self.name())
            .finish()
    }
}

impl std::fmt::Display for SymbolNode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        assert_ne!(self as *const Self, std::ptr::null());
        write!(f, "{}", self.as_str())
    }
}

impl SymbolNode {
    fn as_str(&self) -> &str {
        self.name()
    }

    fn as_cstr(&self) -> &CStr {
        unsafe {
            let slice = std::slice::from_raw_parts(self.name.as_ptr(), self.len + 1);
            CStr::from_bytes_with_nul_unchecked(slice)
        }
    }

    /// Allocate a new SymbolNode and assign `s` as its value.
    fn allocate(s: &str) -> *const SymbolNode {
        unsafe {
            let size = s.len();
            let ptr = gc::allocate_perm(size_of::<SymbolNode>() + size + 1) as *mut SymbolNode;
            set_type(ptr, SYMBOL_T.load());
            let hash = Self::str_hash(s);
            *ptr = SymbolNode {
                hash,
                left: AtomicPtr::new(std::ptr::null_mut()),
                right: AtomicPtr::new(std::ptr::null_mut()),
                len: size,
                name: [],
            };

            let name_slice = std::slice::from_raw_parts_mut((*ptr).name.as_mut_ptr(), size + 1);
            name_slice[0..size].copy_from_slice(s.as_bytes());
            name_slice[size] = 0;

            &*ptr
        }
    }

    fn str_hash(s: &str) -> u64 {
        let mut h = DefaultHasher::new();
        (*s).hash(&mut h);
        let result = h.finish();
        result
    }

    /// Search for the string `s` at root `node`.
    ///
    /// If symbol `s` is found, return it as `Ok()` node. If symbol is not found, returns the
    /// insertion place as `Err()` node.
    fn search<'a, 'b>(
        node: &'a AtomicPtr<SymbolNode>,
        s: &'b str,
    ) -> Result<&'a AtomicPtr<SymbolNode>, &'a AtomicPtr<SymbolNode>> {
        Self::search_with_hash(node, Self::str_hash(s), s)
    }

    // TODO: TCO is not guaranteed by Rust. It might be a good idea to rewrite this function as a
    // loop instead.
    fn search_with_hash<'a, 'b>(
        node: &'a AtomicPtr<SymbolNode>,
        hash: u64,
        s: &'b str,
    ) -> Result<&'a AtomicPtr<SymbolNode>, &'a AtomicPtr<SymbolNode>> {
        let this = node.load(AtomicOrdering::SeqCst);
        if this.is_null() {
            return Err(node);
        }

        let this = unsafe { &*this };

        if hash < this.hash {
            return Self::search_with_hash(&this.left, hash, s);
        } else if hash > this.hash {
            return Self::search_with_hash(&this.right, hash, s);
        }

        // hash is equal, compare strings
        let name = this.name();
        let ord = s.cmp(name);
        if ord == Ordering::Less {
            return Self::search_with_hash(&this.left, hash, s);
        } else if ord == Ordering::Greater {
            return Self::search_with_hash(&this.right, hash, s);
        }

        // hash and string are equal
        Ok(node)
    }

    fn name(&self) -> &str {
        unsafe {
            let slice = std::slice::from_raw_parts(self.name.as_ptr(), self.len);
            std::str::from_utf8_unchecked(slice)
        }
    }
}

impl AlphaType for SymbolNode {
    fn typetag() -> *const DataType {
        SYMBOL_T.load()
    }
    fn datatype() -> DataType {
        DataType {
            name: symbol("Symbol"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: usize::MAX, // dynamically-sized
            n_ptrs: 0,
            methods: SVEC_EMPTY.load(),
            pointers: [],
        }
    }
    fn pointers() -> &'static [usize] {
        static PTRS: [usize; 2] = [
            // TODO: very unsafe. Use offset_from() when it becomes const
            1 * 8, // left
            2 * 8, // right
        ];
        &PTRS
    }
}
impl AlphaDataType for SymbolNode {
    fn size(&self) -> usize {
        size_of::<Self>() + self.len + 1
    }

    fn trace_pointers(&mut self, _trace_ptr: unsafe fn(*mut AnyPtrMut) -> bool) {
        // All symbols are perm-allocated, so they do not need to be traced.
        // unsafe {
        //     // TODO: remove transmute
        //     trace_ptr(std::mem::transmute(&mut (*this).left));
        //     trace_ptr(std::mem::transmute(&mut (*this).right));
        // }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_node_allocate() {
        unsafe {
            let s = SymbolNode::allocate("hello");
            assert_eq!((&*s).name(), "hello");
        }
    }

    #[test]
    fn test_symbol_node_cstr() {
        unsafe {
            let s = SymbolNode::allocate("hello");
            assert_eq!((&*s).as_cstr().to_str().unwrap(), "hello");
        }
    }

    #[test]
    fn test_symbol_search_null_root() {
        let root = AtomicPtr::new(std::ptr::null_mut());
        let result = SymbolNode::search(&root, "hello");
        assert!(result.is_err());
        assert!(std::ptr::eq(result.err().unwrap(), &root));
    }

    #[test]
    fn test_symbol_new_equal() {
        let a = symbol("hello");
        let b = symbol("hello");
        assert_eq!(a, b);
    }

    #[test]
    fn test_symbol_new_different() {
        let a = symbol("hello");
        let b = symbol("other");
        assert_ne!(a, b);
    }

    #[test]
    fn test_symbol_to_string() {
        let a = symbol("hello").to_string();
        assert_eq!(a, "hello");
    }
}
