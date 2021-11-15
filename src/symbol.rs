use crate::types::AlphaValue;
use crate::types::DataType;
use crate::types::ANY_T;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::ffi::CStr;
use std::hash::{Hash, Hasher};
use std::mem::size_of;
use std::sync::Mutex;

use log::trace;

use crate::gc;
use crate::gc::GcBox;
use crate::gc_global;
use crate::types::{set_typetag, AnyPtr, SYMBOL_T};

#[ctor::ctor]
static SYMBOLS_MUTEX: Mutex<()> = Mutex::new(());
gc_global!(SYMBOLS_ROOT: SymbolNode);

// TODO: this whole module is probably not safe when GC kicks in. Symbol captures SymbolNode by
// reference, however GC is allowed to relocate the SymbolNode making the reference invalid.
//
// One of the possible workaround is to allocate symbols in the permanent heap, so they are never
// re-allocated.
pub fn symbol(s: &str) -> Symbol {
    let node = unsafe {
        let res = SymbolNode::search(&SYMBOLS_ROOT, s);
        match res {
            Ok(node) => &*node.load(),
            Err(_place) => {
                let _lock = SYMBOLS_MUTEX.lock().unwrap();
                // We call search again because someone might have modified the tree between
                // previous search and now.
                let res = SymbolNode::search(&SYMBOLS_ROOT, s);
                match res {
                    Ok(node) => &*node.load(),
                    Err(place) => {
                        trace!("allocating symbol: {}", s);
                        let node = SymbolNode::allocate(s);
                        place.store(node as *mut _);
                        &*node
                    }
                }
            }
        }
    };

    Symbol { node }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Symbol {
    node: &'static SymbolNode,
}

impl Symbol {
    pub fn as_str(&self) -> &str {
        self.node.as_str()
    }

    #[allow(dead_code)]
    pub fn as_cstr(&self) -> &CStr {
        self.node.as_cstr()
    }

    pub fn as_anyptr(&self) -> AnyPtr {
        self.node as *const SymbolNode as AnyPtr
    }
}

impl AlphaValue for Symbol {
    fn typetag() -> *const DataType {
        SYMBOL_T.load()
    }

    fn datatype() -> DataType {
        DataType {
            name: symbol("Symbol"),
            supertype: ANY_T.load(),
            is_abstract: false,
            size: 0, // dynamically-sized
            n_ptrs: 0,
            methods: Vec::new(),
        }
    }

    fn as_anyptr(&self) -> *const u64 {
        (self as &Symbol).as_anyptr()
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
        hasher.write_u64(self.node.hash);
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "#{}", self)
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Debug)]
pub struct SymbolNode {
    hash: u64,
    left: GcBox<SymbolNode>,
    right: GcBox<SymbolNode>,
    len: usize,
    // follows directly after this struct:
    // name: [u8; len + 1], // NULL-terminated
}

impl SymbolNode {
    fn as_str(&self) -> &str {
        self.name()
    }

    fn as_cstr(&self) -> &CStr {
        unsafe {
            let slice = std::slice::from_raw_parts(self.name_ptr(), self.len + 1);
            CStr::from_bytes_with_nul_unchecked(slice)
        }
    }

    /// Allocate a new SymbolNode and assign `s` as its value.
    fn allocate(s: &str) -> *const SymbolNode {
        unsafe {
            let size = s.len();
            let ptr = gc::allocate(size_of::<SymbolNode>() + size + 1) as *mut SymbolNode;
            set_typetag(ptr, SYMBOL_T.load());
            let hash = Self::str_hash(s);
            *ptr = SymbolNode {
                hash,
                left: GcBox::new(),
                right: GcBox::new(),
                len: size,
            };

            let name_slice = std::slice::from_raw_parts_mut(ptr.add(1) as *mut u8, size + 1);
            name_slice[0..size].copy_from_slice(s.as_bytes());
            name_slice[size] = 0;

            &*ptr
        }
    }

    fn str_hash(s: &str) -> u64 {
        let mut h = DefaultHasher::new();
        s.hash(&mut h);
        h.finish()
    }

    /// Search for the string `s` at root `node`.
    ///
    /// If symbol `s` is found, return it as `Ok()` node. If symbol is not found, returns the
    /// insertion place as `Err()` node.
    fn search<'a, 'b>(
        node: &'a GcBox<SymbolNode>,
        s: &'b str,
    ) -> Result<&'a GcBox<SymbolNode>, &'a GcBox<SymbolNode>> {
        Self::search_with_hash(node, Self::str_hash(s), s)
    }

    // TODO: TCO is not guaranteed by Rust. It might be a good idea to rewrite this function as a
    // loop instead.
    fn search_with_hash<'a, 'b>(
        node: &'a GcBox<SymbolNode>,
        hash: u64,
        s: &'b str,
    ) -> Result<&'a GcBox<SymbolNode>, &'a GcBox<SymbolNode>> {
        let this = node.load();
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

    fn name_ptr(&self) -> *const u8 {
        unsafe { (self as *const SymbolNode).add(1) as *const u8 }
    }

    fn name(&self) -> &str {
        unsafe {
            let slice = std::slice::from_raw_parts(self.name_ptr(), self.len);
            std::str::from_utf8_unchecked(slice)
        }
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
        let root = GcBox::new();
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
