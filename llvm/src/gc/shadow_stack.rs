//! Integration for LLVM's shadow-stack GC strategy.
//!
//! See <https://llvm.org/docs/GarbageCollection.html#the-shadow-stack-gc> for more information.
use std::slice;

#[derive(Debug)]
#[repr(C)]
pub struct FrameMap<const N: usize> {
    /// Number of roots in associated [`StackEntry`].
    pub num_roots: u32,
    /// Number of metadata entries in `meta`.
    pub num_meta: u32,
    /// Metadata for each root.
    ///
    /// Note that this can be variably-sized.
    pub meta: [*const u8; N],
}

#[derive(Debug)]
#[repr(C)]
pub struct StackEntry<const N: usize> {
    /// Link to next stack entry.
    pub next: *mut StackEntry<0>,
    /// [`FrameMap`] for this stack entry.
    // TODO: NonNull?
    pub map: *const FrameMap<0>,
    /// Stack roots (in-place array).
    ///
    /// Note that this can be variably-sized. The actual number of roots is stored at
    /// `(*map).num_roots`.
    pub roots: [*const u8; N],
}

/// The head of the singly-linked list of StackEntry.
pub type GcRootChain = *mut StackEntry<0>;

/// Push a `frame` to [`GcRootChain`].
///
/// This should be accompanied with the appropriate [`pop_gcframe`].
#[inline(always)]
pub unsafe fn push_gcframe(root: &mut GcRootChain, frame: *mut StackEntry<0>) {
    *root = frame;
}

/// Pops the last gc frame.
///
/// Additionally in debug build, checks that it matches the specified frame. This detects
/// out-of-order frames pops.
///
/// For unchecked version, see [`pop_gcframe_unchecked()`].
#[inline(always)]
pub unsafe fn pop_gcframe(root: &mut GcRootChain, frame: *mut StackEntry<0>) {
    debug_assert!(!root.is_null());
    debug_assert_eq!(*root, frame);
    pop_gcframe_unchecked(root);
}

/// Pops the last gc frame.
#[inline(always)]
pub unsafe fn pop_gcframe_unchecked(root: &mut GcRootChain) {
    *root = (**root).next;
}

/// Call `visitor` for every root in [`GcRootChain`].
///
/// The first argument of the visitor is the root, the second argument is constant metadata (can be
/// null).
pub unsafe fn visit_roots<Visitor>(root: GcRootChain, mut visitor: Visitor)
where
    Visitor: FnMut(*mut *const u8, *const u8),
{
    let mut entry = root;
    while !entry.is_null() {
        let roots = (*entry).roots();
        let metas = (*(*entry).map).metas();

        for (i, root) in roots.iter_mut().enumerate() {
            visitor(root, metas.get(i).copied().unwrap_or(std::ptr::null()));
        }

        entry = (*entry).next;
    }
}

impl<const N: usize> FrameMap<N> {
    #[inline]
    pub const fn new(num_roots: u32, meta: [*const u8; N]) -> FrameMap<N> {
        Self {
            num_roots,
            num_meta: N as u32,
            meta,
        }
    }

    #[inline]
    pub const fn as_unsized(this: *const Self) -> *const FrameMap<0> {
        this.cast()
    }

    pub fn metas(&self) -> &[*const u8] {
        unsafe { slice::from_raw_parts(self.meta.as_ptr(), self.num_meta as usize) }
    }
}

impl<const N: usize> StackEntry<N> {
    #[inline]
    pub const unsafe fn new<const M: usize>(
        next: *mut StackEntry<0>,
        map: *const FrameMap<M>,
        roots: [*const u8; N],
    ) -> Self {
        Self {
            next,
            map: FrameMap::as_unsized(map),
            roots,
        }
    }

    #[inline]
    pub const fn as_unsized(this: *const Self) -> *const StackEntry<0> {
        this.cast()
    }

    pub fn roots(&mut self) -> &mut [*const u8] {
        unsafe {
            let num_roots = (*self.map).num_roots;
            let roots = slice::from_raw_parts_mut(self.roots.as_mut_ptr(), num_roots as usize);
            roots
        }
    }
}
