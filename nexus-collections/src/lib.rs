//! Feature-gated collections for low-latency systems.
//!
//! Enable feature families in `Cargo.toml` to unlock the corresponding types:
//!
//! ```toml
//! nexus-collections = { version = "2.0", features = ["slab"] }
//! ```
//!
//! # Feature families
//!
//! | Feature | Types |
//! |---------|-------|
//! | `slab`  | [`slab::List`], [`slab::Heap`], [`slab::BTree`], [`slab::RbTree`] |

#![warn(missing_docs)]

#[cfg(feature = "slab")]
mod btree;
#[cfg(feature = "slab")]
mod compare;
#[cfg(feature = "slab")]
mod heap;
#[cfg(feature = "slab")]
mod list;
#[cfg(feature = "slab")]
mod rbtree;

#[cfg(feature = "slab")]
use std::cell::Cell;

#[cfg(feature = "slab")]
mod sealed {
    pub trait RcSealed {}
    pub trait SlabSealed {}

    impl<T> RcSealed for nexus_slab::rc::bounded::Slab<T> {}
    impl<T> RcSealed for nexus_slab::rc::unbounded::Slab<T> {}
    impl<T> SlabSealed for nexus_slab::bounded::Slab<T> {}
    impl<T> SlabSealed for nexus_slab::unbounded::Slab<T> {}
}

/// Sealed trait for Rc slab types that can free an [`RcSlot`](nexus_slab::rc::RcSlot) handle.
///
/// Implemented by `rc::bounded::Slab<T>` and `rc::unbounded::Slab<T>`.
/// Used by [`slab::List`] and [`slab::Heap`] for `unlink` and `clear`.
///
/// This trait is sealed — it cannot be implemented outside this crate.
#[cfg(feature = "slab")]
pub trait RcFree<T>: sealed::RcSealed {
    /// Free a handle, decrementing the refcount.
    fn free_rc(&self, handle: nexus_slab::rc::RcSlot<T>);
}

#[cfg(feature = "slab")]
impl<T> RcFree<T> for nexus_slab::rc::bounded::Slab<T> {
    #[inline]
    fn free_rc(&self, handle: nexus_slab::rc::RcSlot<T>) {
        self.free(handle);
    }
}

#[cfg(feature = "slab")]
impl<T> RcFree<T> for nexus_slab::rc::unbounded::Slab<T> {
    #[inline]
    fn free_rc(&self, handle: nexus_slab::rc::RcSlot<T>) {
        self.free(handle);
    }
}

/// Sealed trait for raw slab operations.
///
/// Implemented by `bounded::Slab<T>` and `unbounded::Slab<T>`.
/// Used by tree collections for `remove`, `clear`, cursor, entry, and drain.
///
/// This trait is sealed — it cannot be implemented outside this crate.
#[cfg(feature = "slab")]
pub trait SlabOps<T>: sealed::SlabSealed {
    /// Free a slot, dropping the value and returning storage to the freelist.
    fn free_slot(&self, slot: nexus_slab::Slot<T>);
    /// Take the value out of a slot, then free the storage.
    fn take_slot(&self, slot: nexus_slab::Slot<T>) -> T;
    /// Returns true if the pointer falls within this slab's storage.
    fn contains_ptr(&self, ptr: *const ()) -> bool;
}

#[cfg(feature = "slab")]
impl<T> SlabOps<T> for nexus_slab::bounded::Slab<T> {
    #[inline]
    fn free_slot(&self, slot: nexus_slab::Slot<T>) {
        self.free(slot);
    }
    #[inline]
    fn take_slot(&self, slot: nexus_slab::Slot<T>) -> T {
        self.take(slot)
    }
    #[inline]
    fn contains_ptr(&self, ptr: *const ()) -> bool {
        self.contains_ptr(ptr)
    }
}

#[cfg(feature = "slab")]
impl<T> SlabOps<T> for nexus_slab::unbounded::Slab<T> {
    #[inline]
    fn free_slot(&self, slot: nexus_slab::Slot<T>) {
        self.free(slot);
    }
    #[inline]
    fn take_slot(&self, slot: nexus_slab::Slot<T>) -> T {
        self.take(slot)
    }
    #[inline]
    fn contains_ptr(&self, ptr: *const ()) -> bool {
        self.contains_ptr(ptr)
    }
}

#[cfg(feature = "slab")]
thread_local! {
    static NEXT_COLLECTION_ID: Cell<usize> = const { Cell::new(1) };
}

#[cfg(feature = "slab")]
fn next_collection_id() -> usize {
    NEXT_COLLECTION_ID.with(|c| {
        let id = c.get();
        let next = id.wrapping_add(1);
        c.set(if next == 0 { 1 } else { next });
        id
    })
}

/// Slab-backed intrusive collections.
///
/// Requires the `slab` feature:
///
/// ```toml
/// nexus-collections = { version = "2.0", features = ["slab"] }
/// ```
///
/// # Primary types
///
/// - [`List`](slab::List) — doubly-linked list with `RcSlot` handles
/// - [`Heap`](slab::Heap) — pairing heap with `RcSlot` handles
/// - [`BTree`](slab::BTree) — B-tree sorted map with cache-friendly node layout
/// - [`RbTree`](slab::RbTree) — red-black tree sorted map with O(log n) worst case
#[cfg(feature = "slab")]
pub mod slab {
    pub use crate::compare::{Compare, Natural, Reverse};
    pub use crate::{RcFree, SlabOps};
    pub use nexus_slab::rc::{RcSlot, Ref, RefMut};
    pub use nexus_slab::shared::Full;

    pub use crate::btree::{BTree, BTreeNode};
    pub use crate::heap::{Heap, HeapNode};
    pub use crate::list::{List, ListNode};
    pub use crate::rbtree::{RbNode, RbTree};

    /// Sub-modules expose associated types (iterators, cursors, entries).
    pub mod btree {
        pub use crate::btree::*;
    }
    /// Sub-modules expose associated types (iterators, cursors, entries).
    pub mod heap {
        pub use crate::heap::*;
    }
    /// Sub-modules expose associated types (iterators, cursors, entries).
    pub mod list {
        pub use crate::list::*;
    }
    /// Sub-modules expose associated types (iterators, cursors, entries).
    pub mod rbtree {
        pub use crate::rbtree::*;
    }
    /// Comparison traits and built-in comparators.
    pub mod compare {
        pub use crate::compare::*;
    }
}
