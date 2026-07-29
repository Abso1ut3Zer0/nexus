//! Min-heap (pairing heap) with `RcSlot`-based stable handles.
//!
//! # Design
//!
//! A pairing heap — each node stores parent, leftmost-child, and sibling
//! pointers. This gives O(1) push, O(log n) amortized pop.
//! Two-pass pairing merge for optimal amortized bounds.
//!
//! # Ownership Model
//!
//! Same as [`List`](crate::list::List):
//! - User holds `RcSlot<HeapNode<T>>` — their ownership token + data access
//! - Heap stores raw pointers and maintains its own strong reference per node
//! - Every heap-linked node has `refcount >= 2` (user + heap)
//! - Pop transfers the heap's ref to the caller (no net refcount change)
//!
//! # Immutable Data
//!
//! Heap node data is immutable once created. To change priority, unlink
//! the old node and push a new one.

use std::cell::Cell;
use std::ptr;

use nexus_slab::rc::bounded::Slab as RcBoundedSlab;
use nexus_slab::rc::unbounded::Slab as RcUnboundedSlab;
use nexus_slab::rc::{RcCell, RcSlot};
use nexus_slab::shared::Full;

use crate::RcFree;

use crate::next_collection_id;

// =============================================================================
// NodePtr
// =============================================================================

/// Raw pointer to a slab-allocated heap node.
type NodePtr<T> = *mut RcCell<HeapNode<T>>;

// =============================================================================
// HeapNode<T>
// =============================================================================

/// A node in a pairing heap.
pub struct HeapNode<T> {
    parent: Cell<NodePtr<T>>,
    child: Cell<NodePtr<T>>,
    next: Cell<NodePtr<T>>,
    prev: Cell<NodePtr<T>>,
    owner: Cell<usize>,
    /// The user's data.
    pub value: T,
}

impl<T> HeapNode<T> {
    /// Creates a new detached node wrapping the given value.
    pub fn new(value: T) -> Self {
        HeapNode {
            parent: Cell::new(ptr::null_mut()),
            child: Cell::new(ptr::null_mut()),
            next: Cell::new(ptr::null_mut()),
            prev: Cell::new(ptr::null_mut()),
            owner: Cell::new(0),
            value,
        }
    }

    /// Returns `true` if this node is linked to a heap.
    pub fn is_linked(&self) -> bool {
        self.owner.get() != 0
    }

    /// Returns a reference to the user data.
    pub fn value(&self) -> &T {
        &self.value
    }

    /// Consumes the node, returning the user data.
    #[doc(hidden)]
    pub fn into_value(self) -> T {
        self.value
    }

    fn parent_ptr(&self) -> NodePtr<T> {
        self.parent.get()
    }
    fn child_ptr(&self) -> NodePtr<T> {
        self.child.get()
    }
    fn next_ptr(&self) -> NodePtr<T> {
        self.next.get()
    }
    fn prev_ptr(&self) -> NodePtr<T> {
        self.prev.get()
    }
    fn set_parent(&self, ptr: NodePtr<T>) {
        self.parent.set(ptr);
    }
    fn set_child(&self, ptr: NodePtr<T>) {
        self.child.set(ptr);
    }
    fn set_next(&self, ptr: NodePtr<T>) {
        self.next.set(ptr);
    }
    fn set_prev(&self, ptr: NodePtr<T>) {
        self.prev.set(ptr);
    }
    fn owner_id(&self) -> usize {
        self.owner.get()
    }
    fn set_owner(&self, id: usize) {
        self.owner.set(id);
    }
}

// =============================================================================
// node_deref
// =============================================================================

/// Dereferences a `NodePtr<T>` to get `&HeapNode<T>`.
///
/// Returns a reference with an unbounded lifetime. The caller is responsible
/// for ensuring the reference does not outlive the slot's allocation.
///
/// # Safety
///
/// `ptr` must be non-null and point to an occupied `RcCell` with refcount > 0.
#[inline(always)]
unsafe fn node_deref<'a, T>(ptr: NodePtr<T>) -> &'a HeapNode<T> {
    // SAFETY: RcCell::value_ptr() returns *mut T.
    // The Cell-based fields support interior mutability through &self,
    // so shared access is sound.
    unsafe { &*(*ptr).value_ptr().cast_const() }
}

// =============================================================================
// Cold panic helpers
// =============================================================================

#[cold]
#[inline(never)]
fn panic_wrong_heap() -> ! {
    panic!("node is not linked to this heap")
}

#[cold]
#[inline(never)]
fn panic_already_linked() -> ! {
    panic!("node is already linked to a collection")
}

// =============================================================================
// Refcount helpers
// =============================================================================

/// Increments the refcount for the collection's reference.
///
/// Clones the handle (refcount +1) and forgets the clone so the collection
/// holds a strong ref without storing the handle. The matching decrement
/// happens in pop/unlink/clear via `RcSlot::from_raw`.
#[inline]
fn inc_strong<T>(handle: &RcSlot<HeapNode<T>>) {
    let clone = handle.clone();
    core::mem::forget(clone);
}

// =============================================================================
// link — merge two heap roots
// =============================================================================

/// Merges two heap roots. The smaller-valued root becomes the winner,
/// and the loser is added as a child of the winner.
///
/// # Safety
///
/// Both `a` and `b` must be non-null, valid heap node pointers with
/// refcount > 0. Neither may be a child of the other.
unsafe fn link<T: Ord>(a: NodePtr<T>, b: NodePtr<T>) -> NodePtr<T> {
    debug_assert!(!a.is_null() && !b.is_null());

    // SAFETY: both pointers guaranteed non-null and valid by caller.
    let a_node = unsafe { node_deref(a) };
    // SAFETY: same as above; b is non-null and valid by caller.
    let b_node = unsafe { node_deref(b) };

    let (winner, winner_node, loser, loser_node) = if a_node.value() <= b_node.value() {
        (a, a_node, b, b_node)
    } else {
        (b, b_node, a, a_node)
    };

    // SAFETY: winner and loser are distinct valid nodes from the branch above.
    unsafe {
        let old_child = winner_node.child_ptr();

        loser_node.set_next(old_child);
        loser_node.set_prev(ptr::null_mut());
        loser_node.set_parent(winner);

        if !old_child.is_null() {
            // SAFETY: old_child is a valid node — it was the winner's child.
            node_deref(old_child).set_prev(loser);
        }

        winner_node.set_child(loser);
    }

    winner
}

// =============================================================================
// cut
// =============================================================================

/// Detaches a node from its parent and sibling chain.
///
/// # Safety
///
/// `ptr` must be non-null and point to a valid heap node that is currently
/// linked in the tree (has a parent or siblings).
unsafe fn cut<T>(ptr: NodePtr<T>) {
    // SAFETY: ptr is a valid linked node per caller contract.
    // parent/prev/next pointers are valid if non-null because they are
    // maintained by link/merge_pairs operations on valid heap nodes.
    unsafe {
        let node = node_deref(ptr);
        let parent = node.parent_ptr();
        let prev = node.prev_ptr();
        let next = node.next_ptr();

        if prev.is_null() {
            if !parent.is_null() {
                node_deref(parent).set_child(next);
            }
        } else {
            node_deref(prev).set_next(next);
        }

        if !next.is_null() {
            node_deref(next).set_prev(prev);
        }

        node.set_parent(ptr::null_mut());
        node.set_prev(ptr::null_mut());
        node.set_next(ptr::null_mut());
    }
}

// =============================================================================
// merge_pairs
// =============================================================================

/// Two-pass pairing merge: pair siblings left-to-right, then merge
/// the resulting trees right-to-left. O(log n) amortized.
///
/// # Safety
///
/// `first` may be null (returns null). If non-null, it must point to
/// a valid sibling chain of heap nodes (connected via next pointers).
unsafe fn merge_pairs<T: Ord>(first: NodePtr<T>) -> NodePtr<T> {
    if first.is_null() {
        return ptr::null_mut();
    }

    // SAFETY: all node_deref calls below operate on pointers from the
    // sibling chain starting at `first`. Each pointer is valid because
    // it was obtained from a next_ptr() of a valid node in the chain.
    // link() requires both arguments non-null — we verify before calling.
    unsafe {
        let first_node = node_deref(first);
        if first_node.next_ptr().is_null() {
            first_node.set_parent(ptr::null_mut());
            first_node.set_prev(ptr::null_mut());
            return first;
        }

        // Pass 1: pair siblings left-to-right, push winners onto reversed stack
        let mut reversed: NodePtr<T> = ptr::null_mut();
        let mut current = first;

        while !current.is_null() {
            let a = current;
            let a_node = node_deref(a);
            let b = a_node.next_ptr();

            if b.is_null() {
                a_node.set_parent(ptr::null_mut());
                a_node.set_prev(ptr::null_mut());
                a_node.set_next(reversed);
                reversed = a;
                break;
            }

            let b_node = node_deref(b);
            current = b_node.next_ptr();

            // SAFETY: a and b are both non-null valid nodes from the chain.
            let winner = link(a, b);
            let winner_node = node_deref(winner);
            winner_node.set_parent(ptr::null_mut());
            winner_node.set_prev(ptr::null_mut());
            winner_node.set_next(reversed);
            reversed = winner;
        }

        // Pass 2: merge right-to-left
        let mut result = reversed;
        let result_node = node_deref(result);
        let mut current = result_node.next_ptr();
        result_node.set_next(ptr::null_mut());

        while !current.is_null() {
            let current_node = node_deref(current);
            let next = current_node.next_ptr();
            current_node.set_next(ptr::null_mut());
            // SAFETY: result and current are both non-null valid nodes.
            result = link(result, current);
            current = next;
        }

        node_deref(result).set_parent(ptr::null_mut());
        result
    }
}

// =============================================================================
// clear_all
// =============================================================================

/// Iterative tree flattening: detach node, stitch children+siblings into a
/// flat worklist, decrement refcount via the `RcFree` trait.
///
/// # Safety
///
/// `current` must be non-null and the root of a valid heap subtree. Every node
/// in the subtree must have refcount >= 2 (user + heap). After this call,
/// the heap's references are released.
unsafe fn clear_all<T>(mut current: NodePtr<T>, slab: &impl RcFree<HeapNode<T>>) {
    // SAFETY: we iterate the tree by flattening children+siblings into a
    // linear worklist. Each node is visited exactly once. node_deref is safe
    // because every node in a linked heap has refcount >= 2. RcSlot::from_raw
    // reconstructs the heap's handle to release its strong reference.
    unsafe {
        while !current.is_null() {
            let node = node_deref(current);
            let first_child = node.child_ptr();
            let next_sibling = node.next_ptr();

            // Stitch child list onto sibling list to create flat worklist
            if !first_child.is_null() && !next_sibling.is_null() {
                let mut tail = first_child;
                loop {
                    let t = node_deref(tail).next_ptr();
                    if t.is_null() {
                        break;
                    }
                    tail = t;
                }
                node_deref(tail).set_next(next_sibling);
            }

            let next_to_visit = if first_child.is_null() {
                next_sibling
            } else {
                first_child
            };

            node.set_parent(ptr::null_mut());
            node.set_child(ptr::null_mut());
            node.set_next(ptr::null_mut());
            node.set_prev(ptr::null_mut());
            node.set_owner(0);
            // SAFETY: current was obtained from as_ptr() during link. The heap
            // holds one strong ref per node (via inc_strong). Reconstructing
            // the handle releases that ref.
            let rc_handle = RcSlot::from_raw(current);
            slab.free_rc(rc_handle);

            current = next_to_visit;
        }
    }
}

// =============================================================================
// Heap<T>
// =============================================================================

/// A min-heap (pairing heap) backed by slab-allocated `RcSlot` nodes.
///
/// # Complexity
///
/// | Operation  | Time                |
/// |------------|---------------------|
/// | link/push  | O(1)                |
/// | peek       | O(1)                |
/// | pop        | O(log n) amortized  |
/// | unlink     | O(log n) amortized  |
/// | contains   | O(1)                |
pub struct Heap<T: Ord> {
    root: NodePtr<T>,
    len: usize,
    id: usize,
}

impl<T: Ord> Heap<T> {
    /// Creates a new empty heap.
    pub fn new() -> Self {
        Heap {
            root: ptr::null_mut(),
            len: 0,
            id: next_collection_id(),
        }
    }

    /// Returns the number of elements in the heap.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the heap has no elements.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns a reference to the minimum (root) node, or `None` if empty.
    pub fn peek(&self) -> Option<&HeapNode<T>> {
        if self.root.is_null() {
            return None;
        }
        // SAFETY: root is non-null and points to a linked node with refcount >= 2.
        Some(unsafe { node_deref(self.root) })
    }

    /// Returns `true` if the handle is linked to this heap.
    pub fn contains(&self, handle: &RcSlot<HeapNode<T>>) -> bool {
        // SAFETY: handle is a live RcSlot, as_ptr() returns a valid pointer.
        let node = unsafe { node_deref(handle.as_ptr()) };
        node.owner_id() == self.id
    }

    // =========================================================================
    // Link / Pop / Unlink / Clear
    // =========================================================================

    /// Links an existing node into the heap. O(1).
    ///
    /// # Panics
    ///
    /// Panics if the node is already linked to a collection.
    pub fn link(&mut self, handle: &RcSlot<HeapNode<T>>) {
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(handle.as_ptr()) };
        if node.is_linked() {
            panic_already_linked();
        }
        // SAFETY: we just verified the node is not linked.
        unsafe { self.link_unchecked(handle) };
    }

    /// Links an existing node into the heap without verifying it is unlinked.
    ///
    /// # Safety
    ///
    /// The node must not be currently linked to any collection.
    pub unsafe fn link_unchecked(&mut self, handle: &RcSlot<HeapNode<T>>) {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(ptr) };
        node.set_owner(self.id);
        inc_strong(handle);

        if self.root.is_null() {
            self.root = ptr;
        } else {
            // SAFETY: both self.root and ptr are non-null valid heap nodes.
            self.root = unsafe { link(self.root, ptr) };
        }

        self.len += 1;
    }

    /// Removes and returns the minimum (root) node. O(log n) amortized.
    pub fn pop(&mut self) -> Option<RcSlot<HeapNode<T>>> {
        if self.root.is_null() {
            return None;
        }

        let root_ptr = self.root;

        // SAFETY: root_ptr is non-null and points to the heap root with refcount >= 2.
        unsafe {
            let root = node_deref(root_ptr);
            let first_child = root.child_ptr();
            root.set_child(ptr::null_mut());
            root.set_owner(0);
            // SAFETY: first_child is either null or a valid child chain.
            self.root = merge_pairs(first_child);
        }

        self.len -= 1;
        // SAFETY: root_ptr was obtained from as_ptr() during link. The heap held
        // one strong ref (via inc_strong). Transferring it to the returned handle.
        Some(unsafe { RcSlot::from_raw(root_ptr) })
    }

    /// Removes a node from the heap, releasing the heap's reference.
    ///
    /// Works with both bounded and unbounded slabs.
    ///
    /// # Panics
    ///
    /// Panics if the node is not linked to this heap.
    pub fn unlink(&mut self, handle: &RcSlot<HeapNode<T>>, slab: &impl RcFree<HeapNode<T>>) {
        let ptr = self.unwire(handle);
        // SAFETY: ptr was obtained from as_ptr() during link. The heap holds
        // one strong ref (via inc_strong). Reconstructing to release it.
        let rc_handle = unsafe { RcSlot::from_raw(ptr) };
        slab.free_rc(rc_handle);
    }

    /// Removes a node without ownership check.
    ///
    /// # Safety
    ///
    /// The node must be currently linked to this heap.
    pub unsafe fn unlink_unchecked(
        &mut self,
        handle: &RcSlot<HeapNode<T>>,
        slab: &impl RcFree<HeapNode<T>>,
    ) {
        let ptr = self.unwire_unchecked(handle);
        // SAFETY: ptr was obtained from as_ptr() during link. Same as unlink.
        let rc_handle = unsafe { RcSlot::from_raw(ptr) };
        slab.free_rc(rc_handle);
    }

    /// Internal: verify ownership, unwire, return raw pointer for decrement.
    fn unwire(&mut self, handle: &RcSlot<HeapNode<T>>) -> NodePtr<T> {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(ptr) };
        if node.owner_id() != self.id {
            panic_wrong_heap();
        }
        self.unwire_ptr(ptr);
        ptr
    }

    /// Internal: unwire without ownership check.
    fn unwire_unchecked(&mut self, handle: &RcSlot<HeapNode<T>>) -> NodePtr<T> {
        let ptr = handle.as_ptr();
        self.unwire_ptr(ptr);
        ptr
    }

    /// Internal: unwire a node from the heap by raw pointer.
    fn unwire_ptr(&mut self, ptr: NodePtr<T>) {
        if ptr == self.root {
            // SAFETY: ptr == self.root, which is non-null and valid with refcount >= 2.
            unsafe {
                let node = node_deref(ptr);
                let first_child = node.child_ptr();
                node.set_child(ptr::null_mut());
                node.set_owner(0);
                self.root = merge_pairs(first_child);
            }
            self.len -= 1;
            return;
        }

        // SAFETY: ptr is a non-root linked node — it has a parent, so cut is valid.
        unsafe { cut(ptr) };

        // SAFETY: ptr is a valid node we just cut from the tree.
        unsafe {
            let node = node_deref(ptr);
            let first_child = node.child_ptr();
            node.set_child(ptr::null_mut());
            node.set_owner(0);

            if !first_child.is_null() {
                // SAFETY: first_child is a valid child chain; merged result and
                // self.root are both non-null valid nodes.
                let merged = merge_pairs(first_child);
                self.root = link(self.root, merged);
            }
        }

        self.len -= 1;
    }

    /// Clears all nodes, releasing the heap's references through the slab.
    ///
    /// Works with both bounded and unbounded slabs.
    pub fn clear(&mut self, slab: &impl RcFree<HeapNode<T>>) {
        if self.root.is_null() {
            return;
        }
        // SAFETY: root is non-null and heads a valid heap tree.
        unsafe { clear_all(self.root, slab) };
        self.root = ptr::null_mut();
        self.len = 0;
    }

    // =========================================================================
    // Push — bounded slab
    // =========================================================================

    /// Allocates from a bounded slab and inserts into the heap.
    ///
    /// Returns `Err(Full(value))` if the slab is at capacity.
    pub fn try_push(
        &mut self,
        slab: &RcBoundedSlab<HeapNode<T>>,
        value: T,
    ) -> Result<RcSlot<HeapNode<T>>, Full<T>> {
        let handle = slab
            .try_alloc(HeapNode::new(value))
            .map_err(|full| Full(full.into_inner().into_value()))?;
        // SAFETY: freshly allocated node is not linked to any collection.
        unsafe { self.link_unchecked(&handle) };
        Ok(handle)
    }

    // =========================================================================
    // Push — unbounded slab
    // =========================================================================

    /// Allocates from an unbounded slab and inserts into the heap.
    ///
    /// Never fails — the slab grows if needed.
    pub fn push(&mut self, slab: &RcUnboundedSlab<HeapNode<T>>, value: T) -> RcSlot<HeapNode<T>> {
        let handle = slab.alloc(HeapNode::new(value));
        // SAFETY: freshly allocated node is not linked to any collection.
        unsafe { self.link_unchecked(&handle) };
        handle
    }

    // =========================================================================
    // Iterators
    // =========================================================================

    /// Returns a draining iterator that pops elements in sorted order.
    pub fn drain(&mut self) -> Drain<'_, T> {
        Drain { heap: self }
    }

    /// Returns an iterator that pops elements while the predicate is true.
    pub fn drain_while<F: FnMut(&HeapNode<T>) -> bool>(&mut self, pred: F) -> DrainWhile<'_, T, F> {
        DrainWhile { heap: self, pred }
    }
}

impl<T: Ord> Default for Heap<T> {
    fn default() -> Self {
        Self::new()
    }
}

// Heap does NOT implement Drop in release. The user must call clear() with
// the slab to release the heap's strong references.
//
// In debug builds, we panic on non-empty drop to catch slot leaks early.
#[cfg(debug_assertions)]
impl<T: Ord> Drop for Heap<T> {
    #[allow(clippy::manual_assert)]
    fn drop(&mut self) {
        if self.len > 0 && !std::thread::panicking() {
            panic!(
                "Heap dropped with {} elements without calling clear(). \
                 This leaks slab slots. Call heap.clear(&slab) before dropping.",
                self.len
            );
        }
    }
}

// =============================================================================
// Drain
// =============================================================================

/// Draining iterator that pops elements in sorted (min-first) order.
///
/// Unlike [`RbTree::drain`](crate::rbtree::Drain) and
/// [`BTree::drain`](crate::btree::DrainBTree), this iterator does NOT
/// clear remaining elements on drop. Partially consumed drains leave
/// the remaining elements in the heap.
pub struct Drain<'a, T: Ord> {
    heap: &'a mut Heap<T>,
}

impl<T: Ord> Iterator for Drain<'_, T> {
    type Item = RcSlot<HeapNode<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.heap.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.heap.len(), Some(self.heap.len()))
    }
}

impl<T: Ord> ExactSizeIterator for Drain<'_, T> {}

// Note: Drain does NOT clear on drop — the caller must handle remaining
// elements. This is intentional since clear() requires the slab.

// =============================================================================
// DrainWhile
// =============================================================================

/// Iterator that pops elements while a predicate holds.
pub struct DrainWhile<'a, T: Ord, F: FnMut(&HeapNode<T>) -> bool> {
    heap: &'a mut Heap<T>,
    pred: F,
}

impl<T: Ord, F: FnMut(&HeapNode<T>) -> bool> Iterator for DrainWhile<'_, T, F> {
    type Item = RcSlot<HeapNode<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.heap.is_empty() {
            return None;
        }
        // SAFETY: heap is non-empty so root is non-null and valid.
        let node = unsafe { node_deref(self.heap.root) };
        if !(self.pred)(node) {
            return None;
        }
        self.heap.pop()
    }
}
