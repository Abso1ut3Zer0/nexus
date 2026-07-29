//! Doubly-linked list with `RcSlot`-based ownership.
//!
//! # Design
//!
//! - **User holds `RcSlot<ListNode<T>>`** — their ownership token + data access
//! - **List stores raw pointers** and maintains its own strong reference per node
//! - **Guard-based data access** via `RcSlot::borrow()` / `borrow_mut()`
//!
//! # Ownership Model
//!
//! Every linked node has `refcount >= 2`:
//! - One from the user's `RcSlot` handle
//! - One from the list's internal bookkeeping (clone + forget)
//!
//! Unlinking releases the list's ref. The user's handle remains valid.
//! Dropping the list releases all its refs. If the user already dropped
//! their handle, the node is cleaned up. If not, the user still has access.
//!
//! # Example
//!
//! ```ignore
//! use nexus_slab::rc::bounded::Slab;
//! use nexus_collections::list::{List, ListNode};
//!
//! let slab = unsafe { Slab::<ListNode<Order>>::with_capacity(1000) };
//! let mut list = List::new();
//!
//! let handle = slab.alloc(ListNode::new(Order { id: 1, price: 100.0 }));
//! list.link_back(&handle);
//!
//! // Read via borrow guard
//! assert_eq!(handle.borrow().value.price, 100.0);
//!
//! // Re-linking: move between collections
//! list.unlink(&handle);
//! list.link_back(&handle);
//! ```

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

/// Raw pointer used for prev/next links.
///
/// Points to the `RcCell<ListNode<T>>` — the refcount + value wrapper.
/// We use this to reconstruct `RcSlot` handles for pop operations via
/// `RcSlot::from_raw()`.
type NodePtr<T> = *mut RcCell<ListNode<T>>;

// =============================================================================
// ListNode<T>
// =============================================================================

/// A node in a doubly-linked list.
///
/// Contains link pointers (prev/next/owner) as `Cell` fields for interior
/// mutability, and the user's value as a public field.
///
/// # Data Access
///
/// Access user data through `RcSlot`'s borrow guards:
///
/// ```ignore
/// handle.borrow().value.price       // shared borrow
/// handle.borrow_mut().value.price = 5.0  // mutable borrow
/// ```
pub struct ListNode<T> {
    prev: std::cell::Cell<NodePtr<T>>,
    next: std::cell::Cell<NodePtr<T>>,
    owner: std::cell::Cell<usize>,
    /// The user's data.
    pub value: T,
}

impl<T> ListNode<T> {
    /// Creates a new detached node wrapping the given value.
    pub fn new(value: T) -> Self {
        ListNode {
            prev: std::cell::Cell::new(ptr::null_mut()),
            next: std::cell::Cell::new(ptr::null_mut()),
            owner: std::cell::Cell::new(0),
            value,
        }
    }

    /// Returns `true` if this node is linked to a list.
    pub fn is_linked(&self) -> bool {
        self.owner.get() != 0
    }

    /// Consumes the node, returning the user data.
    #[doc(hidden)]
    pub fn into_value(self) -> T {
        self.value
    }

    // Internal accessors for list operations

    fn prev_ptr(&self) -> NodePtr<T> {
        self.prev.get()
    }

    fn next_ptr(&self) -> NodePtr<T> {
        self.next.get()
    }

    fn set_prev(&self, ptr: NodePtr<T>) {
        self.prev.set(ptr);
    }

    fn set_next(&self, ptr: NodePtr<T>) {
        self.next.set(ptr);
    }

    fn owner_id(&self) -> usize {
        self.owner.get()
    }

    fn set_owner(&self, id: usize) {
        self.owner.set(id);
    }
}

// =============================================================================
// node_deref — navigate raw pointer to &ListNode<T>
// =============================================================================

/// Dereferences a `NodePtr<T>` to get `&ListNode<T>`.
///
/// Dereferences a `NodePtr<T>` to get `&ListNode<T>`.
///
/// Returns a reference with an unbounded lifetime. The caller is responsible
/// for ensuring the reference does not outlive the slot's allocation.
///
/// # Safety
///
/// `ptr` must be non-null and point to an occupied `RcCell` with refcount > 0.
#[inline(always)]
unsafe fn node_deref<'a, T>(ptr: NodePtr<T>) -> &'a ListNode<T> {
    // SAFETY: RcCell::value_ptr() returns *mut T.
    // The Cell-based fields (prev, next, owner) support interior mutability
    // through &self, so shared access is sound.
    unsafe { &*(*ptr).value_ptr().cast_const() }
}

// =============================================================================
// Cold panic helpers — extracted so hot-path functions stay leaf/frameless
// =============================================================================

#[cold]
#[inline(never)]
fn panic_wrong_list() -> ! {
    panic!("node is not linked to this list")
}

#[cold]
#[inline(never)]
fn panic_already_linked() -> ! {
    panic!("node is already linked to a collection")
}

// =============================================================================
// Refcount helpers — clone+forget to increment, from_raw+free to decrement
// =============================================================================

/// Increments the refcount for the collection's reference.
///
/// Clones the handle (refcount +1) and forgets the clone so the collection
/// holds a strong ref without storing the handle. The matching decrement
/// happens in pop/unlink/clear via `RcSlot::from_raw`.
#[inline]
fn inc_strong<T>(handle: &RcSlot<ListNode<T>>) {
    let clone = handle.clone();
    core::mem::forget(clone);
}

// =============================================================================
// List<T>
// =============================================================================

/// A doubly-linked list backed by slab-allocated `RcSlot` nodes.
///
/// # Ownership Model
///
/// - User holds `RcSlot<ListNode<T>>` handles — their ownership token
/// - List stores raw pointers and maintains its own strong reference per node
/// - Every linked node has `refcount >= 2` (user + list)
/// - Unlinking decrements the list's ref; the user's handle remains valid
///
/// # Slab Parameter
///
/// The slab is NOT stored in the collection. It is passed to methods that
/// need to allocate or free (push, pop, clear). Link/unlink methods that
/// only wire pointers do not need the slab — except `unlink` and `clear`
/// which must decrement the collection's refcount.
pub struct List<T> {
    head: NodePtr<T>,
    tail: NodePtr<T>,
    len: usize,
    id: usize,
}

impl<T> List<T> {
    /// Creates a new empty list.
    pub fn new() -> Self {
        List {
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
            len: 0,
            id: next_collection_id(),
        }
    }

    /// Returns the number of linked elements.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the list has no linked elements.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    // =========================================================================
    // Link operations
    // =========================================================================

    /// Links a node to the back of the list.
    ///
    /// The list acquires its own strong reference to the node.
    ///
    /// # Panics
    ///
    /// Panics if the node is already linked to a collection.
    pub fn link_back(&mut self, handle: &RcSlot<ListNode<T>>) {
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(handle.as_ptr()) };
        if node.is_linked() {
            panic_already_linked();
        }
        // SAFETY: we just verified the node is not linked.
        unsafe { self.link_back_unchecked(handle) };
    }

    /// Links a node to the back without verifying it is unlinked.
    ///
    /// # Safety
    ///
    /// The node must not be currently linked to any list.
    pub unsafe fn link_back_unchecked(&mut self, handle: &RcSlot<ListNode<T>>) {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(ptr) };

        node.set_prev(self.tail);
        node.set_next(ptr::null_mut());
        node.set_owner(self.id);

        if self.tail.is_null() {
            self.head = ptr;
        } else {
            // SAFETY: tail is non-null and points to a linked node with refcount >= 2.
            unsafe { node_deref(self.tail) }.set_next(ptr);
        }

        self.tail = ptr;
        self.len += 1;
        inc_strong(handle);
    }

    /// Links a node to the front of the list.
    ///
    /// The list acquires its own strong reference to the node.
    ///
    /// # Panics
    ///
    /// Panics if the node is already linked to a collection.
    pub fn link_front(&mut self, handle: &RcSlot<ListNode<T>>) {
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(handle.as_ptr()) };
        if node.is_linked() {
            panic_already_linked();
        }
        // SAFETY: we just verified the node is not linked.
        unsafe { self.link_front_unchecked(handle) };
    }

    /// Links a node to the front without verifying it is unlinked.
    ///
    /// # Safety
    ///
    /// The node must not be currently linked to any list.
    pub unsafe fn link_front_unchecked(&mut self, handle: &RcSlot<ListNode<T>>) {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(ptr) };

        node.set_prev(ptr::null_mut());
        node.set_next(self.head);
        node.set_owner(self.id);

        if self.head.is_null() {
            self.tail = ptr;
        } else {
            // SAFETY: head is non-null and points to a linked node with refcount >= 2.
            unsafe { node_deref(self.head) }.set_prev(ptr);
        }

        self.head = ptr;
        self.len += 1;
        inc_strong(handle);
    }

    /// Links a node immediately after an existing node.
    ///
    /// # Panics
    ///
    /// Panics if `handle` is already linked to a list, or if `after` is not
    /// linked to this list.
    pub fn link_after(&mut self, after: &RcSlot<ListNode<T>>, handle: &RcSlot<ListNode<T>>) {
        // SAFETY: both handles are live RcSlots with refcount >= 1.
        let after_node = unsafe { node_deref(after.as_ptr()) };
        if after_node.owner_id() != self.id {
            panic_wrong_list();
        }

        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let new_node = unsafe { node_deref(handle.as_ptr()) };
        if new_node.is_linked() {
            panic_already_linked();
        }

        let after_ptr = after.as_ptr();
        let new_ptr = handle.as_ptr();
        let next_ptr = after_node.next_ptr();

        new_node.set_prev(after_ptr);
        new_node.set_next(next_ptr);
        new_node.set_owner(self.id);

        after_node.set_next(new_ptr);

        if next_ptr.is_null() {
            self.tail = new_ptr;
        } else {
            // SAFETY: next_ptr is non-null and was the successor of a linked node.
            unsafe { node_deref(next_ptr) }.set_prev(new_ptr);
        }

        self.len += 1;
        inc_strong(handle);
    }

    /// Links a node immediately before an existing node.
    ///
    /// # Panics
    ///
    /// Panics if `handle` is already linked to a list, or if `before` is not
    /// linked to this list.
    pub fn link_before(&mut self, before: &RcSlot<ListNode<T>>, handle: &RcSlot<ListNode<T>>) {
        // SAFETY: both handles are live RcSlots with refcount >= 1.
        let before_node = unsafe { node_deref(before.as_ptr()) };
        if before_node.owner_id() != self.id {
            panic_wrong_list();
        }

        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let new_node = unsafe { node_deref(handle.as_ptr()) };
        if new_node.is_linked() {
            panic_already_linked();
        }

        let before_ptr = before.as_ptr();
        let new_ptr = handle.as_ptr();
        let prev_ptr = before_node.prev_ptr();

        new_node.set_prev(prev_ptr);
        new_node.set_next(before_ptr);
        new_node.set_owner(self.id);

        before_node.set_prev(new_ptr);

        if prev_ptr.is_null() {
            self.head = new_ptr;
        } else {
            // SAFETY: prev_ptr is non-null and was the predecessor of a linked node.
            unsafe { node_deref(prev_ptr) }.set_next(new_ptr);
        }

        self.len += 1;
        inc_strong(handle);
    }

    // =========================================================================
    // Unlink — requires slab to decrement refcount
    // =========================================================================

    /// Unlinks a node, releasing the list's reference through the slab.
    ///
    /// Works with both bounded and unbounded slabs.
    ///
    /// # Panics
    ///
    /// Panics if the node is not linked to this list.
    pub fn unlink(&mut self, handle: &RcSlot<ListNode<T>>, slab: &impl RcFree<ListNode<T>>) {
        let ptr = self.unwire(handle);
        // SAFETY: ptr was obtained from as_ptr() during link. The list holds
        // one strong ref (via inc_strong). Reconstructing to release it.
        let rc_handle = unsafe { RcSlot::from_raw(ptr) };
        slab.free_rc(rc_handle);
    }

    /// Unlinks without ownership check.
    ///
    /// # Safety
    ///
    /// The node must be currently linked to this list.
    pub unsafe fn unlink_unchecked(
        &mut self,
        handle: &RcSlot<ListNode<T>>,
        slab: &impl RcFree<ListNode<T>>,
    ) {
        let ptr = self.unwire_unchecked(handle);
        // SAFETY: ptr was obtained from as_ptr() during link. Same as unlink.
        let rc_handle = unsafe { RcSlot::from_raw(ptr) };
        slab.free_rc(rc_handle);
    }

    /// Internal: verify ownership, unwire, return raw pointer for decrement.
    fn unwire(&mut self, handle: &RcSlot<ListNode<T>>) -> NodePtr<T> {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(ptr) };
        if node.owner_id() != self.id {
            panic_wrong_list();
        }
        self.unwire_ptr(ptr);
        ptr
    }

    /// Internal: unwire without ownership check.
    fn unwire_unchecked(&mut self, handle: &RcSlot<ListNode<T>>) -> NodePtr<T> {
        let ptr = handle.as_ptr();
        self.unwire_ptr(ptr);
        ptr
    }

    /// Internal: unwire a node from the list by raw pointer.
    ///
    /// `ptr` must be non-null and point to a node linked to this list.
    fn unwire_ptr(&mut self, ptr: NodePtr<T>) {
        // SAFETY: ptr is a valid linked node — guaranteed by callers (unwire
        // checks ownership, unwire_unchecked has a safety contract).
        let node = unsafe { node_deref(ptr) };
        let prev = node.prev_ptr();
        let next = node.next_ptr();

        if prev.is_null() {
            self.head = next;
        } else {
            // SAFETY: prev is non-null and a valid linked predecessor.
            unsafe { node_deref(prev) }.set_next(next);
        }

        if next.is_null() {
            self.tail = prev;
        } else {
            // SAFETY: next is non-null and a valid linked successor.
            unsafe { node_deref(next) }.set_prev(prev);
        }

        node.set_prev(ptr::null_mut());
        node.set_next(ptr::null_mut());
        node.set_owner(0);
        self.len -= 1;
    }

    /// Clears all nodes, releasing the list's references through the slab.
    ///
    /// Works with both bounded and unbounded slabs.
    pub fn clear(&mut self, slab: &impl RcFree<ListNode<T>>) {
        let mut current = self.head;
        while !current.is_null() {
            // SAFETY: current is non-null and a linked node with refcount >= 2.
            let node = unsafe { node_deref(current) };
            let next = node.next_ptr();

            node.set_prev(ptr::null_mut());
            node.set_next(ptr::null_mut());
            node.set_owner(0);

            // SAFETY: current was obtained from as_ptr() during link. The list
            // holds one strong ref per node. Reconstructing to release it.
            let rc_handle = unsafe { RcSlot::from_raw(current) };
            slab.free_rc(rc_handle);

            current = next;
        }
        self.head = ptr::null_mut();
        self.tail = ptr::null_mut();
        self.len = 0;
    }

    // =========================================================================
    // Pop — transfers list's strong ref to returned handle
    // =========================================================================

    /// Removes and returns the front node as an `RcSlot`.
    ///
    /// The returned handle carries the list's strong reference — no net
    /// refcount change. The node is detached.
    pub fn pop_front(&mut self) -> Option<RcSlot<ListNode<T>>> {
        if self.head.is_null() {
            return None;
        }

        let ptr = self.head;
        // SAFETY: head is non-null and points to a linked node with refcount >= 2.
        let node = unsafe { node_deref(ptr) };
        let next = node.next_ptr();

        self.head = next;
        if next.is_null() {
            self.tail = ptr::null_mut();
        } else {
            // SAFETY: next is non-null and a valid linked successor.
            unsafe { node_deref(next) }.set_prev(ptr::null_mut());
        }

        node.set_prev(ptr::null_mut());
        node.set_next(ptr::null_mut());
        node.set_owner(0);

        self.len -= 1;

        // SAFETY: ptr was obtained from as_ptr() during link. Transferring the
        // list's strong ref into the returned handle — no net refcount change.
        Some(unsafe { RcSlot::from_raw(ptr) })
    }

    /// Removes and returns the back node as an `RcSlot`.
    pub fn pop_back(&mut self) -> Option<RcSlot<ListNode<T>>> {
        if self.tail.is_null() {
            return None;
        }

        let ptr = self.tail;
        // SAFETY: tail is non-null and points to a linked node with refcount >= 2.
        let node = unsafe { node_deref(ptr) };
        let prev = node.prev_ptr();

        self.tail = prev;
        if prev.is_null() {
            self.head = ptr::null_mut();
        } else {
            // SAFETY: prev is non-null and a valid linked predecessor.
            unsafe { node_deref(prev) }.set_next(ptr::null_mut());
        }

        node.set_prev(ptr::null_mut());
        node.set_next(ptr::null_mut());
        node.set_owner(0);

        self.len -= 1;

        // SAFETY: ptr was obtained from as_ptr() during link. Transferring the
        // list's strong ref into the returned handle.
        Some(unsafe { RcSlot::from_raw(ptr) })
    }

    // =========================================================================
    // Peek
    // =========================================================================

    /// Returns a reference to the front node, or `None` if empty.
    pub fn front(&self) -> Option<&ListNode<T>> {
        if self.head.is_null() {
            return None;
        }
        // SAFETY: head is non-null and points to a linked node with refcount >= 2.
        Some(unsafe { node_deref(self.head) })
    }

    /// Returns a reference to the back node, or `None` if empty.
    pub fn back(&self) -> Option<&ListNode<T>> {
        if self.tail.is_null() {
            return None;
        }
        // SAFETY: tail is non-null and points to a linked node with refcount >= 2.
        Some(unsafe { node_deref(self.tail) })
    }

    // =========================================================================
    // Position checks
    // =========================================================================

    /// Returns `true` if the handle is at the head of this list.
    pub fn is_head(&self, handle: &RcSlot<ListNode<T>>) -> bool {
        handle.as_ptr() == self.head
    }

    /// Returns `true` if the handle is at the tail of this list.
    pub fn is_tail(&self, handle: &RcSlot<ListNode<T>>) -> bool {
        handle.as_ptr() == self.tail
    }

    /// Returns `true` if the handle is linked to this list.
    pub fn contains(&self, handle: &RcSlot<ListNode<T>>) -> bool {
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(handle.as_ptr()) };
        node.owner_id() == self.id
    }

    // =========================================================================
    // Move operations — no refcount changes
    // =========================================================================

    /// Moves a node to the front without changing ownership or refcounts.
    ///
    /// # Panics
    ///
    /// Panics if the node is not linked to this list.
    pub fn move_to_front(&mut self, handle: &RcSlot<ListNode<T>>) {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(ptr) };
        if node.owner_id() != self.id {
            panic_wrong_list();
        }

        if ptr == self.head {
            return;
        }

        let prev = node.prev_ptr();
        let next = node.next_ptr();

        // SAFETY: prev/next are valid linked nodes if non-null (maintained by list ops).
        if !prev.is_null() {
            // SAFETY: prev is non-null and a valid linked predecessor.
            unsafe { node_deref(prev) }.set_next(next);
        }
        if next.is_null() {
            self.tail = prev;
        } else {
            // SAFETY: next is non-null and a valid linked successor.
            unsafe { node_deref(next) }.set_prev(prev);
        }

        node.set_prev(ptr::null_mut());
        node.set_next(self.head);
        if !self.head.is_null() {
            // SAFETY: head is non-null and points to a linked node with refcount >= 2.
            unsafe { node_deref(self.head) }.set_prev(ptr);
        }
        self.head = ptr;
    }

    /// Moves a node to the front without verifying ownership.
    ///
    /// # Safety
    ///
    /// The node must be currently linked to this list.
    pub unsafe fn move_to_front_unchecked(&mut self, handle: &RcSlot<ListNode<T>>) {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot linked to this list per caller contract.
        let node = unsafe { node_deref(ptr) };

        if ptr == self.head {
            return;
        }

        let prev = node.prev_ptr();
        let next = node.next_ptr();

        // SAFETY: prev/next are valid linked nodes if non-null.
        if !prev.is_null() {
            // SAFETY: prev is non-null and a valid linked predecessor.
            unsafe { node_deref(prev) }.set_next(next);
        }
        if next.is_null() {
            self.tail = prev;
        } else {
            // SAFETY: next is non-null and a valid linked successor.
            unsafe { node_deref(next) }.set_prev(prev);
        }

        node.set_prev(ptr::null_mut());
        node.set_next(self.head);
        if !self.head.is_null() {
            // SAFETY: head is non-null and points to a linked node with refcount >= 2.
            unsafe { node_deref(self.head) }.set_prev(ptr);
        }
        self.head = ptr;
    }

    /// Moves a node to the back without changing ownership or refcounts.
    ///
    /// # Panics
    ///
    /// Panics if the node is not linked to this list.
    pub fn move_to_back(&mut self, handle: &RcSlot<ListNode<T>>) {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot with refcount >= 1.
        let node = unsafe { node_deref(ptr) };
        if node.owner_id() != self.id {
            panic_wrong_list();
        }

        if ptr == self.tail {
            return;
        }

        let prev = node.prev_ptr();
        let next = node.next_ptr();

        // SAFETY: prev/next are valid linked nodes if non-null.
        if !next.is_null() {
            // SAFETY: next is non-null and a valid linked successor.
            unsafe { node_deref(next) }.set_prev(prev);
        }
        if prev.is_null() {
            self.head = next;
        } else {
            // SAFETY: prev is non-null and a valid linked predecessor.
            unsafe { node_deref(prev) }.set_next(next);
        }

        node.set_next(ptr::null_mut());
        node.set_prev(self.tail);
        if !self.tail.is_null() {
            // SAFETY: tail is non-null and points to a linked node with refcount >= 2.
            unsafe { node_deref(self.tail) }.set_next(ptr);
        }
        self.tail = ptr;
    }

    /// Moves a node to the back without verifying ownership.
    ///
    /// # Safety
    ///
    /// The node must be currently linked to this list.
    pub unsafe fn move_to_back_unchecked(&mut self, handle: &RcSlot<ListNode<T>>) {
        let ptr = handle.as_ptr();
        // SAFETY: handle is a live RcSlot linked to this list per caller contract.
        let node = unsafe { node_deref(ptr) };

        if ptr == self.tail {
            return;
        }

        let prev = node.prev_ptr();
        let next = node.next_ptr();

        // SAFETY: prev/next are valid linked nodes if non-null.
        if !next.is_null() {
            // SAFETY: next is non-null and a valid linked successor.
            unsafe { node_deref(next) }.set_prev(prev);
        }
        if prev.is_null() {
            self.head = next;
        } else {
            // SAFETY: prev is non-null and a valid linked predecessor.
            unsafe { node_deref(prev) }.set_next(next);
        }

        node.set_next(ptr::null_mut());
        node.set_prev(self.tail);
        if !self.tail.is_null() {
            // SAFETY: tail is non-null and points to a linked node with refcount >= 2.
            unsafe { node_deref(self.tail) }.set_next(ptr);
        }
        self.tail = ptr;
    }

    // =========================================================================
    // Cursor entry points
    // =========================================================================

    /// Creates a cursor positioned before the first element.
    pub fn cursor(&mut self) -> Cursor<'_, T> {
        Cursor {
            list: self,
            position: Position::BeforeStart,
        }
    }

    /// Creates a cursor positioned after the last element.
    pub fn cursor_back(&mut self) -> Cursor<'_, T> {
        Cursor {
            list: self,
            position: Position::AfterEnd,
        }
    }
}

// =============================================================================
// Push methods — bounded slab
// =============================================================================

impl<T> List<T> {
    /// Allocates a new node and links it to the back. Returns the handle.
    ///
    /// Returns `Err(Full(value))` if the slab is at capacity.
    pub fn try_push_back(
        &mut self,
        slab: &RcBoundedSlab<ListNode<T>>,
        value: T,
    ) -> Result<RcSlot<ListNode<T>>, Full<T>> {
        let handle = slab
            .try_alloc(ListNode::new(value))
            .map_err(|full| Full(full.into_inner().into_value()))?;
        // SAFETY: freshly allocated node is not linked to any collection.
        unsafe { self.link_back_unchecked(&handle) };
        Ok(handle)
    }

    /// Allocates a new node and links it to the front. Returns the handle.
    ///
    /// Returns `Err(Full(value))` if the slab is at capacity.
    pub fn try_push_front(
        &mut self,
        slab: &RcBoundedSlab<ListNode<T>>,
        value: T,
    ) -> Result<RcSlot<ListNode<T>>, Full<T>> {
        let handle = slab
            .try_alloc(ListNode::new(value))
            .map_err(|full| Full(full.into_inner().into_value()))?;
        // SAFETY: freshly allocated node is not linked to any collection.
        unsafe { self.link_front_unchecked(&handle) };
        Ok(handle)
    }

    /// Allocates from an unbounded slab and links to the back.
    ///
    /// Never fails — the slab grows if needed.
    pub fn push_back(
        &mut self,
        slab: &RcUnboundedSlab<ListNode<T>>,
        value: T,
    ) -> RcSlot<ListNode<T>> {
        let handle = slab.alloc(ListNode::new(value));
        // SAFETY: freshly allocated node is not linked to any collection.
        unsafe { self.link_back_unchecked(&handle) };
        handle
    }

    /// Allocates from an unbounded slab and links to the front.
    ///
    /// Never fails — the slab grows if needed.
    pub fn push_front(
        &mut self,
        slab: &RcUnboundedSlab<ListNode<T>>,
        value: T,
    ) -> RcSlot<ListNode<T>> {
        let handle = slab.alloc(ListNode::new(value));
        // SAFETY: freshly allocated node is not linked to any collection.
        unsafe { self.link_front_unchecked(&handle) };
        handle
    }
}

impl<T> Default for List<T> {
    fn default() -> Self {
        Self::new()
    }
}

// List does NOT implement Drop in release. The user must call clear() with
// the slab to release the list's strong references. If the list is dropped
// without clearing, the list's cloned refs are leaked (refcounts stay
// incremented). This is deliberate: the list doesn't store a slab reference,
// so it can't free on drop.
//
// In debug builds, we panic on non-empty drop to catch slot leaks early.
#[cfg(debug_assertions)]
impl<T> Drop for List<T> {
    #[allow(clippy::manual_assert)]
    fn drop(&mut self) {
        if self.len > 0 && !std::thread::panicking() {
            panic!(
                "List dropped with {} elements without calling clear(). \
                 This leaks slab slots. Call list.clear(&slab) before dropping.",
                self.len
            );
        }
    }
}

// =============================================================================
// Cursor
// =============================================================================

/// Position state for cursor traversal.
enum Position<T> {
    /// Before the first element.
    BeforeStart,
    /// After the last element.
    AfterEnd,
    /// At a specific node.
    At(NodePtr<T>),
}

#[cold]
#[inline(never)]
fn panic_cursor_not_at_node() -> ! {
    panic!("cursor is not positioned at a node")
}

/// Cursor for positional traversal with modification support.
///
/// # Position States
///
/// - `BeforeStart`: Before the first element
/// - `AfterEnd`: After the last element
/// - `At(ptr)`: Positioned at an element
pub struct Cursor<'a, T> {
    list: &'a mut List<T>,
    position: Position<T>,
}

impl<T> Cursor<'_, T> {
    /// Moves the cursor forward to the next node.
    ///
    /// Returns `true` if the cursor is now at a valid node.
    pub fn advance(&mut self) -> bool {
        let next_ptr = match self.position {
            Position::BeforeStart => self.list.head,
            Position::AfterEnd => return false,
            // SAFETY: ptr is a linked node — set by a previous advance/cursor_back.
            Position::At(ptr) => unsafe { node_deref(ptr) }.next_ptr(),
        };

        if next_ptr.is_null() {
            self.position = Position::AfterEnd;
            return false;
        }

        self.position = Position::At(next_ptr);
        true
    }

    /// Moves the cursor backward to the previous node.
    ///
    /// Returns `true` if the cursor is now at a valid node.
    pub fn advance_back(&mut self) -> bool {
        let prev_ptr = match self.position {
            Position::BeforeStart => return false,
            Position::AfterEnd => self.list.tail,
            // SAFETY: ptr is a linked node — set by a previous advance call.
            Position::At(ptr) => unsafe { node_deref(ptr) }.prev_ptr(),
        };

        if prev_ptr.is_null() {
            self.position = Position::BeforeStart;
            return false;
        }

        self.position = Position::At(prev_ptr);
        true
    }

    /// Returns a reference to the current node, or `None` if the cursor is
    /// at `BeforeStart` or `AfterEnd`.
    pub fn current(&self) -> Option<&ListNode<T>> {
        match self.position {
            // SAFETY: ptr is a linked node — set by a previous advance call.
            Position::At(ptr) => Some(unsafe { node_deref(ptr) }),
            _ => None,
        }
    }

    /// Removes the current node from the list. The cursor auto-advances to
    /// the next node.
    ///
    /// Returns the removed node as an `RcSlot` (transfers the list's strong
    /// reference — no net refcount change).
    ///
    /// # Panics
    ///
    /// Panics if the cursor is not positioned at a node.
    pub fn remove(&mut self) -> RcSlot<ListNode<T>> {
        let Position::At(ptr) = self.position else {
            panic_cursor_not_at_node();
        };

        // SAFETY: ptr is a linked node at the cursor position.
        let node = unsafe { node_deref(ptr) };
        let prev = node.prev_ptr();
        let next = node.next_ptr();

        if prev.is_null() {
            self.list.head = next;
        } else {
            // SAFETY: prev is non-null and a valid linked predecessor.
            unsafe { node_deref(prev) }.set_next(next);
        }

        if next.is_null() {
            self.list.tail = prev;
        } else {
            // SAFETY: next is non-null and a valid linked successor.
            unsafe { node_deref(next) }.set_prev(prev);
        }

        node.set_prev(ptr::null_mut());
        node.set_next(ptr::null_mut());
        node.set_owner(0);
        self.list.len -= 1;

        if next.is_null() {
            self.position = Position::AfterEnd;
        } else {
            self.position = Position::At(next);
        }

        // SAFETY: ptr was obtained from as_ptr() during link. Transferring the
        // list's strong ref into the returned handle.
        unsafe { RcSlot::from_raw(ptr) }
    }

    /// Removes the current node if the predicate returns `true`.
    ///
    /// # Panics
    ///
    /// Panics if the cursor is not positioned at a node.
    pub fn remove_if(
        &mut self,
        f: impl FnOnce(&ListNode<T>) -> bool,
    ) -> Option<RcSlot<ListNode<T>>> {
        let Position::At(ptr) = self.position else {
            panic_cursor_not_at_node();
        };

        // SAFETY: ptr is a linked node at the cursor position.
        let node = unsafe { node_deref(ptr) };
        if f(node) { Some(self.remove()) } else { None }
    }
}
