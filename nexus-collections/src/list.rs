//! Doubly-linked list with internal node storage.
//!
//! Nodes are stored in external storage, with the list managing the links
//! internally. This allows O(1) insertion and removal without requiring
//! users to embed link fields in their types.
//!
//! # Storage Invariant
//!
//! A list instance must always be used with the same storage instance.
//! Passing a different storage is undefined behavior. This is the caller's
//! responsibility to enforce (same discipline as the `slab` crate).
//!
//! # Example
//!
//! ```
//! use nexus_collections::{BoxedListStorage, List};
//!
//! let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
//! let mut list: List<u64, BoxedListStorage<u64>> = List::new();
//!
//! // Insert values - returns index for O(1) access/removal later
//! let a = list.push_back(&mut storage, 1).unwrap();
//! let b = list.push_back(&mut storage, 2).unwrap();
//! let c = list.push_back(&mut storage, 3).unwrap();
//!
//! assert_eq!(list.len(), 3);
//! assert_eq!(list.get(&storage, b), Some(&2));
//!
//! // Remove from middle - O(1)
//! let value = list.remove(&mut storage, b);
//! assert_eq!(value, Some(2));
//! assert_eq!(list.len(), 2);
//!
//! // Pop from front
//! assert_eq!(list.pop_front(&mut storage), Some(1));
//! assert_eq!(list.pop_front(&mut storage), Some(3));
//! assert_eq!(list.pop_front(&mut storage), None);
//! ```
//!
//! # Moving Between Lists
//!
//! Use `unlink` and `link_back`/`link_front` to move nodes between lists
//! without deallocating. The storage index remains stable.
//!
//! ```
//! use nexus_collections::{BoxedListStorage, List};
//!
//! let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
//! let mut list_a: List<u64, BoxedListStorage<u64>> = List::new();
//! let mut list_b: List<u64, BoxedListStorage<u64>> = List::new();
//!
//! let idx = list_a.push_back(&mut storage, 42).unwrap();
//!
//! // Move to list_b - index stays valid
//! list_a.unlink(&mut storage, idx);
//! list_b.link_back(&mut storage, idx);
//!
//! assert!(list_a.is_empty());
//! assert_eq!(list_b.get(&storage, idx), Some(&42));
//! ```
//!
//! # Use Case: Order Queues
//!
//! Multiple price-level queues sharing one storage pool:
//!
//! ```
//! use nexus_collections::{BoxedListStorage, List};
//!
//! #[derive(Debug)]
//! struct Order {
//!     id: u64,
//!     qty: u64,
//! }
//!
//! // One storage for all orders
//! let mut orders: BoxedListStorage<Order> = BoxedListStorage::with_capacity(100_000);
//!
//! // Separate queues per price level
//! let mut queue_100: List<Order, BoxedListStorage<Order>> = List::new();
//! let mut queue_101: List<Order, BoxedListStorage<Order>> = List::new();
//!
//! let idx = queue_100.push_back(&mut orders, Order { id: 1, qty: 50 }).unwrap();
//!
//! // Price amendment: move order to different level
//! queue_100.unlink(&mut orders, idx);
//! queue_101.link_back(&mut orders, idx);
//! // Client's handle (idx) remains valid
//! ```

use std::marker::PhantomData;

use crate::{BoxedStorage, Index, Storage};

pub type BoxedListStorage<T, Idx = u32> = BoxedStorage<ListNode<T, Idx>, Idx>;
#[cfg(feature = "slab")]
pub type SlabListStorage<T> = slab::Slab<ListNode<T, usize>>;
#[cfg(feature = "nexus-slab")]
pub type NexusListStorage<T> = nexus_slab::Slab<ListNode<T, nexus_slab::Key>>;

/// A node in the linked list.
///
/// This wraps user data with prev/next links. Users interact with `&T` and `&mut T`
/// through the list's accessor methods; the node structure is an implementation detail.
#[derive(Debug)]
pub struct ListNode<T, Idx: Index = u32> {
    pub(crate) data: T,
    pub(crate) prev: Idx,
    pub(crate) next: Idx,
}

impl<T, Idx: Index> ListNode<T, Idx> {
    /// Creates a new unlinked node.
    #[inline]
    fn new(data: T) -> Self {
        Self {
            data,
            prev: Idx::NONE,
            next: Idx::NONE,
        }
    }
}

/// A doubly-linked list over external storage.
///
/// The list tracks head, tail, and length. Nodes live in user-provided
/// storage, wrapped in [`ListNode`].
///
/// # Type Parameters
///
/// - `T`: Element type
/// - `S`: Storage type (e.g., [`BoxedListStorage<T>`])
/// - `Idx`: Index type (default `u32`)
///
/// # Example
///
/// ```
/// use nexus_collections::{BoxedListStorage, List};
///
/// let mut storage: BoxedListStorage<String> = BoxedListStorage::with_capacity(100);
/// let mut list: List<String, BoxedListStorage<String>> = List::new();
///
/// let idx = list.push_back(&mut storage, "hello".into()).unwrap();
/// assert_eq!(list.get(&storage, idx), Some(&"hello".into()));
/// ```
#[derive(Debug)]
pub struct List<T, S, Idx: Index = u32>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    head: Idx,
    tail: Idx,
    len: usize,
    _marker: PhantomData<(T, S)>,
}

impl<T, S, Idx: Index> Default for List<T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, S, Idx: Index> List<T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    /// Creates an empty list.
    #[inline]
    pub const fn new() -> Self {
        Self {
            head: Idx::NONE,
            tail: Idx::NONE,
            len: 0,
            _marker: PhantomData,
        }
    }

    /// Returns the number of elements in the list.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the list is empty.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the head node's index, or `None` if empty.
    #[inline]
    pub fn front_idx(&self) -> Option<Idx> {
        if self.head.is_none() {
            None
        } else {
            Some(self.head)
        }
    }

    /// Returns the tail node's index, or `None` if empty.
    #[inline]
    pub fn back_idx(&self) -> Option<Idx> {
        if self.tail.is_none() {
            None
        } else {
            Some(self.tail)
        }
    }

    // ========================================================================
    // Insert operations (allocate + link)
    // ========================================================================

    /// Pushes a value to the back of the list.
    ///
    /// Returns the index of the inserted element.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn push_back(&mut self, storage: &mut S, value: T) -> Result<Idx, S::Error> {
        let idx = storage.try_insert(ListNode::new(value))?;
        self.link_back(storage, idx);
        Ok(idx)
    }

    /// Pushes a value to the front of the list.
    ///
    /// Returns the index of the inserted element.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn push_front(&mut self, storage: &mut S, value: T) -> Result<Idx, S::Error> {
        let idx = storage.try_insert(ListNode::new(value))?;
        self.link_front(storage, idx);
        Ok(idx)
    }

    /// Inserts a value after an existing node.
    ///
    /// Returns the index of the inserted element.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `after` is not valid in storage (debug builds only).
    #[inline]
    pub fn insert_after(&mut self, storage: &mut S, after: Idx, value: T) -> Result<Idx, S::Error> {
        let idx = storage.try_insert(ListNode::new(value))?;
        self.link_after(storage, after, idx);
        Ok(idx)
    }

    /// Inserts a value before an existing node.
    ///
    /// Returns the index of the inserted element.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `before` is not valid in storage (debug builds only).
    #[inline]
    pub fn insert_before(
        &mut self,
        storage: &mut S,
        before: Idx,
        value: T,
    ) -> Result<Idx, S::Error> {
        let idx = storage.try_insert(ListNode::new(value))?;
        self.link_before(storage, before, idx);
        Ok(idx)
    }

    // ========================================================================
    // Remove operations (unlink + deallocate)
    // ========================================================================

    /// Removes and returns the front element.
    ///
    /// Returns `None` if the list is empty.
    #[inline]
    pub fn pop_front(&mut self, storage: &mut S) -> Option<T> {
        if self.head.is_none() {
            return None;
        }

        let idx = self.head;
        self.unlink(storage, idx);
        storage.remove(idx).map(|node| node.data)
    }

    /// Removes and returns the back element.
    ///
    /// Returns `None` if the list is empty.
    #[inline]
    pub fn pop_back(&mut self, storage: &mut S) -> Option<T> {
        if self.tail.is_none() {
            return None;
        }

        let idx = self.tail;
        self.unlink(storage, idx);
        storage.remove(idx).map(|node| node.data)
    }

    /// Removes an element by index.
    ///
    /// Returns `None` if the index is invalid.
    #[inline]
    pub fn remove(&mut self, storage: &mut S, idx: Idx) -> Option<T> {
        if storage.get(idx).is_none() {
            return None;
        }

        self.unlink(storage, idx);
        storage.remove(idx).map(|node| node.data)
    }

    // ========================================================================
    // Link operations (just relink, no alloc/dealloc)
    // ========================================================================

    /// Links an existing node to the back of the list.
    ///
    /// The node must already exist in storage but not be in any list.
    /// Use this with `unlink` to move nodes between lists.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage (debug builds only).
    #[inline]
    pub fn link_back(&mut self, storage: &mut S, idx: Idx) {
        debug_assert!(storage.get(idx).is_some(), "invalid index");

        // Safety: caller guarantees idx is valid
        let node = unsafe { storage.get_unchecked_mut(idx) };
        node.prev = self.tail;
        node.next = Idx::NONE;

        if self.tail.is_some() {
            // Safety: tail is valid when is_some()
            unsafe { storage.get_unchecked_mut(self.tail) }.next = idx;
        } else {
            self.head = idx;
        }

        self.tail = idx;
        self.len += 1;
    }

    /// Links an existing node to the front of the list.
    ///
    /// The node must already exist in storage but not be in any list.
    /// Use this with `unlink` to move nodes between lists.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage (debug builds only).
    #[inline]
    pub fn link_front(&mut self, storage: &mut S, idx: Idx) {
        debug_assert!(storage.get(idx).is_some(), "invalid index");

        // Safety: caller guarantees idx is valid
        let node = unsafe { storage.get_unchecked_mut(idx) };
        node.next = self.head;
        node.prev = Idx::NONE;

        if self.head.is_some() {
            // Safety: head is valid when is_some()
            unsafe { storage.get_unchecked_mut(self.head) }.prev = idx;
        } else {
            self.tail = idx;
        }

        self.head = idx;
        self.len += 1;
    }

    /// Links an existing node after another node.
    ///
    /// # Panics
    ///
    /// Panics if `after` or `idx` is not valid in storage (debug builds only).
    #[inline]
    pub fn link_after(&mut self, storage: &mut S, after: Idx, idx: Idx) {
        debug_assert!(storage.get(after).is_some(), "invalid 'after' index");
        debug_assert!(storage.get(idx).is_some(), "invalid index");

        // Safety: after validated above
        let next = unsafe { storage.get_unchecked(after) }.next;

        // Safety: idx validated above
        let node = unsafe { storage.get_unchecked_mut(idx) };
        node.prev = after;
        node.next = next;

        // Safety: after validated above
        unsafe { storage.get_unchecked_mut(after) }.next = idx;

        if next.is_some() {
            // Safety: next is valid when is_some() (list invariant)
            unsafe { storage.get_unchecked_mut(next) }.prev = idx;
        } else {
            self.tail = idx;
        }

        self.len += 1;
    }

    /// Links an existing node before another node.
    ///
    /// # Panics
    ///
    /// Panics if `before` or `idx` is not valid in storage (debug builds only).
    #[inline]
    pub fn link_before(&mut self, storage: &mut S, before: Idx, idx: Idx) {
        debug_assert!(storage.get(before).is_some(), "invalid 'before' index");
        debug_assert!(storage.get(idx).is_some(), "invalid index");

        // Safety: before validated above
        let prev = unsafe { storage.get_unchecked(before) }.prev;

        // Safety: idx validated above
        let node = unsafe { storage.get_unchecked_mut(idx) };
        node.next = before;
        node.prev = prev;

        // Safety: before validated above
        unsafe { storage.get_unchecked_mut(before) }.prev = idx;

        if prev.is_some() {
            // Safety: prev is valid when is_some() (list invariant)
            unsafe { storage.get_unchecked_mut(prev) }.next = idx;
        } else {
            self.head = idx;
        }

        self.len += 1;
    }

    /// Unlinks a node from the list without deallocating.
    ///
    /// The node remains in storage and can be linked to another list.
    /// Use with `link_back`/`link_front` to move nodes between lists.
    ///
    /// Returns `true` if the node was in the list.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage (debug builds only).
    #[inline]
    pub fn unlink(&mut self, storage: &mut S, idx: Idx) -> bool {
        debug_assert!(storage.get(idx).is_some(), "invalid index");

        // Safety: caller guarantees idx is valid
        let node = unsafe { storage.get_unchecked(idx) };
        let prev = node.prev;
        let next = node.next;

        // Check if actually in a list (has links or is head/tail)
        let in_list = prev.is_some() || next.is_some() || self.head == idx;
        if !in_list {
            return false;
        }

        if prev.is_some() {
            // Safety: prev is valid when is_some() (list invariant)
            unsafe { storage.get_unchecked_mut(prev) }.next = next;
        } else {
            self.head = next;
        }

        if next.is_some() {
            // Safety: next is valid when is_some() (list invariant)
            unsafe { storage.get_unchecked_mut(next) }.prev = prev;
        } else {
            self.tail = prev;
        }

        // Clear the removed node's links
        // Safety: idx already validated
        let node = unsafe { storage.get_unchecked_mut(idx) };
        node.prev = Idx::NONE;
        node.next = Idx::NONE;

        self.len -= 1;
        true
    }

    // ========================================================================
    // Access
    // ========================================================================

    /// Returns a reference to the element at the given index.
    #[inline]
    pub fn get<'a>(&'a self, storage: &'a S, idx: Idx) -> Option<&'a T> {
        storage.get(idx).map(|node| &node.data)
    }

    /// Returns a mutable reference to the element at the given index.
    #[inline]
    pub fn get_mut<'a>(&'a mut self, storage: &'a mut S, idx: Idx) -> Option<&'a mut T> {
        storage.get_mut(idx).map(|node| &mut node.data)
    }

    /// Returns a reference to the front element.
    #[inline]
    pub fn front<'a>(&'a self, storage: &'a S) -> Option<&'a T> {
        if self.head.is_none() {
            None
        } else {
            // Safety: head is valid when is_some()
            Some(unsafe { &storage.get_unchecked(self.head).data })
        }
    }

    /// Returns a mutable reference to the front element.
    #[inline]
    pub fn front_mut<'a>(&'a mut self, storage: &'a mut S) -> Option<&'a mut T> {
        if self.head.is_none() {
            None
        } else {
            // Safety: head is valid when is_some()
            Some(unsafe { &mut storage.get_unchecked_mut(self.head).data })
        }
    }

    /// Returns a reference to the back element.
    #[inline]
    pub fn back<'a>(&'a self, storage: &'a S) -> Option<&'a T> {
        if self.tail.is_none() {
            None
        } else {
            // Safety: tail is valid when is_some()
            Some(unsafe { &storage.get_unchecked(self.tail).data })
        }
    }

    /// Returns a mutable reference to the back element.
    #[inline]
    pub fn back_mut<'a>(&'a mut self, storage: &'a mut S) -> Option<&'a mut T> {
        if self.tail.is_none() {
            None
        } else {
            // Safety: tail is valid when is_some()
            Some(unsafe { &mut storage.get_unchecked_mut(self.tail).data })
        }
    }

    // ========================================================================
    // Bulk operations
    // ========================================================================

    /// Clears the list, removing all elements.
    ///
    /// This unlinks and deallocates all nodes.
    pub fn clear(&mut self, storage: &mut S) {
        let mut idx = self.head;
        while idx.is_some() {
            // Safety: idx is valid (came from list traversal)
            let next = unsafe { storage.get_unchecked(idx) }.next;
            storage.remove(idx);
            idx = next;
        }

        self.head = Idx::NONE;
        self.tail = Idx::NONE;
        self.len = 0;
    }

    /// Appends `other` to the end of this list.
    ///
    /// After this operation, `other` will be empty. This is O(1).
    #[inline]
    pub fn append(&mut self, storage: &mut S, other: &mut Self) {
        if other.is_empty() {
            return;
        }

        if self.is_empty() {
            self.head = other.head;
            self.tail = other.tail;
            self.len = other.len;
        } else {
            // Safety: self.tail and other.head are valid (non-empty lists)
            unsafe { storage.get_unchecked_mut(self.tail) }.next = other.head;
            unsafe { storage.get_unchecked_mut(other.head) }.prev = self.tail;
            self.tail = other.tail;
            self.len += other.len;
        }

        other.head = Idx::NONE;
        other.tail = Idx::NONE;
        other.len = 0;
    }

    /// Moves a node to the back of the list.
    ///
    /// More efficient than `unlink` + `link_back` for repositioning.
    /// Useful for LRU caches.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage (debug builds only).
    #[inline]
    pub fn move_to_back(&mut self, storage: &mut S, idx: Idx) {
        // Already at back
        if self.tail == idx {
            return;
        }

        debug_assert!(storage.get(idx).is_some(), "invalid index");

        // Safety: idx validated above
        let node = unsafe { storage.get_unchecked(idx) };
        let prev = node.prev;
        let next = node.next;

        // Unlink from current position
        if prev.is_some() {
            // Safety: prev is valid (list invariant)
            unsafe { storage.get_unchecked_mut(prev) }.next = next;
        } else {
            self.head = next;
        }

        if next.is_some() {
            // Safety: next is valid (list invariant)
            unsafe { storage.get_unchecked_mut(next) }.prev = prev;
        }
        // Note: next can't be NONE here since we already checked idx != tail

        // Link at back
        // Safety: tail is valid (list is non-empty)
        unsafe { storage.get_unchecked_mut(self.tail) }.next = idx;

        // Safety: idx validated above
        let node = unsafe { storage.get_unchecked_mut(idx) };
        node.prev = self.tail;
        node.next = Idx::NONE;

        self.tail = idx;
    }

    /// Moves a node to the front of the list.
    ///
    /// More efficient than `unlink` + `link_front` for repositioning.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage (debug builds only).
    #[inline]
    pub fn move_to_front(&mut self, storage: &mut S, idx: Idx) {
        // Already at front
        if self.head == idx {
            return;
        }

        debug_assert!(storage.get(idx).is_some(), "invalid index");

        // Safety: idx validated above
        let node = unsafe { storage.get_unchecked(idx) };
        let prev = node.prev;
        let next = node.next;

        // Unlink from current position
        if prev.is_some() {
            // Safety: prev is valid (list invariant)
            unsafe { storage.get_unchecked_mut(prev) }.next = next;
        }
        // Note: prev can't be NONE here since we already checked idx != head

        if next.is_some() {
            // Safety: next is valid (list invariant)
            unsafe { storage.get_unchecked_mut(next) }.prev = prev;
        } else {
            self.tail = prev;
        }

        // Link at front
        // Safety: head is valid (list is non-empty)
        unsafe { storage.get_unchecked_mut(self.head) }.prev = idx;

        // Safety: idx validated above
        let node = unsafe { storage.get_unchecked_mut(idx) };
        node.next = self.head;
        node.prev = Idx::NONE;

        self.head = idx;
    }

    /// Splits the list at the given node.
    ///
    /// Returns a new list containing `idx` and all nodes after it.
    /// `self` will contain all nodes before `idx`.
    ///
    /// This is O(n) due to counting elements in the split portion.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage (debug builds only).
    #[inline]
    pub fn split_off(&mut self, storage: &mut S, idx: Idx) -> Self {
        debug_assert!(storage.get(idx).is_some(), "invalid index");

        // Splitting at head = take everything
        if self.head == idx {
            let other = Self {
                head: self.head,
                tail: self.tail,
                len: self.len,
                _marker: PhantomData,
            };
            self.head = Idx::NONE;
            self.tail = Idx::NONE;
            self.len = 0;
            return other;
        }

        // Safety: idx validated above
        let prev = unsafe { storage.get_unchecked(idx) }.prev;

        // Count nodes in the split-off portion
        let mut count = 0;
        let mut curr = idx;
        while curr.is_some() {
            count += 1;
            curr = unsafe { storage.get_unchecked(curr) }.next;
        }

        // Unlink at split point
        // Safety: prev is valid (idx != head, so prev.is_some())
        unsafe { storage.get_unchecked_mut(prev) }.next = Idx::NONE;
        unsafe { storage.get_unchecked_mut(idx) }.prev = Idx::NONE;

        let other = Self {
            head: idx,
            tail: self.tail,
            len: count,
            _marker: PhantomData,
        };

        self.tail = prev;
        self.len -= count;

        other
    }

    // ========================================================================
    // Position checks
    // ========================================================================

    /// Returns `true` if the node is currently the head of this list.
    #[inline]
    pub fn is_head(&self, idx: Idx) -> bool {
        self.head == idx
    }

    /// Returns `true` if the node is currently the tail of this list.
    #[inline]
    pub fn is_tail(&self, idx: Idx) -> bool {
        self.tail == idx
    }

    // ========================================================================
    // Navigation
    // ========================================================================

    /// Returns the index of the next node after `idx`.
    ///
    /// Returns `None` if `idx` is the tail or invalid.
    #[inline]
    pub fn next_idx(&self, storage: &S, idx: Idx) -> Option<Idx> {
        let next = storage.get(idx)?.next;
        if next.is_none() { None } else { Some(next) }
    }

    /// Returns the index of the previous node before `idx`.
    ///
    /// Returns `None` if `idx` is the head or invalid.
    #[inline]
    pub fn prev_idx(&self, storage: &S, idx: Idx) -> Option<Idx> {
        let prev = storage.get(idx)?.prev;
        if prev.is_none() { None } else { Some(prev) }
    }

    // ========================================================================
    // Iteration
    // ========================================================================

    /// Returns an iterator over references to elements, front to back.
    #[inline]
    pub fn iter<'a>(&self, storage: &'a S) -> Iter<'a, T, S, Idx> {
        Iter {
            storage,
            front: self.head,
            back: self.tail,
            _marker: PhantomData,
        }
    }

    /// Returns an iterator over mutable references to elements, front to back.
    #[inline]
    pub fn iter_mut<'a>(&self, storage: &'a mut S) -> IterMut<'a, T, S, Idx> {
        IterMut {
            storage,
            front: self.head,
            back: self.tail,
            _marker: PhantomData,
        }
    }

    /// Returns an iterator over indices, front to back.
    ///
    /// Useful when you need both the index and the value, or when you
    /// plan to modify the list during iteration (collect indices first).
    #[inline]
    pub fn indices<'a>(&self, storage: &'a S) -> Indices<'a, T, Idx, S> {
        Indices {
            storage,
            front: self.head,
            back: self.tail,
            _marker: PhantomData,
        }
    }

    /// Clears the list, returning an iterator over removed elements.
    ///
    /// The list is empty after this call. Elements are deallocated from
    /// storage as the iterator is consumed.
    #[inline]
    pub fn drain<'a>(&'a mut self, storage: &'a mut S) -> Drain<'a, T, S, Idx> {
        let head = self.head;
        self.head = Idx::NONE;
        self.tail = Idx::NONE;
        self.len = 0;

        Drain {
            storage,
            current: head,
            _marker: PhantomData,
        }
    }

    /// Returns a cursor positioned at the front of the list.
    ///
    /// The cursor allows mutable access and removal during iteration.
    /// See [`Cursor`] for usage examples.
    #[inline]
    pub fn cursor_front<'a>(&'a mut self, storage: &'a mut S) -> Cursor<'a, T, S, Idx> {
        let head = self.head;
        Cursor {
            list: self,
            storage,
            current: head,
        }
    }

    /// Returns a cursor positioned at the back of the list.
    #[inline]
    pub fn cursor_back<'a>(&'a mut self, storage: &'a mut S) -> Cursor<'a, T, S, Idx> {
        let tail = self.tail;
        Cursor {
            list: self,
            storage,
            current: tail,
        }
    }
}

/// A cursor providing mutable access to list elements with removal capability.
///
/// Useful for matching engine workflows where you walk a queue,
/// modify elements, and conditionally remove them.
///
/// # Example
///
/// ```
/// use nexus_collections::{BoxedListStorage, List};
///
/// #[derive(Debug)]
/// struct Order { qty: u64 }
///
/// let mut storage: BoxedListStorage<Order> = BoxedListStorage::with_capacity(100);
/// let mut queue: List<Order, BoxedListStorage<Order>> = List::new();
///
/// queue.push_back(&mut storage, Order { qty: 100 }).unwrap();
/// queue.push_back(&mut storage, Order { qty: 50 }).unwrap();
///
/// let mut incoming_qty = 120u64;
/// let mut cursor = queue.cursor_front(&mut storage);
///
/// while let Some(resting) = cursor.current_mut() {
///     let fill = incoming_qty.min(resting.qty);
///     resting.qty -= fill;
///     incoming_qty -= fill;
///
///     if resting.qty == 0 {
///         cursor.remove_current(); // Removes and advances
///     } else {
///         cursor.move_next();
///     }
///
///     if incoming_qty == 0 {
///         break;
///     }
/// }
/// ```
pub struct Cursor<'a, T, S, Idx: Index>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    list: &'a mut List<T, S, Idx>,
    storage: &'a mut S,
    current: Idx,
}

impl<'a, T, S, Idx: Index> Cursor<'a, T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    /// Returns a reference to the current element.
    ///
    /// Returns `None` if the cursor is exhausted (past end of list).
    #[inline]
    pub fn current(&self) -> Option<&T> {
        if self.current.is_none() {
            None
        } else {
            // Safety: current is valid when not NONE
            Some(unsafe { &self.storage.get_unchecked(self.current).data })
        }
    }

    /// Returns a mutable reference to the current element.
    ///
    /// Returns `None` if the cursor is exhausted (past end of list).
    #[inline]
    pub fn current_mut(&mut self) -> Option<&mut T> {
        if self.current.is_none() {
            None
        } else {
            // Safety: current is valid when not NONE
            Some(unsafe { &mut self.storage.get_unchecked_mut(self.current).data })
        }
    }

    /// Returns the index of the current element.
    ///
    /// Returns `None` if the cursor is exhausted.
    #[inline]
    pub fn index(&self) -> Option<Idx> {
        if self.current.is_none() {
            None
        } else {
            Some(self.current)
        }
    }

    /// Advances the cursor to the next element.
    ///
    /// If already at end, cursor remains exhausted.
    #[inline]
    pub fn move_next(&mut self) {
        if self.current.is_some() {
            // Safety: current is valid when not NONE
            self.current = unsafe { self.storage.get_unchecked(self.current) }.next;
        }
    }

    /// Moves the cursor to the previous element.
    ///
    /// If already at start, cursor remains at start.
    #[inline]
    pub fn move_prev(&mut self) {
        if self.current.is_some() {
            // Safety: current is valid when not NONE
            self.current = unsafe { self.storage.get_unchecked(self.current) }.prev;
        }
    }

    /// Removes the current element and advances to the next.
    ///
    /// Returns the removed value, or `None` if cursor is exhausted.
    /// After removal, cursor points to what was the next element.
    #[inline]
    pub fn remove_current(&mut self) -> Option<T> {
        if self.current.is_none() {
            return None;
        }

        let idx = self.current;
        // Safety: current is valid (cursor invariant)
        let next = unsafe { self.storage.get_unchecked(idx) }.next;

        self.list.unlink(self.storage, idx);
        self.current = next;

        // Safety: idx was valid, we just unlinked it
        let node = unsafe { self.storage.remove_unchecked(idx) };
        Some(node.data)
    }

    /// Returns `true` if the cursor is exhausted (no current element).
    #[inline]
    pub fn is_exhausted(&self) -> bool {
        self.current.is_none()
    }

    /// Peeks at the next element without advancing.
    ///
    /// Returns `None` if at end or cursor is exhausted.
    #[inline]
    pub fn peek_next(&self) -> Option<&T> {
        if self.current.is_none() {
            return None;
        }
        // Safety: current is valid
        let next = unsafe { self.storage.get_unchecked(self.current) }.next;
        if next.is_none() {
            None
        } else {
            // Safety: next is valid when not NONE
            Some(unsafe { &self.storage.get_unchecked(next).data })
        }
    }
}

// ============================================================================
// Iterators
// ============================================================================

/// Iterator over references to list elements.
pub struct Iter<'a, T, S, Idx: Index> {
    storage: &'a S,
    front: Idx,
    back: Idx,
    _marker: PhantomData<T>,
}

impl<'a, T: 'a, S, Idx: Index + 'a> Iterator for Iter<'a, T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.front.is_none() {
            return None;
        }

        // Safety: list invariants guarantee front is valid
        let node = unsafe { self.storage.get_unchecked(self.front) };

        // Check if we've met in the middle
        if self.front == self.back {
            self.front = Idx::NONE;
            self.back = Idx::NONE;
        } else {
            self.front = node.next;
        }

        Some(&node.data)
    }
}

impl<'a, T: 'a, S, Idx: Index + 'a> DoubleEndedIterator for Iter<'a, T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.back.is_none() {
            return None;
        }

        // Safety: list invariants guarantee back is valid
        let node = unsafe { self.storage.get_unchecked(self.back) };

        // Check if we've met in the middle
        if self.front == self.back {
            self.front = Idx::NONE;
            self.back = Idx::NONE;
        } else {
            self.back = node.prev;
        }

        Some(&node.data)
    }
}

/// Iterator over mutable references to list elements.
pub struct IterMut<'a, T, S, Idx: Index + 'a> {
    storage: &'a mut S,
    front: Idx,
    back: Idx,
    _marker: PhantomData<T>,
}

impl<'a, T: 'a, S, Idx: Index + 'a> Iterator for IterMut<'a, T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.front.is_none() {
            return None;
        }

        // Safety: list invariants guarantee front is valid
        let node = unsafe { self.storage.get_unchecked_mut(self.front) };

        // Check if we've met in the middle
        if self.front == self.back {
            self.front = Idx::NONE;
            self.back = Idx::NONE;
        } else {
            self.front = node.next;
        }

        // Extend lifetime - safe because we visit each node exactly once
        Some(unsafe { &mut *((&mut node.data) as *mut T) })
    }
}

impl<'a, T: 'a, S, Idx: Index + 'a> DoubleEndedIterator for IterMut<'a, T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.back.is_none() {
            return None;
        }

        // Safety: list invariants guarantee back is valid
        let node = unsafe { self.storage.get_unchecked_mut(self.back) };

        // Check if we've met in the middle
        if self.front == self.back {
            self.front = Idx::NONE;
            self.back = Idx::NONE;
        } else {
            self.back = node.prev;
        }

        // Extend lifetime - safe because we visit each node exactly once
        Some(unsafe { &mut *((&mut node.data) as *mut T) })
    }
}

/// Iterator over indices in the list.
pub struct Indices<'a, T, Idx: Index, S> {
    storage: &'a S,
    front: Idx,
    back: Idx,
    _marker: PhantomData<T>,
}

impl<'a, T, Idx: Index, S> Iterator for Indices<'a, T, Idx, S>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    type Item = Idx;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.front.is_none() {
            return None;
        }

        let idx = self.front;
        // Safety: list invariants guarantee front is valid
        let node = unsafe { self.storage.get_unchecked(self.front) };

        if self.front == self.back {
            self.front = Idx::NONE;
            self.back = Idx::NONE;
        } else {
            self.front = node.next;
        }

        Some(idx)
    }
}

impl<'a, T, Idx: Index, S> DoubleEndedIterator for Indices<'a, T, Idx, S>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.back.is_none() {
            return None;
        }

        let idx = self.back;
        // Safety: list invariants guarantee back is valid
        let node = unsafe { self.storage.get_unchecked(self.back) };

        if self.front == self.back {
            self.front = Idx::NONE;
            self.back = Idx::NONE;
        } else {
            self.back = node.prev;
        }

        Some(idx)
    }
}

/// Iterator that removes and returns elements from a list.
pub struct Drain<'a, T, S, Idx: Index>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    storage: &'a mut S,
    current: Idx,
    _marker: PhantomData<T>,
}

impl<'a, T, S, Idx: Index> Iterator for Drain<'a, T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.current.is_none() {
            return None;
        }

        let idx = self.current;
        // Safety: current came from list traversal, must be valid
        self.current = unsafe { self.storage.get_unchecked(idx) }.next;
        self.storage.remove(idx).map(|node| node.data)
    }
}

impl<T, S, Idx: Index> Drop for Drain<'_, T, S, Idx>
where
    S: Storage<ListNode<T, Idx>, Index = Idx>,
{
    fn drop(&mut self) {
        // Exhaust remaining elements to ensure cleanup
        for _ in self.by_ref() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_list_is_empty() {
        let list: List<u64, BoxedListStorage<u64>> = List::new();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert!(list.front_idx().is_none());
        assert!(list.back_idx().is_none());
    }

    #[test]
    fn push_back_single() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();

        assert_eq!(list.len(), 1);
        assert_eq!(list.front_idx(), Some(a));
        assert_eq!(list.back_idx(), Some(a));
        assert_eq!(list.get(&storage, a), Some(&1));
        assert!(list.front(&storage).is_some_and(|&front| front == 1));
        assert!(list.back(&storage).is_some_and(|&back| back == 1));
    }

    #[test]
    fn push_back_multiple() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let _b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        assert_eq!(list.len(), 3);
        assert_eq!(list.front_idx(), Some(a));
        assert_eq!(list.back_idx(), Some(c));

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![1, 2, 3]);
    }

    #[test]
    fn push_front_multiple() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_front(&mut storage, 1).unwrap();
        let _b = list.push_front(&mut storage, 2).unwrap();
        let c = list.push_front(&mut storage, 3).unwrap();

        assert_eq!(list.len(), 3);
        assert_eq!(list.front_idx(), Some(c));
        assert_eq!(list.back_idx(), Some(a));

        // Order should be 3, 2, 1
        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![3, 2, 1]);
    }

    #[test]
    fn pop_front() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        assert_eq!(list.pop_front(&mut storage), Some(1));
        assert_eq!(list.len(), 2);

        assert_eq!(list.pop_front(&mut storage), Some(2));
        assert_eq!(list.pop_front(&mut storage), Some(3));
        assert_eq!(list.pop_front(&mut storage), None);
        assert!(list.is_empty());
    }

    #[test]
    fn pop_back() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();

        assert_eq!(list.pop_back(&mut storage), Some(2));
        assert_eq!(list.len(), 1);

        assert_eq!(list.pop_back(&mut storage), Some(1));
        assert!(list.is_empty());
    }

    #[test]
    fn remove_middle() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let _a = list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        let _c = list.push_back(&mut storage, 3).unwrap();

        assert_eq!(list.remove(&mut storage, b), Some(2));
        assert_eq!(list.len(), 2);

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![1, 3]);
    }

    #[test]
    fn unlink_and_link_to_another_list() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list_a: List<u64, _> = List::new();
        let mut list_b: List<u64, _> = List::new();

        let idx = list_a.push_back(&mut storage, 42).unwrap();
        list_a.push_back(&mut storage, 99).unwrap();

        // Move idx to list_b
        assert!(list_a.unlink(&mut storage, idx));
        list_b.link_back(&mut storage, idx);

        assert_eq!(list_a.len(), 1);
        assert_eq!(list_b.len(), 1);
        assert_eq!(list_b.get(&storage, idx), Some(&42));

        // Original index still works
        assert_eq!(storage.get(idx).map(|n| &n.data), Some(&42));
    }

    #[test]
    fn unlink_not_in_list() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let idx = list.push_back(&mut storage, 1).unwrap();
        list.unlink(&mut storage, idx);

        // Second unlink should return false
        assert!(!list.unlink(&mut storage, idx));
    }

    #[test]
    fn get_and_get_mut() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 10).unwrap();

        assert_eq!(list.get(&storage, a), Some(&10));

        *list.get_mut(&mut storage, a).unwrap() = 20;
        assert_eq!(list.get(&storage, a), Some(&20));
    }

    #[test]
    fn front_and_back() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        assert!(list.front(&storage).is_none());
        assert!(list.back(&storage).is_none());

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        assert_eq!(list.front(&storage), Some(&1));
        assert_eq!(list.back(&storage), Some(&3));
    }

    #[test]
    fn insert_after() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let _c = list.push_back(&mut storage, 3).unwrap();
        let _b = list.insert_after(&mut storage, a, 2).unwrap();

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![1, 2, 3]);
    }

    #[test]
    fn insert_before() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let _a = list.push_back(&mut storage, 1).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();
        let _b = list.insert_before(&mut storage, c, 2).unwrap();

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![1, 2, 3]);
    }

    #[test]
    fn clear() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        list.clear(&mut storage);

        assert!(list.is_empty());
        assert!(list.front_idx().is_none());
        assert!(list.back_idx().is_none());
    }

    #[test]
    fn append() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list1: List<u64, _> = List::new();
        let mut list2: List<u64, _> = List::new();

        list1.push_back(&mut storage, 1).unwrap();
        list1.push_back(&mut storage, 2).unwrap();
        list2.push_back(&mut storage, 3).unwrap();
        list2.push_back(&mut storage, 4).unwrap();

        list1.append(&mut storage, &mut list2);

        assert_eq!(list1.len(), 4);
        assert!(list2.is_empty());

        let values: Vec<_> = list1.iter(&storage).copied().collect();
        assert_eq!(values, vec![1, 2, 3, 4]);
    }

    #[test]
    fn move_to_back() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        list.move_to_back(&mut storage, a);

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![2, 3, 1]);
    }

    #[test]
    fn move_to_front() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        list.move_to_front(&mut storage, c);

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![3, 1, 2]);
    }

    #[test]
    fn split_off() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        let tail = list.split_off(&mut storage, b);

        assert_eq!(list.len(), 1);
        let values1: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values1, vec![1]);

        assert_eq!(tail.len(), 2);
        let values2: Vec<_> = tail.iter(&storage).copied().collect();
        assert_eq!(values2, vec![2, 3]);
    }

    #[test]
    fn is_head_and_is_tail() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        assert!(list.is_head(a));
        assert!(!list.is_head(b));
        assert!(!list.is_head(c));

        assert!(!list.is_tail(a));
        assert!(!list.is_tail(b));
        assert!(list.is_tail(c));
    }

    #[test]
    fn iter_empty() {
        let storage = BoxedListStorage::with_capacity(16);
        let list: List<u64, _> = List::new();

        assert_eq!(list.iter(&storage).count(), 0);
    }

    #[test]
    fn iter_mut() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        for val in list.iter_mut(&mut storage) {
            *val *= 10;
        }

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![10, 20, 30]);
    }

    #[test]
    fn indices_iterator() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        let indices: Vec<_> = list.indices(&storage).collect();
        assert_eq!(indices, vec![a, b, c]);
    }

    #[test]
    fn storage_reuse_after_remove() {
        let mut storage = BoxedListStorage::with_capacity(4);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let _b = list.push_back(&mut storage, 2).unwrap();

        list.remove(&mut storage, a);

        // Should be able to insert again
        let c = list.push_back(&mut storage, 3).unwrap();
        assert_eq!(c, a); // Reused slot

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![2, 3]);
    }

    // ============================================================================
    // Cursor tests
    // ============================================================================

    #[test]
    fn cursor_basic_navigation() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        let mut cursor = list.cursor_front(&mut storage);

        assert_eq!(cursor.index(), Some(a));
        assert_eq!(cursor.current(), Some(&1));

        cursor.move_next();
        assert_eq!(cursor.index(), Some(b));
        assert_eq!(cursor.current(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.index(), Some(c));
        assert_eq!(cursor.current(), Some(&3));

        cursor.move_next();
        assert!(cursor.is_exhausted());
        assert_eq!(cursor.current(), None);
    }

    #[test]
    fn cursor_move_prev() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        let mut cursor = list.cursor_back(&mut storage);

        assert_eq!(cursor.index(), Some(c));
        cursor.move_prev();
        assert_eq!(cursor.index(), Some(b));
        cursor.move_prev();
        assert_eq!(cursor.index(), Some(a));
        cursor.move_prev();
        assert!(cursor.is_exhausted());
    }

    #[test]
    fn cursor_current_mut() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 10).unwrap();
        list.push_back(&mut storage, 20).unwrap();

        let mut cursor = list.cursor_front(&mut storage);
        *cursor.current_mut().unwrap() = 100;
        cursor.move_next();
        *cursor.current_mut().unwrap() = 200;

        drop(cursor);

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![100, 200]);
    }

    #[test]
    fn cursor_remove_current() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        let mut cursor = list.cursor_front(&mut storage);

        // Remove first element
        assert_eq!(cursor.remove_current(), Some(1));
        assert_eq!(cursor.index(), Some(b)); // Advanced to b

        // Remove second element (now first)
        assert_eq!(cursor.remove_current(), Some(2));
        assert_eq!(cursor.index(), Some(c)); // Advanced to c

        // Remove last element
        assert_eq!(cursor.remove_current(), Some(3));
        assert!(cursor.is_exhausted());

        assert!(list.is_empty());
    }

    #[test]
    fn cursor_remove_middle() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        let mut cursor = list.cursor_front(&mut storage);
        cursor.move_next(); // Move to middle

        assert_eq!(cursor.remove_current(), Some(2));
        assert_eq!(cursor.current(), Some(&3)); // Now at what was third

        drop(cursor);

        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![1, 3]);
    }

    #[test]
    fn cursor_peek_next() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        let mut cursor = list.cursor_front(&mut storage);

        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.move_next();
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), None); // At tail
    }

    #[test]
    fn cursor_empty_list() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let mut cursor = list.cursor_front(&mut storage);

        assert!(cursor.is_exhausted());
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.index(), None);
        assert_eq!(cursor.remove_current(), None);
    }

    #[test]
    fn cursor_single_element() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 42).unwrap();

        let mut cursor = list.cursor_front(&mut storage);

        assert_eq!(cursor.current(), Some(&42));
        assert_eq!(cursor.peek_next(), None);

        assert_eq!(cursor.remove_current(), Some(42));
        assert!(cursor.is_exhausted());
        assert!(list.is_empty());
    }

    #[test]
    fn cursor_matching_workflow() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        // Resting orders: 100, 50, 75
        list.push_back(&mut storage, 100).unwrap();
        list.push_back(&mut storage, 50).unwrap();
        list.push_back(&mut storage, 75).unwrap();

        // Incoming order wants to fill 120
        let mut remaining = 120u64;
        let mut cursor = list.cursor_front(&mut storage);

        while let Some(resting) = cursor.current_mut() {
            let fill = remaining.min(*resting);
            *resting -= fill;
            remaining -= fill;

            if *resting == 0 {
                cursor.remove_current();
            } else {
                cursor.move_next();
            }

            if remaining == 0 {
                break;
            }
        }

        assert_eq!(remaining, 0);
        drop(cursor);

        // First order (100) fully filled and removed
        // Second order (50) partially filled, 30 remaining
        let values: Vec<_> = list.iter(&storage).copied().collect();
        assert_eq!(values, vec![30, 75]);
    }

    // ============================================================================
    // Iterator tests
    // ============================================================================

    #[test]
    fn iter_rev() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        let values: Vec<_> = list.iter(&storage).rev().copied().collect();
        assert_eq!(values, vec![3, 2, 1]);
    }

    #[test]
    fn iter_double_ended() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();
        list.push_back(&mut storage, 4).unwrap();

        let mut iter = list.iter(&storage);
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next_back(), Some(&4));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn indices_rev() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        let indices: Vec<_> = list.indices(&storage).rev().collect();
        assert_eq!(indices, vec![c, b, a]);
    }

    #[test]
    fn drain_all() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        let values: Vec<_> = list.drain(&mut storage).collect();
        assert_eq!(values, vec![1, 2, 3]);

        assert!(list.is_empty());
        assert!(storage.is_empty());
    }

    #[test]
    fn drain_partial_then_drop() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        list.push_back(&mut storage, 1).unwrap();
        list.push_back(&mut storage, 2).unwrap();
        list.push_back(&mut storage, 3).unwrap();

        {
            let mut drain = list.drain(&mut storage);
            assert_eq!(drain.next(), Some(1));
            // Drop drain without consuming all
        }

        // Storage should still be cleaned up
        assert!(list.is_empty());
        assert!(storage.is_empty());
    }

    #[test]
    fn next_idx_and_prev_idx() {
        let mut storage = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, _> = List::new();

        let a = list.push_back(&mut storage, 1).unwrap();
        let b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        assert_eq!(list.next_idx(&storage, a), Some(b));
        assert_eq!(list.next_idx(&storage, b), Some(c));
        assert_eq!(list.next_idx(&storage, c), None);

        assert_eq!(list.prev_idx(&storage, a), None);
        assert_eq!(list.prev_idx(&storage, b), Some(a));
        assert_eq!(list.prev_idx(&storage, c), Some(b));
    }
}

#[cfg(test)]
mod bench {
    use super::*;
    use hdrhistogram::Histogram;

    #[inline]
    fn rdtscp() -> u64 {
        #[cfg(target_arch = "x86_64")]
        unsafe {
            core::arch::x86_64::__rdtscp(&mut 0)
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            // Fallback for non-x86
            std::time::Instant::now().elapsed().as_nanos() as u64
        }
    }

    fn print_histogram(name: &str, hist: &Histogram<u64>) {
        println!(
            "{:24} p50: {:4} cycles | p99: {:4} cycles | p999: {:5} cycles | min: {:4} | max: {:5}",
            name,
            hist.value_at_quantile(0.50),
            hist.value_at_quantile(0.99),
            hist.value_at_quantile(0.999),
            hist.min(),
            hist.max(),
        );
    }

    const WARMUP: usize = 10_000;
    const ITERATIONS: usize = 100_000;

    /// Benchmark push_back into empty list, then pop to reset.
    ///
    /// Run with:
    /// ```bash
    /// echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
    /// cargo test --release bench_push_back -- --ignored --nocapture
    /// ```
    #[test]
    #[ignore]
    fn bench_list_push_back() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for i in 0..WARMUP {
            let _ = list.push_back(&mut storage, i as u64);
            let _ = list.pop_back(&mut storage);
        }

        // Measure
        for i in 0..ITERATIONS {
            let start = rdtscp();
            let _ = list.push_back(&mut storage, i as u64);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
            let _ = list.pop_back(&mut storage);
        }

        print_histogram("push_back", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_push_front() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..WARMUP {
            let _ = list.push_front(&mut storage, i as u64);
            let _ = list.pop_front(&mut storage);
        }

        for i in 0..ITERATIONS {
            let start = rdtscp();
            let _ = list.push_front(&mut storage, i as u64);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
            let _ = list.pop_front(&mut storage);
        }

        print_histogram("push_front", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_pop_front() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for _ in 0..WARMUP {
            let _ = list.push_back(&mut storage, 1);
            let _ = list.pop_front(&mut storage);
        }

        for i in 0..ITERATIONS {
            let _ = list.push_back(&mut storage, i as u64);
            let start = rdtscp();
            let _ = list.pop_front(&mut storage);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("pop_front", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_pop_back() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for _ in 0..WARMUP {
            let _ = list.push_back(&mut storage, 1);
            let _ = list.pop_back(&mut storage);
        }

        for i in 0..ITERATIONS {
            let _ = list.push_back(&mut storage, i as u64);
            let start = rdtscp();
            let _ = list.pop_back(&mut storage);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("pop_back", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_get() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(1024);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Build list with 1000 elements
        let mut indices = Vec::with_capacity(1000);
        for i in 0..1000 {
            indices.push(list.push_back(&mut storage, i as u64).unwrap());
        }

        // Warmup - access middle element
        let mid_idx = indices[500];
        for _ in 0..WARMUP {
            std::hint::black_box(list.get(&storage, mid_idx));
        }

        // Measure
        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(list.get(&storage, mid_idx));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("get (middle)", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_remove_middle() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for _ in 0..WARMUP {
            let a = list.push_back(&mut storage, 1).unwrap();
            let b = list.push_back(&mut storage, 2).unwrap();
            let c = list.push_back(&mut storage, 3).unwrap();
            let _ = list.remove(&mut storage, b); // Remove middle
            let _ = list.remove(&mut storage, a);
            let _ = list.remove(&mut storage, c);
        }

        // Measure
        for _ in 0..ITERATIONS {
            let a = list.push_back(&mut storage, 1).unwrap();
            let b = list.push_back(&mut storage, 2).unwrap();
            let c = list.push_back(&mut storage, 3).unwrap();

            let start = rdtscp();
            let _ = list.remove(&mut storage, b);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            let _ = list.remove(&mut storage, a);
            let _ = list.remove(&mut storage, c);
        }

        print_histogram("remove (middle)", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_unlink() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for _ in 0..WARMUP {
            let idx = list.push_back(&mut storage, 1).unwrap();
            list.unlink(&mut storage, idx);
            storage.remove(idx);
        }

        // Measure
        for _ in 0..ITERATIONS {
            let idx = list.push_back(&mut storage, 1).unwrap();

            let start = rdtscp();
            list.unlink(&mut storage, idx);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            storage.remove(idx);
        }

        print_histogram("unlink", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_link_back() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for _ in 0..WARMUP {
            let idx = list.push_back(&mut storage, 1).unwrap();
            list.unlink(&mut storage, idx);
            list.link_back(&mut storage, idx);
            list.remove(&mut storage, idx);
        }

        // Measure
        for _ in 0..ITERATIONS {
            let idx = list.push_back(&mut storage, 1).unwrap();
            list.unlink(&mut storage, idx);

            let start = rdtscp();
            list.link_back(&mut storage, idx);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            list.remove(&mut storage, idx);
        }

        print_histogram("link_back", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_link_front() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for _ in 0..WARMUP {
            let idx = list.push_back(&mut storage, 1).unwrap();
            list.unlink(&mut storage, idx);
            list.link_front(&mut storage, idx);
            list.remove(&mut storage, idx);
        }

        // Measure
        for _ in 0..ITERATIONS {
            let idx = list.push_back(&mut storage, 1).unwrap();
            list.unlink(&mut storage, idx);

            let start = rdtscp();
            list.link_front(&mut storage, idx);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            list.remove(&mut storage, idx);
        }

        print_histogram("link_front", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_move_to_back() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Setup: list with 3 elements
        let a = list.push_back(&mut storage, 1).unwrap();
        let _b = list.push_back(&mut storage, 2).unwrap();
        let _c = list.push_back(&mut storage, 3).unwrap();

        // Warmup
        for _ in 0..WARMUP {
            list.move_to_back(&mut storage, a);
        }

        // Measure - move front element to back repeatedly
        for _ in 0..ITERATIONS {
            let front = list.front_idx().unwrap();
            let start = rdtscp();
            list.move_to_back(&mut storage, front);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("move_to_back", &hist);
    }

    #[test]
    #[ignore]
    fn bench_list_move_to_front() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
        let mut list: List<u64, BoxedListStorage<u64>> = List::new();
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Setup: list with 3 elements
        let _a = list.push_back(&mut storage, 1).unwrap();
        let _b = list.push_back(&mut storage, 2).unwrap();
        let c = list.push_back(&mut storage, 3).unwrap();

        // Warmup
        for _ in 0..WARMUP {
            list.move_to_front(&mut storage, c);
        }

        // Measure - move back element to front repeatedly
        for _ in 0..ITERATIONS {
            let back = list.back_idx().unwrap();
            let start = rdtscp();
            list.move_to_front(&mut storage, back);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("move_to_front", &hist);
    }

    /// Combined benchmark: simulates order queue workflow
    /// (insert, access, move between queues, remove)
    #[test]
    #[ignore]
    fn bench_list_order_queue_workflow() {
        let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(32);
        let mut queue_a: List<u64, BoxedListStorage<u64>> = List::new();
        let mut queue_b: List<u64, BoxedListStorage<u64>> = List::new();

        let mut hist_insert = Histogram::<u64>::new(3).unwrap();
        let mut hist_move = Histogram::<u64>::new(3).unwrap();
        let mut hist_cancel = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for i in 0..WARMUP {
            let idx = queue_a.push_back(&mut storage, i as u64).unwrap();
            queue_a.unlink(&mut storage, idx);
            queue_b.link_back(&mut storage, idx);
            queue_b.remove(&mut storage, idx);
        }

        // Measure
        for i in 0..ITERATIONS {
            // Insert (new order)
            let start = rdtscp();
            let idx = queue_a.push_back(&mut storage, i as u64).unwrap();
            hist_insert.record(rdtscp() - start).unwrap();

            // Move (price amendment)
            let start = rdtscp();
            queue_a.unlink(&mut storage, idx);
            queue_b.link_back(&mut storage, idx);
            hist_move.record(rdtscp() - start).unwrap();

            // Cancel
            let start = rdtscp();
            queue_b.remove(&mut storage, idx);
            hist_cancel.record(rdtscp() - start).unwrap();
        }

        println!("\n=== Order Queue Workflow ===");
        print_histogram("insert (new order)", &hist_insert);
        print_histogram("move (amendment)", &hist_move);
        print_histogram("cancel", &hist_cancel);
    }

    /// Run all benchmarks together
    #[test]
    #[ignore]
    fn bench_list_all() {
        println!("\n=== List Benchmarks ===");
        println!("Run with: cargo test --release bench_list_all -- --ignored --nocapture\n");

        bench_list_push_back();
        bench_list_push_front();
        bench_list_pop_front();
        bench_list_pop_back();
        bench_list_get();
        bench_list_remove_middle();
        bench_list_unlink();
        bench_list_link_back();
        bench_list_link_front();
        bench_list_move_to_back();
        bench_list_move_to_front();

        println!();
        bench_list_order_queue_workflow();
    }
}
