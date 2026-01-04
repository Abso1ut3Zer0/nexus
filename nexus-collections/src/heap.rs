//! Min-heap with stable handles for O(log n) removal and priority updates.
//!
//! Nodes are stored in external storage, with the heap managing ordering
//! via an internal index vector. This enables O(1) handle-based access
//! and O(log n) removal/priority updates.
//!
//! # Storage Invariant
//!
//! A heap instance must always be used with the same storage instance.
//! Passing a different storage is undefined behavior.
//!
//! # Ordering Invariant
//!
//! Do not mutate the ordering key of elements via direct storage access
//! without calling [`update_key`](Heap::update_key), [`decrease_key`](Heap::decrease_key),
//! or [`increase_key`](Heap::increase_key) afterward.
//!
//! # Bounded vs Unbounded Storage
//!
//! Push operations have different APIs depending on storage type:
//!
//! ```
//! use nexus_collections::{BoxedHeapStorage, Heap};
//!
//! // Bounded storage (BoxedStorage, nexus_slab) - fallible insertion
//! let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(16);
//! let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::new();
//!
//! let key = heap.try_push(&mut storage, 42).unwrap();
//! assert_eq!(heap.peek(&storage), Some(&42));
//! ```
//!
//! ```ignore
//! // Unbounded storage (slab::Slab) - infallible insertion
//! let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
//! let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::new();
//!
//! let key = heap.push(&mut storage, 42); // No Result!
//! ```
//!
//! # Example
//!
//! ```
//! use nexus_collections::{BoxedHeapStorage, Heap};
//!
//! let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(16);
//! let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::new();
//!
//! let a = heap.try_push(&mut storage, 3).unwrap();
//! let b = heap.try_push(&mut storage, 1).unwrap();
//! let c = heap.try_push(&mut storage, 2).unwrap();
//!
//! assert_eq!(heap.peek(&storage), Some(&1));
//! assert_eq!(heap.pop(&mut storage), Some(1));
//! assert_eq!(heap.pop(&mut storage), Some(2));
//!
//! // Remove by handle - O(log n)
//! assert_eq!(heap.remove(&mut storage, a), Some(3));
//! ```

use std::marker::PhantomData;

use crate::{BoundedStorage, BoxedStorage, Full, Key, Storage, UnboundedStorage};

/// Type alias for bounded heap storage backed by a boxed allocation.
pub type BoxedHeapStorage<T, K = u32> = BoxedStorage<HeapNode<T, K>, K>;

/// Type alias for unbounded heap storage backed by `slab::Slab`.
#[cfg(feature = "slab")]
pub type SlabHeapStorage<T> = slab::Slab<HeapNode<T, usize>>;

/// Type alias for bounded heap storage backed by `nexus_slab::Slab`.
#[cfg(feature = "nexus-slab")]
pub type NexusHeapStorage<T> = nexus_slab::Slab<HeapNode<T, nexus_slab::Key>>;

/// A node in the heap. Wraps user data with heap position tracking.
#[derive(Debug)]
pub struct HeapNode<T, K: Key = u32> {
    pub(crate) data: T,
    pub(crate) heap_pos: K, // position in indices vec, or K::NONE if not in heap
}

impl<T, K: Key> HeapNode<T, K> {
    #[inline]
    fn new(data: T) -> Self {
        Self {
            data,
            heap_pos: K::NONE,
        }
    }
}

/// A min-heap over external storage with O(log n) handle operations.
///
/// # Type Parameters
///
/// - `T`: Element type (must implement `Ord`)
/// - `S`: Storage type (e.g., [`BoxedHeapStorage<T>`])
/// - `K`: Key type (default `u32`)
#[derive(Debug)]
pub struct Heap<T: Ord, S, K: Key = u32>
where
    S: Storage<HeapNode<T, K>, Key = K>,
{
    indices: Vec<K>,
    _marker: PhantomData<(T, S)>,
}

impl<T: Ord, S, K: Key> Default for Heap<T, S, K>
where
    S: Storage<HeapNode<T, K>, Key = K>,
{
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Base impl - works with any Storage (read/remove/update operations)
// =============================================================================

impl<T: Ord, S, K: Key> Heap<T, S, K>
where
    S: Storage<HeapNode<T, K>, Key = K>,
{
    /// Creates an empty heap.
    #[inline]
    pub const fn new() -> Self {
        Self {
            indices: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// Creates an empty heap with pre-allocated capacity for the index vector.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            indices: Vec::with_capacity(capacity),
            _marker: PhantomData,
        }
    }

    /// Returns the number of elements in the heap.
    #[inline]
    pub fn len(&self) -> usize {
        self.indices.len()
    }

    /// Returns `true` if the heap is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.indices.is_empty()
    }

    // ========================================================================
    // Core operations
    // ========================================================================

    /// Removes and returns the minimum element.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn pop(&mut self, storage: &mut S) -> Option<T> {
        if self.indices.is_empty() {
            return None;
        }

        let storage_key = self.indices[0];

        // Swap with last and remove
        let last_pos = self.indices.len() - 1;
        if last_pos > 0 {
            self.swap_positions(storage, 0, last_pos);
        }
        self.indices.pop();

        // Clear heap position and remove from storage
        // Safety: storage_key came from our indices
        unsafe { storage.get_unchecked_mut(storage_key) }.heap_pos = K::NONE;
        let node = storage.remove(storage_key)?;

        // Restore heap property if heap not empty
        if !self.indices.is_empty() {
            self.sift_down(storage, 0);
        }

        Some(node.data)
    }

    /// Returns a reference to the minimum element without removing it.
    #[inline]
    pub fn peek<'a>(&self, storage: &'a S) -> Option<&'a T>
    where
        K: 'a,
    {
        let storage_key = *self.indices.first()?;
        // Safety: indices only contains valid storage keys
        Some(unsafe { &storage.get_unchecked(storage_key).data })
    }

    /// Returns the storage key of the minimum element.
    #[inline]
    pub fn peek_key(&self) -> Option<K> {
        self.indices.first().copied()
    }

    // ========================================================================
    // Handle-based operations
    // ========================================================================

    /// Removes an element by its storage key.
    ///
    /// Returns `None` if the key is not in the heap.
    ///
    /// # Time Complexity
    ///
    /// O(log n)
    #[inline]
    pub fn remove(&mut self, storage: &mut S, storage_key: K) -> Option<T> {
        let node = storage.get(storage_key)?;
        let heap_pos = node.heap_pos;

        // Not in heap
        if heap_pos.is_none() {
            return None;
        }

        let pos = heap_pos.as_usize();
        let last_pos = self.indices.len() - 1;

        // Swap with last and remove
        if pos != last_pos {
            self.swap_positions(storage, pos, last_pos);
        }
        self.indices.pop();

        // Clear heap position and remove from storage
        // Safety: storage_key was validated above
        unsafe { storage.get_unchecked_mut(storage_key) }.heap_pos = K::NONE;
        let node = storage.remove(storage_key)?;

        // Restore heap property if needed
        if pos < self.indices.len() {
            self.sift_update(storage, pos);
        }

        Some(node.data)
    }

    /// Restores heap property after decreasing an element's key.
    ///
    /// Call this after mutating an element to have a *smaller* value.
    ///
    /// # Panics
    ///
    /// Panics if `storage_key` is not in the heap (debug builds only).
    #[inline]
    pub fn decrease_key(&mut self, storage: &mut S, storage_key: K) {
        let heap_pos = self.get_heap_pos(storage, storage_key);
        debug_assert!(heap_pos.is_some(), "key not in heap");
        if heap_pos.is_some() {
            self.sift_up(storage, heap_pos.as_usize());
        }
    }

    /// Restores heap property after increasing an element's key.
    ///
    /// Call this after mutating an element to have a *larger* value.
    ///
    /// # Panics
    ///
    /// Panics if `storage_key` is not in the heap (debug builds only).
    #[inline]
    pub fn increase_key(&mut self, storage: &mut S, storage_key: K) {
        let heap_pos = self.get_heap_pos(storage, storage_key);
        debug_assert!(heap_pos.is_some(), "key not in heap");
        if heap_pos.is_some() {
            self.sift_down(storage, heap_pos.as_usize());
        }
    }

    /// Restores heap property after changing an element's key.
    ///
    /// Use this when you don't know whether the key increased or decreased.
    ///
    /// # Panics
    ///
    /// Panics if `storage_key` is not in the heap (debug builds only).
    #[inline]
    pub fn update_key(&mut self, storage: &mut S, storage_key: K) {
        let heap_pos = self.get_heap_pos(storage, storage_key);
        debug_assert!(heap_pos.is_some(), "key not in heap");
        if heap_pos.is_some() {
            self.sift_update(storage, heap_pos.as_usize());
        }
    }

    /// Returns `true` if the storage key is currently in the heap.
    #[inline]
    pub fn contains(&self, storage: &S, storage_key: K) -> bool {
        storage
            .get(storage_key)
            .map(|n| n.heap_pos.is_some())
            .unwrap_or(false)
    }

    // ========================================================================
    // Bulk operations
    // ========================================================================

    /// Removes all elements from the heap, deallocating from storage.
    pub fn clear(&mut self, storage: &mut S) {
        for &storage_key in &self.indices {
            storage.remove(storage_key);
        }
        self.indices.clear();
    }

    /// Returns an iterator that removes elements in sorted order.
    ///
    /// Each call to `next()` performs a `pop()`, so this yields
    /// elements from smallest to largest.
    #[inline]
    pub fn drain<'a>(&'a mut self, storage: &'a mut S) -> Drain<'a, T, S, K> {
        Drain {
            heap: self,
            storage,
        }
    }

    /// Returns an iterator that removes elements while a predicate holds.
    ///
    /// Useful for timer wheels: "pop all timers that have expired".
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_collections::{BoxedHeapStorage, Heap};
    ///
    /// let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(16);
    /// let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::new();
    ///
    /// heap.try_push(&mut storage, 1).unwrap();
    /// heap.try_push(&mut storage, 5).unwrap();
    /// heap.try_push(&mut storage, 10).unwrap();
    ///
    /// // Pop all elements < 7
    /// let expired: Vec<_> = heap.drain_while(&mut storage, |&x| x < 7).collect();
    /// assert_eq!(expired, vec![1, 5]);
    /// assert_eq!(heap.peek(&storage), Some(&10));
    /// ```
    #[inline]
    pub fn drain_while<'a, F>(
        &'a mut self,
        storage: &'a mut S,
        pred: F,
    ) -> DrainWhile<'a, T, S, K, F>
    where
        F: FnMut(&T) -> bool,
    {
        DrainWhile {
            heap: self,
            storage,
            pred,
        }
    }

    // ========================================================================
    // Internal helpers
    // ========================================================================

    #[inline]
    fn get_heap_pos(&self, storage: &S, storage_key: K) -> K {
        storage
            .get(storage_key)
            .map(|n| n.heap_pos)
            .unwrap_or(K::NONE)
    }

    /// Swaps two positions in the heap and updates heap_pos in nodes.
    #[inline]
    fn swap_positions(&mut self, storage: &mut S, pos_a: usize, pos_b: usize) {
        let key_a = self.indices[pos_a];
        let key_b = self.indices[pos_b];

        self.indices.swap(pos_a, pos_b);

        // Safety: indices came from our vec
        unsafe { storage.get_unchecked_mut(key_a) }.heap_pos = K::from_usize(pos_b);
        unsafe { storage.get_unchecked_mut(key_b) }.heap_pos = K::from_usize(pos_a);
    }

    /// Sifts an element up toward the root using hole technique.
    #[inline]
    fn sift_up(&mut self, storage: &mut S, pos: usize) {
        if pos == 0 {
            return;
        }

        // Safety: pos is valid index into heap
        let key = *unsafe { self.indices.get_unchecked(pos) };
        let mut hole = pos;

        while hole > 0 {
            let parent = (hole - 1) / 2;
            // Safety: parent < hole < len
            let parent_key = *unsafe { self.indices.get_unchecked(parent) };

            // Safety: both keys are valid in storage
            let current = unsafe { &storage.get_unchecked(key).data };
            let parent_val = unsafe { &storage.get_unchecked(parent_key).data };

            if current < parent_val {
                // Move parent down into hole
                *unsafe { self.indices.get_unchecked_mut(hole) } = parent_key;
                unsafe { storage.get_unchecked_mut(parent_key) }.heap_pos = K::from_usize(hole);
                hole = parent;
            } else {
                break;
            }
        }

        // Place element in final position
        if hole != pos {
            *unsafe { self.indices.get_unchecked_mut(hole) } = key;
            unsafe { storage.get_unchecked_mut(key) }.heap_pos = K::from_usize(hole);
        }
    }

    /// Sifts an element down using bottom-up technique.
    #[inline]
    fn sift_down(&mut self, storage: &mut S, pos: usize) {
        let len = self.indices.len();
        if len <= 1 {
            return;
        }

        // Safety: pos is valid index into heap
        let key = *unsafe { self.indices.get_unchecked(pos) };
        let mut hole = pos;

        // Phase 1: Descend to leaf, always following smaller child
        loop {
            let left = 2 * hole + 1;
            if left >= len {
                break;
            }

            let right = left + 1;
            // Safety: left < len
            let left_key = *unsafe { self.indices.get_unchecked(left) };

            let smaller = if right < len {
                let right_key = *unsafe { self.indices.get_unchecked(right) };
                // Safety: both keys valid in storage
                let left_val = unsafe { &storage.get_unchecked(left_key).data };
                let right_val = unsafe { &storage.get_unchecked(right_key).data };
                if right_val < left_val { right } else { left }
            } else {
                left
            };

            // Safety: smaller < len
            let smaller_key = *unsafe { self.indices.get_unchecked(smaller) };
            *unsafe { self.indices.get_unchecked_mut(hole) } = smaller_key;
            unsafe { storage.get_unchecked_mut(smaller_key) }.heap_pos = K::from_usize(hole);
            hole = smaller;
        }

        // Phase 2: Sift up from leaf position back toward original position
        while hole > pos {
            let parent = (hole - 1) / 2;
            // Safety: parent < hole
            let parent_key = *unsafe { self.indices.get_unchecked(parent) };

            // Safety: both keys valid in storage
            let current = unsafe { &storage.get_unchecked(key).data };
            let parent_val = unsafe { &storage.get_unchecked(parent_key).data };

            if current < parent_val {
                *unsafe { self.indices.get_unchecked_mut(hole) } = parent_key;
                unsafe { storage.get_unchecked_mut(parent_key) }.heap_pos = K::from_usize(hole);
                hole = parent;
            } else {
                break;
            }
        }

        // Place element in final position
        *unsafe { self.indices.get_unchecked_mut(hole) } = key;
        unsafe { storage.get_unchecked_mut(key) }.heap_pos = K::from_usize(hole);
    }

    /// Sifts in the appropriate direction after an update.
    #[inline]
    fn sift_update(&mut self, storage: &mut S, pos: usize) {
        // Capture which element we're updating BEFORE any sifting
        let storage_key = *unsafe { self.indices.get_unchecked(pos) };

        // Try sifting up first
        self.sift_up(storage, pos);

        // Check if we moved by looking at the element's current heap_pos
        let current_pos = unsafe { storage.get_unchecked(storage_key) }
            .heap_pos
            .as_usize();

        // If we didn't move up, try sifting down
        if current_pos == pos {
            self.sift_down(storage, pos);
        }
    }
}

// =============================================================================
// BoundedStorage impl - fallible push
// =============================================================================

impl<T: Ord, S, K: Key> Heap<T, S, K>
where
    S: BoundedStorage<HeapNode<T, K>, Key = K>,
{
    /// Pushes a value onto the heap.
    ///
    /// Returns the storage key, which can be used for O(log n) removal
    /// or priority updates.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn try_push(&mut self, storage: &mut S, value: T) -> Result<K, Full<T>> {
        let storage_key = storage
            .try_insert(HeapNode::new(value))
            .map_err(|e| Full(e.0.data))?;

        let heap_pos = self.indices.len();

        // Set heap position and add to indices
        // Safety: we just inserted this
        unsafe { storage.get_unchecked_mut(storage_key) }.heap_pos = K::from_usize(heap_pos);
        self.indices.push(storage_key);

        // Restore heap property
        self.sift_up(storage, heap_pos);

        Ok(storage_key)
    }
}

// =============================================================================
// UnboundedStorage impl - infallible push
// =============================================================================

impl<T: Ord, S, K: Key> Heap<T, S, K>
where
    S: UnboundedStorage<HeapNode<T, K>, Key = K>,
{
    /// Pushes a value onto the heap.
    ///
    /// Returns the storage key, which can be used for O(log n) removal
    /// or priority updates.
    #[inline]
    pub fn push(&mut self, storage: &mut S, value: T) -> K {
        let storage_key = storage.insert(HeapNode::new(value));
        let heap_pos = self.indices.len();

        // Set heap position and add to indices
        // Safety: we just inserted this
        unsafe { storage.get_unchecked_mut(storage_key) }.heap_pos = K::from_usize(heap_pos);
        self.indices.push(storage_key);

        // Restore heap property
        self.sift_up(storage, heap_pos);

        storage_key
    }
}

// ============================================================================
// Iterators
// ============================================================================

/// Iterator that drains elements from the heap in sorted order.
pub struct Drain<'a, T: Ord, S, K: Key>
where
    S: Storage<HeapNode<T, K>, Key = K>,
{
    heap: &'a mut Heap<T, S, K>,
    storage: &'a mut S,
}

impl<'a, T: Ord, S, K: Key> Iterator for Drain<'a, T, S, K>
where
    S: Storage<HeapNode<T, K>, Key = K>,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.heap.pop(self.storage)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.heap.len();
        (len, Some(len))
    }
}

impl<T: Ord, S, K: Key> ExactSizeIterator for Drain<'_, T, S, K> where
    S: Storage<HeapNode<T, K>, Key = K>
{
}

impl<T: Ord, S, K: Key> Drop for Drain<'_, T, S, K>
where
    S: Storage<HeapNode<T, K>, Key = K>,
{
    fn drop(&mut self) {
        // Exhaust remaining elements
        for _ in self.by_ref() {}
    }
}

/// Iterator that drains elements while a predicate holds.
pub struct DrainWhile<'a, T: Ord, S, K: Key, F>
where
    S: Storage<HeapNode<T, K>, Key = K>,
    F: FnMut(&T) -> bool,
{
    heap: &'a mut Heap<T, S, K>,
    storage: &'a mut S,
    pred: F,
}

impl<'a, T: Ord, S, K: Key, F> Iterator for DrainWhile<'a, T, S, K, F>
where
    S: Storage<HeapNode<T, K>, Key = K>,
    F: FnMut(&T) -> bool,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let min = self.heap.peek(self.storage)?;
        if (self.pred)(min) {
            self.heap.pop(self.storage)
        } else {
            None
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Basic Operations
    // ========================================================================

    #[test]
    fn new_heap_is_empty() {
        let heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::new();
        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
        assert!(heap.peek_key().is_none());
    }

    #[test]
    fn try_push_single() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let key = heap.try_push(&mut storage, 42).unwrap();

        assert_eq!(heap.len(), 1);
        assert!(!heap.is_empty());
        assert_eq!(heap.peek(&storage), Some(&42));
        assert_eq!(heap.peek_key(), Some(key));
    }

    #[test]
    fn try_push_maintains_min_heap() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 3).unwrap();
        assert_eq!(heap.peek(&storage), Some(&3));

        heap.try_push(&mut storage, 1).unwrap();
        assert_eq!(heap.peek(&storage), Some(&1));

        heap.try_push(&mut storage, 2).unwrap();
        assert_eq!(heap.peek(&storage), Some(&1));

        heap.try_push(&mut storage, 0).unwrap();
        assert_eq!(heap.peek(&storage), Some(&0));
    }

    #[test]
    fn pop_returns_min() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 3).unwrap();
        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 2).unwrap();

        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn pop_returns_sorted_order() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 5).unwrap();
        heap.try_push(&mut storage, 3).unwrap();
        heap.try_push(&mut storage, 7).unwrap();
        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 4).unwrap();

        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(3));
        assert_eq!(heap.pop(&mut storage), Some(4));
        assert_eq!(heap.pop(&mut storage), Some(5));
        assert_eq!(heap.pop(&mut storage), Some(7));
        assert_eq!(heap.pop(&mut storage), None);
    }

    #[test]
    fn pop_empty_returns_none() {
        let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        assert_eq!(heap.pop(&mut storage), None);
    }

    #[test]
    fn peek_does_not_remove() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 42).unwrap();

        assert_eq!(heap.peek(&storage), Some(&42));
        assert_eq!(heap.peek(&storage), Some(&42));
        assert_eq!(heap.len(), 1);
    }

    #[test]
    fn peek_empty_returns_none() {
        let storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(16);
        let heap: Heap<u64, _> = Heap::new();

        assert_eq!(heap.peek(&storage), None);
    }

    // ========================================================================
    // Handle-based Operations
    // ========================================================================

    #[test]
    fn remove_by_handle() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let _a = heap.try_push(&mut storage, 3).unwrap();
        let _b = heap.try_push(&mut storage, 1).unwrap();
        let c = heap.try_push(&mut storage, 2).unwrap();

        // Remove middle element
        assert_eq!(heap.remove(&mut storage, c), Some(2));
        assert_eq!(heap.len(), 2);

        // Heap still works
        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(3));
    }

    #[test]
    fn remove_min_by_handle() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 3).unwrap();
        let min_key = heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 2).unwrap();

        assert_eq!(heap.remove(&mut storage, min_key), Some(1));
        assert_eq!(heap.peek(&storage), Some(&2));
    }

    #[test]
    fn remove_last_by_handle() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 2).unwrap();
        let last = heap.try_push(&mut storage, 3).unwrap();

        assert_eq!(heap.remove(&mut storage, last), Some(3));
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn remove_invalid_returns_none() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let key = heap.try_push(&mut storage, 1).unwrap();
        heap.pop(&mut storage);

        // Key no longer in heap
        assert_eq!(heap.remove(&mut storage, key), None);
    }

    #[test]
    fn contains() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let key = heap.try_push(&mut storage, 42).unwrap();
        assert!(heap.contains(&storage, key));

        heap.pop(&mut storage);
        assert!(!heap.contains(&storage, key));
    }

    #[test]
    fn decrease_key() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 1).unwrap();
        let key = heap.try_push(&mut storage, 10).unwrap();
        heap.try_push(&mut storage, 5).unwrap();

        // 10 is not the min
        assert_eq!(heap.peek(&storage), Some(&1));

        // Decrease 10 to 0 (need mutable access to data)
        unsafe { storage.get_unchecked_mut(key) }.data = 0;
        heap.decrease_key(&mut storage, key);

        // Now it's the min
        assert_eq!(heap.peek(&storage), Some(&0));
    }

    #[test]
    fn increase_key() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let key = heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 5).unwrap();
        heap.try_push(&mut storage, 10).unwrap();

        // 1 is the min
        assert_eq!(heap.peek(&storage), Some(&1));

        // Increase 1 to 100
        unsafe { storage.get_unchecked_mut(key) }.data = 100;
        heap.increase_key(&mut storage, key);

        // Now 5 is the min
        assert_eq!(heap.peek(&storage), Some(&5));

        // Verify order
        assert_eq!(heap.pop(&mut storage), Some(5));
        assert_eq!(heap.pop(&mut storage), Some(10));
        assert_eq!(heap.pop(&mut storage), Some(100));
    }

    #[test]
    fn update_key_decrease() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 1).unwrap();
        let key = heap.try_push(&mut storage, 10).unwrap();
        heap.try_push(&mut storage, 5).unwrap();

        unsafe { storage.get_unchecked_mut(key) }.data = 0;
        heap.update_key(&mut storage, key);

        assert_eq!(heap.peek(&storage), Some(&0));
    }

    #[test]
    fn update_key_increase() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let key = heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 5).unwrap();
        heap.try_push(&mut storage, 10).unwrap();

        unsafe { storage.get_unchecked_mut(key) }.data = 100;
        heap.update_key(&mut storage, key);

        assert_eq!(heap.peek(&storage), Some(&5));
    }

    // ========================================================================
    // Edge Cases
    // ========================================================================

    #[test]
    fn single_element_pop() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 42).unwrap();
        assert_eq!(heap.pop(&mut storage), Some(42));
        assert!(heap.is_empty());
    }

    #[test]
    fn single_element_remove() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let key = heap.try_push(&mut storage, 42).unwrap();
        assert_eq!(heap.remove(&mut storage, key), Some(42));
        assert!(heap.is_empty());
    }

    #[test]
    fn two_elements() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 2).unwrap();
        heap.try_push(&mut storage, 1).unwrap();

        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(2));
    }

    #[test]
    fn duplicates() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 1).unwrap();

        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(1));
        assert!(heap.is_empty());
    }

    #[test]
    fn try_push_full_returns_value() {
        let mut storage = BoxedHeapStorage::with_capacity(2);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 2).unwrap();

        // Should fail and return the value
        let result = heap.try_push(&mut storage, 3);
        assert!(result.is_err());
        let Full(val) = result.unwrap_err();
        assert_eq!(val, 3);
    }

    // ========================================================================
    // Bulk Operations
    // ========================================================================

    #[test]
    fn clear() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 2).unwrap();
        heap.try_push(&mut storage, 3).unwrap();

        heap.clear(&mut storage);

        assert!(heap.is_empty());
        assert!(storage.is_empty());
    }

    #[test]
    fn drain_sorted_order() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 5).unwrap();
        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 3).unwrap();
        heap.try_push(&mut storage, 2).unwrap();
        heap.try_push(&mut storage, 4).unwrap();

        let values: Vec<_> = heap.drain(&mut storage).collect();
        assert_eq!(values, vec![1, 2, 3, 4, 5]);
        assert!(heap.is_empty());
    }

    #[test]
    fn drain_partial_then_drop() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 2).unwrap();
        heap.try_push(&mut storage, 3).unwrap();

        {
            let mut drain = heap.drain(&mut storage);
            assert_eq!(drain.next(), Some(1));
            // Drop without consuming all
        }

        assert!(heap.is_empty());
        assert!(storage.is_empty());
    }

    #[test]
    fn drain_while_expired_timers() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 10).unwrap();
        heap.try_push(&mut storage, 20).unwrap();
        heap.try_push(&mut storage, 30).unwrap();
        heap.try_push(&mut storage, 40).unwrap();
        heap.try_push(&mut storage, 50).unwrap();

        // "Current time" is 35, pop all expired
        let expired: Vec<_> = heap.drain_while(&mut storage, |&t| t <= 35).collect();
        assert_eq!(expired, vec![10, 20, 30]);

        // Remaining
        assert_eq!(heap.len(), 2);
        assert_eq!(heap.peek(&storage), Some(&40));
    }

    #[test]
    fn drain_while_none_match() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 10).unwrap();
        heap.try_push(&mut storage, 20).unwrap();

        let expired: Vec<_> = heap.drain_while(&mut storage, |&t| t < 5).collect();
        assert!(expired.is_empty());
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn drain_while_all_match() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.try_push(&mut storage, 1).unwrap();
        heap.try_push(&mut storage, 2).unwrap();
        heap.try_push(&mut storage, 3).unwrap();

        let all: Vec<_> = heap.drain_while(&mut storage, |_| true).collect();
        assert_eq!(all, vec![1, 2, 3]);
        assert!(heap.is_empty());
    }

    // ========================================================================
    // Storage Reuse
    // ========================================================================

    #[test]
    fn storage_reuse_after_pop() {
        let mut storage = BoxedHeapStorage::with_capacity(4);
        let mut heap: Heap<u64, _> = Heap::new();

        let a = heap.try_push(&mut storage, 1).unwrap();
        heap.pop(&mut storage);

        // Slot should be reused
        let b = heap.try_push(&mut storage, 2).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn storage_reuse_after_remove() {
        let mut storage = BoxedHeapStorage::with_capacity(4);
        let mut heap: Heap<u64, _> = Heap::new();

        let a = heap.try_push(&mut storage, 1).unwrap();
        heap.remove(&mut storage, a);

        let b = heap.try_push(&mut storage, 2).unwrap();
        assert_eq!(a, b);
    }

    // ========================================================================
    // Stress Tests
    // ========================================================================

    #[test]
    fn stress_push_pop_sorted() {
        let mut storage = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, _> = Heap::new();

        // Push in reverse order
        for i in (0..1000).rev() {
            heap.try_push(&mut storage, i).unwrap();
        }

        // Pop should yield sorted order
        let mut prev = 0;
        while let Some(val) = heap.pop(&mut storage) {
            assert!(val >= prev);
            prev = val;
        }
    }

    #[test]
    fn stress_interleaved_push_pop() {
        let mut storage = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, _> = Heap::new();

        for i in 0..1000 {
            heap.try_push(&mut storage, i).unwrap();
            if i % 3 == 0 {
                heap.pop(&mut storage);
            }
        }

        // Drain and verify sorted
        let values: Vec<_> = heap.drain(&mut storage).collect();
        for i in 1..values.len() {
            assert!(values[i] >= values[i - 1]);
        }
    }

    #[test]
    fn stress_remove_random() {
        let mut storage = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, _> = Heap::new();

        let mut keys = Vec::new();
        for i in 0..100 {
            keys.push(heap.try_push(&mut storage, i).unwrap());
        }

        // Remove every other element
        for (i, &key) in keys.iter().enumerate() {
            if i % 2 == 0 {
                heap.remove(&mut storage, key);
            }
        }

        // Verify remaining are sorted
        let values: Vec<_> = heap.drain(&mut storage).collect();
        for i in 1..values.len() {
            assert!(values[i] >= values[i - 1]);
        }
    }

    // ========================================================================
    // Custom Ord Type
    // ========================================================================

    #[test]
    fn custom_ord_type() {
        #[derive(Eq, PartialEq, Debug)]
        struct Task {
            priority: u32,
            name: &'static str,
        }

        impl Ord for Task {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.priority.cmp(&other.priority)
            }
        }

        impl PartialOrd for Task {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        let mut storage: BoxedHeapStorage<Task> = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<Task, _> = Heap::new();

        heap.try_push(
            &mut storage,
            Task {
                priority: 3,
                name: "low",
            },
        )
        .unwrap();
        heap.try_push(
            &mut storage,
            Task {
                priority: 1,
                name: "high",
            },
        )
        .unwrap();
        heap.try_push(
            &mut storage,
            Task {
                priority: 2,
                name: "medium",
            },
        )
        .unwrap();

        assert_eq!(heap.pop(&mut storage).unwrap().name, "high");
        assert_eq!(heap.pop(&mut storage).unwrap().name, "medium");
        assert_eq!(heap.pop(&mut storage).unwrap().name, "low");
    }
}

// ============================================================================
// slab::Slab tests (UnboundedStorage)
// ============================================================================

#[cfg(all(test, feature = "slab"))]
mod tests_slab {
    use super::*;

    #[test]
    fn slab_push_infallible() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::new();

        // Infallible - no Result!
        let a = heap.push(&mut storage, 3);
        let b = heap.push(&mut storage, 1);
        let c = heap.push(&mut storage, 2);

        assert_eq!(heap.len(), 3);
        assert_eq!(heap.peek(&storage), Some(&1));

        // Keys are sequential
        assert_eq!(a, 0);
        assert_eq!(b, 1);
        assert_eq!(c, 2);
    }

    #[test]
    fn slab_pop_sorted_order() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::new();

        heap.push(&mut storage, 5);
        heap.push(&mut storage, 1);
        heap.push(&mut storage, 3);
        heap.push(&mut storage, 2);
        heap.push(&mut storage, 4);

        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(2));
        assert_eq!(heap.pop(&mut storage), Some(3));
        assert_eq!(heap.pop(&mut storage), Some(4));
        assert_eq!(heap.pop(&mut storage), Some(5));
    }

    #[test]
    fn slab_remove_by_handle() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::new();

        let a = heap.push(&mut storage, 3);
        heap.push(&mut storage, 1);
        heap.push(&mut storage, 2);

        assert_eq!(heap.remove(&mut storage, a), Some(3));
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn slab_decrease_key() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::new();

        heap.push(&mut storage, 1);
        let key = heap.push(&mut storage, 10);
        heap.push(&mut storage, 5);

        assert_eq!(heap.peek(&storage), Some(&1));

        unsafe { storage.get_unchecked_mut(key) }.data = 0;
        heap.decrease_key(&mut storage, key);

        assert_eq!(heap.peek(&storage), Some(&0));
    }

    #[test]
    fn slab_grows_automatically() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(2);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::new();

        // Should grow beyond initial capacity
        for i in 0..100 {
            heap.push(&mut storage, i);
        }

        assert_eq!(heap.len(), 100);

        // Verify still sorted
        let values: Vec<_> = heap.drain(&mut storage).collect();
        for i in 1..values.len() {
            assert!(values[i] >= values[i - 1]);
        }
    }

    #[test]
    fn slab_drain_while() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::new();

        heap.push(&mut storage, 10);
        heap.push(&mut storage, 20);
        heap.push(&mut storage, 30);

        let expired: Vec<_> = heap.drain_while(&mut storage, |&t| t <= 15).collect();
        assert_eq!(expired, vec![10]);
        assert_eq!(heap.len(), 2);
    }
}

#[cfg(test)]
mod bench_boxed_storage {
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

    #[test]
    #[ignore]
    fn bench_heap_try_push() {
        let mut storage: BoxedHeapStorage<u64> =
            BoxedHeapStorage::with_capacity(ITERATIONS + WARMUP);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(ITERATIONS + WARMUP);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..WARMUP {
            let _ = heap.try_push(&mut storage, i as u64);
            let _ = heap.pop(&mut storage);
        }

        for i in 0..ITERATIONS {
            let start = rdtscp();
            let _ = heap.try_push(&mut storage, i as u64);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
            let _ = heap.pop(&mut storage);
        }

        print_histogram("try_push", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_pop() {
        let mut storage: BoxedHeapStorage<u64> =
            BoxedHeapStorage::with_capacity(ITERATIONS + WARMUP);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(ITERATIONS + WARMUP);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for _ in 0..WARMUP {
            let _ = heap.try_push(&mut storage, 1);
            let _ = heap.pop(&mut storage);
        }

        for i in 0..ITERATIONS {
            let _ = heap.try_push(&mut storage, i as u64);
            let start = rdtscp();
            let _ = heap.pop(&mut storage);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("pop", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_peek() {
        let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Build a heap of 1000 elements
        for i in 0..1000 {
            heap.try_push(&mut storage, i as u64).unwrap();
        }

        for _ in 0..WARMUP {
            std::hint::black_box(heap.peek(&storage));
        }

        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(heap.peek(&storage));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("peek", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_remove() {
        let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(16);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for _ in 0..WARMUP {
            let a = heap.try_push(&mut storage, 1).unwrap();
            let b = heap.try_push(&mut storage, 2).unwrap();
            let c = heap.try_push(&mut storage, 3).unwrap();
            let _ = heap.remove(&mut storage, b);
            let _ = heap.remove(&mut storage, a);
            let _ = heap.remove(&mut storage, c);
        }

        for _ in 0..ITERATIONS {
            let a = heap.try_push(&mut storage, 1).unwrap();
            let b = heap.try_push(&mut storage, 2).unwrap();
            let c = heap.try_push(&mut storage, 3).unwrap();

            let start = rdtscp();
            let _ = heap.remove(&mut storage, b);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            let _ = heap.remove(&mut storage, a);
            let _ = heap.remove(&mut storage, c);
        }

        print_histogram("remove (middle)", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_decrease_key() {
        let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Build heap with values 0..1000
        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000 {
            keys.push(heap.try_push(&mut storage, (i * 2) as u64).unwrap());
        }

        for _ in 0..WARMUP {
            let key = keys[500];
            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            heap.decrease_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data = 1000;
            heap.increase_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data;

            // Decrease to 0
            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            let start = rdtscp();
            heap.decrease_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            // Restore
            unsafe { storage.get_unchecked_mut(key) }.data = original;
            heap.increase_key(&mut storage, key);
        }

        print_histogram("decrease_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_increase_key() {
        let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000 {
            keys.push(heap.try_push(&mut storage, (i * 2) as u64).unwrap());
        }

        for _ in 0..WARMUP {
            let key = keys[0];
            unsafe { storage.get_unchecked_mut(key) }.data = 10000;
            heap.increase_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            heap.decrease_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data;

            // Increase to max
            unsafe { storage.get_unchecked_mut(key) }.data = 10000;
            let start = rdtscp();
            heap.increase_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            // Restore
            unsafe { storage.get_unchecked_mut(key) }.data = original;
            heap.decrease_key(&mut storage, key);
        }

        print_histogram("increase_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_update_key() {
        let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000 {
            keys.push(heap.try_push(&mut storage, (i * 2) as u64).unwrap());
        }

        for i in 0..WARMUP {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data;
            unsafe { storage.get_unchecked_mut(key) }.data = (i % 2000) as u64;
            heap.update_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data = original;
            heap.update_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data;

            // Change to random-ish value
            unsafe { storage.get_unchecked_mut(key) }.data = (i % 2000) as u64;
            let start = rdtscp();
            heap.update_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            // Restore
            unsafe { storage.get_unchecked_mut(key) }.data = original;
            heap.update_key(&mut storage, key);
        }

        print_histogram("update_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_contains() {
        let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000 {
            keys.push(heap.try_push(&mut storage, i as u64).unwrap());
        }

        let mid_key = keys[500];
        for _ in 0..WARMUP {
            std::hint::black_box(heap.contains(&storage, mid_key));
        }

        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(heap.contains(&storage, mid_key));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("contains", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_timer_workflow() {
        // Simulates a timer wheel: insert timers, fire expired ones
        let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(1024);
        let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(1024);

        let mut hist_insert = Histogram::<u64>::new(3).unwrap();
        let mut hist_fire = Histogram::<u64>::new(3).unwrap();
        let mut hist_cancel = Histogram::<u64>::new(3).unwrap();

        for i in 0..WARMUP {
            let deadline = (i % 100) as u64;
            let key = heap.try_push(&mut storage, deadline).unwrap();
            if i % 3 == 0 {
                heap.remove(&mut storage, key);
            } else {
                heap.pop(&mut storage);
            }
        }

        for i in 0..ITERATIONS {
            let deadline = (i % 100) as u64;

            // Insert timer
            let start = rdtscp();
            let key = heap.try_push(&mut storage, deadline).unwrap();
            hist_insert.record(rdtscp() - start).unwrap();

            if i % 3 == 0 {
                // Cancel timer
                let start = rdtscp();
                heap.remove(&mut storage, key);
                hist_cancel.record(rdtscp() - start).unwrap();
            } else {
                // Fire timer (pop)
                let start = rdtscp();
                heap.pop(&mut storage);
                hist_fire.record(rdtscp() - start).unwrap();
            }
        }

        println!("\n=== Timer Workflow (BoxedStorage) ===");
        print_histogram("insert (schedule)", &hist_insert);
        print_histogram("fire (pop)", &hist_fire);
        print_histogram("cancel (remove)", &hist_cancel);
    }

    #[test]
    #[ignore]
    fn bench_heap_varying_sizes() {
        println!("\n=== Heap try_push at varying sizes (BoxedStorage) ===");

        for &size in &[10, 100, 1000, 10000] {
            let mut storage: BoxedHeapStorage<u64> =
                BoxedHeapStorage::with_capacity(size + ITERATIONS);
            let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::with_capacity(size + ITERATIONS);
            let mut hist = Histogram::<u64>::new(3).unwrap();

            // Build initial heap
            for i in 0..size {
                heap.try_push(&mut storage, i as u64).unwrap();
            }

            for i in 0..ITERATIONS {
                let start = rdtscp();
                let key = heap.try_push(&mut storage, (size + i) as u64).unwrap();
                let elapsed = rdtscp() - start;
                hist.record(elapsed).unwrap();

                // Remove to keep size constant
                heap.remove(&mut storage, key);
            }

            print_histogram(&format!("size={}", size), &hist);
        }
    }

    #[test]
    #[ignore]
    fn bench_heap_all() {
        println!("\n=== Heap Benchmarks (BoxedStorage) ===");
        println!(
            "Run with: cargo test --release bench_boxed_storage::bench_heap_all -- --ignored --nocapture\n"
        );

        bench_heap_try_push();
        bench_heap_pop();
        bench_heap_peek();
        bench_heap_remove();
        bench_heap_decrease_key();
        bench_heap_increase_key();
        bench_heap_update_key();
        bench_heap_contains();

        println!();
        bench_heap_timer_workflow();
        bench_heap_varying_sizes();
    }
}

#[cfg(all(test, feature = "slab"))]
mod bench_slab_storage {
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

    #[test]
    #[ignore]
    fn bench_heap_push() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::with_capacity(16);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..WARMUP {
            let _ = heap.push(&mut storage, i as u64);
            let _ = heap.pop(&mut storage);
        }

        for i in 0..ITERATIONS {
            let start = rdtscp();
            let _ = heap.push(&mut storage, i as u64);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
            let _ = heap.pop(&mut storage);
        }

        print_histogram("push", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_pop() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::with_capacity(16);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for _ in 0..WARMUP {
            let _ = heap.push(&mut storage, 1);
            let _ = heap.pop(&mut storage);
        }

        for i in 0..ITERATIONS {
            let _ = heap.push(&mut storage, i as u64);
            let start = rdtscp();
            let _ = heap.pop(&mut storage);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("pop", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_peek() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(1024);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..1000 {
            heap.push(&mut storage, i as u64);
        }

        for _ in 0..WARMUP {
            std::hint::black_box(heap.peek(&storage));
        }

        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(heap.peek(&storage));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("peek", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_remove() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(16);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::with_capacity(16);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for _ in 0..WARMUP {
            let a = heap.push(&mut storage, 1);
            let b = heap.push(&mut storage, 2);
            let c = heap.push(&mut storage, 3);
            let _ = heap.remove(&mut storage, b);
            let _ = heap.remove(&mut storage, a);
            let _ = heap.remove(&mut storage, c);
        }

        for _ in 0..ITERATIONS {
            let a = heap.push(&mut storage, 1);
            let b = heap.push(&mut storage, 2);
            let c = heap.push(&mut storage, 3);

            let start = rdtscp();
            let _ = heap.remove(&mut storage, b);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            let _ = heap.remove(&mut storage, a);
            let _ = heap.remove(&mut storage, c);
        }

        print_histogram("remove (middle)", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_decrease_key() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(1024);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000 {
            keys.push(heap.push(&mut storage, (i * 2) as u64));
        }

        for _ in 0..WARMUP {
            let key = keys[500];
            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            heap.decrease_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data = 1000;
            heap.increase_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data;

            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            let start = rdtscp();
            heap.decrease_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            unsafe { storage.get_unchecked_mut(key) }.data = original;
            heap.increase_key(&mut storage, key);
        }

        print_histogram("decrease_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_increase_key() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(1024);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000 {
            keys.push(heap.push(&mut storage, (i * 2) as u64));
        }

        for _ in 0..WARMUP {
            let key = keys[0];
            unsafe { storage.get_unchecked_mut(key) }.data = 10000;
            heap.increase_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            heap.decrease_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data;

            unsafe { storage.get_unchecked_mut(key) }.data = 10000;
            let start = rdtscp();
            heap.increase_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            unsafe { storage.get_unchecked_mut(key) }.data = original;
            heap.decrease_key(&mut storage, key);
        }

        print_histogram("increase_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_timer_workflow() {
        let mut storage: SlabHeapStorage<u64> = slab::Slab::with_capacity(1024);
        let mut heap: Heap<u64, SlabHeapStorage<u64>, usize> = Heap::with_capacity(1024);

        let mut hist_insert = Histogram::<u64>::new(3).unwrap();
        let mut hist_fire = Histogram::<u64>::new(3).unwrap();
        let mut hist_cancel = Histogram::<u64>::new(3).unwrap();

        for i in 0..WARMUP {
            let deadline = (i % 100) as u64;
            let key = heap.push(&mut storage, deadline);
            if i % 3 == 0 {
                heap.remove(&mut storage, key);
            } else {
                heap.pop(&mut storage);
            }
        }

        for i in 0..ITERATIONS {
            let deadline = (i % 100) as u64;

            let start = rdtscp();
            let key = heap.push(&mut storage, deadline);
            hist_insert.record(rdtscp() - start).unwrap();

            if i % 3 == 0 {
                let start = rdtscp();
                heap.remove(&mut storage, key);
                hist_cancel.record(rdtscp() - start).unwrap();
            } else {
                let start = rdtscp();
                heap.pop(&mut storage);
                hist_fire.record(rdtscp() - start).unwrap();
            }
        }

        println!("\n=== Timer Workflow (slab::Slab) ===");
        print_histogram("insert (schedule)", &hist_insert);
        print_histogram("fire (pop)", &hist_fire);
        print_histogram("cancel (remove)", &hist_cancel);
    }

    #[test]
    #[ignore]
    fn bench_heap_all() {
        println!("\n=== Heap Benchmarks (slab::Slab) ===");
        println!(
            "Run with: cargo test --release --features slab bench_slab_storage::bench_heap_all -- --ignored --nocapture\n"
        );

        bench_heap_push();
        bench_heap_pop();
        bench_heap_peek();
        bench_heap_remove();
        bench_heap_decrease_key();
        bench_heap_increase_key();

        println!();
        bench_heap_timer_workflow();
    }
}

#[cfg(all(test, feature = "nexus-slab"))]
mod bench_nexus_slab_storage {
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

    #[test]
    #[ignore]
    fn bench_heap_try_push() {
        let mut storage: NexusHeapStorage<u64> =
            nexus_slab::Slab::with_capacity(ITERATIONS + WARMUP).expect("failed to allocate");
        let mut heap: Heap<u64, NexusHeapStorage<u64>, nexus_slab::Key> =
            Heap::with_capacity(ITERATIONS + WARMUP);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..WARMUP {
            let _ = heap.try_push(&mut storage, i as u64);
            let _ = heap.pop(&mut storage);
        }

        for i in 0..ITERATIONS {
            let start = rdtscp();
            let _ = heap.try_push(&mut storage, i as u64);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
            let _ = heap.pop(&mut storage);
        }

        print_histogram("try_push", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_pop() {
        let mut storage: NexusHeapStorage<u64> =
            nexus_slab::Slab::with_capacity(ITERATIONS + WARMUP).expect("failed to allocate");
        let mut heap: Heap<u64, NexusHeapStorage<u64>, nexus_slab::Key> =
            Heap::with_capacity(ITERATIONS + WARMUP);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for _ in 0..WARMUP {
            let _ = heap.try_push(&mut storage, 1);
            let _ = heap.pop(&mut storage);
        }

        for i in 0..ITERATIONS {
            let _ = heap.try_push(&mut storage, i as u64);
            let start = rdtscp();
            let _ = heap.pop(&mut storage);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("pop", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_peek() {
        let mut storage: NexusHeapStorage<u64> =
            nexus_slab::Slab::with_capacity(1024).expect("failed to allocate");
        let mut heap: Heap<u64, NexusHeapStorage<u64>, nexus_slab::Key> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..1000 {
            heap.try_push(&mut storage, i as u64).unwrap();
        }

        for _ in 0..WARMUP {
            std::hint::black_box(heap.peek(&storage));
        }

        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(heap.peek(&storage));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("peek", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_remove() {
        let mut storage: NexusHeapStorage<u64> =
            nexus_slab::Slab::with_capacity(16).expect("failed to allocate");
        let mut heap: Heap<u64, NexusHeapStorage<u64>, nexus_slab::Key> = Heap::with_capacity(16);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for _ in 0..WARMUP {
            let a = heap.try_push(&mut storage, 1).unwrap();
            let b = heap.try_push(&mut storage, 2).unwrap();
            let c = heap.try_push(&mut storage, 3).unwrap();
            let _ = heap.remove(&mut storage, b);
            let _ = heap.remove(&mut storage, a);
            let _ = heap.remove(&mut storage, c);
        }

        for _ in 0..ITERATIONS {
            let a = heap.try_push(&mut storage, 1).unwrap();
            let b = heap.try_push(&mut storage, 2).unwrap();
            let c = heap.try_push(&mut storage, 3).unwrap();

            let start = rdtscp();
            let _ = heap.remove(&mut storage, b);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            let _ = heap.remove(&mut storage, a);
            let _ = heap.remove(&mut storage, c);
        }

        print_histogram("remove (middle)", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_decrease_key() {
        let mut storage: NexusHeapStorage<u64> =
            nexus_slab::Slab::with_capacity(1024).expect("failed to allocate");
        let mut heap: Heap<u64, NexusHeapStorage<u64>, nexus_slab::Key> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000 {
            keys.push(heap.try_push(&mut storage, (i * 2) as u64).unwrap());
        }

        for _ in 0..WARMUP {
            let key = keys[500];
            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            heap.decrease_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data = 1000;
            heap.increase_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data;

            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            let start = rdtscp();
            heap.decrease_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            unsafe { storage.get_unchecked_mut(key) }.data = original;
            heap.increase_key(&mut storage, key);
        }

        print_histogram("decrease_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_increase_key() {
        let mut storage: NexusHeapStorage<u64> =
            nexus_slab::Slab::with_capacity(1024).expect("failed to allocate");
        let mut heap: Heap<u64, NexusHeapStorage<u64>, nexus_slab::Key> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000 {
            keys.push(heap.try_push(&mut storage, (i * 2) as u64).unwrap());
        }

        for _ in 0..WARMUP {
            let key = keys[0];
            unsafe { storage.get_unchecked_mut(key) }.data = 10000;
            heap.increase_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data = 0;
            heap.decrease_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data;

            unsafe { storage.get_unchecked_mut(key) }.data = 10000;
            let start = rdtscp();
            heap.increase_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            unsafe { storage.get_unchecked_mut(key) }.data = original;
            heap.decrease_key(&mut storage, key);
        }

        print_histogram("increase_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_timer_workflow() {
        let mut storage: NexusHeapStorage<u64> =
            nexus_slab::Slab::with_capacity(1024).expect("failed to allocate");
        let mut heap: Heap<u64, NexusHeapStorage<u64>, nexus_slab::Key> = Heap::with_capacity(1024);

        let mut hist_insert = Histogram::<u64>::new(3).unwrap();
        let mut hist_fire = Histogram::<u64>::new(3).unwrap();
        let mut hist_cancel = Histogram::<u64>::new(3).unwrap();

        for i in 0..WARMUP {
            let deadline = (i % 100) as u64;
            let key = heap.try_push(&mut storage, deadline).unwrap();
            if i % 3 == 0 {
                heap.remove(&mut storage, key);
            } else {
                heap.pop(&mut storage);
            }
        }

        for i in 0..ITERATIONS {
            let deadline = (i % 100) as u64;

            let start = rdtscp();
            let key = heap.try_push(&mut storage, deadline).unwrap();
            hist_insert.record(rdtscp() - start).unwrap();

            if i % 3 == 0 {
                let start = rdtscp();
                heap.remove(&mut storage, key);
                hist_cancel.record(rdtscp() - start).unwrap();
            } else {
                let start = rdtscp();
                heap.pop(&mut storage);
                hist_fire.record(rdtscp() - start).unwrap();
            }
        }

        println!("\n=== Timer Workflow (nexus_slab::Slab) ===");
        print_histogram("insert (schedule)", &hist_insert);
        print_histogram("fire (pop)", &hist_fire);
        print_histogram("cancel (remove)", &hist_cancel);
    }

    #[test]
    #[ignore]
    fn bench_heap_all() {
        println!("\n=== Heap Benchmarks (nexus_slab::Slab) ===");
        println!(
            "Run with: cargo test --release --features nexus-slab bench_nexus_slab_storage::bench_heap_all -- --ignored --nocapture\n"
        );

        bench_heap_try_push();
        bench_heap_pop();
        bench_heap_peek();
        bench_heap_remove();
        bench_heap_decrease_key();
        bench_heap_increase_key();

        println!();
        bench_heap_timer_workflow();
    }
}

#[cfg(test)]
mod bench_hashmap_storage {
    use super::*;
    use crate::Keyed;
    use hdrhistogram::Histogram;
    use std::collections::HashMap;

    // Test type that provides its own key and is orderable by priority
    #[derive(Clone, Eq, PartialEq)]
    struct Timer {
        id: u64,
        deadline: u64,
    }

    impl Ord for Timer {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            // Min-heap by deadline
            self.deadline.cmp(&other.deadline)
        }
    }

    impl PartialOrd for Timer {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    impl Keyed for Timer {
        type Key = u64;
        fn key(&self) -> u64 {
            self.id
        }
    }

    // Implement Keyed for HeapNode<Timer> so HashMap storage works
    impl Keyed for HeapNode<Timer, u64> {
        type Key = u64;
        fn key(&self) -> u64 {
            self.data.id
        }
    }

    type HashMapHeapStorage = HashMap<u64, HeapNode<Timer, u64>>;

    #[inline]
    fn rdtscp() -> u64 {
        #[cfg(target_arch = "x86_64")]
        unsafe {
            core::arch::x86_64::__rdtscp(&mut 0)
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
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

    #[test]
    #[ignore]
    fn bench_heap_push() {
        let mut storage: HashMapHeapStorage = HashMap::with_capacity(16);
        let mut heap: Heap<Timer, HashMapHeapStorage, u64> = Heap::with_capacity(16);
        let mut hist = Histogram::<u64>::new(3).unwrap();
        let mut id_counter = 0u64;

        for i in 0..WARMUP {
            let timer = Timer {
                id: id_counter,
                deadline: (i % 100) as u64,
            };
            id_counter += 1;
            let _ = heap.push(&mut storage, timer);
            let _ = heap.pop(&mut storage);
        }

        for i in 0..ITERATIONS {
            let timer = Timer {
                id: id_counter,
                deadline: (i % 100) as u64,
            };
            id_counter += 1;

            let start = rdtscp();
            let _ = heap.push(&mut storage, timer);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            let _ = heap.pop(&mut storage);
        }

        print_histogram("push", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_pop() {
        let mut storage: HashMapHeapStorage = HashMap::with_capacity(16);
        let mut heap: Heap<Timer, HashMapHeapStorage, u64> = Heap::with_capacity(16);
        let mut hist = Histogram::<u64>::new(3).unwrap();
        let mut id_counter = 0u64;

        for _ in 0..WARMUP {
            let timer = Timer {
                id: id_counter,
                deadline: 100,
            };
            id_counter += 1;
            let _ = heap.push(&mut storage, timer);
            let _ = heap.pop(&mut storage);
        }

        for i in 0..ITERATIONS {
            let timer = Timer {
                id: id_counter,
                deadline: (i % 100) as u64,
            };
            id_counter += 1;
            let _ = heap.push(&mut storage, timer);

            let start = rdtscp();
            let _ = heap.pop(&mut storage);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("pop", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_peek() {
        let mut storage: HashMapHeapStorage = HashMap::with_capacity(1024);
        let mut heap: Heap<Timer, HashMapHeapStorage, u64> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..1000u64 {
            let timer = Timer { id: i, deadline: i };
            heap.push(&mut storage, timer);
        }

        for _ in 0..WARMUP {
            std::hint::black_box(heap.peek(&storage));
        }

        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(heap.peek(&storage));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("peek", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_remove() {
        let mut storage: HashMapHeapStorage = HashMap::with_capacity(16);
        let mut heap: Heap<Timer, HashMapHeapStorage, u64> = Heap::with_capacity(16);
        let mut hist = Histogram::<u64>::new(3).unwrap();
        let mut id_counter = 0u64;

        for _ in 0..WARMUP {
            let a = heap.push(
                &mut storage,
                Timer {
                    id: id_counter,
                    deadline: 1,
                },
            );
            id_counter += 1;
            let b = heap.push(
                &mut storage,
                Timer {
                    id: id_counter,
                    deadline: 2,
                },
            );
            id_counter += 1;
            let c = heap.push(
                &mut storage,
                Timer {
                    id: id_counter,
                    deadline: 3,
                },
            );
            id_counter += 1;
            let _ = heap.remove(&mut storage, b);
            let _ = heap.remove(&mut storage, a);
            let _ = heap.remove(&mut storage, c);
        }

        for _ in 0..ITERATIONS {
            let a = heap.push(
                &mut storage,
                Timer {
                    id: id_counter,
                    deadline: 1,
                },
            );
            id_counter += 1;
            let b = heap.push(
                &mut storage,
                Timer {
                    id: id_counter,
                    deadline: 2,
                },
            );
            id_counter += 1;
            let c = heap.push(
                &mut storage,
                Timer {
                    id: id_counter,
                    deadline: 3,
                },
            );
            id_counter += 1;

            let start = rdtscp();
            let _ = heap.remove(&mut storage, b);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            let _ = heap.remove(&mut storage, a);
            let _ = heap.remove(&mut storage, c);
        }

        print_histogram("remove (middle)", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_decrease_key() {
        let mut storage: HashMapHeapStorage = HashMap::with_capacity(1024);
        let mut heap: Heap<Timer, HashMapHeapStorage, u64> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000u64 {
            let timer = Timer {
                id: i,
                deadline: i * 2,
            };
            keys.push(heap.push(&mut storage, timer));
        }

        for _ in 0..WARMUP {
            let key = keys[500];
            unsafe { storage.get_unchecked_mut(key) }.data.deadline = 0;
            heap.decrease_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data.deadline = 1000;
            heap.increase_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data.deadline;

            unsafe { storage.get_unchecked_mut(key) }.data.deadline = 0;
            let start = rdtscp();
            heap.decrease_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            unsafe { storage.get_unchecked_mut(key) }.data.deadline = original;
            heap.increase_key(&mut storage, key);
        }

        print_histogram("decrease_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_increase_key() {
        let mut storage: HashMapHeapStorage = HashMap::with_capacity(1024);
        let mut heap: Heap<Timer, HashMapHeapStorage, u64> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000u64 {
            let timer = Timer {
                id: i,
                deadline: i * 2,
            };
            keys.push(heap.push(&mut storage, timer));
        }

        for _ in 0..WARMUP {
            let key = keys[0];
            unsafe { storage.get_unchecked_mut(key) }.data.deadline = 10000;
            heap.increase_key(&mut storage, key);
            unsafe { storage.get_unchecked_mut(key) }.data.deadline = 0;
            heap.decrease_key(&mut storage, key);
        }

        for i in 0..ITERATIONS {
            let key = keys[i % 1000];
            let original = unsafe { storage.get_unchecked(key) }.data.deadline;

            unsafe { storage.get_unchecked_mut(key) }.data.deadline = 10000;
            let start = rdtscp();
            heap.increase_key(&mut storage, key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();

            unsafe { storage.get_unchecked_mut(key) }.data.deadline = original;
            heap.decrease_key(&mut storage, key);
        }

        print_histogram("increase_key", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_contains() {
        let mut storage: HashMapHeapStorage = HashMap::with_capacity(1024);
        let mut heap: Heap<Timer, HashMapHeapStorage, u64> = Heap::with_capacity(1024);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        let mut keys = Vec::with_capacity(1000);
        for i in 0..1000u64 {
            let timer = Timer { id: i, deadline: i };
            keys.push(heap.push(&mut storage, timer));
        }

        let mid_key = keys[500];
        for _ in 0..WARMUP {
            std::hint::black_box(heap.contains(&storage, mid_key));
        }

        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(heap.contains(&storage, mid_key));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("contains", &hist);
    }

    #[test]
    #[ignore]
    fn bench_heap_timer_workflow() {
        let mut storage: HashMapHeapStorage = HashMap::with_capacity(1024);
        let mut heap: Heap<Timer, HashMapHeapStorage, u64> = Heap::with_capacity(1024);

        let mut hist_insert = Histogram::<u64>::new(3).unwrap();
        let mut hist_fire = Histogram::<u64>::new(3).unwrap();
        let mut hist_cancel = Histogram::<u64>::new(3).unwrap();

        let mut id_counter = 0u64;

        for i in 0..WARMUP {
            let timer = Timer {
                id: id_counter,
                deadline: (i % 100) as u64,
            };
            id_counter += 1;
            let key = heap.push(&mut storage, timer);
            if i % 3 == 0 {
                heap.remove(&mut storage, key);
            } else {
                heap.pop(&mut storage);
            }
        }

        for i in 0..ITERATIONS {
            let timer = Timer {
                id: id_counter,
                deadline: (i % 100) as u64,
            };
            id_counter += 1;

            let start = rdtscp();
            let key = heap.push(&mut storage, timer);
            hist_insert.record(rdtscp() - start).unwrap();

            if i % 3 == 0 {
                let start = rdtscp();
                heap.remove(&mut storage, key);
                hist_cancel.record(rdtscp() - start).unwrap();
            } else {
                let start = rdtscp();
                heap.pop(&mut storage);
                hist_fire.record(rdtscp() - start).unwrap();
            }
        }

        println!("\n=== Timer Workflow (HashMap) ===");
        print_histogram("insert (schedule)", &hist_insert);
        print_histogram("fire (pop)", &hist_fire);
        print_histogram("cancel (remove)", &hist_cancel);
    }

    #[test]
    #[ignore]
    fn bench_heap_all() {
        println!("\n=== Heap Benchmarks (HashMap) ===");
        println!(
            "Run with: cargo test --release bench_hashmap_storage::bench_heap_all -- --ignored --nocapture\n"
        );

        bench_heap_push();
        bench_heap_pop();
        bench_heap_peek();
        bench_heap_remove();
        bench_heap_decrease_key();
        bench_heap_increase_key();
        bench_heap_contains();

        println!();
        bench_heap_timer_workflow();
    }
}
