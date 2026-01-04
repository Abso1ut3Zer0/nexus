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
//! # Example
//!
//! ```
//! use nexus_collections::{BoxedHeapStorage, Heap};
//!
//! let mut storage: BoxedHeapStorage<u64> = BoxedHeapStorage::with_capacity(16);
//! let mut heap: Heap<u64, BoxedHeapStorage<u64>> = Heap::new();
//!
//! let a = heap.push(&mut storage, 3).unwrap();
//! let b = heap.push(&mut storage, 1).unwrap();
//! let c = heap.push(&mut storage, 2).unwrap();
//!
//! assert_eq!(heap.peek(&storage), Some(&1));
//! assert_eq!(heap.pop(&mut storage), Some(1));
//! assert_eq!(heap.pop(&mut storage), Some(2));
//!
//! // Remove by handle - O(log n)
//! assert_eq!(heap.remove(&mut storage, a), Some(3));
//! ```

use std::marker::PhantomData;

use crate::{BoxedStorage, Index, Storage};

pub type BoxedHeapStorage<T, Idx = u32> = BoxedStorage<HeapNode<T, Idx>, Idx>;

/// A node in the heap. Wraps user data with heap position tracking.
#[derive(Debug)]
pub struct HeapNode<T, Idx: Index = u32> {
    pub(crate) data: T,
    pub(crate) heap_pos: Idx, // position in indices vec, or NONE if not in heap
}

impl<T, Idx: Index> HeapNode<T, Idx> {
    #[inline]
    fn new(data: T) -> Self {
        Self {
            data,
            heap_pos: Idx::NONE,
        }
    }
}

/// A min-heap over external storage with O(log n) handle operations.
///
/// # Type Parameters
///
/// - `T`: Element type (must implement `Ord`)
/// - `S`: Storage type (e.g., [`BoxedHeapStorage<T>`])
/// - `Idx`: Index type (default `u32`)
#[derive(Debug)]
pub struct Heap<T: Ord, S, Idx: Index = u32>
where
    S: Storage<HeapNode<T, Idx>, Index = Idx>,
{
    indices: Vec<Idx>,
    _marker: PhantomData<(T, S)>,
}

impl<T: Ord, S, Idx: Index> Default for Heap<T, S, Idx>
where
    S: Storage<HeapNode<T, Idx>, Index = Idx>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord, S, Idx: Index> Heap<T, S, Idx>
where
    S: Storage<HeapNode<T, Idx>, Index = Idx>,
{
    /// Creates an empty heap.
    #[inline]
    pub const fn new() -> Self {
        Self {
            indices: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// Creates an empty heap with pre-allocated capacity.
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

    /// Pushes a value onto the heap.
    ///
    /// Returns the storage index, which can be used for O(log n) removal
    /// or priority updates.
    ///
    /// # Errors
    ///
    /// Returns `Err` if storage is full.
    #[inline]
    pub fn push(&mut self, storage: &mut S, value: T) -> Result<Idx, S::Error> {
        let storage_idx = storage.try_insert(HeapNode::new(value))?;
        let heap_pos = self.indices.len();

        // Set heap position and add to indices
        // Safety: we just inserted this
        unsafe { storage.get_unchecked_mut(storage_idx) }.heap_pos = Idx::from_usize(heap_pos);
        self.indices.push(storage_idx);

        // Restore heap property
        self.sift_up(storage, heap_pos);

        Ok(storage_idx)
    }

    /// Removes and returns the minimum element.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn pop(&mut self, storage: &mut S) -> Option<T> {
        if self.indices.is_empty() {
            return None;
        }

        let storage_idx = self.indices[0];

        // Swap with last and remove
        let last_pos = self.indices.len() - 1;
        if last_pos > 0 {
            self.swap_positions(storage, 0, last_pos);
        }
        self.indices.pop();

        // Clear heap position and remove from storage
        // Safety: storage_idx came from our indices
        unsafe { storage.get_unchecked_mut(storage_idx) }.heap_pos = Idx::NONE;
        let node = storage.remove(storage_idx)?;

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
        Idx: 'a,
    {
        let storage_idx = *self.indices.first()?;
        // Safety: indices only contains valid storage indices
        Some(unsafe { &storage.get_unchecked(storage_idx).data })
    }

    /// Returns the storage index of the minimum element.
    #[inline]
    pub fn peek_idx(&self) -> Option<Idx> {
        self.indices.first().copied()
    }

    // ========================================================================
    // Handle-based operations
    // ========================================================================

    /// Removes an element by its storage index.
    ///
    /// Returns `None` if the index is not in the heap.
    ///
    /// # Time Complexity
    ///
    /// O(log n)
    #[inline]
    pub fn remove(&mut self, storage: &mut S, storage_idx: Idx) -> Option<T> {
        let node = storage.get(storage_idx)?;
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
        // Safety: storage_idx was validated above
        unsafe { storage.get_unchecked_mut(storage_idx) }.heap_pos = Idx::NONE;
        let node = storage.remove(storage_idx)?;

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
    /// Panics if `storage_idx` is not in the heap (debug builds only).
    #[inline]
    pub fn decrease_key(&mut self, storage: &mut S, storage_idx: Idx) {
        let heap_pos = self.get_heap_pos(storage, storage_idx);
        debug_assert!(heap_pos.is_some(), "index not in heap");
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
    /// Panics if `storage_idx` is not in the heap (debug builds only).
    #[inline]
    pub fn increase_key(&mut self, storage: &mut S, storage_idx: Idx) {
        let heap_pos = self.get_heap_pos(storage, storage_idx);
        debug_assert!(heap_pos.is_some(), "index not in heap");
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
    /// Panics if `storage_idx` is not in the heap (debug builds only).
    #[inline]
    pub fn update_key(&mut self, storage: &mut S, storage_idx: Idx) {
        let heap_pos = self.get_heap_pos(storage, storage_idx);
        debug_assert!(heap_pos.is_some(), "index not in heap");
        if heap_pos.is_some() {
            self.sift_update(storage, heap_pos.as_usize());
        }
    }

    /// Returns `true` if the storage index is currently in the heap.
    #[inline]
    pub fn contains(&self, storage: &S, storage_idx: Idx) -> bool {
        storage
            .get(storage_idx)
            .map(|n| n.heap_pos.is_some())
            .unwrap_or(false)
    }

    // ========================================================================
    // Bulk operations
    // ========================================================================

    /// Removes all elements from the heap, deallocating from storage.
    pub fn clear(&mut self, storage: &mut S) {
        for &storage_idx in &self.indices {
            storage.remove(storage_idx);
        }
        self.indices.clear();
    }

    /// Returns an iterator that removes elements in sorted order.
    ///
    /// Each call to `next()` performs a `pop()`, so this yields
    /// elements from smallest to largest.
    #[inline]
    pub fn drain<'a>(&'a mut self, storage: &'a mut S) -> Drain<'a, T, S, Idx> {
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
    /// heap.push(&mut storage, 1).unwrap();
    /// heap.push(&mut storage, 5).unwrap();
    /// heap.push(&mut storage, 10).unwrap();
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
    ) -> DrainWhile<'a, T, S, Idx, F>
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
    fn get_heap_pos(&self, storage: &S, storage_idx: Idx) -> Idx {
        storage
            .get(storage_idx)
            .map(|n| n.heap_pos)
            .unwrap_or(Idx::NONE)
    }

    /// Swaps two positions in the heap and updates heap_pos in nodes.
    #[inline]
    fn swap_positions(&mut self, storage: &mut S, pos_a: usize, pos_b: usize) {
        let idx_a = self.indices[pos_a];
        let idx_b = self.indices[pos_b];

        self.indices.swap(pos_a, pos_b);

        // Safety: indices came from our vec
        unsafe { storage.get_unchecked_mut(idx_a) }.heap_pos = Idx::from_usize(pos_b);
        unsafe { storage.get_unchecked_mut(idx_b) }.heap_pos = Idx::from_usize(pos_a);
    }

    /// Sifts an element up toward the root using hole technique.
    #[inline]
    fn sift_up(&mut self, storage: &mut S, pos: usize) {
        if pos == 0 {
            return;
        }

        // Safety: pos is valid index into heap
        let idx = *unsafe { self.indices.get_unchecked(pos) };
        let mut hole = pos;

        while hole > 0 {
            let parent = (hole - 1) / 2;
            // Safety: parent < hole < len
            let parent_idx = *unsafe { self.indices.get_unchecked(parent) };

            // Safety: both indices are valid in storage
            let current = unsafe { &storage.get_unchecked(idx).data };
            let parent_val = unsafe { &storage.get_unchecked(parent_idx).data };

            if current < parent_val {
                // Move parent down into hole
                *unsafe { self.indices.get_unchecked_mut(hole) } = parent_idx;
                unsafe { storage.get_unchecked_mut(parent_idx) }.heap_pos = Idx::from_usize(hole);
                hole = parent;
            } else {
                break;
            }
        }

        // Place element in final position
        if hole != pos {
            *unsafe { self.indices.get_unchecked_mut(hole) } = idx;
            unsafe { storage.get_unchecked_mut(idx) }.heap_pos = Idx::from_usize(hole);
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
        let idx = *unsafe { self.indices.get_unchecked(pos) };
        let mut hole = pos;

        // Phase 1: Descend to leaf, always following smaller child
        loop {
            let left = 2 * hole + 1;
            if left >= len {
                break;
            }

            let right = left + 1;
            // Safety: left < len
            let left_idx = *unsafe { self.indices.get_unchecked(left) };

            let smaller = if right < len {
                let right_idx = *unsafe { self.indices.get_unchecked(right) };
                // Safety: both indices valid in storage
                let left_val = unsafe { &storage.get_unchecked(left_idx).data };
                let right_val = unsafe { &storage.get_unchecked(right_idx).data };
                if right_val < left_val { right } else { left }
            } else {
                left
            };

            // Safety: smaller < len
            let smaller_idx = *unsafe { self.indices.get_unchecked(smaller) };
            *unsafe { self.indices.get_unchecked_mut(hole) } = smaller_idx;
            unsafe { storage.get_unchecked_mut(smaller_idx) }.heap_pos = Idx::from_usize(hole);
            hole = smaller;
        }

        // Phase 2: Sift up from leaf position back toward original position
        while hole > pos {
            let parent = (hole - 1) / 2;
            // Safety: parent < hole
            let parent_idx = *unsafe { self.indices.get_unchecked(parent) };

            // Safety: both indices valid in storage
            let current = unsafe { &storage.get_unchecked(idx).data };
            let parent_val = unsafe { &storage.get_unchecked(parent_idx).data };

            if current < parent_val {
                *unsafe { self.indices.get_unchecked_mut(hole) } = parent_idx;
                unsafe { storage.get_unchecked_mut(parent_idx) }.heap_pos = Idx::from_usize(hole);
                hole = parent;
            } else {
                break;
            }
        }

        // Place element in final position
        *unsafe { self.indices.get_unchecked_mut(hole) } = idx;
        unsafe { storage.get_unchecked_mut(idx) }.heap_pos = Idx::from_usize(hole);
    }

    /// Sifts in the appropriate direction after an update.
    #[inline]
    fn sift_update(&mut self, storage: &mut S, pos: usize) {
        // Capture which element we're updating BEFORE any sifting
        let storage_idx = *unsafe { self.indices.get_unchecked(pos) };

        // Try sifting up first
        self.sift_up(storage, pos);

        // Check if we moved by looking at the element's current heap_pos
        let current_pos = unsafe { storage.get_unchecked(storage_idx) }
            .heap_pos
            .as_usize();

        // If we didn't move up, try sifting down
        if current_pos == pos {
            self.sift_down(storage, pos);
        }
    }
}

// ============================================================================
// Iterators
// ============================================================================

/// Iterator that drains elements from the heap in sorted order.
pub struct Drain<'a, T: Ord, S, Idx: Index>
where
    S: Storage<HeapNode<T, Idx>, Index = Idx>,
{
    heap: &'a mut Heap<T, S, Idx>,
    storage: &'a mut S,
}

impl<'a, T: Ord, S, Idx: Index> Iterator for Drain<'a, T, S, Idx>
where
    S: Storage<HeapNode<T, Idx>, Index = Idx>,
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

impl<T: Ord, S, Idx: Index> ExactSizeIterator for Drain<'_, T, S, Idx> where
    S: Storage<HeapNode<T, Idx>, Index = Idx>
{
}

impl<T: Ord, S, Idx: Index> Drop for Drain<'_, T, S, Idx>
where
    S: Storage<HeapNode<T, Idx>, Index = Idx>,
{
    fn drop(&mut self) {
        // Exhaust remaining elements
        for _ in self.by_ref() {}
    }
}

/// Iterator that drains elements while a predicate holds.
pub struct DrainWhile<'a, T: Ord, S, Idx: Index, F>
where
    S: Storage<HeapNode<T, Idx>, Index = Idx>,
    F: FnMut(&T) -> bool,
{
    heap: &'a mut Heap<T, S, Idx>,
    storage: &'a mut S,
    pred: F,
}

impl<'a, T: Ord, S, Idx: Index, F> Iterator for DrainWhile<'a, T, S, Idx, F>
where
    S: Storage<HeapNode<T, Idx>, Index = Idx>,
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
        assert!(heap.peek_idx().is_none());
    }

    #[test]
    fn push_single() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let idx = heap.push(&mut storage, 42).unwrap();

        assert_eq!(heap.len(), 1);
        assert!(!heap.is_empty());
        assert_eq!(heap.peek(&storage), Some(&42));
        assert_eq!(heap.peek_idx(), Some(idx));
    }

    #[test]
    fn push_maintains_min_heap() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 3).unwrap();
        assert_eq!(heap.peek(&storage), Some(&3));

        heap.push(&mut storage, 1).unwrap();
        assert_eq!(heap.peek(&storage), Some(&1));

        heap.push(&mut storage, 2).unwrap();
        assert_eq!(heap.peek(&storage), Some(&1));

        heap.push(&mut storage, 0).unwrap();
        assert_eq!(heap.peek(&storage), Some(&0));
    }

    #[test]
    fn pop_returns_min() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 3).unwrap();
        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 2).unwrap();

        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn pop_returns_sorted_order() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 5).unwrap();
        heap.push(&mut storage, 3).unwrap();
        heap.push(&mut storage, 7).unwrap();
        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 4).unwrap();

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

        heap.push(&mut storage, 42).unwrap();

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

        let _a = heap.push(&mut storage, 3).unwrap();
        let _b = heap.push(&mut storage, 1).unwrap();
        let c = heap.push(&mut storage, 2).unwrap();

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

        heap.push(&mut storage, 3).unwrap();
        let min_idx = heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 2).unwrap();

        assert_eq!(heap.remove(&mut storage, min_idx), Some(1));
        assert_eq!(heap.peek(&storage), Some(&2));
    }

    #[test]
    fn remove_last_by_handle() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 2).unwrap();
        let last = heap.push(&mut storage, 3).unwrap();

        assert_eq!(heap.remove(&mut storage, last), Some(3));
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn remove_invalid_returns_none() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let idx = heap.push(&mut storage, 1).unwrap();
        heap.pop(&mut storage);

        // Index no longer in heap
        assert_eq!(heap.remove(&mut storage, idx), None);
    }

    #[test]
    fn contains() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let idx = heap.push(&mut storage, 42).unwrap();
        assert!(heap.contains(&storage, idx));

        heap.pop(&mut storage);
        assert!(!heap.contains(&storage, idx));
    }

    #[test]
    fn decrease_key() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 1).unwrap();
        let idx = heap.push(&mut storage, 10).unwrap();
        heap.push(&mut storage, 5).unwrap();

        // 10 is not the min
        assert_eq!(heap.peek(&storage), Some(&1));

        // Decrease 10 to 0 (need mutable access to data)
        unsafe { storage.get_unchecked_mut(idx) }.data = 0;
        heap.decrease_key(&mut storage, idx);

        // Now it's the min
        assert_eq!(heap.peek(&storage), Some(&0));
    }

    #[test]
    fn increase_key() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let idx = heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 5).unwrap();
        heap.push(&mut storage, 10).unwrap();

        // 1 is the min
        assert_eq!(heap.peek(&storage), Some(&1));

        // Increase 1 to 100
        unsafe { storage.get_unchecked_mut(idx) }.data = 100;
        heap.increase_key(&mut storage, idx);

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

        heap.push(&mut storage, 1).unwrap();
        let idx = heap.push(&mut storage, 10).unwrap();
        heap.push(&mut storage, 5).unwrap();

        unsafe { storage.get_unchecked_mut(idx) }.data = 0;
        heap.update_key(&mut storage, idx);

        assert_eq!(heap.peek(&storage), Some(&0));
    }

    #[test]
    fn update_key_increase() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let idx = heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 5).unwrap();
        heap.push(&mut storage, 10).unwrap();

        unsafe { storage.get_unchecked_mut(idx) }.data = 100;
        heap.update_key(&mut storage, idx);

        assert_eq!(heap.peek(&storage), Some(&5));
    }

    // ========================================================================
    // Edge Cases
    // ========================================================================

    #[test]
    fn single_element_pop() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 42).unwrap();
        assert_eq!(heap.pop(&mut storage), Some(42));
        assert!(heap.is_empty());
    }

    #[test]
    fn single_element_remove() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        let idx = heap.push(&mut storage, 42).unwrap();
        assert_eq!(heap.remove(&mut storage, idx), Some(42));
        assert!(heap.is_empty());
    }

    #[test]
    fn two_elements() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 2).unwrap();
        heap.push(&mut storage, 1).unwrap();

        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(2));
    }

    #[test]
    fn duplicates() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 1).unwrap();

        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(1));
        assert_eq!(heap.pop(&mut storage), Some(1));
        assert!(heap.is_empty());
    }

    // ========================================================================
    // Bulk Operations
    // ========================================================================

    #[test]
    fn clear() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 2).unwrap();
        heap.push(&mut storage, 3).unwrap();

        heap.clear(&mut storage);

        assert!(heap.is_empty());
        assert!(storage.is_empty());
    }

    #[test]
    fn drain_sorted_order() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 5).unwrap();
        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 3).unwrap();
        heap.push(&mut storage, 2).unwrap();
        heap.push(&mut storage, 4).unwrap();

        let values: Vec<_> = heap.drain(&mut storage).collect();
        assert_eq!(values, vec![1, 2, 3, 4, 5]);
        assert!(heap.is_empty());
    }

    #[test]
    fn drain_partial_then_drop() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 2).unwrap();
        heap.push(&mut storage, 3).unwrap();

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

        heap.push(&mut storage, 10).unwrap();
        heap.push(&mut storage, 20).unwrap();
        heap.push(&mut storage, 30).unwrap();
        heap.push(&mut storage, 40).unwrap();
        heap.push(&mut storage, 50).unwrap();

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

        heap.push(&mut storage, 10).unwrap();
        heap.push(&mut storage, 20).unwrap();

        let expired: Vec<_> = heap.drain_while(&mut storage, |&t| t < 5).collect();
        assert!(expired.is_empty());
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn drain_while_all_match() {
        let mut storage = BoxedHeapStorage::with_capacity(16);
        let mut heap: Heap<u64, _> = Heap::new();

        heap.push(&mut storage, 1).unwrap();
        heap.push(&mut storage, 2).unwrap();
        heap.push(&mut storage, 3).unwrap();

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

        let a = heap.push(&mut storage, 1).unwrap();
        heap.pop(&mut storage);

        // Slot should be reused
        let b = heap.push(&mut storage, 2).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn storage_reuse_after_remove() {
        let mut storage = BoxedHeapStorage::with_capacity(4);
        let mut heap: Heap<u64, _> = Heap::new();

        let a = heap.push(&mut storage, 1).unwrap();
        heap.remove(&mut storage, a);

        let b = heap.push(&mut storage, 2).unwrap();
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
            heap.push(&mut storage, i).unwrap();
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
            heap.push(&mut storage, i).unwrap();
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

        let mut indices = Vec::new();
        for i in 0..100 {
            indices.push(heap.push(&mut storage, i).unwrap());
        }

        // Remove every other element
        for (i, &idx) in indices.iter().enumerate() {
            if i % 2 == 0 {
                heap.remove(&mut storage, idx);
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

        heap.push(
            &mut storage,
            Task {
                priority: 3,
                name: "low",
            },
        )
        .unwrap();
        heap.push(
            &mut storage,
            Task {
                priority: 1,
                name: "high",
            },
        )
        .unwrap();
        heap.push(
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
