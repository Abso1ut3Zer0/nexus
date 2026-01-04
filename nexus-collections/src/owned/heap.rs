//! OwnedHeap - a min-heap that owns its storage.

use crate::heap::{BoxedHeapStorage, Drain, DrainWhile, Heap};
use crate::{Full, Index, Storage};

/// A min-heap that owns its storage.
///
/// This is a convenience wrapper around [`Heap`] + [`BoxedHeapStorage`] for cases
/// where you don't need to share storage across multiple data structures.
///
/// For shared storage scenarios (e.g., timers that can be in multiple heaps
/// over their lifetime), use [`Heap`] directly with external storage.
///
/// # Example
///
/// ```
/// use nexus_collections::OwnedHeap;
///
/// let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(100);
///
/// let a = heap.push(10).unwrap();
/// let b = heap.push(5).unwrap();
/// let c = heap.push(15).unwrap();
///
/// // Peek returns minimum
/// assert_eq!(heap.peek(), Some(&5));
///
/// // Cancel by handle
/// heap.remove(a);
///
/// // Pop in sorted order
/// assert_eq!(heap.pop(), Some(5));
/// assert_eq!(heap.pop(), Some(15));
/// ```
pub struct OwnedHeap<T: Ord, Idx: Index = u32> {
    storage: BoxedHeapStorage<T, Idx>,
    heap: Heap<T, BoxedHeapStorage<T, Idx>, Idx>,
}

impl<T: Ord, Idx: Index> OwnedHeap<T, Idx> {
    /// Creates a new heap with the given capacity.
    ///
    /// Capacity is rounded up to the next power of 2.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            storage: BoxedHeapStorage::with_capacity(capacity),
            heap: Heap::with_capacity(capacity),
        }
    }

    /// Returns the number of elements in the heap.
    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    /// Returns `true` if the heap is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Returns the storage capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.capacity()
    }

    // ========================================================================
    // Core operations
    // ========================================================================

    /// Pushes a value onto the heap.
    ///
    /// Returns the index (handle) of the inserted element.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn push(&mut self, value: T) -> Result<Idx, Full<T>> {
        self.heap.push(&mut self.storage, value)
    }

    /// Removes and returns the minimum element.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.heap.pop(&mut self.storage)
    }

    /// Returns a reference to the minimum element without removing it.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        self.heap.peek(&self.storage)
    }

    /// Returns the index of the minimum element without removing it.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn peek_idx(&self) -> Option<Idx> {
        self.heap.peek_idx()
    }

    // ========================================================================
    // Handle-based operations
    // ========================================================================

    /// Removes an element by index.
    ///
    /// Returns `Some(value)` if the element was in the heap, `None` otherwise.
    #[inline]
    pub fn remove(&mut self, idx: Idx) -> Option<T> {
        self.heap.remove(&mut self.storage, idx)
    }

    /// Returns a reference to the element at the given index.
    ///
    /// Returns `None` if the index is invalid or not in the heap.
    #[inline]
    pub fn get(&self, idx: Idx) -> Option<&T> {
        self.storage.get(idx).map(|node| &node.data)
    }

    /// Returns a mutable reference to the element at the given index.
    ///
    /// **Warning:** Modifying the element may break heap order. After modification,
    /// call [`decrease_key`](Self::decrease_key), [`increase_key`](Self::increase_key),
    /// or [`update_key`](Self::update_key) to restore heap order.
    #[inline]
    pub fn get_mut(&mut self, idx: Idx) -> Option<&mut T> {
        self.storage.get_mut(idx).map(|node| &mut node.data)
    }

    // ========================================================================
    // Priority updates
    // ========================================================================

    /// Restores heap order after decreasing an element's priority.
    ///
    /// Call this after using [`get_mut`](Self::get_mut) to decrease an element's value.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not in the heap (debug builds only).
    #[inline]
    pub fn decrease_key(&mut self, idx: Idx) {
        self.heap.decrease_key(&mut self.storage, idx);
    }

    /// Restores heap order after increasing an element's priority.
    ///
    /// Call this after using [`get_mut`](Self::get_mut) to increase an element's value.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not in the heap (debug builds only).
    #[inline]
    pub fn increase_key(&mut self, idx: Idx) {
        self.heap.increase_key(&mut self.storage, idx);
    }

    /// Restores heap order after changing an element's priority.
    ///
    /// Use when you don't know if the priority increased or decreased.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not in the heap (debug builds only).
    #[inline]
    pub fn update_key(&mut self, idx: Idx) {
        self.heap.update_key(&mut self.storage, idx);
    }

    // ========================================================================
    // Bulk operations
    // ========================================================================

    /// Clears the heap, removing all elements.
    pub fn clear(&mut self) {
        self.heap.clear(&mut self.storage);
        self.storage.clear();
    }

    /// Returns an iterator that drains elements in sorted order.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T, BoxedHeapStorage<T, Idx>, Idx> {
        self.heap.drain(&mut self.storage)
    }

    /// Returns an iterator that drains elements while the predicate is true.
    ///
    /// The predicate is called on each minimum element. Draining stops
    /// when the predicate returns `false` or the heap is empty.
    #[inline]
    pub fn drain_while<F>(&mut self, pred: F) -> DrainWhile<'_, T, BoxedHeapStorage<T, Idx>, Idx, F>
    where
        F: FnMut(&T) -> bool,
    {
        self.heap.drain_while(&mut self.storage, pred)
    }
}

impl<T: Ord, Idx: Index> Default for OwnedHeap<T, Idx> {
    fn default() -> Self {
        Self::with_capacity(16)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_empty() {
        let heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);
        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
        assert!(heap.peek().is_none());
    }

    #[test]
    fn push_pop() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        heap.push(10).unwrap();
        heap.push(5).unwrap();
        heap.push(15).unwrap();

        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), Some(10));
        assert_eq!(heap.pop(), Some(15));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn peek() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        assert!(heap.peek().is_none());

        heap.push(10).unwrap();
        assert_eq!(heap.peek(), Some(&10));

        heap.push(5).unwrap();
        assert_eq!(heap.peek(), Some(&5));

        heap.push(15).unwrap();
        assert_eq!(heap.peek(), Some(&5));
    }

    #[test]
    fn remove_by_index() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        let a = heap.push(10).unwrap();
        let b = heap.push(5).unwrap();
        let c = heap.push(15).unwrap();

        // Remove middle
        assert_eq!(heap.remove(a), Some(10));
        assert_eq!(heap.len(), 2);

        // Remaining: 5, 15
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), Some(15));

        // b and c handles are now invalid (removed)
        assert!(heap.get(b).is_none());
        assert!(heap.get(c).is_none());
    }

    #[test]
    fn get_and_get_mut() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        let a = heap.push(10).unwrap();
        let b = heap.push(5).unwrap();

        assert_eq!(heap.get(a), Some(&10));
        assert_eq!(heap.get(b), Some(&5));

        *heap.get_mut(a).unwrap() = 1;
        heap.decrease_key(a);

        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn decrease_key() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        let a = heap.push(10).unwrap();
        heap.push(5).unwrap();

        *heap.get_mut(a).unwrap() = 1;
        heap.decrease_key(a);

        assert_eq!(heap.peek_idx(), Some(a));
        assert_eq!(heap.pop(), Some(1));
    }

    #[test]
    fn increase_key() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        let a = heap.push(1).unwrap();
        heap.push(5).unwrap();

        assert_eq!(heap.peek_idx(), Some(a));

        *heap.get_mut(a).unwrap() = 100;
        heap.increase_key(a);

        assert_ne!(heap.peek_idx(), Some(a));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), Some(100));
    }

    #[test]
    fn update_key() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        let a = heap.push(10).unwrap();
        heap.push(5).unwrap();

        *heap.get_mut(a).unwrap() = 1;
        heap.update_key(a);

        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn clear() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        heap.push(1).unwrap();
        heap.push(2).unwrap();
        heap.push(3).unwrap();

        heap.clear();

        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
    }

    #[test]
    fn drain() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        heap.push(10).unwrap();
        heap.push(5).unwrap();
        heap.push(15).unwrap();
        heap.push(1).unwrap();

        let values: Vec<_> = heap.drain().collect();
        assert_eq!(values, vec![1, 5, 10, 15]);
        assert!(heap.is_empty());
    }

    #[test]
    fn drain_while() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(16);

        heap.push(1).unwrap();
        heap.push(5).unwrap();
        heap.push(10).unwrap();
        heap.push(15).unwrap();

        let values: Vec<_> = heap.drain_while(|&x| x < 10).collect();
        assert_eq!(values, vec![1, 5]);
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn full_returns_error() {
        let mut heap: OwnedHeap<u32> = OwnedHeap::with_capacity(2);

        heap.push(1).unwrap();
        heap.push(2).unwrap();

        let err = heap.push(3);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().into_inner(), 3);
    }

    #[test]
    fn timer_use_case() {
        #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
        struct Timer {
            fire_at: u64,
            id: u32,
        }

        let mut heap: OwnedHeap<Timer> = OwnedHeap::with_capacity(16);

        let t1 = heap
            .push(Timer {
                fire_at: 100,
                id: 1,
            })
            .unwrap();
        let _t2 = heap.push(Timer { fire_at: 50, id: 2 }).unwrap();
        let t3 = heap
            .push(Timer {
                fire_at: 200,
                id: 3,
            })
            .unwrap();

        // Cancel t1
        heap.remove(t1);

        // Reschedule t3
        heap.get_mut(t3).unwrap().fire_at = 25;
        heap.decrease_key(t3);

        // Process expired timers
        let now = 60;
        let expired: Vec<_> = heap.drain_while(|t| t.fire_at <= now).collect();

        assert_eq!(expired.len(), 2);
        assert_eq!(expired[0].id, 3); // fire_at: 25
        assert_eq!(expired[1].id, 2); // fire_at: 50
    }
}
