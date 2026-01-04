//! OwnedHeap - a min-heap that owns its storage.

use crate::heap::{BoxedHeapStorage, Drain, DrainWhile, Heap};
use crate::{BoundedStorage, Full, Key};

/// A min-heap that owns its storage.
///
/// This is a convenience wrapper around [`Heap`] + [`BoxedHeapStorage`] for cases
/// where you don't need to share storage across multiple data structures.
///
/// For shared storage scenarios (e.g., orders in a heap that can be moved to queues),
/// use [`Heap`] directly with external storage.
///
/// # Example
///
/// ```
/// use nexus_collections::OwnedHeap;
///
/// let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(100);
///
/// let a = heap.try_push(5).unwrap();
/// let b = heap.try_push(1).unwrap();
/// let c = heap.try_push(3).unwrap();
///
/// assert_eq!(heap.len(), 3);
/// assert_eq!(heap.peek(), Some(&1));
///
/// // Pop minimum
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), Some(3));
/// assert_eq!(heap.pop(), Some(5));
/// assert_eq!(heap.pop(), None);
/// ```
///
/// # Priority Updates
///
/// The heap supports O(log n) priority updates via key:
///
/// ```
/// use nexus_collections::OwnedHeap;
///
/// let mut heap: OwnedHeap<i64> = OwnedHeap::with_capacity(100);
///
/// let a = heap.try_push(10).unwrap();
/// let b = heap.try_push(20).unwrap();
/// let c = heap.try_push(30).unwrap();
///
/// // Decrease priority of 'c' to make it the new minimum
/// heap.decrease_with(c, |v| *v = 5);
///
/// assert_eq!(heap.peek(), Some(&5));
/// ```
pub struct OwnedHeap<T: Ord, K: Key = u32> {
    storage: BoxedHeapStorage<T, K>,
    heap: Heap<T, BoxedHeapStorage<T, K>, K>,
}

impl<T: Ord, K: Key> OwnedHeap<T, K> {
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
    // Insert operations
    // ========================================================================

    /// Pushes a value onto the heap.
    ///
    /// Returns the key of the inserted element, which can be used for
    /// O(1) access, O(log n) removal, or priority updates.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn try_push(&mut self, value: T) -> Result<K, Full<T>> {
        self.heap.try_push(&mut self.storage, value)
    }

    // ========================================================================
    // Remove operations
    // ========================================================================

    /// Removes and returns the minimum element.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.heap.pop(&mut self.storage)
    }

    /// Removes and returns the element at the given key.
    ///
    /// Returns `None` if the key is invalid or not in the heap.
    #[inline]
    pub fn remove(&mut self, key: K) -> Option<T> {
        self.heap.remove(&mut self.storage, key)
    }

    // ========================================================================
    // Access
    // ========================================================================

    /// Returns a reference to the minimum element.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        self.heap.peek(&self.storage)
    }

    /// Returns the storage key of the minimum element.
    #[inline]
    pub fn peek_key(&self) -> Option<K> {
        self.heap.peek_key()
    }

    /// Returns `true` if the key is valid and the element is in the heap.
    #[inline]
    pub fn contains(&self, key: K) -> bool {
        self.heap.contains(&self.storage, key)
    }

    // ========================================================================
    // Priority updates
    // ========================================================================

    /// Replaces the value at key with a new value, restoring heap property.
    ///
    /// Returns the old value, or `None` if the key is invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_collections::OwnedHeap;
    ///
    /// let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);
    /// let key = heap.try_push(10).unwrap();
    ///
    /// let old = heap.replace(key, 5);
    /// assert_eq!(old, Some(10));
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    #[inline]
    pub fn replace(&mut self, key: K, value: T) -> Option<T> {
        self.heap.replace(&mut self.storage, key, value)
    }

    /// Mutates the value in place and sifts up (caller asserts value decreased).
    ///
    /// Use this when you know the new value is *smaller* than before.
    ///
    /// # Panics
    ///
    /// Panics if `key` is invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_collections::OwnedHeap;
    ///
    /// let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);
    /// heap.try_push(10).unwrap();
    /// let key = heap.try_push(20).unwrap();
    ///
    /// // Decrease 20 to 5, making it the new minimum
    /// heap.decrease_with(key, |v| *v = 5);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    #[inline]
    pub fn decrease_with<F>(&mut self, key: K, f: F)
    where
        F: FnOnce(&mut T),
    {
        self.heap.decrease_with(&mut self.storage, key, f);
    }

    /// Mutates the value in place and sifts down (caller asserts value increased).
    ///
    /// Use this when you know the new value is *larger* than before.
    ///
    /// # Panics
    ///
    /// Panics if `key` is invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_collections::OwnedHeap;
    ///
    /// let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);
    /// let key = heap.try_push(5).unwrap();
    /// heap.try_push(10).unwrap();
    ///
    /// // Increase 5 to 100, so 10 becomes the new minimum
    /// heap.increase_with(key, |v| *v = 100);
    /// assert_eq!(heap.peek(), Some(&10));
    /// ```
    #[inline]
    pub fn increase_with<F>(&mut self, key: K, f: F)
    where
        F: FnOnce(&mut T),
    {
        self.heap.increase_with(&mut self.storage, key, f);
    }

    // ========================================================================
    // Bulk operations
    // ========================================================================

    /// Clears the heap, removing all elements.
    ///
    /// This drops all values and resets both the heap and storage.
    pub fn clear(&mut self) {
        self.heap.clear(&mut self.storage);
        self.storage.clear();
    }

    /// Returns an iterator that removes elements in sorted order.
    ///
    /// Each call to `next()` performs a `pop()`, so this yields
    /// elements from smallest to largest.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T, BoxedHeapStorage<T, K>, K> {
        self.heap.drain(&mut self.storage)
    }

    /// Removes elements while the predicate returns `true`.
    ///
    /// The predicate receives a reference to the current minimum.
    /// Elements are removed in sorted order (smallest first).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_collections::OwnedHeap;
    ///
    /// let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);
    /// heap.try_push(1).unwrap();
    /// heap.try_push(5).unwrap();
    /// heap.try_push(3).unwrap();
    /// heap.try_push(7).unwrap();
    ///
    /// // Remove all elements less than 4
    /// let removed: Vec<_> = heap.drain_while(|&x| x < 4).collect();
    /// assert_eq!(removed, vec![1, 3]);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    #[inline]
    pub fn drain_while<F>(&mut self, pred: F) -> DrainWhile<'_, T, BoxedHeapStorage<T, K>, K, F>
    where
        F: FnMut(&T) -> bool,
    {
        self.heap.drain_while(&mut self.storage, pred)
    }
}

impl<T: Ord, K: Key> Default for OwnedHeap<T, K> {
    fn default() -> Self {
        Self::with_capacity(16)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_empty() {
        let heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);
        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
        assert!(heap.peek().is_none());
        assert!(heap.peek_key().is_none());
    }

    #[test]
    fn push_pop_order() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        heap.try_push(5).unwrap();
        heap.try_push(1).unwrap();
        heap.try_push(3).unwrap();
        heap.try_push(2).unwrap();
        heap.try_push(4).unwrap();

        assert_eq!(heap.len(), 5);

        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), Some(4));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn peek() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        assert!(heap.peek().is_none());

        heap.try_push(5).unwrap();
        assert_eq!(heap.peek(), Some(&5));

        heap.try_push(1).unwrap();
        assert_eq!(heap.peek(), Some(&1));

        heap.try_push(3).unwrap();
        assert_eq!(heap.peek(), Some(&1));
    }

    #[test]
    fn peek_key() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        assert!(heap.peek_key().is_none());

        let a = heap.try_push(5).unwrap();
        assert_eq!(heap.peek_key(), Some(a));

        let b = heap.try_push(1).unwrap();
        assert_eq!(heap.peek_key(), Some(b)); // 1 is now min
    }

    #[test]
    fn remove_by_key() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        let a = heap.try_push(5).unwrap();
        let b = heap.try_push(1).unwrap();
        let c = heap.try_push(3).unwrap();

        // Remove middle element
        let removed = heap.remove(c);
        assert_eq!(removed, Some(3));
        assert_eq!(heap.len(), 2);

        // Min unchanged
        assert_eq!(heap.peek(), Some(&1));

        // Remove min
        let removed = heap.remove(b);
        assert_eq!(removed, Some(1));
        assert_eq!(heap.peek(), Some(&5));

        // a still valid
        assert!(heap.contains(a));
    }

    #[test]
    fn contains() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        let a = heap.try_push(5).unwrap();
        let b = heap.try_push(1).unwrap();

        assert!(heap.contains(a));
        assert!(heap.contains(b));

        heap.remove(a);
        assert!(!heap.contains(a));
        assert!(heap.contains(b));
    }

    #[test]
    fn replace_decreases() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        heap.try_push(10).unwrap();
        heap.try_push(20).unwrap();
        let c = heap.try_push(30).unwrap();

        assert_eq!(heap.peek(), Some(&10));

        // Replace 30 with 5 - should become new min
        let old = heap.replace(c, 5);
        assert_eq!(old, Some(30));
        assert_eq!(heap.peek(), Some(&5));
    }

    #[test]
    fn replace_increases() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        let a = heap.try_push(10).unwrap();
        heap.try_push(20).unwrap();
        heap.try_push(30).unwrap();

        assert_eq!(heap.peek(), Some(&10));

        // Replace 10 with 100 - 20 should become new min
        let old = heap.replace(a, 100);
        assert_eq!(old, Some(10));
        assert_eq!(heap.peek(), Some(&20));
    }

    #[test]
    fn decrease_with() {
        let mut heap: OwnedHeap<i64> = OwnedHeap::with_capacity(16);

        heap.try_push(10).unwrap();
        heap.try_push(20).unwrap();
        let c = heap.try_push(30).unwrap();

        assert_eq!(heap.peek(), Some(&10));

        // Decrease c to become minimum
        heap.decrease_with(c, |v| *v = 5);

        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), Some(10));
        assert_eq!(heap.pop(), Some(20));
    }

    #[test]
    fn increase_with() {
        let mut heap: OwnedHeap<i64> = OwnedHeap::with_capacity(16);

        let a = heap.try_push(10).unwrap();
        heap.try_push(20).unwrap();
        heap.try_push(30).unwrap();

        assert_eq!(heap.peek(), Some(&10));

        // Increase a so it's no longer minimum
        heap.increase_with(a, |v| *v = 25);

        assert_eq!(heap.peek(), Some(&20));
        assert_eq!(heap.pop(), Some(20));
        assert_eq!(heap.pop(), Some(25));
        assert_eq!(heap.pop(), Some(30));
    }

    #[test]
    fn clear() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        heap.try_push(1).unwrap();
        heap.try_push(2).unwrap();
        heap.try_push(3).unwrap();

        heap.clear();

        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
        assert!(heap.peek().is_none());
    }

    #[test]
    fn drain() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        heap.try_push(5).unwrap();
        heap.try_push(1).unwrap();
        heap.try_push(3).unwrap();

        let values: Vec<_> = heap.drain().collect();
        assert_eq!(values, vec![1, 3, 5]);
        assert!(heap.is_empty());
    }

    #[test]
    fn drain_while() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        heap.try_push(1).unwrap();
        heap.try_push(5).unwrap();
        heap.try_push(3).unwrap();
        heap.try_push(7).unwrap();
        heap.try_push(2).unwrap();

        // Drain elements < 4
        let removed: Vec<_> = heap.drain_while(|&x| x < 4).collect();
        assert_eq!(removed, vec![1, 2, 3]);

        assert_eq!(heap.len(), 2);
        assert_eq!(heap.peek(), Some(&5));
    }

    #[test]
    fn drain_while_empty() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        let removed: Vec<_> = heap.drain_while(|_| true).collect();
        assert!(removed.is_empty());
    }

    #[test]
    fn drain_while_none_match() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        heap.try_push(10).unwrap();
        heap.try_push(20).unwrap();

        let removed: Vec<_> = heap.drain_while(|&x| x < 5).collect();
        assert!(removed.is_empty());
        assert_eq!(heap.len(), 2);
    }

    #[test]
    fn full_returns_error() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(2);

        heap.try_push(1).unwrap();
        heap.try_push(2).unwrap();

        let err = heap.try_push(3);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().into_inner(), 3);
    }

    #[test]
    fn duplicates() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        heap.try_push(5).unwrap();
        heap.try_push(5).unwrap();
        heap.try_push(5).unwrap();

        assert_eq!(heap.len(), 3);
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn default() {
        let heap: OwnedHeap<u64> = OwnedHeap::default();
        assert!(heap.is_empty());
        assert_eq!(heap.capacity(), 16);
    }

    #[test]
    fn timer_use_case() {
        // Simulates a timer wheel
        #[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
        struct Timer {
            deadline: u64,
            id: u64,
        }

        let mut timers: OwnedHeap<Timer> = OwnedHeap::with_capacity(100);

        let _t1 = timers
            .try_push(Timer {
                deadline: 100,
                id: 1,
            })
            .unwrap();
        let t2 = timers
            .try_push(Timer {
                deadline: 50,
                id: 2,
            })
            .unwrap();
        let t3 = timers
            .try_push(Timer {
                deadline: 150,
                id: 3,
            })
            .unwrap();

        // Next timer to fire
        assert_eq!(timers.peek().unwrap().id, 2);

        // Cancel a timer
        timers.remove(t2);
        assert_eq!(timers.peek().unwrap().id, 1);

        // Reschedule timer 3 to fire sooner
        timers.decrease_with(t3, |t| t.deadline = 75);
        assert_eq!(timers.peek().unwrap().id, 3);

        // Fire expired timers (current time = 80)
        let fired: Vec<_> = timers.drain_while(|t| t.deadline <= 80).collect();
        assert_eq!(fired.len(), 1);
        assert_eq!(fired[0].id, 3);
    }
}
