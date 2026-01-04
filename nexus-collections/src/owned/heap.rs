//! OwnedHeap - a min-heap that owns its storage.

use crate::heap::{BoxedHeapStorage, Heap};
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
/// *heap.get_mut(c).unwrap() = 5;
/// heap.decrease_key(c);
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

    /// Returns a mutable reference to the minimum element.
    ///
    /// **Warning:** Modifying the value may violate the heap property.
    /// Call [`update_key`](Self::update_key) after modification if the
    /// relative ordering may have changed.
    #[inline]
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.heap.peek_mut(&mut self.storage)
    }

    /// Returns a reference to the element at the given key.
    ///
    /// Returns `None` if the key is invalid.
    #[inline]
    pub fn get(&self, key: K) -> Option<&T> {
        self.heap.get(&self.storage, key)
    }

    /// Returns a mutable reference to the element at the given key.
    ///
    /// **Warning:** Modifying the value may violate the heap property.
    /// Call the appropriate key update method after modification:
    /// - [`decrease_key`](Self::decrease_key) if value decreased
    /// - [`increase_key`](Self::increase_key) if value increased
    /// - [`update_key`](Self::update_key) if direction unknown
    #[inline]
    pub fn get_mut(&mut self, key: K) -> Option<&mut T> {
        self.heap.get_mut(&mut self.storage, key)
    }

    /// Returns `true` if the key is valid and the element is in the heap.
    #[inline]
    pub fn contains(&self, key: K) -> bool {
        self.heap.contains(&self.storage, key)
    }

    // ========================================================================
    // Priority updates
    // ========================================================================

    /// Restores heap property after decreasing an element's priority.
    ///
    /// Call this after modifying an element to a *smaller* value.
    /// This is O(log n) but faster than [`update_key`](Self::update_key)
    /// when you know the direction of change.
    ///
    /// # Panics
    ///
    /// Panics if `key` is invalid.
    #[inline]
    pub fn decrease_key(&mut self, key: K) {
        self.heap.decrease_key(&mut self.storage, key);
    }

    /// Restores heap property after increasing an element's priority.
    ///
    /// Call this after modifying an element to a *larger* value.
    /// This is O(log n) but faster than [`update_key`](Self::update_key)
    /// when you know the direction of change.
    ///
    /// # Panics
    ///
    /// Panics if `key` is invalid.
    #[inline]
    pub fn increase_key(&mut self, key: K) {
        self.heap.increase_key(&mut self.storage, key);
    }

    /// Restores heap property after modifying an element's priority.
    ///
    /// Call this after modifying an element when you don't know whether
    /// the value increased or decreased. Slightly slower than the
    /// directional variants.
    ///
    /// # Panics
    ///
    /// Panics if `key` is invalid.
    #[inline]
    pub fn update_key(&mut self, key: K) {
        self.heap.update_key(&mut self.storage, key);
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
    pub fn drain_while<F>(&mut self, pred: F) -> DrainWhile<'_, T, K, F>
    where
        F: FnMut(&T) -> bool,
    {
        DrainWhile {
            heap: &mut self.heap,
            storage: &mut self.storage,
            pred,
        }
    }
}

impl<T: Ord, K: Key> Default for OwnedHeap<T, K> {
    fn default() -> Self {
        Self::with_capacity(16)
    }
}

/// An iterator that drains elements while a predicate holds.
///
/// Created by [`OwnedHeap::drain_while`].
pub struct DrainWhile<'a, T: Ord, K: Key, F>
where
    F: FnMut(&T) -> bool,
{
    heap: &'a mut Heap<T, BoxedHeapStorage<T, K>, K>,
    storage: &'a mut BoxedHeapStorage<T, K>,
    pred: F,
}

impl<'a, T: Ord, K: Key, F> Iterator for DrainWhile<'a, T, K, F>
where
    F: FnMut(&T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
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

    #[test]
    fn new_is_empty() {
        let heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);
        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
        assert!(heap.peek().is_none());
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
        assert_eq!(heap.get(a), Some(&5));
    }

    #[test]
    fn get_and_get_mut() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        let a = heap.try_push(5).unwrap();
        let b = heap.try_push(1).unwrap();

        assert_eq!(heap.get(a), Some(&5));
        assert_eq!(heap.get(b), Some(&1));

        *heap.get_mut(a).unwrap() = 10;
        assert_eq!(heap.get(a), Some(&10));
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
    fn decrease_key() {
        let mut heap: OwnedHeap<i64> = OwnedHeap::with_capacity(16);

        let a = heap.try_push(10).unwrap();
        let b = heap.try_push(20).unwrap();
        let c = heap.try_push(30).unwrap();

        assert_eq!(heap.peek(), Some(&10));

        // Decrease c to become minimum
        *heap.get_mut(c).unwrap() = 5;
        heap.decrease_key(c);

        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), Some(10));
        assert_eq!(heap.pop(), Some(20));
    }

    #[test]
    fn increase_key() {
        let mut heap: OwnedHeap<i64> = OwnedHeap::with_capacity(16);

        let a = heap.try_push(10).unwrap();
        let _b = heap.try_push(20).unwrap();
        let _c = heap.try_push(30).unwrap();

        assert_eq!(heap.peek(), Some(&10));

        // Increase a so it's no longer minimum
        *heap.get_mut(a).unwrap() = 25;
        heap.increase_key(a);

        assert_eq!(heap.peek(), Some(&20));
        assert_eq!(heap.pop(), Some(20));
        assert_eq!(heap.pop(), Some(25));
        assert_eq!(heap.pop(), Some(30));
    }

    #[test]
    fn update_key() {
        let mut heap: OwnedHeap<i64> = OwnedHeap::with_capacity(16);

        let a = heap.try_push(10).unwrap();
        let b = heap.try_push(20).unwrap();
        let c = heap.try_push(30).unwrap();

        // Decrease
        *heap.get_mut(c).unwrap() = 5;
        heap.update_key(c);
        assert_eq!(heap.peek(), Some(&5));

        // Increase
        *heap.get_mut(c).unwrap() = 100;
        heap.update_key(c);
        assert_eq!(heap.peek(), Some(&10));
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
    fn peek_mut() {
        let mut heap: OwnedHeap<u64> = OwnedHeap::with_capacity(16);

        heap.try_push(5).unwrap();
        heap.try_push(10).unwrap();

        // Modify min in place
        *heap.peek_mut().unwrap() = 1;
        // Note: since we decreased, heap property still holds

        assert_eq!(heap.peek(), Some(&1));
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

        let t1 = timers
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
        timers.get_mut(t3).unwrap().deadline = 75;
        timers.decrease_key(t3);
        assert_eq!(timers.peek().unwrap().id, 3);

        // Fire expired timers (current time = 80)
        let fired: Vec<_> = timers.drain_while(|t| t.deadline <= 80).collect();
        assert_eq!(fired.len(), 1);
        assert_eq!(fired[0].id, 3);
    }
}
