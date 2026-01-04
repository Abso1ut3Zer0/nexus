//! OwnedList - a doubly-linked list that owns its storage.

use crate::list::{BoxedListStorage, Cursor, Drain, Iter, IterMut, Keys, List};
use crate::{BoundedStorage, Full, Key};

/// A doubly-linked list that owns its storage.
///
/// This is a convenience wrapper around [`List`] + [`BoxedListStorage`] for cases
/// where you don't need to share storage across multiple data structures.
///
/// For shared storage scenarios (e.g., multiple queues sharing one pool),
/// use [`List`] directly with external storage.
///
/// # Example
///
/// ```
/// use nexus_collections::OwnedList;
///
/// let mut list: OwnedList<u64> = OwnedList::with_capacity(100);
///
/// let a = list.try_push_back(1).unwrap();
/// let b = list.try_push_back(2).unwrap();
/// let c = list.try_push_back(3).unwrap();
///
/// assert_eq!(list.len(), 3);
/// assert_eq!(list.get(b), Some(&2));
///
/// // Remove from middle - O(1)
/// let value = list.remove(b);
/// assert_eq!(value, Some(2));
/// assert_eq!(list.len(), 2);
///
/// // Iterate
/// let values: Vec<_> = list.iter().copied().collect();
/// assert_eq!(values, vec![1, 3]);
/// ```
pub struct OwnedList<T, K: Key = u32> {
    storage: BoxedListStorage<T, K>,
    list: List<T, BoxedListStorage<T, K>, K>,
}

impl<T, K: Key> OwnedList<T, K> {
    /// Creates a new list with the given capacity.
    ///
    /// Capacity is rounded up to the next power of 2.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            storage: BoxedListStorage::with_capacity(capacity),
            list: List::new(),
        }
    }

    /// Returns the number of elements in the list.
    #[inline]
    pub fn len(&self) -> usize {
        self.list.len()
    }

    /// Returns `true` if the list is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    /// Returns the storage capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.capacity()
    }

    /// Returns the head node's key, or `None` if empty.
    #[inline]
    pub fn front_key(&self) -> Option<K> {
        self.list.front_key()
    }

    /// Returns the tail node's key, or `None` if empty.
    #[inline]
    pub fn back_key(&self) -> Option<K> {
        self.list.back_key()
    }

    // ========================================================================
    // Insert operations
    // ========================================================================

    /// Pushes a value to the back of the list.
    ///
    /// Returns the key of the inserted node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn try_push_back(&mut self, value: T) -> Result<K, Full<T>> {
        self.list.try_push_back(&mut self.storage, value)
    }

    /// Pushes a value to the front of the list.
    ///
    /// Returns the key of the inserted node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn try_push_front(&mut self, value: T) -> Result<K, Full<T>> {
        self.list.try_push_front(&mut self.storage, value)
    }

    /// Inserts a value after an existing node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `after` is not a valid key.
    #[inline]
    pub fn try_insert_after(&mut self, after: K, value: T) -> Result<K, Full<T>> {
        self.list.try_insert_after(&mut self.storage, after, value)
    }

    /// Inserts a value before an existing node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `before` is not a valid key.
    #[inline]
    pub fn try_insert_before(&mut self, before: K, value: T) -> Result<K, Full<T>> {
        self.list
            .try_insert_before(&mut self.storage, before, value)
    }

    // ========================================================================
    // Remove operations
    // ========================================================================

    /// Removes and returns the front element.
    ///
    /// Returns `None` if the list is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        self.list.pop_front(&mut self.storage)
    }

    /// Removes and returns the back element.
    ///
    /// Returns `None` if the list is empty.
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        self.list.pop_back(&mut self.storage)
    }

    /// Removes and returns the element at the given key.
    ///
    /// Returns `None` if the key is invalid.
    #[inline]
    pub fn remove(&mut self, key: K) -> Option<T> {
        self.list.remove(&mut self.storage, key)
    }

    // ========================================================================
    // Access
    // ========================================================================

    /// Returns a reference to the element at the given key.
    #[inline]
    pub fn get(&self, key: K) -> Option<&T> {
        self.list.get(&self.storage, key)
    }

    /// Returns a mutable reference to the element at the given key.
    #[inline]
    pub fn get_mut(&mut self, key: K) -> Option<&mut T> {
        self.list.get_mut(&mut self.storage, key)
    }

    /// Returns a reference to the front element.
    #[inline]
    pub fn front(&self) -> Option<&T> {
        self.list.front(&self.storage)
    }

    /// Returns a mutable reference to the front element.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.list.front_mut(&mut self.storage)
    }

    /// Returns a reference to the back element.
    #[inline]
    pub fn back(&self) -> Option<&T> {
        self.list.back(&self.storage)
    }

    /// Returns a mutable reference to the back element.
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.list.back_mut(&mut self.storage)
    }

    // ========================================================================
    // Bulk operations
    // ========================================================================

    /// Clears the list, removing all elements.
    ///
    /// This drops all values and resets both the list and storage.
    pub fn clear(&mut self) {
        self.list.clear(&mut self.storage);
        self.storage.clear();
    }

    /// Moves a node to the back of the list.
    ///
    /// Useful for LRU caches.
    ///
    /// # Panics
    ///
    /// Panics if `key` is not valid.
    #[inline]
    pub fn move_to_back(&mut self, key: K) {
        self.list.move_to_back(&mut self.storage, key);
    }

    /// Moves a node to the front of the list.
    ///
    /// # Panics
    ///
    /// Panics if `key` is not valid.
    #[inline]
    pub fn move_to_front(&mut self, key: K) {
        self.list.move_to_front(&mut self.storage, key);
    }

    // ========================================================================
    // Position checks
    // ========================================================================

    /// Returns `true` if the node is currently the head of the list.
    #[inline]
    pub fn is_head(&self, key: K) -> bool {
        self.list.is_head(key)
    }

    /// Returns `true` if the node is currently the tail of the list.
    #[inline]
    pub fn is_tail(&self, key: K) -> bool {
        self.list.is_tail(key)
    }

    // ========================================================================
    // Navigation
    // ========================================================================

    /// Returns the key of the next node after `key`.
    ///
    /// Returns `None` if `key` is the tail or invalid.
    #[inline]
    pub fn next_key(&self, key: K) -> Option<K> {
        self.list.next_key(&self.storage, key)
    }

    /// Returns the key of the previous node before `key`.
    ///
    /// Returns `None` if `key` is the head or invalid.
    #[inline]
    pub fn prev_key(&self, key: K) -> Option<K> {
        self.list.prev_key(&self.storage, key)
    }

    // ========================================================================
    // Iteration
    // ========================================================================

    /// Returns an iterator over references to elements, front to back.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T, BoxedListStorage<T, K>, K> {
        self.list.iter(&self.storage)
    }

    /// Returns an iterator over mutable references to elements, front to back.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T, BoxedListStorage<T, K>, K> {
        self.list.iter_mut(&mut self.storage)
    }

    /// Returns an iterator over keys, front to back.
    #[inline]
    pub fn keys(&self) -> Keys<'_, T, K, BoxedListStorage<T, K>> {
        self.list.keys(&self.storage)
    }

    /// Clears the list, returning an iterator over removed elements.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T, BoxedListStorage<T, K>, K> {
        self.list.drain(&mut self.storage)
    }

    /// Returns a cursor positioned at the front of the list.
    #[inline]
    pub fn cursor_front(&mut self) -> Cursor<'_, T, BoxedListStorage<T, K>, K> {
        self.list.cursor_front(&mut self.storage)
    }

    /// Returns a cursor positioned at the back of the list.
    #[inline]
    pub fn cursor_back(&mut self) -> Cursor<'_, T, BoxedListStorage<T, K>, K> {
        self.list.cursor_back(&mut self.storage)
    }
}

impl<T, K: Key> Default for OwnedList<T, K> {
    fn default() -> Self {
        Self::with_capacity(16)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_empty() {
        let list: OwnedList<u64> = OwnedList::with_capacity(16);
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert!(list.front_key().is_none());
        assert!(list.back_key().is_none());
    }

    #[test]
    fn push_back_pop_front() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        list.try_push_back(3).unwrap();

        assert_eq!(list.len(), 3);

        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), Some(2));
        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), None);
    }

    #[test]
    fn push_front_pop_back() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_front(1).unwrap();
        list.try_push_front(2).unwrap();
        list.try_push_front(3).unwrap();

        assert_eq!(list.pop_back(), Some(1));
        assert_eq!(list.pop_back(), Some(2));
        assert_eq!(list.pop_back(), Some(3));
    }

    #[test]
    fn remove_by_key() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.try_push_back(1).unwrap();
        let b = list.try_push_back(2).unwrap();
        let c = list.try_push_back(3).unwrap();

        let removed = list.remove(b);
        assert_eq!(removed, Some(2));
        assert_eq!(list.len(), 2);

        // a and c still accessible
        assert_eq!(list.get(a), Some(&1));
        assert_eq!(list.get(c), Some(&3));

        // b is gone
        assert!(list.get(b).is_none());
    }

    #[test]
    fn front_and_back() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        assert!(list.front().is_none());
        assert!(list.back().is_none());

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        list.try_push_back(3).unwrap();

        assert_eq!(list.front(), Some(&1));
        assert_eq!(list.back(), Some(&3));
    }

    #[test]
    fn front_mut_and_back_mut() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();

        *list.front_mut().unwrap() = 10;
        *list.back_mut().unwrap() = 20;

        assert_eq!(list.front(), Some(&10));
        assert_eq!(list.back(), Some(&20));
    }

    #[test]
    fn insert_after_and_before() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.try_push_back(1).unwrap();
        let _c = list.try_push_back(3).unwrap();

        // Insert 2 after 1
        list.try_insert_after(a, 2).unwrap();

        // Insert 0 before 1
        list.try_insert_before(a, 0).unwrap();

        // Order: 0, 1, 2, 3
        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![0, 1, 2, 3]);
    }

    #[test]
    fn clear() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        list.try_push_back(3).unwrap();

        list.clear();

        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn move_to_back_and_front() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        let c = list.try_push_back(3).unwrap();

        list.move_to_back(a);
        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![2, 3, 1]);

        list.move_to_front(c);
        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![3, 2, 1]);
    }

    #[test]
    fn iter() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        list.try_push_back(3).unwrap();

        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![1, 2, 3]);
    }

    #[test]
    fn iter_rev() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        list.try_push_back(3).unwrap();

        let values: Vec<_> = list.iter().rev().copied().collect();
        assert_eq!(values, vec![3, 2, 1]);
    }

    #[test]
    fn iter_mut() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        list.try_push_back(3).unwrap();

        for val in list.iter_mut() {
            *val *= 10;
        }

        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![10, 20, 30]);
    }

    #[test]
    fn drain() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        list.try_push_back(3).unwrap();

        let values: Vec<_> = list.drain().collect();
        assert_eq!(values, vec![1, 2, 3]);
        assert!(list.is_empty());
    }

    #[test]
    fn cursor_walk_and_remove() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();
        list.try_push_back(3).unwrap();

        let mut cursor = list.cursor_front();

        // Remove even numbers
        while let Some(&val) = cursor.current() {
            if val % 2 == 0 {
                cursor.remove_current();
            } else {
                cursor.move_next();
            }
        }

        drop(cursor);

        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![1, 3]);
    }

    #[test]
    fn full_returns_error() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(2);

        list.try_push_back(1).unwrap();
        list.try_push_back(2).unwrap();

        let err = list.try_push_back(3);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().into_inner(), 3);
    }

    #[test]
    fn keys() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.try_push_back(1).unwrap();
        let b = list.try_push_back(2).unwrap();
        let c = list.try_push_back(3).unwrap();

        let keys: Vec<_> = list.keys().collect();
        assert_eq!(keys, vec![a, b, c]);
    }

    #[test]
    fn next_and_prev_key() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.try_push_back(1).unwrap();
        let b = list.try_push_back(2).unwrap();
        let c = list.try_push_back(3).unwrap();

        assert_eq!(list.next_key(a), Some(b));
        assert_eq!(list.next_key(b), Some(c));
        assert_eq!(list.next_key(c), None);

        assert_eq!(list.prev_key(a), None);
        assert_eq!(list.prev_key(b), Some(a));
        assert_eq!(list.prev_key(c), Some(b));
    }

    #[test]
    fn is_head_and_is_tail() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.try_push_back(1).unwrap();
        let b = list.try_push_back(2).unwrap();
        let c = list.try_push_back(3).unwrap();

        assert!(list.is_head(a));
        assert!(!list.is_head(b));
        assert!(!list.is_head(c));

        assert!(!list.is_tail(a));
        assert!(!list.is_tail(b));
        assert!(list.is_tail(c));
    }
}
