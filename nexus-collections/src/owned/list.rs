//! OwnedList - a doubly-linked list that owns its storage.

use crate::list::{BoxedListStorage, Cursor, Drain, Indices, Iter, IterMut, List};
use crate::{Full, Index};

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
/// let a = list.push_back(1).unwrap();
/// let b = list.push_back(2).unwrap();
/// let c = list.push_back(3).unwrap();
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
pub struct OwnedList<T, Idx: Index = u32> {
    storage: BoxedListStorage<T, Idx>,
    list: List<T, BoxedListStorage<T, Idx>, Idx>,
}

impl<T, Idx: Index> OwnedList<T, Idx> {
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

    /// Returns the head node's index, or `None` if empty.
    #[inline]
    pub fn front_idx(&self) -> Option<Idx> {
        self.list.front_idx()
    }

    /// Returns the tail node's index, or `None` if empty.
    #[inline]
    pub fn back_idx(&self) -> Option<Idx> {
        self.list.back_idx()
    }

    // ========================================================================
    // Insert operations
    // ========================================================================

    /// Pushes a value to the back of the list.
    ///
    /// Returns the index of the inserted node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn push_back(&mut self, value: T) -> Result<Idx, Full<T>> {
        self.list
            .push_back(&mut self.storage, value)
            .map_err(|e| Full(e.into_inner().data))
    }

    /// Pushes a value to the front of the list.
    ///
    /// Returns the index of the inserted node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn push_front(&mut self, value: T) -> Result<Idx, Full<T>> {
        self.list
            .push_front(&mut self.storage, value)
            .map_err(|e| Full(e.into_inner().data))
    }

    /// Inserts a value after an existing node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `after` is not a valid index (debug builds only).
    #[inline]
    pub fn insert_after(&mut self, after: Idx, value: T) -> Result<Idx, Full<T>> {
        self.list
            .insert_after(&mut self.storage, after, value)
            .map_err(|e| Full(e.into_inner().data))
    }

    /// Inserts a value before an existing node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `before` is not a valid index (debug builds only).
    #[inline]
    pub fn insert_before(&mut self, before: Idx, value: T) -> Result<Idx, Full<T>> {
        self.list
            .insert_before(&mut self.storage, before, value)
            .map_err(|e| Full(e.into_inner().data))
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

    /// Removes and returns the element at the given index.
    ///
    /// Returns `None` if the index is invalid.
    #[inline]
    pub fn remove(&mut self, idx: Idx) -> Option<T> {
        self.list.remove(&mut self.storage, idx)
    }

    // ========================================================================
    // Access
    // ========================================================================

    /// Returns a reference to the element at the given index.
    #[inline]
    pub fn get(&self, idx: Idx) -> Option<&T> {
        self.list.get(&self.storage, idx)
    }

    /// Returns a mutable reference to the element at the given index.
    #[inline]
    pub fn get_mut(&mut self, idx: Idx) -> Option<&mut T> {
        self.list.get_mut(&mut self.storage, idx)
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
    /// Panics if `idx` is not valid (debug builds only).
    #[inline]
    pub fn move_to_back(&mut self, idx: Idx) {
        self.list.move_to_back(&mut self.storage, idx);
    }

    /// Moves a node to the front of the list.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid (debug builds only).
    #[inline]
    pub fn move_to_front(&mut self, idx: Idx) {
        self.list.move_to_front(&mut self.storage, idx);
    }

    // ========================================================================
    // Position checks
    // ========================================================================

    /// Returns `true` if the node is currently the head of the list.
    #[inline]
    pub fn is_head(&self, idx: Idx) -> bool {
        self.list.is_head(idx)
    }

    /// Returns `true` if the node is currently the tail of the list.
    #[inline]
    pub fn is_tail(&self, idx: Idx) -> bool {
        self.list.is_tail(idx)
    }

    // ========================================================================
    // Navigation
    // ========================================================================

    /// Returns the index of the next node after `idx`.
    ///
    /// Returns `None` if `idx` is the tail or invalid.
    #[inline]
    pub fn next_idx(&self, idx: Idx) -> Option<Idx> {
        self.list.next_idx(&self.storage, idx)
    }

    /// Returns the index of the previous node before `idx`.
    ///
    /// Returns `None` if `idx` is the head or invalid.
    #[inline]
    pub fn prev_idx(&self, idx: Idx) -> Option<Idx> {
        self.list.prev_idx(&self.storage, idx)
    }

    // ========================================================================
    // Iteration
    // ========================================================================

    /// Returns an iterator over references to elements, front to back.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T, BoxedListStorage<T, Idx>, Idx> {
        self.list.iter(&self.storage)
    }

    /// Returns an iterator over mutable references to elements, front to back.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T, BoxedListStorage<T, Idx>, Idx> {
        self.list.iter_mut(&mut self.storage)
    }

    /// Returns an iterator over indices, front to back.
    #[inline]
    pub fn indices(&self) -> Indices<'_, T, Idx, BoxedListStorage<T, Idx>> {
        self.list.indices(&self.storage)
    }

    /// Clears the list, returning an iterator over removed elements.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T, BoxedListStorage<T, Idx>, Idx> {
        self.list.drain(&mut self.storage)
    }

    /// Returns a cursor positioned at the front of the list.
    #[inline]
    pub fn cursor_front(&mut self) -> Cursor<'_, T, BoxedListStorage<T, Idx>, Idx> {
        self.list.cursor_front(&mut self.storage)
    }

    /// Returns a cursor positioned at the back of the list.
    #[inline]
    pub fn cursor_back(&mut self) -> Cursor<'_, T, BoxedListStorage<T, Idx>, Idx> {
        self.list.cursor_back(&mut self.storage)
    }
}

impl<T, Idx: Index> Default for OwnedList<T, Idx> {
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
        assert!(list.front_idx().is_none());
        assert!(list.back_idx().is_none());
    }

    #[test]
    fn push_back_pop_front() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        list.push_back(3).unwrap();

        assert_eq!(list.len(), 3);

        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), Some(2));
        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), None);
    }

    #[test]
    fn push_front_pop_back() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.push_front(1).unwrap();
        list.push_front(2).unwrap();
        list.push_front(3).unwrap();

        assert_eq!(list.pop_back(), Some(1));
        assert_eq!(list.pop_back(), Some(2));
        assert_eq!(list.pop_back(), Some(3));
    }

    #[test]
    fn remove_by_index() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.push_back(1).unwrap();
        let b = list.push_back(2).unwrap();
        let c = list.push_back(3).unwrap();

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

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        list.push_back(3).unwrap();

        assert_eq!(list.front(), Some(&1));
        assert_eq!(list.back(), Some(&3));
    }

    #[test]
    fn front_mut_and_back_mut() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();

        *list.front_mut().unwrap() = 10;
        *list.back_mut().unwrap() = 20;

        assert_eq!(list.front(), Some(&10));
        assert_eq!(list.back(), Some(&20));
    }

    #[test]
    fn insert_after_and_before() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.push_back(1).unwrap();
        let _c = list.push_back(3).unwrap();

        // Insert 2 after 1
        list.insert_after(a, 2).unwrap();

        // Insert 0 before 1
        list.insert_before(a, 0).unwrap();

        // Order: 0, 1, 2, 3
        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![0, 1, 2, 3]);
    }

    #[test]
    fn clear() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        list.push_back(3).unwrap();

        list.clear();

        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn move_to_back_and_front() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        let c = list.push_back(3).unwrap();

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

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        list.push_back(3).unwrap();

        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![1, 2, 3]);
    }

    #[test]
    fn iter_rev() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        list.push_back(3).unwrap();

        let values: Vec<_> = list.iter().rev().copied().collect();
        assert_eq!(values, vec![3, 2, 1]);
    }

    #[test]
    fn iter_mut() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        list.push_back(3).unwrap();

        for val in list.iter_mut() {
            *val *= 10;
        }

        let values: Vec<_> = list.iter().copied().collect();
        assert_eq!(values, vec![10, 20, 30]);
    }

    #[test]
    fn drain() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        list.push_back(3).unwrap();

        let values: Vec<_> = list.drain().collect();
        assert_eq!(values, vec![1, 2, 3]);
        assert!(list.is_empty());
    }

    #[test]
    fn cursor_walk_and_remove() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();
        list.push_back(3).unwrap();

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

        list.push_back(1).unwrap();
        list.push_back(2).unwrap();

        let err = list.push_back(3);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().into_inner(), 3);
    }

    #[test]
    fn indices() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.push_back(1).unwrap();
        let b = list.push_back(2).unwrap();
        let c = list.push_back(3).unwrap();

        let indices: Vec<_> = list.indices().collect();
        assert_eq!(indices, vec![a, b, c]);
    }

    #[test]
    fn next_and_prev_idx() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.push_back(1).unwrap();
        let b = list.push_back(2).unwrap();
        let c = list.push_back(3).unwrap();

        assert_eq!(list.next_idx(a), Some(b));
        assert_eq!(list.next_idx(b), Some(c));
        assert_eq!(list.next_idx(c), None);

        assert_eq!(list.prev_idx(a), None);
        assert_eq!(list.prev_idx(b), Some(a));
        assert_eq!(list.prev_idx(c), Some(b));
    }

    #[test]
    fn is_head_and_is_tail() {
        let mut list: OwnedList<u64> = OwnedList::with_capacity(16);

        let a = list.push_back(1).unwrap();
        let b = list.push_back(2).unwrap();
        let c = list.push_back(3).unwrap();

        assert!(list.is_head(a));
        assert!(!list.is_head(b));
        assert!(!list.is_head(c));

        assert!(!list.is_tail(a));
        assert!(!list.is_tail(b));
        assert!(list.is_tail(c));
    }
}
