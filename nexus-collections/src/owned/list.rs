//! OwnedList - a doubly-linked list that owns its storage.

use crate::{BoxedStorage, Full, Index, Iter, IterMut, List, Storage, list::Indices};

/// A doubly-linked list that owns its storage.
///
/// This is a convenience wrapper around [`List`] + [`BoxedStorage`] for cases
/// where you don't need to share storage across multiple data structures.
///
/// # Example
///
/// ```
/// use nexus_collections::{Index, Linked, OwnedList};
///
/// #[derive(Debug)]
/// struct Task {
///     id: u64,
///     priority: u8,
///     next: u32,
///     prev: u32,
/// }
///
/// impl Task {
///     fn new(id: u64, priority: u8) -> Self {
///         Self { id, priority, next: u32::NONE, prev: u32::NONE }
///     }
/// }
///
/// impl Linked<u32> for Task {
///     fn next(&self) -> u32 { self.next }
///     fn prev(&self) -> u32 { self.prev }
///     fn set_next(&mut self, idx: u32) { self.next = idx; }
///     fn set_prev(&mut self, idx: u32) { self.prev = idx; }
/// }
///
/// let mut tasks: OwnedList<Task> = OwnedList::with_capacity(100);
///
/// let a = tasks.push_back(Task::new(1, 10)).unwrap();
/// let b = tasks.push_back(Task::new(2, 5)).unwrap();
/// let c = tasks.push_back(Task::new(3, 8)).unwrap();
///
/// assert_eq!(tasks.len(), 3);
///
/// // Remove from middle
/// let task = tasks.remove(b).unwrap();
/// assert_eq!(task.id, 2);
/// assert_eq!(tasks.len(), 2);
/// ```
pub struct OwnedList<T: Linked<Idx>, Idx: Index = u32> {
    storage: BoxedStorage<T, Idx>,
    list: List<Idx>,
}

impl<T: Linked<Idx>, Idx: Index> OwnedList<T, Idx> {
    /// Creates a new list with the given capacity.
    ///
    /// Capacity is rounded up to the next power of 2.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            storage: BoxedStorage::with_capacity(capacity),
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

    /// Returns the head node's index, or `Idx::NONE` if empty.
    #[inline]
    pub fn head(&self) -> Idx {
        self.list.head()
    }

    /// Returns the tail node's index, or `Idx::NONE` if empty.
    #[inline]
    pub fn tail(&self) -> Idx {
        self.list.tail()
    }

    /// Pushes a value to the back of the list.
    ///
    /// Returns the index of the inserted node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn push_back(&mut self, value: T) -> Result<Idx, Full<T>> {
        let idx = self.storage.try_insert(value)?;
        self.list.push_back(&mut self.storage, idx);
        Ok(idx)
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
        let idx = self.storage.try_insert(value)?;
        self.list.push_front(&mut self.storage, idx);
        Ok(idx)
    }

    /// Removes and returns the front element.
    ///
    /// Returns `None` if the list is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        let idx = self.list.pop_front(&mut self.storage);
        if idx.is_none() {
            return None;
        }
        self.storage.remove(idx)
    }

    /// Removes and returns the back element.
    ///
    /// Returns `None` if the list is empty.
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        let idx = self.list.pop_back(&mut self.storage);
        if idx.is_none() {
            return None;
        }
        self.storage.remove(idx)
    }

    /// Removes and returns the element at the given index.
    ///
    /// Returns `None` if the index is invalid.
    #[inline]
    pub fn remove(&mut self, idx: Idx) -> Option<T> {
        if self.storage.get(idx).is_none() {
            return None;
        }
        self.list.remove(&mut self.storage, idx);
        self.storage.remove(idx)
    }

    /// Returns a reference to the element at the given index.
    #[inline]
    pub fn get(&self, idx: Idx) -> Option<&T> {
        self.storage.get(idx)
    }

    /// Returns a mutable reference to the element at the given index.
    #[inline]
    pub fn get_mut(&mut self, idx: Idx) -> Option<&mut T> {
        self.storage.get_mut(idx)
    }

    /// Returns a reference to the front element.
    #[inline]
    pub fn front(&self) -> Option<&T> {
        let idx = self.list.head();
        if idx.is_none() {
            return None;
        }
        self.storage.get(idx)
    }

    /// Returns a mutable reference to the front element.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        let idx = self.list.head();
        if idx.is_none() {
            return None;
        }
        self.storage.get_mut(idx)
    }

    /// Returns a reference to the back element.
    #[inline]
    pub fn back(&self) -> Option<&T> {
        let idx = self.list.tail();
        if idx.is_none() {
            return None;
        }
        self.storage.get(idx)
    }

    /// Returns a mutable reference to the back element.
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let idx = self.list.tail();
        if idx.is_none() {
            return None;
        }
        self.storage.get_mut(idx)
    }

    /// Inserts a value after an existing node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `after` is not a valid index.
    #[inline]
    pub fn insert_after(&mut self, after: Idx, value: T) -> Result<Idx, Full<T>> {
        let idx = self.storage.try_insert(value)?;
        self.list.insert_after(&mut self.storage, after, idx);
        Ok(idx)
    }

    /// Inserts a value before an existing node.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `before` is not a valid index.
    #[inline]
    pub fn insert_before(&mut self, before: Idx, value: T) -> Result<Idx, Full<T>> {
        let idx = self.storage.try_insert(value)?;
        self.list.insert_before(&mut self.storage, before, idx);
        Ok(idx)
    }

    /// Clears the list, removing all elements.
    ///
    /// This drops all values and resets the list to empty state.
    pub fn clear(&mut self) {
        self.list.clear(&mut self.storage);
        self.storage.clear();
    }

    /// Returns an iterator over references to elements, front to back.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T, Idx, BoxedStorage<T, Idx>> {
        self.list.iter(&self.storage)
    }

    /// Returns an iterator over mutable references to elements, front to back.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T, Idx, BoxedStorage<T, Idx>> {
        self.list.iter_mut(&mut self.storage)
    }

    /// Returns an iterator over indices, front to back.
    #[inline]
    pub fn indices(&self) -> Indices<'_, T, Idx, BoxedStorage<T, Idx>> {
        self.list.indices(&self.storage)
    }
}

impl<T: Linked<Idx>, Idx: Index> Default for OwnedList<T, Idx> {
    fn default() -> Self {
        Self::with_capacity(16)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct Node {
        value: u64,
        next: u32,
        prev: u32,
    }

    impl Node {
        fn new(value: u64) -> Self {
            Self {
                value,
                next: u32::NONE,
                prev: u32::NONE,
            }
        }
    }

    impl Linked<u32> for Node {
        fn next(&self) -> u32 {
            self.next
        }
        fn prev(&self) -> u32 {
            self.prev
        }
        fn set_next(&mut self, idx: u32) {
            self.next = idx;
        }
        fn set_prev(&mut self, idx: u32) {
            self.prev = idx;
        }
    }

    #[test]
    fn new_is_empty() {
        let list: OwnedList<Node> = OwnedList::with_capacity(16);
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn push_back_pop_front() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        list.push_back(Node::new(1)).unwrap();
        list.push_back(Node::new(2)).unwrap();
        list.push_back(Node::new(3)).unwrap();

        assert_eq!(list.len(), 3);

        assert_eq!(list.pop_front().unwrap().value, 1);
        assert_eq!(list.pop_front().unwrap().value, 2);
        assert_eq!(list.pop_front().unwrap().value, 3);
        assert!(list.pop_front().is_none());
    }

    #[test]
    fn push_front_pop_back() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        list.push_front(Node::new(1)).unwrap();
        list.push_front(Node::new(2)).unwrap();
        list.push_front(Node::new(3)).unwrap();

        assert_eq!(list.pop_back().unwrap().value, 1);
        assert_eq!(list.pop_back().unwrap().value, 2);
        assert_eq!(list.pop_back().unwrap().value, 3);
    }

    #[test]
    fn remove_by_index() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        let a = list.push_back(Node::new(1)).unwrap();
        let b = list.push_back(Node::new(2)).unwrap();
        let c = list.push_back(Node::new(3)).unwrap();

        let removed = list.remove(b).unwrap();
        assert_eq!(removed.value, 2);
        assert_eq!(list.len(), 2);

        // a and c still accessible
        assert_eq!(list.get(a).unwrap().value, 1);
        assert_eq!(list.get(c).unwrap().value, 3);

        // b is gone
        assert!(list.get(b).is_none());
    }

    #[test]
    fn front_and_back() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        assert!(list.front().is_none());
        assert!(list.back().is_none());

        list.push_back(Node::new(1)).unwrap();
        list.push_back(Node::new(2)).unwrap();
        list.push_back(Node::new(3)).unwrap();

        assert_eq!(list.front().unwrap().value, 1);
        assert_eq!(list.back().unwrap().value, 3);
    }

    #[test]
    fn front_mut_and_back_mut() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        list.push_back(Node::new(1)).unwrap();
        list.push_back(Node::new(2)).unwrap();

        list.front_mut().unwrap().value = 10;
        list.back_mut().unwrap().value = 20;

        assert_eq!(list.front().unwrap().value, 10);
        assert_eq!(list.back().unwrap().value, 20);
    }

    #[test]
    fn insert_after_and_before() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        let a = list.push_back(Node::new(1)).unwrap();
        let _c = list.push_back(Node::new(3)).unwrap();

        // Insert 2 after 1
        list.insert_after(a, Node::new(2)).unwrap();

        // Insert 0 before 1
        list.insert_before(a, Node::new(0)).unwrap();

        // Order: 0, 1, 2, 3
        let values: Vec<_> = list.iter().map(|n| n.value).collect();
        assert_eq!(values, vec![0, 1, 2, 3]);
    }

    #[test]
    fn clear() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        list.push_back(Node::new(1)).unwrap();
        list.push_back(Node::new(2)).unwrap();
        list.push_back(Node::new(3)).unwrap();

        list.clear();

        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn iter() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        list.push_back(Node::new(1)).unwrap();
        list.push_back(Node::new(2)).unwrap();
        list.push_back(Node::new(3)).unwrap();

        let values: Vec<_> = list.iter().map(|n| n.value).collect();
        assert_eq!(values, vec![1, 2, 3]);
    }

    #[test]
    fn iter_mut() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(16);

        list.push_back(Node::new(1)).unwrap();
        list.push_back(Node::new(2)).unwrap();
        list.push_back(Node::new(3)).unwrap();

        for node in list.iter_mut() {
            node.value *= 10;
        }

        let values: Vec<_> = list.iter().map(|n| n.value).collect();
        assert_eq!(values, vec![10, 20, 30]);
    }

    #[test]
    fn full_returns_error() {
        let mut list: OwnedList<Node> = OwnedList::with_capacity(2);

        list.push_back(Node::new(1)).unwrap();
        list.push_back(Node::new(2)).unwrap();

        let err = list.push_back(Node::new(3));
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().into_inner().value, 3);
    }
}
