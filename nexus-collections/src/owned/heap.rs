//! OwnedHeap - a min-heap that owns its storage.

use crate::{BoxedStorage, Full, Heap, HeapEntry, Index, Storage};

/// A min-heap that owns its storage.
///
/// This is a convenience wrapper around [`Heap`] + [`BoxedStorage`] for cases
/// where you don't need to share storage across multiple data structures.
///
/// # Example
///
/// ```
/// use nexus_collections::{Index, HeapEntry, OwnedHeap};
/// use std::cmp::Ordering;
///
/// #[derive(Debug)]
/// struct Timer {
///     fire_at: u64,
///     id: u32,
///     heap_idx: u32,
/// }
///
/// impl Timer {
///     fn new(fire_at: u64, id: u32) -> Self {
///         Self { fire_at, id, heap_idx: u32::NONE }
///     }
/// }
///
/// impl HeapEntry<u32> for Timer {
///     fn heap_idx(&self) -> u32 { self.heap_idx }
///     fn set_heap_idx(&mut self, idx: u32) { self.heap_idx = idx; }
/// }
///
/// impl Ord for Timer {
///     fn cmp(&self, other: &Self) -> Ordering {
///         self.fire_at.cmp(&other.fire_at)
///     }
/// }
/// impl PartialOrd for Timer {
///     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
///         Some(self.cmp(other))
///     }
/// }
/// impl PartialEq for Timer {
///     fn eq(&self, other: &Self) -> bool {
///         self.fire_at == other.fire_at
///     }
/// }
/// impl Eq for Timer {}
///
/// let mut timers: OwnedHeap<Timer> = OwnedHeap::with_capacity(100);
///
/// let a = timers.push(Timer::new(100, 1)).unwrap();
/// let b = timers.push(Timer::new(50, 2)).unwrap();
/// let c = timers.push(Timer::new(75, 3)).unwrap();
///
/// // Pops in fire_at order (min-heap)
/// assert_eq!(timers.pop().unwrap().id, 2);  // fire_at: 50
/// assert_eq!(timers.pop().unwrap().id, 3);  // fire_at: 75
/// assert_eq!(timers.pop().unwrap().id, 1);  // fire_at: 100
/// ```
pub struct OwnedHeap<T: HeapEntry<Idx> + Ord, Idx: Index = u32> {
    storage: BoxedStorage<T, Idx>,
    heap: Heap<Idx>,
}

impl<T: HeapEntry<Idx> + Ord, Idx: Index> OwnedHeap<T, Idx> {
    /// Creates a new heap with the given capacity.
    ///
    /// Capacity is rounded up to the next power of 2.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            storage: BoxedStorage::with_capacity(capacity),
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

    /// Pushes a value onto the heap.
    ///
    /// Returns the index of the inserted element.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if storage is full.
    #[inline]
    pub fn push(&mut self, value: T) -> Result<Idx, Full<T>> {
        let idx = self.storage.try_insert(value)?;
        self.heap.push(&mut self.storage, idx);
        Ok(idx)
    }

    /// Removes and returns the minimum element.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let idx = self.heap.pop(&mut self.storage)?;
        self.storage.remove(idx)
    }

    /// Returns a reference to the minimum element without removing it.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        let idx = self.heap.peek()?;
        self.storage.get(idx)
    }

    /// Returns the index of the minimum element without removing it.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn peek_idx(&self) -> Option<Idx> {
        self.heap.peek()
    }

    /// Removes an element by index.
    ///
    /// Returns `None` if the index is invalid or not in the heap.
    #[inline]
    pub fn remove(&mut self, idx: Idx) -> Option<T> {
        if !self.heap.remove(&mut self.storage, idx) {
            return None;
        }
        self.storage.remove(idx)
    }

    /// Returns a reference to the element at the given index.
    #[inline]
    pub fn get(&self, idx: Idx) -> Option<&T> {
        self.storage.get(idx)
    }

    /// Returns a mutable reference to the element at the given index.
    ///
    /// # Warning
    ///
    /// If you modify the element's priority, you must call [`update`](Self::update),
    /// [`decrease_key`](Self::decrease_key), or [`increase_key`](Self::increase_key)
    /// to restore heap order.
    #[inline]
    pub fn get_mut(&mut self, idx: Idx) -> Option<&mut T> {
        self.storage.get_mut(idx)
    }

    /// Notifies the heap that an element's priority has decreased.
    ///
    /// Call this after decreasing an element's priority to restore heap order.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not in the heap.
    #[inline]
    pub fn decrease_key(&mut self, idx: Idx) {
        self.heap.decrease_key(&mut self.storage, idx);
    }

    /// Notifies the heap that an element's priority has increased.
    ///
    /// Call this after increasing an element's priority to restore heap order.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not in the heap.
    #[inline]
    pub fn increase_key(&mut self, idx: Idx) {
        self.heap.increase_key(&mut self.storage, idx);
    }

    /// Restores heap order after an element's priority changed.
    ///
    /// Use when you don't know if priority increased or decreased.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not in the heap.
    #[inline]
    pub fn update(&mut self, idx: Idx) {
        self.heap.update(&mut self.storage, idx);
    }

    /// Clears the heap, removing all elements.
    ///
    /// This drops all values and resets the heap to empty state.
    pub fn clear(&mut self) {
        self.heap.clear(&mut self.storage);
        self.storage.clear();
    }
}

impl<T: HeapEntry<Idx> + Ord, Idx: Index> Default for OwnedHeap<T, Idx> {
    fn default() -> Self {
        Self::with_capacity(16)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    #[derive(Debug)]
    struct Task {
        priority: u32,
        id: u32,
        heap_idx: u32,
    }

    impl Task {
        fn new(priority: u32, id: u32) -> Self {
            Self {
                priority,
                id,
                heap_idx: u32::NONE,
            }
        }
    }

    impl HeapEntry<u32> for Task {
        fn heap_idx(&self) -> u32 {
            self.heap_idx
        }
        fn set_heap_idx(&mut self, idx: u32) {
            self.heap_idx = idx;
        }
    }

    impl Ord for Task {
        fn cmp(&self, other: &Self) -> Ordering {
            self.priority.cmp(&other.priority)
        }
    }

    impl PartialOrd for Task {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    impl PartialEq for Task {
        fn eq(&self, other: &Self) -> bool {
            self.priority == other.priority
        }
    }

    impl Eq for Task {}

    #[test]
    fn new_is_empty() {
        let heap: OwnedHeap<Task> = OwnedHeap::with_capacity(16);
        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
        assert!(heap.peek().is_none());
    }

    #[test]
    fn push_pop_single() {
        let mut heap: OwnedHeap<Task> = OwnedHeap::with_capacity(16);

        let _idx = heap.push(Task::new(5, 1)).unwrap();
        assert_eq!(heap.len(), 1);
        assert!(heap.peek().is_some());
        assert_eq!(heap.peek().unwrap().priority, 5);

        let task = heap.pop().unwrap();
        assert_eq!(task.id, 1);
        assert!(heap.is_empty());
    }

    #[test]
    fn min_heap_order() {
        let mut heap: OwnedHeap<Task> = OwnedHeap::with_capacity(16);

        heap.push(Task::new(10, 1)).unwrap();
        heap.push(Task::new(1, 2)).unwrap();
        heap.push(Task::new(5, 3)).unwrap();
        heap.push(Task::new(3, 4)).unwrap();

        assert_eq!(heap.pop().unwrap().priority, 1);
        assert_eq!(heap.pop().unwrap().priority, 3);
        assert_eq!(heap.pop().unwrap().priority, 5);
        assert_eq!(heap.pop().unwrap().priority, 10);
    }

    #[test]
    fn remove_by_index() {
        let mut heap: OwnedHeap<Task> = OwnedHeap::with_capacity(16);

        let _a = heap.push(Task::new(10, 1)).unwrap();
        let _b = heap.push(Task::new(1, 2)).unwrap();
        let c = heap.push(Task::new(5, 3)).unwrap();

        let removed = heap.remove(c).unwrap();
        assert_eq!(removed.id, 3);
        assert_eq!(heap.len(), 2);

        assert_eq!(heap.pop().unwrap().priority, 1);
        assert_eq!(heap.pop().unwrap().priority, 10);
    }

    #[test]
    fn decrease_key() {
        let mut heap: OwnedHeap<Task> = OwnedHeap::with_capacity(16);

        let a = heap.push(Task::new(10, 1)).unwrap();
        let _b = heap.push(Task::new(5, 2)).unwrap();

        // Decrease a's priority
        heap.get_mut(a).unwrap().priority = 1;
        heap.decrease_key(a);

        // Now a should be at the top
        assert_eq!(heap.peek().unwrap().id, 1);
    }

    #[test]
    fn increase_key() {
        let mut heap: OwnedHeap<Task> = OwnedHeap::with_capacity(16);

        let a = heap.push(Task::new(1, 1)).unwrap();
        let _b = heap.push(Task::new(5, 2)).unwrap();

        // Increase a's priority
        heap.get_mut(a).unwrap().priority = 100;
        heap.increase_key(a);

        // Now b should be at the top
        assert_eq!(heap.peek().unwrap().id, 2);
    }

    #[test]
    fn get_and_get_mut() {
        let mut heap: OwnedHeap<Task> = OwnedHeap::with_capacity(16);

        let a = heap.push(Task::new(10, 1)).unwrap();

        assert_eq!(heap.get(a).unwrap().id, 1);

        heap.get_mut(a).unwrap().id = 42;
        assert_eq!(heap.get(a).unwrap().id, 42);
    }

    #[test]
    fn full_returns_error() {
        let mut heap: OwnedHeap<Task> = OwnedHeap::with_capacity(2);

        heap.push(Task::new(1, 1)).unwrap();
        heap.push(Task::new(2, 2)).unwrap();

        let err = heap.push(Task::new(3, 3));
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().into_inner().id, 3);
    }

    #[test]
    fn peek_idx() {
        let mut heap: OwnedHeap<Task> = OwnedHeap::with_capacity(16);

        assert!(heap.peek_idx().is_none());

        let _a = heap.push(Task::new(10, 1)).unwrap();
        let b = heap.push(Task::new(1, 2)).unwrap();

        assert_eq!(heap.peek_idx(), Some(b));
    }
}
