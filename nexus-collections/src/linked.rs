//! Linked trait for intrusive doubly-linked list nodes.
//!
//! Nodes embed their own prev/next links, allowing O(1) insertion and removal
//! without the list owning the data. Objects can participate in multiple lists
//! by embedding multiple link pairs.

use crate::{Index, Storage};

/// Trait for types that can participate in a doubly-linked list.
///
/// Implementors embed prev/next indices directly in their struct.
/// This enables O(1) removal given only a node's index (no search required).
///
/// # Example
///
/// ```
/// use nexus_collections::{Index, Linked};
///
/// struct Order {
///     id: u64,
///     price: u64,
///     qty: u64,
///     // Links for price-level queue
///     next: u32,
///     prev: u32,
/// }
///
/// impl Linked<u32> for Order {
///     fn next(&self) -> u32 { self.next }
///     fn prev(&self) -> u32 { self.prev }
///     fn set_next(&mut self, idx: u32) { self.next = idx; }
///     fn set_prev(&mut self, idx: u32) { self.prev = idx; }
/// }
/// ```
pub trait Linked<Idx: Index> {
    /// Returns the next node's index, or `Idx::NONE` if this is the tail.
    fn next(&self) -> Idx;

    /// Returns the previous node's index, or `Idx::NONE` if this is the head.
    fn prev(&self) -> Idx;

    /// Sets the next node's index.
    fn set_next(&mut self, idx: Idx);

    /// Sets the previous node's index.
    fn set_prev(&mut self, idx: Idx);
}

/// A doubly-linked list over external storage.
///
/// The list itself only stores head, tail, and length. Nodes live in
/// user-provided storage and embed their own links via the [`Linked`] trait.
///
/// # Example
///
/// ```
/// use nexus_collections::{BoxedStorage, Index, Linked, List, Storage};
///
/// #[derive(Debug)]
/// struct Node {
///     value: u64,
///     next: u32,
///     prev: u32,
/// }
///
/// impl Node {
///     fn new(value: u64) -> Self {
///         Self { value, next: u32::NONE, prev: u32::NONE }
///     }
/// }
///
/// impl Linked<u32> for Node {
///     fn next(&self) -> u32 { self.next }
///     fn prev(&self) -> u32 { self.prev }
///     fn set_next(&mut self, idx: u32) { self.next = idx; }
///     fn set_prev(&mut self, idx: u32) { self.prev = idx; }
/// }
///
/// let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
/// let mut list: List<u32> = List::new();
///
/// // Insert nodes into storage first
/// let a = storage.try_insert(Node::new(1)).unwrap();
/// let b = storage.try_insert(Node::new(2)).unwrap();
/// let c = storage.try_insert(Node::new(3)).unwrap();
///
/// // Then add to list
/// list.push_back(&mut storage, a);
/// list.push_back(&mut storage, b);
/// list.push_back(&mut storage, c);
///
/// assert_eq!(list.len(), 3);
///
/// // Remove from middle - O(1)
/// list.remove(&mut storage, b);
/// assert_eq!(list.len(), 2);
/// ```
#[derive(Debug, Clone)]
pub struct List<Idx: Index> {
    head: Idx,
    tail: Idx,
    len: usize,
}

impl<Idx: Index> Default for List<Idx> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Idx: Index> List<Idx> {
    /// Creates an empty list.
    #[inline]
    pub const fn new() -> Self {
        Self {
            head: Idx::NONE,
            tail: Idx::NONE,
            len: 0,
        }
    }

    /// Returns the head node's index, or `Idx::NONE` if empty.
    #[inline]
    pub const fn head(&self) -> Idx {
        self.head
    }

    /// Returns the tail node's index, or `Idx::NONE` if empty.
    #[inline]
    pub const fn tail(&self) -> Idx {
        self.tail
    }

    /// Returns the number of nodes in the list.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the list is empty.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Pushes a node to the back of the list.
    ///
    /// The node must already exist in storage. Its links will be updated.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage.
    #[inline]
    pub fn push_back<T, S>(&mut self, storage: &mut S, idx: Idx)
    where
        T: Linked<Idx>,
        S: Storage<T, Index = Idx>,
    {
        {
            let node = storage.get_mut(idx).expect("invalid index");
            node.set_prev(self.tail);
            node.set_next(Idx::NONE);
        }

        if self.tail.is_some() {
            storage.get_mut(self.tail).unwrap().set_next(idx);
        } else {
            self.head = idx;
        }

        self.tail = idx;
        self.len += 1;
    }

    /// Pushes a node to the front of the list.
    ///
    /// The node must already exist in storage. Its links will be updated.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage.
    #[inline]
    pub fn push_front<T, S>(&mut self, storage: &mut S, idx: Idx)
    where
        T: Linked<Idx>,
        S: Storage<T, Index = Idx>,
    {
        {
            let node = storage.get_mut(idx).expect("invalid index");
            node.set_next(self.head);
            node.set_prev(Idx::NONE);
        }

        if self.head.is_some() {
            storage.get_mut(self.head).unwrap().set_prev(idx);
        } else {
            self.tail = idx;
        }

        self.head = idx;
        self.len += 1;
    }

    /// Removes and returns the head node's index.
    ///
    /// Returns `Idx::NONE` if the list is empty.
    /// The node remains in storage; only its links are cleared.
    #[inline]
    pub fn pop_front<T, S>(&mut self, storage: &mut S) -> Idx
    where
        T: Linked<Idx>,
        S: Storage<T, Index = Idx>,
    {
        if self.head.is_none() {
            return Idx::NONE;
        }

        let idx = self.head;
        self.remove(storage, idx);
        idx
    }

    /// Removes and returns the tail node's index.
    ///
    /// Returns `Idx::NONE` if the list is empty.
    /// The node remains in storage; only its links are cleared.
    #[inline]
    pub fn pop_back<T, S>(&mut self, storage: &mut S) -> Idx
    where
        T: Linked<Idx>,
        S: Storage<T, Index = Idx>,
    {
        if self.tail.is_none() {
            return Idx::NONE;
        }

        let idx = self.tail;
        self.remove(storage, idx);
        idx
    }

    /// Removes a node from the list.
    ///
    /// This is O(1) because the node contains its own prev/next links.
    /// The node remains in storage; only its links are cleared.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage.
    #[inline]
    pub fn remove<T, S>(&mut self, storage: &mut S, idx: Idx)
    where
        T: Linked<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let (prev, next) = {
            let node = storage.get(idx).expect("invalid index");
            (node.prev(), node.next())
        };

        if prev.is_some() {
            storage.get_mut(prev).unwrap().set_next(next);
        } else {
            self.head = next;
        }

        if next.is_some() {
            storage.get_mut(next).unwrap().set_prev(prev);
        } else {
            self.tail = prev;
        }

        // Clear the removed node's links
        let node = storage.get_mut(idx).unwrap();
        node.set_prev(Idx::NONE);
        node.set_next(Idx::NONE);

        self.len -= 1;
    }

    /// Inserts a node after an existing node.
    ///
    /// # Panics
    ///
    /// Panics if `after` or `idx` is not valid in storage.
    #[inline]
    pub fn insert_after<T, S>(&mut self, storage: &mut S, after: Idx, idx: Idx)
    where
        T: Linked<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let next = storage.get(after).expect("invalid index").next();

        {
            let node = storage.get_mut(idx).expect("invalid index");
            node.set_prev(after);
            node.set_next(next);
        }

        storage.get_mut(after).unwrap().set_next(idx);

        if next.is_some() {
            storage.get_mut(next).unwrap().set_prev(idx);
        } else {
            self.tail = idx;
        }

        self.len += 1;
    }

    /// Inserts a node before an existing node.
    ///
    /// # Panics
    ///
    /// Panics if `before` or `idx` is not valid in storage.
    #[inline]
    pub fn insert_before<T, S>(&mut self, storage: &mut S, before: Idx, idx: Idx)
    where
        T: Linked<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let prev = storage.get(before).expect("invalid index").prev();

        {
            let node = storage.get_mut(idx).expect("invalid index");
            node.set_next(before);
            node.set_prev(prev);
        }

        storage.get_mut(before).unwrap().set_prev(idx);

        if prev.is_some() {
            storage.get_mut(prev).unwrap().set_next(idx);
        } else {
            self.head = idx;
        }

        self.len += 1;
    }

    /// Clears the list, resetting all nodes' links.
    ///
    /// Nodes remain in storage; only their links are cleared.
    pub fn clear<T, S>(&mut self, storage: &mut S)
    where
        T: Linked<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let mut idx = self.head;
        while idx.is_some() {
            let next = storage.get(idx).unwrap().next();
            let node = storage.get_mut(idx).unwrap();
            node.set_prev(Idx::NONE);
            node.set_next(Idx::NONE);
            idx = next;
        }

        self.head = Idx::NONE;
        self.tail = Idx::NONE;
        self.len = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BoxedStorage;

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
    fn new_list_is_empty() {
        let list: List<u32> = List::new();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert!(list.head().is_none());
        assert!(list.tail().is_none());
    }

    #[test]
    fn push_back_single() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        list.push_back(&mut storage, a);

        assert_eq!(list.len(), 1);
        assert_eq!(list.head(), a);
        assert_eq!(list.tail(), a);
    }

    #[test]
    fn push_back_multiple() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);
        list.push_back(&mut storage, c);

        assert_eq!(list.len(), 3);
        assert_eq!(list.head(), a);
        assert_eq!(list.tail(), c);

        // Check forward links
        assert_eq!(storage.get(a).unwrap().next, b);
        assert_eq!(storage.get(b).unwrap().next, c);
        assert!(storage.get(c).unwrap().next.is_none());

        // Check backward links
        assert!(storage.get(a).unwrap().prev.is_none());
        assert_eq!(storage.get(b).unwrap().prev, a);
        assert_eq!(storage.get(c).unwrap().prev, b);
    }

    #[test]
    fn push_front_multiple() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_front(&mut storage, a);
        list.push_front(&mut storage, b);
        list.push_front(&mut storage, c);

        assert_eq!(list.len(), 3);
        assert_eq!(list.head(), c);
        assert_eq!(list.tail(), a);

        // Order should be c -> b -> a
        assert_eq!(storage.get(c).unwrap().next, b);
        assert_eq!(storage.get(b).unwrap().next, a);
        assert!(storage.get(a).unwrap().next.is_none());
    }

    #[test]
    fn pop_front() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);
        list.push_back(&mut storage, c);

        assert_eq!(list.pop_front(&mut storage), a);
        assert_eq!(list.len(), 2);
        assert_eq!(list.head(), b);

        assert_eq!(list.pop_front(&mut storage), b);
        assert_eq!(list.len(), 1);
        assert_eq!(list.head(), c);
        assert_eq!(list.tail(), c);

        assert_eq!(list.pop_front(&mut storage), c);
        assert!(list.is_empty());
        assert!(list.head().is_none());
        assert!(list.tail().is_none());

        // Pop from empty
        assert!(list.pop_front(&mut storage).is_none());
    }

    #[test]
    fn pop_back() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);

        assert_eq!(list.pop_back(&mut storage), b);
        assert_eq!(list.len(), 1);
        assert_eq!(list.tail(), a);

        assert_eq!(list.pop_back(&mut storage), a);
        assert!(list.is_empty());
    }

    #[test]
    fn remove_middle() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);
        list.push_back(&mut storage, c);

        list.remove(&mut storage, b);

        assert_eq!(list.len(), 2);
        assert_eq!(list.head(), a);
        assert_eq!(list.tail(), c);

        // a -> c
        assert_eq!(storage.get(a).unwrap().next, c);
        assert_eq!(storage.get(c).unwrap().prev, a);

        // b's links cleared
        assert!(storage.get(b).unwrap().next.is_none());
        assert!(storage.get(b).unwrap().prev.is_none());
    }

    #[test]
    fn remove_head() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);

        list.remove(&mut storage, a);

        assert_eq!(list.len(), 1);
        assert_eq!(list.head(), b);
        assert_eq!(list.tail(), b);
    }

    #[test]
    fn remove_tail() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);

        list.remove(&mut storage, b);

        assert_eq!(list.len(), 1);
        assert_eq!(list.head(), a);
        assert_eq!(list.tail(), a);
    }

    #[test]
    fn insert_after() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, c);
        list.insert_after(&mut storage, a, b);

        // Order: a -> b -> c
        assert_eq!(list.len(), 3);
        assert_eq!(storage.get(a).unwrap().next, b);
        assert_eq!(storage.get(b).unwrap().next, c);
        assert_eq!(storage.get(b).unwrap().prev, a);
        assert_eq!(storage.get(c).unwrap().prev, b);
    }

    #[test]
    fn insert_after_tail() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();

        list.push_back(&mut storage, a);
        list.insert_after(&mut storage, a, b);

        assert_eq!(list.tail(), b);
        assert_eq!(storage.get(a).unwrap().next, b);
        assert!(storage.get(b).unwrap().next.is_none());
    }

    #[test]
    fn insert_before() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, c);
        list.insert_before(&mut storage, c, b);

        // Order: a -> b -> c
        assert_eq!(list.len(), 3);
        assert_eq!(storage.get(a).unwrap().next, b);
        assert_eq!(storage.get(b).unwrap().prev, a);
        assert_eq!(storage.get(b).unwrap().next, c);
    }

    #[test]
    fn insert_before_head() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();

        list.push_back(&mut storage, a);
        list.insert_before(&mut storage, a, b);

        assert_eq!(list.head(), b);
        assert_eq!(storage.get(b).unwrap().next, a);
        assert!(storage.get(b).unwrap().prev.is_none());
    }

    #[test]
    fn clear() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);
        list.push_back(&mut storage, c);

        list.clear(&mut storage);

        assert!(list.is_empty());
        assert!(list.head().is_none());
        assert!(list.tail().is_none());

        // All links cleared
        assert!(storage.get(a).unwrap().next.is_none());
        assert!(storage.get(a).unwrap().prev.is_none());
        assert!(storage.get(b).unwrap().next.is_none());
        assert!(storage.get(b).unwrap().prev.is_none());
    }

    #[test]
    fn iterate_forward() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);
        list.push_back(&mut storage, c);

        let mut values = Vec::new();
        let mut idx = list.head();
        while idx.is_some() {
            values.push(storage.get(idx).unwrap().value);
            idx = storage.get(idx).unwrap().next;
        }

        assert_eq!(values, vec![1, 2, 3]);
    }

    #[test]
    fn iterate_backward() {
        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
        let mut list: List<u32> = List::new();

        let a = storage.try_insert(Node::new(1)).unwrap();
        let b = storage.try_insert(Node::new(2)).unwrap();
        let c = storage.try_insert(Node::new(3)).unwrap();

        list.push_back(&mut storage, a);
        list.push_back(&mut storage, b);
        list.push_back(&mut storage, c);

        let mut values = Vec::new();
        let mut idx = list.tail();
        while idx.is_some() {
            values.push(storage.get(idx).unwrap().value);
            idx = storage.get(idx).unwrap().prev;
        }

        assert_eq!(values, vec![3, 2, 1]);
    }

    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    #[test]
    #[ignore]
    fn bench_list_tsc() {
        const CAPACITY: usize = 4096;
        const ITERATIONS: usize = 100_000;

        #[inline]
        fn rdtsc() -> u64 {
            unsafe {
                core::arch::x86_64::_mm_lfence();
                core::arch::x86_64::_rdtsc()
            }
        }

        let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(CAPACITY);
        let mut list: List<u32> = List::new();

        // Pre-allocate nodes
        let mut indices: Vec<u32> = Vec::with_capacity(CAPACITY);
        for i in 0..CAPACITY {
            indices.push(storage.try_insert(Node::new(i as u64)).unwrap());
        }

        // Warmup
        for &idx in &indices {
            list.push_back(&mut storage, idx);
        }
        list.clear(&mut storage);

        // Collect timings
        let mut push_back_cycles = Vec::with_capacity(ITERATIONS);
        let mut remove_cycles = Vec::with_capacity(ITERATIONS);
        let mut push_front_cycles = Vec::with_capacity(ITERATIONS);
        let mut pop_front_cycles = Vec::with_capacity(ITERATIONS);

        for i in 0..ITERATIONS {
            let idx = indices[i % CAPACITY];

            // push_back
            let start = rdtsc();
            list.push_back(&mut storage, idx);
            let end = rdtsc();
            push_back_cycles.push(end - start);

            // remove
            let start = rdtsc();
            list.remove(&mut storage, idx);
            let end = rdtsc();
            remove_cycles.push(end - start);

            // push_front
            let start = rdtsc();
            list.push_front(&mut storage, idx);
            let end = rdtsc();
            push_front_cycles.push(end - start);

            // pop_front
            let start = rdtsc();
            let _ = std::hint::black_box(list.pop_front(&mut storage));
            let end = rdtsc();
            pop_front_cycles.push(end - start);
        }

        // Sort for percentiles
        push_back_cycles.sort_unstable();
        remove_cycles.sort_unstable();
        push_front_cycles.sort_unstable();
        pop_front_cycles.sort_unstable();

        fn percentile(sorted: &[u64], p: f64) -> u64 {
            let idx = ((p / 100.0) * sorted.len() as f64) as usize;
            sorted[idx.min(sorted.len() - 1)]
        }

        fn print_stats(name: &str, sorted: &[u64]) {
            println!(
                "{:12} | p50: {:5} cycles | p90: {:5} cycles | p99: {:5} cycles | p999: {:6} cycles",
                name,
                percentile(sorted, 50.0),
                percentile(sorted, 90.0),
                percentile(sorted, 99.0),
                percentile(sorted, 99.9),
            );
        }

        println!(
            "\nList<u32> ({} iterations, capacity {})",
            ITERATIONS, CAPACITY
        );
        println!("----------------------------------------------------------------------------");
        print_stats("push_back", &push_back_cycles);
        print_stats("remove", &remove_cycles);
        print_stats("push_front", &push_front_cycles);
        print_stats("pop_front", &pop_front_cycles);
        println!();
    }
}
