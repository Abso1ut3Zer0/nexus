//! Min-heap over external storage with O(1) removal by handle.
//!
//! Entries embed their own heap position, enabling O(log n) decrease-key
//! and O(log n) arbitrary removal.

use crate::{Index, Storage};

/// Trait for types that can participate in a heap.
///
/// Implementors embed their heap position and define ordering.
///
/// # Example
///
/// ```
/// use nexus_collections::{Index, HeapEntry};
/// use std::cmp::Ordering;
///
/// struct Timer {
///     fire_at: u64,
///     callback_id: u32,
///     heap_idx: u32,
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
///
/// impl PartialOrd for Timer {
///     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
///         Some(self.cmp(other))
///     }
/// }
///
/// impl PartialEq for Timer {
///     fn eq(&self, other: &Self) -> bool {
///         self.fire_at == other.fire_at
///     }
/// }
///
/// impl Eq for Timer {}
/// ```
pub trait HeapEntry<Idx: Index>: Ord {
    /// Returns this entry's position in the heap, or `Idx::NONE` if not in heap.
    fn heap_idx(&self) -> Idx;

    /// Sets this entry's position in the heap.
    fn set_heap_idx(&mut self, idx: Idx);

    /// Returns `true` if this entry is currently in a heap.
    #[inline]
    fn in_heap(&self) -> bool {
        self.heap_idx().is_some()
    }
}

/// A min-heap over external storage.
///
/// Elements are stored in external storage and referenced by index.
/// The heap maintains ordering and supports O(log n) operations including
/// arbitrary removal and decrease-key via the embedded heap position.
///
/// # Example
///
/// ```
/// use nexus_collections::{BoxedStorage, Heap, HeapEntry, Index, Storage};
/// use std::cmp::Ordering;
///
/// #[derive(Debug)]
/// struct Task {
///     priority: u32,
///     name: &'static str,
///     heap_idx: u32,
/// }
///
/// impl Task {
///     fn new(priority: u32, name: &'static str) -> Self {
///         Self { priority, name, heap_idx: u32::NONE }
///     }
/// }
///
/// impl HeapEntry<u32> for Task {
///     fn heap_idx(&self) -> u32 { self.heap_idx }
///     fn set_heap_idx(&mut self, idx: u32) { self.heap_idx = idx; }
/// }
///
/// impl Ord for Task {
///     fn cmp(&self, other: &Self) -> Ordering {
///         self.priority.cmp(&other.priority)
///     }
/// }
/// impl PartialOrd for Task {
///     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
///         Some(self.cmp(other))
///     }
/// }
/// impl PartialEq for Task {
///     fn eq(&self, other: &Self) -> bool {
///         self.priority == other.priority
///     }
/// }
/// impl Eq for Task {}
///
/// let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(16);
/// let mut heap: Heap<u32> = Heap::with_capacity(16);
///
/// let a = storage.try_insert(Task::new(10, "low")).unwrap();
/// let b = storage.try_insert(Task::new(1, "high")).unwrap();
/// let c = storage.try_insert(Task::new(5, "medium")).unwrap();
///
/// heap.push(&mut storage, a);
/// heap.push(&mut storage, b);
/// heap.push(&mut storage, c);
///
/// // Pops in priority order (min-heap)
/// let idx = heap.pop(&mut storage).unwrap();
/// assert_eq!(storage.get(idx).unwrap().name, "high");
/// let idx = heap.pop(&mut storage).unwrap();
/// assert_eq!(storage.get(idx).unwrap().name, "medium");
/// let idx = heap.pop(&mut storage).unwrap();
/// assert_eq!(storage.get(idx).unwrap().name, "low");
/// ```
#[derive(Debug, Clone)]
pub struct Heap<Idx: Index> {
    /// Heap-ordered storage indices.
    heap: Vec<Idx>,
}

impl<Idx: Index> Default for Heap<Idx> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Idx: Index> Heap<Idx> {
    /// Creates an empty heap.
    #[inline]
    pub const fn new() -> Self {
        Self { heap: Vec::new() }
    }

    /// Creates a heap with pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            heap: Vec::with_capacity(capacity),
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

    /// Returns the capacity of the heap.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.heap.capacity()
    }

    /// Returns the index of the minimum element without removing it.
    ///
    /// Returns `None` if the heap is empty.
    #[inline]
    pub fn peek(&self) -> Option<Idx> {
        self.heap.first().copied()
    }

    /// Pushes an element onto the heap.
    ///
    /// The element must already exist in storage.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not valid in storage or already in a heap.
    pub fn push<T, S>(&mut self, storage: &mut S, idx: Idx)
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        debug_assert!(
            !storage.get(idx).expect("invalid index").in_heap(),
            "element already in heap"
        );

        let pos = self.heap.len();
        self.heap.push(idx);
        storage
            .get_mut(idx)
            .unwrap()
            .set_heap_idx(Idx::from_usize(pos));

        self.sift_up(storage, pos);
    }

    /// Removes and returns the index of the minimum element.
    ///
    /// Returns `None` if the heap is empty.
    pub fn pop<T, S>(&mut self, storage: &mut S) -> Option<Idx>
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        if self.heap.is_empty() {
            return None;
        }

        let idx = self.heap[0];

        // Clear heap_idx of removed element
        storage.get_mut(idx).unwrap().set_heap_idx(Idx::NONE);

        let last = self.heap.pop().unwrap();
        if !self.heap.is_empty() {
            self.heap[0] = last;
            storage
                .get_mut(last)
                .unwrap()
                .set_heap_idx(Idx::from_usize(0));
            self.sift_down(storage, 0);
        }

        Some(idx)
    }

    /// Removes an arbitrary element from the heap.
    ///
    /// Returns `true` if the element was in the heap and removed.
    ///
    /// This is O(log n) because entries track their own heap position.
    pub fn remove<T, S>(&mut self, storage: &mut S, idx: Idx) -> bool
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let entry = match storage.get(idx) {
            Some(e) => e,
            None => return false,
        };

        let heap_idx = entry.heap_idx();
        if heap_idx.is_none() {
            return false;
        }

        let pos = heap_idx.as_usize();

        // Clear heap_idx of removed element
        storage.get_mut(idx).unwrap().set_heap_idx(Idx::NONE);

        let last_pos = self.heap.len() - 1;
        if pos == last_pos {
            self.heap.pop();
        } else {
            let last = self.heap.pop().unwrap();
            self.heap[pos] = last;
            storage
                .get_mut(last)
                .unwrap()
                .set_heap_idx(Idx::from_usize(pos));

            // May need to sift up or down
            self.sift_down(storage, pos);
            self.sift_up(storage, pos);
        }

        true
    }

    /// Notifies the heap that an element's priority has decreased.
    ///
    /// Call this after decreasing an element's priority to restore heap order.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not in the heap.
    pub fn decrease_key<T, S>(&mut self, storage: &mut S, idx: Idx)
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let pos = storage
            .get(idx)
            .expect("invalid index")
            .heap_idx()
            .as_usize();

        self.sift_up(storage, pos);
    }

    /// Notifies the heap that an element's priority has increased.
    ///
    /// Call this after increasing an element's priority to restore heap order.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not in the heap.
    pub fn increase_key<T, S>(&mut self, storage: &mut S, idx: Idx)
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let pos = storage
            .get(idx)
            .expect("invalid index")
            .heap_idx()
            .as_usize();

        self.sift_down(storage, pos);
    }

    /// Restores heap order after an element's priority changed in either direction.
    ///
    /// Use when you don't know if priority increased or decreased.
    pub fn update<T, S>(&mut self, storage: &mut S, idx: Idx)
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let pos = storage
            .get(idx)
            .expect("invalid index")
            .heap_idx()
            .as_usize();

        self.sift_up(storage, pos);
        self.sift_down(storage, pos);
    }

    /// Clears the heap, marking all entries as not in heap.
    pub fn clear<T, S>(&mut self, storage: &mut S)
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        for &idx in &self.heap {
            if let Some(entry) = storage.get_mut(idx) {
                entry.set_heap_idx(Idx::NONE);
            }
        }
        self.heap.clear();
    }

    #[inline]
    fn sift_up<T, S>(&mut self, storage: &mut S, pos: usize)
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        if pos == 0 {
            return;
        }

        // Safety: pos is valid index into heap
        let idx = *unsafe { self.heap.get_unchecked(pos) };
        let mut hole = pos;

        while hole > 0 {
            let parent = (hole - 1) / 2;
            // Safety: parent < hole <= len
            let parent_idx = *unsafe { self.heap.get_unchecked(parent) };

            // Safety: both indices are valid in storage
            if unsafe {
                storage
                    .get_unchecked(idx)
                    .cmp(storage.get_unchecked(parent_idx))
            }
            .is_lt()
            {
                *unsafe { self.heap.get_unchecked_mut(hole) } = parent_idx;
                unsafe { storage.get_unchecked_mut(parent_idx) }
                    .set_heap_idx(Idx::from_usize(hole));
                hole = parent;
            } else {
                break;
            }
        }

        if hole != pos {
            *unsafe { self.heap.get_unchecked_mut(hole) } = idx;
            unsafe { storage.get_unchecked_mut(idx) }.set_heap_idx(Idx::from_usize(hole));
        }
    }

    #[inline]
    fn sift_down<T, S>(&mut self, storage: &mut S, pos: usize)
    where
        T: HeapEntry<Idx>,
        S: Storage<T, Index = Idx>,
    {
        let len = self.heap.len();
        if len <= 1 {
            return;
        }

        // Safety: pos is valid index into heap
        let idx = *unsafe { self.heap.get_unchecked(pos) };
        let mut hole = pos;

        // Phase 1: Descend to leaf, always following smaller child
        loop {
            let left = 2 * hole + 1;
            if left >= len {
                break;
            }

            let right = left + 1;

            // Safety: left < len
            let left_idx = *unsafe { self.heap.get_unchecked(left) };

            let smaller = if right < len {
                let right_idx = *unsafe { self.heap.get_unchecked(right) };
                // Safety: both indices valid in storage
                if unsafe {
                    storage
                        .get_unchecked(right_idx)
                        .cmp(storage.get_unchecked(left_idx))
                }
                .is_lt()
                {
                    right
                } else {
                    left
                }
            } else {
                left
            };

            // Safety: smaller < len
            let smaller_idx = *unsafe { self.heap.get_unchecked(smaller) };
            *unsafe { self.heap.get_unchecked_mut(hole) } = smaller_idx;
            unsafe { storage.get_unchecked_mut(smaller_idx) }.set_heap_idx(Idx::from_usize(hole));
            hole = smaller;
        }

        // Phase 2: Sift up from leaf position
        while hole > pos {
            let parent = (hole - 1) / 2;
            // Safety: parent < hole
            let parent_idx = *unsafe { self.heap.get_unchecked(parent) };

            // Safety: both indices valid in storage
            if unsafe {
                storage
                    .get_unchecked(idx)
                    .cmp(storage.get_unchecked(parent_idx))
            }
            .is_lt()
            {
                *unsafe { self.heap.get_unchecked_mut(hole) } = parent_idx;
                unsafe { storage.get_unchecked_mut(parent_idx) }
                    .set_heap_idx(Idx::from_usize(hole));
                hole = parent;
            } else {
                break;
            }
        }

        // Place element in final position
        *unsafe { self.heap.get_unchecked_mut(hole) } = idx;
        unsafe { storage.get_unchecked_mut(idx) }.set_heap_idx(Idx::from_usize(hole));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BoxedStorage;
    use std::cmp::Ordering;

    #[derive(Debug)]
    #[allow(unused)]
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
        let heap: Heap<u32> = Heap::new();
        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
        assert!(heap.peek().is_none());
    }

    #[test]
    fn push_pop_single() {
        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(16);
        let mut heap: Heap<u32> = Heap::with_capacity(16);

        let idx = storage.try_insert(Task::new(5, 1)).unwrap();
        heap.push(&mut storage, idx);

        assert_eq!(heap.len(), 1);
        assert_eq!(heap.peek(), Some(idx));

        let popped = heap.pop(&mut storage);
        assert_eq!(popped, Some(idx));
        assert!(heap.is_empty());

        // Entry's heap_idx cleared
        assert!(!storage.get(idx).unwrap().in_heap());
    }

    #[test]
    fn min_heap_order() {
        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(16);
        let mut heap: Heap<u32> = Heap::with_capacity(16);

        let a = storage.try_insert(Task::new(10, 1)).unwrap();
        let b = storage.try_insert(Task::new(1, 2)).unwrap();
        let c = storage.try_insert(Task::new(5, 3)).unwrap();
        let d = storage.try_insert(Task::new(3, 4)).unwrap();

        heap.push(&mut storage, a);
        heap.push(&mut storage, b);
        heap.push(&mut storage, c);
        heap.push(&mut storage, d);

        // Should pop in priority order: 1, 3, 5, 10
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 1);
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 3);
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 5);
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 10);
    }

    #[test]
    fn remove_arbitrary() {
        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(16);
        let mut heap: Heap<u32> = Heap::with_capacity(16);

        let a = storage.try_insert(Task::new(10, 1)).unwrap();
        let b = storage.try_insert(Task::new(1, 2)).unwrap();
        let c = storage.try_insert(Task::new(5, 3)).unwrap();

        heap.push(&mut storage, a);
        heap.push(&mut storage, b);
        heap.push(&mut storage, c);

        // Remove middle priority
        assert!(heap.remove(&mut storage, c));
        assert!(!storage.get(c).unwrap().in_heap());
        assert_eq!(heap.len(), 2);

        // Remaining: 1, 10
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 1);
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 10);
    }

    #[test]
    fn remove_root() {
        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(16);
        let mut heap: Heap<u32> = Heap::with_capacity(16);

        let a = storage.try_insert(Task::new(10, 1)).unwrap();
        let b = storage.try_insert(Task::new(1, 2)).unwrap();
        let c = storage.try_insert(Task::new(5, 3)).unwrap();

        heap.push(&mut storage, a);
        heap.push(&mut storage, b);
        heap.push(&mut storage, c);

        // Remove root (min)
        assert!(heap.remove(&mut storage, b));
        assert_eq!(heap.len(), 2);

        // Remaining: 5, 10
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 5);
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 10);
    }

    #[test]
    fn decrease_key() {
        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(16);
        let mut heap: Heap<u32> = Heap::with_capacity(16);

        let a = storage.try_insert(Task::new(10, 1)).unwrap();
        let b = storage.try_insert(Task::new(5, 2)).unwrap();
        let c = storage.try_insert(Task::new(3, 3)).unwrap();

        heap.push(&mut storage, a);
        heap.push(&mut storage, b);
        heap.push(&mut storage, c);

        // Decrease a's priority from 10 to 1
        storage.get_mut(a).unwrap().priority = 1;
        heap.decrease_key(&mut storage, a);

        // Now a should be at root
        assert_eq!(heap.peek(), Some(a));
        let idx = heap.pop(&mut storage).unwrap();
        assert_eq!(storage.get(idx).unwrap().priority, 1);
    }

    #[test]
    fn increase_key() {
        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(16);
        let mut heap: Heap<u32> = Heap::with_capacity(16);

        let a = storage.try_insert(Task::new(1, 1)).unwrap();
        let b = storage.try_insert(Task::new(5, 2)).unwrap();
        let c = storage.try_insert(Task::new(10, 3)).unwrap();

        heap.push(&mut storage, a);
        heap.push(&mut storage, b);
        heap.push(&mut storage, c);

        // Increase a's priority from 1 to 100
        storage.get_mut(a).unwrap().priority = 100;
        heap.increase_key(&mut storage, a);

        // Now b should be at root (priority 5)
        assert_eq!(heap.peek(), Some(b));
    }

    #[test]
    fn clear() {
        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(16);
        let mut heap: Heap<u32> = Heap::with_capacity(16);

        let a = storage.try_insert(Task::new(10, 1)).unwrap();
        let b = storage.try_insert(Task::new(1, 2)).unwrap();

        heap.push(&mut storage, a);
        heap.push(&mut storage, b);

        heap.clear(&mut storage);

        assert!(heap.is_empty());
        assert!(!storage.get(a).unwrap().in_heap());
        assert!(!storage.get(b).unwrap().in_heap());
    }

    #[test]
    fn stress_push_pop() {
        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(1024);
        let mut heap: Heap<u32> = Heap::with_capacity(1024);

        // Push 1000 items with random-ish priorities
        let mut indices = Vec::with_capacity(1000);
        for i in 0..1000u32 {
            let priority = (i * 7 + 13) % 1000; // Deterministic scramble
            let idx = storage.try_insert(Task::new(priority, i)).unwrap();
            indices.push(idx);
            heap.push(&mut storage, idx);
        }

        // Pop all and verify sorted order
        let mut last = 0;
        while let Some(idx) = heap.pop(&mut storage) {
            let priority = storage.get(idx).unwrap().priority;
            assert!(priority >= last, "heap order violated");
            last = priority;
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    #[test]
    #[ignore]
    fn bench_heap_tsc() {
        const CAPACITY: usize = 4096;
        const HEAP_SIZE: usize = 1024; // Maintain this many elements
        const ITERATIONS: usize = 100_000;

        #[inline]
        fn rdtsc() -> u64 {
            unsafe {
                core::arch::x86_64::_mm_lfence();
                core::arch::x86_64::_rdtsc()
            }
        }

        let mut storage: BoxedStorage<Task> = BoxedStorage::with_capacity(CAPACITY);
        let mut heap: Heap<u32> = Heap::with_capacity(CAPACITY);

        // Pre-allocate all tasks
        let mut indices: Vec<u32> = Vec::with_capacity(CAPACITY);
        for i in 0..CAPACITY {
            indices.push(storage.try_insert(Task::new(i as u32, i as u32)).unwrap());
        }

        // Fill heap to HEAP_SIZE with shuffled priorities
        for i in 0..HEAP_SIZE {
            let idx = indices[i];
            storage.get_mut(idx).unwrap().priority = ((i * 7 + 13) % HEAP_SIZE) as u32;
            heap.push(&mut storage, idx);
        }

        let mut push_cycles = Vec::with_capacity(ITERATIONS);
        let mut pop_cycles = Vec::with_capacity(ITERATIONS);
        let mut remove_cycles = Vec::with_capacity(ITERATIONS);

        // Cycle through remaining indices for push/remove
        let mut next_idx = HEAP_SIZE;

        for i in 0..ITERATIONS {
            // Pop one
            let start = rdtsc();
            let popped = std::hint::black_box(heap.pop(&mut storage).unwrap());
            let end = rdtsc();
            pop_cycles.push(end - start);

            // Push replacement with new priority
            let new_idx = indices[next_idx % CAPACITY];
            // If this index is still in heap (wrapped around), skip
            if storage.get(new_idx).unwrap().in_heap() {
                // Use the one we just popped
                storage.get_mut(popped).unwrap().priority = (i % HEAP_SIZE) as u32;
                let start = rdtsc();
                heap.push(&mut storage, popped);
                let end = rdtsc();
                push_cycles.push(end - start);
            } else {
                storage.get_mut(new_idx).unwrap().priority = (i % HEAP_SIZE) as u32;
                let start = rdtsc();
                heap.push(&mut storage, new_idx);
                let end = rdtsc();
                push_cycles.push(end - start);
                next_idx += 1;
            }

            // Remove from middle (pick element at ~half heap depth)
            if heap.len() > 10 {
                let victim_pos = heap.len() / 2;
                let victim = heap.heap[victim_pos];
                let start = rdtsc();
                std::hint::black_box(heap.remove(&mut storage, victim));
                let end = rdtsc();
                remove_cycles.push(end - start);

                // Re-add to maintain size
                storage.get_mut(victim).unwrap().priority = ((i + 500) % HEAP_SIZE) as u32;
                heap.push(&mut storage, victim);
            }
        }

        push_cycles.sort_unstable();
        pop_cycles.sort_unstable();
        remove_cycles.sort_unstable();

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
            "\nHeap<u32> ({} iterations, heap size {}, capacity {})",
            ITERATIONS, HEAP_SIZE, CAPACITY
        );
        println!("----------------------------------------------------------------------------");
        print_stats("push", &push_cycles);
        print_stats("pop", &pop_cycles);
        print_stats("remove", &remove_cycles);
        println!();
    }
}
