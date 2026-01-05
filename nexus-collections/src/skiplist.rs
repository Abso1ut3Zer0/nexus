//! Skip list - a probabilistic sorted ap backed by external storage.
//!
//! A skip list provides O(log n) expected time for insert, lookup, and removal,
//! with predictable latency (no rebalancing). This makes it well-suited for
//! latency-sensitive applications like order book price levels.
//!
//! # Design
//!
//! Unlike [`List`] and [`Heap`], the skip list stores keys and values internally
//! in its nodes rather than wrapping user data. The external storage owns
//! [`SkipNode`]s which contain the key, value, and forward pointers.
//!
//! ```text
//! Level 3:  HEAD ─────────────────────► 50 ──────────────────► NIL
//!             │                          │
//! Level 2:  HEAD ────────► 20 ──────────► 50 ──────────────────► NIL
//!             │            │              │
//! Level 1:  HEAD ──► 10 ──► 20 ──► 30 ──► 50 ──► 60 ──► NIL
//! ```
//!
//! # Example
//!
//! ```rust
//! use nexus_collections::{SkipList, BoxedSkipStorage};
//! use rand::SeedableRng;
//! use rand::rngs::SmallRng;
//!
//! let mut storage: BoxedSkipStorage<u64, String> = BoxedSkipStorage::with_capacity(100);
//! let rng = SmallRng::seed_from_u64(12345);
//! let mut map: SkipList<u64, String, _, _, _, 16> = SkipList::new(rng);
//!
//! map.try_insert(&mut storage, 100, "first".into()).unwrap();
//! map.try_insert(&mut storage, 50, "second".into()).unwrap();
//!
//! assert_eq!(map.get(&storage, &50), Some(&"second".into()));
//! assert_eq!(map.first(&storage), Some((&50, &"second".into())));
//! ```

use core::marker::PhantomData;

use rand_core::RngCore;

use crate::key::Key;
use crate::storage::{BoundedStorage, Full, Storage, UnboundedStorage};

// ============================================================================
// SkipNode
// ============================================================================

/// A node in the skip list containing key, value, and forward pointers.
///
/// Forward pointers at each level point to the next node at that level.
/// Nodes with higher `level` values participate in more express lanes,
/// allowing O(log n) traversal.
#[derive(Debug, Clone)]
pub struct SkipNode<K, V, Idx: Key, const MAX_LEVEL: usize> {
    /// The key used for ordering.
    pub key: K,
    /// The value associated with this key.
    pub value: V,
    /// Forward pointers at each level. `forward[i]` points to the next node at level i.
    forward: [Idx; MAX_LEVEL],
    /// The level of this node (0-indexed). Node participates in levels 0..=level.
    level: u8,
}

impl<K, V, Idx: Key, const MAX_LEVEL: usize> SkipNode<K, V, Idx, MAX_LEVEL> {
    /// Creates a new node with the given key, value, and level.
    #[inline]
    fn new(key: K, value: V, level: u8) -> Self {
        Self {
            key,
            value,
            forward: [Idx::NONE; MAX_LEVEL],
            level,
        }
    }
}

// ============================================================================
// SkipList
// ============================================================================

/// A probabilistic sorted map backed by external storage.
///
/// The skip list maintains elements in sorted order by key, providing
/// O(log n) expected time for insert, lookup, and removal operations.
///
/// # Type Parameters
///
/// - `K`: Key type, must implement `Ord`
/// - `V`: Value type
/// - `S`: Storage type implementing [`Storage`]
/// - `Idx`: Index type for storage keys, defaults to `u32`
/// - `R`: Random number generator implementing [`RngCore`]
/// - `MAX_LEVEL`: Maximum number of levels, defaults to 16 (~65K elements efficient)
#[derive(Debug)]
pub struct SkipList<K, V, S, Idx = u32, R = (), const MAX_LEVEL: usize = 16>
where
    K: Ord,
    Idx: Key,
{
    /// Head pointers for each level. `head[i]` points to the first node at level i.
    head: [Idx; MAX_LEVEL],
    /// Tail pointer (last node at level 0) for O(1) `last()` access.
    tail: Idx,
    /// Random number generator for level assignment.
    rng: R,
    /// Current maximum level in use (0-indexed).
    level: usize,
    /// Number of elements in the skip list.
    len: usize,
    /// Derived from level_ratio: log2(level_ratio). Used to scale
    /// the geometric distribution in random_level(). Higher values
    /// produce fewer tall nodes (sparser upper levels).
    level_divisor: u8,
    /// Marker for storage and key/value types.
    _marker: PhantomData<(K, V, S)>,
}

impl<K, V, S, Idx, R, const MAX_LEVEL: usize> SkipList<K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Creates a new empty skip list.
    ///
    /// Uses default level ratio of 2 (p=0.5), meaning on average
    /// half of nodes appear at each successive level.
    pub fn new(rng: R) -> Self {
        Self::with_level_ratio(rng, 2)
    }

    /// Creates a new empty skip list with custom level ratio.
    ///
    /// `level_ratio` controls memory vs search speed tradeoff:
    /// - Higher values = fewer levels = less memory, slower search
    /// - Lower values = more levels = more memory, faster search
    ///
    /// Common values:
    /// - 2: Standard (p=0.5), ~2 pointers per node average
    /// - 4: Redis-style (p=0.25), ~1.33 pointers per node average
    ///
    /// Must be a power of 2 and >= 2. Invalid values are rounded
    /// to nearest valid value.
    pub fn with_level_ratio(rng: R, level_ratio: u32) -> Self {
        let level_ratio = level_ratio.max(2).next_power_of_two();
        Self {
            head: [Idx::NONE; MAX_LEVEL],
            tail: Idx::NONE,
            rng,
            level: 0,
            len: 0,
            level_divisor: level_ratio.trailing_zeros() as u8,
            _marker: PhantomData,
        }
    }

    /// Returns the number of elements in the skip list.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the skip list is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns `true` if the skip list contains the given key.
    #[inline]
    pub fn contains_key(&self, storage: &S, key: &K) -> bool {
        self.get(storage, key).is_some()
    }

    /// Returns a reference to the value for the given key, or `None` if not found.
    #[inline]
    pub fn get<'a>(&'a self, storage: &'a S, key: &K) -> Option<&'a V> {
        let found = self.find(storage, key);
        found.map(|idx| &storage.get(idx).expect("invalid index").value)
    }

    /// Returns a mutable reference to the value for the given key, or `None` if not found.
    #[inline]
    pub fn get_mut<'a>(&'a mut self, storage: &'a mut S, key: &K) -> Option<&'a mut V> {
        let found = self.find(storage, key);
        found.map(|idx| &mut storage.get_mut(idx).expect("invalid index").value)
    }

    /// Returns the first (smallest) key-value pair, or `None` if empty.
    #[inline]
    pub fn first<'a>(&'a self, storage: &'a S) -> Option<(&'a K, &'a V)> {
        if self.head[0].is_none() {
            return None;
        }
        let node = storage.get(self.head[0]).expect("invalid head");
        Some((&node.key, &node.value))
    }

    /// Returns a mutable reference to the first (smallest) key-value pair.
    #[inline]
    pub fn first_mut<'a>(&'a mut self, storage: &'a mut S) -> Option<(&'a K, &'a mut V)> {
        if self.head[0].is_none() {
            return None;
        }
        let node = storage.get_mut(self.head[0]).expect("invalid head");
        Some((&node.key, &mut node.value))
    }

    /// Returns the last (largest) key-value pair, or `None` if empty.
    ///
    /// This is O(1) due to maintained tail pointer.
    #[inline]
    pub fn last<'a>(&'a self, storage: &'a S) -> Option<(&'a K, &'a V)> {
        if self.tail.is_none() {
            return None;
        }
        let node = storage.get(self.tail).expect("invalid tail");
        Some((&node.key, &node.value))
    }

    /// Returns a mutable reference to the last (largest) key-value pair.
    ///
    /// This is O(1) due to maintained tail pointer.
    #[inline]
    pub fn last_mut<'a>(&'a mut self, storage: &'a mut S) -> Option<(&'a K, &'a mut V)> {
        if self.tail.is_none() {
            return None;
        }
        let node = storage.get_mut(self.tail).expect("invalid tail");
        Some((&node.key, &mut node.value))
    }

    /// Removes the first (smallest) key-value pair and returns it.
    pub fn pop_first(&mut self, storage: &mut S) -> Option<(K, V)> {
        if self.head[0].is_none() {
            return None;
        }

        let first_idx = self.head[0];

        // Get raw pointer - avoids holding borrow
        let node_ptr =
            storage.get(first_idx).expect("invalid head") as *const SkipNode<K, V, Idx, MAX_LEVEL>;

        // Safety: node_ptr is valid, we're just reading
        let node_level = unsafe { (*node_ptr).level } as usize;

        // Update head pointers at all levels this node participates in
        for i in 0..=node_level {
            // Safety: node_ptr still valid, just reading forward[i]
            self.head[i] = unsafe { (*node_ptr).forward[i] };
        }

        // Update tail if this was the only node
        if self.head[0].is_none() {
            self.tail = Idx::NONE;
        }

        // Reduce level if needed
        while self.level > 0 && self.head[self.level].is_none() {
            self.level -= 1;
        }

        self.len -= 1;

        let node = storage.remove(first_idx).expect("invalid index");
        Some((node.key, node.value))
    }

    /// Removes the last (largest) key-value pair and returns it.
    ///
    /// This is O(log n) as we need to search for predecessors.
    pub fn pop_last(&mut self, storage: &mut S) -> Option<(K, V)>
    where
        K: Clone,
    {
        if self.tail.is_none() {
            return None;
        }

        // Clone the key to release the borrow on storage
        let tail_key = storage.get(self.tail).expect("invalid tail").key.clone();

        // Search for predecessors
        let mut update = [Idx::NONE; MAX_LEVEL];
        self.search(storage, &tail_key, &mut update);

        let idx = self.tail;

        // Get raw pointer - avoids holding borrow
        let node_ptr =
            storage.get(idx).expect("invalid tail") as *const SkipNode<K, V, Idx, MAX_LEVEL>;

        // Safety: node_ptr is valid, we're just reading
        let node_level = unsafe { (*node_ptr).level } as usize;

        // Update forward pointers at each level
        for i in 0..=node_level {
            // Safety: node_ptr still valid, just reading forward[i]
            let next = unsafe { (*node_ptr).forward[i] };

            if update[i].is_none() {
                self.head[i] = next;
            } else {
                // Safety: update[i] != idx (predecessor is always before target)
                let prev = unsafe { storage.get_unchecked_mut(update[i]) };
                prev.forward[i] = next;
            }
        }

        // Update tail to predecessor at level 0
        self.tail = update[0];

        // Reduce level if needed
        while self.level > 0 && self.head[self.level].is_none() {
            self.level -= 1;
        }

        self.len -= 1;

        let node = storage.remove(idx).expect("invalid index");
        Some((node.key, node.value))
    }

    /// Removes the entry for the given key and returns the value, or `None` if not found.
    pub fn remove(&mut self, storage: &mut S, key: &K) -> Option<V> {
        let mut update = [Idx::NONE; MAX_LEVEL];
        let found = self.search(storage, key, &mut update);
        let idx = found?;

        // Get raw pointer - avoids holding borrow
        let node_ptr =
            storage.get(idx).expect("invalid index") as *const SkipNode<K, V, Idx, MAX_LEVEL>;

        // Safety: node_ptr is valid, we're just reading
        let node_level = unsafe { (*node_ptr).level } as usize;
        let forward_0_is_none = unsafe { (*node_ptr).forward[0].is_none() };

        // Update forward pointers at each level
        for i in 0..=node_level {
            // Safety: node_ptr still valid, just reading forward[i]
            let next = unsafe { (*node_ptr).forward[i] };

            if update[i].is_none() {
                self.head[i] = next;
            } else {
                // Safety: update[i] != idx (predecessor is always before target)
                let prev = unsafe { storage.get_unchecked_mut(update[i]) };
                prev.forward[i] = next;
            }
        }

        // Update tail if we removed the last node
        if forward_0_is_none {
            self.tail = update[0];
        }

        // Reduce level if needed
        while self.level > 0 && self.head[self.level].is_none() {
            self.level -= 1;
        }

        self.len -= 1;

        let node = storage.remove(idx).expect("invalid index");
        Some(node.value)
    }

    /// Removes all elements from the skip list.
    pub fn clear(&mut self, storage: &mut S) {
        // Walk level 0 and remove all nodes
        let mut current = self.head[0];
        while current.is_some() {
            let next = storage.get(current).expect("invalid index").forward[0];
            storage.remove(current);
            current = next;
        }

        self.head = [Idx::NONE; MAX_LEVEL];
        self.tail = Idx::NONE;
        self.level = 0;
        self.len = 0;
    }

    /// Returns an iterator over key-value pairs in sorted order.
    #[inline]
    pub fn iter<'a>(&'a self, storage: &'a S) -> Iter<'a, K, V, S, Idx, MAX_LEVEL> {
        Iter {
            storage,
            current: self.head[0],
            _marker: PhantomData,
        }
    }

    /// Returns a mutable iterator over key-value pairs in sorted order.
    #[inline]
    pub fn iter_mut<'a>(&'a mut self, storage: &'a mut S) -> IterMut<'a, K, V, S, Idx, MAX_LEVEL> {
        IterMut {
            current: self.head[0],
            storage,
            _marker: PhantomData,
        }
    }

    /// Returns an iterator over keys in sorted order.
    #[inline]
    pub fn keys<'a>(&'a self, storage: &'a S) -> Keys<'a, K, V, S, Idx, MAX_LEVEL> {
        Keys {
            inner: self.iter(storage),
        }
    }

    /// Returns an iterator over values in sorted order by key.
    #[inline]
    pub fn values<'a>(&'a self, storage: &'a S) -> Values<'a, K, V, S, Idx, MAX_LEVEL> {
        Values {
            inner: self.iter(storage),
        }
    }

    /// Returns a cursor starting at the first element.
    #[inline]
    pub fn cursor_front<'a>(
        &'a mut self,
        storage: &'a mut S,
    ) -> Cursor<'a, K, V, S, Idx, R, MAX_LEVEL> {
        let current = self.head[0];
        Cursor {
            list: self,
            storage,
            current,
            prev_at_level: [Idx::NONE; MAX_LEVEL],
        }
    }

    /// Returns a cursor starting at the given key, or at the first element greater than key.
    #[inline]
    pub fn cursor_at<'a>(
        &'a mut self,
        storage: &'a mut S,
        key: &K,
    ) -> Cursor<'a, K, V, S, Idx, R, MAX_LEVEL> {
        let mut prev_at_level = [Idx::NONE; MAX_LEVEL];
        let found = self.find(storage, key);
        self.search(storage, key, &mut prev_at_level);
        let current = if let Some(idx) = found {
            idx
        } else {
            // Position at first element greater than key
            if prev_at_level[0].is_none() {
                self.head[0]
            } else {
                let prev = storage.get(prev_at_level[0]).expect("invalid index");
                prev.forward[0]
            }
        };

        Cursor {
            list: self,
            storage,
            current,
            prev_at_level,
        }
    }

    // ========================================================================
    // Internal helpers
    // ========================================================================

    /// Finds the index of a key without computing predecessors.
    /// Used for read-only operations (get, contains_key).
    #[inline]
    fn find(&self, storage: &S, key: &K) -> Option<Idx> {
        let mut current = Idx::NONE;

        // Start from the highest level
        for i in (0..=self.level).rev() {
            let mut next = if current.is_none() {
                self.head[i]
            } else {
                // Safety: current is valid
                unsafe { storage.get_unchecked(current) }.forward[i]
            };

            // Traverse forward while next key is less than target
            while next.is_some() {
                let next_node = unsafe { storage.get_unchecked(next) };
                if next_node.key >= *key {
                    break;
                }
                current = next;
                next = next_node.forward[i];
            }
        }

        // Check if we found the exact key
        let next = if current.is_none() {
            self.head[0]
        } else {
            unsafe { storage.get_unchecked(current) }.forward[0]
        };

        if next.is_some() && unsafe { storage.get_unchecked(next) }.key == *key {
            Some(next)
        } else {
            None
        }
    }

    /// Searches for a key, filling the update array with predecessors at each level.
    /// Used for mutations (insert, remove).
    /// Returns the index if found.
    #[inline]
    fn search(&self, storage: &S, key: &K, update: &mut [Idx; MAX_LEVEL]) -> Option<Idx> {
        let mut current = Idx::NONE;

        // Start from the highest level
        for i in (0..=self.level).rev() {
            let mut next = if current.is_none() {
                self.head[i]
            } else {
                // Safety: current is valid
                unsafe { storage.get_unchecked(current) }.forward[i]
            };

            // Traverse forward while next key is less than target
            while next.is_some() {
                let next_node = unsafe { storage.get_unchecked(next) };
                if next_node.key >= *key {
                    break;
                }
                current = next;
                next = next_node.forward[i];
            }

            update[i] = current;
        }

        // Check if we found the exact key
        let next = if current.is_none() {
            self.head[0]
        } else {
            unsafe { storage.get_unchecked(current) }.forward[0]
        };

        if next.is_some() && unsafe { storage.get_unchecked(next) }.key == *key {
            Some(next)
        } else {
            None
        }
    }

    /// Generates a random level for a new node.
    ///
    /// Uses geometric distribution with p=0.5 by counting trailing ones
    /// in a random number.
    #[inline]
    fn random_level(&mut self) -> u8 {
        let r = self.rng.next_u32();
        let level = (r.trailing_ones() as usize) / (self.level_divisor as usize);
        level.min(MAX_LEVEL - 1) as u8
    }

    /// Links a newly inserted node into the skip list structure.
    #[inline]
    fn link_node(&mut self, storage: &mut S, idx: Idx, new_level: u8, update: &[Idx; MAX_LEVEL]) {
        // First pass: collect what we need to set as forward pointers
        let mut new_forwards = [Idx::NONE; MAX_LEVEL];
        for i in 0..=new_level as usize {
            if update[i].is_none() {
                new_forwards[i] = self.head[i];
            } else {
                // Safety: update[i] is valid from search
                new_forwards[i] = unsafe { storage.get_unchecked(update[i]) }.forward[i];
            }
        }

        // Second pass: set the new node's forward pointers
        {
            let node = storage.get_mut(idx).expect("invalid index");
            for i in 0..=new_level as usize {
                node.forward[i] = new_forwards[i];
            }
        }

        // Third pass: update predecessors and heads to point to new node
        for i in 0..=new_level as usize {
            if update[i].is_none() {
                self.head[i] = idx;
            } else {
                // Safety: update[i] is valid from search
                let prev = unsafe { storage.get_unchecked_mut(update[i]) };
                prev.forward[i] = idx;
            }
        }

        // Update tail if this is the new last node
        let node = storage.get(idx).expect("invalid index");
        if node.forward[0].is_none() {
            self.tail = idx;
        }

        // Update max level
        if new_level as usize > self.level {
            self.level = new_level as usize;
        }

        self.len += 1;
    }
}

// ============================================================================
// Bounded storage impl
// ============================================================================

impl<K, V, S, Idx, R, const MAX_LEVEL: usize> SkipList<K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: BoundedStorage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Tries to insert a key-value pair, returning an error if storage is full.
    ///
    /// If the key already exists, the value is updated and the old value is returned.
    pub fn try_insert(
        &mut self,
        storage: &mut S,
        key: K,
        value: V,
    ) -> Result<Option<V>, Full<(K, V)>> {
        // Search first to check if key exists
        let mut update = [Idx::NONE; MAX_LEVEL];
        let found = self.search(storage, &key, &mut update);

        // If key exists, update value
        if let Some(existing_idx) = found {
            let node = storage.get_mut(existing_idx).expect("invalid index");
            let old_value = core::mem::replace(&mut node.value, value);
            return Ok(Some(old_value));
        }

        // Key doesn't exist, allocate new node
        let new_level = self.random_level();
        let node = SkipNode::new(key, value, new_level);
        let idx = match storage.try_insert(node) {
            Ok(idx) => idx,
            Err(Full(node)) => return Err(Full((node.key, node.value))),
        };

        // Link the node into the list
        self.link_node(storage, idx, new_level, &update);

        Ok(None)
    }
}

// ============================================================================
// Unbounded storage impl
// ============================================================================

impl<K, V, S, Idx, R, const MAX_LEVEL: usize> SkipList<K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: UnboundedStorage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Inserts a key-value pair.
    ///
    /// If the key already exists, the value is updated and the old value is returned.
    pub fn insert(&mut self, storage: &mut S, key: K, value: V) -> Option<V> {
        // Search first to check if key exists
        let mut update = [Idx::NONE; MAX_LEVEL];
        let found = self.search(storage, &key, &mut update);

        // If key exists, update value
        if let Some(existing_idx) = found {
            let node = storage.get_mut(existing_idx).expect("invalid index");
            let old_value = core::mem::replace(&mut node.value, value);
            return Some(old_value);
        }

        // Key doesn't exist, allocate new node
        let new_level = self.random_level();
        let node = SkipNode::new(key, value, new_level);
        let idx = storage.insert(node);

        // Link the node into the list
        self.link_node(storage, idx, new_level, &update);

        None
    }
}

// ============================================================================
// Entry API
// ============================================================================

/// A view into a single entry in the skip list.
pub enum Entry<'a, K, V, S, Idx, R, const MAX_LEVEL: usize>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V, S, Idx, R, MAX_LEVEL>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V, S, Idx, R, MAX_LEVEL>),
}

/// An occupied entry in the skip list.
pub struct OccupiedEntry<'a, K, V, S, Idx, R, const MAX_LEVEL: usize>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    list: &'a mut SkipList<K, V, S, Idx, R, MAX_LEVEL>,
    storage: &'a mut S,
    idx: Idx,
    update: [Idx; MAX_LEVEL],
}

/// A vacant entry in the skip list.
pub struct VacantEntry<'a, K, V, S, Idx, R, const MAX_LEVEL: usize>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    list: &'a mut SkipList<K, V, S, Idx, R, MAX_LEVEL>,
    storage: &'a mut S,
    key: K,
    update: [Idx; MAX_LEVEL],
}

impl<'a, K, V, S, Idx, R, const MAX_LEVEL: usize> Entry<'a, K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Returns a reference to the key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(e) => &e.storage.get(e.idx).expect("invalid index").key,
            Entry::Vacant(e) => &e.key,
        }
    }

    /// Modifies an existing entry before insertion.
    pub fn and_modify<F>(mut self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        if let Entry::Occupied(ref mut e) = self {
            let node = e.storage.get_mut(e.idx).expect("invalid index");
            f(&mut node.value);
        }
        self
    }
}

impl<'a, K, V, S, Idx, R, const MAX_LEVEL: usize> Entry<'a, K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: BoundedStorage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Ensures a value is in the entry by inserting the default if empty.
    /// Returns `None` if storage is full.
    pub fn or_try_insert(self, default: V) -> Option<&'a mut V> {
        self.or_try_insert_with(|| default)
    }

    /// Ensures a value is in the entry by inserting the result of the function if empty.
    /// Returns `None` if storage is full.
    pub fn or_try_insert_with<F: FnOnce() -> V>(self, f: F) -> Option<&'a mut V> {
        match self {
            Entry::Occupied(e) => Some(&mut e.storage.get_mut(e.idx).expect("invalid index").value),
            Entry::Vacant(e) => e.try_insert(f()),
        }
    }
}

impl<'a, K, V, S, Idx, R, const MAX_LEVEL: usize> Entry<'a, K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: UnboundedStorage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Ensures a value is in the entry by inserting the default if empty.
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.or_insert_with(|| default)
    }

    /// Ensures a value is in the entry by inserting the result of the function if empty.
    pub fn or_insert_with<F: FnOnce() -> V>(self, f: F) -> &'a mut V {
        match self {
            Entry::Occupied(e) => &mut e.storage.get_mut(e.idx).expect("invalid index").value,
            Entry::Vacant(e) => e.insert(f()),
        }
    }

    /// Ensures a value is in the entry by inserting the default value if empty.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }
}

impl<'a, K, V, S, Idx, R, const MAX_LEVEL: usize> OccupiedEntry<'a, K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Gets a reference to the value.
    #[inline]
    pub fn get(&self) -> &V {
        &self.storage.get(self.idx).expect("invalid index").value
    }

    /// Gets a mutable reference to the value.
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.storage.get_mut(self.idx).expect("invalid index").value
    }

    /// Converts to a mutable reference to the value.
    pub fn into_mut(self) -> &'a mut V {
        &mut self.storage.get_mut(self.idx).expect("invalid index").value
    }

    /// Removes the entry and returns the value.
    pub fn remove(self) -> V {
        let idx = self.idx;

        // Get raw pointer - avoids holding borrow
        let node_ptr =
            self.storage.get(idx).expect("invalid index") as *const SkipNode<K, V, Idx, MAX_LEVEL>;

        let node_level = unsafe { (*node_ptr).level } as usize;
        let forward_0_is_none = unsafe { (*node_ptr).forward[0].is_none() };

        // Unlink at each level
        for i in 0..=node_level {
            let next = unsafe { (*node_ptr).forward[i] };

            if self.update[i].is_none() {
                self.list.head[i] = next;
            } else {
                let prev = unsafe { self.storage.get_unchecked_mut(self.update[i]) };
                prev.forward[i] = next;
            }
        }

        // Update tail if we removed the last node
        if forward_0_is_none {
            self.list.tail = self.update[0];
        }

        // Reduce level if needed
        while self.list.level > 0 && self.list.head[self.list.level].is_none() {
            self.list.level -= 1;
        }

        self.list.len -= 1;

        self.storage.remove(idx).expect("invalid index").value
    }
}

impl<'a, K, V, S, Idx, R, const MAX_LEVEL: usize> VacantEntry<'a, K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: BoundedStorage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Tries to insert a value, returning `None` if storage is full.
    pub fn try_insert(self, value: V) -> Option<&'a mut V> {
        let new_level = self.list.random_level();
        let node = SkipNode::new(self.key, value, new_level);
        let idx = self.storage.try_insert(node).ok()?;

        // Link the node
        self.list
            .link_node(self.storage, idx, new_level, &self.update);

        Some(&mut self.storage.get_mut(idx).expect("just inserted").value)
    }
}

impl<'a, K, V, S, Idx, R, const MAX_LEVEL: usize> VacantEntry<'a, K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: UnboundedStorage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Inserts a value.
    pub fn insert(self, value: V) -> &'a mut V {
        let new_level = self.list.random_level();
        let node = SkipNode::new(self.key, value, new_level);
        let idx = self.storage.insert(node);

        // Link the node
        self.list
            .link_node(self.storage, idx, new_level, &self.update);

        &mut self.storage.get_mut(idx).expect("just inserted").value
    }
}

impl<K, V, S, Idx, R, const MAX_LEVEL: usize> SkipList<K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Gets the entry for the given key.
    pub fn entry<'a>(
        &'a mut self,
        storage: &'a mut S,
        key: K,
    ) -> Entry<'a, K, V, S, Idx, R, MAX_LEVEL> {
        let mut update = [Idx::NONE; MAX_LEVEL];
        let found = self.search(storage, &key, &mut update);

        if let Some(idx) = found {
            Entry::Occupied(OccupiedEntry {
                list: self,
                storage,
                idx,
                update,
            })
        } else {
            Entry::Vacant(VacantEntry {
                list: self,
                storage,
                key,
                update,
            })
        }
    }
}

// ============================================================================
// Cursor
// ============================================================================

/// A cursor for traversing and modifying the skip list.
///
/// Unlike iterators, cursors track predecessor nodes at each level as they
/// traverse. This enables O(1) removal at the current position without
/// re-searching. The tradeoff is ~2 index writes per `move_next()` call
/// on average.
///
/// # Use case
///
/// Cursors are designed for sweep operations that may remove elements:
///
/// ```ignore
/// let mut cursor = skip_list.cursor_front(&mut storage);
/// while let Some((price, level)) = cursor.current_mut() {
///     process_level(level);
///     if level.is_empty() {
///         cursor.remove_current();  // O(1), advances automatically
///     } else {
///         cursor.move_next();
///     }
/// }
/// ```
///
/// For read-only traversal, prefer `iter()` which has no tracking overhead.
pub struct Cursor<'a, K, V, S, Idx, R, const MAX_LEVEL: usize>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    list: &'a mut SkipList<K, V, S, Idx, R, MAX_LEVEL>,
    storage: &'a mut S,
    current: Idx,
    prev_at_level: [Idx; MAX_LEVEL],
}

impl<'a, K, V, S, Idx, R, const MAX_LEVEL: usize> Cursor<'a, K, V, S, Idx, R, MAX_LEVEL>
where
    K: Ord,
    Idx: Key,
    R: RngCore,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    /// Returns a reference to the current key-value pair, or `None` if exhausted.
    pub fn current(&self) -> Option<(&K, &V)> {
        if self.current.is_none() {
            return None;
        }
        let node = self.storage.get(self.current).expect("invalid current");
        Some((&node.key, &node.value))
    }

    /// Returns a mutable reference to the current value, or `None` if exhausted.
    pub fn current_mut(&mut self) -> Option<(&K, &mut V)> {
        if self.current.is_none() {
            return None;
        }
        let node = self.storage.get_mut(self.current).expect("invalid current");
        Some((&node.key, &mut node.value))
    }

    /// Returns a reference to the next key-value pair without advancing.
    pub fn peek_next(&self) -> Option<(&K, &V)> {
        if self.current.is_none() {
            return None;
        }
        let node = self.storage.get(self.current).expect("invalid current");
        let next = node.forward[0];
        if next.is_none() {
            return None;
        }
        let next_node = self.storage.get(next).expect("invalid next");
        Some((&next_node.key, &next_node.value))
    }

    /// Advances the cursor to the next position.
    ///
    /// Updates predecessor tracking at each level the current node participates
    /// in. This is O(1) amortized (~2 writes average) and enables O(1) removal
    /// via `remove_current()`.
    pub fn move_next(&mut self) {
        if self.current.is_none() {
            return;
        }

        let node = self.storage.get(self.current).expect("invalid current");
        let node_level = node.level as usize;

        // Track current as predecessor for levels it participates in.
        // Higher levels retain their previous values - those predecessors
        // are still valid since we only move forward at level 0.
        for i in 0..=node_level {
            self.prev_at_level[i] = self.current;
        }

        // Advance
        self.current = node.forward[0];
    }

    /// Removes the current element and advances to the next.
    ///
    /// Returns the removed key-value pair, or `None` if cursor is exhausted.
    pub fn remove_current(&mut self) -> Option<(K, V)> {
        if self.current.is_none() {
            return None;
        }

        let idx = self.current;

        // Get raw pointer - avoids holding borrow
        let node_ptr = self.storage.get(idx).expect("invalid current")
            as *const SkipNode<K, V, Idx, MAX_LEVEL>;

        // Safety: node_ptr is valid, we're just reading
        let node_level = unsafe { (*node_ptr).level } as usize;
        let next = unsafe { (*node_ptr).forward[0] };

        // Update forward pointers at each level
        for i in 0..=node_level {
            // Safety: node_ptr still valid, just reading forward[i]
            let forward_i = unsafe { (*node_ptr).forward[i] };

            if self.prev_at_level[i].is_none() {
                self.list.head[i] = forward_i;
            } else {
                // Safety: prev_at_level[i] != idx (predecessor is always before current)
                let prev = unsafe { self.storage.get_unchecked_mut(self.prev_at_level[i]) };
                prev.forward[i] = forward_i;
            }
        }

        // Update tail if we removed the last node
        if next.is_none() {
            self.list.tail = self.prev_at_level[0];
        }

        // Reduce level if needed
        while self.list.level > 0 && self.list.head[self.list.level].is_none() {
            self.list.level -= 1;
        }

        self.list.len -= 1;

        // Advance cursor
        self.current = next;

        let node = self.storage.remove(idx).expect("invalid index");
        Some((node.key, node.value))
    }
}

// ============================================================================
// Iterators
// ============================================================================

/// An iterator over key-value pairs in sorted order.
pub struct Iter<'a, K, V, S, Idx, const MAX_LEVEL: usize>
where
    Idx: Key,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    storage: &'a S,
    current: Idx,
    _marker: PhantomData<(K, V)>,
}

impl<'a, K: 'a, V: 'a, S, Idx: 'a, const MAX_LEVEL: usize> Iterator
    for Iter<'a, K, V, S, Idx, MAX_LEVEL>
where
    Idx: Key,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.current.is_none() {
            return None;
        }
        let node = self.storage.get(self.current).expect("invalid index");
        self.current = node.forward[0];
        Some((&node.key, &node.value))
    }
}

/// A mutable iterator over key-value pairs in sorted order.
pub struct IterMut<'a, K, V, S, Idx, const MAX_LEVEL: usize>
where
    Idx: Key,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    storage: &'a mut S,
    current: Idx,
    _marker: PhantomData<(K, V)>,
}

impl<'a, K: 'a, V: 'a, S, Idx: 'a, const MAX_LEVEL: usize> Iterator
    for IterMut<'a, K, V, S, Idx, MAX_LEVEL>
where
    Idx: Key,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.current.is_none() {
            return None;
        }
        let idx = self.current;

        // Safety: We only visit each node once (current advances before return).
        // The storage lives for 'a, so the node reference is valid for 'a.
        // We're working around the borrow checker's inability to track this.
        let node: &'a mut SkipNode<K, V, Idx, MAX_LEVEL> =
            unsafe { &mut *(self.storage.get_mut(idx).expect("invalid index") as *mut _) };

        self.current = node.forward[0];
        Some((&node.key, &mut node.value))
    }
}

/// An iterator over keys in sorted order.
pub struct Keys<'a, K, V, S, Idx, const MAX_LEVEL: usize>
where
    Idx: Key,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    inner: Iter<'a, K, V, S, Idx, MAX_LEVEL>,
}

impl<'a, K: 'a, V: 'a, S, Idx: 'a, const MAX_LEVEL: usize> Iterator
    for Keys<'a, K, V, S, Idx, MAX_LEVEL>
where
    Idx: Key,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

/// An iterator over values in sorted order by key.
pub struct Values<'a, K, V, S, Idx, const MAX_LEVEL: usize>
where
    Idx: Key,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    inner: Iter<'a, K, V, S, Idx, MAX_LEVEL>,
}

impl<'a, K: 'a, V: 'a, S, Idx: 'a, const MAX_LEVEL: usize> Iterator
    for Values<'a, K, V, S, Idx, MAX_LEVEL>
where
    Idx: Key,
    S: Storage<SkipNode<K, V, Idx, MAX_LEVEL>, Key = Idx>,
{
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

// ============================================================================
// Type aliases
// ============================================================================

/// Boxed storage for skip list nodes.
pub type BoxedSkipStorage<K, V, Idx = u32, const MAX_LEVEL: usize = 16> =
    crate::BoxedStorage<SkipNode<K, V, Idx, MAX_LEVEL>, Idx>;

#[cfg(feature = "slab")]
/// Slab storage for skip list nodes (unbounded).
pub type SlabSkipStorage<K, V, const MAX_LEVEL: usize = 16> =
    slab::Slab<SkipNode<K, V, usize, MAX_LEVEL>>;

#[cfg(feature = "nexus-slab")]
/// Nexus slab storage for skip list nodes (bounded).
pub type NexusSkipStorage<K, V, const MAX_LEVEL: usize = 16> =
    nexus_slab::Slab<SkipNode<K, V, nexus_slab::Key, MAX_LEVEL>>;

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    type TestStorage = BoxedSkipStorage<u64, String, u32, 8>;
    type TestSkipList = SkipList<u64, String, TestStorage, u32, SmallRng, 8>;

    fn make_rng() -> SmallRng {
        SmallRng::seed_from_u64(12345)
    }

    // ========================================================================
    // Basic operations
    // ========================================================================

    #[test]
    fn new_is_empty() {
        let storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let list: TestSkipList = SkipList::new(make_rng());

        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(list.first(&storage), None);
        assert_eq!(list.last(&storage), None);
    }

    #[test]
    fn insert_single() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        let old = list.try_insert(&mut storage, 100, "hello".into()).unwrap();
        assert_eq!(old, None);
        assert_eq!(list.len(), 1);
        assert!(!list.is_empty());

        assert_eq!(list.get(&storage, &100), Some(&"hello".into()));
        assert_eq!(list.first(&storage), Some((&100, &"hello".into())));
        assert_eq!(list.last(&storage), Some((&100, &"hello".into())));
    }

    #[test]
    fn insert_updates_existing() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 100, "first".into()).unwrap();
        let old = list.try_insert(&mut storage, 100, "second".into()).unwrap();

        assert_eq!(old, Some("first".into()));
        assert_eq!(list.len(), 1);
        assert_eq!(list.get(&storage, &100), Some(&"second".into()));
    }

    #[test]
    fn insert_multiple_maintains_order() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        // Insert out of order
        list.try_insert(&mut storage, 50, "fifty".into()).unwrap();
        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 90, "ninety".into()).unwrap();
        list.try_insert(&mut storage, 30, "thirty".into()).unwrap();

        assert_eq!(list.len(), 4);
        assert_eq!(list.first(&storage), Some((&10, &"ten".into())));
        assert_eq!(list.last(&storage), Some((&90, &"ninety".into())));

        // Verify sorted order via iterator
        let keys: Vec<_> = list.keys(&storage).copied().collect();
        assert_eq!(keys, vec![10, 30, 50, 90]);
    }

    #[test]
    fn get_and_get_mut() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 100, "hello".into()).unwrap();

        assert_eq!(list.get(&storage, &100), Some(&"hello".into()));
        assert_eq!(list.get(&storage, &999), None);

        // Mutate via get_mut
        if let Some(v) = list.get_mut(&mut storage, &100) {
            *v = "world".into();
        }
        assert_eq!(list.get(&storage, &100), Some(&"world".into()));
    }

    #[test]
    fn contains_key() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 100, "hello".into()).unwrap();

        assert!(list.contains_key(&storage, &100));
        assert!(!list.contains_key(&storage, &999));
    }

    // ========================================================================
    // Remove operations
    // ========================================================================

    #[test]
    fn remove_existing() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 100, "hello".into()).unwrap();
        let removed = list.remove(&mut storage, &100);

        assert_eq!(removed, Some("hello".into()));
        assert!(list.is_empty());
        assert_eq!(list.get(&storage, &100), None);
    }

    #[test]
    fn remove_nonexistent() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 100, "hello".into()).unwrap();
        let removed = list.remove(&mut storage, &999);

        assert_eq!(removed, None);
        assert_eq!(list.len(), 1);
    }

    #[test]
    fn remove_middle_preserves_order() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();
        list.try_insert(&mut storage, 30, "thirty".into()).unwrap();

        list.remove(&mut storage, &20);

        let keys: Vec<_> = list.keys(&storage).copied().collect();
        assert_eq!(keys, vec![10, 30]);
        assert_eq!(list.first(&storage), Some((&10, &"ten".into())));
        assert_eq!(list.last(&storage), Some((&30, &"thirty".into())));
    }

    #[test]
    fn remove_first_updates_head() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();

        list.remove(&mut storage, &10);

        assert_eq!(list.first(&storage), Some((&20, &"twenty".into())));
    }

    #[test]
    fn remove_last_updates_tail() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();

        list.remove(&mut storage, &20);

        assert_eq!(list.last(&storage), Some((&10, &"ten".into())));
    }

    // ========================================================================
    // Pop operations
    // ========================================================================

    #[test]
    fn pop_first() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();
        list.try_insert(&mut storage, 30, "thirty".into()).unwrap();

        assert_eq!(list.pop_first(&mut storage), Some((10, "ten".into())));
        assert_eq!(list.pop_first(&mut storage), Some((20, "twenty".into())));
        assert_eq!(list.pop_first(&mut storage), Some((30, "thirty".into())));
        assert_eq!(list.pop_first(&mut storage), None);
        assert!(list.is_empty());
    }

    #[test]
    fn pop_last() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();
        list.try_insert(&mut storage, 30, "thirty".into()).unwrap();

        assert_eq!(list.pop_last(&mut storage), Some((30, "thirty".into())));
        assert_eq!(list.pop_last(&mut storage), Some((20, "twenty".into())));
        assert_eq!(list.pop_last(&mut storage), Some((10, "ten".into())));
        assert_eq!(list.pop_last(&mut storage), None);
        assert!(list.is_empty());
    }

    // ========================================================================
    // Clear
    // ========================================================================

    #[test]
    fn clear() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();

        list.clear(&mut storage);

        assert!(list.is_empty());
        assert_eq!(list.first(&storage), None);
        assert_eq!(list.last(&storage), None);
    }

    // ========================================================================
    // Iteration
    // ========================================================================

    #[test]
    fn iter_sorted() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 50, "fifty".into()).unwrap();
        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 90, "ninety".into()).unwrap();

        let pairs: Vec<_> = list.iter(&storage).map(|(k, v)| (*k, v.clone())).collect();
        assert_eq!(
            pairs,
            vec![
                (10, "ten".into()),
                (50, "fifty".into()),
                (90, "ninety".into())
            ]
        );
    }

    #[test]
    fn iter_mut() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "a".into()).unwrap();
        list.try_insert(&mut storage, 20, "b".into()).unwrap();

        for (_, v) in list.iter_mut(&mut storage) {
            v.push_str("_modified");
        }

        assert_eq!(list.get(&storage, &10), Some(&"a_modified".into()));
        assert_eq!(list.get(&storage, &20), Some(&"b_modified".into()));
    }

    #[test]
    fn keys_and_values() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();

        let keys: Vec<_> = list.keys(&storage).copied().collect();
        let values: Vec<_> = list.values(&storage).cloned().collect();

        assert_eq!(keys, vec![10, 20]);
        assert_eq!(values, vec!["ten".to_string(), "twenty".to_string()]);
    }

    // ========================================================================
    // Entry API
    // ========================================================================

    #[test]
    fn entry_or_try_insert_vacant() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        let val = list
            .entry(&mut storage, 100)
            .or_try_insert("hello".into())
            .unwrap();
        assert_eq!(val, &"hello".to_string());
        assert_eq!(list.get(&storage, &100), Some(&"hello".into()));
    }

    #[test]
    fn entry_or_try_insert_occupied() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 100, "existing".into())
            .unwrap();

        let val = list
            .entry(&mut storage, 100)
            .or_try_insert("new".into())
            .unwrap();
        assert_eq!(val, &"existing".to_string());
    }

    #[test]
    fn entry_and_modify() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 100, "hello".into()).unwrap();

        list.entry(&mut storage, 100)
            .and_modify(|v| v.push_str(" world"))
            .or_try_insert("default".into());

        assert_eq!(list.get(&storage, &100), Some(&"hello world".into()));
    }

    #[test]
    fn entry_remove() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 100, "hello".into()).unwrap();

        if let Entry::Occupied(entry) = list.entry(&mut storage, 100) {
            let val = entry.remove();
            assert_eq!(val, "hello".to_string());
        }

        assert!(list.is_empty());
    }

    // ========================================================================
    // Cursor
    // ========================================================================

    #[test]
    fn cursor_traverse() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();
        list.try_insert(&mut storage, 30, "thirty".into()).unwrap();

        let mut cursor = list.cursor_front(&mut storage);
        let mut keys = Vec::new();

        while let Some((k, _)) = cursor.current() {
            keys.push(*k);
            cursor.move_next();
        }

        assert_eq!(keys, vec![10, 20, 30]);
    }

    #[test]
    fn cursor_remove_current() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();
        list.try_insert(&mut storage, 30, "thirty".into()).unwrap();

        let mut cursor = list.cursor_front(&mut storage);

        // Remove first
        let removed = cursor.remove_current();
        assert_eq!(removed, Some((10, "ten".into())));

        // Now at 20
        assert_eq!(cursor.current().map(|(k, _)| *k), Some(20));

        // Remove 20
        cursor.remove_current();

        // Now at 30
        assert_eq!(cursor.current().map(|(k, _)| *k), Some(30));
    }

    #[test]
    fn cursor_sweep_remove_evens() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        for i in 1..=6 {
            list.try_insert(&mut storage, i, format!("val{}", i))
                .unwrap();
        }

        // Remove even keys
        let mut cursor = list.cursor_front(&mut storage);
        while let Some((k, _)) = cursor.current() {
            if k % 2 == 0 {
                cursor.remove_current();
            } else {
                cursor.move_next();
            }
        }

        let keys: Vec<_> = list.keys(&storage).copied().collect();
        assert_eq!(keys, vec![1, 3, 5]);
    }

    #[test]
    fn cursor_peek_next() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();

        let cursor = list.cursor_front(&mut storage);
        assert_eq!(cursor.current().map(|(k, _)| *k), Some(10));
        assert_eq!(cursor.peek_next().map(|(k, _)| *k), Some(20));
    }

    // ========================================================================
    // Level ratio
    // ========================================================================

    #[test]
    fn level_ratio_default() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(100);
        let mut list: TestSkipList = SkipList::new(make_rng());

        for i in 0..50 {
            list.try_insert(&mut storage, i, format!("val{}", i))
                .unwrap();
        }

        assert_eq!(list.len(), 50);
        // Just verify it works - level distribution is probabilistic
    }

    #[test]
    fn level_ratio_redis_style() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(100);
        let mut list: TestSkipList = SkipList::with_level_ratio(make_rng(), 4);

        for i in 0..50 {
            list.try_insert(&mut storage, i, format!("val{}", i))
                .unwrap();
        }

        assert_eq!(list.len(), 50);
    }

    #[test]
    fn level_ratio_invalid_rounded() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        // Invalid value 3 should round to 4
        let mut list: TestSkipList = SkipList::with_level_ratio(make_rng(), 3);

        list.try_insert(&mut storage, 100, "hello".into()).unwrap();
        assert_eq!(list.get(&storage, &100), Some(&"hello".into()));
    }

    // ========================================================================
    // Storage full
    // ========================================================================

    #[test]
    fn storage_full() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(2);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();

        let result = list.try_insert(&mut storage, 30, "thirty".into());
        assert!(result.is_err());

        if let Err(Full((k, v))) = result {
            assert_eq!(k, 30);
            assert_eq!(v, "thirty".to_string());
        }
    }

    // ========================================================================
    // First/Last mut
    // ========================================================================

    #[test]
    fn first_mut_and_last_mut() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10);
        let mut list: TestSkipList = SkipList::new(make_rng());

        list.try_insert(&mut storage, 10, "ten".into()).unwrap();
        list.try_insert(&mut storage, 20, "twenty".into()).unwrap();

        if let Some((_, v)) = list.first_mut(&mut storage) {
            *v = "TEN".into();
        }
        if let Some((_, v)) = list.last_mut(&mut storage) {
            *v = "TWENTY".into();
        }

        assert_eq!(list.get(&storage, &10), Some(&"TEN".into()));
        assert_eq!(list.get(&storage, &20), Some(&"TWENTY".into()));
    }

    // ========================================================================
    // Stress test
    // ========================================================================

    #[test]
    fn stress_insert_remove() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(1000);
        let mut list: TestSkipList = SkipList::new(make_rng());

        // Insert 500 items
        for i in 0..500 {
            list.try_insert(&mut storage, i, format!("val{}", i))
                .unwrap();
        }
        assert_eq!(list.len(), 500);

        // Remove odd keys
        for i in (1..500).step_by(2) {
            list.remove(&mut storage, &i);
        }
        assert_eq!(list.len(), 250);

        // Verify remaining are even and sorted
        let keys: Vec<_> = list.keys(&storage).copied().collect();
        for (i, k) in keys.iter().enumerate() {
            assert_eq!(*k, (i * 2) as u64);
        }
    }

    // ========================================================================
    // Stress tests
    // ========================================================================

    #[test]
    fn stress_random_operations() {
        use rand::Rng;

        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(500);
        let mut list: TestSkipList = SkipList::new(make_rng());
        let mut rng = SmallRng::seed_from_u64(99999);
        let mut reference: std::collections::BTreeMap<u64, String> =
            std::collections::BTreeMap::new();

        for _ in 0..1000 {
            let op = rng.random_range(0..100);
            let key = rng.random_range(0..200);

            if op < 60 {
                // Insert
                let value = format!("v{}", key);
                let list_result = list.try_insert(&mut storage, key, value.clone());
                let ref_result = reference.insert(key, value);

                match list_result {
                    Ok(old) => assert_eq!(old, ref_result),
                    Err(_) => {
                        // Storage full - reference should have the key already or we skip
                        if ref_result.is_none() {
                            reference.remove(&key);
                        }
                    }
                }
            } else if op < 90 {
                // Remove
                let list_result = list.remove(&mut storage, &key);
                let ref_result = reference.remove(&key);
                assert_eq!(list_result, ref_result);
            } else {
                // Get
                let list_result = list.get(&storage, &key);
                let ref_result = reference.get(&key);
                assert_eq!(list_result, ref_result);
            }
        }

        // Verify final state matches
        assert_eq!(list.len(), reference.len());

        let list_keys: Vec<_> = list.keys(&storage).copied().collect();
        let ref_keys: Vec<_> = reference.keys().copied().collect();
        assert_eq!(list_keys, ref_keys);
    }

    #[test]
    fn stress_head_tail_invariants() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(200);
        let mut list: TestSkipList = SkipList::new(make_rng());

        // Insert in reverse order
        for i in (0..100).rev() {
            list.try_insert(&mut storage, i, format!("v{}", i)).unwrap();

            // First should always be smallest inserted so far
            assert_eq!(list.first(&storage).map(|(k, _)| *k), Some(i));
            // Last should always be 99
            assert_eq!(list.last(&storage).map(|(k, _)| *k), Some(99));
        }

        // Remove from front
        for i in 0..50 {
            list.remove(&mut storage, &i);
            assert_eq!(list.first(&storage).map(|(k, _)| *k), Some(i + 1));
            assert_eq!(list.last(&storage).map(|(k, _)| *k), Some(99));
        }

        // Remove from back
        for i in (75..100).rev() {
            list.remove(&mut storage, &i);
            assert_eq!(list.first(&storage).map(|(k, _)| *k), Some(50));
            assert_eq!(list.last(&storage).map(|(k, _)| *k), Some(i - 1));
        }

        // Verify what remains
        let keys: Vec<_> = list.keys(&storage).copied().collect();
        assert_eq!(keys, (50..75).collect::<Vec<_>>());
    }

    #[test]
    fn stress_pop_first_drain() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(500);
        let mut list: TestSkipList = SkipList::new(make_rng());

        for i in 0..300 {
            list.try_insert(&mut storage, i, format!("v{}", i)).unwrap();
        }

        // Drain via pop_first, verify order
        let mut prev = None;
        let mut count = 0;
        while let Some((k, _)) = list.pop_first(&mut storage) {
            if let Some(p) = prev {
                assert!(k > p, "pop_first returned out of order: {} after {}", k, p);
            }
            prev = Some(k);
            count += 1;
        }

        assert_eq!(count, 300);
        assert!(list.is_empty());
        assert_eq!(list.first(&storage), None);
        assert_eq!(list.last(&storage), None);
    }

    #[test]
    fn stress_pop_last_drain() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(500);
        let mut list: TestSkipList = SkipList::new(make_rng());

        for i in 0..300 {
            list.try_insert(&mut storage, i, format!("v{}", i)).unwrap();
        }

        // Drain via pop_last, verify reverse order
        let mut prev = None;
        let mut count = 0;
        while let Some((k, _)) = list.pop_last(&mut storage) {
            if let Some(p) = prev {
                assert!(k < p, "pop_last returned out of order: {} after {}", k, p);
            }
            prev = Some(k);
            count += 1;
        }

        assert_eq!(count, 300);
        assert!(list.is_empty());
    }

    #[test]
    fn stress_cursor_full_sweep_remove() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(500);
        let mut list: TestSkipList = SkipList::new(make_rng());

        for i in 0..200 {
            list.try_insert(&mut storage, i, format!("v{}", i)).unwrap();
        }

        // Remove everything via cursor
        let mut cursor = list.cursor_front(&mut storage);
        let mut count = 0;
        let mut prev = None;

        while cursor.current().is_some() {
            let (k, _) = cursor.remove_current().unwrap();
            if let Some(p) = prev {
                assert!(k > p, "cursor remove out of order: {} after {}", k, p);
            }
            prev = Some(k);
            count += 1;
        }

        assert_eq!(count, 200);
        assert!(list.is_empty());
    }

    #[test]
    fn stress_cursor_selective_remove() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(500);
        let mut list: TestSkipList = SkipList::new(make_rng());

        for i in 0..200 {
            list.try_insert(&mut storage, i, format!("v{}", i)).unwrap();
        }

        // Remove multiples of 3
        let mut cursor = list.cursor_front(&mut storage);
        while let Some((k, _)) = cursor.current() {
            if k % 3 == 0 {
                cursor.remove_current();
            } else {
                cursor.move_next();
            }
        }

        // Verify
        let keys: Vec<_> = list.keys(&storage).copied().collect();
        for k in &keys {
            assert!(k % 3 != 0, "key {} should have been removed", k);
        }

        // Count: 200 total, 67 multiples of 3 (0, 3, 6, ..., 198)
        assert_eq!(keys.len(), 200 - 67);
    }

    #[test]
    fn stress_interleaved_insert_remove() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(100);
        let mut list: TestSkipList = SkipList::new(make_rng());

        for round in 0..10 {
            let base = round * 20;

            // Insert 20
            for i in 0..20 {
                list.try_insert(&mut storage, base + i, format!("v{}", base + i))
                    .unwrap();
            }

            // Remove 10 (odd offsets)
            for i in (1..20).step_by(2) {
                list.remove(&mut storage, &(base + i));
            }
        }

        // Should have 10 items per round = 100 total
        assert_eq!(list.len(), 100);

        // All remaining should be even offsets within their round
        let keys: Vec<_> = list.keys(&storage).copied().collect();
        for k in &keys {
            assert!(k % 2 == 0, "key {} should be even", k);
        }
    }

    #[test]
    fn stress_entry_api() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(500);
        let mut list: TestSkipList = SkipList::new(make_rng());

        // Use entry API to build counters
        for i in 0..500 {
            let key = i % 50; // 50 unique keys, each hit 10 times
            list.entry(&mut storage, key)
                .and_modify(|v| {
                    let count: u32 = v.parse().unwrap();
                    *v = (count + 1).to_string();
                })
                .or_try_insert("1".into());
        }

        assert_eq!(list.len(), 50);

        // Each key should have count 10
        for i in 0..50 {
            let val = list.get(&storage, &i).unwrap();
            assert_eq!(val, "10", "key {} has wrong count: {}", i, val);
        }
    }

    #[test]
    fn stress_reinsert_after_remove() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(100);
        let mut list: TestSkipList = SkipList::new(make_rng());

        for _ in 0..5 {
            // Fill
            for i in 0..50 {
                list.try_insert(&mut storage, i, format!("v{}", i)).unwrap();
            }
            assert_eq!(list.len(), 50);

            // Empty via clear
            list.clear(&mut storage);
            assert!(list.is_empty());
            assert_eq!(list.first(&storage), None);
            assert_eq!(list.last(&storage), None);
        }

        // Final fill and verify
        for i in 0..50 {
            list.try_insert(&mut storage, i, format!("final{}", i))
                .unwrap();
        }

        let keys: Vec<_> = list.keys(&storage).copied().collect();
        assert_eq!(keys, (0..50).collect::<Vec<_>>());
    }
}

#[cfg(test)]
mod bench_skiplist {
    use super::*;
    use hdrhistogram::Histogram;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    #[inline]
    fn rdtscp() -> u64 {
        #[cfg(target_arch = "x86_64")]
        unsafe {
            core::arch::x86_64::__rdtscp(&mut 0)
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            std::time::Instant::now().elapsed().as_nanos() as u64
        }
    }

    fn print_histogram(name: &str, hist: &Histogram<u64>) {
        println!(
            "{:24} p50: {:4} cycles | p99: {:4} cycles | p999: {:5} cycles | min: {:4} | max: {:5}",
            name,
            hist.value_at_quantile(0.50),
            hist.value_at_quantile(0.99),
            hist.value_at_quantile(0.999),
            hist.min(),
            hist.max(),
        );
    }

    type TestStorage = BoxedSkipStorage<u64, u64, u32, 12>;
    type TestSkipList = SkipList<u64, u64, TestStorage, u32, SmallRng, 12>;

    const WARMUP: usize = 10_000;
    const ITERATIONS: usize = 100_000;

    fn make_rng(seed: u64) -> SmallRng {
        SmallRng::seed_from_u64(seed)
    }

    // ========================================================================
    // Insert benchmarks
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_insert_sequential() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(ITERATIONS + WARMUP);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for i in 0..WARMUP as u64 {
            let _ = list.try_insert(&mut storage, i, i);
        }
        list.clear(&mut storage);

        // Measure
        for i in 0..ITERATIONS as u64 {
            let start = rdtscp();
            let _ = list.try_insert(&mut storage, i, i);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("insert_sequential", &hist);
    }

    #[test]
    #[ignore]
    fn bench_insert_random() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(ITERATIONS + WARMUP);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut rng = make_rng(99999);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Pre-generate keys
        let keys: Vec<u64> = (0..ITERATIONS)
            .map(|_| rng.random_range(0..1_000_000))
            .collect();

        // Warmup
        for i in 0..WARMUP {
            let _ = list.try_insert(&mut storage, keys[i % keys.len()] + 1_000_000, 0);
        }
        list.clear(&mut storage);

        // Measure
        for key in &keys {
            let start = rdtscp();
            let _ = list.try_insert(&mut storage, *key, *key);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("insert_random", &hist);
    }

    #[test]
    #[ignore]
    fn bench_insert_reverse() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(ITERATIONS + WARMUP);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for i in (0..WARMUP as u64).rev() {
            let _ = list.try_insert(&mut storage, i + ITERATIONS as u64, i);
        }
        list.clear(&mut storage);

        // Measure - insert in reverse order
        for i in (0..ITERATIONS as u64).rev() {
            let start = rdtscp();
            let _ = list.try_insert(&mut storage, i, i);
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("insert_reverse", &hist);
    }

    // ========================================================================
    // Lookup benchmarks
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_get_hit() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10_000);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut rng = make_rng(99999);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Fill with known keys
        for i in 0..10_000u64 {
            let _ = list.try_insert(&mut storage, i * 2, i);
        }

        // Pre-generate lookup keys (all hits)
        let keys: Vec<u64> = (0..ITERATIONS)
            .map(|_| rng.random_range(0..10_000u64) * 2)
            .collect();

        // Warmup
        for key in keys.iter().take(WARMUP) {
            std::hint::black_box(list.get(&storage, key));
        }

        // Measure
        for key in &keys {
            let start = rdtscp();
            std::hint::black_box(list.get(&storage, key));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("get_hit", &hist);
    }

    #[test]
    #[ignore]
    fn bench_get_miss() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10_000);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut rng = make_rng(99999);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Fill with even keys
        for i in 0..10_000u64 {
            let _ = list.try_insert(&mut storage, i * 2, i);
        }

        // Pre-generate lookup keys (all misses - odd keys)
        let keys: Vec<u64> = (0..ITERATIONS)
            .map(|_| rng.random_range(0..10_000u64) * 2 + 1)
            .collect();

        // Warmup
        for key in keys.iter().take(WARMUP) {
            std::hint::black_box(list.get(&storage, key));
        }

        // Measure
        for key in &keys {
            let start = rdtscp();
            std::hint::black_box(list.get(&storage, key));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("get_miss", &hist);
    }

    // ========================================================================
    // Remove benchmarks
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_remove_random() {
        let mut hist = Histogram::<u64>::new(3).unwrap();
        let mut rng = make_rng(99999);

        // Run multiple rounds since we deplete the list
        for round in 0..10 {
            let mut storage: TestStorage = BoxedSkipStorage::with_capacity(ITERATIONS / 10 + 100);
            let mut list: TestSkipList = SkipList::new(make_rng(12345 + round));

            // Fill
            let mut keys: Vec<u64> = (0..ITERATIONS as u64 / 10).collect();
            for &k in &keys {
                let _ = list.try_insert(&mut storage, k, k);
            }

            // Shuffle for random removal order
            for i in (1..keys.len()).rev() {
                let j = rng.random_range(0..=i);
                keys.swap(i, j);
            }

            // Measure removes
            for key in &keys {
                let start = rdtscp();
                std::hint::black_box(list.remove(&mut storage, key));
                let elapsed = rdtscp() - start;
                hist.record(elapsed).unwrap();
            }
        }

        print_histogram("remove_random", &hist);
    }

    // ========================================================================
    // Pop benchmarks
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_pop_first() {
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for round in 0..10 {
            let mut storage: TestStorage = BoxedSkipStorage::with_capacity(ITERATIONS / 10 + 100);
            let mut list: TestSkipList = SkipList::new(make_rng(12345 + round));

            // Fill
            for i in 0..ITERATIONS as u64 / 10 {
                let _ = list.try_insert(&mut storage, i, i);
            }

            // Measure pop_first
            while !list.is_empty() {
                let start = rdtscp();
                std::hint::black_box(list.pop_first(&mut storage));
                let elapsed = rdtscp() - start;
                hist.record(elapsed).unwrap();
            }
        }

        print_histogram("pop_first", &hist);
    }

    #[test]
    #[ignore]
    fn bench_pop_last() {
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for round in 0..10 {
            let mut storage: TestStorage = BoxedSkipStorage::with_capacity(ITERATIONS / 10 + 100);
            let mut list: TestSkipList = SkipList::new(make_rng(12345 + round));

            // Fill
            for i in 0..ITERATIONS as u64 / 10 {
                let _ = list.try_insert(&mut storage, i, i);
            }

            // Measure pop_last
            while !list.is_empty() {
                let start = rdtscp();
                std::hint::black_box(list.pop_last(&mut storage));
                let elapsed = rdtscp() - start;
                hist.record(elapsed).unwrap();
            }
        }

        print_histogram("pop_last", &hist);
    }

    // ========================================================================
    // Accessor benchmarks
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_first() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10_000);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..10_000u64 {
            let _ = list.try_insert(&mut storage, i, i);
        }

        for _ in 0..WARMUP {
            std::hint::black_box(list.first(&storage));
        }

        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(list.first(&storage));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("first", &hist);
    }

    #[test]
    #[ignore]
    fn bench_last() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(10_000);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..10_000u64 {
            let _ = list.try_insert(&mut storage, i, i);
        }

        for _ in 0..WARMUP {
            std::hint::black_box(list.last(&storage));
        }

        for _ in 0..ITERATIONS {
            let start = rdtscp();
            std::hint::black_box(list.last(&storage));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("last", &hist);
    }

    // ========================================================================
    // Cursor benchmarks
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_cursor_move_next() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(1_000);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for i in 0..1_000u64 {
            let _ = list.try_insert(&mut storage, i, i);
        }

        // Measure individual move_next calls
        for _ in 0..ITERATIONS / 1_000 {
            let mut cursor = list.cursor_front(&mut storage);
            while cursor.current().is_some() {
                let start = rdtscp();
                cursor.move_next();
                let elapsed = rdtscp() - start;
                hist.record(elapsed).unwrap();
            }
        }

        print_histogram("cursor_move_next", &hist);
    }

    #[test]
    #[ignore]
    fn bench_cursor_remove_current() {
        let mut hist = Histogram::<u64>::new(3).unwrap();

        for round in 0..100 {
            let mut storage: TestStorage = BoxedSkipStorage::with_capacity(1_000);
            let mut list: TestSkipList = SkipList::new(make_rng(12345 + round));

            for i in 0..1_000u64 {
                let _ = list.try_insert(&mut storage, i, i);
            }

            let mut cursor = list.cursor_front(&mut storage);
            while cursor.current().is_some() {
                let start = rdtscp();
                std::hint::black_box(cursor.remove_current());
                let elapsed = rdtscp() - start;
                hist.record(elapsed).unwrap();
            }
        }

        print_histogram("cursor_remove_current", &hist);
    }

    // ========================================================================
    // Entry API benchmarks
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_entry_vacant() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(ITERATIONS + WARMUP);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Warmup
        for i in 0..WARMUP as u64 {
            let _ = list
                .entry(&mut storage, i + ITERATIONS as u64)
                .or_try_insert(i);
        }
        list.clear(&mut storage);

        // Measure entry -> or_try_insert (vacant path)
        for i in 0..ITERATIONS as u64 {
            let start = rdtscp();
            std::hint::black_box(list.entry(&mut storage, i).or_try_insert(i));
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("entry_vacant", &hist);
    }

    #[test]
    #[ignore]
    fn bench_entry_occupied() {
        let mut storage: TestStorage = BoxedSkipStorage::with_capacity(1_000);
        let mut list: TestSkipList = SkipList::new(make_rng(12345));
        let mut rng = make_rng(99999);
        let mut hist = Histogram::<u64>::new(3).unwrap();

        // Fill
        for i in 0..1_000u64 {
            let _ = list.try_insert(&mut storage, i, 0);
        }

        // Pre-generate keys
        let keys: Vec<u64> = (0..ITERATIONS)
            .map(|_| rng.random_range(0..1_000))
            .collect();

        // Warmup
        for key in keys.iter().take(WARMUP) {
            let _ = list.entry(&mut storage, *key).and_modify(|v| *v += 1);
        }

        // Measure
        for key in &keys {
            let start = rdtscp();
            std::hint::black_box(
                list.entry(&mut storage, *key)
                    .and_modify(|v| *v += 1)
                    .or_try_insert(0),
            );
            let elapsed = rdtscp() - start;
            hist.record(elapsed).unwrap();
        }

        print_histogram("entry_occupied", &hist);
    }

    // ========================================================================
    // Scaling benchmarks
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_get_scaling() {
        println!("\n--- Get scaling by size ---");

        for size in [100, 1_000, 5_000, 10_000] {
            let mut storage: TestStorage = BoxedSkipStorage::with_capacity(size + 100);
            let mut list: TestSkipList = SkipList::new(make_rng(12345));
            let mut rng = make_rng(99999);
            let mut hist = Histogram::<u64>::new(3).unwrap();

            for i in 0..size as u64 {
                let _ = list.try_insert(&mut storage, i, i);
            }

            let keys: Vec<u64> = (0..ITERATIONS)
                .map(|_| rng.random_range(0..size as u64))
                .collect();

            for key in &keys {
                let start = rdtscp();
                std::hint::black_box(list.get(&storage, key));
                let elapsed = rdtscp() - start;
                hist.record(elapsed).unwrap();
            }

            print_histogram(&format!("get_size_{}", size), &hist);
        }
    }

    #[test]
    #[ignore]
    fn bench_insert_scaling() {
        println!("\n--- Insert scaling by size ---");

        for size in [100, 1_000, 5_000, 10_000] {
            let mut hist = Histogram::<u64>::new(3).unwrap();
            let mut rng = make_rng(99999);

            let keys: Vec<u64> = (0..ITERATIONS / 10)
                .map(|_| rng.random_range(size as u64..size as u64 * 10))
                .collect();

            for round in 0..10 {
                let mut storage: TestStorage =
                    BoxedSkipStorage::with_capacity(size + ITERATIONS / 10 + 100);
                let mut list: TestSkipList = SkipList::new(make_rng(12345 + round as u64));

                for i in 0..size as u64 {
                    let _ = list.try_insert(&mut storage, i, i);
                }

                for key in &keys {
                    let start = rdtscp();
                    let _ = std::hint::black_box(list.try_insert(&mut storage, *key, *key));
                    let elapsed = rdtscp() - start;
                    hist.record(elapsed).unwrap();
                }
            }

            print_histogram(&format!("insert_size_{}", size), &hist);
        }
    }

    // ========================================================================
    // Order book workflow
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_order_book_workflow() {
        let mut hist_insert = Histogram::<u64>::new(3).unwrap();
        let mut hist_get = Histogram::<u64>::new(3).unwrap();
        let mut hist_pop = Histogram::<u64>::new(3).unwrap();

        for round in 0..10 {
            let mut storage: TestStorage = BoxedSkipStorage::with_capacity(1_000);
            let mut list: TestSkipList = SkipList::new(make_rng(12345 + round));
            let mut rng = make_rng(99999 + round);

            // Simulate order book: insert prices, lookup, remove best
            for _ in 0..1_000 {
                let price = rng.random_range(100..200);

                // Insert new price level
                let start = rdtscp();
                let _ = list.try_insert(&mut storage, price, 1);
                hist_insert.record(rdtscp() - start).unwrap();

                // Lookup a price
                let lookup = rng.random_range(100..200);
                let start = rdtscp();
                std::hint::black_box(list.get(&storage, &lookup));
                hist_get.record(rdtscp() - start).unwrap();

                // Remove best (first)
                if !list.is_empty() && rng.random_bool(0.5) {
                    let start = rdtscp();
                    std::hint::black_box(list.pop_first(&mut storage));
                    hist_pop.record(rdtscp() - start).unwrap();
                }
            }
        }

        println!("\n=== Order Book Workflow ===");
        print_histogram("insert_level", &hist_insert);
        print_histogram("get_level", &hist_get);
        print_histogram("pop_best", &hist_pop);
    }

    // ========================================================================
    // Main benchmark runner
    // ========================================================================

    #[test]
    #[ignore]
    fn bench_skiplist_all() {
        println!("\n=== SkipList Benchmarks ===");
        println!(
            "Run with: cargo test --release bench_skiplist::bench_skiplist_all -- --ignored --nocapture\n"
        );

        println!("--- Insert ---");
        bench_insert_sequential();
        bench_insert_random();
        bench_insert_reverse();

        println!("\n--- Lookup ---");
        bench_get_hit();
        bench_get_miss();

        println!("\n--- Remove ---");
        bench_remove_random();

        println!("\n--- Pop ---");
        bench_pop_first();
        bench_pop_last();

        println!("\n--- Accessors ---");
        bench_first();
        bench_last();

        println!("\n--- Cursor ---");
        bench_cursor_move_next();
        bench_cursor_remove_current();

        println!("\n--- Entry API ---");
        bench_entry_vacant();
        bench_entry_occupied();

        bench_get_scaling();
        bench_insert_scaling();
        bench_order_book_workflow();
    }
}
