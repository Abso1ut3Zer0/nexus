//! OwnedSkipList - a skip list that owns its storage.

use rand_core::RngCore;

use crate::skiplist::{BoxedSkipStorage, Cursor, Entry, Iter, IterMut, Keys, SkipList, Values};
use crate::{BoundedStorage, Full, Key};

/// A skip list that owns its storage.
///
/// This is a convenience wrapper around [`SkipList`] + [`BoxedSkipStorage`] for cases
/// where you don't need to share storage across multiple data structures.
///
/// For shared storage scenarios, use [`SkipList`] directly with external storage.
///
/// # Example
///
/// ```
/// use nexus_collections::OwnedSkipList;
/// use rand::rngs::SmallRng;
/// use rand::SeedableRng;
///
/// let rng = SmallRng::seed_from_u64(12345);
/// let mut map: OwnedSkipList<u64, String, _, 16> = OwnedSkipList::with_capacity(rng, 100);
///
/// map.try_insert(100, "first".into()).unwrap();
/// map.try_insert(50, "second".into()).unwrap();
///
/// assert_eq!(map.get(&50), Some(&"second".into()));
/// assert_eq!(map.first(), Some((&50, &"second".into())));
///
/// // Iterate in sorted order
/// let keys: Vec<_> = map.keys().copied().collect();
/// assert_eq!(keys, vec![50, 100]);
/// ```
pub struct OwnedSkipList<K, V, R, const MAX_LEVEL: usize = 16, Idx: Key = u32>
where
    K: Ord,
    R: RngCore,
{
    storage: BoxedSkipStorage<K, V, Idx, MAX_LEVEL>,
    list: SkipList<K, V, BoxedSkipStorage<K, V, Idx, MAX_LEVEL>, Idx, R, MAX_LEVEL>,
}

impl<K, V, R, const MAX_LEVEL: usize, Idx: Key> OwnedSkipList<K, V, R, MAX_LEVEL, Idx>
where
    K: Ord,
    R: RngCore,
{
    /// Creates a new skip list with the given RNG and capacity.
    ///
    /// Capacity is rounded up to the next power of 2.
    pub fn with_capacity(rng: R, capacity: usize) -> Self {
        Self {
            storage: BoxedSkipStorage::with_capacity(capacity),
            list: SkipList::new(rng),
        }
    }

    /// Creates a new skip list with custom level ratio.
    ///
    /// `level_ratio` controls memory vs search speed tradeoff:
    /// - 2: Standard (p=0.5), ~2 pointers per node average
    /// - 4: Redis-style (p=0.25), ~1.33 pointers per node average
    pub fn with_capacity_and_ratio(rng: R, capacity: usize, level_ratio: u32) -> Self {
        Self {
            storage: BoxedSkipStorage::with_capacity(capacity),
            list: SkipList::with_level_ratio(rng, level_ratio),
        }
    }

    /// Returns the number of elements in the skip list.
    #[inline]
    pub fn len(&self) -> usize {
        self.list.len()
    }

    /// Returns `true` if the skip list is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    /// Returns the storage capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.capacity()
    }

    /// Returns `true` if the skip list contains the given key.
    #[inline]
    pub fn contains_key(&self, key: &K) -> bool {
        self.list.contains_key(&self.storage, key)
    }

    // ========================================================================
    // Access
    // ========================================================================

    /// Returns a reference to the value for the given key, or `None` if not found.
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        self.list.get(&self.storage, key)
    }

    /// Returns a mutable reference to the value for the given key, or `None` if not found.
    #[inline]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self.list.get_mut(&mut self.storage, key)
    }

    /// Returns the first (smallest) key-value pair, or `None` if empty.
    #[inline]
    pub fn first(&self) -> Option<(&K, &V)> {
        self.list.first(&self.storage)
    }

    /// Returns a mutable reference to the first (smallest) key-value pair.
    #[inline]
    pub fn first_mut(&mut self) -> Option<(&K, &mut V)> {
        self.list.first_mut(&mut self.storage)
    }

    /// Returns the last (largest) key-value pair, or `None` if empty.
    #[inline]
    pub fn last(&self) -> Option<(&K, &V)> {
        self.list.last(&self.storage)
    }

    /// Returns a mutable reference to the last (largest) key-value pair.
    #[inline]
    pub fn last_mut(&mut self) -> Option<(&K, &mut V)> {
        self.list.last_mut(&mut self.storage)
    }

    // ========================================================================
    // Insert
    // ========================================================================

    /// Tries to insert a key-value pair, returning an error if storage is full.
    ///
    /// If the key already exists, the value is updated and the old value is returned.
    #[inline]
    pub fn try_insert(&mut self, key: K, value: V) -> Result<Option<V>, Full<(K, V)>> {
        self.list.try_insert(&mut self.storage, key, value)
    }

    // ========================================================================
    // Remove
    // ========================================================================

    /// Removes the entry for the given key and returns the value, or `None` if not found.
    #[inline]
    pub fn remove(&mut self, key: &K) -> Option<V> {
        self.list.remove(&mut self.storage, key)
    }

    /// Removes the first (smallest) key-value pair and returns it.
    #[inline]
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        self.list.pop_first(&mut self.storage)
    }

    /// Removes the last (largest) key-value pair and returns it.
    ///
    /// This is O(log n) as we need to search for predecessors.
    #[inline]
    pub fn pop_last(&mut self) -> Option<(K, V)>
    where
        K: Clone,
    {
        self.list.pop_last(&mut self.storage)
    }

    /// Removes all elements from the skip list.
    pub fn clear(&mut self) {
        self.list.clear(&mut self.storage);
        self.storage.clear();
    }

    // ========================================================================
    // Entry API
    // ========================================================================

    /// Gets the entry for the given key.
    #[inline]
    pub fn entry(
        &mut self,
        key: K,
    ) -> Entry<'_, K, V, BoxedSkipStorage<K, V, Idx, MAX_LEVEL>, Idx, R, MAX_LEVEL> {
        self.list.entry(&mut self.storage, key)
    }

    // ========================================================================
    // Iteration
    // ========================================================================

    /// Returns an iterator over key-value pairs in sorted order.
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V, BoxedSkipStorage<K, V, Idx, MAX_LEVEL>, Idx, MAX_LEVEL> {
        self.list.iter(&self.storage)
    }

    /// Returns a mutable iterator over key-value pairs in sorted order.
    #[inline]
    pub fn iter_mut(
        &mut self,
    ) -> IterMut<'_, K, V, BoxedSkipStorage<K, V, Idx, MAX_LEVEL>, Idx, MAX_LEVEL> {
        self.list.iter_mut(&mut self.storage)
    }

    /// Returns an iterator over keys in sorted order.
    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V, BoxedSkipStorage<K, V, Idx, MAX_LEVEL>, Idx, MAX_LEVEL> {
        self.list.keys(&self.storage)
    }

    /// Returns an iterator over values in sorted order by key.
    #[inline]
    pub fn values(
        &self,
    ) -> Values<'_, K, V, BoxedSkipStorage<K, V, Idx, MAX_LEVEL>, Idx, MAX_LEVEL> {
        self.list.values(&self.storage)
    }

    /// Returns a cursor starting at the first element.
    #[inline]
    pub fn cursor_front(
        &mut self,
    ) -> Cursor<'_, K, V, BoxedSkipStorage<K, V, Idx, MAX_LEVEL>, Idx, R, MAX_LEVEL> {
        self.list.cursor_front(&mut self.storage)
    }

    /// Returns a cursor starting at the given key, or at the first element greater than key.
    #[inline]
    pub fn cursor_at(
        &mut self,
        key: &K,
    ) -> Cursor<'_, K, V, BoxedSkipStorage<K, V, Idx, MAX_LEVEL>, Idx, R, MAX_LEVEL> {
        self.list.cursor_at(&mut self.storage, key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    fn make_rng() -> SmallRng {
        SmallRng::seed_from_u64(12345)
    }

    #[test]
    fn new_is_empty() {
        let list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(list.first(), None);
        assert_eq!(list.last(), None);
    }

    #[test]
    fn insert_and_get() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(100, "hello".into()).unwrap();
        list.try_insert(50, "world".into()).unwrap();

        assert_eq!(list.len(), 2);
        assert_eq!(list.get(&100), Some(&"hello".into()));
        assert_eq!(list.get(&50), Some(&"world".into()));
        assert_eq!(list.get(&999), None);
    }

    #[test]
    fn insert_updates_existing() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(100, "first".into()).unwrap();
        let old = list.try_insert(100, "second".into()).unwrap();

        assert_eq!(old, Some("first".into()));
        assert_eq!(list.len(), 1);
        assert_eq!(list.get(&100), Some(&"second".into()));
    }

    #[test]
    fn maintains_sorted_order() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(50, "fifty".into()).unwrap();
        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(90, "ninety".into()).unwrap();
        list.try_insert(30, "thirty".into()).unwrap();

        let keys: Vec<_> = list.keys().copied().collect();
        assert_eq!(keys, vec![10, 30, 50, 90]);

        assert_eq!(list.first(), Some((&10, &"ten".into())));
        assert_eq!(list.last(), Some((&90, &"ninety".into())));
    }

    #[test]
    fn remove() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();
        list.try_insert(30, "thirty".into()).unwrap();

        let removed = list.remove(&20);
        assert_eq!(removed, Some("twenty".into()));
        assert_eq!(list.len(), 2);

        let keys: Vec<_> = list.keys().copied().collect();
        assert_eq!(keys, vec![10, 30]);
    }

    #[test]
    fn pop_first_and_last() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();
        list.try_insert(30, "thirty".into()).unwrap();

        assert_eq!(list.pop_first(), Some((10, "ten".into())));
        assert_eq!(list.pop_last(), Some((30, "thirty".into())));
        assert_eq!(list.len(), 1);
        assert_eq!(list.first(), Some((&20, &"twenty".into())));
    }

    #[test]
    fn clear() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();

        list.clear();

        assert!(list.is_empty());
        assert_eq!(list.first(), None);
    }

    #[test]
    fn get_mut() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(100, "hello".into()).unwrap();

        if let Some(v) = list.get_mut(&100) {
            *v = "world".into();
        }

        assert_eq!(list.get(&100), Some(&"world".into()));
    }

    #[test]
    fn first_mut_and_last_mut() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();

        if let Some((_, v)) = list.first_mut() {
            *v = "TEN".into();
        }
        if let Some((_, v)) = list.last_mut() {
            *v = "TWENTY".into();
        }

        assert_eq!(list.get(&10), Some(&"TEN".into()));
        assert_eq!(list.get(&20), Some(&"TWENTY".into()));
    }

    #[test]
    fn contains_key() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(100, "hello".into()).unwrap();

        assert!(list.contains_key(&100));
        assert!(!list.contains_key(&999));
    }

    #[test]
    fn iter() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(30, "thirty".into()).unwrap();
        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();

        let pairs: Vec<_> = list.iter().map(|(k, v)| (*k, v.clone())).collect();
        assert_eq!(
            pairs,
            vec![
                (10, "ten".into()),
                (20, "twenty".into()),
                (30, "thirty".into())
            ]
        );
    }

    #[test]
    fn iter_mut() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(10, "a".into()).unwrap();
        list.try_insert(20, "b".into()).unwrap();

        for (_, v) in list.iter_mut() {
            v.push_str("_modified");
        }

        assert_eq!(list.get(&10), Some(&"a_modified".into()));
        assert_eq!(list.get(&20), Some(&"b_modified".into()));
    }

    #[test]
    fn keys_and_values() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();

        let keys: Vec<_> = list.keys().copied().collect();
        let values: Vec<_> = list.values().cloned().collect();

        assert_eq!(keys, vec![10, 20]);
        assert_eq!(values, vec!["ten".to_string(), "twenty".to_string()]);
    }

    #[test]
    fn entry_api() {
        let mut list: OwnedSkipList<u64, u64, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        // Vacant insert
        list.entry(100).or_try_insert(1);
        assert_eq!(list.get(&100), Some(&1));

        // Occupied modify
        list.entry(100).and_modify(|v| *v += 10);
        assert_eq!(list.get(&100), Some(&11));
    }

    #[test]
    fn cursor_traverse() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();
        list.try_insert(30, "thirty".into()).unwrap();

        let mut cursor = list.cursor_front();
        let mut keys = Vec::new();

        while let Some((k, _)) = cursor.current() {
            keys.push(*k);
            cursor.move_next();
        }

        assert_eq!(keys, vec![10, 20, 30]);
    }

    #[test]
    fn cursor_remove() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 16);

        for i in 1..=6 {
            list.try_insert(i, format!("val{}", i)).unwrap();
        }

        // Remove even keys via cursor
        let mut cursor = list.cursor_front();
        while let Some((k, _)) = cursor.current() {
            if k % 2 == 0 {
                cursor.remove_current();
            } else {
                cursor.move_next();
            }
        }

        drop(cursor);

        let keys: Vec<_> = list.keys().copied().collect();
        assert_eq!(keys, vec![1, 3, 5]);
    }

    #[test]
    fn storage_full() {
        let mut list: OwnedSkipList<u64, String, _> = OwnedSkipList::with_capacity(make_rng(), 2);

        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();

        let result = list.try_insert(30, "thirty".into());
        assert!(result.is_err());

        if let Err(Full((k, v))) = result {
            assert_eq!(k, 30);
            assert_eq!(v, "thirty".to_string());
        }
    }

    #[test]
    fn with_level_ratio() {
        let mut list: OwnedSkipList<u64, String, _> =
            OwnedSkipList::with_capacity_and_ratio(make_rng(), 16, 4);

        list.try_insert(10, "ten".into()).unwrap();
        list.try_insert(20, "twenty".into()).unwrap();

        assert_eq!(list.len(), 2);
    }
}
