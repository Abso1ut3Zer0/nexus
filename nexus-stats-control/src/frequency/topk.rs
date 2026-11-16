use alloc::boxed::Box;
use alloc::vec::Vec;

/// Space-Saving algorithm for top-K frequent item tracking.
///
/// Tracks the `capacity` most frequent items in a stream with bounded memory:
/// a table sized once at construction, scanned linearly on every update.
/// Efficient for the usual capacities (10 to 100). Requires `alloc`.
///
/// # Use Cases
/// - "What are the top 10 symbols by message volume?"
/// - "Which endpoints get the most traffic?"
/// - Hot key detection
///
/// # Accuracy
///
/// Guaranteed: if an item's true count exceeds `total / capacity`, it will
/// be tracked. Reported counts may overestimate by at most
/// `total / capacity` (the overcount property).
#[derive(Debug, Clone)]
pub struct TopK<K: Eq + Clone> {
    entries: Box<[Option<Entry<K>>]>,
    len: usize,
    total: u64,
}

#[derive(Debug, Clone)]
struct Entry<K> {
    key: K,
    count: u64,
}

impl<K: Eq + Clone> TopK<K> {
    /// Creates an empty tracker with room for `capacity` keys.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `capacity` is zero.
    #[inline]
    pub fn new(capacity: usize) -> Result<Self, nexus_stats_core::ConfigError> {
        if capacity == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "TopK capacity must be > 0",
            ));
        }
        Ok(Self {
            entries: (0..capacity)
                .map(|_| None)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            len: 0,
            total: 0,
        })
    }

    /// Number of keys the table can hold.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.entries.len()
    }

    /// Updates with an observation of the given key.
    ///
    /// If the key is already tracked, increments its count.
    /// If the table is full, evicts the minimum-count entry and replaces
    /// it with this key (count = evicted count + 1, per Space-Saving).
    #[inline]
    pub fn update(&mut self, key: K) {
        self.total += 1;

        // Check if already tracked
        for e in self.entries[..self.len].iter_mut().flatten() {
            if e.key == key {
                e.count += 1;
                return;
            }
        }

        // Not tracked — add if space available
        if self.len < self.entries.len() {
            self.entries[self.len] = Some(Entry { key, count: 1 });
            self.len += 1;
            return;
        }

        // Table full — find minimum and evict
        let mut min_idx = 0;
        let mut min_count = u64::MAX;
        for (i, entry) in self.entries.iter().enumerate() {
            if let Some(e) = entry
                && e.count < min_count
            {
                min_count = e.count;
                min_idx = i;
            }
        }

        // Replace minimum with new key, count = min_count + 1 (Space-Saving property)
        self.entries[min_idx] = Some(Entry {
            key,
            count: min_count + 1,
        });
    }

    /// Returns the tracked items sorted by estimated frequency (descending).
    ///
    /// The returned slice length is `min(capacity, unique keys observed)`.
    /// Counts may overestimate — see the overcount property.
    #[inline]
    pub fn top(&self, buf: &mut [(K, u64)]) -> usize {
        let n = self.len.min(buf.len());

        // Collect entries
        let mut count = 0;
        for e in self.entries[..self.len].iter().flatten() {
            if count < n {
                buf[count] = (e.key.clone(), e.count);
                count += 1;
            }
        }

        // Sort by count descending
        buf[..count].sort_unstable_by(|a, b| b.1.cmp(&a.1));
        count
    }

    /// Estimated count for a specific key. Returns 0 if not tracked.
    #[inline]
    #[must_use]
    pub fn count_of(&self, key: &K) -> u64 {
        for e in self.entries[..self.len].iter().flatten() {
            if e.key == *key {
                return e.count;
            }
        }
        0
    }

    /// Total observations recorded.
    #[inline]
    #[must_use]
    pub fn total(&self) -> u64 {
        self.total
    }

    /// Number of distinct keys currently tracked.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether any keys are tracked.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        for entry in &mut self.entries {
            *entry = None;
        }
        self.len = 0;
        self.total = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_capacity_is_rejected() {
        assert!(TopK::<u32>::new(0).is_err());
    }

    #[test]
    fn empty() {
        let tk: TopK<u32> = TopK::new(5).unwrap();
        assert_eq!(tk.total(), 0);
        assert_eq!(tk.len(), 0);
        assert!(tk.is_empty());
    }

    #[test]
    fn tracks_single_key() {
        let mut tk: TopK<&str> = TopK::new(5).unwrap();
        tk.update("BTC");
        tk.update("BTC");
        tk.update("BTC");

        assert_eq!(tk.count_of(&"BTC"), 3);
        assert_eq!(tk.total(), 3);
    }

    #[test]
    fn tracks_multiple_keys() {
        let mut tk: TopK<&str> = TopK::new(5).unwrap();
        tk.update("BTC");
        tk.update("ETH");
        tk.update("BTC");
        tk.update("SOL");
        tk.update("BTC");
        tk.update("ETH");

        assert_eq!(tk.count_of(&"BTC"), 3);
        assert_eq!(tk.count_of(&"ETH"), 2);
        assert_eq!(tk.count_of(&"SOL"), 1);
        assert_eq!(tk.total(), 6);
    }

    #[test]
    fn top_returns_sorted() {
        let mut tk: TopK<&str> = TopK::new(5).unwrap();
        tk.update("SOL");
        for _ in 0..5 {
            tk.update("BTC");
        }
        for _ in 0..3 {
            tk.update("ETH");
        }

        let mut buf = [("", 0u64); 5];
        let n = tk.top(&mut buf);
        assert_eq!(n, 3);
        assert_eq!(buf[0].0, "BTC");
        assert_eq!(buf[1].0, "ETH");
        assert_eq!(buf[2].0, "SOL");
    }

    #[test]
    fn eviction_replaces_minimum() {
        let mut tk: TopK<u32> = TopK::new(3).unwrap();

        // Fill the table
        tk.update(1); // count=1
        tk.update(2); // count=1
        tk.update(3); // count=1

        // Bump key 1 so it's not the minimum
        tk.update(1); // count=2

        // New key should evict one of the minimums (2 or 3)
        tk.update(4);

        // Key 1 should still be tracked
        assert!(tk.count_of(&1) >= 2);
        // Key 4 should be tracked (with overcount from evicted entry)
        assert!(tk.count_of(&4) >= 1);
        assert_eq!(tk.len(), 3); // still at capacity
    }

    #[test]
    fn overcount_property() {
        // After eviction, the new entry's count is evicted_count + 1
        // This means counts may overestimate but never underestimate
        let mut tk: TopK<u32> = TopK::new(2).unwrap();

        tk.update(1); // count=1
        tk.update(2); // count=1
        // Table full. Evict minimum (count=1), replace with 3 (count=1+1=2)
        tk.update(3);

        // Key 3 has only been observed once, but count should be 2 (overcount)
        assert_eq!(tk.count_of(&3), 2);
    }

    #[test]
    fn unknown_key_returns_zero() {
        let tk: TopK<u32> = TopK::new(5).unwrap();
        assert_eq!(tk.count_of(&42), 0);
    }

    #[test]
    fn reset_clears_all() {
        let mut tk: TopK<u32> = TopK::new(5).unwrap();
        tk.update(1);
        tk.update(2);

        tk.reset();
        assert_eq!(tk.total(), 0);
        assert_eq!(tk.len(), 0);
        assert!(tk.is_empty());
        assert_eq!(tk.count_of(&1), 0);
    }

    #[test]
    fn string_keys() {
        let mut tk: TopK<u64> = TopK::new(10).unwrap();
        for i in 0..100 {
            tk.update(i % 10);
        }
        assert_eq!(tk.total(), 100);
        // Each of the 10 keys should have count 10
        for i in 0..10 {
            assert_eq!(tk.count_of(&i), 10);
        }
    }
}
