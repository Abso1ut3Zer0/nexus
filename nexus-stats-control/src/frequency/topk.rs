use alloc::vec::Vec;

/// Space-Saving top-K frequent items over a stream, in bounded memory.
///
/// A table of `capacity` (key, count) pairs, sized once at construction and
/// kept sorted by count, highest first. `update` scans for the key from the
/// front, so the hot keys that dominate a skewed stream are found in the first
/// few slots; an increment restores the order with one swap, to the front of
/// the entry's old tie run; a new key on a full table takes the last slot, the
/// minimum, in O(1) and inherits its count plus one (the overcount). Nothing
/// allocates after construction, the output is deterministic, and [`top`] is
/// a view of the table: no copy, no sort, no buffer. Requires `alloc`.
///
/// [`top`]: TopK::top
///
/// # Regime
///
/// This is a small-k statistic. `update` costs one scan of the table (bounded
/// by `capacity`, usually far shorter under skewed traffic), so the flat table
/// is the right trade up to a couple of hundred counters and the wrong tool
/// past that; a hash-indexed table is what a thousands-of-keys tracker needs.
/// See the crate's `topk.md` page for measured costs by table size.
///
/// # Choosing `capacity`
///
/// `capacity` is the table size, not the k you report. Any count may be
/// overestimated by at most `total / capacity`, so the top k are exact only
/// when the k-th true frequency clears that bound; under Zipf-like traffic
/// that means a capacity of several times k. "Top 25 of 10,000 symbols" is a
/// 100 to 500 counter table.
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
pub struct TopK<K: Eq> {
    /// Sorted by `count`, highest first; equal counts in an unspecified but
    /// deterministic order. Every method keeps this invariant.
    entries: Vec<Entry<K>>,
    capacity: usize,
    total: u64,
}

#[derive(Debug, Clone)]
struct Entry<K> {
    key: K,
    count: u64,
}

impl<K: Eq> TopK<K> {
    /// Creates an empty tracker with room for `capacity` keys.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `capacity` is zero.
    #[inline]
    pub fn new(capacity: usize) -> Result<Self, nexus_stats_core::ConfigError> {
        if capacity == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "TopK capacity must be at least 1",
            ));
        }
        Ok(Self {
            entries: Vec::with_capacity(capacity),
            capacity,
            total: 0,
        })
    }

    /// The table size given at construction.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Records one occurrence of `key`.
    ///
    /// One scan from the front of the table (hot keys are found early), then
    /// one swap to keep it sorted. A new key on a full table evicts the last
    /// entry, the minimum, and inherits its count plus one.
    #[inline]
    pub fn update(&mut self, key: K) {
        self.total += 1;
        if let Some(i) = self.entries.iter().position(|e| e.key == key) {
            let old = self.entries[i].count;
            self.entries[i].count += 1;
            self.promote(i, old);
            return;
        }
        if self.entries.len() < self.capacity {
            // Count 1 is the smallest possible, so the end keeps the order.
            self.entries.push(Entry { key, count: 1 });
            return;
        }
        // Table full: the last entry is a minimum. The new key inherits its
        // count plus one (Space-Saving), so it is never under-estimated.
        let last = self.entries.len() - 1;
        let min = self.entries[last].count;
        self.entries[last] = Entry {
            key,
            count: min + 1,
        };
        self.promote(last, min);
    }

    /// Moves the entry at `i`, whose count was `old` before being raised to
    /// `old + 1`, to the front of the `old` tie run with one swap. Everything
    /// left of that run is at least `old + 1`, so the table is sorted again.
    #[inline]
    fn promote(&mut self, i: usize, old: u64) {
        let mut j = i;
        while j > 0 && self.entries[j - 1].count == old {
            j -= 1;
        }
        self.entries.swap(i, j);
    }

    /// The tracked items, highest estimated count first: `top().take(k)` is
    /// the top k.
    ///
    /// A view of the sorted table: nothing is copied or sorted. Equal counts
    /// come out in a deterministic but unspecified order. Counts may
    /// overestimate; see the overcount property.
    #[inline]
    pub fn top(&self) -> impl ExactSizeIterator<Item = (&K, u64)> {
        self.entries.iter().map(|e| (&e.key, e.count))
    }

    /// Estimated count for a specific key. Returns 0 if not tracked.
    #[inline]
    #[must_use]
    pub fn count_of(&self, key: &K) -> u64 {
        self.entries
            .iter()
            .find(|e| e.key == *key)
            .map_or(0, |e| e.count)
    }

    /// Number of keys currently tracked (at most `capacity`).
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether no key has been seen since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Samples processed since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total
    }

    /// Whether at least one key has been counted.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total > 0
    }

    /// Clears all tracked keys and the sample count. Capacity unchanged.
    #[inline]
    pub fn reset(&mut self) {
        self.entries.clear();
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
        assert_eq!(tk.count(), 0);
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
        assert_eq!(tk.count(), 3);
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
        assert_eq!(tk.count(), 6);
    }

    #[test]
    fn top_returns_sorted() {
        let mut tk: TopK<u32> = TopK::new(5).unwrap();
        for _ in 0..5 {
            tk.update(1);
        }
        for _ in 0..3 {
            tk.update(2);
        }
        tk.update(3);
        let ranked: alloc::vec::Vec<(u32, u64)> = tk.top().map(|(k, c)| (*k, c)).collect();
        assert_eq!(ranked, [(1, 5), (2, 3), (3, 1)]);
        assert_eq!(tk.top().len(), 3);
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
        assert_eq!(tk.count(), 0);
        assert_eq!(tk.len(), 0);
        assert!(tk.is_empty());
        assert_eq!(tk.count_of(&1), 0);
    }

    #[test]
    fn string_keys() {
        let mut tk: TopK<&'static str> = TopK::new(3).unwrap();
        for _ in 0..5 {
            tk.update("btc");
        }
        for _ in 0..3 {
            tk.update("eth");
        }
        tk.update("sol");
        assert_eq!(tk.count(), 9);
        assert_eq!(tk.count_of(&"btc"), 5);
        assert_eq!(tk.count_of(&"eth"), 3);
        assert_eq!(tk.count_of(&"sol"), 1);
        assert_eq!(tk.count_of(&"doge"), 0);
    }

    #[test]
    fn top_k_is_a_prefix_of_the_ranking() {
        let mut t: TopK<u32> = TopK::new(10).unwrap();
        for k in 0..5 {
            t.update(k);
        }
        for _ in 0..100 {
            t.update(9);
        }
        for _ in 0..50 {
            t.update(8);
        }
        let top2: alloc::vec::Vec<(u32, u64)> = t.top().take(2).map(|(k, c)| (*k, c)).collect();
        assert_eq!(top2, [(9, 100), (8, 50)]);
    }

    /// Equal counts come out in an unspecified but deterministic order: the
    /// same stream gives the same ranking.
    #[test]
    fn top_is_deterministic_on_ties() {
        let build = || {
            let mut t: TopK<u32> = TopK::new(5).unwrap();
            for k in [7, 3, 5, 9, 1] {
                t.update(k);
            }
            t
        };
        let (a, b) = (build(), build());
        let ra: alloc::vec::Vec<(u32, u64)> = a.top().map(|(k, c)| (*k, c)).collect();
        let rb: alloc::vec::Vec<(u32, u64)> = b.top().map(|(k, c)| (*k, c)).collect();
        assert_eq!(ra, rb);
        assert!(ra.iter().all(|e| e.1 == 1));
    }

    /// The table is sorted after every single update, on streams that fill
    /// the table and evict, and the ranking agrees with `count_of`.
    #[test]
    fn table_is_sorted_after_every_update() {
        use alloc::vec::Vec;
        struct Lcg(u64);
        impl Lcg {
            fn next(&mut self) -> u64 {
                self.0 = self
                    .0
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                self.0 >> 33
            }
        }
        for seed in 1..=60u64 {
            let cap = 1 + (seed as usize % 16);
            let mut t: TopK<u32> = TopK::new(cap).unwrap();
            let mut r = Lcg(seed);
            for step in 0..(r.next() % 400) {
                t.update((r.next() % 40) as u32);
                let counts: Vec<u64> = t.top().map(|(_, c)| c).collect();
                assert!(
                    counts.windows(2).all(|w| w[0] >= w[1]),
                    "seed {seed} step {step}: {counts:?}"
                );
                assert!(t.len() <= cap);
            }
            let ranked: Vec<(u32, u64)> = t.top().map(|(k, c)| (*k, c)).collect();
            assert_eq!(ranked.len(), t.len());
            let mut keys: Vec<u32> = ranked.iter().map(|e| e.0).collect();
            keys.sort_unstable();
            keys.dedup();
            assert_eq!(keys.len(), ranked.len(), "seed {seed}: duplicate key");
            for &(k, c) in &ranked {
                assert_eq!(c, t.count_of(&k), "seed {seed}: count for {k}");
            }
        }
    }

    /// Hot keys end up at the front: the scan for the traffic that dominates
    /// a skewed stream stops in the first slots.
    #[test]
    fn hot_keys_sit_at_the_front() {
        let mut t: TopK<u32> = TopK::new(200).unwrap();
        let mut x = 0x2545_F491_4F6C_DD1Du64;
        for _ in 0..20_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            // Half the traffic on key 0, a quarter on 1, an eighth on 2, the
            // rest spread over 297 cold keys.
            let r = x % 1000;
            let key = if r < 500 {
                0
            } else if r < 750 {
                1
            } else if r < 875 {
                2
            } else {
                3 + ((x >> 20) % 297) as u32
            };
            t.update(key);
        }
        let first: alloc::vec::Vec<u32> = t.top().take(3).map(|(k, _)| *k).collect();
        assert_eq!(first, [0, 1, 2]);
    }
}
