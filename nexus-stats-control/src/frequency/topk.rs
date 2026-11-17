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
    entries: Vec<Entry<K>>,
    capacity: usize,
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
            entries: Vec::with_capacity(capacity),
            capacity,
            total: 0,
        })
    }

    /// Number of keys the table can hold.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Updates with an observation of the given key.
    ///
    /// If the key is already tracked, increments its count.
    /// If the table is full, evicts the minimum-count entry and replaces
    /// it with this key (count = evicted count + 1, per Space-Saving).
    #[inline]
    pub fn update(&mut self, key: K) {
        self.total += 1;

        // Already tracked: bump it.
        if let Some(e) = self.entries.iter_mut().find(|e| e.key == key) {
            e.count += 1;
            return;
        }

        // Not tracked: take a free slot while there is one. The table is
        // sized once; `push` never reallocates below `capacity`.
        if self.entries.len() < self.capacity {
            self.entries.push(Entry { key, count: 1 });
            debug_assert!(
                self.entries.len() <= self.capacity,
                "TopK table grew past its bound"
            );
            return;
        }

        // Table full: evict the minimum. The new key inherits its count plus
        // one (Space-Saving property), so it is never under-estimated.
        let mut min_idx = 0;
        let mut min_count = u64::MAX;
        for (i, e) in self.entries.iter().enumerate() {
            if e.count < min_count {
                min_count = e.count;
                min_idx = i;
            }
        }
        self.entries[min_idx] = Entry {
            key,
            count: min_count + 1,
        };
    }

    /// Writes the most frequent tracked items into `buf`, highest estimated
    /// count first, and returns how many were written:
    /// `min(buf.len(), self.len())`. A `buf` shorter than the table receives
    /// the top `buf.len()` items. Equal counts keep insertion order.
    /// Counts may overestimate; see the overcount property.
    #[must_use]
    #[inline]
    pub fn top(&self, buf: &mut [(K, u64)]) -> usize {
        let n = self.entries.len().min(buf.len());
        // Selection, not a sort: `&self` cannot reorder the table and the
        // call must not allocate. Each pass takes the largest entry that
        // ranks below the previous pick in (count desc, index asc) order.
        let mut prev: Option<(u64, usize)> = None;
        for (written, slot) in buf[..n].iter_mut().enumerate() {
            let mut best: Option<(u64, usize)> = None;
            for (i, e) in self.entries.iter().enumerate() {
                let below_prev =
                    prev.is_none_or(|(pc, pi)| e.count < pc || (e.count == pc && i > pi));
                let above_best =
                    best.is_none_or(|(bc, bi)| e.count > bc || (e.count == bc && i < bi));
                if below_prev && above_best {
                    best = Some((e.count, i));
                }
            }
            // `n <= entries.len()` leaves an unpicked entry for every slot.
            let Some((count, i)) = best else {
                return written;
            };
            *slot = (self.entries[i].key.clone(), count);
            prev = best;
        }
        n
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

    /// Number of distinct keys currently tracked.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether any keys are tracked.
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

    /// Resets to empty state.
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
    fn top_into_short_buffer_takes_the_most_frequent() {
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
        let mut buf = [(0u32, 0u64); 2];
        assert_eq!(t.top(&mut buf), 2);
        assert_eq!(buf, [(9, 100), (8, 50)]);
    }

    #[test]
    fn top_keeps_insertion_order_on_ties() {
        let mut t: TopK<u32> = TopK::new(5).unwrap();
        for k in [7, 3, 5] {
            t.update(k);
        }
        let mut buf = [(0u32, 0u64); 3];
        assert_eq!(t.top(&mut buf), 3);
        assert_eq!(buf, [(7, 1), (3, 1), (5, 1)]);
    }

    #[test]
    fn top_every_buffer_length_is_a_prefix_of_the_full_ranking() {
        use alloc::vec;
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
            for _ in 0..(r.next() % 400) {
                t.update((r.next() % 40) as u32);
            }
            // The full ranking, checked independently of `top` itself.
            let mut full = vec![(0u32, 0u64); cap + 3];
            let nf = t.top(&mut full);
            assert_eq!(nf, t.len());
            assert!(full[..nf].windows(2).all(|w| w[0].1 >= w[1].1));
            let mut keys: Vec<u32> = full[..nf].iter().map(|e| e.0).collect();
            keys.sort_unstable();
            keys.dedup();
            assert_eq!(keys.len(), nf, "seed {seed}: duplicate key");
            for &(k, c) in &full[..nf] {
                assert_eq!(c, t.count_of(&k), "seed {seed}: count for {k}");
            }
            // Every shorter buffer gets the head of that ranking.
            for len in 0..=cap + 2 {
                let mut buf = vec![(0u32, 0u64); len];
                let n = t.top(&mut buf);
                assert_eq!(n, len.min(t.len()));
                assert_eq!(&buf[..n], &full[..n], "seed {seed} len {len}");
            }
        }
    }
}
