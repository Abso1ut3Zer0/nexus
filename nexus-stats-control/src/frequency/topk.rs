use alloc::vec::Vec;

/// Space-Saving top-K frequent items over a stream, in bounded memory.
///
/// A table of `capacity` (key, count) pairs sized once at construction and
/// scanned linearly on every update: a tracked key is incremented, a new key
/// takes a free slot, and once the table is full a new key evicts the minimum
/// and inherits its count (the overcount). Nothing allocates after
/// construction and the output is deterministic. Requires `alloc`.
///
/// # Regime
///
/// This is a small-k statistic. `update` costs one scan of the table: about
/// 40 ticks at 100 counters, 140 at 1,000 and 900 at 10,000 on the scaling
/// harness, against about 17 for a hash-map increment. Up to a couple of
/// hundred counters the flat scan is the right trade (no hashing, no
/// allocation, contiguous memory); past that a hash-indexed table is the
/// right structure and this type is the wrong tool. `top` is a query, not an
/// update-path cost: one pass over the table plus a sort or heap of the
/// result.
///
/// # Choosing `capacity`
///
/// `capacity` is the table size, not the k you report. Any count may be
/// overestimated by at most `total / capacity`, so the top k are exact only
/// when the k-th true frequency clears that bound; under Zipf-like traffic
/// that means a capacity of several times k. "Top 25 of 10,000 symbols" is a
/// 100 to 500 counter table, 50 to 110 ns per update.
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
    /// `min(buf.len(), self.len())`.
    ///
    /// One pass over the table, nothing allocated, the table never reordered.
    /// A buffer that covers the whole table is filled and sorted directly
    /// (O(len log len)); a shorter one is filled through a size-n min-heap
    /// kept in `buf` itself (O(len log n)), so a top 25 of a 1,000-counter
    /// table is one scan plus a few dozen sifts. Equal counts come out in a
    /// deterministic but unspecified order. Counts may overestimate; see the
    /// overcount property.
    #[must_use]
    pub fn top(&self, buf: &mut [(K, u64)]) -> usize {
        let len = self.entries.len();
        let n = len.min(buf.len());
        if n == 0 {
            return 0;
        }
        if n == len {
            for (slot, e) in buf[..n].iter_mut().zip(&self.entries) {
                *slot = (e.key.clone(), e.count);
            }
            buf[..n].sort_unstable_by(|a, b| b.1.cmp(&a.1));
            return n;
        }
        // Size-n min-heap in `buf[..n]`: the root is the weakest kept entry,
        // so once the heap is full most table entries fail one compare
        // against `floor` and move on. `floor` is a local because the
        // compiler cannot see that `heap[0]` is unchanged on the reject path.
        let heap = &mut buf[..n];
        let mut filled = 0;
        let mut floor = 0;
        for e in &self.entries {
            if filled < n {
                heap[filled] = (e.key.clone(), e.count);
                filled += 1;
                sift_up(heap, filled - 1);
                if filled == n {
                    floor = heap[0].1;
                }
            } else if e.count > floor {
                heap[0] = (e.key.clone(), e.count);
                sift_down(heap, 0);
                floor = heap[0].1;
            }
        }
        // Heapsort: move the minimum to the end until the slice is descending.
        let mut end = n;
        while end > 1 {
            heap.swap(0, end - 1);
            end -= 1;
            sift_down(&mut heap[..end], 0);
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

/// Min-heap on `.1` (the count): restore the heap property upward from `i`.
fn sift_up<K>(heap: &mut [(K, u64)], mut i: usize) {
    while i > 0 {
        let parent = (i - 1) / 2;
        if heap[i].1 < heap[parent].1 {
            heap.swap(i, parent);
            i = parent;
        } else {
            break;
        }
    }
}

/// Min-heap on `.1` (the count): restore the heap property downward from `i`.
fn sift_down<K>(heap: &mut [(K, u64)], mut i: usize) {
    let len = heap.len();
    loop {
        let left = 2 * i + 1;
        if left >= len {
            break;
        }
        let right = left + 1;
        let child = if right < len && heap[right].1 < heap[left].1 {
            right
        } else {
            left
        };
        if heap[child].1 < heap[i].1 {
            heap.swap(child, i);
            i = child;
        } else {
            break;
        }
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

    /// Equal counts come out in an unspecified but deterministic order: the
    /// same stream gives the same output, on both the sort and the heap path.
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
        let (mut full_a, mut full_b) = ([(0u32, 0u64); 5], [(0u32, 0u64); 5]);
        assert_eq!(a.top(&mut full_a), 5);
        assert_eq!(b.top(&mut full_b), 5);
        assert_eq!(full_a, full_b);
        assert!(full_a.iter().all(|e| e.1 == 1));
        let (mut short_a, mut short_b) = ([(0u32, 0u64); 3], [(0u32, 0u64); 3]);
        assert_eq!(a.top(&mut short_a), 3);
        assert_eq!(b.top(&mut short_b), 3);
        assert_eq!(short_a, short_b);
    }

    /// Every buffer length returns a valid top-n: sorted, unique keys, counts
    /// matching `count_of`, the same count sequence as the head of the full
    /// ranking, and no omitted key with a count above the n-th.
    #[test]
    fn top_every_buffer_length_is_a_valid_top_n() {
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
            // Every shorter buffer is a valid top-n of that ranking (ties at
            // the boundary may pick either key, so compare counts and sets).
            for len in 0..=cap + 2 {
                let mut buf = vec![(0u32, 0u64); len];
                let n = t.top(&mut buf);
                assert_eq!(n, len.min(t.len()));
                let counts = |v: &[(u32, u64)]| v.iter().map(|e| e.1).collect::<Vec<_>>();
                assert_eq!(
                    counts(&buf[..n]),
                    counts(&full[..n]),
                    "seed {seed} len {len}"
                );
                let mut ks: Vec<u32> = buf[..n].iter().map(|e| e.0).collect();
                ks.sort_unstable();
                ks.dedup();
                assert_eq!(ks.len(), n, "seed {seed} len {len}: duplicate key");
                for &(k, c) in &buf[..n] {
                    assert_eq!(c, t.count_of(&k), "seed {seed} len {len}: count for {k}");
                }
                if n > 0 && n < nf {
                    let boundary = buf[n - 1].1;
                    for &(k, c) in &full[..nf] {
                        if c > boundary {
                            assert!(
                                buf[..n].iter().any(|e| e.0 == k),
                                "seed {seed} len {len}: {k} omitted"
                            );
                        }
                    }
                }
            }
        }
    }

    /// The heap path (buffer much shorter than a large table) against a
    /// brute-force ranking of the same table.
    #[test]
    fn top_heap_path_matches_brute_force() {
        use alloc::vec;
        use alloc::vec::Vec;
        let mut t: TopK<u32> = TopK::new(200).unwrap();
        let mut x = 0x2545_F491_4F6C_DD1Du64;
        for _ in 0..20_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            // skewed keys: low keys far more often than high ones
            let key = ((x >> 40) as u32 % 50).min((x >> 20) as u32 % 300);
            t.update(key);
        }
        let mut full = vec![(0u32, 0u64); 200];
        let nf = t.top(&mut full);
        for n in [1usize, 2, 7, 25, 64, 199] {
            let mut buf = vec![(0u32, 0u64); n];
            assert_eq!(t.top(&mut buf), n.min(nf));
            let counts: Vec<u64> = buf[..n.min(nf)].iter().map(|e| e.1).collect();
            let expect: Vec<u64> = full[..n.min(nf)].iter().map(|e| e.1).collect();
            assert_eq!(counts, expect, "n = {n}");
            assert!(buf[..n.min(nf)].windows(2).all(|w| w[0].1 >= w[1].1));
        }
    }
}
