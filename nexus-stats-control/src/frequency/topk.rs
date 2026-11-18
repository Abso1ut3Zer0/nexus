use alloc::vec;
use alloc::vec::Vec;
use core::hash::{Hash, Hasher};

/// Space-Saving top-k frequent items over a stream, in bounded memory.
///
/// Built for market-data observability: which of thousands of symbols are the
/// busiest right now, answered from a per-message `update` that never
/// allocates, in a table whose size you choose up front. The algorithm is
/// Space-Saving (Metwally, Agrawal and El Abbadi, "Efficient Computation of
/// Frequent and Top-k Elements in Data Streams", ICDT 2005), the deterministic
/// counter-based heavy-hitters sketch that the Cormode and Hadjieleftheriou
/// survey ("Finding Frequent Items in Data Streams", VLDB 2008) found most
/// accurate per byte, and the one behind ClickHouse's `topK` and Algebird's
/// `SpaceSaver`.
///
/// # How it works
///
/// `capacity` counters, each `(key, count, error)`. A tracked key is
/// incremented. A new key on a full table takes the slot of the minimum
/// counter and inherits its count plus one; that inherited count is the
/// entry's `error`, the amount by which its `count` may overstate the truth.
/// So the bottom of the table is a revolving door through which every symbol
/// can enter, the top is where the symbols that keep arriving settle, and a
/// symbol seen more than `total / capacity` times can never be kept out.
///
/// The structure is the paper's Stream-Summary flattened: the counters live
/// in one array kept sorted by count, so an increment restores the order with
/// a single swap to the front of the entry's old tie run and the minimum is
/// always the last slot, and a fixed-size hash index (open addressing, a
/// deterministic hasher) finds a key's slot without scanning. `update` is
/// therefore O(1) expected, independent of `capacity` and of how many distinct
/// keys flow through; nothing is allocated after construction, and the output
/// is deterministic for a given stream.
///
/// # Reading the output
///
/// [`top`](Self::top) is a view of the sorted array: an iterator of
/// [`Counter`]s, highest count first, nothing copied or sorted;
/// `top().take(k)` is the top k. Each counter carries its `error`, so
/// `count - error` is the count that is guaranteed. [`guaranteed_top`](Self::guaranteed_top)
/// is the number of leading ranks whose order is provably exact (the paper's
/// test: a rank's guaranteed count is at least the next rank's count); print
/// that many with confidence, treat the rest as approximate. Equal counts come
/// out in a deterministic but unspecified order.
///
/// # Choosing `capacity`
///
/// `capacity` is the table size, not the k you report. Any count may be
/// overstated by at most `total / capacity`, so the top k are exact only when
/// the k-th true frequency clears that bound; under Zipf-like traffic that
/// means a capacity of several times k. "Top 25 of 10,000 symbols" is a 100 to
/// 500 counter table, a few kilobytes.
///
/// Requires `alloc`. Keys need `Eq + Hash`; for string keys on a hot path
/// prefer a fixed-size ASCII string type with a precomputed hash over `String`.
#[derive(Debug, Clone)]
pub struct TopK<K: Eq + Hash> {
    /// Sorted by `count`, highest first; equal counts in an unspecified but
    /// deterministic order. Every method keeps this invariant.
    entries: Vec<Entry<K>>,
    /// Open-addressing index: each cell is a slot in `entries` (or `EMPTY`)
    /// and the low 32 bits of that entry's hash, so probing and deletion
    /// never touch `entries`. Power-of-two length, at most half full. Empty
    /// for tables of `SCAN_MAX` counters or fewer, which are scanned instead:
    /// at that size the scan beats the hashing.
    cells: Vec<Cell>,
    /// First slot of the run of entries tied at the minimum count (the last
    /// slot's count); `entries.len()` when the table is empty. Every eviction
    /// lands in that run, so its start is kept rather than searched.
    min_run_start: usize,
    capacity: usize,
    total: u64,
}

/// One ranked item from [`TopK::top`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Counter<'a, K> {
    /// The tracked key.
    pub key: &'a K,
    /// Estimated count: an upper bound on the true count.
    pub count: u64,
    /// The count this entry inherited when it entered the table: the most
    /// its `count` can overstate the truth.
    pub error: u64,
}

impl<K> Counter<'_, K> {
    /// The count that is guaranteed: `count - error`.
    #[inline]
    #[must_use]
    pub fn guaranteed(&self) -> u64 {
        self.count - self.error
    }
}

#[derive(Debug, Clone)]
struct Entry<K> {
    key: K,
    count: u64,
    error: u64,
    /// Low 32 bits of the key's hash: a cheap pre-compare before `key ==`,
    /// and the index's home cell is `tag & mask`.
    tag: u32,
    /// Index of this entry's cell in `cells`, so a swap updates the index
    /// without rehashing; `EMPTY` for a scanned table.
    cell: u32,
}

#[derive(Debug, Clone, Copy)]
struct Cell {
    slot: u32,
    /// The entry's tag: the home cell is `tag & mask`, and a tag mismatch
    /// rejects a probe without loading the entry.
    tag: u32,
}

const EMPTY: u32 = u32::MAX;
const EMPTY_CELL: Cell = Cell {
    slot: EMPTY,
    tag: 0,
};

/// Tables this small are scanned rather than hash-indexed: measured, a scan
/// of 16 counters costs less than a probe, a backward-shift deletion and a
/// second probe, and the index earns its keep from a few dozen counters up.
const SCAN_MAX: usize = 32;

impl<K: Eq + Hash> TopK<K> {
    /// Creates an empty tracker with room for `capacity` keys.
    ///
    /// One allocation for the counters and one for the index; nothing is
    /// allocated afterwards.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `capacity` is zero or above `2^30`.
    pub fn new(capacity: usize) -> Result<Self, nexus_stats_core::ConfigError> {
        if capacity == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "TopK capacity must be at least 1",
            ));
        }
        if capacity > (1 << 30) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "TopK capacity must be at most 2^30",
            ));
        }
        // At most half full: expected probe length stays near one.
        let cells = if capacity <= SCAN_MAX {
            0
        } else {
            (capacity * 2).next_power_of_two()
        };
        Ok(Self {
            entries: Vec::with_capacity(capacity),
            cells: vec![EMPTY_CELL; cells],
            min_run_start: 0,
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
    /// One hash lookup, one increment and one swap for a tracked key; for a
    /// new key on a full table, the eviction of the last slot (the minimum)
    /// and two index updates. O(1) expected, whatever the capacity.
    #[inline]
    pub fn update(&mut self, key: K) {
        self.total += 1;
        let tag = tag_of(&key);
        if let Some(i) = self.find(tag, &key) {
            let old = self.entries[i].count;
            self.entries[i].count += 1;
            self.promote(i, old);
            return;
        }
        if self.entries.len() < self.capacity {
            // Count 1 is the smallest possible, so the end keeps the order;
            // it extends the minimum run if that run is already at count 1
            // and starts a new one otherwise.
            let slot = self.entries.len();
            if self.entries.last().is_none_or(|e| e.count != 1) {
                self.min_run_start = slot;
            }
            let cell = self.index_insert(tag, slot);
            self.entries.push(Entry {
                key,
                count: 1,
                error: 0,
                tag,
                cell,
            });
            return;
        }
        // Table full: the last entry is a minimum. The new key inherits its
        // count plus one and records that count as its error.
        let last = self.entries.len() - 1;
        let min = self.entries[last].count;
        if !self.cells.is_empty() {
            self.remove_cell(self.entries[last].cell as usize);
        }
        let cell = self.index_insert(tag, last);
        self.entries[last] = Entry {
            key,
            count: min + 1,
            error: min,
            tag,
            cell,
        };
        self.promote(last, min);
    }

    /// The tracked items, highest estimated count first: `top().take(k)` is
    /// the top k.
    ///
    /// A view of the sorted table: nothing is copied or sorted. Each
    /// [`Counter`] carries its `error`; see [`guaranteed_top`](Self::guaranteed_top)
    /// for how many leading ranks are provably in the right order.
    #[inline]
    pub fn top(&self) -> impl ExactSizeIterator<Item = Counter<'_, K>> {
        self.entries.iter().map(|e| Counter {
            key: &e.key,
            count: e.count,
            error: e.error,
        })
    }

    /// Number of leading ranks of [`top`](Self::top) whose order is provably
    /// exact: for each of them, the guaranteed count (`count - error`) is at
    /// least the next rank's count, so no reordering is consistent with the
    /// error bounds. Ranks beyond it are within their error bounds but may be
    /// misordered among themselves.
    #[must_use]
    pub fn guaranteed_top(&self) -> usize {
        let n = self.entries.len();
        let mut k = 0;
        while k + 1 < n {
            let e = &self.entries[k];
            if e.count - e.error >= self.entries[k + 1].count {
                k += 1;
            } else {
                return k;
            }
        }
        n
    }

    /// Estimated count for a specific key (an upper bound), or 0 if not
    /// tracked. One hash lookup.
    #[inline]
    #[must_use]
    pub fn count_of(&self, key: &K) -> u64 {
        self.find(tag_of(key), key)
            .map_or(0, |i| self.entries[i].count)
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

    /// Clears all tracked keys and the sample count. Capacity unchanged, no
    /// allocation.
    pub fn reset(&mut self) {
        self.entries.clear();
        self.cells.fill(EMPTY_CELL);
        self.min_run_start = 0;
        self.total = 0;
    }

    /// Slot of `key`: a scan of the sorted array for a small table (hot keys
    /// are at the front), otherwise the probe sequence until an empty cell.
    #[inline]
    fn find(&self, tag: u32, key: &K) -> Option<usize> {
        if self.cells.is_empty() {
            return self
                .entries
                .iter()
                .position(|e| e.tag == tag && e.key == *key);
        }
        let mask = self.cells.len() - 1;
        let mut c = (tag as usize) & mask;
        loop {
            let cell = self.cells[c];
            if cell.slot == EMPTY {
                return None;
            }
            if cell.tag == tag && self.entries[cell.slot as usize].key == *key {
                return Some(cell.slot as usize);
            }
            c = (c + 1) & mask;
        }
    }

    /// Records `slot` under `hash` in the index and returns its cell, or
    /// `EMPTY` for a scanned table. The index is never more than half full,
    /// so an empty cell exists on every probe sequence.
    #[inline]
    fn index_insert(&mut self, tag: u32, slot: usize) -> u32 {
        if self.cells.is_empty() {
            return EMPTY;
        }
        let mask = self.cells.len() - 1;
        let mut c = (tag as usize) & mask;
        while self.cells[c].slot != EMPTY {
            c = (c + 1) & mask;
        }
        self.cells[c] = Cell {
            slot: slot as u32,
            tag,
        };
        c as u32
    }

    /// Empties cell `c`, shifting later cells of the same probe run back so
    /// every remaining key stays reachable from its home cell (Knuth's
    /// Algorithm R; no tombstones, so churn never degrades the index).
    #[inline]
    fn remove_cell(&mut self, c: usize) {
        let mask = self.cells.len() - 1;
        let mut i = c;
        let mut j = c;
        loop {
            j = (j + 1) & mask;
            let cell = self.cells[j];
            if cell.slot == EMPTY {
                break;
            }
            let home = (cell.tag as usize) & mask;
            // An entry whose home lies cyclically in (i, j] never probed
            // through `i`; it stays. Otherwise it moves into the hole.
            let stays = if i <= j {
                i < home && home <= j
            } else {
                i < home || home <= j
            };
            if stays {
                continue;
            }
            self.cells[i] = cell;
            self.entries[cell.slot as usize].cell = i as u32;
            i = j;
        }
        self.cells[i] = EMPTY_CELL;
    }

    /// Moves the entry at `i`, whose count was `old` before being raised to
    /// `old + 1`, to the front of the `old` tie run with one swap. Everything
    /// left of that run is at least `old + 1`, so the table is sorted again.
    ///
    /// The run tied at the minimum, where every eviction and every repeat of
    /// a cold key lands, can span most of the table; its start is kept in
    /// `min_run_start`. Any other run belongs to a key with a distinct or
    /// nearly distinct count, so a short walk finds its start, with a binary
    /// search on the sorted counts as the fallback.
    #[inline]
    fn promote(&mut self, i: usize, old: u64) {
        let last = self.entries.len() - 1;
        let j = if old == self.entries[last].count || i == last {
            // `i == last` with a raised count: the last slot was the minimum.
            let j = self.min_run_start;
            self.min_run_start += 1;
            if self.min_run_start > last {
                // The minimum run is exhausted; the new minimum is `old + 1`
                // and its run ends at the last slot (rare: once per count
                // level, not per update).
                let new_min = old + 1;
                self.min_run_start = self.entries.partition_point(|e| e.count > new_min);
            }
            j
        } else {
            let mut j = i;
            let mut steps = 0;
            while j > 0 && self.entries[j - 1].count == old {
                j -= 1;
                steps += 1;
                if steps == 8 {
                    j = self.entries[..j].partition_point(|e| e.count > old);
                    break;
                }
            }
            j
        };
        if j != i {
            self.entries.swap(i, j);
            if !self.cells.is_empty() {
                self.cells[self.entries[i].cell as usize].slot = i as u32;
                self.cells[self.entries[j].cell as usize].slot = j as u32;
            }
        }
    }
}

/// Fx hash (rustc's hasher): a multiply-rotate per word, deterministic across
/// runs and builds, which is all the index needs since the output order comes
/// from the sorted array, never from the index.
#[derive(Default)]
struct FxHasher {
    hash: u64,
}

const FX_SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(FX_SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.add(u64::from_le_bytes(c.try_into().expect("8-byte chunk")));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut buf = [0u8; 8];
            buf[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(buf));
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(u64::from(i));
    }
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(u64::from(i));
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(u64::from(i));
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

/// Low 32 bits of the key's Fx hash: enough to index a table of up to 2^30
/// counters and to pre-filter key comparisons; a false tag match costs one
/// extra `==`.
#[inline]
fn tag_of<K: Hash>(key: &K) -> u32 {
    let mut h = FxHasher::default();
    key.hash(&mut h);
    h.finish() as u32
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    fn ranked(t: &TopK<u32>) -> Vec<(u32, u64)> {
        t.top().map(|c| (*c.key, c.count)).collect()
    }

    /// Every structural invariant: sorted by count, the minimum run start,
    /// index and entries pointing at each other (indexed tables), every
    /// tracked key found, `count_of` agreeing.
    fn check_invariants(t: &TopK<u32>) {
        let counts: Vec<u64> = t.entries.iter().map(|e| e.count).collect();
        assert!(
            counts.windows(2).all(|w| w[0] >= w[1]),
            "unsorted: {counts:?}"
        );
        assert!(t.entries.len() <= t.capacity);
        let expected_run = t.entries.last().map_or(0, |last| {
            t.entries.partition_point(|e| e.count > last.count)
        });
        assert_eq!(t.min_run_start, expected_run, "min run start: {counts:?}");
        if t.cells.is_empty() {
            assert!(t.capacity <= SCAN_MAX);
        } else {
            let occupied = t.cells.iter().filter(|c| c.slot != EMPTY).count();
            assert_eq!(occupied, t.entries.len(), "index/entries size mismatch");
            for (slot, e) in t.entries.iter().enumerate() {
                let c = t.cells[e.cell as usize];
                assert_eq!(c.slot, slot as u32, "cell does not point back");
                assert_eq!(c.tag, e.tag, "cell tag");
            }
        }
        for (slot, e) in t.entries.iter().enumerate() {
            assert_eq!(t.find(e.tag, &e.key), Some(slot), "key {} not found", e.key);
            assert!(e.error <= e.count);
            assert_eq!(t.count_of(&e.key), e.count);
        }
    }

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

    #[test]
    fn zero_capacity_is_rejected() {
        assert!(TopK::<u32>::new(0).is_err());
        assert!(TopK::<u32>::new(1).is_ok());
    }

    #[test]
    fn empty() {
        let tk: TopK<u32> = TopK::new(10).unwrap();
        assert_eq!(tk.len(), 0);
        assert!(tk.is_empty());
        assert_eq!(tk.count(), 0);
        assert!(!tk.is_primed());
        assert_eq!(tk.top().len(), 0);
        assert_eq!(tk.guaranteed_top(), 0);
        assert_eq!(tk.count_of(&7), 0);
    }

    #[test]
    fn tracks_single_key() {
        let mut tk: TopK<u32> = TopK::new(10).unwrap();
        for _ in 0..5 {
            tk.update(42);
        }
        assert_eq!(tk.count_of(&42), 5);
        assert_eq!(tk.len(), 1);
        assert_eq!(tk.count(), 5);
        assert!(tk.is_primed());
        assert_eq!(ranked(&tk), [(42, 5)]);
        assert_eq!(tk.guaranteed_top(), 1);
        check_invariants(&tk);
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
        assert_eq!(ranked(&tk), [(1, 5), (2, 3), (3, 1)]);
        assert_eq!(tk.top().len(), 3);
        // No eviction happened, so every error is 0 and the whole order is exact.
        assert!(tk.top().all(|c| c.error == 0 && c.guaranteed() == c.count));
        assert_eq!(tk.guaranteed_top(), 3);
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
        let top2: Vec<(u32, u64)> = t.top().take(2).map(|c| (*c.key, c.count)).collect();
        assert_eq!(top2, [(9, 100), (8, 50)]);
        assert!(t.guaranteed_top() >= 2);
    }

    /// The paper's trace: a new key enters at the evicted minimum plus one,
    /// records that minimum as its error, and climbs if it keeps arriving.
    #[test]
    fn eviction_inherits_the_minimum_as_error() {
        let mut t: TopK<char> = TopK::new(3).unwrap();
        for c in ['A', 'A', 'A', 'B', 'C'] {
            t.update(c);
        }
        t.update('D'); // evicts a count-1 entry, enters at 2 with error 1
        let d = t.top().find(|c| *c.key == 'D').unwrap();
        assert_eq!((d.count, d.error, d.guaranteed()), (2, 1, 1));
        assert_eq!(t.len(), 3);
        t.update('D');
        let d = t.top().find(|c| *c.key == 'D').unwrap();
        assert_eq!((d.count, d.error, d.guaranteed()), (3, 1, 2));
        // A is exact (error 0) and still first; D is level with it on count.
        assert_eq!(
            t.top().next().map(|c| (*c.key, c.count, c.error)),
            Some(('A', 3, 0))
        );
    }

    #[test]
    fn overcount_property() {
        let mut tk: TopK<u32> = TopK::new(4).unwrap();
        let mut r = Lcg(7);
        let mut truth = [0u64; 64];
        for _ in 0..5_000 {
            let k = (r.next() % 64) as u32;
            // skew: low keys far more often
            let k = if r.next().is_multiple_of(4) { k } else { k % 4 };
            truth[k as usize] += 1;
            tk.update(k);
        }
        let bound = tk.count() / tk.capacity() as u64;
        for c in tk.top() {
            let true_count = truth[*c.key as usize];
            assert!(c.count >= true_count, "count is an upper bound");
            assert!(
                c.count - true_count <= c.error,
                "overcount within the recorded error"
            );
            assert!(c.error <= bound, "error within total / capacity");
        }
        check_invariants(&tk);
    }

    /// `guaranteed_top` counts the leading ranks whose order no error bound
    /// can disturb, and stops at the first rank that could trade places.
    #[test]
    fn guaranteed_top_stops_where_errors_overlap() {
        let mut t: TopK<u32> = TopK::new(4).unwrap();
        for _ in 0..100 {
            t.update(1);
        }
        for _ in 0..60 {
            t.update(2);
        }
        for k in 3..40 {
            t.update(k); // churn through the two bottom slots
        }
        let r: Vec<(u32, u64, u64)> = t.top().map(|c| (*c.key, c.count, c.error)).collect();
        assert_eq!(r[0], (1, 100, 0));
        assert_eq!(r[1], (2, 60, 0));
        // Ranks 3 and 4 entered by eviction and carry errors equal to or near
        // their counts; rank 2's guaranteed 60 beats anything below it.
        assert!(r[2].2 > 0 && r[3].2 > 0);
        assert_eq!(t.guaranteed_top(), 2, "{r:?}");
    }

    #[test]
    fn count_of_unknown_key_is_zero() {
        let mut tk: TopK<u32> = TopK::new(3).unwrap();
        tk.update(1);
        assert_eq!(tk.count_of(&1), 1);
        assert_eq!(tk.count_of(&99), 0);
    }

    #[test]
    fn reset_clears_all() {
        let mut tk: TopK<u32> = TopK::new(3).unwrap();
        for k in 0..10 {
            tk.update(k);
        }
        tk.reset();
        assert_eq!(tk.len(), 0);
        assert_eq!(tk.count(), 0);
        assert!(!tk.is_primed());
        assert!(tk.cells.iter().all(|c| c.slot == EMPTY));
        tk.update(5);
        assert_eq!(ranked(&tk), [(5, 1)]);
        check_invariants(&tk);
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
        let names: Vec<&str> = tk.top().map(|c| *c.key).collect();
        assert_eq!(names, ["btc", "eth", "sol"]);
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
        assert_eq!(ranked(&a), ranked(&b));
        assert!(ranked(&a).iter().all(|e| e.1 == 1));
    }

    /// Sorted, indexed and consistent after every single update on streams
    /// that fill the table and evict constantly.
    #[test]
    fn invariants_hold_after_every_update() {
        for seed in 1..=60u64 {
            // Odd seeds exercise the scanned small table, even seeds the
            // hash-indexed one.
            let cap = if seed % 2 == 1 {
                1 + (seed as usize % 16)
            } else {
                SCAN_MAX + 1 + (seed as usize % 16)
            };
            let mut t: TopK<u32> = TopK::new(cap).unwrap();
            let mut r = Lcg(seed);
            for _ in 0..(r.next() % 400) {
                t.update((r.next() % 80) as u32);
                check_invariants(&t);
            }
            let keys: Vec<u32> = t.top().map(|c| *c.key).collect();
            let mut dedup = keys.clone();
            dedup.sort_unstable();
            dedup.dedup();
            assert_eq!(dedup.len(), keys.len(), "seed {seed}: duplicate key");
        }
    }

    /// Heavy churn: a universe far larger than the table, so the index's
    /// deletion path (backward shift) runs on almost every update.
    #[test]
    fn index_survives_heavy_churn() {
        let mut t: TopK<u32> = TopK::new(64).unwrap();
        let mut r = Lcg(99);
        for step in 0..20_000 {
            t.update((r.next() % 5_000) as u32);
            if step % 97 == 0 {
                check_invariants(&t);
            }
        }
        check_invariants(&t);
        assert_eq!(t.len(), 64);
    }

    /// The scanned small table under the same churn.
    #[test]
    fn small_table_survives_heavy_churn() {
        let mut t: TopK<u32> = TopK::new(16).unwrap();
        let mut r = Lcg(7);
        for step in 0..20_000 {
            t.update((r.next() % 5_000) as u32);
            if step % 97 == 0 {
                check_invariants(&t);
            }
        }
        check_invariants(&t);
        assert_eq!(t.len(), 16);
        assert!(t.cells.is_empty());
    }

    /// Hot keys end up at the front and are the guaranteed ranks.
    #[test]
    fn hot_keys_sit_at_the_front() {
        let mut t: TopK<u32> = TopK::new(200).unwrap();
        let mut x = 0x2545_F491_4F6C_DD1Du64;
        for _ in 0..20_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            // Half the traffic on key 0, a quarter on 1, an eighth on 2, the
            // rest spread over 2,000 cold keys.
            let r = x % 1000;
            let key = if r < 500 {
                0
            } else if r < 750 {
                1
            } else if r < 875 {
                2
            } else {
                3 + ((x >> 20) % 2_000) as u32
            };
            t.update(key);
        }
        let first: Vec<u32> = t.top().take(3).map(|c| *c.key).collect();
        assert_eq!(first, [0, 1, 2]);
        assert!(t.guaranteed_top() >= 3);
        check_invariants(&t);
    }
}
