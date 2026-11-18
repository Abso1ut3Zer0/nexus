# TopK — Space-Saving Heavy Hitters

**Type:** `TopK<K>` (generic over the key type)
**Import:** `use nexus_stats_control::frequency::TopK;`
**Feature flags:** `alloc`.

## What it does

Tracks the approximate top-K most frequent items in a stream using the Space-Saving algorithm (Metwally, Agrawal, El Abbadi, ICDT 2005), the deterministic heavy-hitters sketch behind ClickHouse's `topK` and Algebird's `SpaceSaver`. Fixed memory: `capacity` counters plus a fixed hash index, allocated once. Built for market-data observability (which of thousands of symbols are the busiest, from a per-message update), though nothing in it is market-specific.

The structure is the paper's Stream-Summary flattened into an array kept sorted by count (one swap per update keeps the order; the minimum to evict is the last slot), with an open-addressing hash index for the key lookup above 32 counters (smaller tables are scanned, which is cheaper at that size), so `update` is O(1) expected regardless of capacity or of how many distinct keys flow through, and `top()` is a view of the sorted array.

Space-Saving is an approximate algorithm: it guarantees that the true top-K items are always tracked if they are sufficiently dominant, but the *order* and *counts* of less-frequent items may be biased. For dominant items the estimates are exact.

## When to use it

- **Heavy-hitter detection** — which users are generating the most traffic?
- **Top trading pairs by volume.**
- **Most frequent errors / reasons / tokens.**
- **Leaderboards** over a stream without storing the whole stream.

Not for: exact frequency counts with bounded error on minor items — use a full `HashMap` for that if memory allows.

## API

```rust
impl<K: Eq + Hash> TopK<K> {
    pub fn new(capacity: usize) -> Result<Self, nexus_stats_core::ConfigError>;  // two allocations, none after
    pub fn capacity(&self) -> usize;
    pub fn update(&mut self, key: K);
    pub fn top(&self) -> impl ExactSizeIterator<Item = Counter<'_, K>>;  // highest count first
    pub fn guaranteed_top(&self) -> usize;  // leading ranks whose order is provably exact
    pub fn count_of(&self, key: &K) -> u64;
    pub fn len(&self) -> usize;
    pub fn is_empty(&self) -> bool;
    pub fn count(&self) -> u64;      // samples seen
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}
```

`update(key)` increments the count for `key`. When the structure is full and a new key arrives, Space-Saving displaces the current minimum-count slot with the new key, taking over its count (plus one). The "error bar" on any slot's count is at most the minimum count — the heaviest hitters have very tight bounds.

`top()` is a view of the sorted table: an iterator of `Counter { key, count, error }`, highest count first, nothing copied, sorted or allocated; `top().take(k)` is the top k. `count` is an upper bound on the truth, `error` is the count the entry inherited when it entered (the most it can be overstated by, at most `total / capacity`), and `guaranteed()` is `count - error`. `guaranteed_top()` is the number of leading ranks whose order no error bound can disturb: print those as exact, the rest as approximate. Equal counts come out in a deterministic but unspecified order.

## Example — trading pair volume tracker

```rust
use nexus_stats_control::frequency::TopK;

let mut top: TopK<&'static str> = TopK::new(16).unwrap();

// Stream of trade events.
let events = ["BTC-USD", "ETH-USD", "BTC-USD", "SOL-USD",
              "BTC-USD", "ETH-USD", "BTC-USD", "ADA-USD"];
for sym in events {
    top.update(sym);
}

for c in top.top().take(3) {
    println!("{}: {} (at least {})", c.key, c.count, c.guaranteed());
}
// BTC-USD: 4 (at least 4)
// ETH-USD: 2 (at least 2)
// SOL-USD or ADA-USD: 1 (at least 1)
assert_eq!(top.guaranteed_top(), 2); // the third rank is a tie
```

## Parameter tuning

Capacity is the one knob, and it is the table size, not the k you report. Any count may be overestimated by at most `total / capacity`, so the top k are exact only when the k-th true frequency clears that bound: set capacity to several times k (2 to 10x under Zipf-like traffic). "Top 25 of 10,000 symbols" is a 100 to 500 counter table.

## Caveats

- **Approximate for tail items.** For heavy hitters (say, top-3 of the stream) Space-Saving is effectively exact. For tail items it's biased.
- **Counts aren't absolute.** A displaced item's count-at-displacement is the new lower bound for the replacing item. Use `count_of` knowing it's an upper bound, not a count.
- **No decay.** `TopK` counts forever. Combine with periodic `reset()` if you want "top-K in the last window".
- **Generic over key type.** The key must be `Eq + Hash`; nothing is cloned. For string keys on the hot path, use a small fixed-size ASCII string type (e.g., `nexus-ascii`, which hashes and compares by a precomputed hash) rather than `String`.
- **Cost does not grow with the table.** Tables of 32 counters or fewer are scanned (27 to 50 TSC ticks measured); above that a hash index makes `update` O(1) expected, 15 to 80 ticks from 64 counters to 1,000 counters over a million symbols. See the umbrella `docs/algorithms/topk.md` for the measured table and the literature.

## Cross-references

- [`DecayAccum`](decay-accum.md) — per-entity decaying score (alternative to Space-Saving for time-weighted rank).
- [`FlexProportion`](flex-proportion.md) — each known key's share of recent events, not top-K.
