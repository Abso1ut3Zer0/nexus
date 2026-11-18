# TopK — Space-Saving Heavy Hitters

**Type:** `TopK<K>` (generic over the key type)
**Import:** `use nexus_stats_control::frequency::TopK;`
**Feature flags:** `alloc`.

## What it does

Tracks the approximate top-K most frequent items in a stream using the Space-Saving algorithm (Metwally, Agrawal, El Abbadi, 2005). Fixed memory, `capacity` slots, one per tracked item, allocated once. The table is kept sorted by count on every update (one swap), so hot keys are found at the front of the scan, the minimum to evict is the last slot, and reading the ranking is free.

Space-Saving is an approximate algorithm: it guarantees that the true top-K items are always tracked if they are sufficiently dominant, but the *order* and *counts* of less-frequent items may be biased. For dominant items the estimates are exact.

## When to use it

- **Heavy-hitter detection** — which users are generating the most traffic?
- **Top trading pairs by volume.**
- **Most frequent errors / reasons / tokens.**
- **Leaderboards** over a stream without storing the whole stream.

Not for: exact frequency counts with bounded error on minor items — use a full `HashMap` for that if memory allows.

## API

```rust
impl<K: Eq> TopK<K> {
    pub fn new(capacity: usize) -> Result<Self, nexus_stats_core::ConfigError>;  // the table is allocated once
    pub fn capacity(&self) -> usize;
    pub fn update(&mut self, key: K);
    pub fn top(&self) -> impl ExactSizeIterator<Item = (&K, u64)>;  // highest count first
    pub fn count_of(&self, key: &K) -> u64;
    pub fn len(&self) -> usize;
    pub fn is_empty(&self) -> bool;
    pub fn count(&self) -> u64;      // samples seen
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}
```

`update(key)` increments the count for `key`. When the structure is full and a new key arrives, Space-Saving displaces the current minimum-count slot with the new key, taking over its count (plus one). The "error bar" on any slot's count is at most the minimum count — the heaviest hitters have very tight bounds.

`top()` is a view of the sorted table: an iterator of `(&key, count)`, highest count first, with nothing copied, sorted or allocated. `top().take(k)` is the top k. Equal counts come out in a deterministic but unspecified order.

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

for (sym, count) in top.top().take(3) {
    println!("{sym}: {count}");
}
// BTC-USD: 4
// ETH-USD: 2
// SOL-USD or ADA-USD: 1
```

## Parameter tuning

Capacity is the one knob, and it is the table size, not the k you report. Any count may be overestimated by at most `total / capacity`, so the top k are exact only when the k-th true frequency clears that bound: set capacity to several times k (2 to 10x under Zipf-like traffic). "Top 25 of 10,000 symbols" is a 100 to 500 counter table.

## Caveats

- **Approximate for tail items.** For heavy hitters (say, top-3 of the stream) Space-Saving is effectively exact. For tail items it's biased.
- **Counts aren't absolute.** A displaced item's count-at-displacement is the new lower bound for the replacing item. Use `count_of` knowing it's an upper bound, not a count.
- **No decay.** `TopK` counts forever. Combine with periodic `reset()` if you want "top-K in the last window".
- **Generic over key type.** The key must be `Eq`; nothing is hashed or cloned. For string keys on the hot path, use a small fixed-size ASCII string type (e.g., `nexus-ascii`, which compares by a precomputed hash) rather than `String`, whose comparison chases a pointer per slot.
- **Small-k statistic.** `update` is one scan of the table, bounded by `capacity` and usually far shorter under skewed traffic: about 40 ticks at 100 counters, 120 at 1,000, 700 at 10,000. Up to a couple of hundred counters the flat table is the right trade; past that a hash-indexed table is the right structure. See the umbrella `docs/algorithms/topk.md` for the measured table.

## Cross-references

- [`DecayAccum`](decay-accum.md) — per-entity decaying score (alternative to Space-Saving for time-weighted rank).
- [`FlexProportion`](flex-proportion.md) — each known key's share of recent events, not top-K.
