# TopK — Space-Saving Heavy Hitters

**Type:** `TopK<K>` (generic over the key type)
**Import:** `use nexus_stats_control::frequency::TopK;`
**Feature flags:** `alloc`.

## What it does

Tracks the approximate top-K most frequent items in a stream using the Space-Saving algorithm (Metwally, Agrawal, El Abbadi, 2005). Fixed memory — `O(K)` slots, one per tracked item. Zero allocation per update.

Space-Saving is an approximate algorithm: it guarantees that the true top-K items are always tracked if they are sufficiently dominant, but the *order* and *counts* of less-frequent items may be biased. For dominant items the estimates are exact.

## When to use it

- **Heavy-hitter detection** — which users are generating the most traffic?
- **Top trading pairs by volume.**
- **Most frequent errors / reasons / tokens.**
- **Leaderboards** over a stream without storing the whole stream.

Not for: exact frequency counts with bounded error on minor items — use a full `HashMap` for that if memory allows.

## API

```rust
impl<K: Eq + Clone> TopK<K> {
    pub fn new(capacity: usize) -> Result<Self, nexus_stats_core::ConfigError>;  // the table is allocated once
    pub fn capacity(&self) -> usize;
    pub fn update(&mut self, key: K);
    pub fn top(&self, buf: &mut [(K, u64)]) -> usize;
    pub fn count_of(&self, key: &K) -> u64;
    pub fn len(&self) -> usize;
    pub fn reset(&mut self);
}
```

`update(key)` increments the count for `key`. When the structure is full and a new key arrives, Space-Saving displaces the current minimum-count slot with the new key, taking over its count (plus one). The "error bar" on any slot's count is at most the minimum count — the heaviest hitters have very tight bounds.

`top(&mut buf)` writes the top items into a caller-provided buffer (no allocation), sorted by count descending. Returns the number of items written.

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

let mut buf = [("".into(), 0u64); 3];
let n = top.top(&mut buf);

for &(ref sym, count) in &buf[..n] {
    println!("{sym}: {count}");
}
// BTC-USD: 4
// ETH-USD: 2
// SOL-USD or ADA-USD: 1
```

## Parameter tuning

Capacity is the one knob. Rule of thumb: set capacity to `2-10 * K` if you want to report the top-K reliably. Items that are 1/K of the stream are guaranteed tracked; items below that frequency may be missed or have biased counts.

## Caveats

- **Approximate for tail items.** For heavy hitters (say, top-3 of the stream) Space-Saving is effectively exact. For tail items it's biased.
- **Counts aren't absolute.** A displaced item's count-at-displacement is the new lower bound for the replacing item. Use `count_of` knowing it's an upper bound, not a count.
- **No decay.** `TopK` counts forever. Combine with periodic `reset()` if you want "top-K in the last window".
- **Generic over key type.** The key must be `Eq + Hash + Clone`. For string keys on the hot path, use a small fixed-size ASCII string type (e.g., `nexus-ascii`) rather than `String`.

## Cross-references

- [`DecayAccum`](decay-accum.md) — per-entity decaying score (alternative to Space-Saving for time-weighted rank).
- [`FlexProportion`](flex-proportion.md) — each known key's share of recent events, not top-K.
