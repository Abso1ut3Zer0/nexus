# TopK — Space-Saving Top-K Frequent Items

**Tracks the K most frequent items in a stream with bounded memory.**
Guarantees items above the `total/K` frequency threshold are tracked.

| Property | Value |
|----------|-------|
| Update cost | 36 cycles (K=16) |
| Memory | K × (key + count) |
| Types | `TopK<K>` for `K: Eq + Clone`; capacity at construction (`alloc`) |
| Output | Sorted list of (key, count) pairs |

## What It Does

Maintains a fixed-size table of (item, estimated count) pairs.
- If item is tracked: increment its count
- If table not full: add item with count 1
- If table full: evict the minimum-count item, replace with new item,
  count = evicted_count + 1 (the overcount)

**Accuracy guarantee:** Any item with true frequency > `total / CAP`
is guaranteed to be in the output. Reported counts may overestimate
by at most `total / CAP`.

## Configuration

```rust
let mut top: TopK<String> = TopK::new(16).unwrap();  // track top 16

top.update("BTC-USD".to_string());
top.update("ETH-USD".to_string());
top.update("BTC-USD".to_string());

let mut buf = [("".to_string(), 0u64); 16];
let n = top.top(&mut buf);
for (key, count) in &buf[..n] {
    println!("{key}: {count}");
}
```

## Examples

- "Top 10 symbols by message volume"
- "Most frequent error codes"
- "Hottest cache keys"

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `TopK::update` (16 slots) | 36 cycles | 44 cycles |

Linear scan over `capacity` entries. Above a few dozen, consider a min-heap variant.

## Academic Reference

Metwally, A., Agrawal, D., and El Abbadi, A. "Efficient Computation of
Frequent and Top-k Elements in Data Streams." *ICDT* (2005).
