# TopK — Space-Saving Top-K Frequent Items

**Tracks the most frequent items in a stream with bounded memory.**
Guarantees items above the `total / capacity` frequency threshold are tracked.
A small-k statistic: a flat table scanned on every update, right up to a
couple of hundred counters and the wrong tool past that.

| Property | Value |
|----------|-------|
| Update cost | O(capacity): 36 cycles at 16 counters, ~40 ticks at 100, ~900 at 10,000 |
| Query cost (`top`) | one pass over the table plus a sort or heap of the result |
| Memory | capacity × (key + count), one allocation at construction |
| Types | `TopK<K>` for `K: Eq + Clone`; capacity at construction (`alloc`) |
| Output | (key, count) pairs, highest count first |

## What It Does

Maintains a fixed-size table of (item, estimated count) pairs.
- If item is tracked: increment its count
- If table not full: add item with count 1
- If table full: evict the minimum-count item, replace with new item,
  count = evicted_count + 1 (the overcount)

**Accuracy guarantee:** Any item with true frequency > `total / capacity`
is guaranteed to be in the output. Reported counts may overestimate
by at most `total / capacity`.

**Choosing `capacity`:** it is the table size, not the k you report. The
top k are exact only when the k-th true frequency clears the overcount
bound above, which under Zipf-like traffic means a capacity of several
times k. "Top 25 of 10,000 symbols" is a 100 to 500 counter table.

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

`update` is one linear scan of the table, so it scales with `capacity`
(scaling harness, Zipf stream, TSC ticks, p50; a `HashMap` increment is
about 17 for comparison):

| counters | `update` | `top(25)` | `top` full ranking |
|---|---|---|---|
| 100 | 40 | 930 | 1,600 |
| 1,000 | 140 | 2,300 | 18,000 |
| 10,000 | 880 | 9,600 | 76,000 |

Up to a couple of hundred counters the flat scan is the right trade (no
hashing, no allocation, contiguous memory). Past that, a hash-indexed table
is the right structure for `update`; this type is not it.

`top(n)` is a query: a buffer that covers the table is sorted directly, a
shorter one is filled through a size-n min-heap kept in the buffer
(O(len log n)). Equal counts come out in a deterministic but unspecified
order.

## Academic Reference

Metwally, A., Agrawal, D., and El Abbadi, A. "Efficient Computation of
Frequent and Top-k Elements in Data Streams." *ICDT* (2005).
