# TopK — Space-Saving Top-K Frequent Items

**Tracks the most frequent items in a stream with bounded memory.**
Guarantees items above the `total / capacity` frequency threshold are tracked.
A small-k statistic: a flat table scanned on every update, right up to a
couple of hundred counters and the wrong tool past that.

| Property | Value |
|----------|-------|
| Update cost | O(capacity): 36 cycles at 16 counters, ~40 ticks at 100, ~900 at 10,000 |
| Query cost (`top`) | free: an iterator over the table, which is kept sorted |
| Memory | capacity × (key + count), one allocation at construction |
| Types | `TopK<K>` for `K: Eq`; capacity at construction (`alloc`) |
| Output | `top()`: iterator of `(&key, count)`, highest count first |

## What It Does

Maintains a fixed-size table of (item, estimated count) pairs, kept sorted
by count, highest first.
- If item is tracked: increment its count and swap it to the front of its
  old tie run (one swap keeps the order)
- If table not full: append the item with count 1 (the minimum, so the end)
- If table full: the last entry is a minimum; replace it with the new item,
  count = evicted_count + 1 (the overcount), and swap it forward likewise

Because the table is sorted, the hot keys of a skewed stream sit at the
front and the scan that finds them ends early, the minimum is found in O(1),
and `top()` is a view with nothing to copy or sort.

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

for (key, count) in top.top().take(10) {
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

`update` is one scan of the table for the key plus one swap, so its cost is
bounded by `capacity` and, on a skewed stream, is usually far less: the hot
keys sit at the front. Scaling harness, Zipf stream, TSC ticks, p50 (a
`HashMap` increment is about 17 for comparison):

| symbols / counters | `update`, sorted table | `update`, previous unsorted table | `top().take(25)` |
|---|---|---|---|
| 100 / 100 | 42 | 43 | 9 |
| 1,000 / 1,000 | 121 | 139 | 9 |
| 10,000 / 10,000 | 692 | 872 | 9 |
| 10,000 / 100 (42% of updates hit) | 104 | 124 | 9 |
| 10,000 / 500 (61% hit) | 242 | 298 | 9 |
| 10,000 / 1,000 (71% hit) | 481 | 602 | 9 |

Up to a couple of hundred counters the flat table is the right trade (no
hashing, no allocation, contiguous memory). Past that, a hash-indexed table
is the right structure for `update`; this type is not it.

`top()` is a view of the sorted table: an iterator of `(&key, count)` with no
copy, no sort and no buffer; `top().take(k)` is the top k. Equal counts come
out in a deterministic but unspecified order.

## Academic Reference

Metwally, A., Agrawal, D., and El Abbadi, A. "Efficient Computation of
Frequent and Top-k Elements in Data Streams." *ICDT* (2005).
