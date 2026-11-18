# TopK — Space-Saving Top-K Frequent Items

**Which items are the busiest right now, from a stream too wide to count,
in a table whose size you choose.** The inspiration is market-data
observability: thousands of symbols, one `update` per message, "print the
ten busiest" on demand, no allocation on the message path. Any count may be
overstated by at most `total / capacity`, and every reported counter says by
how much.

| Property | Value |
|----------|-------|
| Update cost | O(1) expected from 64 counters up (hash index): 15 to 80 TSC ticks measured through a million symbols. Tables of 32 counters or fewer are scanned instead, 27 to 50 ticks |
| Query cost (`top`) | free: an iterator over the table, which is kept sorted |
| Memory | capacity × (key + 24 bytes, padded) counters, plus for tables above 32 counters an 8-byte-cell index of 2 × capacity rounded up to a power of two; allocated at construction, nothing after |
| Types | `TopK<K>` for `K: Eq + Hash`; capacity at construction (`alloc`) |
| Output | `top()`: iterator of `Counter { key, count, error }`, highest count first; `guaranteed_top()`: how many leading ranks are provably in order |

## The algorithm

Space-Saving (Metwally, Agrawal, El Abbadi, 2005). `capacity` counters, each
`(key, count, error)`.

- Tracked key: increment its count.
- New key, table not full: append it with count 1.
- New key, table full: the entry with the smallest count is evicted; the new
  key takes its slot with `count = min + 1` and records `error = min`.

The inherited count is what makes the table work: it is how a symbol that
was not being tracked becomes a top symbol (it enters at the minimum plus
one and climbs if it keeps arriving), and it is also the only way a count can
be wrong (the new key may have had anywhere from zero to `min` earlier
occurrences). Three guarantees follow (the paper's Theorems 2 to 4):

- any key seen more than `total / capacity` times is in the table;
- every `count` is an upper bound on the truth, by at most `error`, and
  `error <= total / capacity`;
- the top k is exactly right when the k-th rank's guaranteed count
  (`count - error`) is at least the (k+1)-th rank's `count`.

The structure is the paper's Stream-Summary, flattened: the counters sit in
one array kept sorted by count (an increment restores the order with a single
swap to the front of the entry's old tie run; the minimum is always the last
slot, and the start of the run tied at the minimum is kept, not searched),
and, for tables above 32 counters, a fixed-size open-addressing hash index
(deterministic Fx hashing, 32-bit tags so probes never touch the counters,
backward-shift deletion, never more than half full) finds a key's slot
without scanning. Tables of 32 counters or fewer are simply scanned: at that
size a scan costs less than a probe, a deletion and a second probe, and the
hot keys sit at the front of the array anyway. The bottom of the array is the
revolving door newcomers come through.

## Reading the output

```rust
use nexus_stats::frequency::TopK;

let mut busiest: TopK<u32> = TopK::new(256).unwrap();   // instrument ids
// per message:
busiest.update(instrument_id);

// on demand:
let exact = busiest.guaranteed_top();
for (rank, c) in busiest.top().take(10).enumerate() {
    let mark = if rank < exact { "" } else { "~" };
    println!("{mark}{}: {} (at least {})", c.key, c.count, c.guaranteed());
}
```

`top()` is a view of the sorted array: nothing copied, nothing sorted,
`top().take(k)` is the top k. Each `Counter` carries `count` and `error`;
`guaranteed()` is `count - error`. `guaranteed_top()` walks down the ranking
while each rank's guaranteed count still beats the next rank's count and
returns how many ranks that covered: print that many as exact and the rest as
approximate. Equal counts come out in a deterministic but unspecified order.

## Choosing `capacity`

`capacity` is the table size, not the k you report. The error bound is
`total / capacity`, so the top k are exact only when the k-th true frequency
clears it; under Zipf-like traffic that means several times k (2 to 10x).
"Top 25 of 10,000 symbols" is a 100 to 500 counter table, a few kilobytes.
`guaranteed_top()` tells you after the fact whether the table was big enough.

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `TopK::update` (16 slots) | 36 cycles | 48 cycles |

`update` is O(1) expected whatever the universe of keys: a hash lookup (a
scan, for 32 counters or fewer), an increment and a swap for a tracked key;
for a new key on a full table, the O(1) eviction of the last slot and two
index writes. Scaling harness, interleaved in one process against the two
earlier shapes of this type (the array kept sorted without an index, and the
unsorted table this type had before), TSC ticks, p50 (a `HashMap` increment
with SipHash is about 17 for comparison):

| symbols / counters | `update`, final | `update`, sorted array only | `update`, previous unsorted table |
|---|---|---|---|
| 16 / 16, all hits (scanned table) | 35 | 31 | 25 |
| 100 uniform / 16, 16% hits (scanned; the README row's shape) | 29 | 27 | 30 |
| 32 / 32, all hits (scanned) | 39 | 37 | 34 |
| 200 uniform / 32, 16% hits (scanned) | 50 | 50 | 52 |
| 64 / 64, all hits (indexed) | 18 | 39 | 37 |
| 400 uniform / 64, 16% hits (indexed) | 86 | 111 | 110 |
| 100 / 100, all hits | 15 | 45 | 43 |
| 1,000 / 1,000, all hits | 23 | 122 | 139 |
| 10,000 Zipf / 100, 42% hits | 62 | 108 | 120 |
| 10,000 Zipf / 500, 61% hits | 53 | 238 | 289 |
| 10,000 Zipf / 1,000, 70% hits | 47 | 345 | 439 |
| 1,000,000 Zipf / 500, 38% hits | 73 | 347 | 410 |
| 1,000,000 Zipf / 1,000, 43% hits | 71 | 593 | 719 |

The hit rate is how often the arriving key was already in the table; the
rest of the updates evict. Both earlier shapes paid a scan of the table per
update (the unsorted one paid a second scan for the minimum on every miss),
so their cost grew with the table; the final shape does not. The one place
the earlier table was cheaper is a tiny table that never evicts (16 or 32
symbols in total, every update a hit), by 5 to 10 ticks: each counter now
carries its error and tag, so the scan touches twice the bytes. That is not a
top-k problem, and a top-k over a real symbol universe is the other rows.

## Literature

- Metwally, A., Agrawal, D., and El Abbadi, A. "Efficient Computation of
  Frequent and Top-k Elements in Data Streams." *ICDT* (2005). The algorithm,
  the Stream-Summary structure, and the three guarantees above.
- Cormode, G., and Hadjieleftheriou, M. "Finding Frequent Items in Data
  Streams." *VLDB* (2008). The survey that compares the counter-based and
  sketch-based families; Space-Saving comes out most accurate per byte among
  the deterministic ones.
- In production: ClickHouse's `topK` aggregate and Twitter's Algebird
  `SpaceSaver` are Space-Saving.
