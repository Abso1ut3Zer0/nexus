# Snowflake IDs

Twitter-style packed integer IDs: `[timestamp | worker | sequence]`. The bit
layout is encoded in the type via const generics, so the ID and its generator
share the same layout parameters at compile time.

## Layout parameters

```rust
Snowflake64<const T: u32, const W: u32, const S: u32>
```

- `T` — timestamp bits
- `W` — worker/shard bits
- `S` — sequence bits

Constraint: `T + W + S <= 63` (top bit reserved to keep IDs positive for
systems that can't handle unsigned, e.g. Java or Postgres `bigint`).

Twitter's original layout is `Snowflake64<41, 10, 12>`. A layout like
`<42, 6, 16>` gives you 16 bits of sequence room per millisecond (65k IDs/ms
per worker) at the cost of only 64 workers.

## Generating IDs

```rust
use nexus_id::{Snowflake64, SnowflakeId64};

// Worker 5, epoch = 2024-01-01 or similar (your choice, passed to next_id)
let mut gen: Snowflake64<42, 6, 16> = Snowflake64::new(5);

// Second argument is the current timestamp in milliseconds since your epoch
let id: SnowflakeId64<42, 6, 16> = gen.next_id(now_millis()).unwrap();

assert_eq!(id.worker(), 5);
// id.tick(), id.sequence(), id.raw() all available
```

`next_id` returns `Result<_, SequenceExhausted>`. Exhaustion means you've
burned through the entire sequence space for the *current* millisecond — the
caller can either spin-wait for the next tick or error out. With 16 sequence
bits (65,536 IDs/ms/worker), this is effectively impossible for non-pathological
workloads.

## Monotonicity

Within a single worker, IDs are strictly monotonic as long as:

1. You feed `next_id` timestamps that don't go backwards.
2. You don't exhaust the sequence space within a tick without bumping time.

Clock goes backwards? You need a policy: crash, clamp to `last_timestamp`,
or refuse to generate. The generator clamps — it will never produce an ID
smaller than the previous one from the same generator.

## Signed variants

`SnowflakeSigned64` / `SnowflakeSigned32` use an `i64`/`i32` backing type for
systems that want sign-preserving packed IDs. Same layout rules, just signed.

## Why const generics?

The alternative is storing layout in the generator at runtime. We don't,
because:

- `worker()`, `timestamp()`, `sequence()` become branchless bit-shifts with
  compile-time constants. The compiler folds the masks into the instruction
  stream.
- Two Snowflakes with different layouts are *different types*. You can't
  accidentally compare a `SnowflakeId64<42,6,16>` with a
  `SnowflakeId64<41,10,12>`.

The cost is that you need to commit to a layout at build time. For a trading
system where the layout is part of the protocol, that's fine.

## Hash-map footgun

Snowflake IDs have *awful* bit distribution for power-of-2 hash tables — the
low bits cycle through the sequence counter, the high bits barely move. Two
options:

1. Use a good hasher (`rustc_hash::FxHashMap`, `ahash::AHashMap`).
2. Wrap in [`MixedId64`](mixed-id.md) and use `nohash_hasher` for identity
   hashing at ~1 cycle per lookup.

See [mixed-id.md](mixed-id.md).
