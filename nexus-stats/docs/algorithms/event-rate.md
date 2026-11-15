# EventRate — Smoothed Events Per Unit Time

**EMA of inter-arrival times, inverted to give rate.** "How many events
per second is this source producing?"

| Property | Value |
|----------|-------|
| Update cost | ~6 cycles |
| Memory | ~32 bytes |
| Types | `EventRate` (`u64` ticks) |

## API

```rust
let mut rate = EventRate::builder().span(15).build().unwrap();

rate.update(timestamp_ns);  // record an event
if let Some(r) = rate.rate() {
    println!("{r} events per time unit");
}
```

Internally: bit-shift EMA of inter-arrival times (i128 accumulator,
shift-based smoothing), rate = 1.0 / interval. Same pattern as `Liveness`.

`EventRate` takes `u64` timestamps (e.g. nanoseconds from `Instant`).

## When to Use Something Else

- Need to detect silence → [Liveness](liveness.md) (adds deadline check)
- Need throughput in bytes/sec → compute bytes/interval and use [EMA](ema.md)
- Need exact count in window → use a sliding window counter
