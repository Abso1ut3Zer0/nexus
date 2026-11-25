# nexus-stats-monitoring

Monitors for a running system, for [nexus-stats](https://crates.io/crates/nexus-stats): extremes, rates, liveness and queue health, each updated in fixed memory.

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` protects the state.** A type has one when some input does damage that outlasts the sample, or when `update` drops a sample you should be told about (a NaN it ignores, a timestamp that goes back). It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reader reports what the arithmetic gives,** NaN included where the true answer is undefined. It never substitutes a number. The library protects the state. It does not promise a reading is never NaN.
- **The caller brings the clock.** Physical time is a `Timestamp`: `i128` or `i64` nanoseconds, an `Instant`, a named unit (`Micros`, `Millis`, `Seconds`, `Nanos`), or a type of your own. One instance lives on one clock. Time must not go back. An `update` that takes a time ignores one before the latest it took, and its guarded form returns `NonMonotonicTime`. A call that closes an interval, such as `EventRate::take`, refuses a time that is not later.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.
- **Maxima and minima ignore NaN and accept infinity,** as `f64::max` does.

Every type in this crate follows these.

## Which type do I use?

**Highs and lows**

- **WindowedMax / WindowedMin**: the extreme over a sliding window of time
- **PeakHold**: the magnitude of a signal, followed up at once, held, then left to decay
- **PeakToTrough**: the fall from the highest value seen, and the largest such fall; on P&L, the drawdown

**Rates and timing**

- **EventRate**: events in a window, their exact rate, and the load over 1, 5 and 15 minutes (requires `std` or `libm`)
- **ErrorRate**: errors as a count (USE), a ratio per interval (SRE) and a smoothed ratio
- **Jitter**: interarrival jitter, as RFC 3550 estimates it
- **Liveness**: how long a source has been silent, in typical gaps, and the chance that a live source would be that quiet (requires `alloc`; the chance also needs `std` or `libm`)

**Queues**

- **CoDel**: a queue that is not draining, from how long each item waited (RFC 8289's rule)
- **PollSaturation**: how saturated a consumer is, from what its polls return; healthy is one message per poll and no backlog
- **SojournSaturation**: the same, from stamped waiting times

Each type's docs give its definition, what one `update` is worth (its weighting clock), and how to read it.

## Example

```rust
use core::time::Duration;
use nexus_stats_monitoring::WindowedMax;

// The slowest request over the last second, in microseconds. Time is
// i128 nanoseconds here. An `Instant`, or `Millis(ts)`, works the same way.
let mut slowest = WindowedMax::<i64, i128>::new(Duration::from_secs(1)).unwrap();
for (millis, micros) in [(0, 120), (300, 431), (600, 118), (900, 125)] {
    slowest.update(millis * 1_000_000, micros);
}
assert_eq!(slowest.max(), Some(431));
```

## Features

| Feature | Default | Enables |
|---------|---------|---------|
| `std` | yes | `exp` from the standard library; implies `alloc` |
| `alloc` | no (implied by `std`) | passed through to `nexus-stats-core` |
| `libm` | no | pure Rust `exp` for `no_std` |

`Condition`, `ConfigError`, `DataError` and `Sample` are re-exported, so this crate can be used without depending on `nexus-stats-core` directly.

## Usage

Enable the `monitoring` feature on `nexus-stats` for unified import paths:

```rust,ignore
use nexus_stats::monitoring::WindowedMax;
```

Or depend on this crate directly:

```rust
use nexus_stats_monitoring::WindowedMax;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
