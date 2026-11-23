# nexus-stats-monitoring

Monitors for a running system, for [nexus-stats](https://crates.io/crates/nexus-stats): extremes, rates, liveness and queue health, each updated in fixed memory.

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` exists only where it has a job.** A type has one when some input can leave it unable to give a right reading until `reset()`. It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.
- **Maxima and minima ignore NaN and accept infinity,** as `f64::max` does.

**Not yet migrated:** `CoDel`, `Drawdown`, `ErrorRate`, `EventRate`, `HawkesIntensity`, `Jitter`, `Liveness`, `PollSaturation`, `SojournSaturation`. They have not been moved to these guarantees. Most still validate in `update` and return a `Result`.

## Which type do I use?

**Highs and lows**

- **WindowedMax / WindowedMin**: the extreme over a sliding window of time
- **PeakHold**: the magnitude of a signal, followed up at once, held, then left to decay
- **Drawdown**: the fall from the highest value seen

**Rates and timing**

- **EventRate**: events per unit of time, smoothed
- **ErrorRate**: the share of events that failed
- **Jitter**: how much consecutive samples or arrivals vary
- **Liveness**: whether anything has happened recently
- **HawkesIntensity**: the rate of events that come in clusters (requires `std` or `libm`)

**Queues**

- **CoDel**: a queue that is not draining, from how long each item waited
- **PollSaturation**: how saturated a consumer is, from what its polls return
- **SojournSaturation**: the same, from stamped waiting times

Each type's docs give its definition, what one `update` is worth (its weighting clock), and how to read it.

## Example

```rust
use nexus_stats_monitoring::WindowedMax;

// The slowest request over the last 1,000 ticks, in microseconds.
let mut slowest = WindowedMax::<i64>::new(1_000).unwrap();
for (tick, micros) in [(0, 120), (300, 431), (600, 118), (900, 125)] {
    slowest.update(tick, micros);
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
