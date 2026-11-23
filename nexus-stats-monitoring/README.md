# nexus-stats-monitoring

Monitors for a running system, for [nexus-stats](https://crates.io/crates/nexus-stats): extremes, rates, liveness and queue health, each updated in fixed memory.

## Which type do I use?

**Highs and lows**

- **WindowedMax / WindowedMin**: the extreme over a sliding window of time
- **PeakHold**: a peak that decays
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
