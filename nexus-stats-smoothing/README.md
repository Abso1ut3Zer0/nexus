# nexus-stats-smoothing

Advanced smoothing algorithms for [nexus-stats](https://crates.io/crates/nexus-stats).

## Types

- **Holt** — Double exponential smoothing (level + trend)
- **Spring** — Critically damped spring (chase without overshoot)
- **Kama** — Kaufman Adaptive Moving Average (requires `alloc`)
- **WindowedMedian<f64> / WindowedMedian<i64>** — Running median (requires `alloc`)

Start with `Ema` from the core crate and move to one of these for a reason: a trend (`Holt`), alternating regimes (`Kama`), a known noise model (`Kalman1d`, in the regression crate), a target to chase (`Spring`), or outliers (`HuberEma`, `Hampel`, `WindowedMedian`). The crate docs say which to use for what.

## Usage

Enable the `smoothing` feature on `nexus-stats` for unified import paths:

```rust
use nexus_stats::smoothing::Holt;
```

Or depend on this crate directly:

```rust
use nexus_stats_smoothing::Holt;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
