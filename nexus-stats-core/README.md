# nexus-stats-core

Core types shared across the nexus-stats ecosystem.

This crate provides the fundamental streaming statistics types: error enums,
math utilities, clock trait (`Clock`, `MonotonicClock`, `EpochClock`), core smoothing
(EMA, AsymEma, Slew), the descriptive statistics (Welford, Moments, EwmVar,
Covariance, HarmonicMean, Percentile, BucketAccumulator, FirstDiff, SecondDiff),
and core detection (CUSUM).

**Not intended for direct use** — import from
[`nexus-stats`](https://crates.io/crates/nexus-stats) instead.

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
