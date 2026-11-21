# nexus-stats-core

Core types shared across the nexus-stats ecosystem.

This crate provides the fundamental streaming statistics types: error enums,
math utilities, clock trait (`Clock`, `MonotonicClock`, `EpochClock`), core smoothing
(EMA, AsymEma, Slew), statistics (Welford, Moments, EwmVar, Covariance,
HarmonicMean, Percentile, BipowerVariation *(std/libm)*, RollSpread *(std/libm)*,
TwoScaleRv *(alloc+std/libm)*), monitoring (HawkesIntensity *(std/libm)*),
core detection (CUSUM), and core control types
(DeadBand, Hysteresis, Debounce, LevelCrossing, Diff).

**Not intended for direct use** — import from
[`nexus-stats`](https://crates.io/crates/nexus-stats) instead.

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
