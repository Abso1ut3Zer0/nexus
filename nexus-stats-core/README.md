# nexus-stats-core

Core types shared across the nexus-stats ecosystem.

The foundation of the nexus-stats crates, and the descriptive statistics they build on:

- the shared pieces: error enums, the `Accuracy` report, the `Sample` and `Float` traits, math utilities, ring storage, and the clock trait (`Clock`, `MonotonicClock`, `EpochClock`);
- the descriptive statistics: Welford, Moments, Covariance, CovarianceMatrix, HarmonicMean, Percentile, BucketAccumulator, FirstDiff, SecondDiff.

Every other concept (smoothing, detection, monitoring, control, normalization, regression, trading) has its own crate.

**Not intended for direct use** — import from
[`nexus-stats`](https://crates.io/crates/nexus-stats) instead.

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
