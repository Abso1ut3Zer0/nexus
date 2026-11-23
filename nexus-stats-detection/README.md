# nexus-stats-detection

Change detection and signal analysis for [nexus-stats](https://crates.io/crates/nexus-stats): detectors that say when a stream's behavior has shifted, measures of how a series behaves over time, and sequential tests.

## Which type do I use?

**Has something changed?** (`detection`)

- **Cusum**: a lasting shift in the mean, up or down
- **ShiryaevRoberts**: the same, when the size of the shift is known in advance (requires `std` or `libm`)
- **PageHinkley**: a drift in the mean, by the Page-Hinkley test
- **Mosum**: a spike that has since passed (requires `alloc`)
- **AdaptiveThreshold**: one sample that is an outlier, for roughly normal data (requires `std` or `libm`)
- **RobustZScore**: one sample that is an outlier, for heavy tails
- **TrendAlert**: a trend heading for a limit
- **MultiGate**: graded severity, from normal to critical
- **DistributionShift**: a change in shape (skewness, kurtosis) with the mean where it was (requires `std` or `libm`)
- **Adwin**: a change in distribution, over a window that adapts (requires `alloc` + (`std` or `libm`))

**How does the series behave over time?** (`signal`)

- **Autocorrelation**: trending or reverting, at one lag (requires `alloc`)
- **Hurst**: trending or reverting, as an exponent over a window (requires `alloc` + (`std` or `libm`))
- **HalfLife**: how fast a series reverts to its mean (requires `std` or `libm`)
- **CrossCorrelation**: which of two streams leads (requires `alloc`)
- **Entropy**: how unpredictable a stream is (requires `alloc` + (`std` or `libm`))
- **TransferEntropy**: whether one stream drives another (requires `alloc` + (`std` or `libm`))
- **PredictiveInfoBound**: binned mutual information (requires `alloc` + (`std` or `libm`))

**A decision as soon as the evidence allows** (`estimation`)

- **SprtBernoulli**: a sequential test on a rate (requires `std` or `libm`)
- **SprtGaussian**: a sequential test on a mean (requires `std` or `libm`)

Each type's docs give its definition and how to read it.

## Usage

Enable the `detection` feature on `nexus-stats` for unified import paths:

```rust
use nexus_stats::detection::RobustZScore;
use nexus_stats::signal::Autocorrelation;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
