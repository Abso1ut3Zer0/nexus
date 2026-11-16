# nexus-stats-detection

Advanced change detection and signal analysis for [nexus-stats](https://crates.io/crates/nexus-stats).

## Detection Types

- **Mosum** — Moving sum change detection (requires `alloc`)
- **ShiryaevRoberts** — Shiryaev-Roberts change detection (requires `std` or `libm`)
- **AdaptiveThreshold** — EMA + Welford adaptive threshold (requires `std` or `libm`)
- **RobustZScore<f64>** — Robust z-score on an EMA of mean absolute deviation (outliers cannot inflate the scale)
- **TrendAlert** — Holt-based trend alerting
- **MultiGate** — Multi-threshold gating
- **PageHinkley** — Sequential mean drift detection (Page-Hinkley test)
- **Adwin** — Adaptive window distribution change detection (requires `alloc` + (`std` or `libm`))

## Signal Types

- **Autocorrelation** — Lagged autocorrelation (requires `alloc`)
- **CrossCorrelation** — Lagged cross-correlation (requires `alloc`)
- **Entropy** — Shannon entropy estimation (requires `alloc` + (`std` or `libm`))
- **TransferEntropy** — Transfer entropy between series (requires `alloc` + (`std` or `libm`))
- **PredictiveInfoBound** — Binned mutual information estimation (requires `alloc` + (`std` or `libm`))

## Estimation Types

- **SprtBernoulli** — Sequential Probability Ratio Test (requires `std` or `libm`)
- **SprtGaussian** — Gaussian SPRT (requires `std` or `libm`)

## Usage

Enable the `detection` feature on `nexus-stats` for unified import paths:

```rust
use nexus_stats::detection::RobustZScore;
use nexus_stats::signal::Autocorrelation;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
