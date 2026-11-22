# Type Matrix

Every public algorithm type: its numeric form, the Cargo feature it needs, and
the crate and module that own it. Module paths are under `nexus_stats::`; the
umbrella re-exports every sub-crate, so a type from `nexus-stats-detection` is
`nexus_stats::detection::Mosum` once the umbrella's `detection` feature (or
`full`) is on. The Feature column is the sub-crate's own gate: `—` is always
available, `alloc` is implied by `std`, `std|libm` means one of the two math
providers, `alloc + std|libm` means both.

Numeric forms:

- **`f64`**: a plain name, one instantiation.
- **`T: Sample`**: one generic type for `f64` and `i64` (`Drawdown<f64>`, `Drawdown<i64>`). `update` returns `Result` on `f64` (NaN and infinity rejected) and the plain value on `i64`. Name `T` at construction: `Drawdown::<i64>::new()`, `CoDel::<i64>::builder()`.
- **`T: Float`**: one generic type for `f64` and `f32`; takes and returns `T`, accumulates in `f64`.
- **`u64` ticks**: timestamps in any unit, the same clock for every stamp into one value; `clock::MonotonicClock` is the `std` bridge from `Instant`.

See [Integer vs Float](../guides/integer-vs-float.md) for the caller rules and
[Migrating to 7.0](../guides/migrating-to-7.md) for the 6.x names.

## Change detection

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `Cusum` | `f64` | — | core (`detection`) |
| `DistributionShift` | `f64` | `std\|libm` | core (`detection`) |
| `Mosum` | `f64` | `alloc` | detection (`detection`) |
| `ShiryaevRoberts` | `f64` | `std\|libm` | detection (`detection`) |
| `MultiGate` | `f64` | — | detection (`detection`) |
| `RobustZScore<T>` | `T: Float` | — | detection (`detection`) |
| `AdaptiveThreshold` | `f64` | `std\|libm` | detection (`detection`) |
| `TrendAlert` | `f64` | — | detection (`detection`) |
| `PageHinkley` | `f64` | — | detection (`detection`) |
| `Adwin` | `f64` | `alloc + std\|libm` | detection (`detection`) |
| `Bocpd` | `f64` | `alloc + std\|libm` | detection (`detection`) |
| `DistDrift` | `f64` | `alloc + std\|libm` | detection (`detection`) |

## Smoothing

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `Ema` | `f64` | — | core (`smoothing`) |
| `AsymEma` | `f64` | — | core (`smoothing`) |
| `Slew<T>` | `T: Sample` | — | core (`smoothing`) |
| `Holt` | `f64` | — | smoothing |
| `Kalman1d` | `f64` | — | smoothing |
| `Spring` | `f64` | — | smoothing |
| `HuberEma` | `f64` | — | smoothing |
| `Kama` | `f64` | `alloc` | smoothing |
| `Hampel` | `f64` | `alloc` | smoothing |
| `WindowedMedian<T>` | `T: Sample` | `alloc` | smoothing |

## Statistics

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `Welford` | `f64` | — | core (`statistics`) |
| `Moments` | `f64` | — | core (`statistics`) |
| `EwmVar` | `f64` | — | core (`statistics`) |
| `Covariance` | `f64` | — | core (`statistics`) |
| `CovarianceMatrix` | `f64` | `alloc` | core (`statistics`) |
| `HarmonicMean` | `f64` | — | core (`statistics`) |
| `Percentile` | `f64` | — | core (`statistics`) |
| `Lpm` | `f64` | — | core (`statistics`) |
| `Cvar` | `f64` | — | core (`statistics`) |
| `HitRate` | `f64` pairs (signs compared) | — | core (`statistics`) |
| `BucketAccumulator` (→ `BucketSummary`) | `f64` | — | core (`statistics`) |
| `Amihud` | `f64` | — | core (`statistics`) |
| `BipowerVariation` (→ `JumpDecomposition`) | `f64` | `std\|libm` | core (`statistics`) |
| `RollSpread` (→ `RollEstimate`) | `f64` | `std\|libm` | core (`statistics`) |
| `HalfLife` | `f64` | `std\|libm` | core (`statistics`) |
| `Hurst` | `f64` | `alloc + std\|libm` | core (`statistics`) |
| `VarianceRatio` (→ `VarianceRatioEstimate`) | `f64` | `alloc + std\|libm` | core (`statistics`) |
| `TwoScaleRv` (→ `TwoScaleEstimate`) | `f64` | `alloc + std\|libm` | core (`statistics`) |

## Normalization

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `MinMaxNorm<T>` | `T: Float` | — | core (`normalization`) |
| `ZScoreNorm<T>` | `T: Float` | `std\|libm` | core (`normalization`) |
| `QuantileNorm<T>` | `T: Float` | `alloc` | core (`normalization`) |

## Monitoring

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `Drawdown<T>` | `T: Sample` | — | core (`monitoring`) |
| `RunningMax<T>`, `RunningMin<T>` | `T: Sample` | — | core (`monitoring`) |
| `WindowedMax<T>`, `WindowedMin<T>` | `T: Sample`, `u64` ticks | — | core (`monitoring`) |
| `MaxGauge<T>` | `T: Sample` | — | core (`monitoring`) |
| `PeakHold<T>` | `T: Sample` | — | core (`monitoring`) |
| `CoDel<T>` | `T: Sample` sojourn, `u64` ticks | — | core (`monitoring`) |
| `Jitter<T>` | `T: Sample` | — | core (`monitoring`) |
| `Liveness` | `u64` ticks | — | core (`monitoring`) |
| `EventRate` | `u64` ticks | — | core (`monitoring`) |
| `PollSaturation` (→ `PollSummary`) | `u64` ticks, counts | — | core (`monitoring`) |
| `SojournSaturation` (→ `SojournSummary`) | `i64` sojourn, `u64` summary | — | core (`monitoring`) |
| `ErrorRate` | `bool` outcomes, `f64` weights | — | core (`monitoring`) |
| `HawkesIntensity` | `f64` | `std\|libm` | core (`monitoring`) |

## Control

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `DeadBand<T>` | `T: Sample` | — | core (`control`) |
| `Hysteresis<T>` | `T: Sample` | — | core (`control`) |
| `LevelCrossing<T>` | `T: Sample` | — | core (`control`) |
| `FirstDiff<T>`, `SecondDiff<T>` | `T: Sample` | — | core (`control`) |
| `Debounce` | `u64` count | — | core (`control`) |
| `PeakDetector<T>` (→ `Peak<T>`) | `T: Sample` | — | control (`control`) |
| `BoolWindow` | `bool` | `alloc` | control (`control`) |

## Frequency

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `TopK<K>` | any `K: Eq + Hash`, `u64` counts | `alloc` | control (`frequency`) |
| `FlexProportionGlobal`, `FlexProportionLocal` | `u64` counts | — | control (`frequency`) |
| `DecayAccum` | `u64` ticks, `f64` weights | `std\|libm` | control (`frequency`) |

## Regression

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `LinearRegression`, `EwLinearRegression` | `f64` | — | regression (`regression`) |
| `PolynomialRegression`, `EwPolynomialRegression` | `f64` | — | regression (`regression`) |
| `ExponentialRegression`, `LogarithmicRegression`, `PowerRegression` (+ `Ew*`) | `f64` | `std\|libm` | regression (`regression`) |
| `LogisticRegression` | `f64` | `alloc + std\|libm` | regression (`regression`) |
| `KyleLambda` | `f64` | — | regression (`regression`) |
| `LaggedPredictor` | `f64` | `alloc + std\|libm` | regression (`regression`) |
| `SignalDecayCurve` | `f64` | `alloc + std\|libm` | regression (`regression`) |

## Learning and optimization

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `LmsFilter`, `NlmsFilter`, `RlsFilter` | `f64` | `alloc` | regression (`learning`) |
| `HuberRegression` | `f64` | `alloc` | regression (`learning`) |
| `OnlineKMeans` | `f64` | `alloc` | regression (`learning`) |
| `OnlineGd` | `f64` | `alloc` | regression (`learning`) |
| `AdaGrad`, `Adam` | `f64` | `alloc + std\|libm` | regression (`learning`) |
| `Ucb1`, `ThompsonBeta`, `ThompsonGamma`, `EpsilonGreedy`, `Exp3` | `f64` rewards | `alloc + std\|libm` | regression (`learning`) |

## Estimation and hypothesis testing

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `Kalman2d`, `Kalman3d` | `f64` | — | regression (`estimation`) |
| `BetaBinomial` | `bool` / counts | — | regression (`estimation`) |
| `GammaPoisson` | counts, `f64` exposure | — | regression (`estimation`) |
| `SprtBernoulli` | `bool` | `std\|libm` | detection (`estimation`) |
| `SprtGaussian` | `f64` | `std\|libm` | detection (`estimation`) |

## Signal analysis and information theory

| Type | Numeric | Feature | Crate (module) |
|------|---------|---------|----------------|
| `Autocorrelation` | `f64` | `alloc` | detection (`signal`) |
| `CrossCorrelation` | `f64` | `alloc` | detection (`signal`) |
| `Entropy` | category index | `alloc + std\|libm` | detection (`signal`) |
| `TransferEntropy` | bin indices | `alloc + std\|libm` | detection (`signal`) |
| `PredictiveInfoBound` | bin indices | `alloc + std\|libm` | detection (`signal`) |

## Clocks

| Type | What | Feature | Crate (module) |
|------|------|---------|----------------|
| `MonotonicClock` | `u64` nanoseconds since construction, from `Instant` | `std` | core (`clock`) |
| `EpochClock` | `u64` nanoseconds since the Unix epoch, from `SystemTime` | `std` | core (`clock`) |

## Feature-gated summary

| Feature | What it enables |
|---------|-----------------|
| `std` (default) | Hardware `sqrt` / `exp` / `ln`, the clocks, and `alloc` |
| `libm` | Pure Rust `sqrt` / `exp` / `ln` for `no_std`; the `std\|libm` rows above |
| `alloc` | Runtime-sized windows and buffers: MOSUM, WindowedMedian, KAMA, Hampel, BoolWindow, the correlations and entropies, the adaptive filters, optimizers and bandits, Hurst, VarianceRatio, TwoScaleRv, CovarianceMatrix, QuantileNorm |
