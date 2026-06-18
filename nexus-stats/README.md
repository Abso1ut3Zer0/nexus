# nexus-stats

Fixed-memory, zero-allocation streaming statistics for real-time systems.

Every primitive is O(1) per update, fixed memory after construction, and
`no_std` compatible. Designed for event loops, trading systems, and
anywhere you need statistics without latency jitter.

## Quick Start

```rust
use nexus_stats::{Direction, detection::CusumF64, smoothing::EmaF64, statistics::WelfordF64};

// Detect latency shifts with CUSUM
let mut cusum = CusumF64::builder(100.0)  // target: 100μs baseline
    .slack(5.0)                            // sensitivity
    .threshold(50.0)                       // decision boundary
    .min_samples(20)                       // warmup
    .build().unwrap();

for latency in samples {
    match cusum.update(latency) {
        Some(Direction::Rising) => println!("latency degradation detected"),
        Some(Direction::Falling) => println!("latency recovered"),
        _ => {}
    }
}

// Smooth noisy measurements with EMA
let mut ema = EmaF64::builder()
    .span(20)          // ~20-sample smoothing window
    .min_samples(10)
    .build().unwrap();

if let Some(smoothed) = ema.update(sample) {
    // use smoothed value
}

// Track running statistics with Welford
let mut stats = WelfordF64::new();
stats.update(sample);
if let Some(mean) = stats.mean() {
    println!("mean={mean}, std_dev={}", stats.std_dev().unwrap());
}
```

## Algorithms

60+ algorithms across 10 categories. See [full documentation](docs/INDEX.md)
for deep-dives on each algorithm.

### Change Detection

| Type | What It Detects | p50 |
|------|----------------|-----|
| `CusumF64` | Persistent mean shifts (up or down) | 5 |
| `MosumF64` | Transient spikes within a window | 6 |
| `ShiryaevRobertsF64` | Mean shifts with optimal detection delay | 17 |
| `MultiGateF64` | Graded anomalies: Accept/Unusual/Suspect/Reject | 12 |
| `RobustZScoreF64` | MAD-based outlier scoring with estimator freeze | 12 |
| `AdaptiveThresholdF64` | Z-score anomalies with self-learning baseline | 15 |
| `PageHinkleyF64` | Sequential mean drift (Page-Hinkley test) | TBD |
| `AdwinF64` | Adaptive window distribution change (ADWIN) | TBD |

### Smoothing & Filtering

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `EmaF64` / `EmaI64` | Exponential moving average (float / integer) | 5 |
| `AsymEmaF64` | Different alpha for rising vs falling | 11 |
| `KamaF64` | Kaufman adaptive MA (adapts to trend/noise) | 16 |
| `Kalman1dF64` | 1D Kalman filter with velocity tracking | 25 |
| `HoltF64` | Double exponential (level + trend) | 11 |
| `SpringF64` | Critically damped spring (smooth target chasing) | 12 |
| `SlewF64` | Hard rate-of-change clamp | 3 |
| `WindowedMedianF64` | Robust median filter (outlier-immune) | 132 |

### Statistics

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `WelfordF64` | Online mean, variance, std dev (Chan's merge) | 10 |
| `MomentsF64` | Online skewness & kurtosis (Pébay, 2008). Merge support | 24 |
| `EwmaVarF64` | Exponentially weighted variance | 12 |
| `CovarianceF64` | Online covariance + Pearson correlation | 12 |
| `HarmonicMeanF64` | Correct average for rates/throughputs | 5 |
| `BipowerVariationF64` | Jump-robust volatility (BV vs RV) | TBD |
| `RollSpreadF64` *(std\|libm)* | Implicit bid-ask spread from autocovariance | TBD |
| `TwoScaleRvF64` *(alloc, std\|libm)* | Noise-corrected realized variance | TBD |

### Regression

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `LinearRegressionF64` | Online OLS linear fit (`y = ax + b`) | TBD |
| `EwLinearRegressionF64` | Exponentially-weighted linear fit | TBD |
| `PolynomialRegressionF64` | Online polynomial fit (`.builder().degree(2)`, `.degree(3)`, ...) | TBD |
| `EwPolynomialRegressionF64` | Exponentially-weighted polynomial fit | TBD |
| `ExponentialRegressionF64` | Exponential fit (`y = ae^(bx)`) | TBD |
| `LogarithmicRegressionF64` | Logarithmic fit (`y = a·ln(x) + b`) | TBD |
| `PowerRegressionF64` | Power law fit (`y = ax^b`) | TBD |

### Multi-Armed Bandits *(alloc, std|libm)*

| Type | What It Does | p50 |
|------|-------------|-----|
| `Ucb1F64` | UCB1 — deterministic explore/exploit | TBD |
| `ThompsonBetaF64` | Thompson Sampling — Beta prior for [0,1] rewards | TBD |
| `ThompsonGammaF64` | Thompson Sampling — Gamma prior for positive rewards | TBD |
| `EpsilonGreedyF64` | ε-greedy — simplest bandit baseline | TBD |
| `Exp3F64` | EXP3 — adversarial bandit (no stochastic assumption) | TBD |

### Signal Analysis

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `AutocorrelationF64` | Self-correlation at fixed lag (trending vs reverting) | 12 |
| `CrossCorrelationF64` | Two-stream correlation with lead/lag detection | 39 |

### Information Theory *(std\|libm)*

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `EntropyF64` | Shannon entropy over K categories | 3 |
| `TransferEntropyF64` *(alloc, std\|libm)* | Directed information flow (Granger causality) | 14 |
| `PredictiveInfoBoundF64` *(alloc, std\|libm)* | Binned mutual information I(X;Y) with Miller-Madow | TBD |

### Monitoring

| Type | What It Tracks | p50 |
|------|---------------|-----|
| `DrawdownF64` | Peak-to-trough decline, max drawdown | 5 |
| `RunningMinF64` / `RunningMaxF64` | All-time extrema | 5 |
| `WindowedMaxF64` / `WindowedMinF64` | Sliding window extrema (Nichols'/BBR) | 9 |
| `PeakHoldF64` | Peak envelope with hold + decay | 7 |
| `MaxGaugeF64` | Reset-on-read maximum (Netflix pattern) | 5 |
| `LivenessI64` / `LivenessU64` | Source alive/dead detection | 6 |
| `EventRateU64` | Smoothed events per unit time | 6 |
| `CoDelI64` | Queue backpressure detection (CoDel-inspired) | 7 |
| `SaturationF64` | Resource utilization threshold (USE method) | 6 |
| `ErrorRateF64` | Failure rate with weighted severity | 6 |
| `TrendAlertF64` | Trend direction (Stable/Rising/Falling) | 12 |
| `JitterF64` | Signal variability measurement | 6 |
| `HawkesIntensityF64` *(std\|libm)* | Self-exciting point process intensity | TBD |

### Frequency & Scoring

| Type | What It Tracks | p50 |
|------|---------------|-----|
| `TopK<K, CAP>` | Space-Saving top-K frequent items | 42 |
| `FlexProportionGlobal/Entity` | Per-entity fraction with lazy decay | O(1) |
| `DecayAccumF64` | Event-driven score with time decay | O(1) |

### Utilities

| Type | What It Does | p50 |
|------|-------------|-----|
| `DebounceU32` | N consecutive events before triggering | 2 |
| `DeadBandF64` | Suppress changes below threshold | 2 |
| `HysteresisF64` | Binary decision with different rising/falling thresholds | 3 |
| `BoolWindow` | Sliding pass/fail rate over last N events | 6 |
| `PeakDetectorF64` | Local maxima/minima with prominence | 3 |
| `LevelCrossingF64` | Threshold crossing counter | 2 |
| `FirstDiffF64` | Discrete derivative (rate of change) | 2 |
| `SecondDiffF64` | Discrete acceleration | 2 |

## Type Variants

Explicit concrete types — no generics to fight with. Float types use FMA
intrinsics; integer types use bit-shift arithmetic.

| Algorithm | f32 | f64 | i32 | i64 | i128 |
|-----------|:---:|:---:|:---:|:---:|:----:|
| CUSUM, Drawdown | ✓ | ✓ | ✓ | ✓ | ✓ |
| RunningMin/Max, WindowedMin/Max | ✓ | ✓ | ✓ | ✓ | ✓ |
| SlewLimiter, DeadBand, Hysteresis | ✓ | ✓ | ✓ | ✓ | ✓ |
| PeakHold, PeakDetector, LevelCrossing | ✓ | ✓ | ✓ | ✓ | ✓ |
| FirstDiff, SecondDiff, MOSUM | ✓ | ✓ | ✓ | ✓ | ✓ |
| MaxGauge, CoDel | | | ✓ | ✓ | ✓ |
| EMA, Jitter, AsymEMA | ✓ | ✓ | ✓ | ✓ | |
| Liveness, EventRate | ✓ | ✓ | ✓ | ✓ | |
| Welford, EwmaVar, Covariance, HarmonicMean | ✓ | ✓ | | | |
| Moments, Autocorrelation | ✓ | ✓ | ✓ | ✓ | |
| CrossCorrelation, Entropy | ✓ | ✓ | | | |
| TransferEntropy | | ✓ | | | |
| Holt, KAMA, Kalman1D, Spring | ✓ | ✓ | | | |
| MultiGate, RobustZScore, AdaptiveThreshold | ✓ | ✓ | | | |
| PageHinkley | ✓ | ✓ | | | |
| ADWIN | ✓ | ✓ | | | |
| PredictiveInfoBound | ✓ | ✓ | | | |
| BipowerVariation | ✓ | ✓ | | | |
| RollSpread | ✓ | ✓ | | | |
| TwoScaleRv | | ✓ | | | |
| HawkesIntensity | ✓ | ✓ | | | |
| Saturation, ErrorRate, TrendAlert | ✓ | ✓ | | | |
| ShiryaevRoberts | | ✓ | | | |
| Ucb1, ThompsonBeta, ThompsonGamma, EpsilonGreedy, Exp3 | ✓ | ✓ | | | |

## Common API Patterns

All types follow consistent conventions:

- **Builder pattern** for config-driven types (`CusumF64::builder(target)`)
- **`const fn new()`** for zero-config types (`WelfordF64::new()`)
- **Priming** — returns `None` until `min_samples` reached
- **`is_primed()`** — check if enough data has been seen
- **`count()`** — total samples processed
- **`reset()`** — clear state for operational/admin reset
- **`seed()`** — skip warmup with pre-loaded baseline (CUSUM, EMA, AdaptiveThreshold)
- **`#[must_use]`** — compiler warns if you ignore return values

## Documentation

Comprehensive [documentation](docs/INDEX.md) including:

- [Which algorithm do I need?](docs/guides/choosing.md) — decision tree
- [Quick start recipes](docs/guides/quickstart.md) — copy-paste examples
- [Parameter tuning guide](docs/guides/parameter-tuning.md) — how to set alpha, slack, etc.
- [Composing primitives](docs/guides/composition.md) — building monitors from parts
- 40 algorithm deep-dives with ASCII diagrams, domain examples, and performance data
- 10 use-case guides (latency, backpressure, anomaly detection, feed health, networking, gaming, SRE, capacity planning, industrial, rate management)

## Performance

All measurements in CPU cycles (`rdtsc`), pinned to a single core.
Batch of 64 updates per sample to amortize timing overhead.

```bash
cargo build --release --example perf_stats -p nexus-stats
taskset -c 0 ./target/release/examples/perf_stats
```

## Data Quality & Error Policy

nexus-stats distinguishes two failure categories:

- **Data errors** (NaN, Inf) — All float update methods return `Result<_, DataError>`. The library rejects the input and leaves state unchanged. The caller declares the policy: `.unwrap()` to crash, log and continue, or trigger a circuit breaker.
- **Programmer errors** (wrong dimensions, out-of-range) — The library panics. Fix the code.

The library makes no assumptions about which policy is correct. Each system has different implications.

```rust
// Production: log and continue
if let Err(e) = stats.update(sample) {
    warn!("bad data: {e:?}");
}

// Testing: crash hard
stats.update(sample).unwrap();
```

## Features

| Feature | Default | What |
|---------|---------|------|
| `std` | yes | `WallClock`, hardware intrinsics for `sqrt`/`exp` |
| `libm` | no | Pure Rust math fallback for `no_std` |
| `alloc` | no | Runtime-sized windows (MOSUM, WindowedMedian, KAMA, BoolWindow) |

One of `std` or `libm` must be enabled. Update hot paths never use
transcendentals — `sqrt` and `exp` are only used in queries (`std_dev()`)
and construction (`halflife()`).

## Sub-Crates

nexus-stats is split into five workspace crates for independent compilation and feature gating:

- **nexus-stats-core** — shared traits, error types, clock (`Clock`, `WallClock`, `EpochClock`), and builder infrastructure
- **nexus-stats-smoothing** — EMA, KAMA, Kalman, Holt, Spring, Slew, WindowedMedian
- **nexus-stats-detection** — CUSUM, MOSUM, Shiryaev-Roberts, MultiGate, RobustZScore, AdaptiveThreshold
- **nexus-stats-regression** — Linear, polynomial, exponential, logarithmic, power regression
- **nexus-stats-control** — DeadBand, Hysteresis, Debounce, LevelCrossing, PeakDetector, BoolWindow

The top-level `nexus-stats` crate re-exports everything. Use the sub-crates directly if you only need a subset.

## Trading & Signal Analysis (v4.2)

New primitives for market making, signal quality measurement, and regime detection.
See [`docs/use-cases/trading.md`](docs/use-cases/trading.md) for full guide with examples.

| Use Case | Type | Crate |
|----------|------|-------|
| Market impact | `KyleLambdaF64` | regression |
| Illiquidity | `AmihudF64` | core |
| Bar construction | `BucketAccumulator` | core |
| Signal decay curve | `SignalDecayCurve` | regression |
| Lagged prediction / markout | `LaggedPredictor` | regression |
| Mean-reversion speed | `HalfLifeF64` | core |
| Trending vs mean-reverting | `HurstF64` | core |
| Random walk test | `VarianceRatioF64` | core |
| Distribution change | `DistributionShiftF64` | core |
| Win rate | `HitRateF64` | core |
| Jump-robust volatility | `BipowerVariationF64` | core |
| Implicit spread estimation | `RollSpreadF64` | core |
| Noise-corrected realized vol | `TwoScaleRvF64` | core |
| Bursty event intensity | `HawkesIntensityF64` | core |
| Conditional smoothing | `ConditionalEmaF64` | smoothing |
| Venue selection | `ThompsonBetaF64` / `Ucb1F64` | regression |
| Parameter A/B testing | `Ucb1F64` / `EpsilonGreedyF64` | regression |
| Adversarial strategy | `Exp3F64` | regression |

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT License](LICENSE-MIT) at your option.
