# nexus-stats

Fixed-memory, zero-allocation streaming statistics for real-time systems.

Scalar primitives are O(1) per update; window and dimension types
(`WindowedMedian`, `Kama`, `Hampel`, `Bocpd`, `RlsFilter`, `CovarianceMatrix`,
`OnlineKMeans`, `QuantileNorm`) cost O(window) or O(d²) and say so on their
page. Memory is fixed after construction. The crates are `no_std`; types
marked *(alloc)* or *(std|libm)* in the tables below need those features.
Designed for event loops, trading systems, and anywhere you need statistics
without latency jitter.

## Quick Start

```rust
use nexus_stats::{Direction, detection::Cusum, smoothing::Ema, statistics::Welford};

// Detect latency shifts with CUSUM
let mut cusum = Cusum::builder(100.0)  // target: 100μs baseline
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
let mut ema = Ema::builder()
    .span(20)          // ~20-sample smoothing window
    .min_samples(10)
    .build().unwrap();

if let Some(smoothed) = ema.update(sample) {   // unchecked; see checked_update
    // use smoothed value
}

// Track running statistics with Welford
let mut stats = Welford::new();
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
| `Cusum` | Persistent mean shifts (up or down) | 6 |
| `Mosum` | Transient spikes within a window | 5 |
| `ShiryaevRoberts` | Mean shifts with optimal detection delay | 18 |
| `MultiGate` | Graded anomalies: Accept/Unusual/Suspect/Reject | 8 |
| `RobustZScore<f64>` | MAD-based outlier scoring with estimator freeze | 8 |
| `AdaptiveThreshold` | Z-score anomalies with self-learning baseline | 7 |
| `PageHinkley` | Sequential mean drift (Page-Hinkley test) | 6 |
| `Adwin` | Adaptive window distribution change (ADWIN) | 63 |
| `Bocpd` | Bayesian online change-point detection, run-length posterior (max run 64) | 3637 |

### Smoothing & Filtering

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `Ema` | Exponential moving average | 5 |
| `AsymEma` | Different alpha for rising vs falling | 12 |
| `Kama` | Kaufman adaptive MA (adapts to trend/noise) | 15 |
| `Kalman1d` | 1D Kalman filter with velocity tracking | 26 |
| `Holt` | Double exponential (level + trend) | 11 |
| `Spring` | Critically damped spring (smooth target chasing) | 13 |
| `Slew<f64>` | Hard rate-of-change clamp | 8 |
| `WindowedMedian<f64>` | Robust median filter (outlier-immune) | 80 |

### Statistics

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `Welford` | Online mean, variance, std dev (Chan's merge) | 13 |
| `Moments` | Online skewness & kurtosis (Pébay, 2008). Merge support | 17 |
| `EwmVar` | Exponentially weighted variance | 7 |
| `Covariance` | Online covariance + Pearson correlation | 11 |
| `HarmonicMean` | Correct average for rates/throughputs | 6 |
| `BipowerVariation` *(std\|libm)* | Jump-robust volatility (BV vs RV) | 22 |
| `RollSpread` *(std\|libm)* | Implicit bid-ask spread from autocovariance | 21 |
| `TwoScaleRv` *(alloc, std\|libm)* | Noise-corrected realized variance | 7 |

### Regression

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `LinearRegression` | Online OLS linear fit (`y = ax + b`) | 7 |
| `EwLinearRegression` | Exponentially-weighted linear fit | 7 |
| `PolynomialRegression` | Online polynomial fit (`.builder().degree(2)`, `.degree(3)`, ...) | 17 |
| `EwPolynomialRegression` | Exponentially-weighted polynomial fit | 17 |
| `ExponentialRegression` | Exponential fit (`y = ae^(bx)`) | 19 |
| `LogarithmicRegression` | Logarithmic fit (`y = a·ln(x) + b`) | 17 |
| `PowerRegression` | Power law fit (`y = ax^b`) | 27 |

### Multi-Armed Bandits *(alloc, std|libm)*

| Type | What It Does | p50 (`select`, 10 arms) |
|------|-------------|-----|
| `Ucb1` | UCB1 — deterministic explore/exploit | 74 |
| `ThompsonBeta` | Thompson Sampling — Beta prior for [0,1] rewards | 1101 |
| `ThompsonGamma` | Thompson Sampling — Gamma prior for positive rewards | 557 |
| `EpsilonGreedy` | ε-greedy — simplest bandit baseline | 33 |
| `Exp3` | EXP3 — adversarial bandit (no stochastic assumption) | 186 |

### Signal Analysis

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `Autocorrelation` | Self-correlation at fixed lag (trending vs reverting) | 12 |
| `CrossCorrelation` | Two-stream correlation with lead/lag detection | 28 |

### Information Theory *(std\|libm)*

| Type | What It Computes | p50 |
|------|-----------------|-----|
| `Entropy` | Shannon entropy over K categories | 4 |
| `TransferEntropy` *(alloc, std\|libm)* | Directed information flow (Granger causality) | 13 |
| `PredictiveInfoBound` *(alloc, std\|libm)* | Binned mutual information I(X;Y) with Miller-Madow | 23 |

### Monitoring

| Type | What It Tracks | p50 |
|------|---------------|-----|
| `Drawdown<f64>` | Peak-to-trough decline, max drawdown | 5 |
| `RunningMin<f64>` / `RunningMax<f64>` | All-time extrema | 5 |
| `WindowedMax<f64>` / `WindowedMin<f64>` | Sliding window extrema (Nichols'/BBR) | 9 |
| `PeakHold<f64>` | Peak envelope with hold + decay | 8 |
| `MaxGauge<f64>` | Reset-on-read maximum (Netflix pattern) | 6 |
| `Liveness` | Source alive/dead detection | 7 |
| `EventRate` | Smoothed events per unit time | 7 |
| `CoDel<i64>` | Queue backpressure detection (CoDel-inspired) | 5 |
| `PollSaturation` | Consumer-side saturation from poll outcomes: `on_work` / `on_idle` | 6 / 1 |
| `SojournSaturation` | Consumer saturation from stamped queue sojourn, exact per message | 7 |
| `ErrorRate` | Failure rate with weighted severity | 7 |
| `TrendAlert` | Trend direction (Stable/Rising/Falling) | 10 |
| `Jitter<f64>` | Signal variability measurement | 7 |
| `HawkesIntensity` *(std\|libm)* | Self-exciting point process intensity | 15 |

### Frequency & Scoring

| Type | What It Tracks | p50 |
|------|---------------|-----|
| `TopK<K>` *(alloc)* | Space-Saving top-K frequent items | 36 |
| `FlexProportionGlobal` / `FlexProportionLocal` | Each key's share of a decaying event count | 4 |
| `DecayAccum` | Event-driven score with time decay (`u64` ticks) | O(1) |

### Utilities

| Type | What It Does | p50 |
|------|-------------|-----|
| `Debounce` | N consecutive events before triggering | 5 |
| `DeadBand<f64>` | Suppress changes below threshold | 4 |
| `Hysteresis<f64>` | Binary decision with different rising/falling thresholds | 2 |
| `BoolWindow` | Sliding pass/fail rate over last N events | 5 |
| `PeakDetector<f64>` | Local maxima/minima with prominence | 3 |
| `LevelCrossing<f64>` | Threshold crossing counter | 3 |
| `FirstDiff<f64>` | Discrete derivative (rate of change) | 6 |
| `SecondDiff<f64>` | Discrete acceleration | 6 |

## Numeric Types

No numeric suffixes. A type whose algorithm exists for one numeric type is
named plainly and is `f64` (`Ema`, `Welford`, `Cusum`, ...). The cheap
primitives that also make sense on integers are one generic type over the
sealed `Sample` trait, instantiated for `f64` and `i64`:

| Generic over `Sample` (`f64`, `i64`) | Module |
|--------------------------------------|--------|
| `Drawdown`, `RunningMax`, `RunningMin`, `WindowedMax`, `WindowedMin`, `MaxGauge`, `PeakHold`, `CoDel`, `Jitter` | `monitoring` |
| `DeadBand`, `Hysteresis`, `LevelCrossing`, `FirstDiff`, `SecondDiff`, `PeakDetector` *(control feature)* | `control` |
| `Slew`, `WindowedMedian` *(smoothing feature)* | `smoothing` |

`update` returns `Result` on the `f64` instantiation (NaN and infinity are
rejected) and the plain value on `i64`, where there is nothing to reject.
Constructors are shared, so name the type once: `Drawdown::<i64>::new()`,
`CoDel::<i64>::builder()`, `let dd: Drawdown<f64> = Drawdown::new()`.

The normalizers (`ZScoreNorm`, `MinMaxNorm`, `QuantileNorm`) and
`RobustZScore` are generic over `Float` (`f64`, `f32`): they take and return
`T` but accumulate in `f64`, so the `f32` form is a boundary type for `f32`
feature vectors. Time-aware types (`Liveness`, `EventRate`, `PollSaturation`,
`SojournSaturation`, `DecayAccum`, the windowed extrema's timestamps) take
`u64` ticks in any unit; `clock::MonotonicClock` is the `std` bridge from
`Instant`. The full table is [`docs/reference/type-matrix.md`](docs/reference/type-matrix.md);
upgrading from 6.x: [`docs/guides/migrating-to-7.md`](docs/guides/migrating-to-7.md).

## Common API Patterns

All types follow consistent conventions:

- **Builder pattern** for config-driven types (`Cusum::builder(target)`)
- **`const fn new()`** for zero-config types (`Welford::new()`)
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
- 53 algorithm deep-dives with ASCII diagrams, domain examples, and performance data
- 12 use-case guides (latency, backpressure, anomaly detection, feed health, consumer saturation, rate management, capacity planning, gaming, networking, industrial, SRE, trading)
- [Migrating to 7.0](docs/guides/migrating-to-7.md) — the 6.x → 7.0 rename map, the generics' caller rules, removed types, behavior changes

## Performance

All measurements are `rdtsc` ticks per update on an Intel Core Ultra 7 165U,
pinned to a P-core (`taskset -c 0`) with turbo on, best of three runs, batch of
64 updates per sample to amortize timing overhead. A developer laptop, not a
perf lab: read them as estimates of relative cost, taken the same way as every
earlier number here. Built for the default x86_64 target, where
multiply-adds are computed as `a * b + c`; with `-C target-cpu=native` (or
`+fma`) they become single FMA instructions, which changes results in the
last bit and costs about the same. Full tables,
including p99:
[`docs/reference/performance.md`](docs/reference/performance.md).

```bash
cargo build --release --example perf_stats -p nexus-stats
taskset -c 0 ./target/release/examples/perf_stats
```

## Data Quality & Error Policy

nexus-stats distinguishes two failure categories:

- **Data errors** (NaN, Inf): the validating method returns `Result<_, DataError>`, rejects the input and leaves state unchanged. The caller declares the policy: `.unwrap()` to crash, log and continue, or trigger a circuit breaker. The types are moving one at a time to the standard library's `+` / `checked_add` shape: on a moved type (the migration guide lists them) the validating method is `checked_update`, and `update` does the arithmetic without validating (IEEE 754). On the others `update` itself validates and returns the `Result`.
- **Programmer errors** (wrong dimensions, out-of-range) — The library panics. Fix the code.

The library makes no assumptions about which policy is correct. Each system has different implications.

```rust
// Production: log and continue
if let Err(e) = stats.checked_update(sample) {
    warn!("bad data: {e:?}");
}

// Testing: crash hard
stats.checked_update(sample).unwrap();
```

## Features

| Feature | Default | What |
|---------|---------|------|
| `std` | yes | `MonotonicClock`, hardware intrinsics for `sqrt`/`exp`; implies `alloc` |
| `libm` | no | Pure Rust math fallback for `no_std` |
| `alloc` | no (implied by `std`) | Runtime-sized tables (Mosum, WindowedMedian, Kama, BoolWindow, TopK), adaptive filters, optimizers |

One of `std` or `libm` must be enabled. Update hot paths never use
transcendentals — `sqrt` and `exp` are only used in queries (`std_dev()`)
and construction (`halflife()`).

## Sub-Crates

nexus-stats is split into five workspace crates for independent compilation and feature gating:

- **nexus-stats-core** — shared traits, error types, clock (`Clock`, `MonotonicClock`, `EpochClock`), and builder infrastructure
- **nexus-stats-smoothing** — EMA, KAMA, Kalman, Holt, Spring, Slew, WindowedMedian
- **nexus-stats-detection** — CUSUM, MOSUM, Shiryaev-Roberts, MultiGate, RobustZScore, AdaptiveThreshold
- **nexus-stats-regression** — Linear, polynomial, exponential, logarithmic, power regression
- **nexus-stats-control** — DeadBand, Hysteresis, Debounce, LevelCrossing, PeakDetector, BoolWindow

The top-level `nexus-stats` crate re-exports everything. Use the sub-crates directly if you only need a subset.

## Trading & Signal Analysis

Primitives for market making, signal quality measurement, and regime detection.
See [`docs/use-cases/trading.md`](docs/use-cases/trading.md) for full guide with examples.

| Use Case | Type | Crate |
|----------|------|-------|
| Market impact | `KyleLambda` | regression |
| Illiquidity | `Amihud` | core |
| Bar construction | `BucketAccumulator` | core |
| Signal decay curve | `SignalDecayCurve` | regression |
| Lagged prediction / markout | `LaggedPredictor` | regression |
| Mean-reversion speed | `HalfLife` | core |
| Trending vs mean-reverting | `Hurst` | core |
| Random walk test | `VarianceRatio` | core |
| Distribution change | `DistributionShift` | core |
| Directional accuracy | `HitRate` | core |
| Jump-robust volatility | `BipowerVariation` | core |
| Implicit spread estimation | `RollSpread` | core |
| Noise-corrected realized vol | `TwoScaleRv` | core |
| Bursty event intensity | `HawkesIntensity` | core |
| Conditional smoothing | `Ema`, updated only when the condition holds | core |
| Venue selection | `ThompsonBeta` / `Ucb1` | regression |
| Parameter A/B testing | `Ucb1` / `EpsilonGreedy` | regression |
| Adversarial strategy | `Exp3` | regression |

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT License](LICENSE-MIT) at your option.
