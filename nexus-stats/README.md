# nexus-stats

Fixed-memory, zero-allocation streaming statistics for real-time systems.

Scalar primitives are O(1) per update; window and dimension types
(`WindowedMedian`, `Kama`, `Hampel`, `Bocpd`, `RlsFilter`, `CovarianceMatrix`,
`OnlineKMeans`, `QuantileNorm`) cost O(window) or O(d²) and say so on their
page. Memory is fixed after construction. The crates are `no_std`; types
marked *(alloc)* or *(std|libm)* in the tables below need those features.
Designed for event loops, trading systems, and anywhere you need statistics
without latency jitter.

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` exists only where it has a job.** A type has one when some input can leave it unable to give a right reading until `reset()`. It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.
- **Maxima and minima ignore NaN and accept infinity,** as `f64::max` does.
- **A windowed type with running totals reports its own accuracy.** `update` returns `Accuracy`. A reading that is given is sound. `resync()` is never run for you.
- **Misuse panics.** A wrong dimension or an out-of-range argument to a method is a bug in the calling code.

**Not yet migrated.** These types have not been moved to these guarantees. Most still validate in `update` and return a `Result`. The list shrinks with each release of the 7.0 series.

- `statistics`: `BucketAccumulator`, `CovarianceMatrix`, `FirstDiff`, `Percentile`, `SecondDiff`
- `smoothing`: `Hampel`, `Holt`, `Kama`, `Slew`, `Spring`, `WindowedMedian`
- `monitoring`: `CoDel`, `Drawdown`, `ErrorRate`, `EventRate`, `HawkesIntensity`, `Jitter`, `Liveness`, `PollSaturation`, `SojournSaturation`
- `normalization`: `MinMaxNorm`, `QuantileNorm`
- `trading`: `Cvar`, `KyleLambda`
- `control`, `frequency`: every type
- `detection`, `signal`: every type except `HalfLife` and `Hurst`
- `regression`, `learning`, `estimation`: every type except `HitRate`

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

60+ algorithms across 10 categories. Each type is documented in the crate
docs, and each module's docs say which type to use for what.

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
| `WindowedMax<f64>` / `WindowedMin<f64>` | Sliding window extrema (Nichols'/BBR) | 9 |
| `PeakHold<f64>` | Amplitude tracker: instant attack, hold, decay | 8 |
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
| `Drawdown`, `WindowedMax`, `WindowedMin`, `PeakHold`, `CoDel`, `Jitter` | `monitoring` |
| `DeadBand`, `Hysteresis`, `LevelCrossing`, `PeakDetector` *(control feature)* | `control` |
| `FirstDiff`, `SecondDiff` | `statistics` |
| `Slew`, `WindowedMedian` *(smoothing feature)* | `smoothing` |

On the migrated types (`WindowedMax`, `WindowedMin`, `PeakHold`) there is
one `update` for both. On the others, `update` still returns `Result` on
the `f64` instantiation and the plain value on `i64`.
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

The API docs are the reference for every type. Alongside them, the
[guides and recipes](docs/INDEX.md):

- [Which algorithm do I need?](docs/guides/choosing.md) — decision tree
- [Quick start recipes](docs/guides/quickstart.md) — copy-paste examples
- [Parameter tuning guide](docs/guides/parameter-tuning.md) — how to set alpha, slack, etc.
- [Composing primitives](docs/guides/composition.md) — building monitors from parts
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

nexus-stats is split into workspace crates for independent compilation and feature gating. Every concept lives in one crate, and all of them are on by default:

- **nexus-stats-core** — shared traits, error types, clock (`Clock`, `MonotonicClock`, `EpochClock`), and the descriptive statistics (Welford, Moments, Covariance, Percentile)
- **nexus-stats-smoothing** — EMA, AsymEma, Slew, EwmVar, KAMA, Holt, Spring, HuberEma, Hampel, WindowedMedian
- **nexus-stats-detection** — CUSUM, DistributionShift, MOSUM, Shiryaev-Roberts, MultiGate, RobustZScore, AdaptiveThreshold, and signal analysis (Autocorrelation, Hurst, HalfLife)
- **nexus-stats-regression** — Linear, polynomial, exponential, logarithmic, power regression; learning; Kalman and Bayesian estimation
- **nexus-stats-control** — DeadBand, Hysteresis, Debounce, LevelCrossing, PeakDetector, BoolWindow, and the frequency types
- **nexus-stats-monitoring** — Drawdown, running and windowed extremes, EventRate, ErrorRate, Jitter, Liveness, CoDel, the saturation monitors
- **nexus-stats-normalization** — ZScoreNorm, MinMaxNorm, QuantileNorm
- **nexus-stats-trading** — VarianceRatio, TwoScaleRv, BipowerVariation, Amihud, RollSpread, KyleLambda, Lpm, Cvar

The top-level `nexus-stats` crate re-exports everything. Use the sub-crates directly if you only need a subset.

## Trading & Signal Analysis

Primitives for market making, signal quality measurement, and regime detection.
See [`docs/use-cases/trading.md`](docs/use-cases/trading.md) for full guide with examples.

| Use Case | Type | Crate |
|----------|------|-------|
| Market impact | `KyleLambda` | trading |
| Illiquidity | `Amihud` | trading |
| Bar construction | `BucketAccumulator` | core |
| Signal decay curve | `SignalDecayCurve` | regression |
| Lagged prediction / markout | `LaggedPredictor` | regression |
| Mean-reversion speed | `HalfLife` | detection (`signal`) |
| Trending vs mean-reverting | `Hurst` | detection (`signal`) |
| Random walk test | `VarianceRatio` | trading |
| Distribution change | `DistributionShift` | detection |
| Directional accuracy | `HitRate` | regression |
| Jump-robust volatility | `BipowerVariation` | trading |
| Implicit spread estimation | `RollSpread` | trading |
| Noise-corrected realized vol | `TwoScaleRv` | trading |
| Bursty event intensity | `HawkesIntensity` | monitoring |
| Conditional smoothing | `Ema`, updated only when the condition holds | smoothing |
| Venue selection | `ThompsonBeta` / `Ucb1` | regression |
| Parameter A/B testing | `Ucb1` / `EpsilonGreedy` | regression |
| Adversarial strategy | `Exp3` | regression |

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT License](LICENSE-MIT) at your option.
