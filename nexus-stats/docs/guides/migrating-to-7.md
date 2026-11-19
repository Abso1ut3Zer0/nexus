# Migrating to nexus-stats 7

7.0 is one change applied everywhere: **one naming convention**. The numeric
suffix (`F64`, `I64`, `U64`, `F32`) is gone from every type and builder name.
Where an algorithm existed for one numeric type, the name is the algorithm
(`EmaF64` → `Ema`). Where it existed for two, the two types are one generic
type (`DrawdownF64` / `DrawdownI64` → `Drawdown<f64>` / `Drawdown<i64>`). A
few callerless types are removed. The crates move together:

| Crate | 6.x | 7.0 |
|-------|-----|-----|
| `nexus-stats` (umbrella) | 6.x | 7.0 |
| `nexus-stats-core` | 3.x | 4.0 |
| `nexus-stats-smoothing`, `-detection`, `-control`, `-regression` | 2.x | 3.0 |

Most of the migration is search and replace. The tables below are the
complete map (generated from the inventory; nothing is renamed that is not
listed here). The sections after them cover the generics' two caller rules
and the behavior changes that are not renames.

## 1. Renames

The algorithm existed for one numeric type; the suffix carried no
information. Builders follow their type: `EmaF64Builder` → `EmaBuilder`,
`HoltF64Builder` → `HoltBuilder`. Import lists shrink the same way:
`use nexus_stats::smoothing::EmaF64;` → `use nexus_stats::smoothing::Ema;`.

### nexus-stats-core

| 6.x | 7.0 |
|-----|-----|
| `AmihudF64` | `Amihud` |
| `AsymEmaF64` | `AsymEma` |
| `BipowerVariationF64` | `BipowerVariation` |
| `CovarianceF64` | `Covariance` |
| `CusumF64` | `Cusum` |
| `CvarF64` | `Cvar` |
| `DebounceU64` | `Debounce` |
| `DistributionShiftF64` | `DistributionShift` |
| `EmaF64` | `Ema` |
| `ErrorRateF64` | `ErrorRate` |
| `EventRateU64` | `EventRate` |
| `EwmaVarF64` | `EwmaVar` |
| `HalfLifeF64` | `HalfLife` |
| `HarmonicMeanF64` | `HarmonicMean` |
| `HawkesIntensityF64` | `HawkesIntensity` |
| `HitRateF64` | `HitRate` |
| `HurstF64` | `Hurst` |
| `LivenessU64` | `Liveness` |
| `LpmF64` | `Lpm` |
| `MomentsF64` | `Moments` |
| `OnlineCovarianceF64` | `CovarianceMatrix` |
| `WallClock` | `MonotonicClock` |
| `CoDelBuilder::window(n)` | `interval(n)` |
| `BucketPolicy::WallTimeNanos(n)` | `BucketPolicy::Ticks(n)` |
| `BucketAccumulator::update_at_raw(v, t)` | `update_at(v, t)` |
| `PercentileF64` | `Percentile` |
| `RollSpreadF64` | `RollSpread` |
| `TwoScaleRvF64` | `TwoScaleRv` |
| `VarianceRatioF64` | `VarianceRatio` |
| `WelfordF64` | `Welford` |

### nexus-stats-smoothing

| 6.x | 7.0 |
|-----|-----|
| `ConditionalEmaF64` | `ConditionalEma` |
| `HampelF64` | `Hampel` |
| `HoltF64` | `Holt` |
| `HuberEmaF64` | `HuberEma` |
| `Kalman1dF64` | `Kalman1d` |
| `KamaF64` | `Kama` |
| `SpringF64` | `Spring` |

### nexus-stats-detection

| 6.x | 7.0 |
|-----|-----|
| `AdaptiveThresholdF64` | `AdaptiveThreshold` |
| `AdwinF64` | `Adwin` |
| `AutocorrelationF64` | `Autocorrelation` |
| `BocpdF64` | `Bocpd` |
| `CrossCorrelationF64` | `CrossCorrelation` |
| `DistDriftF64` | `DistDrift` |
| `EntropyF64` | `Entropy` |
| `MosumF64` | `Mosum` |
| `MultiGateF64` | `MultiGate` |
| `PageHinkleyF64` | `PageHinkley` |
| `PredictiveInfoBoundF64` | `PredictiveInfoBound` |
| `ShiryaevRobertsF64` | `ShiryaevRoberts` |
| `TransferEntropyF64` | `TransferEntropy` |
| `TrendAlertF64` | `TrendAlert` |

### nexus-stats-control

| 6.x | 7.0 |
|-----|-----|
| `DecayAccumU64` | `DecayAccum` |
| `TopK::total()` | `TopK::count()` |
| `TopK::top(&mut buf) -> usize` | `TopK::top() -> impl ExactSizeIterator<Item = Counter<'_, K>>` (`key`, `count`, `error`, `guaranteed()`), a view of the sorted table; `top().take(k)` is the top k; `guaranteed_top()` says how many leading ranks are exact. `K: Eq + Hash` (was `Eq + Clone`) |

### nexus-stats-regression

| 6.x | 7.0 |
|-----|-----|
| `AdaGradF64` | `AdaGrad` |
| `AdamF64` | `Adam` |
| `BetaBinomialF64` | `BetaBinomial` |
| `CoefficientsF64` | `Coefficients` |
| `EpsilonGreedyF64` | `EpsilonGreedy` |
| `EwExponentialRegressionF64` | `EwExponentialRegression` |
| `EwLinearRegressionF64` | `EwLinearRegression` |
| `EwLogarithmicRegressionF64` | `EwLogarithmicRegression` |
| `EwPolynomialRegressionF64` | `EwPolynomialRegression` |
| `EwPowerRegressionF64` | `EwPowerRegression` |
| `Exp3F64` | `Exp3` |
| `ExponentialRegressionF64` | `ExponentialRegression` |
| `GammaPoissonF64` | `GammaPoisson` |
| `HuberRegressionF64` | `HuberRegression` |
| `Kalman2dF64` | `Kalman2d` |
| `Kalman3dF64` | `Kalman3d` |
| `KyleLambdaF64` | `KyleLambda` |
| `LinearRegressionF64` | `LinearRegression` |
| `LmsFilterF64` | `LmsFilter` |
| `LogarithmicRegressionF64` | `LogarithmicRegression` |
| `LogisticRegressionF64` | `LogisticRegression` |
| `NlmsFilterF64` | `NlmsFilter` |
| `OnlineGdF64` | `OnlineGd` |
| `OnlineKMeansF64` | `OnlineKMeans` |
| `PolynomialRegressionF64` | `PolynomialRegression` |
| `PowerRegressionF64` | `PowerRegression` |
| `RlsFilterF64` | `RlsFilter` |
| `ThompsonBetaF64` | `ThompsonBeta` |
| `ThompsonGammaF64` | `ThompsonGamma` |
| `Ucb1F64` | `Ucb1` |
| `intercept_value()` (linear, EW and transformed regressions) | `intercept()` |
| `total_pulls()` on the bandits | `count()` |

## 2. Pairs become one generic type

Where the `F64` and `I64` (or `F64` and `F32`) forms were the same algorithm,
there is now one type, generic over a sealed trait: `Sample` for `f64` /
`i64`, `Float` for `f64` / `f32`. Builders follow: `CoDelF64Builder` /
`CoDelI64Builder` → `CoDelBuilder<f64>` / `CoDelBuilder<i64>`.

| 6.x | 7.0 | Bound | Crate |
|-----|-----|-------|-------|
| `CoDelF64` / `CoDelI64` | `CoDel<f64>` / `CoDel<i64>` | `Sample` | nexus-stats-core |
| `DeadBandF64` / `DeadBandI64` | `DeadBand<f64>` / `DeadBand<i64>` | `Sample` | nexus-stats-core |
| `DrawdownF64` / `DrawdownI64` | `Drawdown<f64>` / `Drawdown<i64>` | `Sample` | nexus-stats-core |
| `FirstDiffF64` / `FirstDiffI64` | `FirstDiff<f64>` / `FirstDiff<i64>` | `Sample` | nexus-stats-core |
| `HysteresisF64` / `HysteresisI64` | `Hysteresis<f64>` / `Hysteresis<i64>` | `Sample` | nexus-stats-core |
| `JitterF64` / `JitterI64` | `Jitter<f64>` / `Jitter<i64>` | `Sample` | nexus-stats-core |
| `LevelCrossingF64` / `LevelCrossingI64` | `LevelCrossing<f64>` / `LevelCrossing<i64>` | `Sample` | nexus-stats-core |
| `MaxGaugeF64` / `MaxGaugeI64` | `MaxGauge<f64>` / `MaxGauge<i64>` | `Sample` | nexus-stats-core |
| `MinMaxNormF64` / `MinMaxNormF32` | `MinMaxNorm<f64>` / `MinMaxNorm<f32>` | `Float` | nexus-stats-core |
| `PeakHoldF64` / `PeakHoldI64` | `PeakHold<f64>` / `PeakHold<i64>` | `Sample` | nexus-stats-core |
| `QuantileNormF64` / `QuantileNormF32` | `QuantileNorm<f64>` / `QuantileNorm<f32>` | `Float` | nexus-stats-core |
| `RunningMaxF64` / `RunningMaxI64` | `RunningMax<f64>` / `RunningMax<i64>` | `Sample` | nexus-stats-core |
| `RunningMinF64` / `RunningMinI64` | `RunningMin<f64>` / `RunningMin<i64>` | `Sample` | nexus-stats-core |
| `SecondDiffF64` / `SecondDiffI64` | `SecondDiff<f64>` / `SecondDiff<i64>` | `Sample` | nexus-stats-core |
| `SlewF64` / `SlewI64` | `Slew<f64>` / `Slew<i64>` | `Sample` | nexus-stats-core |
| `WindowedMaxF64` / `WindowedMaxI64` | `WindowedMax<f64>` / `WindowedMax<i64>` | `Sample` | nexus-stats-core |
| `WindowedMinF64` / `WindowedMinI64` | `WindowedMin<f64>` / `WindowedMin<i64>` | `Sample` | nexus-stats-core |
| `ZScoreNormF64` / `ZScoreNormF32` | `ZScoreNorm<f64>` / `ZScoreNorm<f32>` | `Float` | nexus-stats-core |
| `WindowedMedianF64` / `WindowedMedianI64` | `WindowedMedian<f64>` / `WindowedMedian<i64>` | `Sample` | nexus-stats-smoothing |
| `RobustZScoreF64` / `RobustZScoreF32` | `RobustZScore<f64>` / `RobustZScore<f32>` | `Float` | nexus-stats-detection |
| `PeakDetectorF64` / `PeakDetectorI64` | `PeakDetector<f64>` / `PeakDetector<i64>` | `Sample` | nexus-stats-control |

The body is written once; methods whose signature differs by type are
implemented per instantiation, so `Drawdown<f64>::update` still returns
`Result<f64, DataError>` (NaN and infinity rejected) and
`Drawdown<i64>::update` still returns `i64`. The arithmetic is unchanged and
the codegen is cycle-identical to 6.x (verified against the perf harness and
the disassembly).

Two rules fall out of the shared constructors:

1. **Name `T` at construction.** Constructors and builders live on the
   generic type, so `Drawdown::new()` alone is ambiguous. Write
   `Drawdown::<i64>::new()`, `CoDel::<i64>::builder()`, or annotate the
   binding: `let dd: Drawdown<f64> = Drawdown::new();`.
2. **`T` must be known before the first `update`.** There are two `update`s,
   one per instantiation; inference cannot pick one from the sample alone
   while the binding is still untyped. In practice rule 1 covers this.

```rust
// 6.x
use nexus_stats::monitoring::{DrawdownI64, WindowedMaxF64};
let mut dd = DrawdownI64::new();
let mut wm = WindowedMaxF64::new(1_000_000).unwrap();

// 7.0
use nexus_stats::monitoring::{Drawdown, WindowedMax};
let mut dd = Drawdown::<i64>::new();
let mut wm = WindowedMax::<f64>::new(1_000_000).unwrap();
dd.update(42);                       // i64: plain value
wm.update(now, 3.5).unwrap();        // f64: Result
```

Code that works over both forms names the bound:
`fn drain<T: Sample>(dd: &mut Drawdown<T>)`. Through the bound you can call
the shared surface (constructors, builders, `count`, `is_primed`, `reset`,
the getters); `update` and the other per-instantiation methods need a
concrete `T`, since their signatures differ. `Sample` and `Float` are
exported from `nexus_stats` and `nexus_stats_core`; they are sealed (`f64` /
`i64` and `f64` / `f32` only), so you name them, you never implement them.

What the merge adds: `WindowedMedian<i64>` gains `quantile`, `mad`, `iqr` and
`modified_z_score` (they were `f64` only); `Jitter<i64>` gains
`jitter_ratio()`. `Jitter` has one builder for both: `span` on both,
`alpha` / `halflife` on `f64` only, `effective_span()` on `i64` only.

### `Float` generics have `f64` internals

`ZScoreNorm<f32>`, `MinMaxNorm<f32>`, `QuantileNorm<f32>` and
`RobustZScore<f32>` take and return `f32` but accumulate in `f64`: they are
boundary types for `f32` feature vectors, no longer `f32` accumulators.
Results may differ from 6.x in the last bits (for the better); if you relied
on `f32` accumulation for speed, measure: the hot path gains a convert.

## 3. Removed

| 6.x | Use instead |
|-----|-------------|
| `SaturationF64` | `Ema` on the utilization fraction and compare against your threshold (it was exactly that, with an unvalidated threshold), or `PollSaturation` / `SojournSaturation` for a consumer thread's own saturation ([#761](https://github.com/Abso1ut3Zer0/nexus/issues/761)) |
| `LivenessF64`, `LivenessI64` | `Liveness` (`u64` ticks; cast `i64` stamps at the call site) |
| `EventRateI64` | `EventRate` (`u64` ticks) |
| `MosumI64` | `Mosum` on `f64` ([#379](https://github.com/Abso1ut3Zer0/nexus/issues/379)) |
| `AutocorrelationI64` | `Autocorrelation` on `f64` (correlation is fractional) ([#379](https://github.com/Abso1ut3Zer0/nexus/issues/379)) |
| `DecayAccumF64` | `DecayAccum` (`u64` ticks) |
| `update_i64(timestamp, ..)` on `WindowedMax`, `WindowedMin`, `CoDel` | `update(timestamp as u64, ..)` |
| `HalfLifeBuilder` | `HalfLife::new()` (the builder had no knobs) |
| `CoDel::min_sojourn()` | the detector no longer keeps a windowed minimum (it implements RFC 8289 directly); keep a `WindowedMin<i64>` beside it if you report one |

## 4. Behavior changes

- **`DeadBand<T>::new(threshold)` returns `Result<_, ConfigError>`** and
  rejects a negative or non-finite threshold. `DeadBand<i64>` takes an `i64`
  threshold (was `u64`); the `abs_diff` arithmetic is the same.
- **`PeakHold<T>`**: after the hold expires, a sample *equal* to the decayed
  peak restarts the hold (`>=`, was `>`).
- **`Slew<f64>`** clamps with `max().min()` instead of `clamp()`: identical
  for finite inputs, without the `lo <= hi` assertion.
- **Normalizers** accumulate in `f64` for both `T` (above).
- **`FlexProportionEntity` is `FlexProportionLocal`**, the kernel's name, and
  the protocol changed with the algorithm fix below: `global.update(&mut
  local)` records an event (one call, was `global.update()` plus
  `local.update(global.period())`), and `local.fraction(&global)` reads the
  share (was `local.fraction(global.total(), global.period())`). The global's
  `total()` is `events()`.
- **`TopK<K, CAP>` is `TopK<K>`** with the capacity given at construction:
  `TopK::new(capacity)` returns `Result` (zero is rejected), `capacity()`
  reads it back, and the `Default` impl is gone. The table is one boxed
  slice allocated in `new`, so `TopK` now needs the `alloc` feature, like
  every other runtime-sized type. The last const generic in the family.

Fixes in the same release that change reported numbers, each with its own
CHANGELOG entry in `nexus-stats-core`:

- `WindowedMin` / `WindowedMax` are now a literal port of the kernel's
  `win_minmax`; the old code disagreed with an exact window on 11 to 22% of
  updates on stationary input ([#758](https://github.com/Abso1ut3Zer0/nexus/issues/758)).
- `CoDel` implements RFC 8289's `first_above_time` rule and no longer reports
  `Degraded` on a single sample above target ([#759](https://github.com/Abso1ut3Zer0/nexus/issues/759)).
- `Liveness::update` could never report dead once `deadline_multiple >= 2^k`
  and ignored the absolute deadline when both were configured
  ([#760](https://github.com/Abso1ut3Zer0/nexus/issues/760)).
- `PeakHold<f64>` seeds from the first sample (a negative-only stream reported
  `0.0`); `Jitter<f64>` honors a seed under `min_samples(1)`
  ([#763](https://github.com/Abso1ut3Zer0/nexus/issues/763)).
- `FlexProportion` shares no longer decay toward zero: the global count now
  halves at every period like the locals do, as in the kernel. A key with
  every event reads 1.0 instead of 0.5 after one half-life.

### Construction validation (code-quality audit, second PR)

- Builders reject NaN and infinite parameters everywhere; the old `x <= 0.0`
  tests let NaN through (Cusum, MultiGate, RobustZScore, AdaptiveThreshold,
  Mosum, ShiryaevRoberts, LMS/NLMS, RLS, Kalman2d/3d, logistic regression).
- `min_samples(0)` is rejected (`is_primed()` was true before any sample and
  getters reported `Some(0.0)`): Ema, EwmaVar, BipowerVariation, Lpm,
  RollSpread, Holt, HuberEma, Kalman1d; `Jitter` needs 2 unseeded.
- Fallible constructors return `Result<_, ConfigError>` instead of panicking or
  returning a bare type: `WindowedMedian::new`, `LevelCrossing::new`,
  `DistributionShiftBuilder::build`, `BipowerVariationBuilder::build`,
  `Welford::from_parts`, `Cusum::reset_with_target`. Infallible builders stay
  bare; that is the rule.
- EW regressions reject `alpha >= 1 / (number of coefficients)`: such a fit
  could never prime (`effective_n` approaches `1/alpha` from below).
- `RlsFilter`'s `max_covariance` must be finite and above `initial_covariance`.

### Data policy

- `DataError::OutOfRange` is new: `HarmonicMean::update` returns it for a
  non-positive sample instead of panicking; ThompsonBeta/Exp3 use it for a
  reward outside `[0, 1]` (and Exp3 for `prob` outside `(0, 1]`),
  ThompsonGamma for a non-positive reward. `Negative` is kept for strictly
  negative inputs (Amihud volume, GammaPoisson exposure).
- `HitRate::hit_rate` / `ew_hit_rate` and `Amihud::illiq` return `Option<f64>`
  (`None` before any observation; a rate over nothing is not zero).
- Float *slices* (features, observation vectors) are the caller's to validate:
  `debug_assert!`ed only, as in every mainstream numeric library.

### Numerics

- `PolynomialRegression` / `EwPolynomialRegression` judge singularity relative
  to the matrix scale and never return NaN coefficients; `LinearRegression` /
  `EwLinearRegression` keep means and co-moments instead of raw power sums,
  so a large x or y offset (unix timestamps, a price level) no longer
  cancels, and return `None` for constant x instead of a rounding-noise
  slope.
- `ShiryaevRoberts` saturates its statistic at `1e300` instead of overflowing
  to `+inf`, turning NaN and reporting `false` forever.
- `RobustZScore` scales by `sqrt(2/π)` (its spread is a *mean* absolute
  deviation, not a median one); `mad()` is `mean_abs_dev()`.
- `PredictiveInfoBound` applies the Miller-Madow correction with the right
  sign (`(Kx + Ky - Kxy - 1) / 2N`, usually negative).
- ThompsonBeta/ThompsonGamma decay toward the prior, not toward zero, so an
  un-pulled arm never degenerates; `beta_sample` has no `0.5` sentinel.
- Kalman2d/3d: a non-positive innovation covariance restores P and skips the
  measurement instead of applying a `1/EPSILON` gain; P is re-symmetrized
  after every update. `RlsFilter` does the same for its denominator.
- `EventRate` re-anchors on a backwards timestamp like `Liveness` does.
- `AdaptiveThreshold::seed(mean, std_dev)` now seeds the spread estimate
  (the `std_dev` was stored and ignored).
- `Hurst` primes at its configured window, not at a fixed 20 samples.

### Surface consistency (code-quality audit, fourth PR)

- **`Adwin::update` / `PageHinkley::update` return `Result<Option<bool>, _>`:**
  `Ok(None)` while priming, `Ok(Some(changed))` after. Replace
  `if det.update(x)? {` with `if det.update(x)? == Some(true) {`.
- **`Debounce::count()` is the number of updates.** The consecutive-`true`
  run that `update` compares to the threshold is `consecutive()`; rename
  that call.
- **`Exp3::select` takes `&mut self`** (it fills a scratch buffer); bind the
  bandit mutably. `Exp3` is `Sync` and `Clone` now.
- Additive, no action needed: `count()` / `is_primed()` on 24 more types,
  `halflife(h)` on every builder that has `alpha(a)`,
  `Covariance::variance_x` / `variance_y`, `Coefficients::eval`, and a
  `libm` feature on `nexus-stats-smoothing` (the umbrella forwards it).

### Core foundations (blind audit, PR C1)

- **`LevelCrossing::update` returns the direction.** `Result<Option<Direction>, _>`
  for `f64`, `Option<Direction>` for `i64`: `Some(Rising)` / `Some(Falling)`
  on a crossing, `None` otherwise. Replace `if lc.update(x)? {` with
  `if lc.update(x)?.is_some() {`. A sample exactly on the threshold is no
  longer "above": touching the threshold and going back is not a crossing.
- **A seed is a value, not samples** (`Ema`, `Cusum`). `count()` starts at 0
  on a seeded instance instead of at `min_samples`, and `reset()` returns to
  the seed instead of discarding it. Code that read `count()` to mean
  "primed" should call `is_primed()`.
- **`Cusum` seeds must be non-negative**, and `Cusum::builder(0.0)` without
  explicit thresholds is rejected at `build()` with the message that names
  the cause. When both sides are over threshold the side further over is
  reported (it was always `Rising`).
- **`Slew::value()` returns `Option<T>`**: `None` before the first sample
  (it was a fabricated 0).
- **`Ema::builder().span(n)` needs `n >= 2`** and `.halflife(h)` a positive
  finite `h`; the error names the knob that was set. `AsymEma`'s
  `span_up(n)` / `span_down(n)` need `n >= 2` as well, and it rejects
  `min_samples(0)`.
- **`SecondDiff<f64>`** is computed as the difference of first differences;
  results can differ from 7.0 pre-releases in the last bit.
- **`Hysteresis::new` rejects infinite thresholds.**
- Additive: `CusumBuilder::restart_on_alarm()`, `SecondDiff::count()`,
  `math::alpha_from_span`. The `i64` forms of `FirstDiff`, `SecondDiff` and
  `Slew` saturate instead of overflowing.

### Normalizers and DistributionShift (blind audit, PR C2)

- **`normalize(value)` returns `Result<Option<T>, DataError>`** on
  `ZScoreNorm`, `MinMaxNorm` and `QuantileNorm`: NaN and infinity are
  rejected as `update` rejects them. Add a `?` or `.unwrap()` before the
  existing `Option` handling.
- **`ZScoreNorm::update` scores the sample against the statistics before
  it**, then folds it in. Scores are larger than before (the old score was
  capped at `sqrt((1 - alpha) / alpha)`) and the first score arrives one
  sample later. A sample that departs from a so-far constant stream scores
  `+inf` or `-inf`, not `0.0`: clamp the score if it feeds a type that
  rejects infinity. Thresholds tuned against the old capped values need
  retuning.
- **`QuantileNorm` is a P² histogram.** Ranks reach exactly 0 and 1
  outside the range seen and prime after `resolution + 2` samples.
  `min_samples` below `resolution + 2` is an error (it was silently raised).
  Values differ from the old estimator grid.
- **`DistributionShift::update` returns `Result<Option<ShapeShift>, _>`**:
  `Some` on the sample that completes a window, with that window compared
  against the baseline before it, and `last()` returns the most recent one.
  `kurtosis_shift()`, `skewness_shift()` and `is_shifted(t)` are removed:
  read `shift.excess_kurtosis` and `shift.skewness` and test each against
  its own threshold. `is_primed()` is true once the first window has
  completed. `fast_window` must be at least 4.
- Additive: `DistributionShift::last()` / `fast_window()`, `ShapeShift`,
  `QuantileNorm` accepts `resolution(1)`.

## 5. Checklist

1. Replace the names in tables 1 and 2, builders included.
2. Turbofish or annotate every constructor of a generic type.
3. Replace the removed types from table 3.
4. `cargo build`. What remains is section 4: `DeadBand::new` now returns
   `Result`, any `i64` `DeadBand` threshold changes type, `Adwin` /
   `PageHinkley` verdicts are `Option<bool>`, `Debounce::count()` is
   `consecutive()`, `Exp3::select` needs a `&mut` bandit, `TopK::top()`
   returns an iterator instead of filling a buffer, and the method renames in
   the section 1 tables (`intercept`, `count`, `interval`, `update_at`).
