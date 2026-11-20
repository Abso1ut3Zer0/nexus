# Changelog

All notable changes to nexus-stats are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

The stats major ([#773](https://github.com/Abso1ut3Zer0/nexus/issues/773)):
one naming convention across the family. Migration guide:
[`docs/guides/migrating-to-7.md`](docs/guides/migrating-to-7.md).

### Changed

- **No numeric suffixes.** A type whose algorithm exists for one numeric
  type is named plainly (`EmaF64` → `Ema`, `WelfordF64` → `Welford`,
  `LivenessU64` → `Liveness`, `HoltF64` → `Holt`, `LinearRegressionF64` →
  `LinearRegression`, ...); builders follow. A genuine pair is one generic
  type bounded by the sealed `Sample` trait (`f64`, `i64`): `Drawdown<T>`,
  `WindowedMax<T>`, `WindowedMin<T>`, `RunningMax<T>`, `RunningMin<T>`,
  `MaxGauge<T>`, `PeakHold<T>`, `CoDel<T>`, `Jitter<T>`, `FirstDiff<T>`,
  `SecondDiff<T>`, `Hysteresis<T>`, `DeadBand<T>`, `LevelCrossing<T>`,
  `Slew<T>`, `WindowedMedian<T>`, `PeakDetector<T>`; the normalizers and
  `RobustZScore<T>` are `Float` generics (`f64`, `f32`) over `f64`
  internals. `update` returns `Result` on floats and the plain value on
  `i64`. The full map, per crate, is in the core, smoothing, detection,
  control and regression CHANGELOGs and in the migration guide.
- `Sample` and `Float` are re-exported at the crate root so the bounds can be
  named from the umbrella.
- `DeadBand<T>::new` returns `Result`; `PeakHold` restarts its hold on a
  sample equal to the decayed peak. The core CHANGELOG has the rest of the
  behavior changes.
- **Hot-path pass before release.** Every `update` in the README tables had
  its assembly read once. Ring indices advance with a compare instead of a
  division (`Autocorrelation`, `CrossCorrelation`, `TransferEntropy`,
  `Mosum`, `Kama`, `BoolWindow`, `TwoScaleRv`, `VarianceRatio`,
  `WindowedMedian`); extrema and sign tests use selects instead of branches
  (`Drawdown`, `RunningMax`, `RunningMin`, `PageHinkley`, `Lpm`, `HitRate`);
  `WindowedMedian::update` ranks by vectorized count; `TopK` and `VarianceRatio`
  drop their `Option` slots and `VecDeque`. On the reference machine
  (rdtsc ticks, p50): `WindowedMedian(32)::update` 149 → 81,
  `Hampel(21)::update` 250 → 96, `CrossCorrelation(10)::update` 54 → 30,
  `Kama(10)::update` 24 → 15, `TopK(16)::update` 45 → 36,
  `BoolWindow(64)::update` 11 → 6. Numbers in the README and
  `docs/reference/performance.md` regenerated.
- **Construction validation and numerics pass from the code-quality audit
  (second PR).** NaN-safe builders everywhere; `min_samples(0)` rejected;
  `WindowedMedian::new`, `LevelCrossing::new`, `DistributionShift` and
  `BipowerVariation` builders, `Welford::from_parts` and
  `Cusum::reset_with_target` return `Result`; `DataError::OutOfRange`;
  `HitRate`/`Amihud` rates return `Option`; `RobustZScore::mean_abs_dev`
  (was `mad`) with the `sqrt(2/π)` scale; `ShiryaevRoberts` saturates at `1e300`.
  See the per-crate CHANGELOGs and `docs/guides/migrating-to-7.md` § 4.
- **Storage pass from the code-quality audit (3 of 4).** One fixed-capacity
  ring, `storage::Ring<T>` *(alloc)*, replaces the hand-rolled head-and-wrap
  buffers in `WindowedMedian`, `Kama`, `Mosum`, `Hurst`, `Autocorrelation`,
  `CrossCorrelation`, `TransferEntropy` and `LaggedPredictor`; `BoolWindow`
  keeps its bit ring as
  `Box<[u64]>`. No raw pointers, manual `Drop` / `Clone` or `unsafe impl Send`
  remain in storage, and the converted types are `Sync`. `Bocpd` has no
  `unsafe` and drops a redundant per-run counter. `Adwin` holds its bucket
  levels as fixed lanes in one allocation, so memory is fixed at build for
  every type. `CovarianceMatrix` and `SignalDecayCurve` store boxed slices.
  No API changes beyond the new `storage` module and one gating change: the
  `signal` and `learning` modules exist only with `alloc` now (without it they
  were empty), which `detection`- or `regression`-without-`alloc` builds see.
- **Shared kernels and surface consistency pass from the code-quality audit
  (4 of 4).** Every type that primes reports `count()` and `is_primed()`
  beside `reset()` (24 types gain one or both); every builder with
  `alpha(a)` has `halflife(h)`; `Debounce::count()` counts updates and the
  run length is `consecutive()`; `Adwin` / `PageHinkley::update` return
  `Option<bool>` (`None` while priming); `Exp3::select` takes `&mut self`
  and `Exp3` is `Sync`; `HalfLife::new()` replaces its empty builder. Under
  the surface each algorithm exists once: the bandits share an arm bank,
  `Liveness` / `EventRate` share the shift-EMA kernel, `HalfLife` is a
  `Covariance`, `Autocorrelation` is a `Welford`, the adaptive filters share
  `dot` / `axpy`, and the last three `$ty` stamping macros are plain structs.
  Measured against the previous PR on every touched row of the perf harness:
  parity within a tick, with `HalfLife` 13 → 8, `Percentile` 41 → 37 and
  `RlsFilter` 133 → 92 ticks. See the per-crate CHANGELOGs and
  `docs/guides/migrating-to-7.md` § 4.
- **Renames** from the audit's naming pass: `OnlineCovariance` →
  `CovarianceMatrix`, `WallClock` → `MonotonicClock`, `CoDelBuilder::window`
  → `interval`, `BucketPolicy::WallTimeNanos` → `Ticks`,
  `BucketAccumulator::update_at_raw` → `update_at`, `TopK::total` → `count`,
  `intercept_value` → `intercept`, the bandits' `total_pulls` → `count`.
- **`TopK` is a hash-indexed sorted table with per-counter error** (control):
  `update` is O(1) expected whatever the capacity (15 ticks at 100 counters,
  71 for 1,000 counters over a million symbols; tables of 32 or fewer are
  scanned); `top()` is an iterator of
  `Counter { key, count, error }` over the sorted table, `top().take(k)` the
  top k, `guaranteed_top()` the number of ranks that are provably exact.
  `K: Eq + Hash` (was `Eq + Clone`).
- `libm` also enables `nexus-stats-smoothing/libm`, so `HuberEma` /
  `ConditionalEma::halflife` exist on a `no_std` + `libm` build.

- Carried from core (blind audit, PR C1): `LevelCrossing::update` returns
  the crossing's `Direction` and no longer counts a touch as a crossing;
  seeds on `Ema` and `Cusum` are values, not samples (`count()` starts at 0,
  `reset()` restores the seed); `Slew::value()` is an `Option`; `Cusum`
  reports the side further over threshold and gains `restart_on_alarm()`;
  `halflife` / `span` errors name the knob. See the migration guide.

- Carried from core (blind audit, PR C2): `ZScoreNorm::update` scores
  before it folds, so outliers are no longer capped; `QuantileNorm` is a P²
  histogram; `DistributionShift::update` returns a `ShapeShift` once per
  completed window, its `kurtosis_shift()` / `skewness_shift()` /
  `is_shifted()` readers are removed, and `is_primed()` means the first
  window has completed; `normalize` returns `Result<Option<T>, _>` on the
  three normalizers. See the migration guide.
- Carried from core: `Welford::update` no longer validates or returns a
  `Result`; `Welford::checked_update` is the validating form (after the
  standard library's `+` and `checked_add`). `INPUT_LIMIT` is re-exported
  at the crate root. The other types follow one at a time; the migration
  guide keeps the list.

### Removed

- `SaturationF64` ([#761](https://github.com/Abso1ut3Zer0/nexus/issues/761)),
  `LivenessF64`, `LivenessI64`, `EventRateI64`, `update_i64` on the windowed
  extrema and CoDel, `CoDel::min_sojourn` (core); `MosumI64`,
  `AutocorrelationI64` ([#379](https://github.com/Abso1ut3Zer0/nexus/issues/379),
  detection); `DecayAccumF64` (control); `HalfLifeBuilder` (core; it had no
  knobs, use `HalfLife::new()`).

### Added

- `PollSaturation` / `PollSummary` ([#764](https://github.com/Abso1ut3Zer0/nexus/issues/764))
  and `SojournSaturation` / `SojournSummary` ([#770](https://github.com/Abso1ut3Zer0/nexus/issues/770)):
  a consumer thread's saturation from its poll outcomes, or from stamped
  queue sojourns.
- `count()` / `is_primed()` where they were missing (see the 4-of-4 entry);
  `halflife(h)` on `VarianceRatio`, `RollSpread`, `MultiGate`,
  `RobustZScore`, `EwLinearRegression`, `EwPolynomialRegression`,
  `KyleLambda` and the EW transformed regressions; `Covariance::variance_x` /
  `variance_y`; `Welford::m2`; `Coefficients::eval`; `Debounce::consecutive`;
  `nexus-stats-smoothing`'s `libm` feature.

### Fixed

- Carried from core: `BipowerVariation` works on log returns and reports
  period totals, as the definitions do, read as a `JumpDecomposition`
  from `decomposition()`. Readings are not comparable with earlier ones; see the
  migration guide.
- Carried from core: `HalfLife` divided by the wrong variance, which
  misread short and decaying series. `coefficient()` and `reversion()`
  replace `autocorrelation()` and `half_life()`; see the migration guide.
- Carried from core: `Moments` no longer returns NaN for skewness or
  kurtosis on very small spreads. `Moments::shape()` replaces
  `skewness()` / `excess_kurtosis()` / `kurtosis()`; see the migration
  guide.
- Carried from core: `Covariance::correlation` no longer overflows or
  underflows on very large or very small inputs, and stays within
  `[-1, 1]`.

- Carried from core: `WindowedMin` / `WindowedMax` kernel-exact
  ([#758](https://github.com/Abso1ut3Zer0/nexus/issues/758)), `CoDel` RFC 8289
  `first_above` rule ([#759](https://github.com/Abso1ut3Zer0/nexus/issues/759)),
  `Liveness` deadlines ([#760](https://github.com/Abso1ut3Zer0/nexus/issues/760)),
  `PeakHold<f64>` negative-only streams and `Jitter<f64>` seeding
  ([#763](https://github.com/Abso1ut3Zer0/nexus/issues/763)).
- **`WindowedMedian::mad()` allocated and sorted a scratch `Vec` per call**,
  which made every `Hampel::update` allocate. Now one vectorized O(N) count
  over the sorted window: no allocation, no sort, same value.
- **`full,libm` without `alloc` compiled with warnings.** The umbrella `signal`
  and `learning` modules re-exported subcrate modules that are empty without
  `alloc`; both are gated on `alloc` now, matching every type they contain.

### Docs

- Every page under `docs/`, the README and the sub-crate docs use the new
  names. The type matrix and the integer-vs-float guide are rewritten; the
  README's type-variant table is replaced by a numeric-types section. About
  150 stale code examples are fixed against the shipped API (methods and
  builder options that never existed, unhandled `Result`s, removed types).
  `docs/algorithms/saturation.md` is replaced by `poll-saturation.md` and
  `sojourn-saturation.md`.
- **The headline cost claim is honest now.** README and crate docs promised
  "every primitive is O(1) per update, fixed memory after construction"; the
  window and dimension types (`WindowedMedian`, `Kama`, `Hampel`, `Bocpd`,
  `RlsFilter`, `CovarianceMatrix`, `OnlineKMeans`, `QuantileNorm`) are
  O(window) or O(d²), as their own pages already said. The module tables name every exported type with its
  feature gate (`alloc`, `std|libm`), list the `normalization` module, and
  name `FirstDiff`/`SecondDiff` where they said `Diff`.
- Removed `docs/guides/runtime-vs-const.md`: it documented a `Mosum::<64>`
  const-generic window that has not existed since the runtime-configuration
  change, and claimed stack-allocated rings.

## [6.0.1] — 2026-06-05

### Changed

- **nexus-stats-core** — Replaced `EventRateF64` with `EventRateU64` / `EventRateI64` using integer timestamps and bit-shift EMA. See core CHANGELOG for details.

## [6.0.0] — 2026-05-28

Type-variant audit: removed F32, I32, and I128 type variants across all
sub-crates. Use the F64/I64 equivalents. See each sub-crate's CHANGELOG
for the full removal list.

### Removed

- **nexus-stats-core 3.0.0** — 46 removed types (smoothing, control,
  monitoring, statistics modules). See core CHANGELOG.
- **nexus-stats-smoothing 2.0.0** — `HoltF32`, `SpringF32`, `Kalman1dF32`,
  `KamaF32`, `WindowedMedianF32`, `WindowedMedianI32` and their builders.
- **nexus-stats-detection 2.0.0** — `TrendAlertF32`, `MosumF32/I32/I128`,
  `MultiGateF32`, `PageHinkleyF32`, `AdwinF32`, `DistDriftF32`,
  `AutocorrelationF32/I32`, `CrossCorrelationF32`, `EntropyF32`,
  `PredictiveInfoBoundF32` and their builders.
- **nexus-stats-regression 2.0.0** — 20 removed types across regression,
  estimation, and learning modules. See regression CHANGELOG.
- **nexus-stats-control 2.0.0** — `PeakDetectorF32`, `PeakDetectorI32`,
  `PeakDetectorI128`.

## [5.1.0] — 2026-05-26

### Added

- **`BipowerVariationF64/F32`** — jump-robust volatility (no_std).
- **`RollSpreadF64/F32`** — Roll's implicit spread with Hasbrouck adjustment (std/libm).
- **`TwoScaleRvF64`** — noise-corrected realized variance (alloc+std/libm).
- **`HawkesIntensityF64/F32`** — self-exciting point process intensity (std/libm).
- **`PageHinkleyF64/F32`** — Page-Hinkley change detection (detection feature).
- **`AdwinF64/F32`** — ADWIN adaptive windowing (detection feature).
- **`PredictiveInfoBoundF64/F32`** — predictive information bound (detection feature).
- **`Ucb1F64/F32`** — UCB1 multi-armed bandit (regression feature).
- **`ThompsonBetaF64/F32`** — Thompson Sampling with Beta prior (regression feature).
- **`ThompsonGammaF64/F32`** — Thompson Sampling with Gamma prior (regression feature).
- **`EpsilonGreedyF64/F32`** — epsilon-greedy bandit (regression feature).
- **`Exp3F64/F32`** — EXP3 adversarial bandit (regression feature).

## [5.0.0] — 2026-05-18

Breaking: tracks nexus-stats-core 2.0.0.

### Added

- **`clock` module** re-exported from nexus-stats-core. `Clock` trait,
  `WallClock`, `EpochClock`.

### Changed

- `std` feature now also provides `WallClock`.

### Removed

- All `Instant`-based stats types (see nexus-stats-core 2.0.0 CHANGELOG).
- `Raw` suffix dropped from windowed/CoDel type names.

## [4.x] — workspace re-export pattern

`nexus-stats` is the umbrella crate that re-exports from the
focused subcrates: `nexus-stats-core`, `nexus-stats-control`,
`nexus-stats-detection`, `nexus-stats-regression`, and
`nexus-stats-smoothing`. The umbrella version tracks the workspace
release cadence; subcrate versions track per-area changes.

For per-algorithm or per-type changes, see the relevant subcrate's
CHANGELOG (or its git history).

## [4.2.2] and earlier

Earlier history is not documented in this CHANGELOG. See git history,
GitHub release notes, and the per-subcrate CHANGELOGs for details.
