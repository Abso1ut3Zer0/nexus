# Changelog

All notable changes to nexus-stats-core are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- `DataError::NonMonotonicTime`: a timestamp before the last one taken.
  Returned by `checked_update` on `WindowedMax` and `WindowedMin`.
- `Sample::is_nan` and `Sample::magnitude` (the absolute value; `i64::MIN`
  saturates to `i64::MAX`), for the generic `update` of the windowed
  extremes and `PeakHold`.

### Removed (moved to other crates, step 3)

- `Ema`, `AsymEma`, `Slew` and `EwmVar` are now in `nexus-stats-smoothing`;
  `Cusum` and `DistributionShift` in `nexus-stats-detection`. The crate is
  now the shared foundation and the descriptive statistics.

### Added (internal)

- **`parts` module (doc-hidden):** the small pieces of state several types
  share. `Weight` (a smoothing weight with its complement) and `Warmup`
  (the sample count with the number needed before a reading) are new;
  `EwWeight`, `RoundingEstimate` and `RoundingBound` move there from
  `math`, which now holds operations on numbers only.

### Changed (internal)

- `math::step_mean` (doc-hidden): the running-mean step the accumulators
  share, moved out of `statistics` so `EwmVar` can use it from its new crate.

### Removed (moved to other crates, step 2)

- The `monitoring` module is now `nexus-stats-monitoring`, `normalization`
  is `nexus-stats-normalization`, and the `control` types (`DeadBand`,
  `Hysteresis`, `Debounce`, `LevelCrossing`) are in `nexus-stats-control`.

### Removed (moved to other crates)

- `VarianceRatio`, `TwoScaleRv`, `BipowerVariation`, `Amihud`, `RollSpread`,
  `Lpm` and `Cvar` are now in `nexus-stats-trading`; `Hurst` and `HalfLife`
  in `nexus-stats-detection` (`signal`); `HitRate` in
  `nexus-stats-regression`. `statistics` now holds the descriptive
  statistics only.

### Changed (module)

- `FirstDiff` and `SecondDiff` move from `control` to `statistics`.

### Changed

- **Thresholds are named, documented and built from the float type.** Each
  number a converted type relies on is a private constant on the type, or
  a shared constant or `const fn` in `math` when several types use it, with
  a line saying what it means and where it comes from (SciPy, LAPACK, the
  paper, or "our choice"). The input limits `checked_update` enforces are
  explained in a new "Input limits" section of the crate docs and checked
  against `f64::MAX` at compile time; they are not exported.

- **One naming convention, no numeric suffixes** (the stats major, [#773](https://github.com/Abso1ut3Zer0/nexus/issues/773)).
  A type whose algorithm exists for one numeric type is named plainly:
  `EmaF64` → `Ema`, `WelfordF64` → `Welford`, `CusumF64` → `Cusum`,
  `LivenessU64` → `Liveness`, `DebounceU64` → `Debounce`, and so on for every
  `F64`/`U64`-only type; builders follow (`EmaBuilder`). A type whose algorithm
  exists for two numeric types is one generic type bounded by the sealed
  `Sample` trait (`f64`, `i64`): `Drawdown<f64>` / `Drawdown<i64>`,
  `WindowedMax<T>`, `WindowedMin<T>`, `RunningMax<T>`, `RunningMin<T>`,
  `MaxGauge<T>`, `PeakHold<T>`, `CoDel<T>`, `Jitter<T>`, `FirstDiff<T>`,
  `SecondDiff<T>`, `Hysteresis<T>`, `DeadBand<T>`, `LevelCrossing<T>`,
  `Slew<T>`; builders are `CoDelBuilder<T>` etc. The algorithm body is
  written once; methods whose signature differs by type are implemented per
  instantiation, so `update` still returns `Result` for floats (NaN and
  infinity rejected) and the plain value for integers. Constructors and
  builders are shared, so write the type once: `Drawdown::<i64>::new()`,
  `let dd: Drawdown<f64> = Drawdown::new()`, `CoDel::<i64>::builder()`.
  Codegen is unchanged (verified against the perf harness and disassembly).
- **Normalizers are `Float` generics over `f64` internals.** `ZScoreNorm<T>`,
  `MinMaxNorm<T>`, `QuantileNorm<T>` for `T` in `f64`, `f32`: they take and
  return `T` but accumulate in `f64`, so the `f32` forms are boundary types
  for `f32` feature vectors, no longer `f32` accumulators. The `pub(crate)`
  `f32` stamps of `EwmVar`, `Percentile` and the windowed extrema are gone.
- **`DeadBand<T>::new(threshold: T)` returns `Result`** and rejects a negative
  or non-finite threshold (`ConfigError::Invalid`); the integer form takes an
  `i64` threshold instead of `u64`, with the same exact `abs_diff` arithmetic.
- **`PeakHold<T>`**: after the hold expires, a sample equal to the decayed
  peak now restarts the hold (`>=`, was `>`); the integer form drops to the
  current sample as before. `jitter_ratio()` is available on `Jitter<i64>`.
- **`Jitter<i64>` and `Jitter<f64>` share one builder:** `span(n)` on both;
  `alpha` and `halflife` on `f64` only; `effective_span()` on `i64` only.
- **Fused multiply-add is used only when the target has FMA.** Rust's
  `f64::mul_add` is an FMA instruction only with the `fma` target feature
  (`-C target-cpu=native` / `-C target-feature=+fma`; always on aarch64);
  elsewhere LLVM lowers it to a call into compiler-builtins' software `fma`,
  which cost the FMA-heavy types (the regressions, the adaptive filters,
  `EwmVar`, `Moments`) 3 to 5 times their arithmetic on a default
  `cargo build --release`. The crate's shim now fuses in the first case and
  computes `a * b + c` in the second. Results on the two paths differ in
  the last bit; results within one build are deterministic as before.
- **Hot-path pass before release.** `Drawdown`, `RunningMax` and `RunningMin`
  update their extremum with a select instead of a branch (a new peak is a
  coin flip for the predictor in a trending series); `Drawdown` seeds its
  internal peak at `T::MIN`, so the first sample needs no special case.
  `HitRate` folds its four sign compares into flags, `Lpm` clamps the
  shortfall instead of branching on it, `TwoScaleRv` advances
  its ring index with a compare instead of a division. Same results; no `div` and fewer unpredictable
  jumps on the update path.
- **Construction validation is NaN-safe and complete.** `math::positive_finite`,
  `nonnegative_finite` and `in_unit_interval` replace the sign-only tests that
  let NaN through; `Cusum` validates target, slack, thresholds and seeds, and
  `reset_with_target` returns `Result` (target 0 with default thresholds is
  rejected instead of installing a threshold of zero). `min_samples(0)` is
  rejected by Ema, EwmVar, BipowerVariation, Lpm, RollSpread, and Jitter needs
  2 unseeded; seeds must be finite; Lpm `order` is capped at 16; Liveness and
  EventRate spans at 2^62. `WindowedMedian`-style bare or panicking
  constructors return `Result`: `LevelCrossing::new`,
  `DistributionShiftBuilder::build`, `BipowerVariationBuilder::build`,
  `Welford::from_parts`.
- **`DataError::OutOfRange`** for finite inputs outside a method's range.
  `HarmonicMean::checked_update` returns it for a non-positive sample
  (`update` used to panic on one); the `DataError` doc states the three-way policy.
- **`HitRate::hit_rate` / `ew_hit_rate` and `Amihud::illiq` return `Option`:**
  a rate over zero observations is undefined, not 0.0. `Amihud` rejects
  negative volume with `Negative`, skips zero volume without advancing
  `count`, and propagates an overflowed ratio instead of discarding it.
- `Percentile::min_samples()` is public; `QuantileNorm` reads its grid's
  priming need from it instead of re-deriving the formula. `Hurst` primes at
  its configured window.
- `CovarianceMatrix` stores its matrix and means as `Box<[f64]>` (fixed at
  build) instead of `Vec`.
- **Shared kernels and surface consistency pass from the code-quality audit
  (4 of 4).** Every type reports `count()` and `is_primed()` beside `reset()`
  where the notion applies: `DeadBand`, `Slew`, `FirstDiff`, `SecondDiff`,
  `LevelCrossing`, `Hysteresis`, `MaxGauge`, `PollSaturation` and
  `SojournSaturation` gain both; `PeakHold`, `WindowedMax` / `WindowedMin`,
  `BucketAccumulator` and `Covariance` gain `is_primed()`. Each type's rule
  is its own (`Covariance` needs two samples, `FirstDiff` two, `SecondDiff`
  three, the saturation monitors count messages). The `initialized` flags
  behind `DeadBand`, `Slew`, `FirstDiff` and `LevelCrossing` are the counter
  now; the update paths compile to the same code.
- **`Debounce::count()` is the number of updates;** the run of consecutive
  `true`s that `update` compares to the threshold is `consecutive()` (was
  `count()`).
- **Every builder with `alpha(a)` has `halflife(h)`** (`std` or `libm`):
  `RollSpread` gains it, all of them computed by one
  `math::alpha_from_halflife`. The missing-field error is
  `ConfigError::Missing("alpha")` everywhere (`HitRate` said "alpha or
  halflife"), the range test is `math::in_unit_interval` everywhere, and
  `Hawkes` rejects a negative or non-finite `alpha`.
- **Renames** (the audit's naming pass). `OnlineCovariance` →
  `CovarianceMatrix` (and its builder); `WallClock` → `MonotonicClock` (it is
  `Instant`-based; `EpochClock` is the wall clock); `CoDelBuilder::window(n)`
  → `interval(n)`, RFC 8289's name; `BucketPolicy::WallTimeNanos(n)` →
  `BucketPolicy::Ticks(n)` and `BucketAccumulator::update_at_raw` →
  `update_at`, since the stamp is in any unit like every other time-aware
  type.
- **One copy of each kernel.** `Liveness` and `EventRate` run on the
  `sample::ShiftEma` kernel (which gains `is_initialized()` and `reset()`);
  `HalfLife` is a `Covariance` over consecutive pairs; `EwmVar` and
  `Percentile` are plain items (the `$ty` stamping macros are gone, as is the
  never-called `math::check_finite` function; the `check_finite!` macro is
  exported, doc-hidden, for the sibling crates). `math::dot`, `math::axpy`
  and `math::upper_tail_z` (Abramowitz-Stegun 26.2.23) serve the regression
  crate's filters and conjugate priors. `Hysteresis<i64>::update` and
  `LevelCrossing<i64>::update` are `#[must_use]` like their `f64` forms.

- **`LevelCrossing::update` returns the direction of the crossing**
  (`Option<Direction>`: `Rising`, `Falling`, or `None`) instead of a `bool`,
  and a sample exactly on the threshold is on neither side. Before, the
  threshold itself counted as "above", so a signal that touched it and went
  back (-1, 0, -1 around 0) was counted as two crossings.
- **A seed is a value, not samples** (`Ema`, `Cusum`). A seeded instance is
  primed at once, `count()` counts only samples fed (it used to start at
  `min_samples`), and `reset()` returns to the as-built state, seed included.
  `Cusum::reset_with_target` drops the seeds, which were calibrated against
  the old target.
- **`Cusum` reports the side further over its threshold when both are over**
  (it always reported `Rising`), and documents that an alarm persists until
  the sum drains or `reset()` is called.
- **`Slew::value()` returns `Option<T>`**, `None` before the first sample.
- **`SecondDiff` is the difference of the two first differences.** Same value
  as before up to floating-point rounding; the `i64` form no longer
  overflows.
- **`AsymEma::update` selects the weight and applies
  `value += alpha * (sample - value)`**: one select instead of two, and two
  fewer fields.

- **`ZScoreNorm::update` scores a sample against the statistics of the
  samples before it, then folds it in.** It folded first, which bounds the
  score by `sqrt((1 - alpha) / alpha)` whatever the sample: 3.0 at alpha
  0.1, so a 1e9 outlier scored 2.9999999999999996 and a gate at 4 could
  never fire.
- **`ZScoreNorm` gives no score to a stream with no spread.** While every
  sample so far has been the same value there is no scale, and `update`
  and `normalize` return `None`, as NumPy, pandas and SciPy give no value
  (NaN) there. It scored `0.0`. "No spread" is a variance at or below
  `(EPSILON * mean)^2`, the test SciPy uses, in place of a fixed `1e-14`
  floor.
- **`ZScoreNorm::update` and `normalize` no longer validate or return a
  `Result`**: both return `Option<T>`. `checked_update` and `checked_normalize` are the validating
  forms: both refuse NaN, infinity, and a magnitude above `1e120`.
- **`QuantileNorm` is a P² histogram** (Jain & Chlamtac 1985): one array of
  `resolution + 2` markers adjusted in a single pass, in place of
  `resolution` independent P² estimators with five markers each. Ranks are
  non-decreasing in the value, exactly 0 below the minimum seen and 1 above
  the maximum (the tails were the constants `p1 / 2` and `(1 + pn) / 2`,
  with a step at the edge), and the markers cannot cross. Memory is
  `16 * (resolution + 2)` bytes, down from about `190 * resolution`.
  `resolution(1)` is accepted (minimum, median, maximum).
- **`DistributionShift` compares each completed window with the baseline
  before it** and latches the result. `update` returns
  `Result<Option<ShapeShift>, DataError>`, `Some` on the sample that
  completes a window. Before, the window was discarded in the same `update`
  that completed it, so a full window could never be read: the accessors saw
  only a partly filled one, and nothing at all for the first three samples
  of each. The baseline no longer includes the window under test, and each
  sample is folded once instead of twice. `is_primed()` means "the first
  window has completed, so a baseline exists" and stays true until `reset`;
  whether the last window produced a reading is `last()`.
- **`DistributionShift::kurtosis_shift()`, `skewness_shift()` and
  `is_shifted()` are removed.** The reading is the `ShapeShift` that
  `update` returns and `last()` holds; the three were one-line reads of it,
  and `is_shifted` applied a single threshold to two quantities on different
  scales.
- **`normalize` returns `Result<Option<T>, DataError>`** on the three
  normalizers; NaN and infinity went straight through to the output.
  `MinMaxNorm::normalize` is documented as unclamped.
- **`Welford::update` no longer validates and no longer returns a
  `Result`**, after the standard library's `+` and `checked_add`: it does
  the arithmetic, which follows IEEE 754. The validating form is the new
  `checked_update`. This is the shape every type is moving to, one type at
  a time; the crate docs state the rule.
- **`HarmonicMean::update` no longer validates or returns a `Result`**,
  the same change as `Welford`. `checked_update` is the validating form.
- **`Covariance::update` no longer validates or returns a `Result`**, the
  same change again. `checked_update(x, y)` validates both values.
- **`EwmaVar` is renamed `EwmVar`.** `ewm` is the stem Polars (`ewm_mean`,
  `ewm_var`) and pandas (`ewm().var()`) use. `Ema` keeps its name. The
  `Ew*Regression` types in `nexus-stats-regression` will take the `Ewm`
  stem when each is converted.
- **`AsymEma::update` no longer validates or returns a `Result`**: it
  returns `Option<f64>`, as `Ema` does. `checked_update` is the validating
  form and refuses NaN and infinity.
- **`Ema::update` no longer validates or returns a `Result`**: it returns
  `Option<f64>`. `checked_update` is the validating form and refuses NaN
  and infinity.
- **`EwmVar::update` returns a `MeanVariance { mean, variance }`**, with
  `std_dev()`, in place of a `(mean, variance)` tuple, and no longer
  validates or returns a `Result`. `checked_update` is the validating
  form. `value()` replaces `mean()`, `variance()` and `std_dev()` on the
  type.
- **`EwmVar` needs `min_samples` of at least 2** (one sample has no
  variance; it accepted 1 and reported a variance of 0), and treats a seed
  as `Ema` does: a converged state, with `count()` at 0 and `reset()`
  returning to it. A seed used to set `count()` to `min_samples`, and
  `reset()` discarded it.
- **`ZScoreNorm` readings shift**, because the variance under it is now
  unbiased (see Fixed). It follows `EwmVar` on the rest too: `min_samples`
  must be at least 2, a seeded normalizer starts with `count()` at 0, and
  `reset()` returns to the seed.
- **`VarianceRatio`, `TwoScaleRv` and `Hurst` take a price and no longer
  validate or return a `Result` from `update`** (`VarianceRatio::update`
  returns an `Accuracy`). Each takes the logarithm
  itself. `checked_update` is the validating form and refuses NaN,
  infinity, and a price that is zero or negative.
- **`VarianceRatio` is the Lo and MacKinlay statistic over a sliding
  window.** It was a ratio of two exponentially weighted variances, a
  construction with no published counterpart. It now computes their
  estimator on the log price over the last `window` returns (overlapping
  `q`-period returns, endpoint drift, both bias corrections) and matches
  `arch.unitroot.VarianceRatio`. The builder takes `horizon` (the paper's `q`) and `window`;
  `alpha` and `halflife` are gone. `estimate()` returns a
  `VarianceRatioEstimate { ratio, z_statistic }`, replacing
  `variance_ratio()`; `is_mean_reverting()` and `is_trending()` are removed
  (compare `z_statistic` with a level you choose). Needs `std` or `libm`.
- **`Hurst` is the multi-scale rescaled-range estimate.** It computed
  `ln(R/S) / ln(n)` over one window, which is biased and shrinks toward
  0.5. It now measures `R/S` at the window and each halving down to
  `smallest_window`, corrects each by the Anis-Lloyd-Peters expectation,
  and fits the slope, matching `nolds.hurst_rs`. `exponent()` replaces
  `hurst()`; the builder's `window_size` is `window`, in returns;
  `is_mean_reverting()` and `is_trending()` are removed.
- **`TwoScaleRv` works on log prices and applies the paper's small-sample
  adjustment** (Zhang, Mykland and Aït-Sahalia, 2005, equation 64, as R's
  `highfrequency` does). It differenced raw prices. `estimate()` returns a
  `TwoScaleEstimate { variance, realized_variance, noise_variance,
  returns }`, replacing `realized_variance()`, `realized_volatility()`,
  `fast_rv()` and `noise_variance()`. The variance is no longer clamped at
  zero; `volatility()` takes a negative estimate as zero. The noise
  variance is the paper's `[Y,Y]all / 2n`. `min_samples` must be at least
  `k + 1`. Old readings are not comparable.
- **`Amihud::update` and `HitRate::update` no longer validate or return a
  `Result`.** `checked_update` is the validating form on both.
- **`Amihud::update` takes the period's return, signed or not,** and uses
  its magnitude. It took an absolute return and trusted the caller to have
  made it one. A ratio that overflows is refused by `checked_update` as
  `OutOfRange` (it was `Infinite`).
- **`RollSpread` works on log-price changes, with the mean removed.**
  `update(price)` takes the logarithm itself, so the spread is a proportion
  of the price (`0.0005` is 5 basis points), as in Roll's own estimates and
  most later work; it differenced raw prices. The autocovariance has the
  mean change removed, as the implementations compared do (R's `bidask`,
  pandas-based code); it was a plain average of products, which a drifting
  price pushed toward zero. Old readings are not comparable.
- **`RollSpread::estimate()` returns a `RollEstimate { spread,
  autocovariance }`.** `update` no longer validates and returns nothing;
  `checked_update` is the validating form. `spread()` and
  `autocovariance()` on the type are removed. A non-negative autocovariance
  gives a spread of `0.0` (it was `None`), the usual substitute (Hasbrouck,
  2009; Goyenko, Holden & Trzcinka, 2009); the `autocovariance` field
  shows when that happened. `min_samples` must be at least 3. The builder
  also accepts `span`.
- **`update` returns a value only on a transform.** A type whose result the
  caller uses for each sample (a smoother, a normalizer) returns it from
  `update`. A type that summarizes many samples returns nothing and is
  read by a method named for what it returns. `BipowerVariation` follows:
  `decomposition()` replaces `last()`, and its `update` returns nothing.
- **`BipowerVariation` works on log returns and reports period totals.**
  `update(price)` takes the logarithm itself, as the definitions
  (Barndorff-Nielsen & Shephard, 2004) and the MFE Toolbox do; it
  differenced raw prices. Realized variance and bipower variation are sums
  since the last `reset()`, as defined; they were per-step averages, with
  different divisors. Old readings are not comparable. The type now needs
  `std` or `libm`, and `min_samples` must be at least 3.
- **`BipowerVariation::decomposition()` returns a `JumpDecomposition`.**
  `update` no longer validates and returns nothing; `checked_update` is the
  validating form. `realized_variance()`, `bipower_variation()`,
  `jump_variation()` and `jump_ratio()` on the tracker are replaced by the
  reading: fields `realized_variance`, `bipower_variation` (the original
  definition) and `returns`; methods `debiased_bipower_variation()`
  (scaled by `M / (M - 1)`, as the MFE Toolbox's debiased output),
  `jump_variation()` and `jump_ratio()`, which use the debiased form.
- **`HalfLife::update` no longer validates or returns a `Result`.**
  `checked_update` is the validating form.
- **`HalfLife::coefficient()` and `reversion()` replace `autocorrelation()`
  and `half_life()`.** The value was a regression coefficient, not a
  correlation. `reversion()` returns a `Reversion`: `Reverting
  { half_life }`, `NotReverting` (`phi >= 1`) or `Oscillating`
  (`phi < 0`). `half_life()` returned `None` for all of "not enough data",
  "not reverting" and "oscillating".
- **`Lpm::update` no longer validates or returns a `Result`.**
  `checked_update` is the validating form.
- **`Moments::update` no longer validates or returns a `Result`.**
  `checked_update` refuses a magnitude above `1e60`.
- **`Moments::shape()` replaces `skewness()`, `excess_kurtosis()` and
  `kurtosis()`.** It returns a `Shape { skewness, excess_kurtosis }`, with
  `kurtosis()` on the struct. Skewness now needs four samples (it was
  three), since the pair comes together.

### Removed

- **`RollSpread::hasbrouck_spread()`.** It computed `spread * sqrt(1 + rho)`
  and credited Hasbrouck (2009). No published estimator has that form;
  Hasbrouck's is a Bayesian sampler for the Roll model.

- **`SaturationF64`** ([#761](https://github.com/Abso1ut3Zer0/nexus/issues/761)):
  an EMA of a caller-supplied utilization fraction against an unvalidated
  threshold, identical to `ErrorRate::update_weighted`. Smooth the
  fraction with `Ema` and compare, or use `PollSaturation` /
  `SojournSaturation` for a consumer thread's saturation.
- **`LivenessI64`, `EventRateI64`**: ticks are `u64` (the `clock` module's
  contract). `Liveness` and `EventRate` are the former `U64` types.
- **`update_i64(timestamp: i64, ..)`** on the windowed extrema and CoDel:
  cast at the call site.
- **`CoDel::min_sojourn()`**: the RFC 8289 detector no longer keeps a
  windowed minimum (see Fixed). Keep a `WindowedMin<i64>` beside it if you
  report one.
- **`LivenessF64`**: `f64` timestamps lose precision past 2^52; `Liveness` takes `u64` ticks.
- **`HalfLifeBuilder`**: it had no knobs. `HalfLife::new()`.

### Added

- `ShapeShift`, `DistributionShift::last()` and `fast_window()`.

- `CusumBuilder::restart_on_alarm()`: zero the alarming side as it reports,
  for one alarm per detection (the classic restarting CUSUM).
- `SecondDiff::count()`.
- `math::alpha_from_span`, and `math::EwWeight`, the shared resolver behind
  the `alpha` / `halflife` / `span` builder knobs.
- `Sample::sat_sub` / `sat_add`.

- **`PollSaturation`** / **`PollSummary`** — consumer-side saturation from
  poll outcomes and the caller's stamps: no message timestamps, no queue
  depth, no clock inside the type, no clock read on an idle spin. Tracks the
  arrival floor (the latest tick the input was proven empty, by an empty
  poll or a short batch poll) and `on_work(now, n)` returns `behind`, an
  upper bound on how long any message in that poll waited for this thread;
  zero is exact. `new(budget)` takes the wait you consider late. `take()`
  returns the summary of every poll since the previous take, whenever the
  caller decides to snap (timer, message count, event): `max_messages_per_poll` and
  `max_backlog_messages` (the count form of saturation), `messages_waited`, `messages_over_budget` and
  `max_behind_ticks` (the duration form), and the `is_fully_utilized` / `is_backlogged`
  flags. Summaries merge exactly. 80 bytes, `on_idle` is one store
  ([#764](https://github.com/Abso1ut3Zer0/nexus/issues/764)).
- **`SojournSaturation`** / **`SojournSummary`** — the stamped twin of
  `PollSaturation`: feed each message's queue sojourn (dequeue tick minus
  enqueue tick, same clock) and `take()` returns the period's
  `messages_seen`, `messages_over_budget`, `min_sojourn_ticks` (the floor;
  zero means the clocks disagree), `max_sojourn_ticks`,
  `total_sojourn_ticks` with an integer `mean_sojourn_ticks()`, and
  `is_backlogged` (no message within budget all period). One knob, the
  budget; no clock inside; snap when the caller decides; summaries merge
  exactly as a plain fold (an empty period is the identity of every field).
  Negative sojourns (clock skew) clamp to zero
  ([#770](https://github.com/Abso1ut3Zer0/nexus/issues/770)).
- **`storage::Ring<T>`** *(alloc)*: the fixed-capacity overwrite ring every
  windowed type now shares (`Hurst` here; `Mosum`, `Kama`, `WindowedMedian`,
  `Autocorrelation`, `CrossCorrelation`, `LaggedPredictor` in the subcrates).
  `push` returns the evicted sample once the ring is full, `replace` returns
  the slot's previous content unconditionally (the fill while filling),
  `as_slices` / `iter` walk the contents oldest-first at any fill, and `raw`
  exposes storage order and head for callers that have established fullness
  and want the two runs without the test (`Kama`). One
  allocation at construction, one length, no `%`, and fullness is a flag set
  in the wrap branch, so a push costs what a hand-rolled ring costs. Public
  because the subcrates need it; shaped for them, not a general-purpose ring
  buffer.
- `Covariance::variance_x()` / `variance_y()`: the marginal variances the
  type already carries.
- `Welford::m2()`: the sum of squared deviations, the `m2` of `from_parts`.
- `Welford::checked_update`: `update` with the sample validated first. It
  returns a `DataError` and leaves the accumulator unchanged for a NaN, an
  infinity, or a magnitude above `1e120`, within
  which the variance cannot overflow.
- `HarmonicMean::checked_update`: refuses a NaN, an infinity, or a sample
  outside `[1e-120, 1e120]` (which includes zero and
  negatives), and leaves the accumulator unchanged.
- `RollSpread::checked_update` (refuses NaN, infinity, and a zero or
  negative price), `RollSpread::estimate`, `RollEstimate`.
- `BipowerVariation::checked_update` (refuses NaN, infinity, and a zero or
  negative price), `BipowerVariation::decomposition`, `JumpDecomposition`.
- `HalfLife::checked_update`, `Reversion`.
- `Lpm::checked_update`: refuses a NaN, an infinity, and the sample whose
  shortfall raised to the order would overflow the running sum. It tests
  the result, not the input, since the order goes up to 16 and no single
  input limit covers every order. The type docs give rough bounds and the
  libraries this follows.
- `Ema::checked_update`, `Ema::reset_with_seed`.
- `AsymEma::checked_update`, `AsymEma::reset_with_seed`, and on its
  builder `seed`, `halflife_up`, `halflife_down`.
- `ZScoreNorm::checked_update`, `ZScoreNorm::checked_normalize`,
  `ZScoreNorm::reset_with_seed`.
- `VarianceRatio::checked_update`, `estimate`, `resync` and `window`;
  `VarianceRatioEstimate`. The z statistic is Lo and MacKinlay's
  heteroskedasticity-robust one. `update` costs time proportional to `q`,
  from running totals, and works out the reading; `estimate` returns it.
  `update` returns
  `Accuracy::ResyncRequired { error }` when rounding in the totals could reach
  one part in a thousand of z (after volatility falls a long way, a price
  far off the market, or a trend far from where it was),
  and keeps returning it until `resync()` recomputes them from the stored
  prices. Until then `estimate()` returns `None` and `update` only stores
  the price.
- `Accuracy`, at the crate root: what a windowed type's `update` reports
  about its running totals, `Sound` or `ResyncRequired { error }`.
  `VarianceRatio` is the first to return it.
- `math::RoundingEstimate` and `math::RoundingBound`: the rounding error a
  running total has accumulated, from the size of the total at each add.
  The estimate treats the errors as independent (Higham and Mary, 2019)
  and matches what is seen; the bound is the worst case. For totals that
  are added to and removed from. `VarianceRatio` decides its
  `Accuracy::ResyncRequired` with the estimate.
- `storage::SliceRing`: a fixed-capacity ring whose contents are always
  one slice, for windows that are read across. `Hurst` and `VarianceRatio`
  use it.
- `Hurst::checked_update`, `exponent`, `window`, and the builder's
  `smallest_window`. Its inner loop has SSE2 and AVX2 versions (AVX2 when
  the build enables `avx2` and `fma`): a read is about twice as fast on a
  default x86-64 build and about three times with AVX2.
- `TwoScaleRv::checked_update`, `estimate`; `TwoScaleEstimate`.
- `Amihud::checked_update` (refuses NaN, infinity, a negative volume, and
  a ratio that overflows) and `HitRate::checked_update` (NaN and infinity).
  Both builders accept `span`.
- `math::check_inputs!`: `check_input` for several values with one limit,
  `check_inputs!(limit; a, b)?`, or `check_inputs!(a, b)?` for NaN and
  infinity only.
- `EwmVar::checked_update` (refuses NaN, infinity, and a magnitude above
  `1e120`), `EwmVar::value`, `EwmVar::reset_with_seed`, `MeanVariance`.
- `Moments::checked_update`, `Shape`.
- `Covariance::checked_update`: refuses the pair, and leaves the
  accumulator unchanged, if either value is NaN, infinite, or larger in
  magnitude than `1e120`.
- `math::alpha_from_halflife`, `math::dot`, `math::axpy`,
  `math::upper_tail_z`.

### Fixed

- **`Hurst` read a random walk as trending when fed prices.** Its docs
  allowed "a return or price level", and on price levels a random walk
  read about 0.8. It takes prices and differences them itself.
- **`Hurst` skips a stretch whose returns are equal to within rounding.**
  Such a stretch contributed a ratio of rounding noise. The test is the one
  SciPy applies to a variance, at the scale of the log price.
- **`EwmVar` no longer reads low.** The variance came from the recursion
  `var = (1 - alpha) * (var + alpha * d^2)`, which gives about 18% of the
  true variance after two samples (alpha 0.1) and stays about 5% low. It
  is now the unbiased weighted variance, the weighted sum of squared
  deviations over `W - W2 / W`, which pandas (`ewm().var()`) and Polars
  (`ewm_var`) compute by default. Unbiased from the second sample on. Old
  readings are not comparable.
- **Builders refuse a weight too small to use, under every knob.** An
  `alpha` below half of machine epsilon (about `1.1e-16`), or a `span`
  large enough to give one, was accepted, though `1 - alpha` rounds to 1
  there and nothing is ever forgotten. `halflife` already refused such a
  weight. Applies to the builders that use the shared resolver: `Ema`,
  `AsymEma`, `ZScoreNorm`, `RollSpread`.
- **`RollSpread` no longer reads low while warming up.** Its weighted
  averages started at zero and climbed, so early estimates were a fraction
  of the true spread. They are now divided by the weight accumulated so
  far.
- **`HalfLife` divides by the variance of the lagged values.** The
  least-squares slope of `x_t` on `x_{t-1}` is `Cov / Var(x_{t-1})`; it
  divided by `Var(x_t)`. The two agree on long stationary series and not
  on short or decaying ones: `8, 4, 2, 1` read as not reverting (it has a
  half-life of 1), and `1, 2, 4, 8` as a half-life of 1 (it does not
  revert). `coefficient()` is also `None` when the lagged values differ
  only at rounding level (variance at or below `(f64::EPSILON * mean)^2`),
  where the slope was numerical noise.
- **`Moments` no longer returns NaN for skewness or kurtosis.** On data
  with a spread under about `1e-73` the divisors underflowed or lost
  their digits. `shape()` returns `None` there, and also when the variance
  is at or below `(f64::EPSILON * mean)^2`, the test SciPy's `skew` and
  `kurtosis` use for data too close to constant. A term of the update that
  underflowed for tiny values on very long streams is regrouped.
- **`Covariance::correlation` no longer overflows or underflows, and stays
  within `[-1, 1]`.** It multiplied the two sums of squares before taking
  the root, so inputs near `1e120` read as a correlation of 0 and inputs
  near `1e-120` as `None`, and rounding could leave a result just outside
  the range. It now takes the two roots separately and clamps.
- **`QuantileNorm` rejects a `min_samples` below `resolution + 2`** instead
  of silently raising it.
- **`ZScoreNorm` reports a bad `halflife` or `span` under its own name**, as
  `Ema` does.
- **`DistributionShift` requires `fast_window >= 4`**, the fewest samples
  for which excess kurtosis is defined.

- **A bad `halflife` or `span` is reported under its own name.** The `Ema`
  builder (and `AsymEma`'s `span_up` / `span_down`) converted the knob to an
  alpha as it was set, so `halflife(-1.0)` and `span(0)` surfaced as "alpha
  must be in (0, 1)".
  `halflife` must be positive and finite and `span` at least 2.
- **`Cusum::builder` validates the target first.** A NaN target was reported
  as a slack error, and a target of 0 with default thresholds as "threshold
  must be positive". Negative seeds are rejected (the sums are never
  negative).
- **`FirstDiff<i64>`, `SecondDiff<i64>` and `Slew<i64>` saturate** instead of
  panicking in debug and wrapping in release on sentinel-sized inputs; their
  docs said they cannot fail.
- **`Hysteresis` documents its thresholds as inclusive**, which is what the
  code does, and rejects infinite thresholds (the state could never change).
- **`AsymEma` rejects `min_samples(0)`**, which made `value()` report
  `Some(0.0)` before any sample.

- **`feature_vector!` alignment soundness** ([#787](https://github.com/Abso1ut3Zer0/nexus/issues/787)): a `#[repr(packed)]` attribute from the caller lowered struct alignment to 1, so the safe `as_slice()` and `as_mut_slice()` could build a `&[f64]` from a misaligned pointer. A compile-time assertion now rejects any struct whose alignment falls below that of `f64`.
- **`no_std` + `alloc` without `std` or `libm` builds again.** `CovarianceMatrix`
  called `f64::mul_add` directly, which only exists with `std`; it now goes
  through the same fused-multiply-add shim as the rest of the crate (`a * b +
  c` without a math provider). `math::powf` is added for the sub-crates.
- **`WindowedMin<T>` / `WindowedMax<T>`** departed from the kernel `win_minmax`
  algorithm they cite: a choice was replaced by age before its value was
  compared, and sub-windows were `window / 3` instead of the kernel's quarter
  and half with the "no distinct choice yet" guard. On stationary input the
  reported extremum disagreed with an exact window on 11 to 22% of updates
  (1 to 2% for the kernel algorithm), always in the direction of a max too
  low or a min too high. Both instantiations now share a literal port of
  `minmax_running_max` / `minmax_running_min` / `minmax_subwin_update`.
  Affected `CoDel` through its former `min_sojourn()` and any delay baseline built on
  `WindowedMin` ([#758](https://github.com/Abso1ut3Zer0/nexus/issues/758)).
- **`WindowedMin<T>` / `WindowedMax<T>` / `MinMaxNorm<T>` ignore a late
  sample** ([#799](https://github.com/Abso1ut3Zer0/nexus/issues/799)): a
  sample timestamped before the previous one read as a gap longer than the
  window under wrapping subtraction and reset the tracker to itself, so
  updates at 1000, 1030 and a late 1020 reported the late value as the max
  with a larger one still in the window, and `MinMaxNorm` returned 0.5 and
  misread the next sample. A sample timestamped before the previous
  accepted one is now ignored (no state change, not counted, the current
  extremum returned), so a late extreme value is dropped too; lateness is
  the signed difference, so a counter that wraps still works.
  `MinMaxNorm::update` normalizes a late sample against the current window
  and clamps it to [0, 1]. The trackers are 72 bytes (one more tick).
- **`CoDel<T>`** reported `Degraded` on a single sample above
  target. RFC 8289 requires sojourn to stay above target for a whole
  interval. It now implements the RFC's `first_above_time` rule directly:
  a sample above target arms a deadline at `now + interval`, a sample
  below target disarms it, and only a sample above target at or after the
  deadline is `Degraded`. A sample equal to the target counts as above
  ([#791](https://github.com/Abso1ut3Zer0/nexus/issues/791)). The windowed minimum the
  old composition relied on (and its own inaccuracy, #758) is gone.
  the builder's `interval` is the RFC's. `CoDelBuilder<f64>::build` now rejects a
  non-finite target ([#759](https://github.com/Abso1ut3Zer0/nexus/issues/759)).
- **`CoDel<T>` ignores a late sample** ([#797](https://github.com/Abso1ut3Zer0/nexus/issues/797)):
  a sample timestamped before the timer's start read as a huge elapsed time
  under wrapping subtraction, so one reordered sample right after the timer
  armed reported `Degraded` at once. A sample timestamped before the
  previous accepted one is now ignored (no state change, not counted, the
  current condition returned), with lateness judged by the signed
  difference so a counter that wraps still works. State is two timestamps
  (64 bytes). `standing_queue` is branch-free, so the update costs the same
  as before.

- **`Liveness`**: two defects. `update()` folded the gap
  into the smoothed interval before testing it, which made the test
  `dt <= m * (old + (dt - old) / 2^k)`; that is always true once
  `deadline_multiple >= 2^k` (for example span 7 with multiple 8), so
  `update()` could never report dead and otherwise disagreed with `check()`
  by one interval. It now judges each gap against the interval as it stood
  before the event, then folds. With both deadlines configured the absolute
  one was ignored; a gap is now dead if it exceeds either. Also: until a
  positive gap has been seen only the absolute deadline judges (from both
  `update()` and `check()`); a timestamp at or behind the previous one is
  alive and is no longer folded into the estimate, where a
  large backwards step could drive it negative and make the next real gap
  read dead; and the multiple product saturates
  ([#760](https://github.com/Abso1ut3Zer0/nexus/issues/760)).

- **`PeakHold<f64>`** returned `0.0` for a negative-only stream because the
  peak started at zero; it now seeds from the first sample, as the integer
  form always did ([#763](https://github.com/Abso1ut3Zer0/nexus/issues/763)).
- **`Jitter<f64>`** discarded a seeded jitter under `min_samples(1)`, since
  seeded state was inferred from the sample count; the smoother now carries
  an explicit seeded flag ([#763](https://github.com/Abso1ut3Zer0/nexus/issues/763)).
- `no_std` without `libm` compiles again (an unused `halflife` field in the
  `HitRate` builder); the `TwoScaleRv` rustdoc no longer emits broken links.
- `EventRate` folded a backwards or wrapped timestamp step as a negative
  interval, driving the accumulator negative (Liveness already re-anchored).
- `CovarianceMatrix::covariance(i, j)` only `debug_assert`ed its indices; an
  out-of-range query returned another cell in release. It panics, per policy.
- **`Hurst` allocated once more at its first full window.** `update` pushed
  before popping, so the deque briefly held `window_size + 1` values, one past
  its reservation, and grew on the first wrap. The window is a `storage::Ring`
  now: fixed at build, no deque.

### Docs

- `docs/normalization.md` is compiled and run as a doctest, and the
  `DistributionShift` section of `docs/detection.md` is rewritten against
  the new behavior. The `MinMaxNorm` example had its `update` arguments
  reversed.

- `docs/control.md`, `docs/detection.md` and `docs/smoothing.md` are compiled
  and run as doctests; their examples assert the values they describe. The
  pages had drifted: `Direction::Up`/`Down`, reversed `Hysteresis::new`
  arguments, a `LevelCrossing` example for the old return type.

- Every monitoring type states its **weighting clock** (per `update` call, per
  event with its timestamp, the caller's timestamps, or none) and the module
  docs carry the rule: never update a per-call type from a loop whose
  iteration time depends on the quantity being measured
  ([#762](https://github.com/Abso1ut3Zer0/nexus/issues/762)). `EventRate`
  documents that one stamp per batch breaks it and what to use instead;
  `WindowedMax` / `WindowedMin` document that the accessors reflect the last
  update ([#763](https://github.com/Abso1ut3Zer0/nexus/issues/763)).
- `nexus-stats-core/docs` rewritten against the shipped API: the `Instant`
  types it described never existed.
- `Hurst` states its cost: O(1) per `update`, O(window) per `hurst()` query.
- `feature_vector!`'s SAFETY comments cite the two compile-time assertions
  (size, alignment) that make them true, after
  [#788](https://github.com/Abso1ut3Zer0/nexus/pull/788) added the second.

## [3.0.1] — 2026-06-05

### Changed

- **Breaking:** Replaced `EventRateF64` / `EventRateI64` with `EventRateU64` / `EventRateI64` using integer timestamps and bit-shift EMA (same pattern as `LivenessI64`). The old `EventRateF64` incorrectly used `f64` timestamps; the new types use `u64` / `i64` timestamps with fixed-point `i128` accumulator and `span()` builder instead of `alpha()`.

## [3.0.0] — 2026-05-28

### Removed

- `EmaF32`, `EmaF32Builder`, `EmaI32`, `EmaI32Builder` — use `EmaF64` / `EmaI64`
- `AsymEmaF32`, `AsymEmaF32Builder`, `AsymEmaI32`, `AsymEmaI32Builder` — use `AsymEmaF64` / `AsymEmaI64`
- `SlewF32`, `SlewI32`, `SlewI128` — use `SlewF64` / `SlewI64`
- `CusumF32`, `CusumF32Builder`, `CusumI32`, `CusumI32Builder`, `CusumI128`, `CusumI128Builder` — use `CusumF64` / `CusumI64`
- `DistributionShiftF32`, `DistributionShiftI32`, `DistributionShiftI128` — use `DistributionShiftF64` / `DistributionShiftI64`
- `DeadBandF32`, `DeadBandI32`, `DeadBandI128` — use `DeadBandF64` / `DeadBandI64`
- `DebounceF32` — use `DebounceF64`
- `HysteresisF32`, `HysteresisI32`, `HysteresisI128` — use `HysteresisF64` / `HysteresisI64`
- `LevelCrossingF32`, `LevelCrossingI32`, `LevelCrossingI128` — use `LevelCrossingF64` / `LevelCrossingI64`
- `FirstDiffF32`, `FirstDiffI32`, `FirstDiffI128` — use `FirstDiffF64` / `FirstDiffI64`
- `SecondDiffF32`, `SecondDiffI32`, `SecondDiffI128` — use `SecondDiffF64` / `SecondDiffI64`
- `DrawdownF32`, `DrawdownI32`, `DrawdownI128` — use `DrawdownF64` / `DrawdownI64`
- `ErrorRateF32`, `ErrorRateF32Builder` — use `ErrorRateF64`
- `SaturationF32`, `SaturationF32Builder` — use `SaturationF64`
- `EventRateF32`, `EventRateF32Builder`, `EventRateI32`, `EventRateI32Builder` — use `EventRateF64` / `EventRateI64`
- `LivenessF32`, `LivenessF32Builder`, `LivenessI32`, `LivenessI32Builder` — use `LivenessF64` / `LivenessI64`
- `JitterF32`, `JitterF32Builder`, `JitterI32`, `JitterI32Builder` — use `JitterF64` / `JitterI64`
- `MaxGaugeF32`, `MaxGaugeI32`, `MaxGaugeI128` — use `MaxGaugeF64` / `MaxGaugeI64`
- `PeakHoldF32`, `PeakHoldF32Builder`, `PeakHoldI32`, `PeakHoldI32Builder`, `PeakHoldI128`, `PeakHoldI128Builder` — use `PeakHoldF64` / `PeakHoldI64`
- `RunningMaxF32`, `RunningMaxI32`, `RunningMaxI128` — use `RunningMaxF64` / `RunningMaxI64`
- `RunningMinF32`, `RunningMinI32`, `RunningMinI128` — use `RunningMinF64` / `RunningMinI64`
- `WindowedMaxF32`, `WindowedMaxI32`, `WindowedMaxI128` — use `WindowedMaxF64` / `WindowedMaxI64`
- `WindowedMinF32`, `WindowedMinI32`, `WindowedMinI128` — use `WindowedMinF64` / `WindowedMinI64`
- `CoDelF32`, `CoDelF32Builder`, `CoDelI32`, `CoDelI32Builder`, `CoDelI128`, `CoDelI128Builder` — use `CoDelF64` / `CoDelI64`
- `HawkesIntensityF32`, `HawkesIntensityF32Builder` — use `HawkesIntensityF64`
- `RollSpreadF32`, `RollSpreadF32Builder` — use `RollSpreadF64`
- `WelfordF32` — use `WelfordF64`
- `MomentsF32`, `MomentsI32` — use `MomentsF64` / `MomentsI64`
- `CovarianceF32` — use `CovarianceF64`
- `HarmonicMeanF32` — use `HarmonicMeanF64`
- `LpmF32`, `LpmF32Builder` — use `LpmF64`
- `CvarF32`, `CvarF32Builder` — use `CvarF64`

## [2.2.0] — 2026-05-20

### Added

- **`LpmF64/F32`** — Lower Partial Moments. Streaming downside risk
  with configurable target and integer order. Order 0 = shortfall
  probability, 1 = expected shortfall, 2 = semivariance.
  Convenience: `LpmF64::semivariance(target)`.
- **`CvarF64/F32`** — Conditional Value at Risk (Expected Shortfall).
  Streaming CVaR at configurable confidence level. Composes P²
  percentile internally.
- **`normalization` module** — Online feature normalization:
  - `ZScoreNormF64/F32` — EW z-score: `(x - mean) / std_dev`.
    Requires `std` or `libm`.
  - `MinMaxNormF64/F32` — Windowed min-max scaling to [0, 1].
  - `QuantileNormF64/F32` — Quantile transform via P² grid.
    Requires `alloc`.

## [2.1.0] — 2026-05-18

### Added

- **`BipowerVariationF64/F32`** — jump-robust volatility estimator using
  products of consecutive absolute returns. Barndorff-Nielsen & Shephard (2004).
- **`RollSpreadF64/F32`** — Roll's implicit spread estimator from
  autocovariance of consecutive price changes, with Hasbrouck (2009) adjustment.
  Requires `std` or `libm`.
- **`TwoScaleRvF64`** — two-scale realized variance, noise-corrected volatility
  estimator. Zhang, Mykland, Ait-Sahalia (2005). Requires `alloc` + `std`/`libm`.
- **`HawkesIntensityF64/F32`** — self-exciting point process intensity
  estimator. Models bursty event arrivals with exponential decay. Requires
  `std` or `libm`.

## [2.0.0] — 2026-05-18

Clock trait and Instant type removal.

### Added

- **`clock` module.** `Clock` trait (`stamp() -> u64`), `WallClock` (std,
  wraps `Instant`, returns elapsed nanos), `EpochClock` (manual/test clock
  with `set()`/`advance()`). Stats types accept `u64` timestamps; the caller
  owns the clock.
- **`elapsed(from, to)` helper** — saturating u64 subtraction.

### Removed

- **All `Instant`-based stats types.** `WindowedMax/MinF64/F32/I64/I32/I128`,
  `CoDelF64/F32/I64/I32/I128` (Instant variants), `LivenessInstant`,
  `EventRateInstant`, and `BucketAccumulator::update_instant()`. Epoch
  management belongs in the Clock, not the stats type.

### Changed

- **Renamed Raw variants to canonical.** `WindowedMaxF64Raw` → `WindowedMaxF64`,
  `CoDelF64Raw` → `CoDelF64`, etc. The `Raw` suffix was disambiguation for
  the now-removed Instant variants.

## [1.2.1] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
