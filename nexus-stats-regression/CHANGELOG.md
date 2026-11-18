# Changelog

All notable changes to nexus-stats-regression are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed

- **No numeric suffixes** (the stats major, [#773](https://github.com/Abso1ut3Zer0/nexus/issues/773)). Every type here is `f64` and is named
  plainly: `LinearRegressionF64` → `LinearRegression`, `RlsFilterF64` →
  `RlsFilter`, `Ucb1F64` → `Ucb1`, `OnlineKMeansF64` → `OnlineKMeans`, and
  so on; builders follow.
- **Builders are NaN-safe and complete:** LMS/NLMS (`learning_rate`,
  `epsilon`), RLS (`forgetting_factor`, `initial_covariance`, and
  `max_covariance`, which must be finite and above `initial_covariance`),
  Kalman2d/3d (`measurement_noise`, plus finite `process_noise`,
  `initial_covariance`, `initial_state`) and logistic regression
  (`learning_rate`) reject NaN where `<= 0.0` let it through.
- **EW regressions reject `alpha >= 1/(number of coefficients)`:** the
  effective sample size approaches `1/alpha` from below, so such a fit could
  never prime and returned `None` forever.
- **Range errors are `DataError::OutOfRange`**, not `Negative`: ThompsonBeta /
  Exp3 reward outside `[0, 1]`, Exp3 `prob` outside `(0, 1]`, ThompsonGamma
  non-positive reward. `GammaPoisson::update` rejects negative exposure.
- **Float slices are the caller's to validate** (features, Kalman `h`):
  debug-asserted, as in every mainstream numeric library; the scalar
  `check_finite` policy is unchanged.
- **`LaggedPredictor` keeps its estimate history in a
  `nexus_stats_core::storage::Ring`** instead of a `VecDeque`: `push` hands
  back the estimate from `lag` updates ago, no `expect`, no deque bookkeeping.
  `SignalDecayCurve` stores its predictors and lags as boxed slices. Same API,
  same results.
- **The four count-based bandits share one arm bank.** `Ucb1`,
  `EpsilonGreedy`, `ThompsonBeta` and `ThompsonGamma` keep their per-arm
  pairs in one `pub(crate)` kernel: the same `arm >= num_arms` panic, the
  same `decay` validation (`(0, 1]`, NaN rejected) and the same
  decay-toward-reference step. No API change.
- **`Exp3::select` takes `&mut self`.** The scratch buffer is a plain
  `Box<[f64]>`; the `UnsafeCell` is gone with the `!Sync` caveat, and `Exp3`
  is `Clone` and `Debug`.
- **Renames.** `intercept_value()` → `intercept()` on `LinearRegression`,
  `EwLinearRegression` and the transformed regressions (the builder flag keeps
  `intercept(bool)`); the bandits' `total_pulls()` is gone, `count()` is the
  same number.
- **Every EW builder has `halflife(h)`** (`std` or `libm`):
  `EwLinearRegression`, `EwPolynomialRegression`, `KyleLambda`,
  `EwExponentialRegression`, `EwLogarithmicRegression`, `EwPowerRegression`.
- **Builder validation uses the core predicates:** an infinite
  `learning_rate`, `epsilon` or `weight_decay` (`Adam`) or prior parameter
  (`BetaBinomial`, `GammaPoisson`) is rejected like NaN.
- **`Coefficients::eval(x)`** evaluates the fitted polynomial;
  `PolynomialRegression::predict` is `coefficients()?.eval(x)`. `Kalman2d`
  and `Kalman3d` gain `is_primed()`.
- **One copy of each kernel.** LMS, NLMS, RLS, Huber and `OnlineGd` use
  `math::dot` / `math::axpy`; `BetaBinomial` and `GammaPoisson` share
  `math::upper_tail_z`. The existing tests pass unchanged.

### Fixed

- **`no_std` + `libm` builds again.** `PowerRegression::predict` and
  `EwPowerRegression::predict` called `f64::powf` directly, which only exists
  with `std`; they now use `nexus_stats_core::math::powf` (`libm::pow` under
  `libm`).
- **`Exp3::select` could alias its scratch buffer from safe code.** The
  caller's `rng` closure ran while the `&mut` into the internal `UnsafeCell`
  scratch was live, so a closure that re-entered `select` on the same
  `&Exp3` created a second `&mut` to the same memory. `select` now takes
  `&mut self` and the scratch is a plain `Box<[f64]>`, so the borrow checker
  enforces the exclusivity (see Changed).
- **`RlsFilter::covariance` doc** said "P matrix diagonal"; it returns the
  full d×d row-major matrix, and now says so.
- **Singular fits returned garbage.** `gauss_solve_f64` judged singularity
  with an absolute `1e-14` pivot on an unscaled normal matrix (entries
  `~ n·x^2d`): rank-deficient data at large |x| solved to nonsense, well-posed
  small-|x| cubics were called singular, and NaN passed every test. It now
  uses a relative tolerance, treats NaN as singular and checks the solution is
  finite. `LinearRegression` / `EwLinearRegression` guarded on `denom == 0.0`,
  which constant x never hits exactly; they use the rounding bound of the two
  cancelled terms and return `None`.
- **Thompson decay collapsed un-pulled arms.** Multiplying `(alpha, beta)` by
  `decay` every update drove an un-pulled arm's posterior toward zero, where
  `beta_sample` hit a fabricated `0.5` and the arm was always or never
  selected (Gamma: `0/0`). Both bandits decay toward the prior; the sentinel
  is gone.
- **Kalman2d/3d `S.max(EPSILON)` masked a degraded or NaN covariance** into a
  gain of `~1e15`; a non-positive innovation covariance now restores P and
  skips the measurement, and P is re-symmetrized after every update (the
  `(I-KH)P` form drifts asymmetric). `RlsFilter`'s denominator floor had the
  same shape and gets the same treatment.

## [2.0.0] — 2026-05-28

### Removed

- `LinearRegressionF32`, `LinearRegressionF32Builder` — use `LinearRegressionF64`
- `EwLinearRegressionF32`, `EwLinearRegressionF32Builder` — use `EwLinearRegressionF64`
- `CoefficientsF32` — use `CoefficientsF64`
- `PolynomialRegressionF32`, `PolynomialRegressionF32Builder` — use `PolynomialRegressionF64`
- `EwPolynomialRegressionF32`, `EwPolynomialRegressionF32Builder` — use `EwPolynomialRegressionF64`
- `ExponentialRegressionF32` — use `ExponentialRegressionF64`
- `LogarithmicRegressionF32` — use `LogarithmicRegressionF64`
- `PowerRegressionF32` — use `PowerRegressionF64`
- `BetaBinomialF32`, `BetaBinomialF32Builder` — use `BetaBinomialF64`
- `GammaPoissonF32`, `GammaPoissonF32Builder` — use `GammaPoissonF64`
- `Kalman2dF32`, `Kalman2dF32Builder` — use `Kalman2dF64`
- `Kalman3dF32`, `Kalman3dF32Builder` — use `Kalman3dF64`
- `Ucb1F32`, `Ucb1F32Builder` — use `Ucb1F64`
- `ThompsonBetaF32`, `ThompsonBetaF32Builder` — use `ThompsonBetaF64`
- `ThompsonGammaF32`, `ThompsonGammaF32Builder` — use `ThompsonGammaF64`
- `EpsilonGreedyF32`, `EpsilonGreedyF32Builder` — use `EpsilonGreedyF64`
- `Exp3F32`, `Exp3F32Builder` — use `Exp3F64`
- `RlsFilterF32`, `RlsFilterF32Builder` — use `RlsFilterF64`
- `LmsFilterF32`, `LmsFilterF32Builder` — use `LmsFilterF64`
- `NlmsFilterF32`, `NlmsFilterF32Builder` — use `NlmsFilterF64`

## [1.3.1] — 2026-05-26

## [1.3.0] — 2026-05-19

### Added

- **`Ucb1F64/F32`** — UCB1 multi-armed bandit. Deterministic selection,
  no RNG needed. Auer, Cesa-Bianchi, Fischer (2002).
- **`ThompsonBetaF64/F32`** — Thompson Sampling with Beta conjugate
  prior for binary/[0,1] rewards. Thompson (1933).
- **`ThompsonGammaF64/F32`** — Thompson Sampling with Gamma conjugate
  prior for positive continuous rewards.
- **`EpsilonGreedyF64/F32`** — Epsilon-greedy bandit. Simplest baseline.
- **`Exp3F64/F32`** — EXP3 adversarial bandit. Robust to non-stochastic
  rewards. Auer, Cesa-Bianchi, Freund, Schapire (2002).
- UCB1, ThompsonBeta, ThompsonGamma, and EpsilonGreedy support
  exponential discounting via `decay` parameter for non-stationary
  reward environments. EXP3 handles non-stationarity through its
  `gamma` exploration mixing rate.
- Internal sampling utilities (Marsaglia polar, Marsaglia-Tsang Gamma,
  Beta from Gamma ratio).

All bandit types require `alloc` + (`std` or `libm`).

## [1.2.0] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
