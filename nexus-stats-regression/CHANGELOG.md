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

### Fixed

- **`no_std` + `libm` builds again.** `PowerRegression::predict` and
  `EwPowerRegression::predict` called `f64::powf` directly, which only exists
  with `std`; they now use `nexus_stats_core::math::powf` (`libm::pow` under
  `libm`).
- **`Exp3::select` could alias its scratch buffer from safe code.** The
  caller's `rng` closure ran while the `&mut` into the internal `UnsafeCell`
  scratch was live, so a closure that re-entered `select` on the same
  `&Exp3` created a second `&mut` to the same memory. The random draw now
  happens before the borrow, so no caller code runs while it is live. The
  type doc states that `Exp3` is `!Sync`.
- **`RlsFilter::covariance` doc** said "P matrix diagonal"; it returns the
  full d×d row-major matrix, and now says so.

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
