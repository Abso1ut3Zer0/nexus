# Changelog

All notable changes to nexus-stats-detection are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed

- **No numeric suffixes** (the stats major, [#773](https://github.com/Abso1ut3Zer0/nexus/issues/773)): `CusumF64`-style names become plain
  (`MosumF64` → `Mosum`, `AdaptiveThresholdF64` → `AdaptiveThreshold`,
  `TrendAlertF64` → `TrendAlert`, `AutocorrelationF64` → `Autocorrelation`,
  `BocpdF64` → `Bocpd`, ...); builders follow.
- **`RobustZScore<T>`** replaces `RobustZScoreF64` / `RobustZScoreF32`: a
  `Float` generic (`f64`, `f32`) that takes and returns `T` but keeps its EMA
  baseline and absolute-deviation scale in `f64`, so the `f32` form is a
  boundary type for `f32` feature pipelines, no longer an `f32` accumulator.
- **Hot-path pass before release.** `Autocorrelation`, `CrossCorrelation`,
  `TransferEntropy` and `Mosum` advance their ring index with a compare
  instead of a division; `CrossCorrelation` walks its ring newest-first
  through one iterator, removing the per-lag `% lag` from its inner loop.
  `PageHinkley` tracks its running extrema with selects instead of branches.

### Removed

- **`MosumI64`**, **`AutocorrelationI64`** ([#379](https://github.com/Abso1ut3Zer0/nexus/issues/379)):
  no integer count-stream caller for MOSUM; autocorrelation is fractional.
  Use `Mosum` and `Autocorrelation` on `f64`.

### Fixed

- **`alloc` + `libm` without `std` builds again.** `Bocpd` called
  `f64::mul_add` directly; it now uses the core fused-multiply-add shim.
- **The AVX2 `exp` kernel was wrong by r²/2 on every reduced argument.**
  `simd_math::exp_sum` (used by `Bocpd` on `+avx2,+fma` builds) evaluated
  musl's polynomial in `r` instead of `r²` and used `r²·P` where musl's
  `c = r - r²·P(r²)` belongs, which drops the r²/2 term of `exp(r)`: an error
  of up to 8% per term at |r| = ln(2)/2. Nothing caught it because the kernels
  are compiled only under `+avx2,+fma`, no CI job set that for this crate, and
  nothing compared them to the scalar kernels. The kernel now follows musl
  exactly; a per-element parity test (4096 draws over the kernel's range) and
  an `exp_sum` / `ln_inplace` parity test over all tail lengths run on a new
  `+avx2,+fma` CI leg. Default-target builds were never affected. The module
  doc said `+avx2`; it says `+avx2,+fma`.

## [2.0.0] — 2026-05-28

### Removed

- `TrendAlertF32`, `TrendAlertF32Builder` — use `TrendAlertF64` (dependency `HoltF32` removed from smoothing crate)
- `MosumF32`, `MosumF32Builder` — use `MosumF64`
- `MosumI32`, `MosumI32Builder` — use `MosumI64`
- `MosumI128`, `MosumI128Builder` — use `MosumI64`
- `MultiGateF32`, `MultiGateF32Builder` — use `MultiGateF64`
- `PageHinkleyF32`, `PageHinkleyF32Builder` — use `PageHinkleyF64`
- `AdwinF32`, `AdwinF32Builder` — use `AdwinF64`
- `DistDriftF32`, `DistDriftF32Builder` — use `DistDriftF64`
- `AutocorrelationF32`, `AutocorrelationF32Builder` — use `AutocorrelationF64`
- `AutocorrelationI32`, `AutocorrelationI32Builder` — use `AutocorrelationI64`
- `CrossCorrelationF32`, `CrossCorrelationF32Builder` — use `CrossCorrelationF64`
- `EntropyF32`, `EntropyF32Builder` — use `EntropyF64`
- `PredictiveInfoBoundF32`, `PredictiveInfoBoundF32Builder` — use `PredictiveInfoBoundF64`

### Changed

- `TrendAlertF64Builder::build` now rejects negative and non-finite trend thresholds

## [1.2.0] — 2026-05-20

### Added

- **`DistDriftF64` / `DistDriftF32`** — distribution drift metrics: KL divergence,
  Jensen-Shannon divergence, Wasserstein-1 distance over reference/live histograms.
  Equi-width bins with Laplace smoothing. Requires `alloc` + (`std` or `libm`).
- **`BocpdF64`** — Bayesian Online Change Point Detection (Adams & MacKay 2007).
  Gaussian observation model, Normal-Inverse-Gamma conjugate prior, truncated
  run-length posterior. O(W) per update. Requires `alloc` + (`std` or `libm`).
- **`nexus_stats_core::math::ln_gamma`** — Lanczos approximation for log-gamma (f64).
- **`nexus_stats_core::math::ln_f32`** / **`exp_f32`** — f32 transcendental functions.

## [1.1.0] — 2026-05-18

### Added

- **`PageHinkleyF64` / `PageHinkleyF32`** — sequential test for mean drift.
  O(1) per update, two-sided (detects upward and downward shifts).
- **`AdwinF64` / `AdwinF32`** — adaptive windowing for distribution change
  detection (Bifet & Gavalda, 2007). O(log n) per update, O(log n) memory.
  Requires `alloc` + (`std` or `libm`).
- **`PredictiveInfoBoundF64` / `PredictiveInfoBoundF32`** — streaming binned
  mutual information I(X;Y) with Miller-Madow bias correction. Equi-width
  bins on user-specified ranges. Requires `alloc` + (`std` or `libm`).

## [1.0.1] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
