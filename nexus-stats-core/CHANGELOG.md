# Changelog

All notable changes to nexus-stats-core are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Removed

- **`LivenessF64`** — f64 timestamps cause silent precision loss past 2^52; use `LivenessI64` or `LivenessU64`.

### Added

- **`LivenessU64`** — liveness detector with `u64` timestamps, mirrors `LivenessI64`.

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
