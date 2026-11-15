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

### Removed

- `SaturationF64` ([#761](https://github.com/Abso1ut3Zer0/nexus/issues/761)),
  `LivenessF64`, `LivenessI64`, `EventRateI64`, `update_i64` on the windowed
  extrema and CoDel, `CoDel::min_sojourn` (core); `MosumI64`,
  `AutocorrelationI64` ([#379](https://github.com/Abso1ut3Zer0/nexus/issues/379),
  detection); `DecayAccumF64` (control).

### Added

- `PollSaturation` / `PollSummary` ([#764](https://github.com/Abso1ut3Zer0/nexus/issues/764))
  and `SojournSaturation` / `SojournSummary` ([#770](https://github.com/Abso1ut3Zer0/nexus/issues/770)):
  a consumer thread's saturation from its poll outcomes, or from stamped
  queue sojourns.

### Fixed

- Carried from core: `WindowedMin` / `WindowedMax` kernel-exact
  ([#758](https://github.com/Abso1ut3Zer0/nexus/issues/758)), `CoDel` RFC 8289
  `first_above` rule ([#759](https://github.com/Abso1ut3Zer0/nexus/issues/759)),
  `Liveness` deadlines ([#760](https://github.com/Abso1ut3Zer0/nexus/issues/760)),
  `PeakHold<f64>` negative-only streams and `Jitter<f64>` seeding
  ([#763](https://github.com/Abso1ut3Zer0/nexus/issues/763)).

### Docs

- Every page under `docs/`, the README and the sub-crate docs use the new
  names. The type matrix and the integer-vs-float guide are rewritten; the
  README's type-variant table is replaced by a numeric-types section. About
  150 stale code examples are fixed against the shipped API (methods and
  builder options that never existed, unhandled `Result`s, removed types).
  `docs/algorithms/saturation.md` is replaced by `poll-saturation.md` and
  `sojourn-saturation.md`.

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
