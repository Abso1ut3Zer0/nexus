# Changelog

All notable changes to nexus-stats-control are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed

- **No numeric suffixes** (the stats major, [#773](https://github.com/Abso1ut3Zer0/nexus/issues/773)): `BoolWindow`, `TopK`, `FlexProportion*`
  were already plain; `DecayAccumU64` → `DecayAccum` (ticks are `u64`).
- **`PeakDetector<T>`** replaces `PeakDetectorF64` / `PeakDetectorI64`: one
  generic type bounded by `nexus_stats_core::Sample` (`f64`, `i64`) returning
  `Peak<T>`. `update` returns `Result` for `f64` and the option directly for
  `i64`. Construct as `PeakDetector::<i64>::new(prominence)`.

### Removed

- **`DecayAccumI64`**: ticks are `u64` (the clock contract); `DecayAccum` is
  the former `DecayAccumU64`.
- **`DecayAccumF64`** — f64 timestamps cause silent precision loss past 2^52; replaced by `DecayAccum` (`u64` ticks).

### Added 

- **`DecayAccumU64`** — decaying accumulator with `u64` timestamps.
- **`DecayAccumI64`** — decaying accumulator with `i64` timestamps.

## [2.0.0] — 2026-05-28

### Removed

- `PeakDetectorF32` — use `PeakDetectorF64`
- `PeakDetectorI32` — use `PeakDetectorI64`
- `PeakDetectorI128` — use `PeakDetectorI64`

## [1.0.3] — 2026-05-26

## [1.0.2] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
