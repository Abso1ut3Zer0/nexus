# Changelog

All notable changes to nexus-stats-control are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Removed

- **`DecayAccumF64`** — f64 timestamps cause silent precision loss past 2^52; replaced by `DecayAccumU64` and `DecayAccumI64`.

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
