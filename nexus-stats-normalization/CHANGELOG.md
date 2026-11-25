# Changelog

All notable changes to nexus-stats-normalization are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed (breaking)

- **`MinMaxNorm` takes any `Timestamp`,** which now includes `i64`
  nanoseconds, the named time types and a caller's own time type. An
  unsuffixed integer literal no longer infers as a timestamp; write
  `0_i64`.

### Changed (breaking, time)

- **`MinMaxNorm<V, T>` takes time as `i128` nanoseconds or `Instant`,**
  through the `Timestamp` trait, with a second type parameter for the
  clock. `window` takes a `Duration`.

### Changed (dependencies)

- `ZScoreNorm` now takes `EwmVar` from `nexus-stats-smoothing`, a new dependency of this crate.

### Added

- The crate. `ZScoreNorm`, `MinMaxNorm` and `QuantileNorm` move here from
  `nexus-stats-core`'s `normalization` module. No change to any of them.
- `ConfigError`, `DataError` and `Float` are re-exported, so the crate can
  be used without a direct dependency on `nexus-stats-core`.
