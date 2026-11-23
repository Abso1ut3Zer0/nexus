# Changelog

All notable changes to nexus-stats-trading are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed (internal)

- `RollSpread`, `Lpm`, `BipowerVariation` and `TwoScaleRv` keep their
  sample count and warm-up threshold in the shared `Warmup` part, and
  `RollSpread` its weight in `Weight`. No change in results.

### Changed (dependencies)

- `Amihud` now takes `Ema` from `nexus-stats-smoothing`, a new dependency of this crate.

### Added

- The crate. `VarianceRatio`, `TwoScaleRv`, `BipowerVariation`, `Amihud`,
  `RollSpread`, `Lpm` and `Cvar` move here from `nexus-stats-core`'s
  `statistics`, and `KyleLambda` from `nexus-stats-regression` (behind the
  `regression` feature, on by default). No change to any of them.
- `Accuracy`, `ConfigError` and `DataError` are re-exported, so the crate
  can be used without a direct dependency on `nexus-stats-core`.
