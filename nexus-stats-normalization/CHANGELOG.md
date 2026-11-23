# Changelog

All notable changes to nexus-stats-normalization are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- The crate. `ZScoreNorm`, `MinMaxNorm` and `QuantileNorm` move here from
  `nexus-stats-core`'s `normalization` module. No change to any of them.
- `ConfigError`, `DataError` and `Float` are re-exported, so the crate can
  be used without a direct dependency on `nexus-stats-core`.
