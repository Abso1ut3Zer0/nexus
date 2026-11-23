# Changelog

All notable changes to nexus-stats-monitoring are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- The crate. The fifteen monitors move here from `nexus-stats-core`'s
  `monitoring` module. No change to any of them.
- `Condition`, `ConfigError`, `DataError` and `Sample` are re-exported, so
  the crate can be used without a direct dependency on `nexus-stats-core`.
