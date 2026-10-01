# Changelog

All notable changes to nexus-rate are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

## [2.1.4] — 2026-10-01

### Added

- `try_acquire` now `debug_assert!`s that `cost` does not exceed the limiter's
  capacity — `burst` for the token bucket, the `burst + 1` tolerance for GCRA,
  the window `limit` for the sliding window. A request larger than capacity can
  never be admitted and would otherwise starve silently in a caller's retry
  loop; the assert surfaces that misconfiguration in dev. Release builds are
  unchanged: the oversized request still returns `false` via saturating
  arithmetic (the graceful safety-net). Applies to the `local` and `sync`
  variants of every limiter. GCRA's `time_until_allowed` carries the same
  assert: for such a request no finite wait is correct, so it must not
  report one.

### Fixed

- Token bucket (`local` and `sync`) admitted unbounded requests after an
  idle period longer than one burst. `try_acquire` advanced `zero_time`
  from its stored value with no clamp, so a long gap banked unlimited
  credit while `available()` kept reporting `burst`. `zero_time` is now
  clamped to `now - burst * nanos_per_token` before consuming
  ([#749](https://github.com/Abso1ut3Zer0/nexus/issues/749)).

## [2.1.3] — 2026-05-10

Doc + bench infra release. No public API change.

### Changed

- README "performance" tables replaced with measured floors from
  controlled-conditions runs (taskset-pinned P-cores, turbo on,
  best-of-5). Previous claim ("2-4 cycle hot path") was for the
  pure algorithm body; the bench measures realistic per-call cost
  including `Instant + Duration` construction inside the timed
  window. Updated tables: Local variants 11-16cy; Sync variants
  11-29cy; rejection paths included.

### Internal

- `examples/perf_rate.rs` moved to `benches/perf_rate.rs` with
  `harness = false` so `cargo bench -p nexus-rate` discovers it.
- New `BENCHMARKS.md` documenting methodology + baseline tables.

## [2.1.2] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
