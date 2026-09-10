# Changelog

All notable changes to nexus-id are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed (breaking)

- `SequenceExhausted` is restored as a standalone struct with fields `tick: u64`
  and `max_sequence: u64`. It is no longer a type alias for `SnowflakeError`.
  ULID `try_next` and UUID v7 `next*` continue to return `SequenceExhausted`.
  Migration: replace any `SequenceExhausted::Exhausted { tick, max_sequence }`
  construction or pattern with `SequenceExhausted { tick, max_sequence }`.

- `SnowflakeError` is now a separate `#[non_exhaustive]` enum returned only by
  the six Snowflake methods (`next`, `mixed`, `next_id`, `mixed_id`,
  `next_signed`, `mixed_signed`). Variants: `Exhausted(SequenceExhausted)` and
  `TimestampOverflow { tick: u64, max: u64 }`. A `From<SequenceExhausted> for
  SnowflakeError` impl is provided for composition.
  Migration: change `SnowflakeError::Exhausted { max_sequence, .. }` patterns
  to `SnowflakeError::Exhausted(err)` and read `err.max_sequence`.

### Added

- `Snowflake::next()` now returns `Err(SnowflakeError::TimestampOverflow)`
  when the caller supplies a tick value that exceeds `TIMESTAMP_MAX` for the
  generator's bit layout. Previously the tick was silently truncated, producing
  IDs with the wrong timestamp and potentially colliding with earlier IDs at
  tick 0.

## [1.1.5] — 2026-05-10

Doc + bench infra release. No public API change.

### Changed

- README ID Generation and ID Types tables updated with measured
  floors from controlled-conditions runs (taskset-pinned P-cores,
  turbo on, best-of-5). Three claims drifted +14-21% from the
  previous numbers and are now corrected:
  - `UuidV4 → Uuid` (formatted): 48 → 58 cy
  - `UuidCompact::parse(32-char)`: 48 → 56 cy
  - `HexId64::parse(16-char)`: 42 → 48 cy
- Other claims (Snowflake64 generate, UuidV7, Ulid generate, Uuid
  parse, Ulid parse) verified within ±10% of prior numbers.

### Internal

- 4 perf benches moved from `examples/` to `benches/` with
  `harness = false`.
- Missing-doc additions across `parse` and `types` modules.

## [1.1.4] and earlier

`nexus-id` ships a broad family of ID generators (`Snowflake64`,
`Snowflake32`, `UuidV4`, `UuidV7`, `UlidGenerator`) and the
corresponding ID types (`Uuid`, `UuidCompact`, `Ulid`, `HexId64`,
`Base62Id`, `Base36Id`, `TypeId`, `MixedId64`, `SnowflakeId64`/`32`).
SIMD-accelerated hex encode/decode (SSSE3 / SSE2) on x86_64, with a
scalar fallback that is also used as the parity-test reference.

Earlier per-version history is not documented here. See git history
and GitHub release notes for details.
