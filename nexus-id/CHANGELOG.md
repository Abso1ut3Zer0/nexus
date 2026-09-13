# Changelog

All notable changes to nexus-id are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Fixed

- `UuidV7` sequence counter wrapped through `u16::MAX` after exhaustion.
  `wrapping_add` incremented the counter past `SEQUENCE_MAX` (4095) on
  every error-returning call. After 61440 further calls the counter
  cycled back to `0`, and the next call succeeded with sequence `0`,
  reusing a value within the same millisecond. This produced duplicate
  and non-monotonic UUIDs. Fixed by checking `sequence >= SEQUENCE_MAX`
  before incrementing: once exhausted the counter stays at `4095`
  permanently and every subsequent call returns `SequenceExhausted`.


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
