# Changelog

All notable changes to nexus-id are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

## [3.0.0] — 2026-09-19

## [2.0.0] — 2026-09-19

### Added

- `Snowflake::next()` now returns `Err(SnowflakeError::TimestampOverflow)`
  when the caller supplies a tick value that exceeds `TIMESTAMP_MAX` for the
  generator's bit layout. Previously the tick was silently truncated, producing
  IDs with the wrong timestamp and potentially colliding with earlier IDs at
  tick 0.
- `Snowflake::try_new(worker) -> Result<Self, WorkerIdError>` — a non-panicking
  constructor that returns `Err(WorkerIdError { worker, max })` when
  `worker > WORKER_MAX`. `Snowflake::new` still panics (it now delegates to
  `try_new`). The new `WorkerIdError` type is exported from the crate root and
  implements `std::error::Error` under the `std` feature.
- `TryFrom<&[u8]>` for `Uuid`, `UuidCompact`, and `Ulid`, delegating to
  `from_be_bytes` (error type matches `from_be_bytes`).
- `nil()` const constructors and `Default` impls (the all-zero value) for
  `Uuid`, `UuidCompact`, and `Ulid`.
- `PartialOrd` + `Ord` for `HexId64`, `Base62Id`, and `Base36Id`, ordering by
  the underlying decoded `u64`.
- `Debug` and `Clone` for the `Snowflake` generator, matching the other
  generators.
- `TypeId` now defaults its capacity parameter to `TypeId<32>`, so the const
  generic can be omitted for prefixes up to 5 characters.
- Little-endian byte output for the 128-bit ID types: `to_le_bytes()`,
  `from_le_bytes()`, and `from_le_bytes_unchecked()` on `Uuid`, `UuidCompact`,
  and `Ulid`. These are the byte-reverse of the canonical big-endian form
  (same semantics as `u128::to_le_bytes`) and are provided for little-endian
  wire protocols such as SBE / CME MDP. Big-endian remains canonical:
  `TryFrom<&[u8]>` is unchanged (still big-endian).
- `put_to_le` on all five `bytes`-crate integration types (`Uuid`,
  `UuidCompact`, `Ulid`, `SnowflakeId64`, `SnowflakeId32`), writing the
  little-endian representation into a `BufMut`. For the 128-bit types the
  output is exactly `to_le_bytes()`.

### Changed (breaking)

- `UlidGenerator::next(now)` is now fallible: it returns
  `Result<Ulid, SequenceExhausted>` (previously infallible, silently wrapping
  the 80-bit random field on overflow). The separate `try_next` method is
  removed — there is now a single `next` that errors, mirroring the `ulid`
  crate's `Generator::generate() -> Result`. Migration: add `?` or `.unwrap()`
  to `next` calls.
- Timestamp accessors renamed for clarity and consistency:
  `timestamp_ms()` → `timestamp_millis()` on `Ulid`, `Uuid`, and `TypeId`;
  `timestamp()` → `tick()` on the Snowflake typed IDs (`SnowflakeId64`,
  `SnowflakeId32`), since that field is a generic tick, not necessarily
  milliseconds. `Uuid::timestamp_millis()` still returns `Option<u64>`.
- Binary-bytes methods renamed on `Uuid`, `UuidCompact`, and `Ulid`:
  `to_bytes()` → `to_be_bytes()`, `from_bytes()` → `from_be_bytes()`,
  `from_bytes_unchecked()` → `from_be_bytes_unchecked()`. The `as_bytes()`
  method (which returns the ASCII *text* bytes) is unchanged.
- `decode()` → `to_raw()` on the value types `Uuid` and `UuidCompact` (returns
  the raw 128-bit `(hi, lo)` value, the inverse of `from_raw`). The encoded ID
  types `HexId64`, `Base62Id`, and `Base36Id` keep their `encode`/`decode`
  pair.
- The parse-error enums `ParseError`, `UuidParseError`, `DecodeError`, and
  `TypeIdParseError` are now `#[non_exhaustive]`. Downstream `match` expressions
  over these types must add a wildcard (`_`) arm.

- The `bytes`-crate `put_to` method is renamed to `put_to_be` on all five
  integration types (`Uuid`, `UuidCompact`, `Ulid`, `SnowflakeId64`,
  `SnowflakeId32`), pairing with the new `put_to_le`. Migration: rename
  `.put_to(buf)` calls to `.put_to_be(buf)`.

- The `Debug` output of the Snowflake typed IDs (`SnowflakeId64`,
  `SnowflakeId32`) now labels the ordering field `tick=` instead of `ts=`,
  matching the renamed `tick()` accessor. Migration: update any code or tests
  that pin the `ts=` substring.

- `SequenceExhausted` is restored as a standalone struct with fields `tick: u64`
  and `max_sequence: u64`. It is no longer a type alias for `SnowflakeError`.
  ULID `next` and UUID v7 `next*` continue to return `SequenceExhausted`.
  Migration: replace any `SequenceExhausted::Exhausted { tick, max_sequence }`
  construction or pattern with `SequenceExhausted { tick, max_sequence }`.

- `SnowflakeError` is now a separate `#[non_exhaustive]` enum returned only by
  the six Snowflake methods (`next`, `mixed`, `next_id`, `mixed_id`,
  `next_signed`, `mixed_signed`). Variants: `Exhausted(SequenceExhausted)` and
  `TimestampOverflow { tick: u64, max: u64 }`. A `From<SequenceExhausted> for
  SnowflakeError` impl is provided for composition.
  Migration: change `SnowflakeError::Exhausted { max_sequence, .. }` patterns
  to `SnowflakeError::Exhausted(err)` and read `err.max_sequence`.

### Fixed

- `Ulid::from_raw` no longer silently truncates a `timestamp_ms` that exceeds
  48 bits. Debug builds now `debug_assert!` the value fits in 48 bits, release
  builds mask explicitly to the low 48 bits, and the behavior is documented.
- `SequenceExhausted`'s `Display` impl no longer panics in debug builds when
  `max_sequence == u64::MAX` (as passed by the ULID generator): it now uses
  `saturating_add(1)` instead of `+ 1`.
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
