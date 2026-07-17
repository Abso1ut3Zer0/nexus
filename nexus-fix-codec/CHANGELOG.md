# Changelog

All notable changes to nexus-fix-codec are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- `SessionCustomizer`, `AdminMsgOut`, and `NoCustomizer` — the per-venue hook for
  Logon authentication. Venues (Coinbase, Binance, Deribit) compute their auth
  over engine-assigned `MsgSeqNum(34)`/`SendingTime(52)`, so it can be neither
  static configuration nor generated from a FIX XML dictionary. The engine runs
  the hook after stamping the session header and before framing computes
  `BodyLength(9)`/`CheckSum(10)`, so injected fields — `Username(553)`,
  `Password(554)`, `RawData(96)` — are covered by both, and signatures can be
  taken over the header as stamped. `AdminMsgOut` exposes read accessors
  (`seq_num`, `sending_time`, `sender`, `target`, `msg_type`) alongside `field`
  for exactly that reason.

  Hooks are per message type (`configure_logon`, `configure_heartbeat`, …) and
  default to no-ops, so a venue implements only what it customizes and cannot
  leak Logon credentials into every Heartbeat — the miswiring QuickFIX's single
  undifferentiated `toAdmin` forces callers to hand-guard against.

  Writing an engine-owned tag from a hook trips a `debug_assert`: it is a
  programming error in expert-authored, once-per-venue code, and the failure is
  immediate and loud on the wire. The check is **per message** (via the new
  `AdminKind`, which also single-sources each message's `MsgType(35)`): the
  session framing and header it stamps on every admin (8, 9, 10, 34, 35, 49, 52,
  56) plus the params that message's own encoder writes — `108` on a Logon,
  `141` on a Logon carrying `ResetSeqNumFlag`, `7`/`16` on a ResendRequest, and
  so on. A tag the engine owns on one message is the venue's to write on another
  (`108` is engine-owned on a Logon, writable on a Heartbeat).

- `FieldSpan` and `GroupSpan` zero-copy field reference types
- SIMD SOH and `=` scanning: AVX-512, AVX2, SSE2, SWAR, scalar
- `DelimiterScanner` iterator with SIMD mask caching
- `FieldReader`, a pure SOH-delimiter scanner; the FIX checksum is a separate
  single-pass `verify_checksum` (not fused into the scan), so a trusted feed can
  skip verification entirely
- `FieldView::get_unchecked` — bypass printable-ASCII validation on text fields
  for trusted venues (`unsafe`)
- `FieldWriter` for writing `tag=value\x01` fields
- `parse_tag`, `find_tag`, `checksum`, `validate_checksum` helpers
- `encode_field`, `format_checksum` writer helpers
- `DecodeError` and `ChecksumError` error types
- Cycle-level benchmarks (`examples/perf_scan.rs`)
- Value-type parsers/encoders: `FixDecimal`, `FixDate`, `FixTime`,
  `FixTimestamp`; `parse_fix_int`/`uint`/`seqnum`/`bool` and their encoders
- `parse_fix_char` / `encode_fix_char` — FIX `char` → `AsciiChar`
- `parse_fix_text` — FIX `String`/`Currency`/`Exchange`/`Country`/`Language`/
  `Symbol` as a zero-copy printable-ASCII `AsciiTextStr` (text *encoding* is a
  plain `as_bytes()` copy, so there is no `encode_fix_text`)
- `parse_fix_day_of_month` — `DayOfMonth` (`1..=31`)
- `FixMonthYear` — `YYYYMM` / `YYYYMMDD` / `YYYYMM`+`wW`, byte-exact round-trip
- `FixTenor` and `TenorUnit` — FIX 5.0 SP2 `Tenor` (`[DWMY]<n>`, canonical form)
- `parse_fix_multi_char` / `parse_fix_multi_string` — `MultipleCharValue` /
  `MultipleStringValue` as zero-allocation borrowing iterators
- `FixTzTime` / `FixTzTimestamp` — `TZTimeOnly` / `TZTimestamp`, offset-preserving
- `FixValueError` — value-level parse error (`Empty`, `NotNumeric`, `Overflow`,
  `OutOfRange`, `BadFormat`, `NotPrintable`)
- Re-exports of `nexus_ascii::{AsciiChar, AsciiText, AsciiTextStr}`
- Type-parser benchmarks (`benches/parse_types.rs`, `benches/perf_parse_cycles.rs`)
- `MAX_VALUE_ENCODE_LEN` — the maximum bytes any owned value type encodes to
  (33, the worst-case `FixTzTimestamp`). Generated encoder scratch buffers for
  owned value types size to it, so a buffer can never fall behind a type's
  `encode()` width.
- `EncodeError::GroupCountMismatch { declared, written }` — surfaced by a
  generated `finish_group()` when the declared `NumInGroup` count does not match
  the entries written (see Changed).

### Changed

- **Breaking:** `FixDictionary::encode_*` now write their standard fields into a
  caller-owned `&mut FrameFormatter` and return `()`, instead of owning
  `FrameFormatter::new`/`finish` over a `&mut [u8]` and returning
  `Option<(usize, usize)>`. The caller owns the frame lifecycle so it can run a
  `SessionCustomizer` between the standard fields and `finish()`. This keeps the
  dictionary customizer-agnostic — no `Config` associated type, no customizer
  threaded through the trait. Generated dictionaries are unaffected: codegen
  emits only associated types, `BEGIN_STRING`, and `is_admin`, and inherits every
  `encode_*` default body.
- Value parsers now return `Result<T, FixValueError>` instead of `Option<T>`,
  surfacing the granular failure reason. Field *absence* is unchanged — it
  remains an `Option` at the lookup layer (`find_tag`), never a parse error.
- `FixDecimal`/`FixTimestamp`/`FixDate`/`FixTime` `encode` methods now perform
  a single up-front capacity `assert!` (atomic, clearly-messaged failure)
  rather than panicking mid-write.
- `nexus-ascii` is now a core (non-optional) dependency.
- Generated `{Group}Enc::finish_group()` now returns
  `Result<_, EncodeError>` instead of panicking on a declared-vs-written
  `NumInGroup` count mismatch; the caller chooses the failure policy
  (`EncodeError::GroupCountMismatch`).

### Fixed

- Generated decoders now reject a present-but-empty CheckSum (`10=\x01`)
  instead of silently skipping verification and accepting the message. The
  verify gate keyed on a non-empty value (`is_present()`), so an empty tag 10
  bypassed the check and diverged from `validate_checksum`; it now keys on the
  field being present at all.
- Generated encoder setters for `TZTimestamp` fields no longer panic at runtime.
  `FixTzTimestamp::encode` needs 33 bytes but the owned-value scratch buffer was
  32; it is now sized to `MAX_VALUE_ENCODE_LEN`.

- `FixDecimal::Display` no longer panics at scale 19 (`10^19` overflows the
  `i64` divisor it used); it now divides in `u64` and carries the sign
  separately. Reachable from `parse("0.0000000000000000001")`.
- Leap second `23:59:60` is now supported faithfully. It previously parsed to
  a full day of nanoseconds (`hour()` returned 24 and re-encoding rolled the
  instant forward a day). `FixTime` now reports `23:59:60` and round-trips it;
  `FixTimestamp` stores the equivalent Unix instant (Unix time has no leap
  seconds). A `:60` anywhere other than `23:59` is rejected (it would alias a
  normal time, e.g. `00:00:60` == `00:01:00`).
- `FixTime`, `FixTimestamp`, and `FixDate` now reject trailing/over-length
  bytes (the field value is SOH-delimited, so trailing bytes belong to it)
  rather than silently parsing a prefix.
- TZ offsets accept `Z` and `±HH:MM`, including `+00:00`/`-00:00` (which
  normalize to `Z`); the minutes-omitted `±HH` form is not accepted.
- `FixDate::to_epoch_days` doc no longer claims it returns `None` for
  pre-epoch dates (it always returns `Some`).
- `FixTime`/`FixTzTime`/`FixTimestamp` reject a `.` with no fractional digits
  (`"14:30:00."`, or `"14:30:00.+01:00"` via a TZ offset).
- `FixTimestamp::as_secs`/`as_millis`/`as_micros`/`subsec_nanos` are Euclidean,
  so they agree with each other and with `decompose()` for pre-epoch (negative)
  instants (previously a negative timestamp reported a wrong sub-second part).
- `encode_tz_offset`/`write_tz_offset` use `unsigned_abs` (no `i16::MIN`
  negation panic); an out-of-range offset is a clear assert, not an
  out-of-bounds LUT index.
