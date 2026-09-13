# Changelog

All notable changes to nexus-decimal are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Fixed

- `round_to_tick` misrounded values for odd tick sizes. The old code computed
  `half_tick = tick / 2` (integer division), which truncates for odd ticks:
  with `tick=3`, `half_tick=1`, so a remainder of `1` landed in the
  banker's-rounding branch even though the true midpoint is `1.5`. The fix
  replaces the division with a complement: `complement = tick - |remainder|`.
  Comparing `|remainder|` against `complement` is exact and needs no
  division — for odd ticks `2 * |remainder|` can never equal an odd tick, so
  the midpoint branch is unreachable. This subsumes the `1.2.2` `tick=1` case
  (where `half_tick=0` made every non-zero remainder hit the branch) and the
  general odd-tick class.

## [1.2.2] — 2026-05-23

### Fixed

- `round_to_tick` with `tick=1` falsely triggered banker's rounding on
  already-aligned values, moving odd raw values to the adjacent even
  number. Root cause: `half_tick = 1/2 = 0` in integer division made
  `remainder == half_tick` always true. Fixed with early return when
  remainder is zero.

## [1.2.0] — 2026-05-16

### Added

- `EPSILON` constant — smallest positive representable value (`1 / 10^D`)
- `HALF` constant — the value 0.5 (requires `D >= 1`, compile-time enforced)
- `TWO` constant — the value 2.0 (compile-time overflow check)
- Power-of-2 multiplication family: `mul_pow2`, `checked_mul_pow2`,
  `saturating_mul_pow2`, `wrapping_mul_pow2`, `try_mul_pow2`. Multiplies
  by `2^n` via a backing-width shift; the `10^D` scale factor cancels
  because the multiplier is dimensionless. The bare form follows stdlib
  `*` semantics (debug-panic, release-wrap via `wrapping_shl`).
- `div_pow2(n)` — divide by `2^n` with truncate-toward-zero rounding,
  matching `halve` / `div10` / `div100` / the rest of the division
  surface. Invariant: `div_pow2(1) == halve()`. Constant `n` folds to
  shift + sign-correction; variable `n` is a real signed division.
- `checked_abs_diff(other) -> Option<Self>` — overflow-safe absolute
  difference. Returns `None` when the result exceeds `MAX` (operands
  with opposite signs near the rails — `|MIN - MAX|` exceeds `MAX` on
  every signed type). Named `checked_*` to match the crate's convention
  for `Option`-returning operations; there is no bare `abs_diff`.
- `BASIS_POINT` constant (requires `D >= 4`, compile-time enforced)
- Basis-point operations: `bps_of`, `shift_bps`, `bps_diff`, `bps_diff_by`
- Percentage operations: `pct_of`, `shift_pct`, `pct_diff`, `pct_diff_by`
- Tick operations: `add_ticks`, `tick_diff`, `is_tick_aligned`
- Proximity guards: `within_bps`, `within_ticks`
- Bps rounding: `round_bps`, `floor_bps`, `ceil_bps`
- Property-based tests for arithmetic invariants (cross-backing equivalence, truncation direction)
- Property-based tests for financial methods (rounding alignment, tick roundtrip, shift identity)
- Property-based tests for pow2 operations (mul/div roundtrip, halve equivalence, abs_diff symmetry)

## [1.1.0] — 2026-04-23

### Added

- `Decimal::abs()` — plain absolute value with the same semantics as
  `i64::abs` / `i32::abs` / `i128::abs`: debug builds panic on `Self::MIN`,
  release builds wrap. Explicit overflow policies remain available via
  `checked_abs`, `saturating_abs`, `wrapping_abs`, and `try_abs`.
- `Decimal::from_scaled(value, scale)` — construct a decimal representing
  `value * 10^-scale`. Useful for tick sizes and precision boundaries
  (e.g., `D64::from_scaled(1, 5)` returns `0.00001`). Returns `None` if
  `scale > D` or if the scaled value overflows the backing. The `value`
  parameter takes the backing type directly, so `i128`-backed decimals
  can accept the full `i128` range.
- `From<IntType>` impls for every `(Backing, D, IntType)` combination
  where the conversion is statically sound. A `Decimal<i64, 8>` now
  accepts `i8`, `i16`, `i32`, `u8`, `u16`, `u32` via `From`, eliminating
  `.from_i32(n).expect(...)` ceremony at call sites. Attempting an
  unsound combination (e.g., `i32` into `Decimal<i64, 11>`) produces a
  standard "trait not implemented" compile error. Sound combinations
  are determined by the rule `|IntType::MAX| * 10^D ≤ |Backing::MAX|`
  and enumerated via macro across all three backings.
- `From<i32> for Decimal<i32, 0>`, `From<i64> for Decimal<i64, 0>`,
  and `From<i128> for Decimal<i128, 0>` — identity conversions for
  pure-integer decimal configurations. `TryFrom<backing>` is
  auto-provided via std's blanket impl.

### Changed

- `TryFrom<i64>` and `TryFrom<u64>` moved from generic `impl<const D: u8>`
  to per-`(Backing, D)` emission. Behavior is unchanged for callers. The
  refactor was required to resolve a coherence conflict with the new
  `From<IntType>` impls (std's blanket
  `impl<T, U: Into<T>> TryFrom<U> for T` auto-derives `TryFrom` from any
  `From`, which would collide with an explicit generic `TryFrom`).
- `<Decimal<i64, 0> as TryFrom<i64>>::Error` is now `std::convert::Infallible`
  (previously `ConvertError`). The conversion was always infallible at D=0
  (identity mapping, no scaling); the new type reflects that accurately.
  Callers using `.unwrap()`, `.ok()`, or `.is_ok()` are unaffected.
  Code that annotates `Result<_, ConvertError>` explicitly on this
  specific conversion needs to update the annotation to `Infallible` or
  drop the annotation. Not applicable to `Decimal<i32, 0>` / `Decimal<i128, 0>`
  — those had no prior explicit `TryFrom<backing>` impl, so the new auto-derived
  `Infallible` error type is purely additive there.
- Inherent `abs()` now shadows `num_traits::Signed::abs` via method
  resolution. If you previously called `.abs()` on a `Decimal` with
  `use num_traits::Signed;` in scope, you got saturating behavior from
  the `Signed` impl. You now get the inherent method's debug-panic-on-
  `MIN` / release-wrap semantics. If the saturating behavior is needed,
  call `saturating_abs()` explicitly or use a fully-qualified
  `Signed::abs(&x)`.

### Motivation

- 599 call-site port at FalconX exposed the ergonomic gaps that
  motivated this release.

## [1.0.3] — prior

No changelog entries recorded for earlier versions. See git history.

[1.1.0]: https://github.com/Abso1ut3Zer0/nexus/compare/v1.0.3...v1.1.0
