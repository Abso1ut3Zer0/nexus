# Changelog

All notable changes to nexus-stats-control are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed

- **No numeric suffixes** (the stats major, [#773](https://github.com/Abso1ut3Zer0/nexus/issues/773)): `BoolWindow`, `TopK`, `FlexProportion*`
  were already plain; the decay accumulator is `DecayAccum` (`u64` ticks; see Removed).
- **FlexProportion is a port of the kernel algorithm, with the kernel's
  names.** `FlexProportionEntity` is `FlexProportionLocal` (`fprop_global` /
  `fprop_local_single`), and the global owns the one mutating call:
  `global.update(&mut local)` records an event for that local, and the local
  answers `fraction(&global)` and `events(&global)`. The old protocol
  (`global.update(); local.update(global.period()); local.fraction(total,
  period)`) let a local be fed another population's values with no error.
  `FlexProportionLocal` is `Copy` and `Default`; the global gains `events()`,
  `half_life_events()`, `count()`, `is_primed()`.
- **`TopK<K>` takes its capacity at runtime:** `TopK::new(capacity) ->
  Result<Self, ConfigError>` (zero rejected) and `capacity()`, replacing
  `TopK<K, const CAP: usize>` with `new()` and its `Default` impl. The table
  is allocated once in `new`, so the type sits behind the `alloc` feature
  with the other runtime-sized types. No const generic is
  left in the stats crates.
- **`PeakDetector<T>`** replaces `PeakDetectorF64` / `PeakDetectorI64`: one
  generic type bounded by `nexus_stats_core::Sample` (`f64`, `i64`) returning
  `Peak<T>`. `update` returns `Result` for `f64` and the option directly for
  `i64`. Construct as `PeakDetector::<i64>::new(prominence)`.
- **Hot-path pass before release.** `BoolWindow` advances its ring index
  with a compare instead of a division. `TopK` keeps its live entries in a
  `Vec` sized once at construction instead of `Box<[Option<Entry>]>`, so
  the scan no longer tests a discriminant per slot. API unchanged.

### Fixed

- **FlexProportion shares decayed to zero.** The global total never halved
  while every local's count did, so a key receiving every single event read
  a 0.5 share after one half-life and 0.01 after a hundred. As in the kernel,
  the global count now halves at each period and the locals halve to match
  on their next touch; shares sum to one and a sole key reads 1.0 forever.
- **`FlexProportionGlobal::reset` could revive a stale local.** Resetting set
  the period back to zero, so a local last touched in period 0 (or one whose
  period the global later grew back into) read its old count as current and
  `fraction` clamped it to 1.0. The period now jumps forward by 64 on reset,
  which every stale local reads as zero by construction. Two tests cover
  both shapes.
- Docs: `PeakDetector` fires at a reversal of *at least* the prominence (the
  code's `>=`); the docs said "more than". `DecayAccum::update`'s `# Errors`
  described a float timestamp the method no longer takes.

### Removed

- **`DecayAccumF64`**: `f64` timestamps lose precision past 2^52, and ticks
  are `u64` (the clock contract). `DecayAccum` (`u64` ticks) is the one form.

## [2.0.0] — 2026-05-28

### Removed

- `PeakDetectorF32` — use `PeakDetectorF64`
- `PeakDetectorI32` — use `PeakDetectorI64`
- `PeakDetectorI128` — use `PeakDetectorI64`

## [1.0.3] — 2026-05-26

## [1.0.2] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
