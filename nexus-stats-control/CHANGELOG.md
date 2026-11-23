# Changelog

All notable changes to nexus-stats-control are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added (moved in)

- `control::DeadBand`, `control::Hysteresis`, `control::Debounce` and
  `control::LevelCrossing`, from `nexus-stats-core`. No change to any of
  them. The crate now holds every control type.

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
- `PeakDetector::new` rejects an infinite prominence; `BoolWindow` counts
  failures in `usize` (its capacity type), so a window above `u32::MAX`
  cannot overflow the counter.
- **`BoolWindow` stores its bits as `Box<[u64]>`:** no raw pointer, manual
  `Drop` / `Clone` or `unsafe impl Send`; the type is `Sync` now. Same API.
- **`count()` / `is_primed()` where they were missing.** `DecayAccum` gains
  both (`count` is updates since construction or `reset`; `score()` does not
  count); `TopK` gains `is_primed()` and its `total()` is `count()`;
  `PeakDetector` and `BoolWindow` gain `is_primed()` (`BoolWindow`'s is
  `is_full()`). `TopK::top()` is `#[must_use]`, and a debug assertion checks
  that the table never exceeds its capacity.
- Docs: `BoolWindow::failure_rate` says an empty window reads `0.0`.
- **`TopK` is the paper's Stream-Summary: a hash-indexed array kept sorted,
  with per-counter error.** The table was an unsorted array scanned on every
  update (twice on a miss), and `top()` (after
  [#790](https://github.com/Abso1ut3Zer0/nexus/pull/790)) ranked it into a
  caller-supplied buffer with n selection passes. Now: the counters live in an
  array kept sorted by count (one swap per update; the minimum to evict is the
  last slot, and the start of the run tied at the minimum is maintained, not
  searched), a fixed open-addressing index with a deterministic Fx hasher
  and 32-bit tags finds a key's slot for tables above 32 counters (smaller
  tables are scanned; cheaper at that size), and each counter carries the
  `error` it inherited on entry, as in Metwally et al. (2005). `update` is
  O(1) expected regardless of capacity or universe: on the scaling harness,
  interleaved against the old table in one process, 15 vs 43 ticks at 100
  counters, 23 vs 139 at 1,000, and 71 vs 719 for a 1,000-counter table over
  a million symbols; a tiny table that never evicts (16 symbols, 16 counters)
  costs 5 to 10 ticks more than before, each counter being twice the bytes. `top()`
  returns an iterator of `Counter { key, count, error }` over the sorted
  array (`guaranteed()` is `count - error`), `top().take(k)` is the top k,
  and `guaranteed_top()` is the number of leading ranks whose order is
  provably exact. `K: Eq + Hash` (was `Eq + Clone`; nothing is cloned).
  Equal counts come out in a deterministic but unspecified order. The type
  doc and both pages state the inspiration (market-data observability), the
  three guarantees, how to size `capacity` for a wanted k, and the
  literature.
### Fixed

- **TopK::top short-buffer selection** ([#789](https://github.com/Abso1ut3Zer0/nexus/issues/789)): `top` copied the first `n` table entries into the buffer in insertion order then sorted, so a buffer shorter than the table returned arbitrary entries rather than the most frequent. The method now selects instead of sorting: each slot takes the highest-ranked entry not yet picked, keeping ties in insertion order.
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
