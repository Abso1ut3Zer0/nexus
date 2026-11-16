# Changelog

All notable changes to nexus-stats-smoothing are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed

- **No numeric suffixes** (the stats major, [#773](https://github.com/Abso1ut3Zer0/nexus/issues/773)). Every type here exists for one numeric
  type and is named plainly: `HoltF64` → `Holt`, `KamaF64` → `Kama`,
  `Kalman1dF64` → `Kalman1d`, `SpringF64` → `Spring`, `HampelF64` → `Hampel`,
  and so on; builders follow (`HoltBuilder`).
- **`WindowedMedian<T>`** replaces `WindowedMedianF64` / `WindowedMedianI64`:
  one generic type bounded by `nexus_stats_core::Sample` (`f64`, `i64`), the
  same insertion-sorted ring buffer written once. `update` returns `Result`
  for `f64` (NaN and infinity rejected) and nothing for `i64`. `quantile`,
  `mad`, `iqr` and `modified_z_score` are available on both instantiations
  (`quantile` was `f64` only). Construct as `WindowedMedian::<i64>::new(n)`.
- **Hot-path pass before release.** `WindowedMedian::update` ranks the
  evicted and the new sample with a vectorized linear count up to 64
  elements (a binary search above that) and shifts with one `copy_within`;
  the ring index advances with a compare instead of a division. `Kama`
  indexes its ring by the head it already carried instead of
  `count % window`, and `Hampel::update` has no `unwrap` left.
- **`WindowedMedian::new` returns `Result<Self, ConfigError>`** (zero window
  rejected) like every sibling constructor, instead of panicking. Holt,
  HuberEma and Kalman1d reject `min_samples(0)`.
- **`WindowedMedian` and `Kama` store their rings as
  `nexus_stats_core::storage::Ring`.** The raw-pointer rings, the manual
  `Drop` / `Clone` and the `unsafe impl Send` are gone; both types are `Sync`
  as well as `Send` now. Same API, same codegen (verified instruction for
  instruction on the Hampel hot loop). `Kama` drops a field it stored but
  never read.

### Fixed

- **`alloc` without `std` builds again.** `Hampel` called `f64::mul_add`
  directly; it now uses the core fused-multiply-add shim.
- **`WindowedMedian::mad()` allocated and sorted a scratch `Vec` on every
  call**, which made every `Hampel::update` allocate. The `k + 1` points
  nearest the median are consecutive in sorted order, so the `k`-th deviation
  is the tightest such window, found with one vectorized count: O(N), no
  allocation, no sort, no data-dependent branch, same value (tested against
  the sorted definition for every window length up to 40). `mad()` at N=32:
  341 → 48 ticks; `Hampel(21)::update` 250 → 96.
- Docs: the crate doc claimed O(1) per update for every type; the windowed
  types (`WindowedMedian`, `Kama`, `Hampel`) are O(window) and the doc now
  says so. `Kama`'s doc states its per-update cost and the N-1 intervals its
  volatility spans; the types table lists `ConditionalEma`.

## [2.0.0] — 2026-05-28

### Removed

- `HoltF32`, `HoltF32Builder` — use `HoltF64` (f32 is a precision footgun for accumulating smoothers)
- `SpringF32` — use `SpringF64`
- `Kalman1dF32`, `Kalman1dF32Builder` — use `Kalman1dF64`
- `KamaF32`, `KamaF32Builder` — use `KamaF64`
- `WindowedMedianF32` — use `WindowedMedianF64`
- `WindowedMedianI32` — use `WindowedMedianI64`

### Changed

- `WindowedMedianI64::modified_z_score` now returns `Option<f64>` (was `Option<i64>`) to include the 0.6745 scale factor
- `Kalman1dF64Builder::build` now rejects NaN/infinite process and measurement noise

## [1.2.3] — 2026-05-26

## [1.2.1] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
