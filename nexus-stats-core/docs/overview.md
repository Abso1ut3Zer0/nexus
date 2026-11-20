# Overview

`nexus-stats-core` provides the foundation types of the nexus-stats ecosystem: error types, math utilities, and the most-used streaming primitives. It was factored out from the umbrella `nexus-stats` crate so that downstream crates (`nexus-stats-smoothing`, `nexus-stats-detection`, `nexus-stats-regression`, `nexus-stats-control`) can share a minimal common base.

Most end users should depend on `nexus-stats` directly (which re-exports everything) rather than this crate.

## Design Conventions

Every streaming type in this crate follows the same shape:

```rust
use nexus_stats_core::statistics::Welford;

let mut w = Welford::new();
w.update(100.5);            // O(1), unchecked; `checked_update` refuses NaN/Inf
w.update(99.8);
if w.is_primed() {
    let mean = w.mean().unwrap();
    let var  = w.variance().unwrap();
}
w.reset();
```

- **`update(sample)` → `Result<_, DataError>`** for float types. NaN/Inf inputs return an error. The caller decides whether to propagate, log, or swallow.
- **`is_primed()` / `count()` / `reset()`** on every type.
- **O(1) per update.** Fixed memory. No allocation on the hot path after construction.
- **`f64` by default**; the cheap primitives (`Slew`, `DeadBand`, `Hysteresis`, the extrema, the diffs, ...) are generic over `f64` and `i64`. See [Integer Variants](#integer-variants).
- **Builder or `new(...)` for construction.** Types with many parameters (CUSUM, EwmaVar, AsymEma) use a builder; simple types (Welford, LevelCrossing, DeadBand, Slew) have a plain `new`.

## Error Types

Two error enums live at the crate root:

```rust
pub enum DataError {
    NotANumber,      // input was NaN
    Infinite,        // input was +Inf / -Inf
    // ...
}

pub enum ConfigError {
    Invalid(&'static str), // builder validation failed
    // ...
}
```

- `DataError` comes out of `update` on float types. Programmer policy: propagate, log, or discard.
- `ConfigError` comes out of `new` / `build` when parameters are nonsensical (`halflife <= 0`, `alpha > 1`, etc.). Surface it at boot, not on the hot path.

## Module Layout

- `nexus_stats_core::statistics` — Welford, Moments, EwmaVar, Covariance, CovarianceMatrix, HarmonicMean, Percentile, BucketAccumulator, Amihud, HitRate, HalfLife, Hurst, VarianceRatio.
- `nexus_stats_core::smoothing` — `Ema`, `AsymEma`, `Slew<f64>` / `Slew<i64>`.
- `nexus_stats_core::monitoring` — Drawdown, RunningMax/Min, WindowedMax/Min, PeakHold, MaxGauge, Liveness, EventRate, CoDel, ErrorRate, Jitter, HawkesIntensity, PollSaturation, SojournSaturation.
- `nexus_stats_core::detection` — CUSUM, DistributionShift.
- `nexus_stats_core::control` — DeadBand, Hysteresis, Debounce, LevelCrossing, FirstDiff, SecondDiff.

Everything is namespaced by submodule. Import paths look like:

```rust
use nexus_stats_core::statistics::Welford;
use nexus_stats_core::smoothing::Ema;
use nexus_stats_core::detection::Cusum;
use nexus_stats_core::monitoring::WindowedMax;
use nexus_stats_core::control::DeadBand;

let mut w = WindowedMax::<f64>::new(1_000)?;   // the numeric type goes at the use site
let mut d: DeadBand<i64> = DeadBand::new(3)?;
```

## Performance

O(1) per update, fixed memory, no allocation. Cycle counts are in the tens for the cheap types (Welford, EMA, DeadBand, RunningMax) and low-hundreds for the window-based types. See umbrella `nexus-stats/docs/reference/performance.md` for benchmark data.

## no_std Story

All types work in `no_std` with `libm`. The windowed monitoring types additionally require `alloc`.

```toml
[dependencies]
nexus-stats-core = { version = "*", default-features = false, features = ["libm"] }
# or with alloc
nexus-stats-core = { version = "*", default-features = false, features = ["libm", "alloc"] }
```

Time-aware types (`Liveness`, `EventRate`, `CoDel`, `Windowed*`) take `u64` ticks in any unit and work in `no_std`; `clock::MonotonicClock` (std) is the bridge from `Instant`, producing nanoseconds since construction.

## Integer Variants

For latency-critical hot paths where float ops are cycles you don't have, integer variants exist for the cheap primitives:

- `Slew<i64>`
- `DeadBand<i64>`, `Hysteresis<i64>`, `LevelCrossing<i64>`, `FirstDiff<i64>`, `SecondDiff<i64>`
- `RunningMax<i64>`, `RunningMin<i64>`, `WindowedMax<i64>`, `WindowedMin<i64>`

These are the `i64` instantiations of the generic types, sharing one implementation with the `f64` form; their `update` does not return `Result` because there is no NaN to reject. Smoothing statistics (`Ema`, `Welford`, ...) are `f64` only: fixed-point smoothing of arbitrary data has no realistic caller.

## Re-exports

If you depend on `nexus-stats` (the umbrella), everything in this crate is re-exported. Depend on `nexus-stats-core` directly only when you want nothing else in the family.
