# Overview

`nexus-stats-smoothing` is the "advanced smoothers" crate in the nexus-stats ecosystem. It provides smoothing primitives that either:

1. Need more state than a single EMA (Holt, Kalman1d, KAMA),
2. Need to be robust to outliers (Huber EMA, Hampel, WindowedMedian), or
3. Target specific domain patterns (Spring for chase-to-target, ConditionalEMA for gated updates).

The most common smoothers — `Ema`, `AsymEma`, `Slew<f64>` / `Slew<i64>` — live in `nexus-stats-core::smoothing`. Reach for this crate when those aren't enough.

## Design Conventions

Every type follows the same streaming-statistics shape:

```rust
let mut smoother = Holt::builder().alpha(0.2).beta(0.05).build()?;
smoother.update(100.5)?;                                       // O(1) per update, Result for NaN/Inf
if smoother.is_primed() { let v = smoother.level().unwrap(); } // query
smoother.reset();                                              // back to initial state
```

- **O(1) per update.** No allocation on the hot path once the type is constructed.
- **Fixed memory.** Even the window-based types (KAMA, Hampel, WindowedMedian) allocate once and reuse forever.
- **Error policy.** NaN/Inf inputs return `DataError`. The caller decides whether to propagate, log, or ignore. The library makes no policy choice.
- **`f64` and `f32`.** Most types ship in both flavors. `f32` is there for memory-bound workloads and SIMD feeding.

## Performance

All update paths are O(1) in time and memory. Typical cycle counts (uncontested, hot cache, Intel x86_64):

| Type | p50 (approx cycles) |
|------|---------------------|
| Holt | ~10 |
| Kalman1d | ~18 |
| Spring | ~8 |
| HuberEma | ~12 |
| Kama (window size 10) | ~35 |
| Hampel (window size 11) | ~80 |
| WindowedMedian (window size 21) | ~120 |

Measure on your own workload. Cycle counts scale with window size for windowed types.

## Feature Flags

| Feature | Effect | Default |
|---------|--------|---------|
| `std` | Uses `std` math (`libm` intrinsics). | Yes |
| `libm` | `no_std` fallback for `f64`/`f32` math. | No |
| `alloc` | Enables windowed types (`Kama`, `Hampel`, `WindowedMedian<f64>`). | Yes via `std` |

In a strict `no_std` environment with `alloc`:

```toml
[dependencies]
nexus-stats-smoothing = { version = "*", default-features = false, features = ["libm", "alloc"] }
```

## Re-exports

If you already depend on `nexus-stats` with the `smoothing` feature, every type in this crate is re-exported at `nexus_stats::smoothing::*`. You only need to depend on `nexus-stats-smoothing` directly when you want to avoid pulling in the rest of the ecosystem.

## no_std Usage

All types work in `no_std` with `libm`. The windowed types additionally require `alloc`. No `std::time::Instant` is touched in this crate — the smoothers operate on sample sequences, not wall-clock timestamps.

## Relationship to the Rest of the Ecosystem

- **Base smoothers** — `nexus-stats-core::smoothing::{Ema, AsymEma, Slew}`.
- **Statistics on smoothed output** — feed the output into `Welford` or `EwmVar` to get mean/variance bands.
- **Change detection on smoothed output** — `Cusum`, `Mosum`, `ShiryaevRoberts` live in `nexus-stats-core::detection` and `nexus-stats-detection::detection`.
- **Regression on smoothed inputs** — `LinearRegression`, `Kalman2d` in `nexus-stats-regression`.
