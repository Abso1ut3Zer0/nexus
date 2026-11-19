# Normalization

Streaming online normalizers. Module path: `nexus_stats_core::normalization`.

## At a glance

| Type | Method | Memory | Feature gate |
|------|--------|--------|-------------|
| `ZScoreNorm<f64>` / `ZScoreNorm<f32>` | `(x - μ) / σ` via EW mean+var | small, fixed | `std` or `libm` |
| `MinMaxNorm<f64>` / `MinMaxNorm<f32>` | `(x - min) / (max - min)` via windowed extremes | small, fixed | — |
| `QuantileNorm<f64>` / `QuantileNorm<f32>` | Rank in P² quantile grid | O(resolution) | `alloc` |

All three follow the standard conventions: `update()` feeds a sample and returns the normalized value, `normalize()` queries without updating state, `count()` / `is_primed()` / `reset()`.

---

## ZScoreNorm<f64> — EW z-score normalization

Normalizes values to z-scores using exponentially-weighted mean and variance. Wraps `EwmaVar` internally.

```rust
use nexus_stats_core::normalization::ZScoreNorm;

let mut zn = ZScoreNorm::<f64>::builder().halflife(100.0).build().unwrap();
for i in 0..500 {
    let _ = zn.update(i as f64);
}
let z = zn.update(250.0).unwrap().unwrap();  // z-score relative to EW stats
```

**Use for:** feature normalization in streaming ML, adaptive thresholding, comparing values across instruments with different scales.

**Caveats:** requires `std` or `libm` (for sqrt). A relative std-dev floor prevents division-by-zero on constant input — `sd > max(|mean|, 1.0) * 1e-14` (f64). Returns `None` until primed.

---

## MinMaxNorm<f64> — Windowed min-max normalization

Maps values to [0, 1] using windowed min and max trackers. Takes a `u64` timestamp parameter, consistent with the monitoring module.

```rust
use nexus_stats_core::normalization::MinMaxNorm;

let mut mn = MinMaxNorm::<f64>::builder()
    .window(1_000_000_000)  // 1-second window
    .build()
    .unwrap();

for i in 0..200 {
    let _ = mn.update(i as f64, i as u64 * 5_000_000);
}
let v = mn.normalize(100.0).unwrap();  // position in [0, 1]
```

**Use for:** range-based normalization where the scale drifts over time. Market data features, sensor readings, any signal where min/max shift.

**Caveats:** returns 0.5 when the range is zero (all values equal within the window). A sample timestamped before the previous one does not enter the window; it is normalized against the current window and clamped to [0, 1]. No feature gate required — works on bare no_std.

---

## QuantileNorm<f64> — P² quantile grid normalization

Maps values to approximate uniform [0, 1] by maintaining a grid of P² percentile estimators at uniformly spaced quantile points. The normalized value is the interpolated rank within the grid.

```rust
use nexus_stats_core::normalization::QuantileNorm;

let mut qn = QuantileNorm::<f64>::builder()
    .resolution(9)   // grid at 0.1, 0.2, ..., 0.9
    .build()
    .unwrap();

for i in 0..2000 {
    let _ = qn.update(i as f64);
}
let rank = qn.normalize(1000.0).unwrap();  // ~0.5
```

Resolution is configurable: `resolution(n)` places grid points at `1/(n+1), 2/(n+1), ..., n/(n+1)`. Higher resolution = finer approximation but O(resolution) per update since each sample feeds all P² estimators.

**Use for:** distribution-free normalization, quantile-based features, copula transforms. Handles arbitrary distributions without assumptions about shape.

**Caveats:** requires `alloc`. O(resolution) per update — at resolution 9, that's 9 P² updates (~126ns). Pre-allocates at construction, no hot-path allocation. Minimum samples are derived from the most extreme grid quantile to ensure P² convergence.

---

## Cross-references

- The EW mean/variance underneath ZScoreNorm: [`statistics.md`](statistics.md) (EwmaVar).
- The windowed trackers underneath MinMaxNorm: [`monitoring.md`](monitoring.md) (WindowedMax/Min).
- The P² algorithm underneath QuantileNorm: [`statistics.md`](statistics.md) (Percentile).
