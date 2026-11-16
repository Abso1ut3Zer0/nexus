# WindowedMedian — Robust Median Filter

**Sorted ring buffer providing streaming median, MAD, and quartiles.**
Robust to outliers — the median ignores them entirely.

| Property | Value |
|----------|-------|
| Update cost | 79 cycles (N=32) |
| Memory | ~2×N×8 bytes |
| Types | `WindowedMedian<f64>`, `WindowedMedian<i64>` |
| Requires | `alloc` feature (runtime window size) |
| Priming | After N samples (window full) |

## What It Does

```
  Signal with outlier spikes:

  Value
  200 ┤        ·              ·        ← outliers
  100 ┤  ·  ·     ·  ·  ·  ·     ·  · ← true signal ~100
      └──────────────────────────────── t

  EMA (alpha=0.1):         WindowedMedian (N=7):
  100 ┤──────╱╲────────╱╲──  100 ┤─────────────────────
      ↑ outlier bleeds     ↑ outlier ignored entirely
        into the estimate
```

Provides:
- **`median()`** — 50th percentile (robust center)
- **`mad()`** — median absolute deviation (robust spread)
- **`q1()`, `q3()`** — quartiles
- **`iqr()`** — interquartile range
- **`modified_z_score(x)`** — `0.6745 × (x - median) / MAD`

## When to Use It

- Bad data filtering: median ignores outliers, EMA doesn't
- Robust baseline estimation for anomaly detection
- When you need quartiles/IQR, not just mean/variance

## When to Use Something Else

- O(1) is required → [RobustZScore](robust-z-score.md) (O(1) but less robust)
- Just need smoothing → [EMA](ema.md) (5 cycles vs 136)
- Just need all-time stats → [Welford](welford.md)

## Configuration

```rust
let mut median = WindowedMedian::<f64>::new(32);  // 32-sample window

median.update(sample);

if let Some(m) = median.median() {
    println!("median={m}, MAD={}", median.mad().unwrap());
}

// Modified z-score for outlier testing:
if let Some(z) = median.modified_z_score(sample) {
    if z.abs() > 3.5 { /* outlier */ }
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `WindowedMedian::<f64>::update` (N=32) | 79 cycles | 85 cycles |
| `median()` query | O(1) | — |
| `mad()` query (N=32) | 44 cycles | 51 cycles |

Update is O(N): two vectorized rank counts (a binary search above 64
elements) plus one memmove. For N=32 that is at most 256 bytes moved, 4
cache lines. The `mad()` query finds the tightest window of the N/2+1
points nearest the median with one vectorized count: O(N), no allocation,
no sort, no data-dependent branch.

## Background

The median is the "breakdown point = 50%" estimator — up to half the
data can be arbitrarily corrupted without affecting the result. This
makes it ideal for filtering bad ticks/samples where EMA (breakdown
point = 0%) fails.

Hampel, F.R. "The Influence Curve and Its Role in Robust Estimation."
*JASA* 69 (1974): 383-393.
