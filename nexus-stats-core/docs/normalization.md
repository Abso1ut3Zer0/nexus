# Normalization

Streaming online normalizers. Module path: `nexus_stats_core::normalization`.

## At a glance

| Type | Method | Memory | Feature gate |
|------|--------|--------|-------------|
| `ZScoreNorm<f64>` / `ZScoreNorm<f32>` | `(x - μ) / σ` against the EW mean and std-dev before `x` | small, fixed | `std` or `libm` |
| `MinMaxNorm<f64>` / `MinMaxNorm<f32>` | `(x - min) / (max - min)` via windowed extremes | small, fixed | — |
| `QuantileNorm<f64>` / `QuantileNorm<f32>` | Rank in a P² histogram | `16 * (resolution + 2)` bytes | `alloc` |

All three share one shape:

- `update(..)` feeds a sample and returns its normalized value, `None` while there is nothing to normalize against. `ZScoreNorm` scores the sample against the state *before* it and then folds it in (a score against statistics that already contain the sample is capped). `MinMaxNorm` and `QuantileNorm` fold first: a range or a rank is defined to include the sample, so a new maximum reads exactly 1.
- `normalize(value)` scores a value against the current state without changing it, `None` if not primed.
- On `MinMaxNorm` and `QuantileNorm` both return a `Result` and refuse NaN and infinity. `ZScoreNorm` has moved to the unchecked `update` / `normalize` with `checked_update` / `checked_normalize` beside them; the other two follow.
- `count()` / `is_primed()` / `reset()`.

---

## ZScoreNorm<f64> — EW z-score normalization

Scores each sample against the exponentially weighted mean and standard deviation of the samples *before* it, then feeds it in. Wraps `EwmVar` internally.

```rust
use nexus_stats_core::normalization::ZScoreNorm;

let mut zn = ZScoreNorm::<f64>::builder().span(50).build().unwrap();
for i in 0..500 {
    zn.update(100.0 + f64::from(i % 7));
}
// A typical sample scores small; an outlier scores as large as it is.
assert!(zn.update(103.0).unwrap().abs() < 1.0);
assert!(zn.update(10_000.0).unwrap() > 1_000.0);
```

Scoring first is what makes the outlier visible. A sample fed into the statistics before being scored against them is bounded by its own weight, whatever its size: about 2.9 at alpha 0.1.

`update` returns `None` until `min_samples` earlier samples have been seen (default and minimum 2, or at once when seeded). It does not validate; `checked_update` refuses NaN, infinity, and magnitudes above `1e120`. `normalize(value)` scores without feeding the value in, and `checked_normalize` is its validating form, with the same limit.

**No spread, no score.** While every sample so far has been the same value, the standard deviation is zero and there is nothing to score against, so the result is `None`. This is the convention of NumPy, pandas and SciPy, which give no value (NaN) there.

```rust
use nexus_stats_core::normalization::ZScoreNorm;

let mut zn = ZScoreNorm::<f64>::builder().span(50).build().unwrap();
for _ in 0..100 {
    zn.update(100.0);
}
assert_eq!(zn.normalize(100.0), None);
assert_eq!(zn.update(150.0), None);    // a jump out of a flat stream: no scale yet
assert!(zn.update(150.0).is_some());   // the jump gave it one
```

If a jump out of a flat stream should alarm, treat `None` on a primed normalizer as that signal.

`seed(mean, variance)` starts it converged; `reset_with_seed(mean, variance)` does the same on a live normalizer.

**Use for:** outlier scoring, adaptive thresholding, comparing values across instruments with different scales.

**Caveats:** requires `std` or `libm` (for sqrt). `ZScoreNorm<f32>` returns infinity for a finite score too large for `f32`. A variance at or below `(EPSILON * mean)^2`, what rounding alone produces, counts as no spread (the test SciPy uses).

---

## MinMaxNorm<f64> — Windowed min-max normalization

Maps values to [0, 1] using windowed min and max trackers. `update` takes a `u64` timestamp first, consistent with the monitoring module.

```rust
use nexus_stats_core::normalization::MinMaxNorm;

let mut mn = MinMaxNorm::<f64>::builder()
    .window(1_000_000_000)  // 1-second window, in nanosecond ticks
    .build()
    .unwrap();

for i in 0..=200u32 {
    let _ = mn.update(u64::from(i) * 1_000_000, f64::from(i)).unwrap();
}
// The window holds 0..=200.
assert_eq!(mn.normalize(100.0).unwrap(), Some(0.5));
assert_eq!(mn.normalize(300.0).unwrap(), Some(1.5)); // outside the window's range
```

**Use for:** range-based normalization where the scale drifts over time. Market data features, sensor readings, any signal where min/max shift.

**Caveats:** the windowed extremes are tracked with three stored samples each and are approximate: the range can be narrower than the true window's, never wider. Returns 0.5 when the range is zero (all values equal within the window). `update` clamps its result to [0, 1]; `normalize` does not, so a value outside the window's range reads below 0 or above 1. A sample timestamped before the previous one does not enter the window; it is normalized against the current window. No feature gate required: works on bare no_std.

---

## QuantileNorm<f64> — P² histogram normalization

Maps a value to its approximate rank in [0, 1] among the samples seen, using the P² histogram of Jain and Chlamtac (1985): `resolution + 2` markers (the minimum, the maximum, and `resolution` interior quantiles), each a value and a position, adjusted in one pass per sample. The rank is interpolated between the two markers that bracket the value.

```rust
use nexus_stats_core::normalization::QuantileNorm;

let mut qn = QuantileNorm::<f64>::builder()
    .resolution(9)   // interior markers at the deciles
    .build()
    .unwrap();

for i in 0..2000 {
    let _ = qn.update(f64::from(i)).unwrap();
}
let rank = qn.normalize(1000.0).unwrap().unwrap();
assert!((rank - 0.5).abs() < 0.01);
assert_eq!(qn.normalize(-1.0).unwrap(), Some(0.0));    // below everything seen
assert_eq!(qn.normalize(9999.0).unwrap(), Some(1.0));  // above everything seen
```

`resolution(n)` tracks the quantiles `1/(n+1), ..., n/(n+1)`. The rank is non-decreasing in the value, and continuous except at a value that several markers share (one value making up a large part of the stream), where it steps across that run.

**Accuracy:** the rank is off by at most the probability in one cell, `1 / (resolution + 1)`, plus the markers' own estimation error. The bound is approached where a cell is far from uniform: one that spans a gap in the distribution, or an end cell of a long-tailed distribution. Typical error is far smaller (under 0.001 on a uniform stream at resolution 19; mean error 0.002 on an exponential one). Raise the resolution if the tails matter.

**Use for:** distribution-free normalization, quantile-based features, copula transforms. Handles arbitrary distributions without assumptions about shape.

**Caveats:** requires `alloc`. O(resolution) per update; see the [performance reference](../../nexus-stats/docs/reference/performance.md) for measured cost. Allocates once at construction. All-time: every sample since construction or `reset` counts equally. Ranks are available after `resolution + 2` samples.

---

## Cross-references

- The EW mean/variance underneath ZScoreNorm: [`statistics.md`](statistics.md) (EwmVar).
- The windowed trackers underneath MinMaxNorm: [`monitoring.md`](monitoring.md) (WindowedMax/Min).
- The single-quantile P² estimator: [`statistics.md`](statistics.md) (Percentile).
