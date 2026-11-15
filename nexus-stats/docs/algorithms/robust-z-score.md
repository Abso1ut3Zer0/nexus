# RobustZScore — MAD-Based Anomaly Scoring

**Exponential moving MAD with estimator freeze.** Cheaper than
WindowedMedian (O(1) vs O(N)), more robust than AdaptiveThreshold
(MAD vs standard deviation).

| Property | Value |
|----------|-------|
| Update cost | ~12 cycles |
| Memory | ~32 bytes |
| Types | `RobustZScore<f64>`, `RobustZScore<f32>` |
| Output | `Option<f64>` — modified z-score |

## What It Does

```
Modified z-score = 0.6745 × (x - EMA) / EMA_abs_deviation

The 0.6745 constant makes it comparable to standard z-scores
for normally distributed data.

z > 3.5  → probable outlier
z > 5.0  → almost certainly bad data
```

**Key feature:** When z exceeds the reject threshold, the internal
EMA baseline is **frozen** — the bad sample does not corrupt the
estimator. This prevents the classic failure mode where outliers
shift the baseline, making future outliers harder to detect.

## When to Use It

- Fast O(1) outlier scoring
- More robust than standard z-score (MAD vs std dev)
- When [WindowedMedian](windowed-median.md) is too expensive

## Configuration

```rust
let mut rz = RobustZScore::<f64>::builder()
    .span(50)               // EMA smoothing
    .reject_threshold(5.0)  // freeze EMA when z > 5
    .min_samples(20)
    .build().unwrap();

if let Some(z) = rz.update(sample) {
    if z.abs() > 3.5 {
        // outlier detected, but EMA didn't move (frozen)
    }
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `RobustZScore::<f64>::update` | 12 cycles | 27 cycles |
