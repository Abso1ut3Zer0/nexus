# EwmVar: Exponentially Weighted Variance

**Recent volatility tracking.** `Welford` with decay: old samples fade, so
the mean and variance follow the stream as it drifts.

| Property | Value |
|----------|-------|
| Update cost | 7 cycles |
| Memory | 88 bytes |
| Types | `EwmVar`, reading `MeanVariance` |

## What It Does

Sample `i` of `n` carries weight `(1 - alpha)^(n - i)`:

```
W    = sum of weights          W2 = sum of squared weights
mean = sum(w * x) / W
var  = sum(w * (x - mean)^2) / (W - W2 / W)
```

This is the estimator pandas (`ewm(alpha=a).var()`) and Polars (`ewm_var`)
compute by default. It is unbiased from the second sample on.

The plain recursion `var = (1 - alpha) * (var + alpha * d^2)` (RiskMetrics
style) is cheaper to write down but reads low: about 18% of the true
variance after two samples at alpha 0.1, and about 5% low for good.
Versions before 7.0 used it.

## When to Use It

- Current volatility, not all-time
- Adaptive thresholds: `mean ± k × std_dev`
- Pairs with [EMA](ema.md) for level tracking

**Use something else when:**
- You need all-time variance → [Welford](welford.md)
- You only need the mean → [EMA](ema.md) is cheaper

## Usage

```rust
let mut ev = EwmVar::builder().span(30).min_samples(10).build().unwrap();

if let Some(reading) = ev.update(sample) {
    let threshold = reading.mean + 3.0 * reading.std_dev();
}
```

- `update` does not validate. `checked_update` refuses NaN, infinity, and
  magnitudes above `1e120`, and leaves the state unchanged.
- `value()` reads the current `MeanVariance` without feeding a sample.
- `min_samples` is at least 2: one sample has no variance.

## Seeding

`seed(mean, variance)` starts the tracker as if it had converged on a
stream with that mean and variance. A reading is available at once,
`count()` counts only samples fed, and `reset()` returns to the seed.
`reset_with_seed(mean, variance)` moves a live tracker to a new seed.

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `EwmVar::update` | 7 cycles | 7 cycles |
