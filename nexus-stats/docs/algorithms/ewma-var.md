# EwmaVariance — Exponentially Weighted Variance

**Recent volatility tracking.** More responsive than Welford's cumulative
variance. The estimator pandas computes by default
(`ewm(alpha=a).mean()` / `.var()`).

| Property | Value |
|----------|-------|
| Update cost | see the performance reference |
| Memory | ~120 bytes |
| Types | `EwmaVar`, reading `MeanVariance` |

## What It Does

Sample `i` of `n` carries weight `(1 - alpha)^(n - i)`. The reading is the
weighted mean and the unbiased weighted variance:

```
W    = sum of weights          W2 = sum of squared weights
mean = sum(w * x) / W
var  = sum(w * (x - mean)^2) / (W - W2 / W)
```

computed incrementally, with no stored samples. It is unbiased from the
second sample on: there is no warm-up period in which the variance reads
low. (The plain RiskMetrics recursion
`var = (1 - alpha) * (var + alpha * (x - mean)^2)` reads 18% of the true
variance after two samples at alpha 0.1, and 5% low forever.)

Unlike Welford (which gives equal weight to all observations), this
weights recent observations more heavily. Old volatility fades away.

## When to Use It / When Not To

**Don't use EwmaVariance when:**
- You need all-time variance → [Welford](welford.md) (cumulative, not decaying)
- You need integer-only computation → not available (needs float multiply)
- You only need the mean → [EMA](ema.md) is cheaper

## When to Use It

- Current/recent volatility (not all-time)
- Adaptive threshold computation: `mean ± k × sqrt(var)`
- Pairs naturally with [EMA](ema.md) for level tracking

## Configuration

```rust
let mut ev = EwmaVar::builder().span(30).min_samples(10).build().unwrap();

if let Some(reading) = ev.update(sample) {
    let threshold = reading.mean + 3.0 * reading.std_dev();
}
// `ev.last()` re-reads the same `MeanVariance` without feeding a sample.
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `EwmaVar::update` | 6 cycles | 6 cycles |
