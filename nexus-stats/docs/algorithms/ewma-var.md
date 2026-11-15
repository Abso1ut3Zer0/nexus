# EwmaVariance — Exponentially Weighted Variance

**Recent volatility tracking.** More responsive than Welford's cumulative
variance. The RiskMetrics (JP Morgan 1996) pattern.

| Property | Value |
|----------|-------|
| Update cost | ~12 cycles |
| Memory | ~24 bytes |
| Types | `EwmaVar` |

## What It Does

Tracks two EMA-like values — smoothed mean and smoothed variance:
```
mean_new = alpha × sample + (1 - alpha) × mean_old
var_new  = (1 - alpha) × (var_old + alpha × (sample - mean_old)²)
```

Unlike Welford (which gives equal weight to all observations), EWMA
variance weights recent observations more heavily. Old volatility
fades away.

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

if let Some((mean, var)) = ev.update(sample).unwrap() {
    let threshold = mean + 3.0 * var.sqrt();
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `EwmaVar::update` | 12 cycles | 30 cycles |
