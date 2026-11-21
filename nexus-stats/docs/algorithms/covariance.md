# Covariance — Online Covariance and Pearson Correlation

**Welford-style running covariance between two paired signals.**
Supports Chan's merge for parallel aggregation.

| Property | Value |
|----------|-------|
| Update cost | 11 cycles |
| Memory | ~48 bytes |
| Types | `Covariance` |
| Error handling | `update` does not validate; `checked_update` returns `Result<_, DataError>` |

## What It Does

Tracks two signals simultaneously and computes their covariance and
Pearson correlation coefficient (-1 to +1).

```rust
let mut cov = Covariance::new();

for (x, y) in paired_samples {
    cov.update(x, y);
}

if let Some(r) = cov.correlation() {
    // r ≈ 1.0 → positively correlated
    // r ≈ 0.0 → uncorrelated
    // r ≈ -1.0 → negatively correlated
}
```

`update` does not validate its input. `checked_update` returns a
`DataError` and changes nothing if either value is NaN, infinite, or larger
in magnitude than `1e120`.

`correlation()` is always within `[-1, 1]`, and `None` when either signal
has zero variance.

## When to Use It / When Not To

**Don't use Covariance when:**
- You only need variance of one signal → [Welford](welford.md) or [EwmaVariance](ewma-var.md)
- You need exponentially weighted correlation (recent data weighted more) →
  not available; use Covariance with periodic reset as an approximation

## When to Use It

- "Are these two latency signals correlated?"
- "Does throughput on venue A predict throughput on venue B?"
- Same numerical stability properties as [Welford](welford.md)
- Supports `merge()` for parallel computation

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Covariance::update` | 11 cycles | 11 cycles |
| `correlation()` query | 6 cycles (includes sqrt) |

Three running accumulators (M2_x, M2_y, C) updated per paired sample.
