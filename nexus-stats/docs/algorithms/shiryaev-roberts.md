# ShiryaevRoberts — Optimal Change Detection

**Quasi-Bayesian change detector.** Theoretically optimal average
detection delay among all sequential procedures.

| Property | Value |
|----------|-------|
| Update cost | ~17 cycles |
| Memory | ~24 bytes |
| Types | `ShiryaevRoberts` |
| Output | `Option<bool>` — true when change detected |

## What It Does

```
R = (1 + R) × likelihood_ratio(sample)
detected = R > threshold
```

Each sample updates a running statistic R using the likelihood ratio
between the "no change" and "change occurred" hypotheses. When R exceeds
the threshold, a change is declared.

## When to Use It

- When you need the theoretically fastest detection for a given false alarm rate
- Better average detection delay than [CUSUM](cusum.md) for changes at unknown times
- Float-only (needs `exp()` for the likelihood ratio)

## When to Use CUSUM Instead

- CUSUM is simpler (5 cycles vs 17)
- CUSUM gives directional detection (Upper/Lower)
- CUSUM works on integers
- For most practical applications, CUSUM is sufficient

## Configuration

```rust
let mut sr = ShiryaevRoberts::builder()
    .pre_change_mean(100.0)
    .post_change_mean(120.0)
    .variance(25.0)
    .threshold(100.0)
    .min_samples(10)
    .build().unwrap();
```

Currently assumes normal distribution for the likelihood ratio.

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `ShiryaevRoberts::update` | 17 cycles | 41 cycles |

Dominated by one `exp()` call for the likelihood ratio computation.

## Academic Reference

Shiryaev, A.N. "On Optimum Methods in Quickest Detection Problems."
*Theory of Probability and Its Applications* 8.1 (1963): 22-46.

Roberts, S.W. "A Comparison of Some Control Chart Procedures."
*Technometrics* 8.3 (1966): 411-430.
