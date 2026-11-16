# HarmonicMean — Correct Average of Rates

**The right way to average rates and throughputs.** Arithmetic mean of
rates gives the wrong answer.

| Property | Value |
|----------|-------|
| Update cost | 7 cycles |
| Memory | ~16 bytes |
| Types | `HarmonicMean` |
| Output | `Option<T>` — harmonic mean once primed |

## Why Not Arithmetic Mean?

```
  Download 100MB at 10 MB/s, then 100MB at 1 MB/s.
  Total: 200MB in 110 seconds.

  Arithmetic mean: (10 + 1) / 2 = 5.5 MB/s  ← WRONG
  Harmonic mean:   2 / (1/10 + 1/1) = 1.82 MB/s  ← CORRECT

  Actual throughput: 200 / 110 = 1.82 MB/s  ✓
```

The harmonic mean is the correct average when combining rates, speeds,
or throughputs over equal-work intervals.

## Formula

```
H = n / (1/x₁ + 1/x₂ + ... + 1/xₙ)
```

Implementation: maintain `sum_of_reciprocals` and `count`.

## Configuration

```rust
let mut hm = HarmonicMean::new();

hm.update(10.0);  // first rate
hm.update(1.0);   // second rate

assert!((hm.mean().unwrap() - 1.818).abs() < 0.01);
```

## When to Use Something Else

- Averaging values (not rates) → arithmetic mean via [Welford](welford.md)
- Smoothing a rate signal over time → [EMA](ema.md)
- Average of weighted values → [Welford](welford.md) doesn't support weights,
  but [EMA](ema.md) naturally decays

## Examples

- Average throughput across multiple transfer segments
- Average bandwidth across different network paths
- Netflix uses harmonic mean for adaptive bitrate estimation

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `HarmonicMean::update` | 7 cycles | 7 cycles |

One reciprocal (division) + one addition per update.
