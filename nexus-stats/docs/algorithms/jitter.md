# Jitter — Signal Variability Measurement

**EMA of consecutive absolute differences.** Measures how unstable a
signal is, not where it is.

| Property | Value |
|----------|-------|
| Update cost | ~6 cycles |
| Memory | ~24 bytes |
| Types | `Jitter<f64>`, `Jitter<i64>` |
| Output | `Option<T>` — smoothed jitter value |

## What It Does

```
  Low jitter:                    High jitter:
  Value                          Value
  102 ┤  ·  ·  ·  ·  ·          120 ┤     ·        ·
  100 ┤──·──·──·──·──·──        100 ┤  ·     ·
   98 ┤  ·  ·  ·  ·  ·           80 ┤        ·  ·     ·
  jitter ≈ 2                     jitter ≈ 20
```

Tracks: `EMA(|x[n] - x[n-1]|)`. Also provides `jitter_ratio()` =
jitter / mean (context-relative: is 5μs jitter a lot? depends on mean).

## Configuration

```rust
let mut j = Jitter::<f64>::builder().span(20).build().unwrap();

if let Some(jitter) = j.update(latency).unwrap() {
    if let Some(ratio) = j.jitter_ratio() {
        // ratio > 0.5 → jitter is 50% of mean → very unstable
    }
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Jitter::<f64>::update` | 6 cycles | ~9 cycles |
