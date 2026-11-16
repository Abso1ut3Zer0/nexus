# Holt — Double Exponential Smoothing

**Level + trend in one primitive.** Detects not just "value is high" but
"value is getting worse over time."

| Property | Value |
|----------|-------|
| Update cost | 9 cycles |
| Memory | ~32 bytes |
| Types | `Holt` |
| Priming | After 2 samples (needs 2 for initial trend) |
| Output | `Option<(T, T)>` — (level, trend) |

## What It Does

```
  Signal with linear uptrend:

  Value
  150 ┤                           ·  ·  ·
  130 ┤                     ·  ·
  110 ┤               ·  ·
   90 ┤         ·  ·
   70 ┤   ·  ·
      └──────────────────────────────── t

  Holt output:
  level = smoothed current value (like EMA)
  trend = +3.5 per sample (rate of increase)
  forecast(10) = level + 10 × trend ← prediction
```

Two exponential smoothing equations run in parallel:
```
level = alpha × sample + (1 - alpha) × (level + trend)
trend = beta × (level - prev_level) + (1 - beta) × trend
```

## When to Use It

- "Is latency increasing over time, or just high?"
- Trend forecasting: `level + N × trend`
- Cheaper and simpler than [Kalman1D](kalman1d.md) when fixed smoothing is sufficient

## Configuration

```rust
let mut holt = Holt::builder()
    .alpha(0.3)    // level smoothing
    .beta(0.1)     // trend smoothing
    .build().unwrap();

if let Some((level, trend)) = holt.update(sample).unwrap() {
    let forecast_10 = holt.forecast(10).unwrap();
    if trend > 1.0 { /* getting worse */ }
}
```

| Parameter | What | Guidance |
|-----------|------|----------|
| `alpha` | Level smoothing | Higher = more reactive to level changes |
| `beta` | Trend smoothing | Higher = more reactive to trend changes |

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Holt::update` | 9 cycles | 10 cycles |

Two `mul_add` operations per update. No division, no transcendentals.
