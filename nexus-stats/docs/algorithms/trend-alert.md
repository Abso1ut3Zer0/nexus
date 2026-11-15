# TrendAlert — Trend Direction Detection

**"Is this getting worse over time?"** Internally uses Holt's double
exponential smoothing. Signals when the trend component exceeds a threshold.

| Property | Value |
|----------|-------|
| Update cost | ~12 cycles |
| Memory | ~40 bytes |
| Types | `TrendAlert` |
| Output | `Option<Direction>` — `Stable`, `Rising`, or `Falling` |

## What It Does

```
  Signal with upward trend:

  Value
  150 ┤                        ·  · ·
  130 ┤                  ·  ·
  110 ┤            ·  ·               trend > threshold
   90 ┤      ·  ·                     → Direction::Rising
   70 ┤  ·
      └──────────────────────────────── t

  Stable signal (same mean, noisy):

  Value
  110 ┤  ·     ·     ·     ·
  100 ┤     ·     ·     ·     ·       trend ≈ 0
   90 ┤  ·     ·     ·     ·         → Direction::Neutral
      └──────────────────────────────── t
```

Separates the signal into level + trend, then classifies:
- **`Rising`** — trend > threshold (e.g., latency increasing)
- **`Falling`** — trend < -threshold (e.g., throughput declining)
- **`Stable`** — trend within ±threshold

## Configuration

```rust
let mut ta = TrendAlert::builder()
    .alpha(0.3)
    .beta(0.1)
    .trend_threshold(0.5)            // absolute: trend > 0.5 per sample
    // or: .trend_threshold_relative(0.02)  // relative: |trend/level| > 2%
    .build().unwrap();

match ta.update(sample) {
    Some(Direction::Rising) => { /* getting worse */ }
    Some(Direction::Falling) => { /* improving */ }
    _ => {}
}
```

Supports both absolute and relative thresholds.

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `TrendAlert::update` | ~12 cycles | ~18 cycles |
