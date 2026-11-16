# RunningMin / RunningMax — All-Time Extrema

**Track the minimum or maximum value ever observed.** One comparison
per update. Zero configuration.

| Property | Value |
|----------|-------|
| Update cost | 5 cycles |
| Memory | ~16 bytes |
| Types | `RunningMax<f64>`, `RunningMax<i64>`, `RunningMin<f64>`, `RunningMin<i64>` |
| Output | `Option<T>` — None until first sample |

## What They Do

```rust
let mut min = RunningMin::<f64>::new();
let mut max = RunningMax::<f64>::new();

min.update(100.0);  // min = 100
min.update(50.0);   // min = 50
min.update(75.0);   // min = 50 (unchanged)

max.update(100.0);  // max = 100
max.update(150.0);  // max = 150
max.update(120.0);  // max = 150 (unchanged)
```

## When to Use Something Else

- Min/max over a *time window* → [WindowedMin/Max](windowed-min-max.md)
- Peak with decay envelope → [PeakHoldDecay](peak-hold.md)
- Max since last read (reset-on-read) → [MaxGauge](max-gauge.md)
- Peak-to-trough difference → [Drawdown](drawdown.md)

## Examples

```rust
// Track best and worst latency ever
let mut best = RunningMin::<f64>::new();
let mut worst = RunningMax::<f64>::new();

best.update(latency);
worst.update(latency);

println!("best={}, worst={}", best.min().unwrap(), worst.max().unwrap());
```

Implements `Default`. Pure comparison — works on any ordered type.
