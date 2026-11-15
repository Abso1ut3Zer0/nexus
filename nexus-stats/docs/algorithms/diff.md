# FirstDiff / SecondDiff — Discrete Derivative and Acceleration

**Rate of change and acceleration detection.** The simplest possible
signal processing primitives.

| Property | FirstDiff | SecondDiff |
|----------|-----------|------------|
| Update cost | ~2 cycles | ~2 cycles |
| Memory | 8 bytes | 16 bytes |
| Types | All (f32, f64, i32, i64) | All |
| Output | `Option<T>` — None until 2nd/3rd sample |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What They Do

```
  Signal:        10   12   15   14   16   20

  FirstDiff:          +2   +3   -1   +2   +4   ← rate of change
  SecondDiff:               +1   -4   +3   +2   ← acceleration (change of change)
```

**FirstDiff** = `x[n] - x[n-1]` — instantaneous rate of change.
**SecondDiff** = `x[n] - 2·x[n-1] + x[n-2]` — instantaneous acceleration.

## When to Use Them

- FirstDiff + [EMA](ema.md) = smoothed rate of change
- SecondDiff = inflection point detection (sign changes = curvature reversal)
- FirstDiff + [LevelCrossing](level-crossing.md) = "rate exceeded threshold" detector

## Examples

```rust
let mut rate = FirstDiff::<f64>::new();
let mut accel = SecondDiff::<f64>::new();

for sample in stream {
    if let Some(dx) = rate.update(sample).unwrap() {
        // dx = rate of change from previous sample
    }
    if let Some(ddx) = accel.update(sample).unwrap() {
        // ddx = acceleration (positive = speeding up, negative = slowing down)
    }
}
```

Integer variants work natively — pure subtraction, no float needed.
