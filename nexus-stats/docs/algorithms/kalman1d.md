# Kalman1D — 1D Kalman Filter with Velocity

**Optimal adaptive smoother.** Tracks position and velocity from noisy
measurements. Automatically balances process noise against measurement
noise — reactive when uncertain, stable when confident.

| Property | Value |
|----------|-------|
| Update cost | 26 cycles |
| Memory | ~56 bytes |
| Types | `Kalman1d` |
| Priming | Configurable via `min_samples` |
| Output | `Option<(T, T)>` — (position, velocity) |

## What It Does

```
  Noisy measurements vs Kalman estimate:

  Value
  120 ┤      ·              ·
  115 ┤  ·       ·       ·     ·
  110 ┤    ─────────────────────────── Kalman (smooth + tracks trend)
  105 ┤ ·──────────────·──·──────────  EMA (smooth but lags on trends)
  100 ┤──·───·────·──·─────·──·──·────
   95 ┤            ·        ·
      └──────────────────────────────── t

  Early (uncertain):  Kalman gain high → reactive, trusts measurements
  Later (confident):  Kalman gain low → smooth, trusts model
```

Unlike EMA (fixed alpha) or Holt (fixed alpha/beta), the Kalman filter
adapts its gain based on how confident it is. After a reset or startup,
it's reactive (high gain). Once it accumulates evidence, it stabilizes
(low gain).

## When to Use It

**Use Kalman1D when:**
- You need level + velocity (rate of change) from noisy data
- You want adaptive smoothing that's principled, not heuristic
- The noise characteristics may change (e.g., after reconnection)
- You can characterize process noise and measurement noise

**Use something simpler when:**
- Fixed smoothing is sufficient → [EMA](ema.md)
- You don't need velocity → [EMA](ema.md) or [KAMA](kama.md)
- You know the signal is always trending → [Holt](holt.md) is simpler

## Timing Assumption

**This filter assumes dt = 1 between consecutive measurements.** For
variable-interval data, either:
- Scale `process_noise` proportionally to the actual interval
- Pre-normalize timestamps so samples arrive at uniform intervals

## Configuration

```rust
let mut kf = Kalman1d::builder()
    .process_noise(0.01)       // expected change per sample
    .measurement_noise(1.0)    // measurement uncertainty
    .min_samples(1)
    .build().unwrap();

if let Some((pos, vel)) = kf.update(measurement).unwrap() {
    println!("estimated value: {pos}, trend: {vel}/sample");
}
```

### Parameters

| Parameter | What | Guidance |
|-----------|------|----------|
| `process_noise` (Q) | How much the true value changes per sample | Higher = more reactive |
| `measurement_noise` (R) | How noisy the measurements are | Higher = more smoothing |
| Q/R ratio | Controls the balance | High Q/R = trust measurements. Low Q/R = trust model. |

### Seeding

```rust
let kf = Kalman1d::builder()
    .process_noise(0.01)
    .measurement_noise(1.0)
    .seed(100.0, 0.5)  // initial position=100, velocity=0.5
    .build().unwrap();
```

## Examples

### Trading — Throughput Estimation After Reconnection
```rust
// After reconnect, Kalman is reactive (uncertain).
// As measurements stabilize, it smooths.
let mut throughput = Kalman1d::builder()
    .process_noise(100.0)     // throughput can change significantly
    .measurement_noise(500.0) // measurements are noisy
    .build().unwrap();

if let Some((current, trend)) = throughput.update(msgs_per_sec).unwrap() {
    if trend < -10.0 {
        // throughput declining
    }
}
```

### SRE — Load Prediction
```rust
let mut load = Kalman1d::builder()
    .process_noise(0.1)
    .measurement_noise(5.0)
    .build().unwrap();

if let Some((current, trend)) = load.update(cpu_percent).unwrap() {
    let predicted_5min = current + trend * 300.0; // 300 samples ahead
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Kalman1d::update` | 26 cycles | 26 cycles |

2x2 matrix predict + update. ~15 multiplies + ~10 adds + 1 division.
Uses multiply-adds on the hot path (fused into FMA only on targets with `+fma`).
