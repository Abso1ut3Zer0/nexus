# Hysteresis — Schmitt Trigger

**Binary decision with different rising and falling thresholds.**
Prevents oscillation when a noisy signal hovers near a decision boundary.

| Property | Value |
|----------|-------|
| Update cost | ~2-3 cycles |
| Memory | ~24 bytes |
| Types | `Hysteresis<f64>`, `Hysteresis<i64>` |
| Output | `bool` — current state (high/low) |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

```
  Single threshold — oscillates at boundary:

  Value
  105 ┤     ·  ·     ·  ·        ·  ·
  100 ┤──·──·──·──·──·──·──·──·──·──·── threshold
   95 ┤  ·  ·     ·  ·     ·  ·

  Output: HIGH LOW HIGH LOW HIGH LOW HIGH LOW HIGH LOW ...
          ↑ flapping — every crossing triggers a state change


  Hysteresis — stable decisions:

  Value
  105 ┤─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ high threshold
  103 ┤     ·  ·     ·  ·        ·  ·
  100 ┤  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·
   97 ┤  ·  ·     ·  ·     ·  ·
   95 ┤─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ low threshold

  Output: LOW  LOW  LOW  LOW  LOW  LOW  LOW  LOW ...
          ↑ stable — signal never crosses BOTH thresholds

  With actual transition:

  Value
  110 ┤                              ·  ·  ·
  105 ┤─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─·─ ─ ─ ─ ─ ─ high threshold
  100 ┤  ·  ·  ·  ·  ·  ·  ·  ·
   95 ┤─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ low threshold
   90 ┤

  Output: LOW  LOW  LOW  LOW  LOW  HIGH HIGH HIGH
                                   ↑ crossed HIGH threshold — stable switch
```

The gap between thresholds is the **dead zone**. The signal must cross
the *high* threshold to go high, and cross the *low* threshold to go
low. Noise within the dead zone causes no state changes.

## When to Use It

**Use Hysteresis when:**
- A binary decision flaps due to noise at the boundary
- You want "enter above X, exit below Y" behavior
- You need clean on/off signals from noisy analog inputs

**Don't use Hysteresis when:**
- You want multi-level classification → use [MultiGate](multi-gate.md)
- You want a smoothed continuous signal → use [EMA](ema.md)
- You want change detection, not binary classification → use [CUSUM](cusum.md)

## Configuration

```rust
let mut hyst = Hysteresis::<f64>::new(
    95.0,   // low threshold  (go LOW when signal drops below this)
    105.0,  // high threshold (go HIGH when signal rises above this)
);
```

### Parameters

| Parameter | What | Guidance |
|-----------|------|----------|
| `low_threshold` | Below this → output goes LOW | Set below the noise floor of your signal at the boundary |
| `high_threshold` | Above this → output goes HIGH | Set above the noise floor |

**Dead zone width** = `high - low`. Wider = more stable, but slower to
react to genuine transitions. Size it to be wider than your typical noise
amplitude at the boundary.

## Examples by Domain

### Trading — Connection Quality

```rust
// Connection is "good" above 95% success rate, "bad" below 80%
let mut conn_quality = Hysteresis::<f64>::new(0.80, 0.95);

// On each health check:
let is_good = conn_quality.update(success_rate).unwrap();
if !is_good {
    route_to_backup();
}
```

### Networking — Link Utilization Alert

```rust
// Alert when utilization crosses 90%, clear when it drops below 70%
let mut util_alert = Hysteresis::<f64>::new(0.70, 0.90);
```

### IoT — Temperature Control

```rust
// Heater: turn on below 19°C, off above 21°C
let mut heater = Hysteresis::<f64>::new(19.0, 21.0);

let should_heat = heater.update(current_temp).unwrap();
```

### Gaming — LOD Switching

```rust
// Switch to high-detail model when close, low-detail when far
// Dead zone prevents LOD popping at the boundary
let mut lod = Hysteresis::<f64>::new(45.0, 55.0);  // distance units

let use_high_detail = !lod.update(distance).unwrap();  // closer = lower value = HIGH
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Hysteresis::<f64>::update` | ~3 cycles | ~3 cycles |

One or two comparisons. The p99 in benchmarks may show higher due to
branch misprediction when the input alternates above and below both
thresholds — in production with stable signals this is ~3 cycles.

## Background

The Schmitt trigger was invented by Otto Schmitt in 1934 for
converting noisy analog signals to clean digital pulses. The same
principle applies anywhere a binary decision is made from a continuous
signal: thermostats, motor controllers, level detectors, alert systems.

The key property is **positive feedback at the switching point**: once
the output has switched, it takes a larger signal change to switch it
back. This is the opposite of negative feedback (which seeks stability)
— hysteresis seeks *commitment* to a decision once made.
