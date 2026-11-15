# PeakHoldDecay — Peak Envelope Tracking

**Instant attack, configurable hold, exponential decay.** Tracks the
"worst recent value" with a smooth fading envelope.

| Property | Value |
|----------|-------|
| Update cost | ~7 cycles |
| Memory | ~24 bytes |
| Types | `PeakHold<f64>`, `PeakHoldF32`, `PeakHold<i64>`, `PeakHoldI32` |
| Output | Current envelope value |

## What It Does

```
  Signal with a spike:

  Value
  100 ┤              ·
   80 ┤           ·     ·
   60 ┤        ·           ·
   40 ┤  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·  ·
   20 ┤
      └──────────────────────────────────────────────── t

  PeakHoldDecay envelope:

  Value
  100 ┤              ┌────────┐
   80 ┤              │  hold  │╲
   60 ┤              │        │  ╲  decay
   40 ┤──────────────┘        │    ╲──────────────────
   20 ┤                       │      ╲
      └──────────────────────────────────────────────── t
                     ↑         ↑       ↑
                  instant   hold     exponential
                  attack    period   decay begins

  vs WindowedMax (hard window):

  Value
  100 ┤              ┌────────────────┐
   80 ┤              │                │
   60 ┤              │   flat until   │
   40 ┤──────────────┘   window      ─┘──────────────
      └──────────────────────────────────────────────── t
                                      ↑
                               hard drop when
                               window expires
```

The key difference from `WindowedMax`: PeakHoldDecay gives a smooth
envelope that fades gracefully. WindowedMax gives an exact maximum that
drops abruptly when the peak exits the window.

## When to Use It

**Use PeakHoldDecay when:**
- You want "worst recent performance" that fades over time
- You need a smooth envelope for display/dashboard
- Audio-style VU/PPM metering behavior

**Don't use PeakHoldDecay when:**
- You need the exact maximum in a time window → use [WindowedMax](windowed-min-max.md)
- You need the all-time maximum → use [RunningMax](running-min-max.md)
- You need the maximum since last check → use [MaxGauge](max-gauge.md)

## Configuration

```rust
let mut peak = PeakHold::<f64>::builder()
    .hold_samples(10)     // hold peak for 10 samples before decay
    .decay_rate(0.95)     // multiply by 0.95 each sample after hold
    .build().unwrap();
```

### Parameters

| Parameter | What | Default | Guidance |
|-----------|------|---------|----------|
| `hold_samples` | Samples to hold peak before decay starts | 0 | Higher = longer flat top |
| `decay_rate` | Per-sample multiplicative decay (0-1) | 0.99 | Lower = faster fade |

**decay_rate = 0.99** means the peak drops to ~37% after 100 samples.
**decay_rate = 0.95** means the peak drops to ~37% after 20 samples.

## Examples by Domain

### Trading — Worst Latency Envelope

```rust
let mut worst_latency = PeakHold::<f64>::builder()
    .hold_samples(100)   // hold worst spike for 100 ticks
    .decay_rate(0.99)    // slow fade
    .build().unwrap();

// On each event:
let envelope = worst_latency.update(latency_us);
dashboard.set_peak_latency(envelope);
```

### Gaming — Frame Time Spike Display

```rust
let mut spike_display = PeakHold::<f64>::builder()
    .hold_samples(60)    // hold for 1 second at 60fps
    .decay_rate(0.97)
    .build().unwrap();
```

### Audio — Peak Level Meter (PPM)

```rust
let mut meter = PeakHold::<f64>::builder()
    .hold_samples(0)      // no hold — instant decay
    .decay_rate(0.9995)   // slow decay (PPM standard)
    .build().unwrap();
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `PeakHold::<f64>::update` | 7 cycles | 9 cycles |

One comparison (new peak?), one conditional multiply (decay), one
counter decrement (hold). No division, no transcendentals.
