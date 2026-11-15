# CriticallyDampedSpring — Smooth Target Chasing

**Chase a moving target without overshoot.** Has velocity tracking so it
anticipates rather than lags. Unity's `SmoothDamp` — one of the most-used
utility functions in game development.

| Property | Value |
|----------|-------|
| Update cost | 18 cycles |
| Memory | ~16 bytes |
| Types | `Spring` |
| Output | Current smoothed value |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

```
  Target jumps from 0 to 100:

  EMA (alpha=0.1):
  100 ┤                              ─────────
   80 ┤                         ──
   60 ┤                    ──
   40 ┤               ──             lags behind,
   20 ┤          ──                  approaches asymptotically
    0 ┤─────────
      └──────────────────────────────────────── t

  Spring (smooth_time=10):
  100 ┤                    ───────────────────
   80 ┤                ─
   60 ┤             ─                faster convergence,
   40 ┤          ─                   no overshoot,
   20 ┤       ─                      has velocity (anticipates)
    0 ┤──────
      └──────────────────────────────────────── t

  Underdamped spring (NOT this — for comparison):
  120 ┤                 ─
  100 ┤              ─     ─────── ────────
   80 ┤            ─     ─        overshoots!
   60 ┤         ─
    0 ┤──────
      └──────────────────────────────────────── t
```

The critically damped spring converges as fast as possible WITHOUT
overshooting. It's the optimal response — any faster would oscillate,
any slower would lag unnecessarily.

## When to Use It

**Use Spring when:**
- You need to smoothly chase a moving target
- Overshoot is unacceptable (display values, adaptive thresholds)
- The target changes frequently and you want smooth transitions
- You need variable-dt stability (game loops, irregular updates)

**Don't use Spring when:**
- You just need simple signal smoothing → [EMA](ema.md)
- You need statistics (variance, etc.) → [Welford](welford.md)
- The target is the signal itself, not a separate goal

## Configuration

```rust
let mut spring = Spring::new(0.5).unwrap();  // smooth_time in seconds

// Each update: provide target and time delta
let smoothed = spring.update(target_value, dt_seconds).unwrap();
```

### Parameters

| Parameter | What | Guidance |
|-----------|------|----------|
| `smooth_time` | Time to converge (seconds) | Lower = faster, snappier |

**smooth_time = 0.1** — snappy, reaches target in ~0.3s
**smooth_time = 0.5** — smooth, reaches target in ~1.5s
**smooth_time = 2.0** — very smooth, reaches target in ~6s

### Implementation Note

Uses a Padé approximant instead of `exp(-x)` for numerical stability
with variable dt. Accurate within 1% for `omega × dt < 2`. For very
large dt values, the spring still converges — just not at the
mathematically exact rate.

## Examples

### Dashboard — Smooth Gauge Display
```rust
let mut gauge = Spring::new(0.3).unwrap();

// On each data update (potentially irregular):
let display_value = gauge.update(actual_value, dt).unwrap();
render_gauge(display_value);
```

### Trading — Adaptive Threshold
```rust
let mut threshold = Spring::new(1.0).unwrap();

// Smoothly track a moving threshold target
let target = compute_new_threshold(market_conditions);
let smooth_threshold = threshold.update(target, dt).unwrap();
```

### Gaming — Camera Follow
```rust
let mut cam_x = Spring::new(0.2).unwrap();
let mut cam_y = Spring::new(0.2).unwrap();

let sx = cam_x.update(player_x, dt).unwrap();
let sy = cam_y.update(player_y, dt).unwrap();
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Spring::update` | 18 cycles | 18 cycles |

~10 floating-point ops. No transcendentals (Padé approximant avoids
`exp()`). Consistent timing — no data-dependent branches.
