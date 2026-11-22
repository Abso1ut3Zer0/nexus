# SlewLimiter — Hard Rate-of-Change Clamp

**Limits how fast the output can change per sample.** Different from
smoothing — this is a hard constraint, not a filter.

| Property | Value |
|----------|-------|
| Update cost | 8 cycles |
| Memory | ~16 bytes |
| Types | `Slew<f64>`, `Slew<i64>` |
| Output | Rate-limited value |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

```
  Input with spike:              SlewLimiter output (max_rate = 5):

  Value                          Value
  100 ┤     ·                    100 ┤
   80 ┤                           80 ┤
   60 ┤                           60 ┤          ╱──── limited to +5/sample
   40 ┤  ·     ·                  40 ┤     ╱──╱
   20 ┤                           20 ┤  ╱─╱
    0 ┤─·──────── ·               0 ┤─·
      └──────────── t                └──────────── t
      spike passes through          spike is rate-clamped
```

The output can never change by more than `max_rate` per sample.
Spikes are slew-limited to a ramp. Gradual changes pass through unchanged.

## When to Use It

- Output conditioning: prevent actuator damage from sudden jumps
- Anti-spike: limit how fast a control signal can change
- Different from EMA (smooths everything) and [MultiGate](multi-gate.md)
  (detects but doesn't correct)

## Configuration

```rust
let mut slew = Slew::<f64>::new(5.0).unwrap();  // max change of 5.0 per sample

slew.update(0.0).unwrap();    // → 0.0
slew.update(100.0).unwrap();  // → 5.0 (clamped)
slew.update(100.0).unwrap();  // → 10.0 (clamped)
slew.update(10.0).unwrap();   // → 10.0 (within range, passes through)
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Slew::<f64>::update` | 8 cycles | 8 cycles |

Clamps as `max(lo).min(hi)` (the sealed `Sample::clamp_to`), which compiles
to a bare `maxsd`/`minsd` pair: branchless, and without the `lo <= hi`
assertion and its panic path that `f64::clamp` carries.
