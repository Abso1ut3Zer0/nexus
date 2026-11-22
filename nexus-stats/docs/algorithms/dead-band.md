# DeadBand — Change Suppression

**Only reports when the change exceeds a threshold.** Reduces downstream
processing by suppressing small, irrelevant fluctuations.

| Property | Value |
|----------|-------|
| Update cost | 4 cycles |
| Memory | ~16 bytes |
| Types | `DeadBand<f64>`, `DeadBand<i64>` |
| Output | `Option<T>` — `Some(value)` if changed enough, `None` if suppressed |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

```
  Without dead band — every change reported:

  Value
  102 ┤     ·
  101 ┤  ·     ·     ·     ·
  100 ┤     ·     ·     ·     ·     ← 10 reports for 2-unit noise
   99 ┤  ·     ·     ·
   98 ┤
      └──────────────────────────── t
  Reports: ↑  ↑  ↑  ↑  ↑  ↑  ↑  ↑  ↑  ↑  (10 reports)


  With dead band (threshold = 5):

  Value
  102 ┤     ·
  101 ┤  ·     ·     ·     ·
  100 ┤     ·     ·     ·     ·     ← suppressed (change < 5)
   99 ┤  ·     ·     ·
   98 ┤
      └──────────────────────────── t
  Reports: ↑                         (1 report — initial value only)


  With actual significant change:

  Value
  115 ┤                           ·
  110 ┤                        ·  ·
  105 ┤── ── ── ── ── ── ── ── ── ── dead band upper
  100 ┤  ·  ·  ·  ·  ·  ·  ·
   95 ┤── ── ── ── ── ── ── ── ── ── dead band lower
      └──────────────────────────── t
  Reports: ↑                     ↑    (2 reports — initial + significant change)
```

## When to Use It

**Use DeadBand when:**
- Downstream is expensive and most changes don't matter
- You want to reduce event/notification volume
- Slowly-drifting signals generate too much noise

**Don't use DeadBand when:**
- Every change matters (order book updates, price ticks)
- You want smoothing, not suppression → use EMA

## Configuration

```rust
let mut db = DeadBand::<f64>::new(5.0).unwrap();  // suppress changes < 5.0

// Returns Some only when change from last reported value exceeds threshold
match db.update(sample).unwrap() {
    Some(value) => send_downstream(value),  // significant change
    None => {}                               // suppressed
}
```

## Examples by Domain

### IoT — Sensor Reporting

```rust
// Temperature sensor: only report if changed by 0.5°C
let mut db = DeadBand::<f64>::new(0.5).unwrap();
```

### SRE — Metric Reduction

```rust
// CPU utilization: only alert on 5% changes
let mut db = DeadBand::<f64>::new(5.0).unwrap();
```

### Trading — Quote Throttling

```rust
// Throttle internal quote updates: only propagate if price moved 1 tick
let mut db = DeadBand::<i64>::new(1).unwrap();
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `DeadBand::<f64>::update` | 4 cycles | 4 cycles |

One subtraction, one absolute value, one comparison.
