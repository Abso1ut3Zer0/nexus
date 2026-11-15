# MultiGate — Layered Anomaly Filter

**Three-level gate pattern with graded severity.** The production
standard for filtering bad data in real-time systems.

| Property | Value |
|----------|-------|
| Update cost | ~12 cycles |
| Memory | ~56 bytes |
| Types | `MultiGate` |
| Priming | Configurable via `min_samples` |
| Output | `Option<Verdict>` — `Accept`, `Unusual`, `Suspect`, `Reject` |

## What It Does

```
  Three gates, progressively more sensitive:

  Value
  200 ┤  ·                                    Reject (hard limit)
      ┤ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ── Gate 1: hard limit
  150 ┤
      ┤ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ── Gate 2: z-score
  130 ┤              ·                        Suspect (statistical)
  120 ┤
      ┤ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ── Gate 3: spread
  110 ┤     ·           ·                    Unusual (spread-relative)
  100 ┤──·──·──·──·──·──·──·──·──·──·──·── Accept
   90 ┤
      └─────────────────────────────────────── t
```

Each gate acts as a filter. A sample must pass the outer gates before
reaching the inner ones:

1. **Gate 1 (Hard limit)** — absolute percentage rejection. "Price moved
   50% in one tick — impossible."
2. **Gate 2 (Z-score)** — statistical rejection. "This move is 6 standard
   deviations from recent behavior."
3. **Gate 3 (Spread)** — relative to recent volatility. "This move is
   unusual given recent spread."

## Critical Design Property

**The internal baseline EMA is NOT updated on Suspect or Reject verdicts.**

This prevents estimator corruption — a bad sample can't shift the
baseline, which would make future bad samples harder to detect. This
is the #1 bug in production anomaly filters.

```
  Without freeze:                  With freeze:
  bad tick shifts EMA →            EMA stays stable →
  next bad tick looks normal →     next bad tick still detected →
  estimator "forgets" what         correct operation
  normal looks like
```

## Configuration

```rust
let mut gate = MultiGate::builder()
    .alpha(0.1)              // EMA smoothing
    .hard_limit_pct(0.50)    // reject >50% moves (Gate 1)
    .suspect_z(6.0)          // suspect >6σ moves (Gate 2)
    .unusual_spread_mult(3.0) // unusual >3× recent spread (Gate 3)
    .min_samples(20)
    .build().unwrap();

match gate.update(sample) {
    Some(Verdict::Accept)  => process(sample),
    Some(Verdict::Unusual) => { process(sample); log_unusual(sample); }
    Some(Verdict::Suspect) => { log_suspect(sample); /* don't process */ }
    Some(Verdict::Reject)  => { log_reject(sample); /* definitely don't process */ }
    None => {} // not primed
}
```

## Examples

### Trading — Market Data Quality
```rust
let mut tick_filter = MultiGate::builder()
    .alpha(0.05)
    .hard_limit_pct(0.20)     // 20% move = impossible for this instrument
    .suspect_z(5.0)
    .unusual_spread_mult(5.0)
    .min_samples(100)
    .build().unwrap();
```

### IoT — Sensor Data Validation
```rust
let mut sensor = MultiGate::builder()
    .alpha(0.1)
    .hard_limit_pct(0.50)
    .suspect_z(4.0)
    .min_samples(30)
    .build().unwrap();
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `MultiGate::update` | 12 cycles | 17 cycles |

Three gate checks + conditional EMA update. The conditional update
(freeze on reject) adds no cost on the Accept path.
