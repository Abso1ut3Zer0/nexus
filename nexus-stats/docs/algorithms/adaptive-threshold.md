# AdaptiveThreshold — Z-Score Anomaly Detection

**Detects anomalous samples using a self-learning baseline.** Internally
combines EMA (baseline) + Welford (std dev) to compute z-scores.

| Property | Value |
|----------|-------|
| Update cost | ~15 cycles |
| Memory | ~56 bytes |
| Types | `AdaptiveThreshold` |
| Priming | Default: 20 samples (needs enough data for std_dev) |
| Output | `Option<Direction>` — `Rising` or `Falling` once `|z|` crosses the threshold, else `None` |

## What It Does

```
  z-score = (sample - baseline) / std_dev

  Value
  130 ┤                              ·  ← z > 3 → Direction::Rising
      ┤ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─  +3σ
  115 ┤
  110 ┤     ·  ·     ·
  105 ┤  ·     ·  ·     ·  ·  ·  ·        Normal range
  100 ┤──────────────────────────────────  baseline (EMA)
   95 ┤  ·     ·        ·
      ┤ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─  -3σ
   70 ┤        ·                          ← z < -3 → Direction::Falling
      └──────────────────────────────────── t
```

Reports **direction**: `Rising` (above baseline) or `Falling` (below baseline).
This matters — a latency spike (`Rising`) is different from a latency improvement (`Falling`).

## When to Use It

- "Is this sample unusual given recent behavior?"
- You don't know the baseline in advance (it's learned)
- You want directional anomaly classification

## When to Use Something Else

- You know the baseline → [CUSUM](cusum.md) (persistent shifts) or [MultiGate](multi-gate.md) (graded)
- You want robust detection (outlier-resistant) → [RobustZScore](robust-z-score.md) (MAD-based)

## Configuration

```rust
let mut at = AdaptiveThreshold::builder()
    .span(50)            // EMA baseline smoothing
    .z_threshold(3.0)    // standard 3-sigma threshold
    .min_samples(20)     // warmup for std_dev
    .build().unwrap();

// Or seed from known baseline:
let at = AdaptiveThreshold::builder()
    .span(50)
    .z_threshold(3.0)
    .seed(100.0, 5.0)  // baseline_mean=100, baseline_std=5
    .build().unwrap();
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `AdaptiveThreshold::update` | ~15 cycles | ~20 cycles |

EMA update + Welford update + z-score computation + comparison.
