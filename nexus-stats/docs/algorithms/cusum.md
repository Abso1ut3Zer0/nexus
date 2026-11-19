# CUSUM — Cumulative Sum Change Detector

**Page's Cumulative Sum test (1954).** Detects persistent shifts in the
mean of a streaming process.

| Property | Value |
|----------|-------|
| Update cost | 6 cycles |
| Memory | ~56 bytes |
| Types | `Cusum` |
| Priming | Configurable via `min_samples` |
| Output | `Option<Direction>` — `Rising`, `Falling`, or `None` |

## What It Does

CUSUM accumulates deviations from an expected mean. Small deviations are
absorbed by a "slack" parameter. When enough deviation accumulates to
exceed a threshold, a shift is detected.

It tracks both directions independently:
- **`Direction::Rising`** — the mean has increased (e.g., latency got worse)
- **`Direction::Falling`** — the mean has dropped below target (e.g., latency
  fell under the baseline). A return *to* target reads `Direction::Neutral`.

The sums are not cleared when a threshold is crossed: `update` keeps
reporting the direction until the sum drains back under the threshold (as
long as the excursion took to build) or you call `reset()`. Build with
`.restart_on_alarm()` to zero the alarming side as it reports, so each alarm
is a fresh detection. If both sides are over threshold at once, the one
further over relative to its own threshold is reported.

## When to Use It

**Use CUSUM when:**
- You expect a signal to hover around a known baseline
- You want to detect when the baseline has *permanently* shifted
- You need directional detection (up vs down)
- You want sub-10-cycle detection cost

**Don't use CUSUM when:**
- You want to detect *temporary* spikes → use [MOSUM](mosum.md) instead
- You want to classify individual outliers → use [MultiGate](multi-gate.md) or [AdaptiveThreshold](adaptive-threshold.md)
- You don't know the expected baseline → consider [AdaptiveThreshold](adaptive-threshold.md) which learns its own baseline
- The signal is non-stationary (always trending) → use [TrendAlert](trend-alert.md)

## How It Works

```
Signal with mean shift at sample 50:

  Value
  120 ┤                                          ·  ·  ·  ·  ·
  115 ┤                                       · ·  ·  ·  ·
  110 ┤                                    ·  ·  ·
  105 ┤  ·     ·        ·                 ·
  100 ┤─ ─ · ─ ─ ·─ ─ · ─ ·─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ target
   95 ┤    ·  ·     ·  ·  · ·
   90 ┤                       ·
      └──────────────────────────────────────────────────────── t
                              ↑ shift occurs

  S_upper (cumulative sum):
       ┤                                                ╱ threshold
   50 ─┤─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ╱─ ─ ─ ═══
       ┤                                         ╱    DETECTED!
       ┤                                      ╱
       ┤                                   ╱
       ┤                                ╱
    0 ─┤── ── ── ── ── ── ── ── ── ──╱
       └──────────────────────────────────────────────────────── t
                              ↑ starts accumulating
```

Each sample above `target + slack` adds to `S_upper`. The sum grows
linearly when the mean has shifted. When it crosses the threshold,
the shift is confirmed. Samples at or below target reset the sum
toward zero (the `max(0, ...)` clamp).

Two cumulative sums run independently:

```
S_upper = max(0, S_upper + (x - target) - slack)
S_lower = max(0, S_lower + (target - x) - slack)
```

On each sample:
1. Compute deviation from target: `x - target`
2. Subtract slack (allowable noise): `deviation - slack`
3. Accumulate (but never go below zero)
4. If accumulation exceeds threshold → shift detected

The `max(0, ...)` ensures the sum resets when the signal returns to
normal. This is what makes CUSUM detect *persistent* shifts — a single
spike accumulates once but then gets reset by subsequent normal samples.

### Why Slack Matters

Without slack (k=0), every sample that's even slightly above target
accumulates. You'd detect "shifts" from normal noise. Slack sets the
minimum deviation per sample that counts:

- **Slack = 0** — hypersensitive. Any deviation accumulates.
- **Slack = σ/2** — classic choice. Detects shifts of ~1σ.
- **Slack = σ** — conservative. Only accumulates on >1σ deviations.

Rule of thumb: set slack to half the minimum shift you want to detect.

### Why Threshold Matters

Threshold controls how much evidence you need before declaring a shift:

- **Low threshold** — faster detection, more false alarms
- **High threshold** — slower detection, fewer false alarms

The tradeoff is characterized by the **Average Run Length (ARL)**:
- ARL₀ = average samples before a false alarm (want this high)
- ARL₁ = average samples to detect a real shift (want this low)

For a shift of size δ with slack = δ/2, threshold h ≈ 4-5 gives good
ARL₀ (>1000) with ARL₁ of ~10-20 samples.

## Configuration

```rust
let mut cusum = Cusum::builder(100.0)  // target: baseline mean
    .slack(5.0)                            // sensitivity
    .threshold(50.0)                       // decision boundary
    .min_samples(20)                       // warmup period
    .build().unwrap();
```

### Parameters

| Parameter | What | Default | Guidance |
|-----------|------|---------|----------|
| `target` | Expected baseline mean | Required | From calibration or historical data |
| `slack` | Noise allowance per sample | 5% of target | Half the minimum shift to detect |
| `threshold` | Accumulated evidence for detection | 50% of target | Higher = fewer false alarms |
| `min_samples` | Warmup before detection active | 0 | Set to 10-50 for noisy startup |

### Asymmetric Configuration

Different sensitivity for upward vs downward shifts:

```rust
let cusum = Cusum::builder(100.0)
    .slack_upper(2.0)     // very sensitive to increases
    .slack_lower(10.0)    // tolerant of decreases
    .threshold_upper(20.0)  // trigger fast on degradation
    .threshold_lower(200.0) // trigger slow on recovery
    .build().unwrap();
```

This is useful when upward shifts (degradation) need fast detection but
downward shifts (recovery) should be confirmed over a longer period.

### Seeding

Start with evidence already accumulated, for example carried over from a
previous session:

```rust
let cusum = Cusum::builder(100.0)
    .slack(5.0)
    .threshold(50.0)
    .min_samples(20)
    .seed_upper(30.0)  // 30 of the 50 needed for a Rising alarm
    .build().unwrap();
assert!(cusum.is_primed());      // a seed primes; min_samples no longer applies
assert_eq!(cusum.count(), 0);    // and is not counted as samples
```

Seeds must be finite and non-negative. `reset()` returns to the seeds;
`reset_with_target()` drops them, since they were calibrated against the old
target.

### Integer Inputs

`Cusum` is `f64` only: a sum of deviations is exact for integers below 2^53,
so cast tick durations at the call site rather than carrying a fixed-point
form.

Note: for small integer targets, default slack uses `max(1, target / 20)`
to avoid zero-slack from integer truncation.

## Examples by Domain

### Trading — Exchange Latency Monitoring

```rust
// Baseline ack latency: 200μs, detect 50μs shifts
let mut ack_monitor = Cusum::builder(200.0)
    .slack(25.0)      // half of 50μs minimum shift
    .threshold(200.0) // ~8 samples of sustained shift
    .min_samples(100) // warmup after connect
    .build().unwrap();

// On each ack:
match ack_monitor.update(ack_latency_us) {
    Some(Direction::Rising) => {
        log::warn!("exchange ack latency degraded");
        ack_monitor.reset();  // start watching for next shift
    }
    Some(Direction::Falling) => {
        log::info!("exchange ack latency recovered");
        ack_monitor.reset();
    }
    _ => {}
}
```

### Networking — RTT Shift Detection

```rust
// Detect when path quality changes
let baseline = rtt_baseline_ns as f64;
let mut rtt_monitor = Cusum::builder(baseline)
    .slack(baseline / 10.0)     // 10% tolerance
    .threshold(baseline * 5.0)  // significant evidence
    .build().unwrap();
```

### IoT / Industrial — Sensor Drift

```rust
// Temperature sensor calibrated to 22.0°C
let mut temp_monitor = Cusum::builder(22.0)
    .slack(0.1)       // 0.1°C noise tolerance
    .threshold(2.0)   // 2°C accumulated drift
    .min_samples(60)  // 1 minute warmup at 1 sample/sec
    .build().unwrap();
```

### Gaming — Frame Time Shift

```rust
// Detect when frame time shifts from 16ms baseline (60fps)
let mut frame_monitor = Cusum::builder(16.67)
    .slack(1.0)       // 1ms tolerance
    .threshold(10.0)  // sustained shift evidence
    .build().unwrap();
```

### SRE — Response Time Monitoring

```rust
// Service baseline: 50ms p50
let mut svc_monitor = Cusum::builder(50.0)
    .slack(5.0)
    .threshold(50.0)
    .build().unwrap();

// Alert when: the mean has shifted, not just individual slow requests
```

## Composition Patterns

### CUSUM + Liveness

"Detect both degradation and death":

```rust
let mut cusum = Cusum::builder(baseline).slack(k).threshold(h).build().unwrap();
let mut liveness = Liveness::builder().span(20).deadline_multiple(5).build().unwrap();

// On each event:
liveness.update(now);
if let Some(shift) = cusum.update(latency).unwrap() {
    // Degradation detected
}

// On timer tick:
if !liveness.check(now) {
    // Source is dead — no events at all
}
```

### CUSUM + TrendAlert

"Detect shift AND diagnose if it's getting worse":

```rust
let mut cusum = Cusum::builder(baseline).build().unwrap();
let mut trend = TrendAlert::builder().alpha(0.3).beta(0.1)
    .trend_threshold(0.5).build().unwrap();

match cusum.update(sample) {
    Some(Direction::Rising) => {
        // Shift detected — is it stable or worsening?
        match trend.update(sample) {
            Some(Direction::Rising) => log::error!("degrading and getting worse"),
            Some(Direction::Neutral) => log::warn!("degraded but stable"),
            _ => {}
        }
    }
    _ => { trend.update(sample).unwrap(); }
}
```

### CUSUM + WindowedMedian

"Reset baseline after legitimate regime change":

Use CUSUM to detect the shift. Once confirmed, reset CUSUM with the new
baseline (computed from the WindowedMedian of recent samples):

```rust
if let Some(Direction::Rising) = cusum.update(sample) {
    // Shift detected — compute new baseline from recent data
    if let Some(new_baseline) = median.median() {
        cusum.reset_with_target(new_baseline);
    }
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Cusum::update` | 6 cycles | 6 cycles |

No branches beyond the `max(0, x)` clamp. No division, no transcendentals.

## Academic Reference

Page, E.S. "Continuous Inspection Schemes." *Biometrika* 41.1/2 (1954):
100-115.

The original paper introduces both one-sided and two-sided CUSUM. The
one-sided test (upper only) is the simplest form. The two-sided test
(upper + lower, as implemented here) detects shifts in both directions.

The key parameters (slack `k` and threshold `h`) are analyzed via
Average Run Length (ARL) theory. Tables of ARL values for different
(k, h, δ) combinations can be found in:

- Montgomery, D.C. *Introduction to Statistical Quality Control.* Chapter 9.
- Hawkins, D.M. and Olwell, D.H. *Cumulative Sum Charts and Charting for Quality Improvement.* Springer, 1998.
