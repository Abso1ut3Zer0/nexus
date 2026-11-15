# Use Case: Latency Monitoring

How to track, smooth, alert on, and diagnose latency in real-time systems.

## The Problem

You have a stream of latency measurements (round-trip times, processing
durations, queue wait times). You need to:

- Display a smooth current value (not jumpy)
- Detect when latency has degraded
- Detect when latency has recovered
- Track the worst recent spike
- Know if latency is trending upward over time
- Filter out bad measurements (sensor errors, clock glitches)

## Recipe: Basic Latency Dashboard

```rust
use nexus_stats::smoothing::Ema;
use nexus_stats::statistics::Welford;
use nexus_stats::monitoring::PeakHold;

// Smooth display value
let mut ema = Ema::builder().span(20).min_samples(5).build().unwrap();

// Running statistics
let mut stats = Welford::new();

// Worst recent spike (fades over 100 samples)
let mut peak = PeakHold::<f64>::builder()
    .hold_samples(50)
    .decay_rate(0.98)
    .build().unwrap();

// On each latency measurement:
fn on_measurement(latency_us: f64,
                  ema: &mut Ema,
                  stats: &mut Welford,
                  peak: &mut PeakHold<f64>) {
    let smoothed = ema.update(latency_us);
    stats.update(latency_us);
    let envelope = peak.update(latency_us);

    // Display:
    // smoothed = current smoothed latency
    // stats.mean() = long-term average
    // stats.std_dev() = variability
    // envelope = worst recent spike (fading)
}
```

## Recipe: Latency Degradation Detection

```rust
use nexus_stats::Direction;
use nexus_stats::detection::{Cusum, TrendAlert};

let baseline_us = 200.0;  // from calibration

// Detect persistent shifts
let mut cusum = Cusum::builder(baseline_us)
    .slack(10.0)       // 10μs noise tolerance
    .threshold(100.0)  // 100μs accumulated evidence
    .min_samples(50)
    .build().unwrap();

// Detect trend (getting worse over time, not just high)
let mut trend = TrendAlert::builder()
    .alpha(0.3)
    .beta(0.1)
    .trend_threshold(0.5)  // 0.5μs/sample increase rate
    .build().unwrap();

// On each measurement:
match cusum.update(latency_us) {
    Some(Direction::Rising) => {
        // Latency degraded — check if stable or worsening
        match trend.update(latency_us) {
            Some(Direction::Rising) => {
                // Getting worse — escalate
                alert_escalate("latency degrading and trending up");
            }
            Some(Direction::Neutral) => {
                // Degraded but stable — shifted to new level
                alert_warn("latency shifted up, stable at new level");
            }
            _ => {}
        }
        cusum.reset();
    }
    Some(Direction::Falling) => {
        alert_info("latency recovered");
        cusum.reset();
    }
    _ => { trend.update(latency_us).unwrap(); }
}
```

## Recipe: Latency Jitter Monitoring

```rust
use nexus_stats::monitoring::Jitter;

let mut jitter = Jitter::<f64>::builder().span(30).build().unwrap();

// On each measurement:
if let Some(j) = jitter.update(latency_us).unwrap() {
    if let Some(ratio) = jitter.jitter_ratio() {
        if ratio > 0.3 {
            // Jitter is 30% of mean — unstable
            alert_warn("high latency jitter");
        }
    }
}
```

## Recipe: Bad Measurement Filtering

```rust
use nexus_stats::detection::{MultiGate, Verdict};
use nexus_stats::statistics::Welford;

// Multi-gate filter: reject impossible values, flag suspect ones
let mut gate = MultiGate::builder()
    .alpha(0.05)
    .hard_limit(0.50)  // reject >50% jumps
    .suspect_z(5.0)        // flag >5σ jumps
    .min_samples(50)
    .build().unwrap();

// Only feed good data to downstream stats
let mut stats = Welford::new();

match gate.update(latency_us) {
    Some(Verdict::Accept) | Some(Verdict::Unusual) => {
        stats.update(latency_us);  // good data
    }
    Some(Verdict::Suspect) => {
        log_suspect(latency_us);   // don't update stats
    }
    Some(Verdict::Reject) => {
        log_reject(latency_us);    // definitely don't update
    }
    None => {}
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [EMA](../algorithms/ema.md) | Smooth display value |
| [Welford](../algorithms/welford.md) | Running mean/variance/std_dev |
| [PeakHoldDecay](../algorithms/peak-hold.md) | Worst recent spike envelope |
| [CUSUM](../algorithms/cusum.md) | Shift detection (up/down) |
| [TrendAlert](../algorithms/trend-alert.md) | Trend direction (rising/stable/falling) |
| [Jitter](../algorithms/jitter.md) | Variability measurement |
| [MultiGate](../algorithms/multi-gate.md) | Bad measurement filtering |

## Tips

- **Don't use all-time statistics for alerting.** A 99th percentile
  computed over hours is useless for detecting a degradation that started
  30 seconds ago. Use windowed or exponentially-weighted stats.

- **Separate smoothing from detection.** EMA for display, CUSUM for
  detection. Feeding CUSUM a pre-smoothed signal delays detection.

- **Filter before tracking.** Bad measurements corrupt your statistics.
  Use MultiGate first, then feed only accepted data to Welford/EMA.

- **Detect recovery, not just degradation.** `Direction::Falling` tells you
  when a problem is fixed — useful for auto-closing alerts.
