# Use Case: Anomaly Detection

How to detect bad data, outliers, and impossible events in streaming systems.

## The Problem

Not all anomalies are the same:
- **Bad data** — sensor error, parsing bug, stale echo. Clearly wrong.
- **Outlier** — extreme but possibly valid. Needs investigation.
- **Regime change** — the process has genuinely shifted. Not an error.

You need to classify each sample and respond appropriately — not just
binary "good/bad" but graded severity with different actions.

## Recipe: Graded Anomaly Filter

```rust
use nexus_stats::detection::{MultiGateF64, Verdict};
use nexus_stats::statistics::Welford;

let mut gate = MultiGateF64::builder()
    .alpha(0.05)
    .hard_limit_pct(0.30)     // 30% move = reject
    .suspect_z(5.0)           // 5σ = suspect
    .unusual_spread_mult(3.0) // 3× spread = unusual
    .min_samples(50)
    .build().unwrap();

// Only update downstream stats with clean data
let mut stats = Welford::new();

match gate.update(sample) {
    Some(Verdict::Accept) => {
        stats.update(sample);
        process(sample);
    }
    Some(Verdict::Unusual) => {
        stats.update(sample);  // still good data, just noteworthy
        process(sample);
        log_unusual(sample);
    }
    Some(Verdict::Suspect) => {
        // Don't update stats — might be bad
        quarantine(sample);
    }
    Some(Verdict::Reject) => {
        // Definitely bad — drop and log
        log_reject(sample);
    }
    None => {} // warming up
}
```

**Critical rule:** Never update your estimators with data you've classified
as suspect or reject. This is the #1 bug in production anomaly filters.

## Recipe: Robust Outlier Scoring

For cheaper O(1) outlier scoring when MultiGate is overkill:

```rust
use nexus_stats::detection::RobustZScoreF64;

let mut rz = RobustZScoreF64::builder()
    .span(100)
    .reject_threshold(5.0)  // freeze baseline when z > 5
    .min_samples(30)
    .build().unwrap();

if let Some(z) = rz.update(sample) {
    if z.abs() > 5.0 { /* almost certainly bad */ }
    else if z.abs() > 3.5 { /* probable outlier */ }
    else { /* normal */ }
}
```

## Recipe: Distinguish Outlier from Regime Change

An outlier is one bad sample. A regime change is a legitimate shift in
the process. How to tell them apart:

```rust
use nexus_stats::Direction;
use nexus_stats::detection::{MultiGateF64, Verdict, Cusum};

let mut gate = MultiGateF64::builder().alpha(0.05).suspect_z(5.0)
    .hard_limit_pct(0.30).min_samples(50).build().unwrap();

let mut cusum = Cusum::builder(baseline)
    .slack(slack).threshold(threshold).build().unwrap();

// On each sample:
let verdict = gate.update(sample);
let shift = cusum.update(sample);

match (verdict, shift) {
    (Some(Verdict::Reject), _) => {
        // Clearly bad data — reject regardless of CUSUM
    }
    (Some(Verdict::Suspect), Some(Direction::Rising)) => {
        // Extreme sample + mean has shifted = might be legitimate regime change
        // Don't reject — investigate
        log_possible_regime_change(sample);
    }
    (Some(Verdict::Suspect), Some(Direction::Neutral)) => {
        // Extreme sample but no shift = isolated outlier
        quarantine(sample);
    }
    _ => {
        process(sample);
    }
}
```

## Recipe: Rate-of-Change Guard

Sometimes the simplest check is the most effective:

```rust
use nexus_stats::smoothing::Slew<f64>;

// Reject samples that change too fast
let mut slew = Slew::<f64>::new(max_allowed_change);
let clamped = slew.update(sample);

if (clamped - sample).abs() > 0.001 {
    // Sample was clamped — original exceeded rate limit
    log_rate_violation(sample, clamped);
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [MultiGate](../algorithms/multi-gate.md) | Graded severity filter |
| [RobustZScore](../algorithms/robust-z-score.md) | O(1) outlier scoring |
| [CUSUM](../algorithms/cusum.md) | Regime change detection |
| [SlewLimiter](../algorithms/slew.md) | Rate-of-change guard |
| [WindowedMedian](../algorithms/windowed-median.md) | Robust baseline for outlier thresholds |

## Tips

- **Layer your defenses.** Hard limits (SlewLimiter) catch impossible values.
  Statistical tests (MultiGate) catch subtle anomalies. Use both.

- **Never update estimators with rejected data.** MultiGate does this
  automatically. If building your own pipeline, enforce it explicitly.

- **Distinguish outliers from regime changes.** Pair an outlier detector
  (MultiGate) with a shift detector (CUSUM). If both fire, it's probably
  a legitimate change, not bad data.
