# Composing Primitives

How to combine nexus-stats primitives to build complex monitoring systems
from simple parts.

## Principle: Separate Concerns

Each primitive answers one question. Complex monitoring answers multiple
questions by composing primitives, not by finding one primitive that does
everything.

```
┌──────────────┐
│  Raw Signal  │
└──────┬───────┘
       │
       ▼
┌──────────────┐     ┌──────────────┐
│  MultiGate   │────▶│   Rejected   │  (filter bad data)
│  (quality)   │     │   log/drop   │
└──────┬───────┘     └──────────────┘
       │ Accept/Unusual
       ├───────────────────────────┐
       ▼                           ▼
┌──────────────┐           ┌──────────────┐
│     EMA      │           │   Welford    │  (statistics)
│  (smoothed)  │           │  (mean/var)  │
└──────┬───────┘           └──────────────┘
       │
       ▼
┌──────────────┐     ┌──────────────┐
│    CUSUM     │────▶│    Alert     │  (change detection)
│   (shifts)   │     │   handler    │
└──────────────┘     └──────────────┘
```

## Common Patterns

### Filter → Track → Detect

The most common composition. Filter bad data first, track statistics on
clean data, detect anomalies in the statistics.

```rust
// 1. Filter
let verdict = gate.update(sample);
if matches!(verdict, Some(Verdict::Accept | Verdict::Unusual)) {
    // 2. Track
    ema.update(sample);
    stats.update(sample);
    // 3. Detect
    cusum.update(sample);
}
```

### Dual-EMA Crossover

Two EMAs at different speeds detect trend changes when the fast one
crosses the slow one.

```rust
let mut fast = Ema::builder().span(5).build().unwrap();
let mut slow = Ema::builder().span(50).build().unwrap();

if let (Some(f), Some(s)) = (fast.update(x), slow.update(x)) {
    if f > s { /* uptrend */ }
    else { /* downtrend */ }
}
```

### CUSUM + WindowedMedian for Auto-Baseline

When CUSUM detects a shift, use WindowedMedian to compute the new
baseline, then reset CUSUM:

```rust
if let Some(Direction::Rising) = cusum.update(sample) {
    if let Some(new_base) = median.median() {
        cusum.reset_with_target(new_base);
    }
}
```

### Multi-Signal Health Score

Combine several bool-returning monitors into a composite:

```rust
enum Status { Healthy, Warning, Critical }   // your own summary type

let alive = liveness.check(now);
let queue_ok = !matches!(qd.update(now, sojourn), Some(Condition::Degraded));
error_rate.update(ok);
let errors_ok = error_rate.smoothed_ratio().is_none_or(|r| r <= 0.01); // your limit

let health_score = [alive, queue_ok, errors_ok]
    .iter().filter(|&&b| b).count();

match health_score {
    3 => Status::Healthy,
    2 => Status::Warning,
    _ => Status::Critical,
}
```

## Anti-Patterns

### Don't smooth before detecting

Feeding CUSUM an EMA-smoothed signal delays detection. CUSUM works best
on raw (filtered but unsmoothed) data.

### Don't use all-time stats for live alerting

`Welford::mean()` after 1 million samples barely moves when the last
100 samples shift. Use windowed or exponentially-weighted variants.

### Don't cascade detectors redundantly

CUSUM and AdaptiveThreshold both detect mean shifts. Using both on the
same signal doesn't add information — pick the one that fits your model.
