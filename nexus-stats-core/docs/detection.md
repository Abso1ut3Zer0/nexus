# Detection (core)

Basic change-detection primitives that ship with the core crate. Module path: `nexus_stats_core::detection`.

For advanced detection (MOSUM, Shiryaev-Roberts, AdaptiveThreshold, RobustZScore, TrendAlert, MultiGate), see [`nexus-stats-detection`](../../nexus-stats-detection/docs/INDEX.md).

## At a glance

| Type | Detects |
|------|---------|
| `Cusum` | Persistent shifts in mean (Page 1954) |
| `DistributionShift` | Change in distribution shape (skewness/kurtosis) |

---

## CUSUM — Cumulative Sum

Page's cumulative sum test. Two accumulators (`upper` and `lower`) track cumulative deviation from a target. A `threshold` crossing signals a persistent shift.

```text
upper_t = max(0, upper_{t-1} + (sample - target - slack))
lower_t = max(0, lower_{t-1} + (target - sample - slack))

if upper_t > threshold -> Rising
if lower_t > threshold -> Falling
```

The `slack` parameter (typically 0.5 * expected_shift) prevents false alarms from normal noise.

### API

```rust,ignore
impl Cusum {
    pub fn builder(target: f64) -> CusumBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<Direction>, DataError>;
    pub fn upper(&self) -> f64;
    pub fn lower(&self) -> f64;
    pub fn reset(&mut self);
    // ...
}
```

`update` returns `Ok(None)` until `min_samples` samples have been seen (the default is 0, so by default never). After that it returns `Ok(Some(Direction::Rising))` while the upper sum is over its threshold, `Ok(Some(Direction::Falling))` while the lower sum is, and `Ok(Some(Direction::Neutral))` otherwise.

### After an alarm

The sums are not cleared when a threshold is crossed. `update` keeps reporting the direction until the sum drains back under the threshold, which takes as long as the excursion took to build, or until you call `reset()`. For one alarm per detection, build with `.restart_on_alarm()`: the alarming side is zeroed as it reports.

If both sides are over threshold at once, the side further over relative to its own threshold is reported. `upper()` and `lower()` expose both sums.

### Example — latency shift detector

```rust
use nexus_stats_core::detection::Cusum;
use nexus_stats_core::Direction;

let target = 120.0; // expected latency in us
let mut cusum = Cusum::builder(target)
    .slack(10.0)          // ignore noise up to 10us
    .threshold(50.0)      // cumulative budget before alert
    .restart_on_alarm()   // one alarm per detection
    .build()
    .unwrap();

// On target, then a persistent +30us shift. Each shifted sample adds
// 30 - 10 = 20 to the upper sum: 20, 40, 60 crosses the threshold of 50.
let latencies = [120.0, 125.0, 115.0, 150.0, 150.0, 150.0, 150.0];
let mut alarms = Vec::new();
for (i, &latency) in latencies.iter().enumerate() {
    match cusum.update(latency).unwrap() {
        Some(Direction::Rising) => alarms.push((i, "up")),
        Some(Direction::Falling) => alarms.push((i, "down")),
        Some(Direction::Neutral) | None => {}
    }
}
assert_eq!(alarms, [(5, "up")]);
```

**Use for:** detecting persistent mean shifts — e.g. a GC policy change added 20us to every request, and you want to know within a dozen samples.

**Caveats:** detects *persistent* shifts, not spikes. One bad sample doesn't trip it. For spike detection, use `MOSUM` from `nexus-stats-detection`. Tuning is the hard part — see umbrella `algorithms/cusum.md` for the full tuning story.

**Parameter tuning:**
- `slack` ≈ half the size of the smallest shift you want to catch. Bigger slack = fewer false positives, slower detection.
- `threshold` is a noise budget; larger = fewer false alarms, slower detection. Rule of thumb: `threshold = 5 * sigma` for clean data, `10 * sigma` for noisy.

---

## DistributionShift

Detects changes in the *shape* of a distribution rather than its mean: kurtosis shift (tails getting fatter/thinner) and skewness shift. Maintains two windows — a slow baseline and a fast recent window — and compares them.

```rust
use nexus_stats_core::detection::DistributionShift;

let mut ds = DistributionShift::builder()
    .fast_window(100)
    .build()
    .unwrap();

let returns = (0..250).map(|i| f64::from(i % 7) - 3.0);
for r in returns { ds.update(r).unwrap(); }

if ds.is_shifted(2.0) {
    // the fast window's kurtosis or skewness differs from the baseline's
    // by more than 2.0
    println!("distribution shape changed");
}
```

**Use for:** "something structural changed" detection — e.g. market regime changes where the mean is still 0 but the tails got fatter. Complements CUSUM (mean shift) and MOSUM (spike).

---

## Cross-references

- Spike / transient detection: [`MOSUM`](../../nexus-stats-detection/docs/detection.md#mosum--moving-sum) in `nexus-stats-detection`.
- Optimal change detection: [`Shiryaev-Roberts`](../../nexus-stats-detection/docs/detection.md#shiryaevroberts--optimal-change-detection).
- Adaptive anomaly: [`AdaptiveThreshold`](../../nexus-stats-detection/docs/detection.md#adaptivethreshold--ema-based-z-score).
- Moments used to build `DistributionShift`: [`Moments`](statistics.md#moments--skewness-and-kurtosis).
