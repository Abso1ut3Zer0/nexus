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

```
upper_t = max(0, upper_{t-1} + (sample - target - slack))
lower_t = max(0, lower_{t-1} + (target - sample - slack))

if upper_t > threshold -> upward shift
if lower_t > threshold -> downward shift
```

The `slack` parameter (typically 0.5 * expected_shift) prevents false alarms from normal noise.

### API

```rust
impl Cusum {
    pub fn builder(target: f64) -> CusumBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<Direction>, DataError>;
    pub fn upper(&self) -> f64;
    pub fn lower(&self) -> f64;
    pub fn reset(&mut self);
    // ...
}
```

`update` returns `Ok(Some(Direction::Up))` or `Ok(Some(Direction::Down))` when a threshold crosses, else `Ok(None)`.

### Example — latency shift detector

```rust
use nexus_stats_core::detection::Cusum;
use nexus_stats_core::Direction;

let target = 120.0; // expected latency in us
let mut cusum = Cusum::builder(target)
    .slack(10.0)          // ignore noise up to 10us
    .threshold(50.0)      // cumulative budget before alert
    .build()
    .unwrap();

for &latency in &latencies {
    match cusum.update(latency).unwrap() {
        Some(Direction::Up)   => println!("latency regime shifted UP"),
        Some(Direction::Down) => println!("latency regime shifted DOWN"),
        None => {}
    }
}
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
    .build();

for r in returns { ds.update(r).unwrap(); }

if ds.is_shifted(2.0) {
    // z-score > 2 on kurtosis or skewness shift
    println!("distribution shape changed");
}
```

**Use for:** "something structural changed" detection — e.g. market regime changes where the mean is still 0 but the tails got fatter. Complements CUSUM (mean shift) and MOSUM (spike).

---

## Cross-references

- Spike / transient detection: [`MOSUM`](../../nexus-stats-detection/docs/detection.md#mosum) in `nexus-stats-detection`.
- Optimal change detection: [`Shiryaev-Roberts`](../../nexus-stats-detection/docs/detection.md#shiryaev-roberts).
- Adaptive anomaly: [`AdaptiveThreshold`](../../nexus-stats-detection/docs/detection.md#adaptivethreshold).
- Moments used to build `DistributionShift`: [`Moments`](statistics.md#momentsf64--skewness-and-kurtosis).
