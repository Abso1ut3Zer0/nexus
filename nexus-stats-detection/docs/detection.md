# Detection Algorithms

Module path: `nexus_stats_detection::detection`.

---

## MOSUM — Moving Sum

**Types:** `Mosum`. Requires `alloc`.

### What it does

Maintains a sliding window sum of `(sample - target)` and fires when the moving sum exceeds a positive or negative threshold. Like CUSUM but bounded to recent history — old evidence ages out.

```
mosum_t = sum_{i = t - window + 1}^{t} (sample_i - target)
fire if mosum_t > +threshold   (Direction::Up)
fire if mosum_t < -threshold   (Direction::Down)
```

### When to use it

- **Transient spikes.** "Did something go wrong in the last 100 samples?" — a CUSUM would latch the evidence forever, but MOSUM forgets.
- **Local anomalies.** Temporary drift due to a one-off cause (deploy, GC storm, exchange hiccup).
- **Low false alarm rate over long runs.** CUSUM accumulates forever; a slow drift will eventually trigger. MOSUM stays bounded.

### API

```rust
impl Mosum {
    pub fn builder(target: f64) -> MosumBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<Direction>, DataError>;
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
    // value accessors, see source
}

impl MosumBuilder {
    pub fn window(self, n: u64) -> Self;
    pub fn threshold(self, t: f64) -> Self;
    pub fn build(self) -> Result<Mosum, ConfigError>;
}
```

### Example — latency spike detector

```rust
use nexus_stats_detection::detection::Mosum;
use nexus_stats_core::Direction;

let mut mosum = Mosum::builder(120.0) // target latency 120us
    .window_size(50)
    .threshold(500.0)                    // 500us-us cumulative budget
    .build()
    .unwrap();

for &latency in &request_latencies {
    if let Some(dir) = mosum.update(latency).unwrap() {
        eprintln!("mosum fired: {dir:?}");
    }
}
```

### Parameter tuning

- `window`: trade responsiveness vs stability. 20-200 typical.
- `threshold`: roughly `3 * window * sigma_expected`. Start conservative and tighten.

### Caveats

- Not optimal in the minimax sense — use Shiryaev-Roberts if you need that.
- Window sum has a burn-in period; `is_primed()` is false until the window fills.

---

## ShiryaevRoberts — Optimal change detection

**Type:** `ShiryaevRoberts`. Requires `std` or `libm`.

### What it does

Shiryaev-Roberts is the asymptotically optimal (minimax) change-point detector when the pre-change and post-change distributions are known. It maintains a likelihood-ratio statistic `R_t` and fires when `R_t` exceeds a threshold.

Under the standard framing, you provide the pre-change mean, the post-change mean, and the noise variance. The detector updates the likelihood ratio on every sample.

### When to use it

- You *know* what the "bad" regime looks like (from calibration or domain knowledge).
- You want the lowest possible expected detection delay at a fixed false-alarm rate.
- You have Gaussian-ish data with known variance.

### API

```rust
impl ShiryaevRoberts {
    pub fn builder() -> ShiryaevRobertsBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<bool>, DataError>;
    pub fn is_primed(&self) -> bool;
    // more accessors, see source
}

impl ShiryaevRobertsBuilder {
    pub fn pre_change_mean(self, mean: f64) -> Self;
    pub fn post_change_mean(self, mean: f64) -> Self;
    pub fn variance(self, variance: f64) -> Self;
    pub fn threshold(self, t: f64) -> Self;
    pub fn build(self) -> Result<ShiryaevRoberts, ConfigError>;
}
```

### Example — regime-change detector

```rust
use nexus_stats_detection::detection::ShiryaevRoberts;

// Known: pre-change mean 0.5, post-change mean 1.2, noise sigma 0.3 (variance 0.09).
let mut sr = ShiryaevRoberts::builder()
    .pre_change_mean(0.5)
    .post_change_mean(1.2)
    .variance(0.09)
    .threshold(100.0) // larger = fewer false alarms, slower detection
    .build()
    .unwrap();

for &x in &stream {
    if let Some(true) = sr.update(x).unwrap() {
        println!("regime change detected");
        break;
    }
}
```

### Caveats

- Needs the post-change distribution known. If you don't know it, use CUSUM or MOSUM.
- Log-likelihood ratio accumulates; reset after each detection.

---

## AdaptiveThreshold — EMA-based z-score

**Type:** `AdaptiveThreshold`. Requires `std` or `libm`.

### What it does

Maintains a streaming EMA and EW variance. On each update, computes `z = (x - ema) / stddev`. Fires when `|z|` exceeds a configured threshold.

### When to use it

- You want the simplest streaming z-score outlier detector.
- Data is Gaussian-ish (no fat tails).
- You want the baseline to adapt to gradual drift.

### API

```rust
impl AdaptiveThreshold {
    pub fn builder() -> AdaptiveThresholdBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<Direction>, DataError>;
    pub fn z_score(&self) -> Option<f64>;
    // more
}
```

### Example — CPU load outlier

```rust
use nexus_stats_detection::detection::AdaptiveThreshold;
use nexus_stats_core::Direction;

let mut at = AdaptiveThreshold::builder()
    .halflife(500.0)
    .z_threshold(3.0)      // flag samples beyond 3 sigma of the adaptive baseline
    .build()
    .unwrap();

for &load in &cpu_samples {
    match at.update(load).unwrap() {
        Some(Direction::Rising) => page_oncall("cpu spike"),
        Some(Direction::Falling) => log_warn("cpu dropout"),
        _ => {}
    }
}
```

### Caveats

- Gaussian assumption. Fat tails → frequent false alarms. Use `RobustZScore<f64>` instead.
- The baseline adapts — if the anomaly is *sustained*, the baseline eventually catches up and the alarm clears.

---

## RobustZScore — MAD-based anomaly score

**Type:** `RobustZScore<f64>`.

### What it does

Maintains an EMA of the level and an EMA of the mean absolute deviation about it (no sorted window, so no median). Computes `z = sqrt(2/π) * (x - ema) / ema_abs_dev`: for Gaussian data `E|X - μ| = σ·sqrt(2/π)`, so the factor `sqrt(2/π) ≈ 0.798` puts the score in standard-deviation units. The scale only moves when a sample is accepted (`|z|` below the reject threshold), so outliers cannot inflate it.

Robust to up to ~50% corruption — unlike AdaptiveThreshold, whose variance estimate gets polluted by the very outliers you're trying to detect.

### When to use it

- **Heavy-tailed data.** Financial returns, sensor flakes, anything with real outliers.
- **Unknown noise model.** MAD is nonparametric.
- **Long-running detectors** where accumulated outliers would degrade a Gaussian baseline.

### API

```rust
impl RobustZScore<f64> {
    pub fn builder() -> RobustZScoreBuilder<f64>;
    /// The robust z-score of `sample` once primed; samples past
    /// `reject_threshold` are scored but do not move the estimators.
    pub fn update(&mut self, sample: f64) -> Result<Option<f64>, DataError>;
    // accessors: z_score(), baseline(), mad(), count(), is_primed(), reset()
}
```

### Example — price outlier detection

```rust
use nexus_stats_detection::detection::RobustZScore;

let mut rz = RobustZScore::<f64>::builder()
    .span(50)                 // EMA span for the baseline and the MAD scale
    .reject_threshold(3.5)    // |z| above this does not move the estimators
    .build()
    .unwrap();

for &price in &prices {
    if let Some(z) = rz.update(price).unwrap() {
        if z.abs() > 3.0 {
            println!("price outlier: z = {z:.1}");
        }
    }
}
```

### Caveats

- Slightly more expensive than `AdaptiveThreshold` (needs running median or approximation).
- Reaction time is similar — no free lunch.

---

## TrendAlert — Forecast-based detection

**Type:** `TrendAlert`.

### What it does

Internally maintains a Holt-style level + trend estimate. Fires when the smoothed trend (slope per sample) exceeds a threshold, absolute (`trend_threshold`) or relative to the level (`trend_threshold_relative`); `forecast(steps)` projects the level ahead for your own limit checks.

### When to use it

- **SLO degradation warnings.** "Latency is increasing — will cross SLO in 30s, page now."
- **Capacity forecasting.** Utilization climbing toward 100%.
- **Anywhere the rate-of-change matters more than the current value.**

### API

```rust
impl TrendAlert {
    pub fn builder() -> TrendAlertBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<Direction>, DataError>;
    // level(), trend(), forecast(steps)
}
```

### Example — SLO degradation

```rust
use nexus_stats_detection::detection::TrendAlert;
use nexus_stats_core::Direction;

let mut alert = TrendAlert::builder()
    .alpha(0.3)
    .beta(0.05)
    .trend_threshold(0.5)   // slope per sample (latency units) that counts as a trend
    .build()
    .unwrap();

for &latency in &stream {
    if let Some(Direction::Rising) = alert.update(latency).unwrap() {
        fire_page();
    }
}
```

### Caveats

- Holt assumes local linearity. Projecting 10000 samples ahead is meaningless.
- Two-parameter tuning (alpha, beta) is harder than one. See [Holt tuning](../../nexus-stats-smoothing/docs/parameter-tuning.md#holt-alpha-and-beta).

---

## MultiGate — Layered severity

**Type:** `MultiGate`.

### What it does

Three gates, outer to inner, each more sensitive than the last, giving one `Verdict` per sample: a **hard limit** on the fractional move from the EMA baseline (`Reject`), a **z-score** gate against the EW standard deviation (`Suspect`), and a **spread** gate relative to recent volatility (`Unusual`); a sample inside all three is `Accept`. The baseline EMA is not updated on `Suspect` or `Reject`, so a bad sample cannot pull the estimator toward itself and hide the next one.

### When to use it

- **Market data quality**: reject impossible prints, flag suspicious ones, keep the baseline honest.
- **Sensor validation**, and any feed where graded severity beats a single outlier flag.

### API

```rust
impl MultiGate {
    pub fn builder() -> MultiGateBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<Verdict>, DataError>;
}

impl MultiGateBuilder {
    pub fn alpha(self, alpha: f64) -> Self;                // or span(n)
    pub fn hard_limit(self, pct: f64) -> Self;             // gate 1: fraction of the baseline
    pub fn suspect_z(self, z: f64) -> Self;                // gate 2: z-score
    pub fn unusual_spread_multiple(self, k: f64) -> Self;  // gate 3: multiple of recent spread
    pub fn min_samples(self, min: u64) -> Self;
    pub fn build(self) -> Result<MultiGate, ConfigError>;
}
```

`Verdict` is `Accept | Unusual | Suspect | Reject`. Diagrams and examples: [MultiGate](../../nexus-stats/docs/algorithms/multi-gate.md).

---

## Cross-references

- CUSUM and DistributionShift: [`nexus-stats-core::detection`](../../nexus-stats-core/docs/detection.md).
- Smoothing before detection: [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).
- `Condition` and `Direction` enums: `nexus_stats_core::{Condition, Direction}`.
