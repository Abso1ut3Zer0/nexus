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
    .window(50)
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

Under the standard framing, you provide the pre-change mean (`mu_0`), post-change mean (`mu_1`), and noise scale (`sigma`). The detector updates the likelihood ratio on every sample.

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
    pub fn mu_before(self, mu: f64) -> Self;
    pub fn mu_after(self, mu: f64) -> Self;
    pub fn sigma(self, sigma: f64) -> Self;
    pub fn threshold(self, t: f64) -> Self;
    pub fn build(self) -> Result<ShiryaevRoberts, ConfigError>;
}
```

### Example — regime-change detector

```rust
use nexus_stats_detection::detection::ShiryaevRoberts;

// Known: pre-change mean 0.5, post-change mean 1.2, noise sigma 0.3.
let mut sr = ShiryaevRoberts::builder()
    .mu_before(0.5)
    .mu_after(1.2)
    .sigma(0.3)
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
    pub fn update(&mut self, sample: f64) -> Result<Option<Condition>, DataError>;
    pub fn z_score(&self) -> Option<f64>;
    // more
}
```

### Example — CPU load outlier

```rust
use nexus_stats_detection::detection::AdaptiveThreshold;
use nexus_stats_core::Condition;

let mut at = AdaptiveThreshold::builder()
    .halflife(500.0)
    .warning_sigma(2.0)
    .critical_sigma(4.0)
    .build()
    .unwrap();

for &load in &cpu_samples {
    match at.update(load).unwrap() {
        Some(Condition::Warning) => log_warn("cpu anomaly"),
        Some(Condition::Critical) => page_oncall("cpu spike"),
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

Maintains streaming estimates of the median and MAD (median absolute deviation). Computes `z = 0.6745 * (x - median) / MAD`. The factor `0.6745` makes MAD ≈ stddev under Gaussian data, so the score reads in standard-deviation units regardless of the data's actual distribution.

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

Internally maintains a Holt-style level + trend estimate. Fires when the `forecast(h)` function exceeds a threshold — i.e. when you're projected to cross a limit within `h` samples.

### When to use it

- **SLO degradation warnings.** "Latency is increasing — will cross SLO in 30s, page now."
- **Capacity forecasting.** Utilization climbing toward 100%.
- **Anywhere the rate-of-change matters more than the current value.**

### API

```rust
impl TrendAlert {
    pub fn builder() -> TrendAlertBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<Condition>, DataError>;
    // level(), trend(), forecast(steps)
}
```

### Example — SLO degradation

```rust
use nexus_stats_detection::detection::TrendAlert;
use nexus_stats_core::Condition;

let mut alert = TrendAlert::builder()
    .alpha(0.3)
    .beta(0.05)
    .forecast_horizon(300) // 300 samples ahead
    .warning_threshold(180.0)
    .critical_threshold(200.0)
    .build()
    .unwrap();

for &latency in &stream {
    if let Some(Condition::Critical) = alert.update(latency).unwrap() {
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

Multiple thresholded "gates" feeding a single state machine. Typically configured with `Warning` and `Critical` levels that each have their own hysteresis and debounce. Emits state *transitions* (`None | Warning | Critical`) rather than per-sample scores.

### When to use it

- **Composite alerts** where "warning" and "critical" need separate debouncing, separate hysteresis, or separate thresholds.
- **Dashboards** that distinguish "degraded" from "failing".

### API

```rust
impl MultiGate {
    pub fn builder() -> MultiGateBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<Condition>, DataError>;
}
```

Configure gates via the builder; see source for the exact parameter set.

---

## Cross-references

- CUSUM and DistributionShift: [`nexus-stats-core::detection`](../../nexus-stats-core/docs/detection.md).
- Smoothing before detection: [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).
- `Condition` and `Direction` enums: `nexus_stats_core::{Condition, Direction}`.
