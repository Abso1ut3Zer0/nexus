# Trading Systems

How to use nexus-stats for market making, signal analysis, execution
quality, and regime detection. Maps trading problems to types.

---

## Market Microstructure

### Measure price impact of order flow

**Type:** `KyleLambda` (nexus-stats-regression)

Regresses price changes against signed order flow. Lambda = how much
the price moves per unit of informed volume.

```rust
use nexus_stats_regression::regression::KyleLambda;

let mut kyle = KyleLambda::builder()
    .alpha(0.02)  // slow decay — impact is structural
    .build()?;

// On each trade or sampling interval:
kyle.update(signed_volume, price_change)?;

if let Some(lambda) = kyle.lambda() {
    // lambda > 0: positive price impact per unit volume
    // Use for: spread floor (>= 2 × lambda × expected fill size)
    // Use for: trade subtraction ratio in book aggregation
}
```

### Measure illiquidity

**Type:** `Amihud` (nexus-stats-core)

`|return| / dollar_volume` — higher means more illiquid, wider spreads
needed. Simpler than Kyle's lambda (no regression, just a ratio).

```rust
use nexus_stats_core::statistics::Amihud;

let mut illiq = Amihud::builder()
    .halflife(100.0)
    .build()?;

illiq.update(return_abs, dollar_volume)?;

// Cross-venue comparison: which venue is most liquid right now?
let venue_a_illiq = venue_a_amihud.illiq();
let venue_b_illiq = venue_b_amihud.illiq();
```

### Build time/volume/count bars from tick data

**Type:** `BucketAccumulator` (nexus-stats-core)

Accumulates observations into buckets closed by count, volume, or time.
The bucket summary (sum, mean, count, change) feeds into downstream
analysis.

```rust
use nexus_stats_core::statistics::{BucketAccumulator, BucketPolicy};

// Volume bars: close after $1M notional
let mut bars = BucketAccumulator::builder()
    .policy(BucketPolicy::Volume(1_000_000.0))
    .build()
    .unwrap();

// On each trade:
if let Some(bar) = bars.update_volume(price, notional_volume)? {
    // bar.mean()   — VWAP of the bar
    // bar.change() — price change over the bar
    // bar.count()  — number of trades in the bar
    // Feed into LaggedPredictor, Hurst, VarianceRatio, etc.
}
```

---

## Signal Analysis

### Is my signal still predictive at different horizons?

**Type:** `SignalDecayCurve` (nexus-stats-regression)

Runs `LaggedPredictor` at multiple lags simultaneously. Shows the R²
curve — how long a signal stays predictive.

```rust
use nexus_stats_regression::regression::SignalDecayCurve;

let mut decay = SignalDecayCurve::builder()
    .lags(&[1, 2, 5, 10, 20, 50])
    .halflife(200.0)
    .build()?;

// On each tick:
decay.update(our_signal, realized_outcome)?;

// Find useful horizon: where does R² drop below threshold?
if let Some(horizon) = decay.useful_horizon(0.01) {
    // Signal is predictive for `horizon` ticks
}
```

### How predictive is my estimate N ticks ahead?

**Type:** `LaggedPredictor` (nexus-stats-regression)

Was my point estimate K ticks ago correct about where the value is now?
R² = prediction quality. Slope = calibration.

```rust
use nexus_stats_regression::regression::LaggedPredictor;

// FV quality: does our fair value predict the mid 5 ticks later?
let mut fv_quality = LaggedPredictor::builder()
    .lag(5)
    .halflife(100.0)
    .build()?;

fv_quality.update(our_fv, realized_mid)?;

if let Some(slope) = fv_quality.slope() {
    // slope = 1.0 → perfectly calibrated
    // slope < 1.0 → over-predicting moves
    // slope > 1.0 → under-predicting moves
}
```

**Markout analysis:** Same type, different inputs:
```rust
// fill_price[T] predicts mid[T+K] — the core TCA metric
let mut markout = LaggedPredictor::builder()
    .lag(10)  // 10-tick markout horizon
    .halflife(500.0)
    .build()?;

markout.update(fill_price, current_mid)?;
```

### How fast does my signal mean-revert?

**Type:** `HalfLife` (nexus-stats-core)

Fits `x_t = c + phi * x_{t-1}` and reports the half-life of a deviation,
`-ln(2) / ln(phi)`.

```rust
use nexus_stats_core::statistics::{HalfLife, Reversion};

let mut hl = HalfLife::new();

// Feed spread observations (from outside, so through the checked form):
hl.checked_update(current_spread)?;

match hl.reversion() {
    Some(Reversion::Reverting { half_life }) => {
        // half_life = 6 → signal mean-reverts in ~6 ticks
        // Use for: KAMA slow period, hedger wake threshold (2× half-life)
    }
    Some(Reversion::NotReverting) => { /* trending */ }
    Some(Reversion::Oscillating) => { /* overshoots every step */ }
    None => { /* fewer than three values, or a constant series */ }
}
```

### Is the market trending or mean-reverting?

**Type:** `Hurst` (nexus-stats-core)

Rolling Hurst exponent via R/S analysis. H < 0.5 = mean-reverting,
H > 0.5 = trending, H ≈ 0.5 = random walk.

```rust
use nexus_stats_core::statistics::Hurst;

let mut hurst = Hurst::builder()
    .window_size(100)
    .build()
    .unwrap();

// Feed bar-level returns (not tick-by-tick):
hurst.update(bar_return)?;

if hurst.is_mean_reverting() {
    // Tighter spreads, mean-reversion strategies
} else if hurst.is_trending() {
    // Wider spreads, trend-following bias
}
```

**Pair with `VarianceRatio`** for confirmation — two independent
tests of the same hypothesis.

### Variance ratio test for random walk

**Type:** `VarianceRatio` (nexus-stats-core)

VR(q) = Var(q-period returns) / (q × Var(1-period returns)).
VR = 1 → random walk. VR < 1 → mean-reverting. VR > 1 → trending.

```rust
use nexus_stats_core::statistics::VarianceRatio;

let mut vr = VarianceRatio::builder()
    .q(5)            // compare 5-period vs 1-period variance
    .alpha(0.0035)   // EW forgetting factor, about a 200-sample half-life
    .build()?;

vr.update(price)?;

if let Some(ratio) = vr.variance_ratio() {
    // ratio < 1.0 → mean-reverting at 5-tick scale
}
```

Run at multiple q values (2, 5, 10, 20) for a multi-scale view.
Cheaper to compute than Hurst.

---

## Regime Detection

### Has the distribution changed?

**Type:** `DistributionShift` (nexus-stats-core)

Compares the kurtosis and skewness of each completed window with the
baseline before it. Catches regime changes that CUSUM misses (mean stays
flat, but tails get fat).

```rust
use nexus_stats_core::detection::DistributionShift;

let mut det = DistributionShift::builder()
    .fast_window(50)
    .build()?;

// `Some` once per 50 returns, on the one that completes a window.
if let Some(shift) = det.update(trade_return)? {
    if shift.excess_kurtosis > 2.0 {
        // the window just completed has much heavier tails
        // Action: widen spreads, reduce position limits
    }
    if shift.skewness < -1.0 {
        // returns skewed left (adverse selection)
        // Action: reduce passive quoting, increase aggression
    }
}
// Between windows, `det.last()` holds the most recent reading.
```

### Change detection on a running metric

**Types:** `Cusum`, `ShiryaevRoberts` (nexus-stats-core)

CUSUM detects persistent mean shifts. Shiryaev-Roberts detects transient
shifts. Use CUSUM for structural changes (regime shift), S-R for
short-lived anomalies (flash event).

---

## Execution & Performance

### Track win rate

**Type:** `HitRate` (nexus-stats-core)

Fraction of directionally correct predictions. Both cumulative and
exponentially weighted.

```rust
use nexus_stats_core::statistics::HitRate;

let mut hits = HitRate::builder()
    .halflife(100.0)
    .build()?;

// predicted_sign and realized_sign: positive or negative
hits.update(predicted_sign, realized_sign)?;

let rate = hits.ew_hit_rate();
// 50% = coin flip, 55% = meaningful edge, 60%+ = strong signal
```

### Conditional smoothing

**Type:** `ConditionalEma` (nexus-stats-smoothing)

EMA that only updates when a condition holds. "Mean markout when VPIN
is high" vs "when VPIN is low."

```rust
use nexus_stats_smoothing::ConditionalEma;

let mut high_vpin_markout = ConditionalEma::builder()
    .halflife(50.0)
    .build()?;

let mut low_vpin_markout = ConditionalEma::builder()
    .halflife(50.0)
    .build()?;

// On each fill:
high_vpin_markout.update(markout, vpin > 0.5)?;
low_vpin_markout.update(markout, vpin <= 0.5)?;

// Discover: overall markout is -1bps (looks fine) but
// high_vpin_markout = -8bps (terrible), low_vpin = +2bps (great)
```

---

## Composition Patterns

### Bucketed prediction

Feed `BucketAccumulator` summaries into `LaggedPredictor` with lag=1:

```rust
let mut bars = BucketAccumulator::builder()
    .policy(BucketPolicy::Count(50))
    .build()
    .unwrap();

let mut predictor = LaggedPredictor::builder()
    .lag(1)
    .halflife(100.0)
    .build()?;

// On each tick:
if let Some(bar) = bars.update(tick_count as f64)? {
    // Does this bar's tick count predict next bar's volume?
    predictor.update(bar.sum(), realized_volume)?;
}
```

### Confirm mean-reversion with two tests

```rust
// Hurst: structural, long-window
let trending = hurst.is_trending();

// Variance ratio: fast, multi-scale
let mean_reverting = vr.variance_ratio().map_or(false, |r| r < 0.95);

if !trending && mean_reverting {
    // High confidence: market is mean-reverting at this scale
}
```

### Signal quality dashboard

```rust
// For each signal in your pipeline:
let r2 = lagged.r_squared();          // prediction power
let slope = lagged.slope();            // calibration
let hit = hits.ew_hit_rate();          // directional accuracy
let reversion = hl.reversion();        // signal persistence
let horizon = decay.useful_horizon(0.01);  // predictive horizon
```

---

## Quick Reference

| Use Case | Type | Crate |
|----------|------|-------|
| Market impact | `KyleLambda` | regression |
| Illiquidity | `Amihud` | core |
| Bar construction | `BucketAccumulator` | core |
| Signal decay curve | `SignalDecayCurve` | regression |
| Lagged prediction / markout | `LaggedPredictor` | regression |
| Mean-reversion speed | `HalfLife` | core |
| Trending vs mean-reverting | `Hurst` | core |
| Random walk test | `VarianceRatio` | core |
| Distribution change | `DistributionShift` | core/detection |
| Win rate | `HitRate` | core |
| Conditional smoothing | `ConditionalEma` | smoothing |
| Mean shift detection | `Cusum` | core |
| Transient anomaly detection | `ShiryaevRoberts` | core |
