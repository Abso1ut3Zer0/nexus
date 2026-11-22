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

The average of `|return| / dollar_volume` (Amihud, 2002): higher means
more illiquid, wider spreads needed. Simpler than Kyle's lambda (no regression, just a ratio).

```rust
use nexus_stats_core::statistics::Amihud;

let mut illiq = Amihud::builder()
    .halflife(100.0)
    .build()?;

// The period's return, signed or not; a zero-volume period is left out.
illiq.update(period_return, dollar_volume);

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

Hurst exponent of the price series by rescaled-range analysis. H < 0.5 is
mean-reverting, H > 0.5 trending, H near 0.5 a random walk.

```rust
use nexus_stats_core::statistics::Hurst;

let mut hurst = Hurst::builder().window(1024).build()?;

// Feed prices; the type differences their logarithms itself.
hurst.update(bar_close);

// Read per bar: the exponent is recomputed over the window.
if let Some(h) = hurst.exponent() {
    // At this window the estimate spreads about 0.04 around 0.5 on a
    // random walk, so leave a margin before calling a regime.
    if h < 0.42 {
        // Mean-reverting: tighter spreads, reversion strategies
    } else if h > 0.58 {
        // Trending: wider spreads, trend-following bias
    }
}
```

**Pair with `VarianceRatio`** for confirmation: two independent tests of
the same hypothesis.

### Variance ratio test for random walk

**Type:** `VarianceRatio` (nexus-stats-core)

VR(q) = Var(q-period returns) / (q × Var(1-period returns)), with Lo and
MacKinlay's test statistic. VR = 1 is a random walk, below 1
mean-reverting, above 1 trending.

```rust
use nexus_stats_core::statistics::{Resync, VarianceRatio};

let mut vr = VarianceRatio::builder()
    .q(5)          // compare 5-period with 1-period variance
    .window(2000)  // over the last 2000 returns
    .build()?;

// Cheap enough for every tick. The return value says when the running
// totals have lost digits (after a bad print, say) and a resync is due.
if let Resync::Advised { .. } = vr.update(price) {
    schedule_on_slow_path(symbol); // call vr.resync() there
}

if let Some(estimate) = vr.estimate() {
    // The ratio says which way; z says whether it could be chance.
    if estimate.z_statistic < -2.58 {
        // Mean-reverting at the 5-tick scale, at the 1% level
    }
}
```

Run at several `q` (2, 5, 10, 20) for a multi-scale view. `resync()` costs
the whole window, so do not run it for every symbol on the same bar.

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

### Track directional accuracy

**Type:** `HitRate` (nexus-stats-core)

Fraction of predictions whose sign matched the outcome (Pesaran and
Timmermann, 1992), cumulative and exponentially weighted. A zero on either
side is a miss.

```rust
use nexus_stats_core::statistics::HitRate;

let mut hits = HitRate::builder()
    .halflife(100.0)
    .build()?;

// Any values: only the signs are compared.
hits.update(predicted_return, realized_return);

let rate = hits.ew_hit_rate();
// 50% = coin flip, 55% = meaningful edge, 60%+ = strong signal
```

### Conditional smoothing

**Type:** `Ema`, one per condition, updated only when its condition holds.

"Mean markout when VPIN is high" vs "when VPIN is low."

```rust
use nexus_stats::smoothing::Ema;

let mut high_vpin_markout = Ema::builder().halflife(50.0).build()?;
let mut low_vpin_markout = Ema::builder().halflife(50.0).build()?;

// On each fill:
if vpin > 0.5 {
    high_vpin_markout.update(markout);
} else {
    low_vpin_markout.update(markout);
}

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
// Hurst: structural, long-window, read per bar
let trending = hurst.exponent().is_some_and(|h| h > 0.58);

// Variance ratio: fast, multi-scale, with a significance test
let mean_reverting = vr.estimate().is_some_and(|e| e.z_statistic < -2.58);

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
| Directional accuracy | `HitRate` | core |
| Conditional smoothing | `Ema`, updated only when the condition holds | core |
| Mean shift detection | `Cusum` | core |
| Transient anomaly detection | `ShiryaevRoberts` | core |
