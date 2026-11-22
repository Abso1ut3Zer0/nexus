# Statistics

Streaming, fixed-memory, O(1)-per-update statistical primitives. Module path: `nexus_stats_core::statistics`.

## At a glance

| Type | What it computes | Memory |
|------|------------------|--------|
| `Welford` | Mean, variance, stddev | 3 words |
| `Moments` | Mean, variance, skewness, kurtosis (Pebay 2008) | 5 words |
| `EwmVar` | Exponentially-weighted mean & variance | small, fixed |
| `Covariance` | Online covariance + Pearson correlation | 5 words |
| `CovarianceMatrix` | N-dimensional covariance matrix | O(N²) |
| `HarmonicMean` | Harmonic mean | 2 words |
| `Percentile` | Online percentile (P² algorithm) | small, fixed |
| `BucketAccumulator` | Bar-style OHLC / VWAP aggregation | small, fixed |
| `Amihud` | Amihud illiquidity measure (EW) | small |
| `HitRate` | Directional accuracy of a prediction (cumulative and EW) | small |
| `HalfLife` | Mean-reversion half-life estimator | small |
| `Hurst` | Hurst exponent of a price series (multi-scale R/S) | alloc, windowed |
| `VarianceRatio` | Lo-MacKinlay variance ratio and test statistic | alloc, windowed |
| `TwoScaleRv` | Realized variance with tick noise removed | alloc, small |
| `Lpm` | Lower partial moments (downside risk, semivariance) | 5 words |
| `Cvar` | Conditional Value at Risk (expected shortfall) | small, fixed |

---

## Welford — Online mean / variance / stddev

Numerically stable single-pass computation of sample mean and variance using Welford's algorithm. No catastrophic cancellation. Supports merging partial results via Chan's algorithm for parallel aggregation.

```rust
use nexus_stats_core::statistics::Welford;

let mut w = Welford::new();
for latency_us in [120.0, 118.0, 125.0, 130.0, 119.0] {
    w.update(latency_us);
}

let mean = w.mean().unwrap();        // ~ 122.4
let var  = w.variance().unwrap();    // sample variance (n-1)
let std  = w.std_dev().unwrap();
let n    = w.count();
```

`update` does not validate its input (IEEE 754, as `f64` arithmetic). `checked_update` returns a `DataError` and changes nothing for a NaN, an infinity, or a magnitude above `1e120`.

**Use for:** running mean/variance/stddev on any float stream. The default first choice when you need "how noisy is this?".

**Caveats:** sample variance (divisor `n-1`), not population. If you need population variance, compute `var * (n-1)/n` yourself. Primed after 2 samples.

---

## Moments — Skewness and kurtosis

Extends Welford to third and fourth central moments using Pébay's online formulas. Numerically stable, single pass.

```rust
use nexus_stats_core::statistics::Moments;

let mut m = Moments::new();
for r in returns { m.update(r); }

let shape  = m.shape().unwrap();
let skew   = shape.skewness;         // asymmetry, 0 = symmetric
let excess = shape.excess_kurtosis;  // normal = 0
let kurt   = shape.kurtosis();       // classical (normal = 3)
```

`shape()` is `None` with fewer than four samples, or when the data is too close to constant for a shape to be resolved. `update` does not validate; `checked_update` refuses a NaN, an infinity, or a magnitude above `1e60`.

**Use for:** return distributions, latency distribution shape, detecting fat tails. `excess_kurtosis > 3` is a serious tail warning.

**Caveats:** higher moments need more samples to stabilize. Don't trust skewness below ~30 samples, kurtosis below ~100.

---

## EwmVar — Exponentially-weighted variance

Mean and variance with exponentially decaying weights. `Welford` with decay: it follows drift, where `Welford` weighs every sample equally.

```rust
use nexus_stats_core::statistics::EwmVar;

let mut ew = EwmVar::builder()
    .halflife(100.0)
    .build()
    .unwrap();

for x in stream {
    if let Some(reading) = ew.update(x) {
        let band = reading.mean + 3.0 * reading.std_dev();
    }
}
```

`update` returns a `MeanVariance { mean, variance }` once primed; `value()` reads the same thing without feeding a sample. `checked_update` refuses NaN, infinity, and magnitudes above `1e120`.

The variance is the unbiased weighted variance, the one pandas (`ewm().var()`) and Polars (`ewm_var`) compute by default. `min_samples` is at least 2: one sample has no variance.

`seed(mean, variance)` starts it converged on those values. `reset_with_seed(mean, variance)` does the same on a live tracker.

**Use for:** adaptive z-scores, volatility bands on a drifting mean, anywhere you want `Welford` but with decay.

---

## Covariance — Online covariance and correlation

Tracks `cov(X, Y)` and `corr(X, Y)` in one pass.

```rust
use nexus_stats_core::statistics::Covariance;

let mut c = Covariance::new();
for (bid_change, ask_change) in book_updates {
    c.update(bid_change, ask_change);
}

let cov  = c.covariance().unwrap();
let corr = c.correlation().unwrap();
```

**Use for:** pairs trading, book side cohesion, any two-stream relationship measurement.

---

## CovarianceMatrix — N-dim covariance matrix

Builder-configured dimension `N`, streaming observation vectors of length `N`.

```rust
use nexus_stats_core::statistics::CovarianceMatrix;

let mut cov = CovarianceMatrix::builder().dim(3).build().unwrap();
for observation in observations {
    cov.update(&observation).unwrap();  // &[f64] of length 3
}
// query cov.covariance_matrix() / cov.correlation_matrix() etc.
```

**Use for:** multi-asset portfolios, multi-factor models, PCA inputs.

**Caveats:** O(N²) memory and O(N²) per update. Fine for small N (2-20), overkill for N > 50. Requires `alloc`.

---

## HarmonicMean — Correct average of rates

`H = n / sum(1/x_i)`. The right mean for ratios, rates, and latencies when you care about throughput semantics.

```rust
use nexus_stats_core::statistics::HarmonicMean;

let mut h = HarmonicMean::new();
for rate_mbps in throughputs { h.update(rate_mbps); }
let effective = h.mean().unwrap();
```

**Use for:** "what's the effective throughput across these links?" (classical HM use case). Rarely the right answer for latency — arithmetic mean over latency is usually what you want.

**Caveats:** defined for strictly positive inputs. `update` does not validate; `checked_update` refuses zero, negatives, NaN, infinity, and anything outside `[1e-120, 1e120]`.

---

## Percentile — Online percentile (P²)

The P² algorithm: maintains 5 markers that track a target percentile in O(1) memory. No window, no allocation, adapts over time.

```rust
use nexus_stats_core::statistics::Percentile;

let mut p99 = Percentile::new(0.99).unwrap();
for latency in latencies { p99.update(latency).unwrap(); }

if p99.is_primed() {
    let estimate = p99.percentile().unwrap();
}
```

**Use for:** p50/p95/p99/p999 estimation on a continuous stream. No storage costs.

**Caveats:** approximate. Accuracy depends on how many samples you've fed it — p50 primes at ~5 samples, p99 at ~100, p999 at ~1000. See `is_primed()`. For exact percentiles on bounded data, use histograms.

---

## BucketAccumulator — Bar-style aggregation

Accumulates samples into time-bucketed bars (OHLC, VWAP, count, sum). Emits a `BucketSummary` when the bucket rolls.

```rust
use nexus_stats_core::statistics::{BucketAccumulator, BucketPolicy};

let mut bucket = BucketAccumulator::builder()
    .policy(BucketPolicy::Count(100))   // close a bar every 100 samples
    .build()
    .unwrap();

for tick in ticks {
    if let Ok(Some(summary)) = bucket.update_volume(tick.price, tick.volume) {
        // bucket rolled, summary is the finished bar
    }
}
```

**Use for:** building minute bars, hour bars, volume bars from a tick stream without allocating.

---

## Amihud: illiquidity

The exponentially weighted average of `|return| / dollar_volume` (Amihud, 2002). Higher means less liquid: more price movement per unit of volume.

```rust
use nexus_stats_core::statistics::Amihud;
let mut a = Amihud::builder().halflife(500.0).build().unwrap();
a.update(period_return, dollar_volume);
let score = a.illiq().unwrap();
```

Pass the period's return, signed or not; its magnitude is used. A period with zero volume is left out (the ratio is undefined there), and `count()` does not advance. `checked_update` refuses NaN, infinity, a negative volume, and a ratio that overflows.

**Use for:** liquidity monitoring on crypto venues. Cross-venue comparison. Signal input to smart order routing.

---

## HitRate: directional accuracy

The fraction of predictions whose sign matched the outcome: `hit_rate()` over everything fed, `ew_hit_rate()` weighted toward recent pairs.

```rust
use nexus_stats_core::statistics::HitRate;
let mut hr = HitRate::builder().halflife(200.0).build().unwrap();
hr.update(predicted_return, realized_return);
let rate = hr.hit_rate().unwrap();
```

A hit is a prediction and an outcome that are both positive or both negative. A zero on either side is a miss. This is the hit rate of Pesaran and Timmermann (1992); the weighted rate is this crate's addition. `checked_update` refuses NaN and infinity.

It scores a signal's direction. For the rate of a yes/no event, use [`ErrorRate`](monitoring.md#errorrate), or `BetaBinomial` when you want a prior and an interval.

---

## HalfLife — Mean-reversion half-life

Fits `x_t = c + phi * x_{t-1}` by least squares, in a streaming way. A deviation from the mean shrinks by `phi` each step, so it halves in `-ln 2 / ln phi` steps.

```rust
use nexus_stats_core::statistics::{HalfLife, Reversion};
let mut hl = HalfLife::new();
for spread in spreads { hl.update(spread); }

match hl.reversion() {
    Some(Reversion::Reverting { half_life }) => println!("half life = {half_life:.1} samples"),
    Some(Reversion::NotReverting) => println!("trending (phi >= 1)"),
    Some(Reversion::Oscillating) => println!("overshoots every step (phi < 0)"),
    None => println!("fewer than three values, or a (near-)constant series"),
}
```

**Bias:** the least-squares estimate of `phi` is biased low, most visibly near 1 (the Dickey-Fuller bias): a random walk usually reads as reverting with a long half-life. The estimate is left uncorrected, as statsmodels' `AutoReg` and R's `ar` leave it. Use a unit-root test, not this, to decide whether a series reverts.

`coefficient()` returns `phi` itself. `update` does not validate; `checked_update` refuses a NaN, an infinity, or a magnitude above `1e120`.

**The formula:** `-ln 2 / ln phi` is exact for data sampled at fixed steps. A common shortcut (Chan, *Algorithmic Trading*) is `-ln 2 / (phi - 1)`. It agrees when reversion is slow and reads long when it is fast (39% long at `phi = 0.5`). To get Chan's number: `-LN_2 / (hl.coefficient()? - 1.0)`.

**Use for:** stat arb, pairs trading calibration — if half-life is longer than your holding period, the trade isn't mean-reverting fast enough.

---

## Hurst: Hurst exponent

Memory in the returns of a price series, by rescaled-range analysis:

- `H = 0.5`: independent returns, a random walk.
- `H < 0.5`: mean-reverting.
- `H > 0.5`: persistent, trending.

```rust
use nexus_stats_core::statistics::Hurst;
let mut hurst = Hurst::builder().window(1024).build().unwrap();
for price in prices { hurst.update(price); }
let h = hurst.exponent().unwrap();
```

Feed prices; the type takes the logarithm and differences them. The rescaled range `R/S` of a stretch of returns grows like `n^H` with its length, so `H` is the slope of `ln(R/S)` against `ln(n)`. `Hurst` measures `R/S` at the whole window, each half, each quarter and so on down to `smallest_window` (default 8), divides each by the value expected of independent returns (Anis and Lloyd, with Peters' term), and fits the slope. This is the procedure in Weron (2002), and matches `nolds.hurst_rs` with `fit="poly"` on the same lengths.

**Reading it.** On independent returns the estimate spreads about 0.04 around 0.5 at a window of 1024 and 0.03 at 4096; a smaller difference is noise. Below a window of about 128 it is too noisy to use. Short-lived correlation moves it too: a larger `smallest_window` looks past that, at the cost of a wider spread.

**Cost.** `update` stores the price. `exponent()` recomputes over the window: about 25,000 cycles at a window of 2048 on any x86-64 build, about 14,000 with AVX2 and FMA enabled. Read it per bar, not per tick. No incremental form exists: the mean the range is measured about moves as the window slides.

`checked_update` refuses NaN, infinity, and a price that is zero or negative. A stretch whose returns are equal to within rounding has no rescaled range and is left out.

**Use for:** regime detection, signal-vs-noise classification on slow timescales.

---

## VarianceRatio: Lo-MacKinlay variance ratio

Is the price a random walk? If returns are independent, the variance of a `q`-period return is `q` times the variance of a one-period return, and their ratio is 1. Below 1 points to mean reversion, above 1 to trending.

```rust
use nexus_stats_core::statistics::VarianceRatio;
let mut vr = VarianceRatio::builder().q(5).window(2000).build().unwrap();
for price in prices { vr.update(price); }
let estimate = vr.estimate().unwrap();
let (ratio, z) = (estimate.ratio, estimate.z_statistic);
```

This is the statistic of Lo and MacKinlay (1988) on the log price over the last `window` returns: overlapping `q`-period returns, the drift taken from the window's two ends, and their bias corrections. `z_statistic` is their heteroskedasticity-robust statistic. Both match `arch.unitroot.VarianceRatio` with its defaults (`vr` and `stat`).

**Deciding.** The ratio says which way and how far; `z` says whether that could be chance.

- `|z|` below about 2: consistent with a random walk, whatever the ratio.
- `z` above about 2: trending. Below about -2: mean-reverting. 1.96 is the 5% level, 2.58 the 1% level.
- Read on every bar, a 5% level gives a false signal about one bar in twenty. Use a higher level, or require it to hold for several reads.

**Cost and rounding.** The sums are running totals: `update` and `estimate` cost time proportional to `q`, whatever the window (about 300 and 70 cycles at `q = 8`), so a reading stays cheap when many instruments are read on the same bar. Each total keeps the digits a plain sum would drop, a window in which the price has not moved reads `None`, and the totals are measured about the window's drift as of the last `resync()`. Against an exact recompute over 20 million updates, the ratio stays within `1e-15` and the z statistic within `1e-9`, including with a price a million times off the market every half million updates. `resync()` recomputes everything from the stored prices: call it when there is time to spare (once a session), and after the window first fills if the price trends far more than it wanders.

`checked_update` refuses NaN, infinity, and a price that is zero or negative.

**Use for:** quantitative mean-reversion testing, complement to `HalfLife` and `Hurst`.

---

## TwoScaleRv: realized variance without the noise

Squared returns sampled at every tick are inflated by bid-ask bounce. Sampled every `k` ticks they are much less so. `TwoScaleRv` takes the slow-scale variance and subtracts the noise it still carries, which the fast scale measures (Zhang, Mykland and Aït-Sahalia, 2005).

```rust
use nexus_stats_core::statistics::TwoScaleRv;
let mut tsrv = TwoScaleRv::builder().k(30).build().unwrap();
for price in session_prices { tsrv.update(price); }
let estimate = tsrv.estimate().unwrap();
let (variance, noise) = (estimate.variance, estimate.noise_variance);
tsrv.reset(); // start the next period
```

Feed prices; the type works on log prices, as the paper does. The sums run from the last `reset()`, so a reading covers one period. `estimate()` returns the corrected variance (with the paper's small-sample adjustment, as R's `highfrequency` applies), the uncorrected realized variance, the variance of the noise in one observed price, and the return count. `volatility()` is the square root, taking a slightly negative estimate as zero.

The paper's guidance for `k` is the order of `n^(2/3)` for `n` returns in the period.

`checked_update` refuses NaN, infinity, and a price that is zero or negative.

**Use for:** intraday volatility from tick data; measuring how much of the tick-level variance is noise.

---

## Lpm — Lower Partial Moments (downside risk)

Measures deviations below a target threshold, raised to a configurable integer order. Fishburn (1977), Sortino & van der Meer (1991).

- **Order 0**: shortfall probability (fraction of samples below target)
- **Order 1**: expected shortfall (mean distance below target)
- **Order 2**: semivariance (variance of downside deviations only)

```rust
use nexus_stats_core::statistics::Lpm;

// Semivariance (order 2) with target = 0.0
let mut lpm = Lpm::semivariance(0.0).unwrap();
for &v in &[-3.0, -1.0, 0.0, 2.0, 5.0] {
    lpm.update(v);
}
let sv = lpm.lpm().unwrap();  // (9 + 1 + 0 + 0 + 0) / 5 = 2.0

// Shortfall probability (order 0)
let mut sp = Lpm::builder().target(50.0).order(0).build().unwrap();
for i in 0..100 { sp.update(i as f64); }
let prob = sp.lpm().unwrap();  // ~0.5
```

**Overflow:** the shortfall is raised to the order and summed directly, as R's `PerformanceAnalytics::lpm` and Boost.Accumulators' `moment` do, neither of which rescales. For a stream of any length, keep shortfalls under about `1e144` at order 2, `1e72` at order 4, `1e18` at order 16. `update` does not validate. `checked_update` refuses a NaN, an infinity, and the sample that would overflow the sum: it tests the result, which is where IEEE 754 defines overflow.

**Use for:** downside risk measurement, Sortino ratio inputs, tail-sensitive risk metrics. Semivariance is the most common application — use the `semivariance(target)` convenience constructor.

**Caveats:** orders >= 3 use a manual multiply loop (`powi` unavailable in no_std). Fine in practice — nobody runs order > 3.

---

## Cvar — Conditional Value at Risk (Expected Shortfall)

Streaming CVaR: the average loss in the worst α-tail, estimated online using a P² percentile estimator for VaR.

```rust
use nexus_stats_core::statistics::Cvar;

let mut cvar = Cvar::builder().alpha(0.05).build().unwrap();
for i in 0..2000 {
    cvar.update((i % 1000 + 1) as f64).unwrap();
}
if cvar.is_primed() {
    let var  = cvar.var().unwrap();   // 5th percentile estimate
    let es   = cvar.cvar().unwrap();  // mean of samples <= VaR
}
```

**Use for:** tail risk measurement, position sizing, drawdown budgeting. More informative than VaR alone — tells you how bad the bad cases are, not just where the threshold is.

**Caveats:** tail tracking starts after P² primes (~5 samples). During P² convergence the VaR estimate is evolving, so early tail classifications may be slightly off. Not windowed — streaming with a priming phase. For windowed tail risk, compose with a ring buffer upstream.

---

## Cross-references

- Smoothers on top of statistics: [`smoothing.md`](smoothing.md), [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).
- Change detection built on statistics: [`detection.md`](detection.md), [`nexus-stats-detection`](../../nexus-stats-detection/docs/INDEX.md).
- Regression and Kalman estimators: [`nexus-stats-regression`](../../nexus-stats-regression/docs/INDEX.md).
