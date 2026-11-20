# Statistics

Streaming, fixed-memory, O(1)-per-update statistical primitives. Module path: `nexus_stats_core::statistics`.

## At a glance

| Type | What it computes | Memory |
|------|------------------|--------|
| `Welford` | Mean, variance, stddev | 3 words |
| `Moments` | Mean, variance, skewness, kurtosis (Pebay 2008) | 5 words |
| `EwmaVar` | Exponentially-weighted mean and unbiased variance (pandas `ewm` defaults) | small, fixed |
| `Covariance` | Online covariance + Pearson correlation | 5 words |
| `CovarianceMatrix` | N-dimensional covariance matrix | O(N²) |
| `HarmonicMean` | Harmonic mean | 2 words |
| `Percentile` | Online percentile (P² algorithm) | small, fixed |
| `BucketAccumulator` | Bar-style OHLC / VWAP aggregation | small, fixed |
| `Amihud` | Amihud illiquidity measure (EW) | small |
| `RollSpread` | Roll's implicit bid-ask spread | small |
| `BipowerVariation` | Realized variance, bipower variation, jump share | small |
| `TwoScaleRv` | Noise-robust realized variance (two time scales) | alloc, `k` prices |
| `HitRate` | Rolling success rate over labels | small |
| `HalfLife` | Mean-reversion half-life from an AR(1) fit | small |
| `Hurst` | Hurst exponent by R/S analysis | alloc, windowed |
| `VarianceRatio` | Lo-MacKinlay variance ratio (mean-reversion test) | alloc, `q` values |
| `Lpm` | Lower partial moments (downside risk, semivariance) | 5 words |
| `Cvar` | Conditional Value at Risk (expected shortfall) | small, fixed |

## `update` and `checked_update`

Two ways in, after the standard library's `+` and `checked_add`:

- `update` is unchecked. It does no validation, returns its reading directly, and follows IEEE 754: a NaN or an infinity makes the readings NaN from then on, and a value large enough for its square to overflow makes them infinite or NaN.
- `checked_update` validates first and returns a `Result`. It refuses NaN, infinity, a magnitude above `INPUT_LIMIT` (`1e120`; `INPUT_LIMIT_FOURTH_MOMENT`, `1e60`, for `Moments`), and anything outside the type's domain, with a `DataError`, and changes nothing. Fed only through it, no reading is ever NaN.

A type that has taken bad input through `update` is put right with `reset()`. When to call it is the application's decision.

```rust
use nexus_stats_core::statistics::Welford;
use nexus_stats_core::{DataError, INPUT_LIMIT};

// `update`: unchecked. A NaN stays in the state until `reset`.
let mut w = Welford::new();
w.update(1.0);
w.update(f64::NAN);
assert!(w.mean().unwrap().is_nan());
w.reset();
w.update(1.0);
assert_eq!(w.mean(), Some(1.0));

// `checked_update`: bad input is refused and the state is untouched.
let mut w = Welford::new();
assert_eq!(w.checked_update(f64::NAN), Err(DataError::NotANumber));
assert_eq!(w.checked_update(1e200), Err(DataError::OutOfRange));
assert_eq!(w.count(), 0);
assert!(w.checked_update(INPUT_LIMIT).is_ok());
```

Every type on this page except `Percentile` and `Cvar` has the pair. (Those two, and the rest of the library, still validate in `update` and return a `Result` from it; they are being converted cluster by cluster.)

---

## Welford — Online mean / variance / stddev

Numerically stable single-pass computation of sample mean and variance using Welford's algorithm. No catastrophic cancellation. Supports merging partial results via Chan's algorithm for parallel aggregation.

```rust
use nexus_stats_core::statistics::Welford;

let mut w = Welford::new();
for latency_us in [120.0, 118.0, 125.0, 130.0, 119.0] {
    w.update(latency_us);
}

assert!((w.mean().unwrap() - 122.4).abs() < 1e-9);
assert!((w.variance().unwrap() - 25.3).abs() < 1e-9); // sample variance (n-1)
assert!((w.std_dev().unwrap() - 25.3f64.sqrt()).abs() < 1e-9);
assert_eq!(w.count(), 5);
```

**Use for:** running mean/variance/stddev on any float stream. The default first choice when you need "how noisy is this?".

**Caveats:** `variance()` is the sample variance (divisor `n-1`); `population_variance()` divides by `n`. Primed after 2 samples.

---

## Moments — Skewness and kurtosis

Extends Welford to third and fourth central moments using Pébay's online formulas. Numerically stable, single pass.

```rust
use nexus_stats_core::statistics::Moments;

let mut m = Moments::new();
// Mostly small moves, one large loss: a long left tail.
let returns = [0.01, -0.01, 0.02, -0.02, 0.01, 0.0, -0.01, 0.01, -0.30, 0.02];
for r in returns { m.update(r); }

let skew   = m.skewness().unwrap();         // asymmetry, 0 = symmetric
let kurt   = m.kurtosis().unwrap();         // classical (normal = 3)
let excess = m.excess_kurtosis().unwrap();  // normal = 0
assert!(skew < -2.0);                       // skewed left by the loss
assert!(excess > 3.0);                      // heavy tail
assert!((kurt - excess - 3.0).abs() < 1e-12);
```

**Use for:** return distributions, latency distribution shape, detecting fat tails. `excess_kurtosis > 3` is a serious tail warning.

**Caveats:** higher moments need more samples to stabilize. Don't trust skewness below ~30 samples, kurtosis below ~100. Skewness and kurtosis are `None` for constant data, and for data whose spread is too small for the higher moments to be resolved (under about `1e-97` and `1e-73`).

---

## EwmaVar — Exponentially-weighted variance

Exponentially weighted mean and variance. Adapts to drift, unlike `Welford`.

The estimator is the one pandas computes by default, `ewm(alpha=a).mean()` and `ewm(alpha=a).var()`: sample `i` of `n` has weight `(1 - alpha)^(n - i)`, and the variance is the unbiased weighted variance. It is unbiased from the second sample on, with no warm-up period in which it reads low. `update` returns the reading as a `MeanVariance { mean, variance }`, and `last()` re-reads it.

```rust
use nexus_stats_core::statistics::EwmaVar;

let mut ew = EwmaVar::builder().alpha(0.5).build().unwrap();
assert_eq!(ew.update(0.0), None); // one sample has no variance
let reading = ew.update(2.0).unwrap();
// Two samples, weights 0.5 and 1: mean 4/3, unbiased variance 2.
assert!((reading.mean - 4.0 / 3.0).abs() < 1e-12);
assert!((reading.variance - 2.0).abs() < 1e-12);
assert_eq!(ew.last(), Some(reading));
```

`reading.std_dev()` is the square root of the variance (needs `std` or `libm`). Set the weight with `alpha(a)`, `halflife(h)` or `span(n)`.

**Seeding:** `seed(mean, variance)` starts the tracker as if it had already converged there. Readings are available at once, `count()` still counts only samples fed, and `reset()` returns to the seed.

**Use for:** adaptive z-scores, volatility bands on a drifting mean, anywhere you want `Welford` but with decay.

**Cost:** the weight totals converge within about `36 / alpha` samples. Until then an update refreshes two reciprocals; after that it is the same work as a plain exponential recursion.

---

## Covariance — Online covariance and correlation

Tracks `cov(X, Y)` and `corr(X, Y)` in one pass.

```rust
use nexus_stats_core::statistics::Covariance;

let mut c = Covariance::new();
// The ask moves twice as far as the bid, in the same direction.
for bid_change in [1.0, -2.0, 0.5, 3.0, -1.5] {
    c.update(bid_change, 2.0 * bid_change);
}

let cov  = c.covariance().unwrap();
let corr = c.correlation().unwrap();
assert!((cov - 2.0 * c.variance_x().unwrap()).abs() < 1e-12);
assert!((corr - 1.0).abs() < 1e-12);
```

`correlation()` is in `[-1, 1]`, and `None` when either side is constant (the correlation is then undefined).

**Use for:** pairs trading, book side cohesion, any two-stream relationship measurement.

---

## CovarianceMatrix — N-dim covariance matrix

Exponentially weighted covariance matrix of observation vectors of a builder-configured dimension. The weight (`alpha` or `halflife`) is required.

```rust
use nexus_stats_core::statistics::CovarianceMatrix;

let mut cov = CovarianceMatrix::builder().dim(3).alpha(0.05).build().unwrap();
for i in 0..500 {
    let x = f64::from(i % 7);
    // Second component tracks the first; third moves against it.
    cov.update(&[x, 2.0 * x, -x]).unwrap();  // &[f64] of length 3
}
assert!(cov.correlation(0, 1).unwrap() > 0.999);
assert!(cov.correlation(0, 2).unwrap() < -0.999);
assert!(cov.variance(1).unwrap() > cov.variance(0).unwrap());
// The whole matrix, row-major: `cov.as_matrix()`, with `cov.dim()` per side.
assert_eq!(cov.as_matrix().len(), 9);
```

**Use for:** multi-asset portfolios, multi-factor models, PCA inputs.

**Caveats:** O(N²) memory and O(N²) per update. Fine for small N (2-20), overkill for N > 50. Requires `alloc`.

---

## HarmonicMean — Correct average of rates

`H = n / sum(1/x_i)`. The right mean for ratios, rates, and latencies when you care about throughput semantics.

```rust
use nexus_stats_core::statistics::HarmonicMean;

let mut h = HarmonicMean::new();
// Two legs of equal length at 60 and 30: the effective rate is 40, not 45.
for rate in [60.0, 30.0] { h.update(rate); }
assert!((h.mean().unwrap() - 40.0).abs() < 1e-12);
```

**Use for:** "what's the effective throughput across these links?" (classical HM use case). Rarely the right answer for latency — arithmetic mean over latency is usually what you want.

**Caveats:** requires all inputs strictly positive. Rejects zero and negatives.

---

## Percentile — Online percentile (P²)

The P² algorithm: maintains 5 markers that track a target percentile in O(1) memory. No window, no allocation, adapts over time.

```rust
use nexus_stats_core::statistics::Percentile;

let mut p99 = Percentile::new(0.99).unwrap();
// 1..=1000, shuffled by a fixed stride.
for i in 0..1000u32 {
    p99.update(f64::from(i * 617 % 1000 + 1)).unwrap();
}

assert!(p99.is_primed());
let estimate = p99.percentile().unwrap();
assert!((estimate - 990.0).abs() < 10.0);
```

**Use for:** p50/p95/p99/p999 estimation on a continuous stream. No storage costs.

**Caveats:** approximate. `percentile()` is `None` until `min_samples()` observations have been fed: 5 for central percentiles, `1 / (p (1 - p))` for extreme ones (101 for p99, about 1000 for p999). For exact percentiles on bounded data, use histograms.

---

## BucketAccumulator — Bar-style aggregation

Accumulates samples into buckets and emits a `BucketSummary` (sum, count, mean, first, last, change) when a bucket closes. A bucket closes by count, by accumulated volume, or by elapsed ticks, according to its `BucketPolicy`.

```rust
use nexus_stats_core::statistics::{BucketAccumulator, BucketPolicy};

let mut bucket = BucketAccumulator::builder()
    .policy(BucketPolicy::Count(4))   // close a bar every 4 samples
    .build()
    .unwrap();

let mut bars = Vec::new();
for price in [10.0, 12.0, 11.0, 13.0, 20.0, 18.0, 19.0, 21.0, 30.0] {
    // `update` is the method for the Count policy.
    if let Some(summary) = bucket.update(price).unwrap() {
        bars.push(summary);
    }
}
assert_eq!(bars.len(), 2);
assert_eq!((bars[0].first(), bars[0].last(), bars[0].mean()), (10.0, 13.0, 11.5));
assert_eq!(bars[1].change(), 1.0); // last - first: 21 - 20
// The ninth price has opened a third bar, which has not closed yet.
```

**Each policy has its own update method**, and calling a different one feeds the bucket without ever closing it: `update(value)` for `Count`, `update_volume(value, volume)` for `Volume`, `update_at(timestamp, value)` for `Ticks`.

**Use for:** building minute bars, hour bars, volume bars from a tick stream without allocating.

---

## Amihud — Illiquidity estimator

Amihud's (2002) illiquidity measure is the average over periods of `|return| / dollar volume`: the price move per unit of money traded. This type keeps an exponentially weighted average of the per-period ratio. Higher means less liquid.

```rust
use nexus_stats_core::statistics::Amihud;

let mut amihud = Amihud::builder().alpha(0.5).build().unwrap();

// A 1% move on $1M traded, either direction.
assert_eq!(amihud.update(-0.01, 1_000_000.0), Some(1e-8));
// A 2% move on $1M: the ratio doubles and the average moves halfway.
let illiq = amihud.update(0.02, 1_000_000.0).unwrap();
assert!((illiq - 1.5e-8).abs() < 1e-20);
// No trading: the period is skipped and the reading is unchanged.
assert_eq!(amihud.update(0.05, 0.0), Some(illiq));
assert_eq!(amihud.count(), 2);
```

The return may have either sign; its absolute value is used. Periods with zero dollar volume are left out, as in the original measure.

**Use for:** liquidity monitoring on crypto venues. Cross-venue comparison. Signal input to smart order routing.

---

## RollSpread: implicit bid-ask spread

Roll's (1984) estimator. A trade prints half a spread above or below the efficient price, on a random side, which makes consecutive price changes negatively correlated: `spread = 2 * sqrt(-Cov(dp_t, dp_{t-1}))`. The covariance is exponentially weighted and normalized by the weight accumulated, so it does not read low while warming up.

```rust
use nexus_stats_core::statistics::RollSpread;

let mut rs = RollSpread::builder().alpha(0.05).build().unwrap();

// Trades at a fixed mid of 100 with a spread of 0.02, on a random side.
let mut state = 7u64;
let mut estimate = None;
for _ in 0..5_000 {
    state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    let side = if state >> 63 == 0 { 0.01 } else { -0.01 };
    estimate = rs.update(100.0 + side);
}
let estimate = estimate.unwrap();
assert!(estimate.model_fits());
assert!((estimate.spread - 0.02).abs() < 0.006);
```

`update` returns a `RollEstimate { spread, autocovariance }`. When the autocovariance is not negative the data does not show the bounce the model assumes, and the spread is reported as 0, the usual convention for this estimator. `model_fits()` is `false` when the autocovariance is positive (consecutive changes continue, as in a trending market), which tells that case from a price that simply has not moved (zero autocovariance, zero spread).

**Use for:** an effective-spread estimate from trade prices alone, when quotes are unavailable or untrusted.

**Caveats:** requires `std` or `libm`. Assumes price changes have no drift over the weighting horizon.

---

## BipowerVariation: realized variance and jumps

Barndorff-Nielsen and Shephard (2004). Over the price changes `r_i` since the last `reset()`:

- realized variance `RV = sum r_i^2` measures all of the path's variation, jumps included;
- bipower variation `BV = (pi / 2) * sum |r_i| * |r_{i-1}|` measures only the continuous part.

`RV - BV` estimates the variation that came from jumps.

```rust
use nexus_stats_core::statistics::BipowerVariation;

let mut bv = BipowerVariation::builder().min_samples(3).build().unwrap();
// Changes of +1, -1, +1, +1 and then a jump of +10.
let mut reading = None;
for price in [100.0, 101.0, 100.0, 101.0, 102.0, 112.0] {
    reading = bv.update(price);
}
let r = reading.unwrap();
assert_eq!(r.realized_variance, 104.0);  // 1 + 1 + 1 + 1 + 100
let expected_bv = core::f64::consts::FRAC_PI_2 * 13.0; // 1 + 1 + 1 + 10
assert!((r.bipower_variation - expected_bv).abs() < 1e-12);
// Most of the variation is the jump.
assert!(r.jump_ratio().unwrap() > 0.8);
```

The reading is a `JumpDecomposition { realized_variance, bipower_variation }` with `jump_variation()` and `jump_ratio()`.

**These are totals over the period**, as in the literature: they grow with the number of prices fed. Call `reset()` at the start of each period (a session, a day, a bar) and read at its end. Divide by `count() - 1` for a per-step figure.

**Use for:** separating jump risk from diffusive volatility; flagging sessions dominated by a few large moves.

---

## TwoScaleRv: noise-robust realized variance

Zhang, Mykland and Aït-Sahalia (2005). At high frequency the realized variance of every tick measures mostly microstructure noise (bid-ask bounce). Two-scale realized variance takes the average realized variance of `K`-tick changes, which noise inflates much less, and subtracts the remaining noise using the all-tick figure, with the paper's small-sample refinement.

```rust
use nexus_stats_core::statistics::TwoScaleRv;

let mut tsrv = TwoScaleRv::builder().k(5).build().unwrap();

// A price that only bounces between bid and ask: all noise, no
// movement in the efficient price.
let mut estimate = None;
for i in 0..2_000 {
    let bounce = if i % 2 == 0 { 0.01 } else { -0.01 };
    estimate = tsrv.update(100.0 + bounce);
}
let e = estimate.unwrap();
// The all-tick realized variance is all bounce...
assert!(e.realized_variance > 0.79);
// ...and the two-scale estimate removes it.
assert!(e.two_scale_variance < 0.01 * e.realized_variance);
```

The reading is a `TwoScaleEstimate { two_scale_variance, realized_variance, noise_variance }` with `two_scale_volatility()`. `realized_variance` is the plain all-tick sum of squares, the same quantity `BipowerVariation` reports under that name; `two_scale_variance` is the noise-corrected estimate. Both are totals since the last `reset()`.

**Use for:** volatility from tick data, where a naive realized variance is dominated by the spread.

**Caveats:** requires `alloc` and `std` or `libm`. `k` is typically 5 to 20.

---

## HitRate — Rolling success rate

Fraction of predictions whose direction matched the outcome: a hit is when the predicted and the realized value have the same sign. Tracks the all-time rate and an exponentially weighted one.

```rust
use nexus_stats_core::statistics::HitRate;

let mut hr = HitRate::builder().alpha(0.5).build().unwrap();
hr.update(1.0, 0.4);   // predicted up, went up: hit
hr.update(-1.0, 0.2);  // predicted down, went up: miss
hr.update(-0.5, -3.0); // predicted down, went down: hit
assert!((hr.hit_rate().unwrap() - 2.0 / 3.0).abs() < 1e-12);
// Weighted toward the recent outcomes: 1, then 0.5, then 0.75.
assert!((hr.ew_hit_rate().unwrap() - 0.75).abs() < 1e-12);
```

A zero on either side counts as a miss.

---

## HalfLife — Mean-reversion half-life

Fits `x_t = c + phi * x_{t-1}` by least squares over all consecutive pairs seen. A deviation from the mean shrinks by a factor of `phi` each step, so it halves in `-ln 2 / ln phi` steps when `0 < phi < 1`.

```rust
use nexus_stats_core::statistics::{HalfLife, Reversion};

// Each value is half the last: phi = 0.5, a half-life of one step.
let mut hl = HalfLife::new();
for x in [8.0, 4.0, 2.0, 1.0] {
    hl.update(x);
}
assert_eq!(hl.ar1_coefficient(), Some(0.5));
let Some(Reversion::Reverting { half_life }) = hl.reversion() else {
    panic!("expected a reverting series");
};
assert!((half_life - 1.0).abs() < 1e-12);

// Each value is double the last: phi = 2, so it never reverts.
let mut hl = HalfLife::new();
for x in [1.0, 2.0, 4.0, 8.0] {
    hl.update(x);
}
assert_eq!(hl.reversion(), Some(Reversion::NotReverting));
```

`reversion()` names the three regimes instead of overloading one number:

| `phi` | `Reversion` |
|---|---|
| `0 <= phi < 1` | `Reverting { half_life }` |
| `phi >= 1` | `NotReverting` (a random walk or an explosive series) |
| `phi < 0` | `Oscillating` (each step overshoots the mean) |

It is `None` until three values have been fed, and for a constant series, where the fit is undefined.

**Use for:** stat arb, pairs trading calibration. If the half-life is longer than your holding period, the trade is not mean-reverting fast enough.

**Caveats:** all-time, with `reset()`. Requires `std` or `libm`.

---

## Hurst — Hurst exponent

The Hurst exponent `H` of a series of **increments** (returns, changes; not price levels): 0.5 for independent increments, above when moves persist, below when they reverse.

Computed by standard R/S analysis (Hurst, 1951; Mandelbrot and Wallis, 1969) over the last `window_size` samples: average the rescaled range `R / S` over blocks of length `n`, for `n = N, N/2, N/4, ...` (halving while `n` is at least 8), and take the slope of `ln(R/S)` against `ln(n)`. A window stuck on one value has no exponent (`None`).

```rust
use nexus_stats_core::statistics::Hurst;

let mut h = Hurst::builder().window_size(256).build().unwrap();

// Returns that alternate in sign: every move reverses.
for i in 0..256 {
    h.update(if i % 2 == 0 { 0.01 } else { -0.01 });
}
// The range never grows with the block length, so the slope is zero.
assert!(h.hurst().unwrap().abs() < 1e-9);
```

**Known bias:** for short blocks `R / S` grows faster than its asymptotic law, so on independent data the slope reads above 0.5: about 0.6 for windows of a few hundred samples, falling slowly toward 0.5 as the window grows. This is a property of the method. Compare a reading with what the same window gives on shuffled or simulated independent data, not with 0.5.

**Use for:** regime detection, signal-vs-noise classification on slow timescales.

**Caveats:** requires `alloc` and `std` or `libm`. `update` is O(1); `hurst()` is O(window * log(window)), a per-bar computation. The window must be at least 32.

---

## VarianceRatio — Lo-MacKinlay variance ratio test

`VR(q) = Var(q-period change) / (q * Var(1-period change))` (Lo and MacKinlay, 1988). Under a random walk VR = 1; below 1 indicates mean reversion, above 1 momentum.

Feed values (prices or levels). Both variances are exponentially weighted. The q-period changes overlap and are therefore correlated, which makes a naive ratio read low; the ratio is corrected for that so it averages 1 on a random walk.

```rust
use nexus_stats_core::statistics::VarianceRatio;

let mut vr = VarianceRatio::builder().q(5).alpha(0.05).build().unwrap();

// A series that alternates around a level: every change reverses.
let mut ratio = None;
for i in 0..500 {
    let value = 100.0 + if i % 2 == 0 { 5.0 } else { -5.0 };
    ratio = vr.update(value);
}
// One-step and five-step changes have the same size, so VR(5) is 1/5
// before the overlap correction and a little above it after.
let ratio = ratio.unwrap();
assert!(ratio > 0.2 && ratio < 0.23, "{ratio}");
```

**Choosing alpha:** the weights span roughly `2 / alpha` changes. That must be at least `q` (the builder rejects `alpha > 2 / q`) and should be several times `q`. A single reading is noisy; compare it with 1 using a margin.

**Use for:** quantitative mean-reversion testing, complement to `HalfLife` and `Hurst`.

**Caveats:** requires `alloc`. `None` until `2 * q + 1` values have been fed, and for a constant series or an exact straight line. `update` is O(1) once the weights settle (about `36 / alpha` values) and O(q) before that.

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
assert_eq!(lpm.lpm(), Some(2.0));  // (9 + 1 + 0 + 0 + 0) / 5

// Shortfall probability (order 0)
let mut sp = Lpm::builder().target(50.0).order(0).build().unwrap();
for i in 0..100 { sp.update(f64::from(i)); }
assert_eq!(sp.lpm(), Some(0.5));   // 0..=49 are below 50
```

**Use for:** downside risk measurement, Sortino ratio inputs, tail-sensitive risk metrics. Semivariance is the most common application — use the `semivariance(target)` convenience constructor.

**Caveats:** orders run from 0 to 16; orders of 3 and above use a multiply loop.

---

## Cvar — Conditional Value at Risk (Expected Shortfall)

Streaming CVaR: the average loss in the worst α-tail, estimated online using a P² percentile estimator for VaR.

```rust
use nexus_stats_core::statistics::Cvar;

let mut cvar = Cvar::builder().alpha(0.05).build().unwrap();
for i in 0..2000u32 {
    cvar.update(f64::from(i * 617 % 1000 + 1)).unwrap(); // 1..=1000, shuffled
}
assert!(cvar.is_primed());
let var = cvar.var().unwrap();   // 5th percentile estimate, about 50
let es  = cvar.cvar().unwrap();  // mean of the samples at or below it, about 25
assert!((var - 50.0).abs() < 10.0);
assert!(es < var && (es - 25.0).abs() < 10.0);
```

The tail is the **low** end: `alpha(0.05)` is the worst 5% when lower values are worse (returns, P&L). For a quantity where higher is worse, feed its negative.

**Use for:** tail risk measurement, position sizing, drawdown budgeting. More informative than VaR alone — tells you how bad the bad cases are, not just where the threshold is.

**Caveats:** tail tracking starts after P² primes (~5 samples). During P² convergence the VaR estimate is evolving, so early tail classifications may be slightly off. Not windowed — streaming with a priming phase. For windowed tail risk, compose with a ring buffer upstream.

---

## Cross-references

- Smoothers on top of statistics: [`smoothing.md`](smoothing.md), [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).
- Change detection built on statistics: [`detection.md`](detection.md), [`nexus-stats-detection`](../../nexus-stats-detection/docs/INDEX.md).
- Regression and Kalman estimators: [`nexus-stats-regression`](../../nexus-stats-regression/docs/INDEX.md).
