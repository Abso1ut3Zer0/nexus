# Statistics

The module docs for `nexus_stats_core::statistics` list every type and say which to use, and each type's own docs give its contract. This page covers only the types whose docs have not moved there yet.

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
