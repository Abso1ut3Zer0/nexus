# Signal Analysis

Module path: `nexus_stats_detection::signal`.

Signal-analysis primitives that answer "how does this stream relate to itself, or to another stream?". Not detectors per se — they compute quantities you feed *into* detectors and trading decisions.

---

## Autocorrelation

**Types:** `Autocorrelation`.

### What it computes

`ρ(lag) = E[(x_t - μ)(x_{t-lag} - μ)] / Var(x)` — the self-correlation at a fixed lag. Positive = trending, negative = mean-reverting, near zero = random walk.

### When to use it

- **Regime classification.** "Is the signal currently trending or reverting?"
- **Strategy selection.** Mean-reversion strategies need `ρ(1) < 0`; trend strategies need `ρ(1) > 0`.
- **Noise diagnosis.** If your smoother's output has negative `ρ(1)`, you're over-smoothing.

### API

```rust
use nexus_stats_detection::signal::Autocorrelation;

let mut ac = Autocorrelation::builder()
    .lag(1)
    .build()
    .unwrap();

for &x in &series {
    ac.update(x).unwrap();
}

let rho = ac.correlation().unwrap(); // -1.0 .. 1.0
```

### Caveats

- Single-lag estimate. For a full autocorrelation function you'd need a series of estimators at different lags.
- Sensitive to non-stationarity. Drift in the mean will bias the estimate — consider differencing first.

---

## CrossCorrelation

**Type:** `CrossCorrelation`.

### What it computes

`ρ_{xy}(lag) = E[(x_t - μ_x)(y_{t-lag} - μ_y)]` — correlation between `x_t` and a lagged version of `y`. Tells you which stream leads and by how much.

### When to use it

- **Lead-lag analysis between exchange feeds.** Does Binance lead Coinbase? By how many ticks?
- **Feature engineering.** Find the best lag to use `y_{t-k}` as a predictor of `x_t`.
- **Signal latency measurement.** If a known signal appears at lag 3, you're 3 samples behind.

### API

```rust
use nexus_stats_detection::signal::CrossCorrelation;

let mut xc = CrossCorrelation::builder()
    .lag(10)             // correlations are kept for lags 0..=10
    .build()
    .unwrap();

for (a, b) in paired_stream {
    xc.update(a, b).unwrap();
}

let lead = xc.peak_lag();            // Option<usize>: the lag with the strongest correlation
let rho = xc.correlation(3);         // Option<f64>: correlation at a given lag
```

### Caveats

- Needs both streams to be aligned in sampling rate. Misalignment biases the estimate.
- Window-based: longer window = more stable estimate, more lag to detect changes.

---

## Entropy

**Type:** `Entropy`. Requires `alloc`.

### What it computes

Shannon entropy `H = -Σ p_i log p_i` over a categorical distribution. You feed it bin indices; it tracks `p_i` as EW histogram and returns the entropy.

### When to use it

- **Diversity / concentration monitoring.** Is order flow spread across many participants or concentrated in one?
- **Feed quality.** Low entropy on a "should be uniform" stream = something is wrong.
- **Regime detection.** Sudden drop in trading diversity often precedes volatility.

### API

```rust
use nexus_stats_detection::signal::Entropy;

let mut e = Entropy::builder()
    .bins(10)
    .build()
    .unwrap();

for category in categorized_events {
    e.update(category); // bin index in 0..bins
}

let h = e.entropy();        // 0.0 .. ln(num_bins)
```

### Caveats

- You choose the bins. The shape of the result depends on your binning choice.
- For continuous inputs, pre-bin with a [`BucketAccumulator`](../../nexus-stats-core/docs/statistics.md#bucketaccumulator--bar-style-aggregation).

---

## TransferEntropy

**Type:** `TransferEntropy`. Requires `alloc`.

### What it computes

Transfer entropy from X to Y:

`TE_{X→Y} = H(Y_t | Y_{t-1}) - H(Y_t | Y_{t-1}, X_{t-1})`

— the reduction in uncertainty about `Y_t` when you know `X_{t-1}` in addition to `Y_{t-1}`. A nonlinear, information-theoretic cousin of Granger causality. TE > 0 means X "causally" drives Y in the information-flow sense.

### When to use it

- **Causal discovery in signals.** Which order book side leads?
- **Signal research.** Finding predictive features correlation misses (nonlinear dependencies).
- **Market microstructure.** Does informed trading show up in one stream before another?

### API

```rust
use nexus_stats_detection::signal::TransferEntropy;

let mut te = TransferEntropy::builder()
    .bins(5)
    .lag(1)
    .build()
    .unwrap();

for (x_bin, y_bin) in paired_binned_stream {
    te.update(x_bin, y_bin);
}

let te_xy = te.te_x_to_y(); // Option<f64>, bits; te_y_to_x() and net_flow() for the reverse and the difference
```

### Caveats

- Expensive. Histogram grows as `bins^3`. Keep bins small (3-8).
- Needs a lot of data to stabilize — noisy at low sample counts.
- Binning choice dominates. Don't over-interpret small TE values.
- Not for hot paths — use on background data or offline research.

---

## Cross-references

- `Hurst`, `HalfLife`, `VarianceRatio` — [`nexus-stats-core::statistics`](../../nexus-stats-core/docs/statistics.md) — complementary regime classifiers.
- `Covariance` — lag-0 linear relationship when nonlinear info isn't needed.
