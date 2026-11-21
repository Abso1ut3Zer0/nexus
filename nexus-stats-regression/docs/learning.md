# Learning — Adaptive Filters & Optimizers

Gradient-based and recursive adaptive filters. Module path: `nexus_stats_regression::learning`.

For small-dimension closed-form fits, use [`regression.md`](regression.md). For high-dimensional, streaming, possibly-drifting fits, use this module.

## API shape

All adaptive filters follow:

```rust
let mut filter = LmsFilter::builder()
    .dimensions(8)
    .learning_rate(0.01)
    .build()
    .unwrap();

let y_hat = filter.predict(&features);              // &[f64] of length 8
filter.update(&features, target).unwrap();          // or update(features, target)
let weights = filter.weights();                     // &[f64]
```

The optimizers (`OnlineGd`, `AdaGrad`, `Adam`) are slightly different — they take a gradient rather than `(features, target)`, for use with user-defined loss functions.

---

## LmsFilter — Least Mean Squares

The canonical adaptive filter. On each sample:

```
error = target - predict(features)
weights += step_size * error * features
```

Simple, cheap, works.

### When to use it

- **Channel estimation / echo cancellation / equalization.**
- **Simple predictors** where you want plain stochastic gradient descent on squared error.
- **Baseline to compare other methods against.**

### Caveats

- **Step size is sensitive.** Too big = divergence. Too small = slow convergence. Rule of thumb: `step_size < 2 / (dimensions * input_variance)`.
- **No per-feature scaling.** If features have vastly different scales, the worst-conditioned coordinate dictates step size. Use NLMS or RLS.

---

## NlmsFilter — Normalized LMS

Same as LMS, except the step is normalized by input power: `weights += (step_size / (eps + |features|²)) * error * features`. Automatically adapts step size to the input magnitude.

### When to use it

- **Input power varies over time** (bursty signals, volume changes).
- **Drop-in replacement for LMS** when you don't want to hand-tune step size.

### Caveats

- Slightly more expensive than LMS (one extra dot product per update).
- Still first-order — slower convergence than RLS for well-conditioned problems.

---

## RlsFilter — Recursive Least Squares

Maintains an explicit covariance matrix `P` of the features and does Newton-style updates. Converges in roughly `dimensions` samples for well-conditioned problems — much faster than LMS/NLMS. O(d²) per update.

### API

```rust
use nexus_stats_regression::learning::RlsFilter;

let mut rls = RlsFilter::builder()
    .dimensions(8)
    .forgetting_factor(0.99)   // 1.0 = batch, <1.0 = decay
    .max_covariance(1e4)       // resets P when trace exceeds this (auto-stability)
    .build()
    .unwrap();

rls.update(&features, target).unwrap();
let y_hat = rls.predict(&features);
```

### When to use it

- **Fast convergence needed** (few samples available).
- **Well-conditioned features.** RLS struggles when the feature correlation matrix is near-singular.
- **Stationary or slowly-drifting** relationships (forgetting_factor ~ 0.99+).

### Caveats

- O(d²) memory and per update. Don't use for d > 50 or so.
- P-matrix can diverge under drift — the `max_covariance` guard auto-resets when it does. Log when this fires.
- Requires `alloc`.

---

## HuberRegression — outlier-robust linear regression

Gradient descent on Huber loss: quadratic near the fit, linear for large residuals. Bounds the influence of any single observation.

### When to use it

- **Noisy training targets** where LMS/NLMS would be dragged by outliers.
- **Robust signal research** on real data with flakes.

### Example

```rust
use nexus_stats_regression::learning::HuberRegression;

let mut fit = HuberRegression::builder()
    .dimensions(3)
    .delta(1.5)            // Huber threshold in residual stddevs
    .learning_rate(0.01)
    .build()
    .unwrap();

for (x, y) in training {
    fit.update(&x, y).unwrap();
}
```

### Caveats

- `delta` needs to be in the scale of the residual. Track `EwmVar` on residuals and adjust.
- Slower convergence than plain LMS because outliers contribute less information.

---

## OnlineKMeans — streaming cluster assignment

Online MacQueen-style k-means. Each new point is assigned to the nearest centroid and pulls that centroid toward itself. Unlike batch k-means, there's no global refitting.

### API

```rust
use nexus_stats_regression::learning::OnlineKMeans;

let mut km = OnlineKMeans::builder()
    .dimensions(3)
    .clusters(5)
    // learning rate
    .build()
    .unwrap();

for point in stream {
    let cluster_id = km.update(&point); // returns assigned cluster
}
```

### When to use it

- **Streaming clustering.** Anomalies are points far from any centroid.
- **Regime classification.** Use the assigned cluster as a categorical regime ID.
- **Quantization.** Compress a continuous stream into a few cluster IDs.

### Caveats

- **Seed-dependent.** Different random seeds give different clusters. Fix the seed in reproducible settings.
- **Centroids drift.** Don't expect stable cluster identities over long runs.

---

## OnlineGd — plain online gradient descent

A plain SGD loop. You compute gradients in your user code and call `update(gradient)` — the optimizer applies the step with configurable learning rate.

### When to use it

- **Custom loss functions.** When LMS/NLMS/Huber don't fit, roll your own loss and feed gradients.
- **Minimal state.** OnlineGd is the simplest optimizer — no moment estimates, no per-feature adaptation.

---

## AdaGrad — adaptive per-feature learning rate

AdaGrad accumulates squared gradients per feature and divides the learning rate by `sqrt(sum_sq_grad + eps)`. Features that get big gradients end up with small effective step sizes; rarely-updated features keep large ones.

### When to use it

- **Sparse features.** Some features fire rarely and need a big step when they do.
- **Mixed feature scales.** AdaGrad is scale-robust without manual normalization.

### Caveats

- **Learning rate monotonically decreases.** AdaGrad eventually stops learning as the accumulator grows. Not suitable for long-running streams with drift. Use Adam instead.

---

## Adam — Adam / AdamW optimizer

Adam combines momentum and per-feature adaptive step sizes with bias correction. The default optimizer for most deep learning, usable here for custom online models.

### API

```rust
use nexus_stats_regression::learning::Adam;

let mut opt = Adam::builder()
    .dimensions(10)
    .learning_rate(0.001)
    .beta1(0.9)
    .beta2(0.999)
    .weight_decay(0.0)     // AdamW if > 0
    .build()
    .unwrap();

opt.step(&gradients).unwrap();
```

### When to use it

- **Custom online models.** Adam is a good default optimizer.
- **You need momentum** — e.g. noisy gradient estimates benefit from it.

### Caveats

- More state than SGD (two moment estimates per feature).
- `learning_rate` still matters — Adam isn't learning-rate-free, it's learning-rate-insensitive.

---

## Cross-references

- Closed-form alternatives: [`regression.md`](regression.md).
- State-space alternatives: [`estimation.md`](estimation.md).
