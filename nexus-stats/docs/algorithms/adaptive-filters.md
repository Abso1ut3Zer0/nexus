# Adaptive Filters — Online Weight Learning

Streaming prediction with adaptive weights. "Given features x,
predict y. Update weights when the true y arrives."

| Type | Update cost | Memory | Method |
|------|-------------|--------|--------|
| `LmsFilter` | O(d) | 8d bytes | Gradient descent |
| `NlmsFilter` | O(d) | 8d bytes | Normalized gradient |
| `RlsFilter` | O(d²) | 8d²+8d bytes | Recursive least squares |
| `LogisticRegression` | O(d) | 8d bytes | SGD on cross-entropy |
| `OnlineKMeans` | O(k×d) | 8kd bytes | EMA centroid update |

All require `alloc` (heap-allocated weight vectors).
LogisticRegression additionally requires `std|libm` (sigmoid).

## LMS / NLMS — Least Mean Squares

The simplest adaptive filter. Updates weights by stepping in the
gradient direction after each prediction error.

```
LMS:  w += learning_rate × error × x
NLMS: w += (learning_rate / (x·x + ε)) × error × x
```

NLMS normalizes by input energy, making convergence independent
of input scale. Use NLMS unless you have a specific reason for LMS.

### Configuration

```rust
use nexus_stats::learning::NlmsFilter;

let mut filter = NlmsFilter::builder()
    .dimensions(3)
    .learning_rate(0.01)
    .epsilon(1e-8)
    .build()
    .unwrap();

// Predict:
let prediction = filter.predict(&[x1, x2, x3]);

// Update with true value:
filter.update(&[x1, x2, x3], actual_value);
```

### When to Use

- Fastest adaptive filter (O(d) per update)
- Good when features are well-scaled (NLMS) or when you just need something simple
- Convergence is slow but steady — good for tracking slow-changing relationships

## RLS — Recursive Least Squares

Maintains the full inverse covariance matrix. Converges much faster
than LMS because it accounts for feature correlations. The
forgetting factor λ controls how quickly old data is discounted.

```
K = P×x / (λ + x'×P×x)    — Kalman gain
w += K × error              — weight update
P = (P - K×x'×P) / λ       — covariance update (Sherman-Morrison)
```

### Configuration

```rust
use nexus_stats::learning::RlsFilter;

let mut filter = RlsFilter::builder()
    .dimensions(3)
    .forgetting_factor(0.99)    // 0.95-1.0 typical
    .initial_covariance(1000.0) // P = δ×I
    .build()
    .unwrap();

filter.update(&features, target);
let prediction = filter.predict(&features);

// Inspect learned weights:
println!("weights: {:?}", filter.weights());
```

### When to Use

- Need fast convergence (O(d²) cost is acceptable)
- Features are correlated (LMS struggles with correlated features)
- Tracking a time-varying relationship (forgetting factor adapts)
- Need the covariance matrix for confidence estimates

### Forgetting Factor Guide

| λ | Effective window | Use case |
|---|---|---|
| 1.00 | All history | Stationary relationship |
| 0.99 | ~100 samples | Slowly drifting |
| 0.95 | ~20 samples | Moderately non-stationary |
| 0.90 | ~10 samples | Rapidly changing |

### Numerical Stability

The inverse covariance matrix P is guaranteed to stay positive
definite with valid inputs. An epsilon floor on the denominator
prevents NaN propagation if P degrades after many updates with
ill-conditioned features. For very long-running filters, periodic
reset may be needed.

## Logistic Regression — Binary Classification

Online SGD for binary probability estimation. Predicts P(outcome=1)
from features via the sigmoid function.

```
z = w · x
p = sigmoid(z) = 1 / (1 + exp(-z))
error = outcome - p
w += learning_rate × error × x
```

F64 only — f32 sigmoid gradient loses precision in the compressed
range near 0 and 1.

### Configuration

```rust
use nexus_stats::regression::LogisticRegression;

let mut model = LogisticRegression::builder()
    .dimensions(5)
    .learning_rate(0.01)
    .build()
    .unwrap();

// Predict probability:
let prob = model.predict(&features);  // in [0, 1]

// Update with true outcome:
model.update(&features, outcome_bool);
```

### Sigmoid Stability

The implementation branches on the sign of z to avoid overflow:
- z ≥ 0: `1 / (1 + exp(-z))` — exp of negative, never overflows
- z < 0: `exp(z) / (1 + exp(z))` — numerator bounded by 1

Output is always in [0, 1] for any input.

## Online k-Means — Streaming Clustering

Assigns each observation to the nearest centroid and updates that
centroid with an EMA step. The first k observations seed the
initial centroids.

### Configuration

```rust
use nexus_stats::learning::OnlineKMeans;

let mut kmeans = OnlineKMeans::builder()
    .clusters(3)
    .dimensions(5)
    .learning_rate(0.01)
    .build()
    .unwrap();

// Update returns cluster assignment:
let cluster = kmeans.update(&features);

// Classify without updating:
let cluster = kmeans.classify(&features);

// Inspect centroids:
let centroid_0 = kmeans.centroid(0);
```

### Seeding

The first k observations become the initial centroids (one per
cluster). Until k observations have been seen, `classify()` will
panic. Check `is_seeded()` before calling `classify()` in
early-stage code.

## Examples by Domain

### Monitoring — Adaptive Latency Prediction

```rust
// Predict latency from queue depth + CPU + active connections
let mut predictor = NlmsFilter::builder()
    .dimensions(3)
    .learning_rate(0.05)
    .build()
    .unwrap();

let features = [queue_depth, cpu_pct, active_conns];
let predicted_latency = predictor.predict(&features);

// When actual latency is known:
predictor.update(&features, actual_latency);

// After convergence, predicted_latency tracks actual closely.
// The weights tell you which features matter most.
```

### Networking — Regime Classification

```rust
let mut classifier = OnlineKMeans::builder()
    .clusters(3)      // 3 regimes
    .dimensions(4)    // 4 features
    .learning_rate(0.02)
    .build()
    .unwrap();

let features = [volatility, spread, rate, autocorrelation];
let regime = classifier.update(&features);

// regime 0, 1, or 2 — adapt behavior per regime
```

## Performance

| Operation | p50 (d=5) |
|-----------|-----------|
| `LmsFilter::update` | 27 cycles |
| `NlmsFilter::update` | 27 cycles |
| `RlsFilter::update` | 92 cycles |
| `LogisticRegression::update` | 61 cycles |
| `OnlineKMeans::update` (k=3) | 52 cycles |
