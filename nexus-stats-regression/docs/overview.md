# Overview

`nexus-stats-regression` is the "online model-fitting" crate in the nexus-stats ecosystem. It provides three families of tools:

1. **Closed-form regressors** — linear, polynomial, transformed, EW variants. Streaming, exact OLS solutions.
2. **Gradient-based learners** — LMS, NLMS, RLS, Huber, logistic, Adam/AdaGrad/OnlineGD. For high-dimensional problems where closed-form OLS is impractical.
3. **Bayesian / state-space estimators** — Kalman2d, Kalman3d, BetaBinomial, GammaPoisson. For problems with known noise structure or when you need uncertainty quantification.

## Two kinds of "regression"

The crate deliberately mixes two styles:

- **Streaming closed-form**: update sufficient statistics, solve OLS in closed form on query. Exact. No hyperparameters (except EW halflife). Use for 1-8 features.
- **Gradient adaptive**: maintain a weight vector, update by stochastic gradient on each sample. Approximate. Has learning rate. Scales to many features.

For small problems (polynomial fits, pairs-trade beta, signal decay curves) use the closed-form regressors. For anything with many features or where the true relationship is changing, use the gradient-based learners.

## API shape

Single-output regressors (most of them):

```rust
let mut reg = LinearRegression::new();
reg.update(x, y)?;            // feed observations
let y_hat = reg.predict(x0);  // query
reg.slope();                  // Option<f64>
reg.intercept();        // Option<f64>
```

Multi-feature learners:

```rust
let mut lms = LmsFilter::builder().dimensions(8).learning_rate(0.01).build()?;
lms.update(&features, target);       // features is &[f64] of len dimensions
let y_hat = lms.predict(&features);
lms.weights();                        // &[f64]
```

Kalman:

```rust
kf.predict();                         // advance time with default dynamics
kf.predict_with_dynamics(F);          // custom transition matrix
kf.update(measurement, H, R);         // measurement update
kf.state();                           // query
```

## Conventions

- `update(...)` returns `Result<(), DataError>` (float inputs are NaN/Inf-checked).
- `predict(...)` is pure query; no state change.
- `is_primed()` / `count()` / `reset()` on every type.
- Builders everywhere — most types have 3+ parameters.

## Feature Flags

| Feature | Effect |
|---------|--------|
| `std` | Native math, default. |
| `libm` | `no_std` math fallback. |
| `alloc` | Required for everything with dynamic dimension: LMS/NLMS/RLS, K-Means, Adam/AdaGrad, logistic, polynomial (degree > compile-time constant). |

The Kalman2d/Kalman3d and the scalar closed-form linear regressors work without `alloc`.

## Performance

- **Closed-form scalar regressors**: ~tens of cycles per update.
- **Polynomial degree `d`**: O(d²) per update for the sufficient statistics, O(d³) to solve on query. Query-only when you need the coefficients.
- **LMS / NLMS**: O(dimensions) per update.
- **RLS**: O(dimensions²) per update — faster convergence at higher cost.
- **Kalman2d/3d**: constant-per-update, small (matrices are 2x2 / 3x3).

## Composing

Common patterns:

- **Pair-trading beta**: `LinearRegression` or `EwLinearRegression` on (x, y) returns.
- **Streaming mid-price**: feed exchange mid into `Kalman2d` with position+velocity state.
- **Signal research**: `LmsFilter` or `RlsFilter` with lagged features to find optimal weights.
- **Execution quality**: `SignalDecayCurve` to find how fast alpha decays with holding period.

## Cross-references

- Scalar Kalman: [`Kalman1d`](../../nexus-stats-smoothing/docs/kalman1d.md) — use instead of Kalman2d when state is 1D.
- For regression *inputs* that are cleaned of noise: [`Hampel`](../../nexus-stats-smoothing/docs/hampel.md), [`WindowedMedian<f64>`](../../nexus-stats-smoothing/docs/windowed-median.md).
- Half-life / Hurst classifiers: [`nexus-stats-core::statistics`](../../nexus-stats-core/docs/statistics.md).
