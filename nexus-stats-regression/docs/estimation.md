# Estimation — Kalman filters and Bayesian estimators

Module path: `nexus_stats_regression::estimation`.

## Kalman2dF64 / Kalman3dF64 — Multivariate Kalman

Two-dimensional and three-dimensional Kalman filters with customizable dynamics. Unlike `Kalman1dF64` (which lives in `nexus-stats-smoothing` and assumes constant-velocity dynamics), these filters let you pass an arbitrary transition matrix via `predict_with_dynamics`.

### When to use each

- **Kalman1d** ([`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/kalman1d.md)): scalar measurement, position + velocity state. Simplest case.
- **Kalman2d**: two-dimensional state. Position/velocity in 2D, or two correlated quantities.
- **Kalman3d**: three-dimensional state. Position/velocity/acceleration, or a three-factor model.

### API (Kalman2d, Kalman3d mirrors it)

```rust
impl Kalman2dF64 {
    pub fn builder() -> Kalman2dF64Builder;

    pub fn predict(&mut self);
    pub fn predict_with_dynamics(&mut self, f: [[f64; 2]; 2]);
    pub fn update(&mut self, measurement: /* see source */) -> Result<(), DataError>;

    // State accessors via source.
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}
```

### Example — Kalman2d with custom dynamics

```rust
use nexus_stats_regression::estimation::Kalman2dF64;

let dt = 0.01;
let mut kf = Kalman2dF64::builder()
    .process_noise([[0.001, 0.0], [0.0, 0.001]])
    .measurement_noise([[0.1, 0.0], [0.0, 0.1]])
    .initial_state([0.0, 0.0])
    .build()
    .unwrap();

for measurement in sensor_stream {
    // Constant-velocity dynamics:
    kf.predict_with_dynamics([[1.0, dt], [0.0, 1.0]]);
    kf.update(measurement).unwrap();
}
```

### Caveats

- You're responsible for the dynamics matrix. If you pass identity, it's a random-walk filter.
- Process and measurement noise must be positive-definite. Builder will fail otherwise.
- `no_std` compatible.

---

## BetaBinomialF64 — Bayesian rate estimation for successes

Conjugate Bayesian estimator for a Bernoulli success rate. Maintains `(alpha, beta)` hyperparameters that update analytically on every observation. Gives you not just a point estimate but full posterior — credible intervals, probability of exceeding a threshold, etc.

### API

```rust
use nexus_stats_regression::estimation::BetaBinomialF64;

let mut bb = BetaBinomialF64::builder()
    .prior_alpha(1.0)  // uniform prior
    .prior_beta(1.0)
    .build()
    .unwrap();

bb.update(true);                 // one success
bb.update_batch(10, 5);          // 10 successes, 5 failures
let mean = bb.posterior_mean();
let (lo, hi) = bb.credible_interval(0.95);
```

### When to use it

- **Small sample counts** where frequentist rates are noisy. Beta-binomial gives you proper uncertainty.
- **A/B tests** with prior knowledge.
- **Fill rate tracking** when you need confidence intervals on the rate, not just the rate.

### Caveats

- Only for Bernoulli outcomes. For continuous targets, use a Gaussian estimator.
- Prior matters when the sample is small. For uninformative priors, use `(1, 1)`.

---

## GammaPoissonF64 — Bayesian rate estimation for counts

Conjugate Bayesian estimator for a Poisson rate with known exposure. Maintains `(alpha, beta)` Gamma hyperparameters.

### API

```rust
use nexus_stats_regression::estimation::GammaPoissonF64;

let mut gp = GammaPoissonF64::new();
gp.update(event_count, exposure).unwrap();
let rate = gp.posterior_mean();
```

### When to use it

- **Event rate tracking** with Bayesian uncertainty.
- **Exposure-weighted averages** — e.g. errors per million requests, where exposure is the number of requests.
- **Credible intervals on rates** rather than just point estimates.

### Caveats

- Needs positive exposure. Zero-exposure updates are no-ops.
- Poisson assumption — events must be approximately independent.

---

## Cross-references

- Scalar state: [`Kalman1dF64`](../../nexus-stats-smoothing/docs/kalman1d.md).
- Rate tracking without uncertainty: [`HitRate`](../../nexus-stats-core/docs/statistics.md#hitrate--rolling-success-rate), [`EventRate`](../../nexus-stats-core/docs/monitoring.md#eventrate).
