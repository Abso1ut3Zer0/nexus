# Regression

Closed-form and EW regressors. Module path: `nexus_stats_regression::regression`.

## LinearRegression — streaming OLS

The simplest streaming regressor: y = a + bx. Updates sufficient statistics (`Σx`, `Σy`, `Σxy`, `Σx²`, `n`) on each `update(x, y)`; solves the OLS equations on query.

### API

```rust
impl LinearRegression {
    pub fn new() -> Self;
    pub fn builder() -> LinearRegressionBuilder;
    pub fn update(&mut self, x: f64, y: f64) -> Result<(), DataError>;
    pub fn slope(&self) -> Option<f64>;
    pub fn intercept_value(&self) -> Option<f64>;
    pub fn predict(&self, x: f64) -> Option<f64>;
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}
```

### Example — pair-trade beta

```rust
use nexus_stats_regression::regression::LinearRegression;

let mut beta = LinearRegression::new();

// Returns of instrument A (x) and instrument B (y).
for (ra, rb) in paired_returns {
    beta.update(ra, rb).unwrap();
}

println!(
    "slope beta = {:.4}, intercept alpha = {:.4}",
    beta.slope().unwrap(),
    beta.intercept_value().unwrap(),
);

// Fair value of B given A's return:
let fair = beta.predict(0.01).unwrap();
```

### Caveats

- OLS assumes `x` is known and noise is in `y`. If both are noisy (pair-trade — both returns are estimates), consider total least squares or a Kalman filter.
- No forgetting. Use `EwLinearRegression` if you need the fit to adapt to drift.

---

## EwLinearRegression — forgetful linear regression

Same shape, but sufficient statistics decay exponentially. The effective sample size stays bounded, so the regression adapts to regime changes.

```rust
let mut beta = EwLinearRegression::builder()
    .alpha(0.0014)   // forgetting factor, about a 500-sample half-life
    .build()
    .unwrap();
for (x, y) in stream { beta.update(x, y).unwrap(); }
```

Use when the relationship between x and y drifts (structural beta change, regime shift).

---

## PolynomialRegression — streaming polynomial fit

Fits `y = a0 + a1 x + ... + ad x^d` for configurable degree `d`. Updates the power moments `Σx^k` and cross moments `Σx^k y` in O(d²) per update; solves on query.

### API

```rust
impl PolynomialRegression {
    pub fn builder() -> PolynomialRegressionBuilder;
    pub fn update(&mut self, x: f64, y: f64) -> Result<(), DataError>;
    pub fn coefficients(&self) -> Option<Vec<f64>>;
    pub fn predict(&self, x: f64) -> Option<f64>;
}
```

### Example — nonlinear trend

```rust
use nexus_stats_regression::regression::PolynomialRegression;

let mut quad = PolynomialRegression::builder()
    .degree(2)
    .intercept(true)
    .build()
    .unwrap();

for (x, y) in training_data {
    quad.update(x, y).unwrap();
}

let coeffs = quad.coefficients().unwrap();   // [a0, a1, a2]
let y_hat = quad.predict(1.5).unwrap();
```

### Caveats

- Conditioning gets bad for degree > 6 without feature centering. The builder has intercept support but doesn't auto-center — center your `x` manually.
- Closed-form solve is O(d³) on query, so don't poll it every sample if the cost matters.

---

## EwPolynomialRegression — forgetful polynomial regression

Same as above but with EW decay. Use when the curve shape drifts.

---

## ExponentialRegression / LogarithmicRegression / PowerRegression — linearized fits

Streaming fits of nonlinear families that linearize under a transformation:

| Family | Transform | Fits |
|--------|-----------|------|
| Exponential | log y | y = a * e^(bx) |
| Logarithmic | — | y = a * ln(x) + b |
| Power | log y, log x | y = a * x^b |

One type per family (`ExponentialRegression`, `LogarithmicRegression`, `PowerRegression`), each with an `Ew*` forgetful twin. You feed raw `(x, y)` pairs; the type applies the transform internally. `predict(x)` returns the value in original space.

### Example — exponential growth fit

```rust
use nexus_stats_regression::regression::ExponentialRegression;

let mut fit = ExponentialRegression::new();
for (t, y) in growth_data {
    fit.update(t, y).unwrap();   // y must be positive
}

let predicted = fit.predict(10.0).unwrap(); // e.g. y at t=10
```

### Caveats

- Log transforms require positive `y` (and positive `x` for power). Inputs at or below 0 error out.
- Error minimization is in log-space, not y-space. Don't use transformed regressors to compute "sum of squared errors in y" — they minimize something else.

---

## LogisticRegression — online binary classifier

Online logistic regression via stochastic gradient steps on the logistic loss. Maintains a weight vector of dimension `features`; `predict(features)` returns a probability in `[0, 1]`.

### API

```rust
impl LogisticRegression {
    pub fn builder() -> LogisticRegressionBuilder;
    pub fn predict(&self, features: &[f64]) -> f64;        // 0..1
    pub fn update(&mut self, features: &[f64], outcome: bool);
    pub fn weights(&self) -> &[f64];
}
```

### Example — predicting fill likelihood

```rust
use nexus_stats_regression::regression::LogisticRegression;

let mut clf = LogisticRegression::builder()
    .dimensions(5)
    .learning_rate(0.01)
    .build()
    .unwrap();

for (features, filled) in training_stream {
    clf.update(&features, filled);
}

let prob = clf.predict(&[/* 5 features */]);
```

### Caveats

- Needs normalized features. Unscaled inputs blow up the gradient.
- No regularization by default — add `l2` in the builder if available, else monitor weights for drift.
- Requires `alloc` and `std`/`libm` for the sigmoid.

---

## LaggedPredictor — y_t = a + b * x_{t-lag}

A linear regression where the feature is lagged relative to the target. Trading-specific: "does bid change at t-3 predict mid change at t?".

### API

```rust
impl LaggedPredictor {
    pub fn builder() -> LaggedPredictorBuilder;
    pub fn update(&mut self, x: f64, y: f64) -> Result<(), DataError>;
    pub fn slope(&self) -> Option<f64>;
    pub fn intercept(&self) -> Option<f64>;
    // more
}
```

Configure the lag via the builder; internally maintains a ring buffer of past `x` values.

### Example — lead-lag model

```rust
use nexus_stats_regression::regression::LaggedPredictor;

let mut pred = LaggedPredictor::builder()
    .lag(3)                // x at t-3 predicts y at t
    .halflife(500.0)
    .build()
    .unwrap();

for (x, y) in stream {
    pred.update(x, y).unwrap();
}

let slope = pred.slope().unwrap();
```

---

## KyleLambda — price impact slope

Kyle's lambda from market microstructure: `ΔP = λ * volume_imbalance`. The regression slope between signed volume and price change.

### API

```rust
impl KyleLambda {
    pub fn builder() -> KyleLambdaBuilder;
    pub fn update(&mut self, signed_volume: f64, price_change: f64) -> Result<(), DataError>;
    pub fn lambda(&self) -> Option<f64>;
    pub fn intercept(&self) -> Option<f64>;
}
```

### Example

```rust
use nexus_stats_regression::regression::KyleLambda;

let mut kl = KyleLambda::builder()
    .alpha(0.0007)   // forgetting factor, about a 1000-sample half-life
    .build()
    .unwrap();

for (signed_vol, dprice) in trade_stream {
    kl.update(signed_vol, dprice).unwrap();
}

let lambda = kl.lambda().unwrap();  // price impact coefficient
```

**Use for:** market impact modeling, execution cost estimation, sizing a trade against the book's liquidity.

---

## SignalDecayCurve — alpha half-life estimator

Given (signal_value, future_return_at_horizon_k) tuples across multiple horizons, fits an exponential decay to the Information Coefficient (signal-return correlation) as a function of horizon. Returns the decay constant / half-life.

### Example

```rust
use nexus_stats_regression::regression::SignalDecayCurve;

let mut decay = SignalDecayCurve::builder()
    // config
    .build()
    .unwrap();

// For each observation, feed the signal and the realized return at each horizon.
for obs in observations {
    decay.update(obs.signal, obs.horizon, obs.return_).unwrap();
}

// Query the fitted decay parameters — see source for accessors.
```

**Use for:** determining how long your alpha lasts, picking holding periods, signal-lifecycle research.

---

## Cross-references

- [`nexus-stats-core::statistics::HalfLife`](../../nexus-stats-core/docs/statistics.md#halflife--mean-reversion-half-life) — mean-reversion half-life for a single series.
- [`Covariance`](../../nexus-stats-core/docs/statistics.md#covariance--online-covariance-and-correlation) — lag-0 linear relationship.
