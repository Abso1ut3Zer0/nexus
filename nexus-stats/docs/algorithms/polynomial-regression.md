# Polynomial Regression — Online Curve Fitting

Online OLS and exponentially-weighted polynomial regression (degree 2+),
plus linearized fits for exponential, logarithmic, and power law models.

For linear regression (degree 1), see [LinearRegression](linear-regression.md)
— a dedicated type with smaller state and closed-form solve.

| Property | Value |
|----------|-------|
| Update cost | 14 cycles (quadratic), 23 cycles (degree 4) |
| Memory | ~208 bytes (fixed, independent of degree) |
| Types | `PolynomialRegression` |
| EW types | `EwPolynomialRegression` |
| Transformed | `ExponentialRegression`, `LogarithmicRegression`, `PowerRegression` |
| Priming | degree + 1 observations (with intercept), degree without |
| Output | `coefficients()`, `r_squared()`, `predict(x)` |

## What It Does

Accumulates sufficient statistics (sums of powers of x and
cross-products with y) and solves the normal equations at query
time to produce polynomial coefficients. Supports any degree from
1 (linear) to 8 (octic), with or without an intercept term.

**OLS** — weights all observations equally (all-history fit).

**Exponentially-weighted** — decays old observations, adapting to
regime changes. Controlled by `alpha` (weight on new data).

**Transformed fits** — exponential (`y = ae^(bx)`), logarithmic
(`y = a·ln(x) + b`), and power law (`y = ax^b`) via linearization.
Apply `ln` at the API boundary, then fit with linear regression
internally.

## When to Use It

**Use PolynomialRegression when:**
- You need to estimate a trend line (slope, intercept)
- You want to detect acceleration (quadratic coefficient)
- You need R² goodness of fit
- You want to predict future values from the fitted model
- Different entities need different model degrees (runtime config)

**Use EwPolynomialRegression when:**
- The underlying relationship changes over time (regime shifts)
- You want the model to adapt to recent data
- "What's the current trend?" not "what's the all-time trend?"

**Use the transformed fits when:**
- You expect exponential growth/decay → `ExponentialRegression`
- You expect diminishing returns / saturation → `LogarithmicRegression`
- You expect scaling laws → `PowerRegression`

**Don't use polynomial regression when:**
- You need windowed statistics → use [Welford](welford.md) or [Moments](moments.md)
- You need change detection → use [CUSUM](cusum.md) or [TrendAlert](trend-alert.md)
- You're fitting degree > 5 with large x values → numerical instability

## How It Works

### Sufficient Statistics

The accumulator maintains sums of powers:

```
sum_x[j]  = Σ x^j     for j = 0..2D    (where D = degree)
sum_xy[j] = Σ x^j·y   for j = 0..D
sum_y2    = Σ y²                         (for R²)
```

Update is O(degree) — compute powers of x and accumulate.

### Normal Equations

At query time, construct the Gram matrix A and vector b:

```
With intercept (dim = degree + 1):
  A[i][j] = sum_x[i + j]     i, j = 0..dim
  b[i]    = sum_xy[i]

Without intercept (dim = degree):
  A[i][j] = sum_x[i + j + 2] i, j = 0..dim
  b[i]    = sum_xy[i + 1]
```

Solve Ax = b via Gaussian elimination with partial pivoting.
Maximum system size: 9×9 (degree 8 + intercept).

## Configuration

### OLS (all-history)

```rust
use nexus_stats::regression::PolynomialRegression;

// Quadratic: y = ax² + bx + c
let mut r = PolynomialRegression::builder()
    .degree(2)
    .build()
    .unwrap();

// Cubic: y = ax³ + bx² + cx + d
let mut r = PolynomialRegression::builder()
    .degree(3)
    .build()
    .unwrap();

// Degree 4, no intercept
let mut r = PolynomialRegression::builder()
    .degree(4)
    .intercept(false)
    .build()
    .unwrap();
```

For linear regression (degree 1), use the dedicated
[`LinearRegression`](linear-regression.md) type instead —
smaller state, closed-form solve, `slope()`/`intercept_value()` API.

### Exponentially-weighted

```rust
use nexus_stats::regression::EwPolynomialRegression;

let mut r = EwPolynomialRegression::builder()
    .degree(3)
    .alpha(0.05)
    .build()
    .unwrap();
```

### Transformed fits

```rust
use nexus_stats::regression::ExponentialRegression;
use nexus_stats::regression::LogarithmicRegression;
use nexus_stats::regression::PowerRegression;

let mut exp = ExponentialRegression::new();    // y = a·e^(bx)
let mut log = LogarithmicRegression::new();    // y = a·ln(x) + b
let mut pow = PowerRegression::new();          // y = a·x^b

// EW variants with builder
let mut ew_exp = EwExponentialRegression::builder()
    .alpha(0.05)
    .build()
    .unwrap();
```

## Examples by Domain

### Trading — Trend Estimation

```rust
// For linear trends, use LinearRegression (see linear-regression.md).
// PolynomialRegression is for degree 2+ curves:

let mut accel = PolynomialRegression::builder()
    .degree(2)
    .build()
    .unwrap();

// Feed (sequence, price):
for (i, price) in prices.enumerate() {
    accel.update(i as f64, price);
}

if let Some(coeffs) = accel.coefficients() {
    let quadratic_coeff = coeffs[2];  // acceleration term
    if quadratic_coeff > 0.0 {
        // Price accelerating upward (parabolic)
    }
}
```

### Science — Exponential Decay Fitting

```rust
let mut decay = ExponentialRegression::new();

for (t, measurement) in data {
    decay.update(t, measurement);
}

if let Some(rate) = decay.growth_rate() {
    println!("half-life: {:.2}", -(2.0_f64.ln()) / rate);
}
```

### Multi-Model Per-Entity

```rust
use std::collections::HashMap;
use nexus_stats::regression::PolynomialRegression;

let mut models: HashMap<String, PolynomialRegression> = HashMap::new();

// Different symbols get different model degrees
models.insert("BTC".into(), PolynomialRegression::quadratic());
models.insert("ETH".into(), PolynomialRegression::linear());

for (symbol, x, y) in data_stream {
    if let Some(model) = models.get_mut(&symbol) {
        model.update(x, y);
    }
}
```

## Numerical Stability

The normal equations with sums-of-powers can become ill-conditioned
for high degree combined with large x values. This is inherent to
the polynomial basis — not a bug in the implementation.

**Guidance:**
- Degree 1-3: fine for any reasonable x range
- Degree 4-5: center and scale x values for best results
  (`x_scaled = (x - x_mean) / x_std`)
- Degree 6-8: only for small x ranges or pre-scaled data
- If `coefficients()` returns `None` despite enough data, the
  system is likely ill-conditioned — reduce degree or scale x

## Transformed Fit Details

### Exponential: y = a·e^(bx)

Internally fits `ln(y) = ln(a) + bx` via linear regression.
- `growth_rate()` → b (positive = growth, negative = decay)
- `scale()` → a = e^(intercept)
- `predict(x)` → a·e^(bx)
- Requires y > 0 — observations with y ≤ 0 are silently skipped
- R² is in log-space (goodness of fit of ln(y) vs x)

### Logarithmic: y = a·ln(x) + b

Internally fits y = a·z + b where z = ln(x).
- `slope()` → a
- `intercept_value()` → b
- `predict(x)` → a·ln(x) + b
- Requires x > 0 — observations with x ≤ 0 are silently skipped

### Power: y = a·x^b

Internally fits ln(y) = ln(a) + b·ln(x).
- `exponent()` → b
- `scale()` → a = e^(intercept)
- `predict(x)` → a·x^b
- Requires x > 0 and y > 0 — invalid observations silently skipped

## Performance

| Operation | p50 |
|-----------|-----|
| `PolynomialRegression::update` (linear) | 11 cycles |
| `PolynomialRegression::update` (quadratic) | 14 cycles |
| `coefficients()` (linear, 2×2 solve) | 72 cycles |
| `coefficients()` (quadratic, 3×3 solve) | 136 cycles |
| `predict(x)` | 133 cycles (re-solves + evaluates) |

`update()` cost scales with degree (computing powers of x).
`coefficients()` cost scales with degree³ (Gaussian elimination).
Both are bounded by the degree ≤ 8 constraint.
