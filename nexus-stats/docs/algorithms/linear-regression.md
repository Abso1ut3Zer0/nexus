# Linear Regression — Online Trend Fitting

Dedicated online linear regression with closed-form solve.
The most common regression primitive — lean struct, direct formulas,
no matrix elimination.

| Property | Value |
|----------|-------|
| Update cost | ~6 cycles |
| Memory | ~48 bytes |
| Types | `LinearRegression` |
| EW types | `EwLinearRegression` |
| Priming | 2 observations (with intercept), 1 (through origin) |
| Output | `slope()`, `intercept_value()`, `r_squared()`, `predict(x)` |

## What It Does

Fits `y = ax + b` (with intercept) or `y = ax` (through origin)
from streaming data. Uses 5 sufficient statistics — no matrix
solve, no array of powers. The slope and intercept are computed
from closed-form formulas on query.

**OLS** — weights all observations equally.

**Exponentially-weighted** — adapts to regime changes via decay.
Controlled by `alpha` (weight on new data).

For polynomial fits (degree 2+), see
[PolynomialRegression](polynomial-regression.md).

## When to Use It

**Use LinearRegression when:**
- You want to estimate trend slope from streaming data
- You need R² to measure how linear the relationship is
- You want to predict the next value from the fitted line
- You need `slope()` and `intercept()` — not `coefficients()[0]`

**Use EwLinearRegression when:**
- The trend changes over time and you need the *current* slope
- You want adaptive trend detection with configurable memory

**Use PolynomialRegression instead when:**
- You need degree 2+ (quadratic, cubic, etc.)
- Different entities need different degrees in the same collection

**Don't use regression when:**
- You only need "is it going up or down?" → use [TrendAlert](trend-alert.md) (cheaper)
- You need smoothing, not fitting → use [EMA](ema.md)
- You need change detection → use [CUSUM](cusum.md)

## How It Works

### Sufficient Statistics

```
sum_x  = Σ x
sum_x2 = Σ x²
sum_y  = Σ y
sum_xy = Σ x·y
sum_y2 = Σ y²      (for R²)
n      = count
```

Update: 6 additions + 2 multiplications. No loop, no powers.

### Closed-Form Solve

**With intercept (y = ax + b):**
```
denom     = n·sum_x2 - sum_x²
slope     = (n·sum_xy - sum_x·sum_y) / denom
intercept = (sum_y - slope·sum_x) / n
```

**Through origin (y = ax):**
```
slope = sum_xy / sum_x2
```

**R² (with intercept):**
```
SS_res = sum_y2 - slope·sum_xy - intercept·sum_y
SS_tot = sum_y2 - sum_y²/n
R²     = 1 - SS_res / SS_tot
```

No Gaussian elimination — these are direct formulas. O(1) per query.

### Numerical Stability

The closed-form formulas use sums of products (not deviations from
mean like Welford). For data where `x` values are large and
close together (e.g., Unix timestamps in nanoseconds), the
`n·sum_x2 - sum_x²` denominator can lose precision due to
catastrophic cancellation.

**Mitigation:** Center your x values. Instead of feeding raw
timestamps, feed `x - x_first` or `x - x_mean`. This keeps
the magnitudes small and the denominator well-conditioned.

For the EW variant, the decay naturally keeps sums bounded —
less susceptible to this issue.

## Configuration

### OLS

```rust
use nexus_stats::regression::LinearRegression;

// Standard: y = ax + b
let mut r = LinearRegression::new();

// Through origin: y = ax
let mut r = LinearRegression::through_origin();

// Builder (for explicit config)
let mut r = LinearRegression::builder()
    .intercept(false)
    .build()
    .unwrap();
```

### Exponentially-Weighted

```rust
use nexus_stats::regression::EwLinearRegression;

let mut r = EwLinearRegression::builder()
    .alpha(0.05)       // weight on new observation
    .intercept(true)   // default
    .build()
    .unwrap();
```

`alpha` controls adaptation speed:
- `alpha = 0.01` → slow adaptation, smooth (~100-sample effective window)
- `alpha = 0.1` → fast adaptation, responsive (~10-sample window)
- Effective window ≈ `2/alpha - 1`

## Examples by Domain

### Trading — Price Trend

```rust
let mut trend = LinearRegression::new();

// Feed (sequence, price):
for (i, price) in prices.enumerate() {
    trend.update(i as f64, price);
}

match trend.slope() {
    Some(s) if s > 0.0 => println!("uptrend: +{s:.4}/tick"),
    Some(s) => println!("downtrend: {s:.4}/tick"),
    None => println!("not enough data"),
}
```

### Monitoring — Latency Trend with Adaptation

```rust
let mut trend = EwLinearRegression::builder()
    .alpha(0.02)
    .build()
    .unwrap();

// Per request:
trend.update(elapsed_secs, latency_us);

if let Some(slope) = trend.slope() {
    if slope > 1.0 {
        // Latency increasing at > 1 μs/sec
        alert("latency trending up");
    }
}
```

### Science — Calibration Curve

```rust
let mut cal = LinearRegression::new();

for (reading, reference) in calibration_data {
    cal.update(reading, reference);
}

if let Some(r2) = cal.r_squared() {
    if r2 > 0.99 {
        // Good linear calibration
        let slope = cal.slope().unwrap();
        let offset = cal.intercept_value().unwrap();
        println!("calibration: y = {slope:.4}x + {offset:.4}");
    }
}
```

### Proportional Fit (Through Origin)

```rust
// "How many units per dollar?" — proportional relationship
let mut r = LinearRegression::through_origin();

for (dollars, units) in transactions {
    r.update(dollars, units);
}

println!("rate: {:.2} units/$", r.slope().unwrap());
```

## LinearRegression vs EMA

| | LinearRegression | EMA |
|---|---|---|
| What it gives you | Slope + intercept + R² | Smoothed value |
| Answers | "What's the rate of change?" | "What's the current level?" |
| Model | y = ax + b (parametric) | Weighted average (non-parametric) |
| Memory | 48 bytes | 24 bytes |
| Update cost | ~6 cycles | ~5 cycles |

Use LinearRegression when you need the *trend direction and rate*.
Use EMA when you need a *smoothed current value*.

## Performance

| Operation | p50 |
|-----------|-----|
| `LinearRegression::update` | ~6 cycles |
| `slope()` query | ~5 cycles |
| `r_squared()` query | ~8 cycles |
| `predict(x)` query | ~6 cycles |

No matrix solve — all queries are direct formulas.
