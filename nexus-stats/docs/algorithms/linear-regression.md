# Linear Regression — Online Trend Fitting

Dedicated online linear regression with closed-form solve.
The most common regression primitive — lean struct, direct formulas,
no matrix elimination.

| Property | Value |
|----------|-------|
| Update cost | 8 cycles |
| Memory | 72 bytes (96 for `EwLinearRegression`) |
| Types | `LinearRegression` |
| EW types | `EwLinearRegression` |
| Priming | 2 observations (with intercept), 1 (through origin) |
| Output | `slope()`, `intercept()`, `r_squared()`, `predict(x)` |

## What It Does

Fits `y = ax + b` (with intercept) or `y = ax` (through origin)
from streaming data. Keeps running means and the co-moments about
them (Welford): no matrix solve, no array of powers. Slope,
intercept and R² are direct formulas on query.

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

### State

With an intercept: the running means and the co-moments about
them (Welford). The means are held relative to the latest sample,
the anchor, so every quantity the update rounds is on the scale of
the data's spread, not its offset.

```
anchor_x, anchor_y   latest sample
mean_x,   mean_y     mean minus anchor
sxx = Σ (x - mx)²     mx, my: the means
sxy = Σ (x - mx)(y - my)
syy = Σ (y - my)²     (for R²)
n   = count
```

Update, with `w = 1/n` (y is the same with `dy`, `ey`):

```
dx = (x - anchor_x) - mean_x      x minus the old mean
ex = dx·(1 - w)                   x minus the new mean
sxx += dx·ex,  sxy += dx·ey,  syy += dy·ey
anchor_x = x,  mean_x = -ex
```

Through the origin: raw `sxx = Σx²`, `sxy = Σxy`, `syy = Σy²`,
which carry no subtraction.

### Closed-Form Solve

```
slope     = sxy / sxx                           (None if sxx = 0)
intercept = my - slope·mx                       mx = anchor_x + mean_x
predict   = my + slope·((x - anchor_x) - mean_x)
R²        = slope·sxy / syy = sxy² / (sxx·syy), clamped to [0, 1]
```

Through the origin, `predict = slope·x` and R² is the uncentered
form of the same expression. With an intercept, `sxx` is zero only
when every x is equal, so any real spread, even one tick at a large
offset, gives a slope. No Gaussian elimination. O(1) per query.

### Numerical Stability

The co-moments are sums of products of deviations, so a large
offset in x or y (unix timestamps, a price level) never cancels.
Against an exact rational fit the slope stays within 3e-13 with x
in unix seconds, milliseconds or microseconds. There is no need to
center x before feeding it.

`EwLinearRegression` uses West's weighted form of the same update:
`effective_n = (1 - α)·effective_n + 1`, `w = 1/effective_n`, and
the co-moments decay, `sxx = (1 - α)·sxx + dx·ex`.

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
        let offset = cal.intercept().unwrap();
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
| Memory | 72 bytes | 24 bytes |
| Update cost | 8 cycles | 5 cycles |

Use LinearRegression when you need the *trend direction and rate*.
Use EMA when you need a *smoothed current value*.

## Performance

| Operation | p50 |
|-----------|-----|
| `LinearRegression::update` | 8 cycles |
| `slope()` query | 2 cycles |
| `r_squared()` query | 5 cycles |
| `predict(x)` query | 3 cycles |

No matrix solve — all queries are direct formulas.
