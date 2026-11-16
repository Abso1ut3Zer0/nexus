# Autocorrelation — Self-Correlation at Fixed Lag

Online autocorrelation coefficient at a configurable lag.
"Is this signal trending or mean-reverting?"

| Property | Value |
|----------|-------|
| Update cost | 11 cycles |
| Memory | `8×LAG + 32` bytes |
| Types | `Autocorrelation` |
| Priming | After `LAG + 2` samples |
| Output | `correlation()` in [-1, 1], `covariance()` — both `Option` |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

Computes the Pearson correlation between a signal and a lagged copy
of itself: r(k) = Cov(x_t, x_{t-k}) / Var(x).

- **r > 0**: trending / persistent — values tend to continue in the same direction
- **r < 0**: mean-reverting / anti-persistent — values tend to reverse
- **r ≈ 0**: no linear dependence at this lag (random walk)

## When to Use It

**Use Autocorrelation when:**
- You want to classify a signal as trending vs mean-reverting
- You want to detect periodicity at a known lag
- You need to monitor stationarity (stable autocorrelation = stationary)

**Don't use Autocorrelation when:**
- You need correlation between TWO different signals → use [CrossCorrelation](cross-correlation.md)
- You need to detect which lag has the strongest effect → use CrossCorrelation with multiple lags
- You need nonlinear dependence → autocorrelation only captures linear relationships

## How It Works

```
State:
  buffer[LAG]  — circular buffer of previous values
  mean         — running mean (Welford)
  m2           — running variance accumulator
  cross_m      — cross-moment accumulator

On each sample x (after buffer is full):
  x_lagged = buffer[oldest]

  // Update Welford mean/variance
  delta = x - mean
  mean += delta / count
  m2 += delta × (x - mean)

  // Update cross-moment (approximate: uses current mean for lagged value)
  cross_m += (x - mean) × (x_lagged - mean)

  // Store in buffer
  buffer[head] = x
  head = (head + 1) % LAG

Autocorrelation r(k) = cross_m / m2
  (1/N normalization cancels in numerator and denominator)
```

The cross-moment uses the current running mean for both x(t) and
x(t-LAG). This introduces O(1/n) error that is negligible for
streaming (n >> 100). Exact computation would require separate
means for the lagged and current windows.

## Configuration

```rust
use nexus_stats::signal::Autocorrelation;

// Lag-1 autocorrelation (is the signal trending?)
let mut ac = Autocorrelation::builder().lag(1).build().unwrap();

for sample in data {
    ac.update(sample).unwrap();
}

if let Some(r) = ac.correlation() {
    println!("lag-1 autocorrelation: {r:.3}");
}
```

`lag` determines the buffer size and is set at construction time
via the builder.

## Examples by Domain

### Trading — Regime Detection

```rust
let mut ac = Autocorrelation::builder().lag(1).build().unwrap();

// Feed returns:
ac.update(price_return).unwrap();

if let Some(r) = ac.correlation() {
    if r > 0.3 {
        // Trending regime — momentum strategies work
    } else if r < -0.3 {
        // Mean-reverting — fade the moves
    } else {
        // Random walk — no edge from autocorrelation
    }
}
```

### Monitoring — Stale Feed Detection

```rust
// High autocorrelation in quote changes = not updating
let mut ac = Autocorrelation::builder().lag(1).build().unwrap();

// Feed quote deltas (should be ~random if feed is live):
ac.update(new_quote - last_quote).unwrap();

if let Some(r) = ac.correlation() {
    if r > 0.8 {
        alert("feed may be stale — changes are highly autocorrelated");
    }
}
```

### Networking — Jitter Periodicity

```rust
// Detect periodic jitter at known interval
let mut ac = Autocorrelation::builder().lag(100).build().unwrap();

// Feed inter-packet intervals:
ac.update(interval_ms).unwrap();

if let Some(r) = ac.correlation() {
    if r > 0.5 {
        // Strong periodicity at lag 100 — possible scheduling artifact
    }
}
```

## Integer Inputs

Correlation is fractional, so there is no integer form. Cast integer
samples (tick counts, queue depths) to `f64` at the call site.

## Performance

| Operation | p50 |
|-----------|-----|
| `Autocorrelation::update` (lag=1) | 11 cycles |
| `Autocorrelation::update` (lag=10) | 13 cycles |
| `correlation()` query | 6 cycles |

The update cost is dominated by the Welford mean/variance update
(one division). Buffer management is a single array write + modular
increment. The correlation query is one division.
