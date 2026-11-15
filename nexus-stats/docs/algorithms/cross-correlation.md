# Cross-Correlation — Two-Stream Lead/Lag Detection

Online Pearson correlation between two streams at multiple lags.
"Does stream A predict stream B, and by how many steps?"

| Property | Value |
|----------|-------|
| Update cost | 46 cycles (LAG=10) |
| Memory | `16×LAG + 48` bytes |
| Types | `CrossCorrelation` |
| Priming | After `LAG + 2` paired observations |
| Output | `correlation(lag)`, `covariance(lag)`, `peak_lag()` — all `Option` |
| Feature | `std` or `libm` (needs `sqrt` for correlation) |

## What It Does

Tracks the correlation between stream A lagged by k steps and stream B
at the current time, for all lags 0 through LAG-1 simultaneously.

```
r_AB(k) = Cov(A_{t-k}, B_t) / sqrt(Var(A) × Var(B))
```

The lag with the strongest correlation indicates the lead/lag
relationship. If `peak_lag() = 3`, stream A leads stream B by 3 steps.

## When to Use It

**Use CrossCorrelation when:**
- You want to find which signal leads or lags another
- You know the approximate lag range to search
- You need the strength AND direction of the relationship

**Don't use CrossCorrelation when:**
- You only need self-correlation → use [Autocorrelation](autocorrelation.md) (cheaper)
- You need DIRECTED information flow → use [TransferEntropy](transfer-entropy.md)
  (cross-correlation is symmetric: r_AB(k) doesn't tell you if A causes B or both are caused by C)
- You need nonlinear relationships → Pearson correlation is linear only

## How It Works

```
State:
  buffer_a[LAG]    — circular buffer of stream A values
  mean_a, mean_b   — Welford running means
  m2_a, m2_b       — Welford variance accumulators
  cross_m[LAG]     — per-lag cross-moment accumulators

On each paired observation (a, b):
  // Update Welford stats for both streams
  // (exact delta-based formulas)

  // Lag 0: exact Welford co-moment
  cross_m[0] += delta_a_old × delta_b_new

  // Lags 1..LAG-1: use buffered A values
  for k in 1..LAG (if buffer has k values):
    a_lagged = buffer_a[(head - k) % LAG]
    cross_m[k] += (a_lagged - mean_a) × (b - mean_b)

  // Store a in buffer
  buffer_a[head] = a
  head = (head + 1) % LAG

correlation(k) = cross_m[k] / sqrt(m2_a × m2_b)
peak_lag()     = argmax_k |cross_m[k]|
```

Lag 0 uses the exact Welford co-moment formula (same as
[Covariance](covariance.md)). Lags > 0 use an approximation with
the current running mean — O(1/n) error, negligible for streaming.

## Configuration

```rust
use nexus_stats::signal::CrossCorrelation;

// Track correlations at lags 0..9
let mut cc = CrossCorrelation::builder().lag(10).build().unwrap();

for (a, b) in stream_a.iter().zip(stream_b.iter()) {
    cc.update(*a, *b);
}

// Which lag has the strongest correlation?
if let Some(lag) = cc.peak_lag() {
    println!("A leads B by {lag} steps");
    println!("correlation: {:.3}", cc.correlation(lag).unwrap());
}
```

`lag` determines the buffer size and the range of lags tracked
(0 through lag-1). Set at construction time via the builder.

## Examples by Domain

### Sensor Networks — Signal Propagation

```rust
// Does sensor A's reading predict sensor B's?
let mut cc = CrossCorrelation::builder().lag(20).build().unwrap();

// Feed readings from both sensors:
cc.update(sensor_a_reading, sensor_b_reading);

if let Some(lag) = cc.peak_lag() {
    if lag > 0 {
        println!("sensor A leads by {lag} samples");
    }
}
```

### Monitoring — Cause and Effect

```rust
// Does CPU spike predict latency spike?
let mut cc = CrossCorrelation::builder().lag(10).build().unwrap();

cc.update(cpu_utilization, request_latency);

// If peak correlation is at lag 2-3,
// CPU spike precedes latency spike by 2-3 samples
```

### Networking — Signal Propagation Delay

```rust
// Measure propagation delay between two sensors
let mut cc = CrossCorrelation::builder().lag(100).build().unwrap();

cc.update(sensor_a_reading, sensor_b_reading);

if let Some(lag) = cc.peak_lag() {
    let delay_ms = lag as f64 * sample_interval_ms;
    println!("propagation delay: {delay_ms:.1} ms");
}
```

## Cross-Correlation vs Transfer Entropy

| | Cross-Correlation | Transfer Entropy |
|---|---|---|
| Measures | Linear correlation at lag k | Directed information flow |
| Symmetry | Symmetric (r_AB = r_BA at flipped lag) | Asymmetric (TE_A→B ≠ TE_B→A) |
| Causality | No — correlation ≠ causation | Closer — measures predictive power |
| Inputs | Continuous values | Discretized bins |
| Cost | O(LAG) per update | O(1) per update, O(BINS³) per query |
| Memory | 16×LAG + 48 bytes | 2×BINS³×8 bytes (heap) |

Use cross-correlation to find the lag. Use transfer entropy to
confirm directionality.

## Performance

| Operation | p50 |
|-----------|-----|
| `CrossCorrelation::update` (lag=10) | 46 cycles |
| `correlation(lag)` query | 9 cycles (includes `sqrt`) |
| `peak_lag()` query | 30 cycles (scans all lags) |
