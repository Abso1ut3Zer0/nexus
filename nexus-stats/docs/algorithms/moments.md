# Moments — Online Skewness and Kurtosis

**Pebay's algorithm (2008).** Numerically stable single-pass
computation of mean, variance, skewness, and excess kurtosis.
Extends [Welford](welford.md) to 3rd and 4th central moments.
Supports parallel merging.

| Property | Value |
|----------|-------|
| Update cost | 26 cycles |
| Memory | ~40 bytes (f64) |
| Types | `Moments` |
| Priming | Mean after 1, variance after 2, skewness after 3, kurtosis after 4 |
| Output | `mean()`, `variance()`, `skewness()`, `kurtosis()` — all `Option` |
| Error handling | Returns `Result<_, DataError>` on NaN/Inf input |

## What It Does

Tracks five values — count, mean, M2 (variance), M3 (third central
moment), and M4 (fourth central moment). Derives skewness and excess
kurtosis from them. All updates use delta-based formulas that avoid
catastrophic cancellation.

**Skewness** measures asymmetry. Positive = right tail is longer
(large upward outliers). Negative = left tail is longer. Zero =
symmetric (like a normal distribution).

**Excess kurtosis** measures tail weight. Positive = heavier tails
than normal ("leptokurtic" — more extreme events). Negative = lighter
tails ("platykurtic"). Zero = normal-like tails. A uniform distribution
has kurtosis of -1.2.

## When to Use It

**Use Moments when:**
- You need distribution shape beyond mean/variance
- You want to detect fat tails (kurtosis) or asymmetry (skewness)
- You need to merge partial results from parallel streams
- You want all four statistics from a single O(1) update

**Don't use Moments when:**
- You only need mean + variance → use [Welford](welford.md) (cheaper)
- You only need smoothed mean → use [EMA](ema.md)
- You need percentiles → use [Percentile](../../../nexus-stats-core/docs/statistics.md#percentile--online-percentile-p²)
- You need windowed statistics → Moments is all-history, not windowed

## How It Works

```
On each sample x:
  delta   = x - mean
  delta_n = delta / count
  delta_n2 = delta_n²
  term1   = delta × delta_n × (count - 1)

  M4 += term1 × delta_n2 × (count² - 3·count + 3)     ← FIRST (uses old M2, M3)
        + 6 × delta_n2 × M2
        - 4 × delta_n × M3
  M3 += term1 × delta_n × (count - 2)                   ← SECOND (uses old M2)
        - 3 × delta_n × M2
  M2 += term1                                            ← THIRD
  mean += delta_n                                        ← LAST

  Update order is critical: M4 → M3 → M2 → mean
  Each formula uses the PREVIOUS iteration's lower moments.
```

```
Skewness = sqrt(count) × M3 / M2^(3/2)
Kurtosis = count × M4 / M2² - 3         ← excess (normal = 0)
```

### Pebay's Merge

Two independent Moments accumulators merge in O(1), extending
Chan's parallel formula to 3rd and 4th moments:

```
delta = b.mean - a.mean
combined.M2 = a.M2 + b.M2 + delta² × na × nb / N
combined.M3 = a.M3 + b.M3 + delta³ × na × nb × (na - nb) / N²
              + 3 × delta × (na × b.M2 - nb × a.M2) / N
combined.M4 = a.M4 + b.M4 + delta⁴ × na × nb × (na² - na·nb + nb²) / N³
              + 6 × delta² × (na² × b.M2 + nb² × a.M2) / N²
              + 4 × delta × (na × b.M3 - nb × a.M3) / N
```

## Configuration

```rust
// No configuration — create and update
let mut m = Moments::new();

for sample in data {
    m.update(sample).unwrap();
}

println!("skewness: {:?}", m.skewness());
println!("kurtosis: {:?}", m.kurtosis());
```

### Merging

```rust
let mut worker_a = Moments::new();
let mut worker_b = Moments::new();

for x in &data[..half] { worker_a.update(*x).unwrap(); }
for x in &data[half..] { worker_b.update(*x).unwrap(); }

worker_a.merge(&worker_b);
// worker_a now has moments for the full dataset
```

## Examples by Domain

### Distribution Shape Monitoring

```rust
let mut samples = Moments::new();

// On each observation:
samples.update(measurement).unwrap();

if let Some(skew) = samples.skewness() {
    if skew < -0.5 {
        // Negative skew: larger negative deviations than positive
    }
}

if let Some(kurt) = samples.kurtosis() {
    if kurt > 3.0 {
        // Fat tails: extreme values more likely than Gaussian
    }
}
```

### SRE — Latency Distribution Shape

```rust
let mut latency = Moments::new();

// Per request:
latency.update(response_time_us).unwrap();

// Alert if distribution becomes asymmetric
// (indicates a subpopulation hitting a slow path)
if let Some(skew) = latency.skewness() {
    if skew > 2.0 {
        alert("latency distribution is right-skewed");
    }
}
```

### Monitoring — Regime Change via Kurtosis

```rust
// Track kurtosis over time:
// Stable regime: kurtosis ≈ 0
// Volatile regime: kurtosis spikes (fat tails)
// Calm regime: kurtosis drops (thin tails)
```

## Population vs Sample

Moments computes **population** estimators (N denominator), not
sample-corrected (N-1). For streaming use cases with n > 100,
the difference is negligible. For small-sample inference (n < 30),
use a batch estimator with Bessel's correction.

## Performance

| Operation | p50 |
|-----------|-----|
| `Moments::update` | 26 cycles |
| `Moments::merge` | 35 cycles |
| `skewness()` query | 6 cycles (includes `sqrt`) |

## Academic Reference

Pebay, P. "Formulas for Robust, One-Pass Parallel Computation of
Covariances and Arbitrary-Order Statistical Moments." *Technical
Report SAND2008-6212*, Sandia National Laboratories (2008).
