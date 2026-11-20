# Welford — Online Mean, Variance, and Standard Deviation

**Welford's algorithm (1962).** Numerically stable single-pass
computation of running statistics. Supports parallel merging via
Chan's algorithm.

| Property | Value |
|----------|-------|
| Update cost | 13 cycles |
| Memory | ~24 bytes |
| Types | `Welford` |
| Priming | Mean after 1 sample, variance after 2 |
| Output | `mean()`, `variance()`, `std_dev()` — all `Option<T>` |

## What It Does

Tracks three values — count, mean, and sum of squared deviations (M2) —
and derives variance and standard deviation from them. Unlike the naive
formula `var = E[x²] - E[x]²`, Welford's avoids catastrophic cancellation
when the mean is large relative to the variance.

## When to Use It

**Use Welford when:**
- You need running mean + variance + std dev
- Numerical stability matters (large offsets, small deltas)
- You want to merge partial results from parallel workers

**Don't use Welford when:**
- You only need smoothed mean → use [EMA](ema.md) (cheaper, no division)
- You need exponentially weighted variance → use [EwmaVariance](ewma-var.md)
- You need integer-only computation → Welford requires division

## How It Works

```
On each sample x:
  count += 1
  delta  = x - mean
  mean  += delta / count          ← one division
  delta2 = x - mean               ← uses UPDATED mean
  M2    += delta × delta2

Variance     = M2 / (count - 1)   ← sample variance (Bessel's correction)
Pop Variance = M2 / count
Std Dev      = sqrt(Variance)
```

```
  Why Welford is stable:

  Naive:  var = sum(x²)/n - (sum(x)/n)²
          With values near 1,000,000 and variance ~1:
          sum(x²)/n ≈ 1,000,000,000,000
          (sum(x)/n)² ≈ 1,000,000,000,000
          Difference ≈ 1 ... but floating point loses precision

  Welford: tracks deviations from running mean
           Never computes large sums that cancel
           Stable for ANY offset + variance combination
```

### Chan's Merge

Two independent Welford accumulators can be merged in O(1):

```
combined.count = a.count + b.count
delta = b.mean - a.mean
combined.mean = weighted average of a.mean and b.mean
combined.M2 = a.M2 + b.M2 + delta² × a.count × b.count / combined.count
```

This enables splitting work across threads or time windows and merging
the results without loss of precision.

## Configuration

```rust
// No configuration needed — just create and update
let mut stats = Welford::new();

for sample in data {
    stats.update(sample);
}

println!("n={}, mean={:.2}, std_dev={:.2}",
    stats.count(),
    stats.mean().unwrap(),
    stats.std_dev().unwrap(),
);
```

### Merging

```rust
let mut worker_a = Welford::new();
let mut worker_b = Welford::new();

// Split work
for x in &data[..half] { worker_a.update(*x); }
for x in &data[half..] { worker_b.update(*x); }

// Merge
worker_a.merge(&worker_b);
// worker_a now has stats for the full dataset
```

## Examples by Domain

### Signal-to-Noise Ratio

```rust
let mut stats = Welford::new();

// On each observation:
stats.update(measurement);

if let (Some(mean), Some(std)) = (stats.mean(), stats.std_dev()) {
    let snr = mean / std;  // signal-to-noise ratio
}
```

### Networking — Latency Statistics

```rust
let mut latency_stats = Welford::new();

// Per-request:
latency_stats.update(response_time_ms);

if let Some(std) = latency_stats.std_dev() {
    // Z-score of current request:
    let z = (response_time_ms - latency_stats.mean().unwrap()) / std;
}
```

### SRE — Per-Endpoint Statistics with Merge

```rust
// Each worker tracks its own stats
let mut per_worker: Vec<Welford> = (0..num_workers)
    .map(|_| Welford::new())
    .collect();

// Periodically merge for global view
let mut global = Welford::new();
for w in &per_worker {
    global.merge(w);
}
```

## Performance

| Operation | p50 | p99 |
|-----------|-----|-----|
| `Welford::update` | 13 cycles | 13 cycles |
| `Welford::std_dev` query | 7 cycles | 7 cycles |

The update includes one division (`delta / count`). The `std_dev()` query
includes one `sqrt` (hardware `vsqrtsd`, ~13 cycles latency but pipelined).

## Academic Reference

Welford, B.P. "Note on a Method for Calculating Corrected Sums of Squares
and Products." *Technometrics* 4.3 (1962): 419-420.

Chan, T.F., Golub, G.H., and LeVeque, R.J. "Updating Formulae and a
Pairwise Algorithm for Computing Sample Variances." *Technical Report
STAN-CS-79-773*, Stanford University (1979).
