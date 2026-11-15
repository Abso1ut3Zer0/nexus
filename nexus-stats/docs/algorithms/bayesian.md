# Bayesian Inference — Conjugate Prior Updates

Online Bayesian rate estimation with credible intervals.
O(1) per update, 16-32 bytes, pure arithmetic.

| Property | Value |
|----------|-------|
| Update cost | ~3 cycles |
| Types | `BetaBinomial/F32`, `GammaPoisson/F32` |
| Memory | 32 bytes (f64) |
| Priming | After 1 observation |
| Output | `mean()`, `variance()`, `credible_interval()` |
| Feature | none (core), `std\|libm` for `credible_interval` |

## What They Do

Conjugate priors give you Bayesian rate estimation for free.
Instead of just a point estimate ("success rate = 73%"), you get
a full posterior distribution with uncertainty ("success rate =
73% ± 4% at 95% confidence").

**Beta-Binomial** — for success/failure rates. Each observation
is binary (success or failure). The posterior is a Beta distribution
that gets sharper with more data.

**Gamma-Poisson** — for event rates. Each observation is a count
over some exposure time. The posterior is a Gamma distribution.

Both update in O(1) — just increment two parameters.

## When to Use Them

**Use Beta-Binomial when:**
- You're tracking a binary outcome rate (fill rate, error rate, uptime)
- You need confidence intervals, not just point estimates
- You want a principled way to combine prior knowledge with data

**Use Gamma-Poisson when:**
- You're tracking an event rate (messages/sec, orders/min)
- You need uncertainty on the rate estimate
- Events arrive in batches with varying observation windows

**Don't use these when:**
- You need smoothed values → use [EMA](ema.md) (cheaper, no Bayesian overhead)
- You need change detection → use [CUSUM](cusum.md)
- Your data is continuous, not count-based → use [Welford](welford.md)

## How They Work

### Beta-Binomial

```
Prior: Beta(α₀, β₀)
On success: α += 1
On failure: β += 1

Posterior mean = α / (α + β)
Posterior variance = αβ / ((α+β)²(α+β+1))

Credible interval: normal approximation
  mean ± z * sqrt(variance)
  (accurate for n > 30)
```

### Gamma-Poisson

```
Prior: Gamma(α₀, β₀)
On observing k events in t time units:
  α += k
  β += t

Posterior rate = α / β
Posterior variance = α / β²
```

## Configuration

### Beta-Binomial

```rust
use nexus_stats::estimation::BetaBinomial;

// Uniform prior (no prior knowledge)
let mut rate = BetaBinomial::new();

// Informative prior (strong belief rate ≈ 0.7)
let mut rate = BetaBinomial::with_prior(70.0, 30.0);

// Observe outcomes:
rate.observe(true);   // success
rate.observe(false);  // failure

// Batch update:
rate.observe_batch(95, 5);  // 95 successes, 5 failures

println!("rate: {:.3}", rate.mean());
println!("95% CI: {:?}", rate.credible_interval(0.95));
```

### Gamma-Poisson

```rust
use nexus_stats::estimation::GammaPoisson;

let mut event_rate = GammaPoisson::new();

// Observed 15 events in 3 seconds
event_rate.observe(15, 3.0);

// Observed 22 events in 5 seconds
event_rate.observe(22, 5.0);

println!("rate: {:.1} events/sec", event_rate.rate());
println!("95% CI: {:?}", event_rate.credible_interval(0.95));
```

## Examples by Domain

### Monitoring — Error Rate with Confidence

```rust
let mut errors = BetaBinomial::new();

// Per request:
errors.observe(request_succeeded);

if let Some((lo, hi)) = errors.credible_interval(0.95) {
    let error_rate = 1.0 - errors.mean();
    // "Error rate: 2.3% (95% CI: 1.8% - 3.1%)"
    // The CI tells you how much data you have.
    // Wide CI → need more observations before acting.
}
```

### Networking — Packet Rate Estimation

```rust
let mut packet_rate = GammaPoisson::new();

// Per measurement window (1 second):
packet_rate.observe(packets_received, 1.0);

// Rate estimate stabilizes after a few windows.
// CI narrows as you accumulate more exposure time.
```

## Credible Interval Accuracy

The credible interval uses a normal approximation to the
Beta/Gamma posterior. This is accurate for moderate sample sizes
(n > 30) but can be poor for very small n or extreme rates
(near 0 or 1).

For n < 30, the true posterior is skewed and the symmetric normal
CI over-covers on one side, under-covers on the other. Use these
numbers for monitoring, not statistical inference at small n.

## Performance

| Operation | p50 |
|-----------|-----|
| `observe()` | ~3 cycles |
| `mean()` | ~3 cycles |
| `credible_interval()` | ~15 cycles (includes sqrt + rational approx) |
