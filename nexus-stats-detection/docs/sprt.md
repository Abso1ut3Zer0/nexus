# SPRT — Sequential Probability Ratio Test

**Types:** `SprtBernoulli`, `SprtGaussian`
**Module path:** `nexus_stats_detection::estimation`
**Feature flags:** `std` or `libm`.

Wald's sequential probability ratio test. Given two hypotheses `H0` and `H1` and pre-specified type I and type II error bounds, SPRT minimizes the expected number of samples to reach a decision by stopping as soon as the evidence is strong enough.

## When to use it

- **Online A/B testing.** Compare two variants without fixing the sample count in advance. Stop early when the evidence is clear.
- **Quality control.** "Is this batch of samples from the good distribution or the bad one?"
- **Early-stopped experiments.** Minimize samples-to-decision while guaranteeing error rates.

## SprtBernoulli — success/failure rates

Test whether an underlying success probability is `p0` (H0) or `p1` (H1).

### API

```rust
use nexus_stats_detection::estimation::SprtBernoulli;

pub enum Decision { Continue, Accept, Reject }

impl SprtBernoulli {
    pub fn builder() -> SprtBernoulliBuilder;
    pub fn update(&mut self, success: bool) -> Decision;
    pub fn is_decided(&self) -> bool;
    pub fn reset(&mut self);
}

impl SprtBernoulliBuilder {
    pub fn p0(self, p0: f64) -> Self;
    pub fn p1(self, p1: f64) -> Self;
    pub fn alpha(self, alpha: f64) -> Self;  // P(reject H0 | H0 true)
    pub fn beta(self, beta: f64) -> Self;    // P(accept H0 | H1 true)
    pub fn build(self) -> Result<SprtBernoulli, ConfigError>;
}
```

### Example — fill rate A/B test

```rust
use nexus_stats_detection::estimation::{SprtBernoulli, Decision};

// H0: fill rate is 0.75 (current)
// H1: fill rate is 0.85 (new quoter)
// type I error 5%, type II error 10%
let mut sprt = SprtBernoulli::builder()
    .null_rate(0.75)
    .alt_rate(0.85)
    .alpha(0.05)
    .beta(0.10)
    .build()
    .unwrap();

let mut count = 0;
for filled in observed_fills {
    count += 1;
    match sprt.update(filled) {
        Decision::Continue => {}
        Decision::Accept => { println!("after {count} samples: accept H0 (old is fine)"); break; }
        Decision::Reject => { println!("after {count} samples: reject H0 (new is better)"); break; }
    }
}
```

SPRT stops at the smallest sample count that distinguishes 75% vs 85% at the specified error bounds — typically 20-100 samples, compared to 300+ for a fixed-sample test.

## SprtGaussian — continuous means

Test whether the mean of a Gaussian stream is `mu_0` (H0) or `mu_1` (H1), at known variance.

### API

```rust
use nexus_stats_detection::estimation::SprtGaussian;

impl SprtGaussian {
    pub fn builder() -> SprtGaussianBuilder;
    pub fn update(&mut self, value: f64) -> Result<Decision, DataError>;
    pub fn is_decided(&self) -> bool;
}
```

### Example — latency regression

```rust
use nexus_stats_detection::estimation::{SprtGaussian, Decision};

// H0: deploy didn't regress (mean 120us)
// H1: deploy regressed by 10us (mean 130us)
// variance known from historical data (sigma 5us)
let mut sprt = SprtGaussian::builder()
    .null_mean(120.0)
    .alt_mean(130.0)
    .variance(25.0)
    .alpha(0.01)
    .beta(0.05)
    .build()
    .unwrap();

for latency in latencies {
    match sprt.update(latency).unwrap() {
        Decision::Continue => {}
        Decision::Accept => { println!("deploy safe"); break; }
        Decision::Reject => { rollback(); break; }
    }
}
```

## Caveats

- **You must specify H1 in advance.** SPRT is a two-hypothesis test, not a general-purpose anomaly detector.
- **Errors are rates, not guarantees per test.** If you run 100 SPRTs with alpha = 0.05, expect ~5 false rejects.
- **Gaussian variant needs known variance.** Estimate from calibration data; feeding the wrong sigma skews decisions.
- **Reset between experiments.** A decided test stays decided until `reset()`.

## Cross-references

- `ErrorRate` — rolling error fraction without sequential-test machinery.
- `HitRate` — directional accuracy of a signal, with no test of significance.
- For multiple comparisons or continuous thresholds, use `AdaptiveThreshold` or `MultiGate` instead.
