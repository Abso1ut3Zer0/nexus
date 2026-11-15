# SPRT — Sequential Probability Ratio Test

Wald's sequential analysis. Makes statistically rigorous decisions
from streaming data with controlled error rates and minimal samples.

| Property | Value |
|----------|-------|
| Update cost | 19 cycles |
| Memory | 48-88 bytes |
| Types | `SprtBernoulli`, `SprtGaussian` |
| Priming | Immediate (can decide after 1 observation) |
| Output | `Decision::Continue`, `AcceptNull`, `AcceptAlternative` |
| Feature | `std\|libm` (ln at construction) |

## What It Does

Tests two competing hypotheses from streaming observations.
After each observation, it either makes a decision or continues
collecting data. Mathematically optimal — uses the minimum
number of observations needed for the desired confidence level.

**SprtBernoulli** — compares two success rates. "Is the rate
p₁ (alternative) or p₀ (null)?"

**SprtGaussian** — compares two means with known variance.
"Is the mean μ₁ or μ₀?"

Both precompute decision boundaries from the desired Type I (α)
and Type II (β) error rates. Updates are one addition + two
comparisons — no transcendentals on the hot path.

F64 only — log-likelihood accumulation requires high precision.

## When to Use It

**Use SPRT when:**
- You need to decide between two hypotheses as fast as possible
- You want controlled false positive AND false negative rates
- You're comparing a current metric against a baseline
- Sample efficiency matters (each observation is expensive or slow)

**Don't use SPRT when:**
- You need continuous monitoring without a decision → use [CUSUM](cusum.md)
- You're comparing distributions, not point hypotheses → use [Moments](moments.md)
- You need an estimate, not a decision → use [BetaBinomial](bayesian.md)

## How It Works

```
Log-likelihood ratio: L = Σ log(P(xᵢ | H₁) / P(xᵢ | H₀))

Decision boundaries:
  Upper: A = ln((1-β)/α)     → accept H₁
  Lower: B = ln(β/(1-α))     → accept H₀

After each observation:
  L += log-odds increment
  if L >= A: accept alternative
  if L <= B: accept null
  otherwise: continue
```

For Bernoulli: increments are precomputed `ln(p₁/p₀)` (success)
and `ln((1-p₁)/(1-p₀))` (failure). Update is pure addition.

For Gaussian: increment is `(μ₁-μ₀)/(2σ²) × (2x - μ₀ - μ₁)`.
One multiply-add per update.

## Configuration

### Bernoulli

```rust
use nexus_stats::estimation::SprtBernoulli;

let mut test = SprtBernoulli::builder()
    .null_rate(0.50)      // H₀: rate = 50%
    .alt_rate(0.55)       // H₁: rate = 55%
    .alpha(0.05)          // 5% false positive rate
    .beta(0.05)           // 5% false negative rate
    .build()
    .unwrap();

// Feed observations:
for outcome in observations {
    match test.update(outcome) {
        Decision::AcceptAlternative => {
            println!("rate is significantly above 50%");
            break;
        }
        Decision::AcceptNull => {
            println!("no evidence rate differs from 50%");
            break;
        }
        Decision::Continue => {}
    }
}
```

### Gaussian

```rust
use nexus_stats::estimation::SprtGaussian;

let mut test = SprtGaussian::builder()
    .null_mean(100.0)     // H₀: mean = 100
    .alt_mean(105.0)      // H₁: mean = 105
    .variance(25.0)       // known variance
    .alpha(0.05)
    .beta(0.05)
    .build()
    .unwrap();

for value in measurements {
    match test.update(value).unwrap() {
        Decision::AcceptAlternative => {
            println!("mean has shifted to ~105");
            break;
        }
        _ => {}
    }
}
```

## Examples by Domain

### Monitoring — A/B Testing

```rust
// Is the new configuration better than the old one?
let mut test = SprtBernoulli::builder()
    .null_rate(0.72)    // current success rate
    .alt_rate(0.76)     // minimum improvement worth detecting
    .alpha(0.05)
    .beta(0.10)
    .build()
    .unwrap();

// Feed results from the new configuration:
let decision = test.update(request_succeeded);
// SPRT stops as soon as it has enough evidence —
// typically 50-200 observations for this effect size.
```

### Networking — Latency Shift Detection

```rust
let mut test = SprtGaussian::builder()
    .null_mean(50.0)     // baseline: 50μs
    .alt_mean(55.0)      // detect 10% increase
    .variance(100.0)     // known latency variance
    .alpha(0.01)
    .beta(0.01)
    .build()
    .unwrap();

// Per request:
let decision = test.update(latency_us).unwrap();
```

## SPRT vs CUSUM

| | SPRT | CUSUM |
|---|---|---|
| Purpose | One-time decision | Continuous monitoring |
| Output | Accept/Reject/Continue | Direction (Rising/Falling) |
| Resets | No (sticky decision) | Yes (after each detection) |
| Use case | "Has it changed?" | "When does it change?" |

SPRT decides once and stops. CUSUM monitors forever.
Use SPRT for experiments, CUSUM for alerting.

## Performance

| Operation | p50 |
|-----------|-----|
| `SprtBernoulli::update` | 19 cycles |
| `SprtGaussian::update` | 7 cycles |
| Builder (one-time) | ~50 cycles (includes ln) |

## Academic Reference

Wald, A. "Sequential Tests of Statistical Hypotheses." *Annals of
Mathematical Statistics* 16.2 (1945): 117-186.
