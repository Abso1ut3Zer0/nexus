# Optimizers — Online Parameter Optimization

Streaming parameter optimization. The user provides gradients,
the library manages the update rule. Designed for background threads,
not the hot path.

| Type | Per step | Memory | Method |
|------|----------|--------|--------|
| `OnlineGd` | O(d) | 8d bytes | Fixed learning rate gradient descent |
| `AdaGrad` | O(d) | 16d bytes | Per-coordinate adaptive rates |
| `Adam` | O(d) | 24d bytes | Adaptive moments + optional weight decay |

All require `alloc`. AdaGrad and Adam additionally require `std|libm`
(for `sqrt`). F64 only — optimization precision matters.

## What They Do

Optimizers adjust a parameter vector to minimize a loss function,
one gradient step at a time. You compute the gradient (how the loss
changes with each parameter), hand it to the optimizer, and it
updates the parameters using its specific strategy.

**Online GD** — simplest. Steps by `learning_rate × gradient`.
Same rate for every parameter, every step.

**AdaGrad** — adapts the learning rate per parameter. Parameters
with frequently large gradients get smaller rates. Parameters
with rare gradients keep large rates.

**Adam** — tracks both momentum (mean of recent gradients) and
adaptive rates (mean of recent squared gradients). Includes
bias correction for early steps. With `weight_decay > 0`, applies
decoupled weight decay (AdamW).

## When to Use Them

**Use an optimizer when:**
- You have a custom loss function (not squared error or cross-entropy)
- You need regularization (AdamW weight decay)
- You're tuning parameters that don't fit the regression/classifier API

**Use LinearRegression/RLS instead when:**
- Your loss is squared error — these are the optimal solution
- You need per-update speed (RLS is specialized, optimizer is general)

**Use LogisticRegression instead when:**
- Your loss is cross-entropy with binary outcomes — hardcoded is faster

**These are NOT hot-path types.** Run them on a background thread.
Accumulate gradients from a batch of observations, then step once.

## How They Work

### Gradient Descent

```
params[i] -= learning_rate * gradient[i]
```

### AdaGrad

```
sum_sq_grad[i] += gradient[i]²
params[i] -= learning_rate * gradient[i] / (sqrt(sum_sq_grad[i]) + epsilon)
```

The accumulated squared gradient makes the effective learning rate
shrink for frequently-updated parameters.

### Adam

```
m[i] = beta1 * m[i] + (1 - beta1) * gradient[i]        // momentum
v[i] = beta2 * v[i] + (1 - beta2) * gradient[i]²       // adaptive rate

m_hat = m[i] / (1 - beta1^t)                            // bias correction
v_hat = v[i] / (1 - beta2^t)

params[i] -= learning_rate * m_hat / (sqrt(v_hat) + epsilon)

// Optional weight decay (AdamW):
params[i] -= weight_decay * params[i]
```

## Configuration

### Online GD

```rust
use nexus_stats::learning::OnlineGd;

let mut gd = OnlineGd::builder()
    .dimensions(5)
    .learning_rate(0.01)
    .build()
    .unwrap();

// Compute gradient externally, then step:
gd.step(&gradient).unwrap();

println!("params: {:?}", gd.parameters());
```

### AdaGrad

```rust
use nexus_stats::learning::AdaGrad;

let mut ag = AdaGrad::builder()
    .dimensions(5)
    .learning_rate(0.01)
    .epsilon(1e-8)       // default
    .build()
    .unwrap();

ag.step(&gradient).unwrap();
```

### Adam (with optional weight decay)

```rust
use nexus_stats::learning::Adam;

// Standard Adam:
let mut adam = Adam::builder()
    .dimensions(5)
    .learning_rate(0.001)   // default
    .beta1(0.9)             // default
    .beta2(0.999)           // default
    .build()
    .unwrap();

// AdamW (with weight decay):
let mut adamw = Adam::builder()
    .dimensions(5)
    .weight_decay(0.01)
    .build()
    .unwrap();

adam.step(&gradient).unwrap();
```

## Examples by Domain

### Monitoring — Adaptive Signal Combination

```rust
// 3 monitoring signals, learn optimal combination weights
let mut optimizer = Adam::builder()
    .dimensions(3)
    .learning_rate(0.001)
    .build()
    .unwrap();

// Periodically (not every tick):
let features = [signal_a, signal_b, signal_c];
let prediction: f64 = optimizer.parameters().iter()
    .zip(&features)
    .map(|(w, f)| w * f)
    .sum();

// When outcome is observed:
let error = prediction - actual;
let gradient: Vec<f64> = features.iter()
    .map(|f| 2.0 * error * f)
    .collect();
optimizer.step(&gradient).unwrap();
```

### Networking — Adaptive Threshold Tuning

```rust
// Tune an alerting threshold based on false positive/negative feedback
let mut opt = OnlineGd::builder()
    .dimensions(1)
    .learning_rate(0.001)
    .build()
    .unwrap();

// On each alert evaluation:
let threshold = opt.parameters()[0];
if was_false_positive {
    // Gradient: increase threshold (positive gradient)
    opt.step(&[1.0]).unwrap();
} else if was_missed_alert {
    // Gradient: decrease threshold (negative gradient)
    opt.step(&[-1.0]).unwrap();
}
```

## Error Handling

All `step()` methods return `Result<(), DataError>`. NaN or Inf
in any gradient element is rejected — the parameters are unchanged
and the error is returned. This is a data error (the user's loss
function produced NaN), not a programmer error.

Dimension mismatch (gradient length != dimensions) panics.

## Choosing an Optimizer

| Situation | Use |
|---|---|
| First attempt, no tuning | Adam (defaults work well) |
| Sparse gradients | AdaGrad |
| Need regularization | Adam with weight_decay |
| Simplest possible | OnlineGD |
| Squared error loss | Skip optimizer, use RLS/LinearRegression |
| Binary classification | Skip optimizer, use LogisticRegression |

## Performance

| Operation | p50 (d=10) |
|-----------|-----------|
| `OnlineGd::step` | 47 cycles |
| `AdaGrad::step` | 56 cycles |
| `Adam::step` | 203 cycles |

These are cheap — the cost is in computing the gradient, not
applying it.
