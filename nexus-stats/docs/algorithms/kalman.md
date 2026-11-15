# Kalman Filters — Multivariate State Estimation

2-state and 3-state Kalman filters with time-varying observation
models. Hardcoded small-matrix math — no generic linear algebra.

| Type | States | Memory | Update cost |
|------|--------|--------|-------------|
| `Kalman2d/F32` | 2 | ~88 bytes | ~20 multiply-adds |
| `Kalman3d/F32` | 3 | ~160 bytes | ~50 multiply-adds |

No feature gates. Pure arithmetic. `no_std` compatible.

For scalar (1-state) Kalman, see [Kalman1D](kalman1d.md).

## What They Do

Track multiple correlated hidden states from noisy observations.
The user provides the observation and a design vector (H) at each
step, telling the filter how the observation relates to the state.

**Kalman2d** — 2 states. The most common case: level + trend,
position + velocity, or any pair of correlated quantities.

**Kalman3d** — 3 states. Position + velocity + acceleration, or
any triple of related quantities.

The filter maintains both the state estimate AND a covariance
matrix that quantifies uncertainty. As more data arrives, the
covariance shrinks — the filter becomes more confident.

## When to Use Them

**Use Kalman2d when:**
- You need to jointly track two related quantities
- You want uncertainty estimates on both states
- The observation model changes over time (time-varying H)
- You need optimal filtering (minimum variance estimate)

**Use Kalman3d when:**
- You need position + velocity + acceleration tracking
- Three correlated states need joint estimation

**Don't use multivariate Kalman when:**
- You only need to track one quantity → use [Kalman1D](kalman1d.md)
- You need to track more than 3 states → consider RLS or an external Kalman library
- You don't need uncertainty → use [EMA](ema.md) or [Holt](holt.md)

## How It Works

```
State:   x (N-vector)
Cov:     P (N×N matrix)
Process: Q (N×N process noise)
Meas:    R (scalar measurement noise)

Predict:
  P = P + Q               (state is identity dynamics by default)

Update:
  y = observation - H·x       (innovation)
  S = H·P·Hᵀ + R              (innovation covariance)
  K = P·Hᵀ / S                (Kalman gain, N-vector)
  x = x + K·y                 (state update)
  P = (I - K·Hᵀ)·P            (covariance update)
```

For 2d, every operation is explicit arithmetic (no loops).
For 3d, short loops (0..3) for readability.

### Numerical Stability

The covariance matrix P stays symmetric positive definite with
valid inputs. An epsilon floor on the innovation variance S
prevents NaN propagation if P degrades numerically after many
updates. For very long-running filters with ill-conditioned
observations, periodic reset or Joseph form covariance update
may be needed.

## Configuration

### Kalman2d

```rust
use nexus_stats::estimation::Kalman2d;

let mut kf = Kalman2d::builder()
    .process_noise([[0.001, 0.0], [0.0, 0.001]])
    .measurement_noise(1.0)
    .initial_state([0.0, 0.0])
    .initial_covariance([[100.0, 0.0], [0.0, 100.0]])
    .build()
    .unwrap();

// Predict (propagate uncertainty):
kf.predict();

// Update with observation and design vector:
// observation = h[0]*state[0] + h[1]*state[1] + noise
kf.update(observation, [1.0, 0.0]);  // observing state[0] directly

println!("state: {:?}", kf.state());
println!("covariance: {:?}", kf.covariance());
```

### Kalman3d

```rust
use nexus_stats::estimation::Kalman3d;

let mut kf = Kalman3d::builder()
    .process_noise([
        [0.001, 0.0, 0.0],
        [0.0, 0.001, 0.0],
        [0.0, 0.0, 0.001],
    ])
    .measurement_noise(1.0)
    .initial_state([0.0, 0.0, 0.0])
    .initial_covariance([
        [100.0, 0.0, 0.0],
        [0.0, 100.0, 0.0],
        [0.0, 0.0, 100.0],
    ])
    .build()
    .unwrap();

kf.predict();
kf.update(observation, [1.0, 0.0, 0.0]);
```

## Design Vectors (H)

The design vector tells the filter how the observation relates
to the hidden state. This is what makes the Kalman filter powerful
— H can change every tick.

| State model | H | What you're observing |
|---|---|---|
| `[level, trend]` | `[1, 0]` | Level directly |
| `[level, trend]` | `[1, dt]` | Level + trend×dt |
| `[alpha, beta]` | `[1, x]` | alpha + beta×x (regression) |
| `[pos, vel, acc]` | `[1, 0, 0]` | Position directly |

The `[1, x]` design vector is the key for online regression:
state tracks the intercept (alpha) and slope (beta), and the
observation is `y = alpha + beta * x + noise`. As x changes
each tick, H changes, and the Kalman filter adapts.

## Examples by Domain

### Monitoring — Level + Trend Tracking

```rust
let mut kf = Kalman2d::builder()
    .process_noise([[0.01, 0.0], [0.0, 0.001]])
    .measurement_noise(5.0)
    .initial_state([0.0, 0.0])
    .initial_covariance([[100.0, 0.0], [0.0, 10.0]])
    .build()
    .unwrap();

// Per observation:
kf.predict();
kf.update(latency_measurement, [1.0, 0.0]);

let [level, trend] = kf.state();
// level = smoothed estimate of current latency
// trend = rate of change
// Both come with uncertainty via covariance()

if trend > 0.5 {
    // Latency trending up at > 0.5 units/tick
    // The covariance tells you how confident this is
}
```

### Signal Processing — Noisy Sensor Fusion

```rust
// State: [true_value, drift_rate]
let mut kf = Kalman2d::builder()
    .process_noise([[0.1, 0.0], [0.0, 0.01]])
    .measurement_noise(10.0)  // noisy sensor
    .initial_state([0.0, 0.0])
    .initial_covariance([[1000.0, 0.0], [0.0, 100.0]])
    .build()
    .unwrap();

// Each sensor reading:
kf.predict();
kf.update(noisy_reading, [1.0, 0.0]);

// kf.state()[0] is the denoised value
// kf.innovation_variance() tells you if the last observation was unusual
```

## Process Noise Tuning

Q (process noise) controls how much the state is allowed to change
between observations. Larger Q = more responsive, noisier. Smaller
Q = smoother, slower to track changes.

| Q magnitude | Behavior |
|---|---|
| Very small (1e-6) | Trusts the model heavily. Slow to respond. |
| Small (1e-3) | Balanced. Good default. |
| Large (1e-1) | Trusts observations heavily. Noisy. |

For level + trend, Q is typically larger for the level (it changes
more) and smaller for the trend (it drifts slowly).

## Separate Predict + Update

Unlike most types in this library, Kalman filters have separate
`predict()` and `update()` methods. This is intentional:

- `predict()` propagates the state forward (adds process noise)
- `update()` incorporates a new observation

Call `predict()` once per time step, then `update()` zero or more
times (if you have observations). Missing observations are handled
naturally by calling `predict()` without `update()` — the
uncertainty grows but the state estimate persists.

## Performance

| Operation | p50 |
|-----------|-----|
| `Kalman2d::predict` | ~8 cycles |
| `Kalman2d::update` | ~20 cycles |
| `Kalman3d::predict` | ~15 cycles |
| `Kalman3d::update` | ~50 cycles |
