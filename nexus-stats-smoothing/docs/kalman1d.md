# Kalman1d — Scalar Kalman Filter

**Types:** `Kalman1dF64`
**Import:** `use nexus_stats_smoothing::Kalman1dF64;`
**Feature flags:** None required.

## What it does

A 1D Kalman filter with position + velocity state. Under Gaussian process and measurement noise, it's the *optimal* linear estimator of both. You provide:

- `q` (process noise variance) — how much the true state is expected to change per step beyond constant velocity.
- `r` (measurement noise variance) — sensor noise variance.

The filter tracks an internal position estimate, velocity estimate, and covariance matrix, updating them via the standard Kalman predict / update equations on every sample.

## When to use it

- You genuinely know your noise model (e.g. from a stationary calibration run).
- You need a **velocity estimate**, not just a smoothed position.
- You want formal optimality guarantees under Gaussian assumptions.

Not for: guessing-at-parameters workflows (use Holt), heavy-tailed noise (Kalman assumes Gaussian; use `HuberEmaF64` or `HampelF64`), multivariate state (use `Kalman2dF64`/`Kalman3dF64` from `nexus-stats-regression`).

## API

```rust
impl Kalman1dF64 {
    pub fn builder() -> Kalman1dF64Builder;
    pub fn update(&mut self, measurement: f64) -> Result<Option<(f64, f64)>, DataError>;
    pub fn position(&self) -> Option<f64>;
    pub fn velocity(&self) -> Option<f64>;
    pub fn uncertainty(&self) -> f64;
    pub fn count(&self) -> u64;
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}

impl Kalman1dF64Builder {
    pub fn process_noise(self, q: f64) -> Self;      // required
    pub fn measurement_noise(self, r: f64) -> Self;  // required
    pub fn min_samples(self, min: u64) -> Self;
    pub fn seed(self, position: f64, velocity: f64) -> Self;
    pub fn build(self) -> Result<Kalman1dF64, ConfigError>;
}
```

## Example — position tracking from noisy sensor

```rust
use nexus_stats_smoothing::Kalman1dF64;

// Noisy measurements of a slowly-moving target.
let measurements: [f64; 10] = [
    10.2, 10.5, 10.9, 11.3, 11.6, 12.1, 12.4, 12.9, 13.2, 13.6,
];

// r calibrated from a stationary period: sensor stddev ~ 0.3, so var ~ 0.09.
// q chosen small: true motion is slow and roughly constant-velocity.
let mut kf = Kalman1dF64::builder()
    .process_noise(0.001)
    .measurement_noise(0.09)
    .build()
    .expect("valid params");

for &z in &measurements {
    kf.update(z).unwrap();
}

println!(
    "position={:.3} velocity={:.3}/step uncertainty={:.4}",
    kf.position().unwrap(),
    kf.velocity().unwrap(),
    kf.uncertainty(),
);
```

## Parameter tuning

- The filter only cares about the *ratio* `q / r`. Fix `r = (sensor_stddev)^2` and sweep `q` until the output looks right.
- Small `q/r` → heavy smoothing, slow to respond.
- Large `q/r` → light smoothing, noisy.
- Calibrate `r` by running `Welford` on residuals during a stationary period: `r ~ welford.variance()`.

See [parameter-tuning.md](parameter-tuning.md#kalman1d-process-noise-and-measurement-noise).

## Caveats

- Assumes Gaussian noise. Heavy-tailed (market returns, sensor flakes) will bias the estimate — pre-filter with `HampelF64`.
- Assumes constant-velocity dynamics. If the true state has acceleration, bump `q` (the filter will absorb unmodeled dynamics as process noise).
- `velocity()` is per-*step*, not per-unit-time. If your samples aren't at fixed intervals, build a proper state-space model instead.

## Cross-references

- [Kalman2d / Kalman3d](../../nexus-stats-regression/docs/estimation.md) — multivariate state.
- [Holt](holt.md) — level + trend without a formal noise model.
- [Spring](spring.md) — deterministic chase, no statistics.
