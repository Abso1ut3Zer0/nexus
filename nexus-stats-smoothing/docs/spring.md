# Spring — Critically Damped Chase

**Types:** `Spring`
**Import:** `use nexus_stats_smoothing::Spring;`
**Feature flags:** None required.

## What it does

A critically-damped 2nd-order spring: given a target, the current value chases it smoothly and is *guaranteed never to overshoot*. Parameterized by "smooth time" — half-life for the error to halve.

This is not a statistical smoother. There's no noise model. It's a deterministic low-pass that follows a (possibly moving) setpoint.

## When to use it

- **UI animations.** Panel slides, camera tracking, scroll momentum.
- **Setpoint following.** Smoothed target for a control loop.
- **Slew-limited references.** Target hedge ratios, position scales, bandwidth quotas.

Not for: denoising a measurement (the spring has no input-noise awareness; you feed it a target, not a noisy sample).

## API

```rust
impl Spring {
    pub fn new(smooth_time: f64) -> Result<Self, ConfigError>;
    pub fn update(&mut self, target: f64, dt: f64) -> Result<f64, DataError>;
    pub fn value(&self) -> f64;
    pub fn velocity(&self) -> f64;
    pub fn reset(&mut self);
    pub fn reset_to(&mut self, value: f64);
}
```

`dt` is the time step in the same units as `smooth_time`. Pass `1.0` if you're driving the spring once per sample and `smooth_time` is in samples.

## Example — smooth target following

```rust
use nexus_stats_smoothing::Spring;

// 10-sample half-life. Pass dt=1.0 per update to measure time in samples.
let mut spring = Spring::new(10.0).expect("smooth_time > 0");
spring.reset_to(0.0);

// Step change target 0 -> 100.
for step in 0..40 {
    spring.update(100.0, 1.0).unwrap();
    if step % 5 == 0 {
        println!("step={step} value={:.2} velocity={:.2}", spring.value(), spring.velocity());
    }
}
// value approaches 100.0 monotonically. No overshoot.
```

## Parameter tuning

Pick `smooth_time` to match how fast you want the response:

- `smooth_time = 5.0` — snappy, good for UI.
- `smooth_time = 30.0` — slow, good for setpoint following where operators see the motion.
- `smooth_time = 100.0` — very slow, good for hedge-ratio drift.

Steady-state error is zero; only transient dynamics change.

## Caveats

- **No noise rejection.** Feed it a clean target. If your target is noisy, pre-filter with an EMA.
- **dt matters.** If your update cadence is irregular, you must pass accurate `dt`s or the response rate will be wrong.
- **Not invariant to unit scale.** `smooth_time` is in the same units as `dt`.

## Cross-references

- [SlewLimiter](../../nexus-stats-core/docs/smoothing.md#slew) — hard rate clamp, not a second-order system.
- [EMA](../../nexus-stats-core/docs/smoothing.md#ema) — first-order, statistical smoother.
