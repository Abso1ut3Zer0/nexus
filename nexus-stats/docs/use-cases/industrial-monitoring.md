# Use Case: Industrial Monitoring

Sensor validation, process control, and equipment health for industrial
and IoT systems.

## Recipe: Sensor Input Validation

```rust
use nexus_stats::smoothing::Slew<f64>;
use nexus_stats::detection::RobustZScoreF64;
use nexus_stats::control::DeadBand<f64>;

// Hard limits (physical impossibility)
let mut slew = Slew::<f64>::new(10.0);  // max 10°C change per sample

// Statistical outlier detection
let mut robust = RobustZScoreF64::builder()
    .span(100).reject_threshold(5.0).build().unwrap();

// Stuck sensor detection
let mut dead_band = DeadBand::<f64>::new(0.01);  // report if > 0.01°C change

let clamped = slew.update(reading);
let z = robust.update(clamped);
let changed = dead_band.update(clamped);

if changed.is_none() {
    stuck_counter += 1;
    if stuck_counter > 60 {
        alert("sensor stuck — no change in 60 readings");
    }
} else {
    stuck_counter = 0;
}
```

## Recipe: Process Drift Detection

```rust
use nexus_stats::Direction;
use nexus_stats::detection::Cusum;
use nexus_stats::control::DebounceU32;

// CUSUM for detecting drift from setpoint
let mut drift = Cusum::builder(setpoint)
    .slack(tolerance * 0.5)
    .threshold(tolerance * 5.0)
    .build().unwrap();

// Debounce for confirmed out-of-spec
let mut confirmed = DebounceU32::new(5);

if let Some(shift) = drift.update(measurement) {
    if matches!(shift, Direction::Rising | Direction::Falling) {
        if confirmed.update(true) {
            alert_process_drift(shift);
        }
    }
} else {
    confirmed.update(false);
}
```

## Primitives Used

| Primitive | Role |
|-----------|------|
| [SlewLimiter](../algorithms/slew.md) | Physical rate-of-change limits |
| [RobustZScore](../algorithms/robust-z-score.md) | Outlier detection |
| [DeadBand](../algorithms/dead-band.md) | Stuck sensor detection |
| [CUSUM](../algorithms/cusum.md) | Process drift |
| [Debounce](../algorithms/debounce.md) | Confirm out-of-spec |
| [Hysteresis](../algorithms/hysteresis.md) | Clean on/off control decisions |
