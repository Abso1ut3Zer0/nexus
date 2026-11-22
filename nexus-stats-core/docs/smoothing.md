# Smoothing

The module docs for `nexus_stats_core::smoothing` list every type and say which to use, and each type's own docs give its contract. This page covers only the types whose docs have not moved there yet. For Holt, KAMA, Kalman1d, Spring, Hampel and WindowedMedian see [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).

---

## Slew

A hard clamp on rate of change: output can change by at most `max_rate` per update. `Slew<f64>` and `Slew<i64>`.

```rust
use nexus_stats_core::smoothing::Slew;

let mut slew = Slew::<f64>::new(10.0).unwrap(); // at most 10 per step
let targets = [100.0, 200.0, 200.0, 105.0];
let output: Vec<f64> = targets.into_iter().map(|t| slew.update(t).unwrap()).collect();
// The first sample passes through; after that each step is clamped to 10.
assert_eq!(output, [100.0, 110.0, 120.0, 110.0]);
```

`value()` is the last output, or `None` before the first sample.

**Use for:** rate-limited control setpoints, slew-limited UI, guaranteed-bounded step size for safety.

**Caveats:** deterministic, not statistical — noise passes straight through, just slowly. Combine with an EMA if the input is noisy.

---

## Integer form

`Slew<i64>` is the integer instantiation of the same type, for hot paths where the value is already an integer (ticks, fixed-point prices). Same interface, except `update` does not return `Result`: there is no NaN to guard against, and the allowed band saturates at the `i64` bounds instead of overflowing. The smoothers (`Ema`, `AsymEma`) are `f64` only.

---

## Cross-references

- Advanced smoothers — Holt, KAMA, Kalman1d, Spring, Huber, Hampel, WindowedMedian — all in [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).
