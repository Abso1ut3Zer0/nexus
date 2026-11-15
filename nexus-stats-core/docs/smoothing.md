# Smoothing

Base smoothing primitives. Module path: `nexus_stats_core::smoothing`. For anything beyond these — Holt, KAMA, Kalman1d, Spring, Huber, Hampel, WindowedMedian — see [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).

## At a glance

| Type | What it does | Notes |
|------|--------------|-------|
| `Ema` | Classic exponentially-weighted moving average | Builder, halflife or alpha |
| `AsymEma` | Different alpha for rising vs falling samples | Drawdown-aware |
| `Slew<f64>` / `Slew<i64>` | Hard rate-of-change clamp | Not statistical — deterministic |

---

## EMA

The classic `y_t = alpha * x_t + (1 - alpha) * y_{t-1}`.

```rust
use nexus_stats_core::smoothing::Ema;

let mut ema = Ema::builder().halflife(50.0).build().unwrap();
for sample in stream { ema.update(sample).unwrap(); }
let smoothed = ema.value().unwrap();
```

**Use for:** the default single-signal smoother. Parameter selection is about half-life — see [umbrella parameter guide](../../nexus-stats/docs/guides/parameter-tuning.md).

**Caveats:** lags trending signals. If your signal has drift, reach for [`Holt`](../../nexus-stats-smoothing/docs/holt.md) instead.

---

## AsymEMA

Two different alphas: one for `sample > current`, one for `sample < current`. Useful when you want to react fast to degradation but smooth slowly on recovery (or vice versa).

```rust
use nexus_stats_core::smoothing::AsymEma;

let mut aema = AsymEma::builder()
    .span_up(5)      // react fast to latency going up
    .span_down(50)   // smooth the recovery
    .build()
    .unwrap();

for us in latencies { aema.update(us).unwrap(); }
```

**Use for:** SLO monitoring (stay on top of degradations, don't flap on recoveries), drawdown tracking, queue-depth monitoring.

---

## Slew

A hard clamp on rate of change: output can change by at most `max_rate` per update. `Slew<f64>` and `Slew<i64>`.

```rust
use nexus_stats_core::smoothing::Slew;

let mut slew = Slew::<f64>::new(0.01).unwrap(); // max change of 0.01 per step
for setpoint in targets {
    let output = slew.update(setpoint).unwrap();
    // `output` tracks `setpoint` but never moves more than 0.01 per step.
}
```

**Use for:** rate-limited control setpoints, slew-limited UI, guaranteed-bounded step size for safety.

**Caveats:** deterministic, not statistical — noise passes straight through, just slowly. Combine with an EMA if the input is noisy.

---

## Integer form

`Slew<i64>` is the integer instantiation of the same type, for hot paths where the value is already an integer (ticks, fixed-point prices). Same interface, except `update` does not return `Result`: there is no NaN to guard against. The smoothers (`Ema`, `AsymEma`) are `f64` only.
- Parameters are still converted from half-life at builder time.

---

## Cross-references

- Advanced smoothers — Holt, KAMA, Kalman1d, Spring, Huber, Hampel, WindowedMedian — all in [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).
- Streaming variance around an EMA: [`EwmaVar`](statistics.md#ewmavarf64--exponentially-weighted-variance).
