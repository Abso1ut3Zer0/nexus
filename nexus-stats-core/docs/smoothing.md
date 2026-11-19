# Smoothing

Base smoothing primitives. Module path: `nexus_stats_core::smoothing`. For anything beyond these — Holt, KAMA, Kalman1d, Spring, Huber, Hampel, WindowedMedian — see [`nexus-stats-smoothing`](../../nexus-stats-smoothing/docs/INDEX.md).

## At a glance

| Type | What it does | Notes |
|------|--------------|-------|
| `Ema` | Classic exponentially-weighted moving average | Builder: alpha, halflife or span |
| `AsymEma` | Different alpha for rising vs falling samples | Drawdown-aware |
| `Slew<f64>` / `Slew<i64>` | Hard rate-of-change clamp | Not statistical — deterministic |

---

## EMA

The classic `y_t = alpha * x_t + (1 - alpha) * y_{t-1}`. The first sample initializes the average.

```rust
use nexus_stats_core::smoothing::Ema;

let mut ema = Ema::builder().alpha(0.25).build().unwrap();
let stream = [8.0, 16.0, 2.0];
let smoothed: Vec<Option<f64>> =
    stream.into_iter().map(|x| ema.update(x).unwrap()).collect();
assert_eq!(smoothed, [Some(8.0), Some(10.0), Some(8.0)]);
```

Set the weight one of three ways: `alpha(a)` with `a` in (0, 1), `halflife(h)` in samples (positive, needs `std` or `libm`), or `span(n)` with `n >= 2` (the pandas `span`, `alpha = 2 / (n + 1)`). A bad value is reported by `build()` under the name of the knob you set.

`min_samples(n)` withholds the value (`None`) until `n` samples have been fed.

### Seeding

`seed(v)` starts the average at `v`, as if it had already converged there. A seed is a value, not samples:

```rust
use nexus_stats_core::smoothing::Ema;

let mut ema = Ema::builder().alpha(0.25).min_samples(10).seed(100.0).build().unwrap();
assert_eq!(ema.value(), Some(100.0)); // available at once; min_samples no longer applies
assert_eq!(ema.count(), 0);           // no sample has been fed
assert_eq!(ema.update(200.0).unwrap(), Some(125.0)); // smoothed into the seed
ema.reset();
assert_eq!(ema.value(), Some(100.0)); // reset returns to the as-built state
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

let latencies = [100.0, 100.0, 400.0, 100.0];
for us in latencies { aema.update(us).unwrap(); }
// The spike pulled the value up fast (span 5); one sample of recovery has
// barely moved it back (span 50).
assert!(aema.value().unwrap() > 190.0);
```

**Use for:** SLO monitoring (stay on top of degradations, don't flap on recoveries), drawdown tracking, queue-depth monitoring.

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
- Streaming variance around an EMA: [`EwmaVar`](statistics.md#ewmavar--exponentially-weighted-variance).
