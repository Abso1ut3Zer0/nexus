# Integer vs Float

Which types have an `i64` form, what it buys you, and the two rules the
generics impose on callers.

## The rule

Most of nexus-stats is `f64`: anything that divides, smooths with a
fractional weight, or takes a square root (`Ema`, `Welford`, `Cusum`,
`Covariance`, the regressions, ...). Those types have no suffix and no type
parameter.

The cheap primitives whose arithmetic is exact on integers are one generic
type over the sealed `Sample` trait, instantiated for `f64` and `i64`:

| Module | `T: Sample` types |
|--------|-------------------|
| `monitoring` | `Drawdown<T>`, `RunningMax<T>`, `RunningMin<T>`, `WindowedMax<T>`, `WindowedMin<T>`, `MaxGauge<T>`, `PeakHold<T>`, `CoDel<T>`, `Jitter<T>` |
| `control` | `DeadBand<T>`, `Hysteresis<T>`, `LevelCrossing<T>`, `FirstDiff<T>`, `SecondDiff<T>`, `PeakDetector<T>` |
| `smoothing` | `Slew<T>`, `WindowedMedian<T>` |

Timestamps are a third kind. `Liveness`, `EventRate`, `PollSaturation`,
`SojournSaturation`, `DecayAccum` and the `timestamp` argument of the
windowed extrema and `CoDel` take `u64` ticks in any unit; use one clock for
every stamp into one value (`clock::MonotonicClock` is the `std` bridge from
`Instant`, see [no_std](no-std.md) for the rest).

The normalizers (`ZScoreNorm<T>`, `MinMaxNorm<T>`, `QuantileNorm<T>`) and
`RobustZScore<T>` are generic over `Float` (`f64`, `f32`) instead: they take
and return `T` but accumulate in `f64`, so the `f32` form is a boundary type
for `f32` feature vectors, not a cheaper accumulator.

## What the `i64` form changes

- **No `Result`.** `Drawdown<f64>::update` returns `Result<f64, DataError>`
  because NaN and infinity are rejected. `Drawdown<i64>::update` returns
  `i64`: there is nothing to reject.
- **Exact arithmetic.** Comparisons, differences and clamps are exact;
  `DeadBand<i64>` uses `abs_diff`. `Jitter<i64>` smooths with the kernel-style
  bit-shift EMA (weights are powers of two, so `span` rounds to `2^k - 1`;
  `effective_span()` tells you which). `PeakHold<i64>` holds, then drops to
  the current sample; the fractional `decay_rate` exists on `f64` only.
- **No FPU.** Nothing in an `i64` instantiation touches floating point.
- **Same codegen.** The generic body monomorphizes to what the old
  old `I64` types compiled to, verified cycle-identical.

## Two caller rules

The body is written once and the constructors are shared, so the compiler has
to know `T` before the first call whose signature differs by type:

```rust
use nexus_stats::monitoring::{CoDel, Drawdown};

let mut dd = Drawdown::<i64>::new();             // turbofish on the constructor, or
let mut dd2: Drawdown<f64> = Drawdown::new();    // a type annotation on the binding
let mut qd = CoDel::<i64>::builder()
    .target(50_000).interval(100_000_000).build().unwrap();

dd.update(42);                                    // i64: plain value
dd2.update(42.0).unwrap();                        // f64: Result
```

1. **Name `T` at construction**: `Drawdown::<i64>::new()`,
   `CoDel::<i64>::builder()`, or an annotated `let`. `Drawdown::new()` alone
   is ambiguous.
2. **`T` must be known before the first `update`.** Two `update`s exist, one
   per instantiation; inference cannot pick one from the sample while the
   binding is still untyped. Rule 1 covers this in practice.

A function over both forms names the bound:
`fn drain<T: Sample>(dd: &mut Drawdown<T>)`. `Sample` and `Float` are
exported from `nexus_stats` and `nexus_stats_core` and are sealed (`f64` /
`i64` and `f64` / `f32` only): you name them, you never implement them.

## Picking

| Data | Use |
|------|-----|
| Latency, sojourn, ticks (already integers) | the `i64` forms of the extrema, diffs, bands, `CoDel`, `Jitter`, `PeakHold`; `u64` ticks for the monitors |
| Prices, rates, ratios, utilization | `f64` |
| Counts you only compare or difference | `i64` |
| Counts you want variance or smoothing on | `f64` (`Welford`, `Ema`): cast at the call site |
| Timestamps | `u64` ticks, one clock per value |
