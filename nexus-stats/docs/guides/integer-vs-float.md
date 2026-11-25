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
| `monitoring` | `WindowedMax<V, T>`, `WindowedMin<V, T>` (the value `V`; `T` is the clock), `PeakHold<T>` |
| `control` | `DeadBand<T>`, `Hysteresis<T>`, `LevelCrossing<T>`, `FirstDiff<T>`, `SecondDiff<T>`, `PeakDetector<T>` |
| `smoothing` | `WindowedMedian<T>` |

Time is a third kind, and the caller brings the clock. Physical time is a
`Timestamp`: a raw `i128` or `i64` is nanoseconds, `Micros`, `Millis` and
`Seconds` name other units, and an `Instant` works with `std`. `Liveness`,
`EventRate`, `CoDel`, `MinMaxNorm` and the windowed extrema take any of
them, one clock per value, and a span is a `Duration`. A raw `u64` or `u32`
is a plain count and an `f64` a running quantity; those are `Tick`s but not
timestamps, for a model such as `HawkesIntensity`. `PollSaturation`,
`DecayAccum` and `BucketAccumulator` have not moved yet and still take
`u64` ticks.

The normalizers (`ZScoreNorm<T>`, `MinMaxNorm<V, T>`, `QuantileNorm<T>`) and
`RobustZScore<T>` are generic over `Float` (`f64`, `f32`) instead: they take
and return `T` but accumulate in `f64`, so the `f32` form is a boundary type
for `f32` feature vectors, not a cheaper accumulator.

## What the `i64` form changes

- **No `Result`.** On a type not yet migrated, the `f64` form's `update`
  returns a `Result` because NaN and infinity are rejected. The `i64`
  form returns the plain value. There is nothing to reject.
- **Exact arithmetic.** Comparisons, differences and clamps are exact;
  `DeadBand<i64>` uses `abs_diff`. `Jitter<i64>` keeps its estimate scaled
  by 16, as RFC 3550 does. `PeakHold<i64>` holds, then drops to
  the current sample; the fractional `decay_rate` exists on `f64` only.
- **No FPU.** Nothing in an `i64` instantiation touches floating point.
- **Same codegen.** The generic body monomorphizes to what the old
  old `I64` types compiled to, verified cycle-identical.

## Two caller rules

The body is written once and the constructors are shared, so the compiler has
to know `T` before the first call whose signature differs by type:

```rust
use core::time::Duration;
use nexus_stats::monitoring::WindowedMax;

let window = Duration::from_secs(1);
let mut wm = WindowedMax::<i64, i128>::new(window);   // turbofish on the constructor, or
let mut wm2: WindowedMax<f64, i128> = WindowedMax::new(window).unwrap(); // a type annotation

dd.update(42);                                    // i64: plain value
dd2.update(42.0).unwrap();                        // f64: Result
```

1. **Name the types at construction**: `WindowedMax::<i64, i128>::new(window)`
   or an annotated `let`. `WindowedMax::new(window)` alone is ambiguous.
2. **`T` must be known before the first `update`.** Two `update`s exist, one
   per instantiation; inference cannot pick one from the sample while the
   binding is still untyped. Rule 1 covers this in practice.

A function over both forms names the bound:
`fn drain<V: Sample, T: Timestamp>(wm: &mut WindowedMax<V, T>)`. `Sample` and `Float` are
exported from `nexus_stats` and `nexus_stats_core` and are sealed (`f64` /
`i64` and `f64` / `f32` only): you name them, you never implement them.

## Picking

| Data | Use |
|------|-----|
| Latency, sojourn, ticks (already integers) | the `i64` forms of the extrema, diffs, bands, `Jitter`, `PeakHold`, `PeakToTrough`; `u64` ticks for the monitors |
| Prices, rates, ratios, utilization | `f64` |
| Counts you only compare or difference | `i64` |
| Counts you want variance or smoothing on | `f64` (`Welford`, `Ema`): cast at the call site |
| Timestamps | `i128` or `i64` nanoseconds, `Micros` / `Millis` / `Seconds`, or `Instant`; `u64` ticks on the types not yet moved |
| Spans of time (a window, an interval, a sojourn) | `Duration` |
