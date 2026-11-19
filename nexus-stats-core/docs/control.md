# Control

Thresholding, debouncing, and discrete differencing. Module path: `nexus_stats_core::control`.

These types don't estimate statistics — they implement discrete logic (threshold passed? Change exceeds band? Direction changed?) for use in control loops, alerting, and signal conditioning.

## At a glance

| Type | What it does |
|------|--------------|
| `DeadBand<f64>` / `DeadBand<i64>` | Suppress updates below a change threshold |
| `Hysteresis<f64>` / `Hysteresis<i64>` | Binary decision with different on/off thresholds |
| `Debounce` | Require N consecutive events before triggering |
| `LevelCrossing<f64>` / `LevelCrossing<i64>` | Detect threshold crossings and their direction, and count them |
| `FirstDiff<f64>` / `FirstDiff<i64>` | Discrete first difference (velocity) |
| `SecondDiff<f64>` / `SecondDiff<i64>` | Discrete second difference (acceleration) |

---

## DeadBand — change suppression

Only emits the new sample if it differs from the last emitted sample by more than `threshold`. Below threshold, emits `None`.

```rust
use nexus_stats_core::control::DeadBand;

let mut db = DeadBand::<f64>::new(0.01).unwrap(); // 1-cent dead band
let updates = [100.00, 100.005, 100.009, 100.012, 100.004];
let emitted: Vec<f64> = updates
    .into_iter()
    .filter_map(|u| db.update(u).unwrap())
    .collect();
// The first sample always emits; 100.012 is the first to move more than
// 0.01 from the last emitted value.
assert_eq!(emitted, [100.00, 100.012]);
```

**Use for:** suppressing "noise updates" in set-point changes, order price repeating, downstream subscribers that don't want sub-threshold churn.

---

## Hysteresis — binary with different on/off thresholds

A Schmitt trigger: `new(low, high)` turns on when a sample reaches `high` (`sample >= high`) and stays on until one reaches `low` (`sample <= low`). Both bounds are inclusive. Stops the output from flapping when the input hovers near a single threshold.

```rust
use nexus_stats_core::control::Hysteresis;

let mut h = Hysteresis::<f64>::new(0.60, 0.80).unwrap(); // off at 0.60, on at 0.80
let load = [0.50, 0.79, 0.80, 0.70, 0.61, 0.60, 0.70];
let active: Vec<bool> = load.into_iter().map(|x| h.update(x).unwrap()).collect();
// On at 0.80, held through the band, off at 0.60, and 0.70 does not re-arm.
assert_eq!(active, [false, false, true, true, true, false, false]);
```

**Use for:** CPU/utilization-based load shedding, spread-based quoting enable/disable, anywhere a single threshold gives flap.

---

## Debounce — N consecutive events

Returns true only after `threshold` consecutive `true` inputs. Resets on any `false`.

```rust
use nexus_stats_core::control::Debounce;

let mut db = Debounce::new(3).unwrap(); // need 3 consecutive trues
let events = [true, true, false, true, true, true, true];
let fired: Vec<bool> = events.into_iter().map(|e| db.update(e)).collect();
// Fires on the third `true` after the `false`, and on each `true` after it.
assert_eq!(fired, [false, false, false, false, false, true, true]);
```

**Use for:** alarm suppression, "N in a row" confirmation, bouncing switches.

---

## LevelCrossing — threshold crossing detector

Reports the sample on which the input lands on the other side of the threshold, with the direction: `Some(Direction::Rising)` for below to above, `Some(Direction::Falling)` for above to below, `None` otherwise. Counts crossings.

A sample exactly on the threshold is on neither side. It reports nothing and does not change sides, so touching the threshold and going back is not a crossing, and passing through it is one crossing, reported on arrival at the far side.

```rust
use nexus_stats_core::control::LevelCrossing;
use nexus_stats_core::Direction;

let mut lc = LevelCrossing::<f64>::new(0.0).unwrap(); // zero crossing
let signal = [-1.0, 0.0, -1.0, 0.0, 2.0, -3.0];
let crossings: Vec<Option<Direction>> =
    signal.into_iter().map(|x| lc.update(x).unwrap()).collect();
assert_eq!(
    crossings,
    [None, None, None, None, Some(Direction::Rising), Some(Direction::Falling)]
);
assert_eq!(lc.crossing_count(), 2);
```

**Use for:** zero-crossing detection, edge triggering, phase detection.

---

## FirstDiff / SecondDiff — discrete derivatives

Streaming first (velocity) and second (acceleration) differences. Each returns `None` until enough samples to compute. The second difference is the difference of consecutive first differences.

```rust
use nexus_stats_core::control::{FirstDiff, SecondDiff};

let mut d1 = FirstDiff::<f64>::new();
let mut d2 = SecondDiff::<f64>::new();

let signal = [1.0, 4.0, 9.0, 16.0];
let vel: Vec<Option<f64>> = signal.into_iter().map(|x| d1.update(x).unwrap()).collect();
let acc: Vec<Option<f64>> = signal.into_iter().map(|x| d2.update(x).unwrap()).collect();
assert_eq!(vel, [None, Some(3.0), Some(5.0), Some(7.0)]);
assert_eq!(acc, [None, None, Some(2.0), Some(2.0)]);
```

The `i64` forms cannot fail and do not return `Result`; a difference outside the `i64` range saturates at the bound.

**Use for:** discrete derivatives for a downstream regressor or controller. Cheap and obvious.

**Caveats:** raw differences amplify noise. Usually you want to smooth the input first (EMA or Hampel) before differencing.

---

## Cross-references

- Smoothing before differencing: [`smoothing.md`](smoothing.md).
- Peak detection (local maxima/minima): [`PeakDetector`](../../nexus-stats-control/docs/peak-detector.md) in `nexus-stats-control`.
- Rolling pass/fail rate: [`BoolWindow`](../../nexus-stats-control/docs/bool-window.md) in `nexus-stats-control`.
