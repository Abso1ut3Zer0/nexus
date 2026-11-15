# Control

Thresholding, debouncing, and discrete differencing. Module path: `nexus_stats_core::control`.

These types don't estimate statistics — they implement discrete logic (threshold passed? Change exceeds band? Direction changed?) for use in control loops, alerting, and signal conditioning.

## At a glance

| Type | What it does |
|------|--------------|
| `DeadBand<f64>` / `DeadBand<i64>` | Suppress updates below a change threshold |
| `Hysteresis<f64>` / `Hysteresis<i64>` | Binary decision with different on/off thresholds |
| `Debounce` | Require N consecutive events before triggering |
| `LevelCrossing<f64>` / `LevelCrossing<i64>` | Count / detect threshold crossings |
| `FirstDiff<f64>` / `FirstDiff<i64>` | Discrete first difference (velocity) |
| `SecondDiff<f64>` / `SecondDiff<i64>` | Discrete second difference (acceleration) |

---

## DeadBand — change suppression

Only emits the new sample if it differs from the last emitted sample by more than `threshold`. Below threshold, emits `None`.

```rust
use nexus_stats_core::control::DeadBand;

let mut db = DeadBand::<f64>::new(0.01).unwrap(); // 1-cent dead band
let updates = [100.00, 100.005, 100.009, 100.012, 100.004];
for u in updates {
    if let Some(v) = db.update(u).unwrap() {
        println!("emit {v:.3}");
    }
}
// emits 100.000, then 100.012 (first crossing of 0.01 band)
```

**Use for:** suppressing "noise updates" in set-point changes, order price repeating, downstream subscribers that don't want sub-threshold churn.

---

## Hysteresis — binary with different on/off thresholds

A Schmitt trigger: turns on above `upper_threshold`, stays on until below `lower_threshold`. Stops the output from flapping when the input hovers near a single threshold.

```rust
use nexus_stats_core::control::Hysteresis;

let mut h = Hysteresis::<f64>::new(0.80, 0.60).unwrap(); // on at 0.80, off at 0.60
for load in load_samples {
    let active = h.update(load).unwrap();
    // `active` is true as long as we're "in the hot zone"
}
```

**Use for:** CPU/utilization-based load shedding, spread-based quoting enable/disable, anywhere a single threshold gives flap.

---

## Debounce — N consecutive events

Returns true only after `threshold` consecutive `true` inputs. Resets on any `false`.

```rust
use nexus_stats_core::control::Debounce;

let mut db = Debounce::new(3).unwrap(); // need 3 consecutive trues
let events = [true, true, false, true, true, true, true];
for e in events {
    if db.update(e) {
        println!("fired");
    }
}
// fires on the third `true` after the `false`, and each subsequent `true`.
```

**Use for:** alarm suppression, "N in a row" confirmation, bouncing switches.

---

## LevelCrossing — threshold crossing detector

Returns true when the input crosses a threshold (up or down). Counts crossings.

```rust
use nexus_stats_core::control::LevelCrossing;

let mut lc = LevelCrossing::<f64>::new(0.0); // zero crossing
for x in signal {
    if lc.update(x).unwrap() {
        println!("crossed zero");
    }
}
```

**Use for:** zero-crossing detection, edge triggering, phase detection.

---

## FirstDiff / SecondDiff — discrete derivatives

Streaming first (velocity) and second (acceleration) differences. Each returns `None` until enough samples to compute.

```rust
use nexus_stats_core::control::{FirstDiff, SecondDiff};

let mut d1 = FirstDiff::<f64>::new();
let mut d2 = SecondDiff::<f64>::new();

for x in signal {
    let vel = d1.update(x).unwrap();
    let acc = d2.update(x).unwrap();
    // vel and acc are Option<f64>
}
```

**Use for:** discrete derivatives for a downstream regressor or controller. Cheap and obvious.

**Caveats:** raw differences amplify noise. Usually you want to smooth the input first (EMA or Hampel) before differencing.

---

## Cross-references

- Smoothing before differencing: [`smoothing.md`](smoothing.md).
- Peak detection (local maxima/minima): [`PeakDetector`](../../nexus-stats-control/docs/peak-detector.md) in `nexus-stats-control`.
- Rolling pass/fail rate: [`BoolWindow`](../../nexus-stats-control/docs/bool-window.md) in `nexus-stats-control`.
