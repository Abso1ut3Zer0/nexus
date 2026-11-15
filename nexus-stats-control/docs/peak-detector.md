# PeakDetector

**Types:** `PeakDetector<f64>`, `PeakDetector<i64>`
**Import:** `use nexus_stats_control::control::PeakDetector;`
**Feature flags:** None required.

## What it does

Detects local maxima (peaks) in a streaming signal. A peak is emitted when a local maximum's prominence — the distance it rose from the surrounding baseline — exceeds a configurable threshold. Noise and minor bumps are filtered out.

There's also a minimum-detecting variant (check the source — it mirrors the max detector).

## When to use it

- **Beat / event detection** in a periodic signal.
- **Peak finding** in smoothed market data (mid-price tops, volume spikes).
- **Instrument / sensor data** — find the characteristic bumps of a waveform.

Not for: when all you need is "was the last value the max so far?" (use `RunningMax<f64>`) or "max over a sliding window?" (use `WindowedMax<f64>`).

## API

```rust
impl PeakDetector<f64> {
    pub fn new(prominence: f64) -> Result<Self, ConfigError>;
    pub fn update(&mut self, sample: f64) -> Result<Option<Peak<f64>>, DataError>;
    pub fn reset(&mut self);
}

pub struct Peak<T> {
    pub value: T,
    // ... index / timestamp fields, see source
}
```

`update` returns `Ok(Some(peak))` when a finished local maximum is confirmed, `Ok(None)` otherwise. Note that a peak is only emitted *after* the signal has come back down by `prominence` — there's inherent lag.

## Example — volume spike detection

```rust
use nexus_stats_control::control::PeakDetector;

let mut detector = PeakDetector::<f64>::new(100.0) // prominence = 100 units
    .expect("prominence > 0");

let volumes = [50.0, 80.0, 120.0, 200.0, 180.0, 90.0, 60.0, 55.0, 70.0];

for &v in &volumes {
    if let Some(peak) = detector.update(v).unwrap() {
        println!("detected peak: {peak:?}");
    }
}
// Emits a peak at v=200.0 once the signal comes back down below 200 - 100 = 100.
```

## Parameter tuning

- **prominence**: the minimum rise-then-fall in sample units to count as a peak. Too small = false positives from noise; too large = misses real peaks. Start with `2-3 * sigma(signal)`.
- If the signal is noisy, pre-filter with [`Ema`](../../nexus-stats-core/docs/smoothing.md) or [`Hampel`](../../nexus-stats-smoothing/docs/hampel.md) before feeding the detector.

## Caveats

- **Lag.** A peak is only emitted after the signal descends from it — you won't know the peak is a peak until it's over. No lookahead.
- **NaN/Inf** inputs return `DataError`.

## Cross-references

- [`RunningMax<f64>`](../../nexus-stats-core/docs/monitoring.md#runningmax--runningmin) — just the all-time max.
- [`WindowedMax<f64>`](../../nexus-stats-core/docs/monitoring.md#windowedmax--windowedmin) — sliding-window max.
- [`LevelCrossing<f64>`](../../nexus-stats-core/docs/control.md#levelcrossing--threshold-crossing-detector) — threshold crossing detection.
