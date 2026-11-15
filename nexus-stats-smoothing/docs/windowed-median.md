# WindowedMedian

**Types:** `WindowedMedian<f64>`, `WindowedMedianF32`
**Import:** `use nexus_stats_smoothing::WindowedMedian;`
**Feature flags:** `alloc`.

## What it does

Maintains the running median over the last `n` samples in a fixed-capacity sliding window. The median is the classic 50%-breakdown estimator: up to `n/2 - 1` corrupted samples in the window have zero effect.

## When to use it

- **Adversarially noisy data** where half or more of the samples might be garbage.
- **Pre-filter** for everything else in this crate when the input is dirty.
- **Robust baseline** against which you measure anomalies.

Not for: signals where you need mean semantics (Welford), or where the window lag is unacceptable.

## API

```rust
impl WindowedMedian<f64> {
    pub fn new(window_size: usize) -> Self;
    pub fn update(&mut self, sample: f64) -> Result<(), DataError>;
    pub fn median(&self) -> Option<f64>;
    pub fn count(&self) -> u64;
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}
```

## Example — latency floor detector

```rust
use nexus_stats_smoothing::WindowedMedian;

let latencies: [f64; 12] = [
    120.0, 125.0, 118.0, 9500.0, 121.0, 130.0,
    8200.0, 119.0, 127.0, 123.0, 8800.0, 122.0,
];

// 11-sample window. With 3 spikes out of 11, median stays clean (< 50% corruption).
let mut med = WindowedMedian::<f64>::new(11);

for &us in &latencies {
    med.update(us).unwrap();
    if let Some(m) = med.median() {
        println!("latency={us:.0} median_11={m:.0}");
    }
}
```

The median tracks ~123us through the spikes.

## Parameter tuning

One parameter: window size. Odd values (5, 11, 21, 51) are conventional. Larger = more robust, more lag, more memory. No other knobs.

## Caveats

- **Half-window lag.** 21-sample window at 1ms = 10ms median lag.
- **Step-insensitive.** After a genuine step change, the median doesn't update until half the window has caught up.
- **O(log n) per update.** Not free, but n is small so still cheap.
- Not differentiable — don't use as the basis for a regression.

## Cross-references

- [Hampel](hampel.md) — same window plus threshold-based filtering.
- [Percentile (P²)](../../nexus-stats-core/docs/statistics.md#percentile) — streaming percentiles with O(1) memory.
