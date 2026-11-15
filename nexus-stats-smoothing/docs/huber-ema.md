# HuberEMA — Outlier-Robust EMA

**Type:** `HuberEma`
**Import:** `use nexus_stats_smoothing::HuberEma;`
**Feature flags:** None required.

## What it does

A regular EMA, except each observation's *influence* is capped. The "residual" between the new sample and the current estimate is clipped to `[-delta, +delta]` before being applied. Small residuals behave like a normal EMA; large residuals (outliers) still contribute, but only by `delta`.

This is the Huber loss function's influence behavior applied to an online exponentially-weighted estimator.

## When to use it

- **Mostly clean data with occasional shocks.** Fill ratios, latency under load, network throughput.
- **You want all data to count,** just with bounded outlier influence — unlike a median, which throws information away.

Not for: data that's routinely garbage (use `WindowedMedian<f64>` or `Hampel`), data where the "outliers" are actually the signal (use plain `Ema`).

## API

```rust
impl HuberEma {
    pub fn builder() -> HuberEmaBuilder;
    pub fn update(&mut self, x: f64) -> Result<Option<f64>, DataError>;
    pub fn value(&self) -> Option<f64>;
    pub fn alpha(&self) -> f64;
    pub fn delta(&self) -> f64;
    pub fn count(&self) -> u64;
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}

impl HuberEmaBuilder {
    pub fn alpha(self, alpha: f64) -> Self;
    pub fn halflife(self, halflife: f64) -> Self; // alternative to alpha
    pub fn delta(self, delta: f64) -> Self;       // clip threshold in units of x
    pub fn min_samples(self, n: u64) -> Self;
    pub fn seed(self, value: f64) -> Self;
    pub fn build(self) -> Result<HuberEma, ConfigError>;
}
```

## Example — robust latency tracker

```rust
use nexus_stats_smoothing::HuberEma;

// Request latencies (us). One of them is a GC pause spike.
let latencies: [f64; 8] = [120.0, 125.0, 122.0, 130.0, 8500.0, 128.0, 124.0, 119.0];

// Clip residuals to +/- 200us: GC spike contributes bounded, not full-weight.
let mut robust = HuberEma::builder()
    .halflife(10.0)
    .delta(200.0)
    .build()
    .unwrap();

for &us in &latencies {
    robust.update(us).unwrap();
}

println!("robust mean latency = {:.1}us", robust.value().unwrap());
// ~125us, not dragged by the 8500 spike.
```

## Parameter tuning

- `halflife`: same rules as a plain EMA. Pick based on how fast you want the baseline to respond.
- `delta`: expected "honest" residual magnitude. A good heuristic is `2 * current_stddev`. Track it with `EwmaVar` and set `delta = 2 * stddev.sqrt()` at construction time.

## Caveats

- Fixed `delta`. If the signal's natural scale drifts, you may want to recalibrate by rebuilding the estimator.
- Still a single-point-of-failure estimator — an adversarial input that stays just inside the clip boundary can slowly bias the value.
- Not the same thing as Huber regression. This is Huber-style robustness applied to a plain EMA, not an M-estimator.

## Cross-references

- [EMA](../../nexus-stats-core/docs/smoothing.md#ema) — unbounded influence.
- [Hampel](hampel.md) — three-zone reject/Winsorize/pass filter.
- [WindowedMedian](windowed-median.md) — hard 50% breakdown median.
