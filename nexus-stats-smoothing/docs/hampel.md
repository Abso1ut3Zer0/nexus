# Hampel — Three-Zone Outlier Filter

**Type:** `Hampel`
**Import:** `use nexus_stats_smoothing::Hampel;`
**Feature flags:** `alloc`.

## What it does

Hampel maintains a sliding window of the last `n` samples. For each new sample it computes the window median and median absolute deviation (MAD). Then:

- If `|x - median| <= inner_threshold * MAD`, the sample passes through unchanged.
- Else if `|x - median| <= outer_threshold * MAD`, the sample is **Winsorized** (clipped to the inner boundary).
- Else, the sample is **rejected** and the filter returns the median.

This gives you graded rejection: obvious spikes are capped, extreme spikes are replaced, normal values are untouched.

## When to use it

- **Market data from dirty feeds.** Exchange glitches that produce impossible prints.
- **Sensor fusion with intermittent failures.** IMUs, GPS, thermometers.
- **Pre-filter before downstream smoothers / regressors.** Clean the stream once, use the cleaned output many times.

## API

```rust
impl Hampel {
    pub fn builder() -> HampelBuilder;
    pub fn update(&mut self, x: f64) -> Result<f64, DataError>;
    pub fn value(&self) -> Option<f64>;
    pub fn median(&self) -> Option<f64>;
    pub fn is_primed(&self) -> bool;
    pub fn count(&self) -> u64;
    pub fn reset(&mut self);
}

impl HampelBuilder {
    pub fn window_size(self, n: usize) -> Self;       // odd, typical 11
    pub fn inner_threshold(self, t: f64) -> Self;     // MAD multiplier for Winsorize, typical 3.0
    pub fn outer_threshold(self, t: f64) -> Self;     // MAD multiplier for reject, typical 6.0
    pub fn mad_scale(self, s: f64) -> Self;           // 1.4826 for Gaussian
    pub fn build(self) -> Result<Hampel, ConfigError>;
}
```

`update` returns the cleaned value (possibly equal to the input, possibly Winsorized, possibly the median).

## Example — cleaning a noisy price feed

```rust
use nexus_stats_smoothing::Hampel;

let raw_prices: [f64; 8] = [
    100.0, 100.1, 99.95, 100.05,
    0.01,      // exchange glitch — rejected
    100.02,
    105.0,     // real fast move, should survive
    105.2,
];

let mut hampel = Hampel::builder()
    .window_size(7)
    .inner_threshold(3.0)
    .outer_threshold(6.0)
    .build()
    .unwrap();

for &p in &raw_prices {
    let cleaned = hampel.update(p).unwrap();
    println!("raw={p:.3} cleaned={cleaned:.3}");
}
```

Expect: `0.01` is replaced by the window median, `105.0` passes through or is Winsorized (depending on exact window contents).

## Parameter tuning

- `window_size`: odd, 7-21 typical. Bigger = more robust, more lag.
- `inner_threshold`: 3.0 is the canonical "3-MAD" rule (~2 sigma under Gaussian).
- `outer_threshold`: 6.0 is "obvious garbage". Adjust down if you want tighter rejection.

Under Gaussian noise, `MAD * 1.4826 ≈ stddev`. The default `mad_scale` is 1.4826 so that the thresholds read in sigma units.

## Caveats

- Lag equals `window_size / 2` samples. At 21-sample windows on a 1ms feed, that's 10ms of lag.
- `window_size - 1` warmup samples before primed.
- Window median computation is O(log n) per update (small n, so still cheap).

## Cross-references

- [WindowedMedian](windowed-median.md) — just the median, no threshold logic.
