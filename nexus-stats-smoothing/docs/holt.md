# Holt (Double Exponential Smoothing)

**Types:** `Holt`
**Import:** `use nexus_stats_smoothing::Holt;`
**Feature flags:** None required.

## What it does

Holt maintains two exponentially weighted estimates: the **level** (where is the signal now?) and the **trend** (how fast is it changing?). Given those, it can forecast `h` steps ahead by extrapolating the trend.

Mathematically, given alpha and beta in `(0, 1]`:

```
level_t = alpha * sample_t + (1 - alpha) * (level_{t-1} + trend_{t-1})
trend_t = beta  * (level_t - level_{t-1}) + (1 - beta) * trend_{t-1}
```

## When to use it

- **Latency degradation detection.** Your p99 is 200us, but is it trending up? `forecast(60)` tells you where you'll be in a minute.
- **Capacity planning.** Throughput with drift — Holt separates "busy moment" from "the system is slowly saturating".
- **Market mid-price with drift.** When you care about both the current mid and whether it's moving.

Not for: signals with no trend (plain `Ema` is cheaper and equivalent), signals dominated by outliers (use `HuberEma` or `Hampel` first), signals with seasonality (Holt doesn't model that — look at Holt-Winters, not provided here).

## API

```rust
impl Holt {
    pub fn builder() -> HoltBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<(f64, f64)>, DataError>;
    pub fn level(&self) -> Option<f64>;
    pub fn trend(&self) -> Option<f64>;
    pub fn forecast(&self, steps: u64) -> Option<f64>;
    pub fn count(&self) -> u64;
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}

impl HoltBuilder {
    pub fn alpha(self, alpha: f64) -> Self;       // level smoothing, (0, 1]
    pub fn beta(self, beta: f64) -> Self;         // trend smoothing, (0, 1]
    pub fn min_samples(self, min: u64) -> Self;   // minimum for is_primed()
    pub fn seed(self, level: f64, trend: f64) -> Self; // optional warm start
    pub fn build(self) -> Result<Holt, ConfigError>;
}
```

`update` returns `Ok(Some((level, trend)))` once primed (by default, after 2 samples), `Ok(None)` before that. `forecast(h)` returns `level + h * trend`.

## Parameter tuning

See [parameter-tuning.md](parameter-tuning.md#holt-alpha-and-beta). Rules of thumb:

- Start `alpha ~ 0.1` (half-life ~ 7 samples), `beta ~ 0.02` (half-life ~ 35 samples).
- `beta < alpha / 5`. Trend needs to be slower than level.
- If trend forecast overshoots, cut `beta` in half.
- If level lags visible shifts, raise `alpha`.

## Example — latency trend detection

```rust
use nexus_stats_smoothing::Holt;

// Per-request latencies (microseconds), gradually degrading.
let latencies: [f64; 20] = [
    100.0, 102.0, 101.0, 105.0, 108.0, 110.0, 112.0, 115.0,
    118.0, 120.0, 125.0, 128.0, 132.0, 135.0, 140.0, 145.0,
    150.0, 156.0, 162.0, 168.0,
];

let mut holt = Holt::builder()
    .alpha(0.3)
    .beta(0.1)
    .build()
    .expect("valid params");

for &us in &latencies {
    holt.update(us).unwrap();
}

// Where are we now, and where will we be in 60 more requests?
let level = holt.level().unwrap();
let trend = holt.trend().unwrap();
let forecast_60 = holt.forecast(60).unwrap();

println!("level={level:.1}us trend={trend:.2}us/req forecast_60={forecast_60:.1}us");
// level ~ 168us, trend ~ +3.3us/req, forecast_60 ~ 366us
```

In a real system, you'd wire the forecast into an alerting rule: "warn if `forecast(300) > SLO`".

## Caveats

- **First two samples.** The trend is initialized from `sample_2 - sample_1`. If that step is noisy, the initial trend is garbage until a few more updates come in. Use `seed()` if you have a better prior.
- **Forecast is linear extrapolation.** Don't use `forecast(h)` with large `h` on anything that isn't locally linear. Holt is a local model.
- **Two parameters.** Harder to tune than EMA. If you find yourself doing a 2D sweep, that's expected — plot alpha in `{0.05, 0.1, 0.2, 0.4}` crossed with beta in `{0.005, 0.02, 0.05, 0.1}` and pick visually.
- **Outliers poison the trend.** A single spike contributes to `level_t - level_{t-1}`, which feeds the trend. Combine with `Hampel` upstream if the input is dirty.

## Cross-references

- EMA — simpler, no trend estimate.
- [KAMA](kama.md) — adapts smoothing by efficiency rather than estimating trend directly.
- [Kalman1d](kalman1d.md) — formal position + velocity with a noise model.
- [TrendAlert](../../nexus-stats-detection/docs/detection.md#trendalert--forecast-based-detection) — uses Holt-style trend for threshold alerts.
