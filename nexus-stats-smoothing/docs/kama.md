# KAMA — Kaufman Adaptive Moving Average

**Types:** `Kama`
**Import:** `use nexus_stats_smoothing::Kama;`
**Feature flags:** `alloc` (uses an internal window).

## What it does

KAMA adapts its smoothing factor based on market *efficiency*. Over a lookback window `n`:

```
efficiency_ratio = |sample_t - sample_{t-n}| / sum(|sample_i - sample_{i-1}|)
```

A signal that moves in a straight line has efficiency ~ 1.0. A signal that oscillates around a mean has efficiency ~ 0. KAMA smooths gently when efficiency is high (trust the trend) and aggressively when efficiency is low (smooth the noise).

The effective alpha is interpolated between a `fast` alpha and a `slow` alpha using the efficiency ratio.

## When to use it

- **Price series that alternate regimes.** Trending markets and ranging markets behave differently and you don't want to hand-switch.
- **Signals with bursty change rate.** Anywhere a single alpha is either too fast or too slow depending on current regime.

Not for: signals where you already know the regime, or signals where you genuinely want a fixed timescale.

## API

```rust
impl Kama {
    pub fn builder() -> KamaBuilder;
    pub fn update(&mut self, sample: f64) -> Result<Option<f64>, DataError>;
    pub fn value(&self) -> Option<f64>;
    pub fn efficiency_ratio(&self) -> Option<f64>;
    pub fn window_size(&self) -> usize;
    pub fn count(&self) -> u64;
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}

impl KamaBuilder {
    pub fn window_size(self, n: usize) -> Self;   // efficiency lookback, default 10
    pub fn fast_span(self, n: u64) -> Self;       // fast EMA half-life, default 2
    pub fn slow_span(self, n: u64) -> Self;       // slow EMA half-life, default 30
    pub fn min_samples(self, min: u64) -> Self;
    pub fn build(self) -> Result<Kama, ConfigError>;
}
```

## Example — price smoother for a crypto mid

```rust
use nexus_stats_smoothing::Kama;

let prices: [f64; 12] = [
    100.0, 100.1, 99.95, 100.05, 100.02,   // ranging
    100.1, 100.8, 101.6, 102.4, 103.3,     // trending
    104.0, 104.5,                          // trending
];

let mut kama = Kama::builder()
    .window_size(10)
    .fast_span(2)
    .slow_span(30)
    .build()
    .expect("valid params");

for &p in &prices {
    kama.update(p).unwrap();
    if let Some(v) = kama.value() {
        let er = kama.efficiency_ratio().unwrap_or(0.0);
        println!("price={p:.2} kama={v:.3} efficiency={er:.2}");
    }
}
```

Expect: during the ranging phase, `kama` barely moves. During the trending phase, it follows aggressively.

## Parameter tuning

Defaults `(10, 2, 30)` are Kaufman's classic. Adjust:

- `window_size`: larger = less reactive efficiency estimate. 5 for fast assets, 20 for slow.
- `fast_span`: smaller = more aggressive during trends. 2 is already very responsive.
- `slow_span`: larger = more damping during chop. 30 is typical; 60+ for very noisy signals.

## Caveats

- Needs at least `window_size + 1` samples before producing an output.
- Efficiency ratio is scale-free but sensitive to the *absolute* step pattern — a signal with log-normal steps can look artificially "efficient".
- Not a statistical estimator. No noise model, no confidence intervals.

## Cross-references

- [EMA](../../nexus-stats-core/docs/smoothing.md#ema) — fixed alpha.
- [Holt](holt.md) — trend-aware, no regime adaptation.
- [Kalman1d](kalman1d.md) — formal state estimation with noise model.
