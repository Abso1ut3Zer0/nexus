# BoolWindow

**Type:** `BoolWindow`
**Import:** `use nexus_stats_control::control::BoolWindow;`
**Feature flags:** `alloc`.

## What it does

Maintains a fixed-count sliding window of boolean outcomes. Each `update(bool)` shifts the window and records the new value. Query the fraction of `true` over the window, the running count of trues, etc.

Internally uses a bitmask for compact O(1) storage and updates — no allocation per update.

## When to use it

- **Rolling success rate** over an exact number of recent attempts. "What fraction of the last 100 requests succeeded?"
- **Fill rate monitoring** with exact window semantics rather than EW smoothing.
- **Health gates** that require "at least X of the last N were good".

When you want EW decay rather than a hard window, use [`ErrorRate`](../../nexus-stats-core/docs/monitoring.md#errorrate) or [`HitRate`](../../nexus-stats-core/docs/statistics.md#hitratef64--rolling-success-rate) instead.

## API

```rust
impl BoolWindow {
    pub fn new(sample_count: usize) -> Result<Self, ConfigError>;
    pub fn update(&mut self, success: bool);
    pub fn count(&self) -> u64;           // total updates fed
    pub fn reset(&mut self);
    // fraction / is_primed / true_count accessors — see source
}
```

## Example — rolling fill rate

```rust
use nexus_stats_control::control::BoolWindow;

let mut bw = BoolWindow::new(100).expect("count > 0");

for filled in fill_stream {
    bw.update(filled);
    // Query the rolling success fraction via the accessor methods.
}
```

## Parameter tuning

Just one knob: `sample_count`. Rule of thumb — pick the smallest window that gives you enough samples for the precision you need:

- 20 samples → fraction precision 5%.
- 100 samples → fraction precision 1%.
- 1000 samples → fraction precision 0.1%.

If `sample_count` is much bigger than ~1024, consider whether an EW estimator gives you the same thing for less memory.

## Caveats

- **Hard window semantics.** The oldest sample has identical weight to the newest, then is dropped abruptly when it falls out.
- **No time weighting.** If your updates arrive irregularly, the window edge is in samples, not time.
- **is_primed()** is false until the window is full.

## Cross-references

- [`ErrorRate`](../../nexus-stats-core/docs/monitoring.md#errorrate) — EW version with alert thresholds.
- [`HitRate`](../../nexus-stats-core/docs/statistics.md#hitratef64--rolling-success-rate) — EW success-rate tracker.
- [`BetaBinomial`](../../nexus-stats-regression/docs/estimation.md#betabinomialf64--bayesian-rate-estimation-for-successes) — Bayesian rate with credible intervals.
