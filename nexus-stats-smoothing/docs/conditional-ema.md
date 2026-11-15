# ConditionalEMA

**Type:** `ConditionalEma`
**Import:** `use nexus_stats_smoothing::ConditionalEma;`
**Feature flags:** None required.

## What it does

An EMA that only incorporates samples when a caller-supplied boolean is true. Call `update(value, active)`; when `active == false`, the estimator is *not* advanced — no decay, no contribution.

This cleanly separates "is the phenomenon happening?" from "how's it doing while it's happening?".

## When to use it

- **Fill-rate tracking.** You only have a fill rate while you're actually quoting. Don't poison the EMA with zeros during idle periods.
- **Queue latency tracking.** Measure wait time only when the queue is non-empty.
- **Gated telemetry.** Session RTT during active sessions only.

## API

```rust
impl ConditionalEma {
    pub fn builder() -> ConditionalEmaBuilder;
    pub fn update(&mut self, value: f64, active: bool) -> Result<(), DataError>;
    pub fn value(&self) -> Option<f64>;
    pub fn active_fraction(&self) -> f64;
    pub fn count(&self) -> u64;
    pub fn active_count(&self) -> u64;
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}

impl ConditionalEmaBuilder {
    pub fn alpha(self, alpha: f64) -> Self;
    pub fn halflife(self, halflife: f64) -> Self;
    pub fn min_samples(self, min: u64) -> Self;
    pub fn build(self) -> Result<ConditionalEma, ConfigError>;
}
```

`active_fraction()` returns the fraction of updates that were marked active — useful for dashboarding "how often were we actually observing?"

## Example — fill rate during active quoting

```rust
use nexus_stats_smoothing::ConditionalEma;

let mut fill_rate = ConditionalEma::builder()
    .halflife(50.0)
    .build()
    .unwrap();

// Each "tick": (fill_ratio_this_window, are_we_quoting)
let ticks: [(f64, bool); 6] = [
    (0.80, true),
    (0.0,  false),  // not quoting, ignored
    (0.75, true),
    (0.0,  false),
    (0.60, true),
    (0.82, true),
];

for (r, active) in ticks {
    fill_rate.update(r, active).unwrap();
}

println!(
    "fill rate = {:.3}, active fraction = {:.2}",
    fill_rate.value().unwrap_or(0.0),
    fill_rate.active_fraction(),
);
```

## Caveats

- `value` is ignored when `active == false`, but passing a NaN while inactive still returns an error. Pass `0.0` or any finite placeholder.
- `active_fraction` is an aggregate over all calls to `update`, not a rolling fraction. If you need a rolling estimate, track it separately with a `BoolWindow`.

## Cross-references

- [EMA](../../nexus-stats-core/docs/smoothing.md#ema) — the unconditional version.
- [BoolWindow](../../nexus-stats-control/docs/bool-window.md) — rolling pass/fail rate.
