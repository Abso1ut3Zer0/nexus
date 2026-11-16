# DecayAccum

**Type:** `DecayAccum`
**Import:** `use nexus_stats_control::frequency::DecayAccum;`
**Feature flags:** None required.

## What it does

An event-driven score that exponentially decays with *real time* between events. Each time something happens, the score jumps up by a configurable amount; between events, it decays toward zero with a fixed half-life.

Unlike an EMA on booleans, `DecayAccum` knows the actual time between events, so its decay is wall-clock accurate even when events arrive in bursts.

## When to use it

- **Per-entity activity score** — "how active has this user been, weighted by recency?"
- **Streaming reputation / hotness** — favors recent bursts, forgives stale activity.
- **Error-rate alarms** with real-time memory rather than sample-memory.
- **Crackdown detection** — "this IP is making a lot of requests recently".

When you have uniform time between samples, a plain EMA is simpler and cheaper.

## API

```rust
impl DecayAccum {
    pub fn new(half_life: f64) -> Result<Self, nexus_stats_core::ConfigError>;
    pub fn update(&mut self, /* event magnitude, current time */) -> /* current score */;
    pub fn reset(&mut self);
    // score / time-of-last-update accessors — see source
}
```

`half_life` is in whatever time units you pass to `update`. If you feed seconds, a `half_life` of `60.0` means the score halves every minute of idleness.

## Example — per-IP request hotness

```rust
use nexus_stats_control::frequency::DecayAccum;

// Half-life: 30 seconds. Score decays to half after 30s of idleness.
let mut hotness = DecayAccum::new(30.0).unwrap();

// Process an event at t=0
// (pass event magnitude and current time — see source for exact signature)

// ... later, at t=5, another event ...
// score is approximately prior_score * 0.89 + new_magnitude

// At t=60, query score:
// score has decayed toward zero based on real elapsed time
```

(The exact `update(...)` parameter list lives in source — check whether it takes magnitude + time, or just time.)

## Parameter tuning

`half_life` is the only knob. Pick based on the attention timescale:

- **5 seconds** — rapid-fire abuse detection.
- **60 seconds** — per-minute hotness for dashboards.
- **3600 seconds** — hourly user reputation.
- **86400 seconds** — daily activity scores.

## Caveats

- **Monotone time assumption.** If you pass a time less than the last update's time, the decay calculation will be wrong. Use a monotonic clock.
- **Floating-point exp()** on every update. Not free, but typically <20 cycles on modern hardware.
- **No cap on the score.** Repeated large events can grow it unbounded. Apply your own clamping if needed.

## Cross-references

- [`FlexProportion`](flex-proportion.md) — each key's share of a count that decays per event, not per unit time.
- [`EventRate`](../../nexus-stats-core/docs/monitoring.md#eventrate) — smoothed event rate rather than decaying score.
- [`PeakHold<f64>`](../../nexus-stats-core/docs/monitoring.md#peakhold) — peak envelope with decay (for values, not counts).
