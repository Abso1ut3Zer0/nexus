# FlexProportion

**Types:** `FlexProportionGlobal`, `FlexProportionEntity`
**Import:** `use nexus_stats_control::frequency::{FlexProportionEntity, FlexProportionGlobal};`
**Feature flags:** None required.

## What it does

Tracks each entity's share of a streaming event count with temporal decay, after the Linux kernel's `lib/flex_proportions.c`. One `FlexProportionGlobal` counts every event and advances a decay period every `half_life_events`; one `FlexProportionEntity` per tracked entity holds that entity's count and catches up on missed periods lazily, the next time it is updated or queried. Old activity fades, recent activity dominates.

Both halves are O(1), zero allocation. The entity never holds a reference to the global: it takes the current period as a plain `u64`, so a map of entities and the global can live in different places.

## When to use it

- **Per-user load share.** "User 42 is 18% of our load right now."
- **Per-client quota tracking** in rate limiters.
- **Market-maker quoting share** on an exchange.

Not for: top-K ranking (use `TopK`). Not for: time-weighted rather than event-weighted shares (use `DecayAccum` + totals).

## API

```rust
impl FlexProportionGlobal {
    pub fn new(half_life_events: u64) -> Result<Self, ConfigError>;
    pub fn update(&mut self);           // once per event, before the entity
    pub fn total(&self) -> u64;
    pub fn period(&self) -> u64;
}

impl FlexProportionEntity {
    pub fn new() -> Self;
    pub fn update(&mut self, current_period: u64);                   // pass global.period()
    pub fn fraction(&self, total: u64, current_period: u64) -> f64;  // 0.0 to 1.0
    pub fn count(&self) -> u64;
    pub fn reset(&mut self);
}
```

`half_life_events` controls how fast old events fade: the global's period advances every that many events, and an entity's count halves once per period it missed. Pass a large value for near-total counting, smaller for recency-weighted shares.

## Example — per-client quota share

```rust
use nexus_stats_control::frequency::{FlexProportionEntity, FlexProportionGlobal};

let mut global = FlexProportionGlobal::new(10_000).unwrap();
let mut client_a = FlexProportionEntity::new();
let mut client_b = FlexProportionEntity::new();

// Each time client A makes a request: the global first, then the entity
global.update();
client_a.update(global.period());

// Each time client B makes a request:
global.update();
client_b.update(global.period());

// Query
let share_a = client_a.fraction(global.total(), global.period());
println!("client A share = {share_a:.3}");
```

## Caveats

- **Not a full leaderboard.** You hold one `FlexProportionEntity` per tracked entity. For dynamic-entity top-K, use `TopK`.
- **Single writer.** Both halves are `&mut self`; share them across threads behind your own synchronization.
- **Half-life in events**, not time. If you want time-based decay, use `DecayAccum`.

## Cross-references

- [`TopK`](topk.md) — ranked heavy hitters.
- [`DecayAccum`](decay-accum.md) — time-decayed per-entity score.
