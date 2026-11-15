# FlexibleProportions — Per-Entity Fraction Tracking

**"What % of total does entity X contribute?"** with lazy per-entity decay.
From Linux kernel `lib/flex_proportions.c`.

| Property | Value |
|----------|-------|
| Update cost | O(1) per event |
| Memory | ~16 bytes per entity + ~16 bytes global |
| Types | `FlexProportionGlobal`, `FlexProportionEntity` |

## What It Does

Tracks a global event stream and per-entity contributions. Each entity's
fraction decays over time — recent activity matters more than old.

```
  Global events: 1000 total
  Entity A: 400 recent events → 40%
  Entity B: 350 recent events → 35%
  Entity C: 250 recent events → 25%

  After Entity A goes quiet:
  Entity A: fraction decays toward 0%
  Entity B and C: fractions increase proportionally
```

**Lazy decay:** Per-entity counters only decay when queried. If you have
1000 entities but only check 3, you pay for 3 decays — not 1000.

## Configuration

```rust
let mut global = FlexProportionGlobal::new(1000).unwrap();  // half-life: 1000 events

let mut entity_a = FlexProportionEntity::new();
let mut entity_b = FlexProportionEntity::new();

// On each event: the global first, then the responsible entity with the global's period
global.update();
entity_a.update(global.period());

// Query:
let pct_a = entity_a.fraction(global.total(), global.period());  // 0.0 to 1.0
```

## Examples

### Trading — Shard Load Balancing
```rust
// Track which symbols generate most traffic for capacity planning
let mut global = FlexProportionGlobal::new(100_000).unwrap();
let mut per_symbol: HashMap<Symbol, FlexProportionEntity> = ...;

// On each market data message:
global.update();
per_symbol.get_mut(&symbol).unwrap().update(global.period());

// Periodically check distribution:
for (sym, entity) in &per_symbol {
    let pct = entity.fraction(global.total(), global.period());
    if pct > 0.20 { /* this symbol is >20% of traffic */ }
}
```

### SRE — Service Traffic Distribution
```rust
// Which endpoints consume the most resources?
let mut global = FlexProportionGlobal::new(50_000).unwrap();
let mut per_endpoint: HashMap<String, FlexProportionEntity> = HashMap::new();

// On each request:
global.update();
per_endpoint.entry(endpoint.clone())
    .or_insert_with(FlexProportionEntity::new)
    .update(global.period());

// Review: which endpoint is heaviest?
for (ep, entity) in &per_endpoint {
    let pct = entity.fraction(global.total(), global.period());
    if pct > 0.25 { log::warn!("{ep} handles {:.0}% of traffic", pct * 100.0); }
}
```

## Performance

O(1) per event and per query. The lazy decay catch-up is O(1) — it
applies the decay exponent for the elapsed periods in one computation.

## Background

Linux kernel implementation: `lib/flex_proportions.c`. Used for dirty page
throttling — tracking what fraction of dirty pages each cgroup is responsible for.

Note: decay is coarse-grained (halving every N events). For smooth exponential
decay, use [DecayingAccumulator](decay-accum.md) instead.
