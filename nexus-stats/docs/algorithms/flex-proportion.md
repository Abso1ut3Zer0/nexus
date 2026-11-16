# FlexProportion — Each Key's Share of a Decaying Count

**"What fraction of recent events went to X?"** with lazy per-key decay.
From the Linux kernel's `lib/flex_proportions.c`.

| Property | Value |
|----------|-------|
| Update cost | 5 cycles (8 locals, round-robin) |
| Memory | 40 bytes global + 16 bytes per local |
| Types | `FlexProportionGlobal`, `FlexProportionLocal` |

## What It Does

One global counts every event of a population and advances a decay period
every `half_life_events`, halving its count. Each local holds one key's count
and halves it the same number of times, lazily, when next touched. The share
`local / global` is therefore a share of *recent* events, and the shares sum
to one.

```
  Half-life 1000 events, three venues:

  Venue A: 400 of the last ~1000 → 40%
  Venue B: 350                   → 35%
  Venue C: 250                   → 25%

  A goes quiet: its count halves every 1000 events, on read, while B and C
  keep theirs; A's share decays toward 0% and B's and C's grow to fill it.
```

**Lazy decay:** idle locals cost nothing. If you track 1000 keys but query
3, you pay for 3 reconciliations, not 1000.

## Configuration

```rust
use nexus_stats::frequency::{FlexProportionGlobal, FlexProportionLocal};

let mut global = FlexProportionGlobal::new(1000).unwrap();  // half-life: 1000 events
let mut venue_a = FlexProportionLocal::new();
let mut venue_b = FlexProportionLocal::new();

// One call per event, on the global, naming the local it belongs to:
global.update(&mut venue_a);

// Query:
let share_a = venue_a.fraction(&global);  // 0.0 to 1.0
```

## Examples

### Trading — Shard Load Balancing
```rust
// Which symbols generate most traffic, for capacity planning
let mut global = FlexProportionGlobal::new(100_000).unwrap();
let mut per_symbol: HashMap<Symbol, FlexProportionLocal> = ...;

// On each market data message:
global.update(per_symbol.entry(symbol).or_default());

// Periodically check the distribution:
for (sym, local) in &per_symbol {
    let share = local.fraction(&global);
    if share > 0.20 { /* this symbol is >20% of recent traffic */ }
}
```

### SRE — Service Traffic Distribution
```rust
// Which endpoints take the most requests?
let mut global = FlexProportionGlobal::new(50_000).unwrap();
let mut per_endpoint: HashMap<String, FlexProportionLocal> = HashMap::new();

// On each request:
global.update(per_endpoint.entry(endpoint.clone()).or_default());

// Review: which endpoint is heaviest?
for (ep, local) in &per_endpoint {
    let share = local.fraction(&global);
    if share > 0.25 { log::warn!("{ep} handles {:.0}% of recent traffic", share * 100.0); }
}
```

## Performance

O(1) per event and per query. Reconciling an idle local is one shift by the
number of elapsed periods (zero past 63), not a loop.

## Background

Linux kernel implementation: `lib/flex_proportions.c`, used for dirty-page
throttling: what fraction of dirty pages each cgroup is responsible for. The
kernel advances the period from a timer; this port advances it every
`half_life_events` events, so it needs no clock and replays deterministically.

Note: decay is coarse-grained (halving every period). For smooth exponential
decay in time, use [DecayAccum](decay-accum.md) instead.
