# FlexProportion

**Types:** `FlexProportionGlobal`, `FlexProportionLocal`
**Import:** `use nexus_stats_control::frequency::{FlexProportionGlobal, FlexProportionLocal};`
**Feature flags:** None required.

## What it does

Each local's share of a decaying global event count, after the Linux kernel's `lib/flex_proportions.c` (`fprop_global` / `fprop_local_single`), where it apportions dirty pages among cgroups. One `FlexProportionGlobal` per population counts every event and advances a decay period every `half_life_events`; at that moment its count halves. One `FlexProportionLocal` per tracked key holds that key's count and the period it last saw, and halves the same number of times, lazily, the next time it is touched. `local / global` is each key's share of recent events, and the shares sum to one (up to the integer halving).

The kernel advances the period from a timer; here the period is event-driven, so the type is clock-free and deterministic. O(1) per update and per query, 40 bytes for the global and 16 per local, no allocation, `no_std`.

## When to use it

- **Per-venue or per-shard share of flow.** "Venue A is 18% of our fills right now."
- **Per-client share** in a fair-share scheduler or rate limiter.
- **Any "what fraction of recent events was X"** where X is one of a known set of keys.

Not for: top-K over an unbounded key space (use `TopK`). Not for: time-weighted rather than event-weighted shares (use `DecayAccum` and a sum).

## API

```rust
impl FlexProportionGlobal {
    pub fn new(half_life_events: u64) -> Result<Self, ConfigError>;
    pub fn update(&mut self, local: &mut FlexProportionLocal);   // one event, attributed to `local`
    pub fn events(&self) -> u64;        // decayed population count (the denominator)
    pub fn period(&self) -> u64;        // how many times the counts have halved
    pub fn half_life_events(&self) -> u64;
    pub fn count(&self) -> u64;         // updates ever, undecayed
    pub fn is_primed(&self) -> bool;
    pub fn reset(&mut self);
}

impl FlexProportionLocal {
    pub const fn new() -> Self;         // also `Default`; `Copy`
    pub fn fraction(&self, global: &FlexProportionGlobal) -> f64;  // 0.0 to 1.0
    pub fn events(&self, global: &FlexProportionGlobal) -> u64;    // decayed to the global's period
    pub fn reset(&mut self);
}
```

The global owns the only mutating call, so a local can never be fed with the wrong population's period. Locals are plain data: keep them in a map, an array or a struct; they hold no reference to the global.

## Example — per-venue share of fills

```rust
use nexus_stats_control::frequency::{FlexProportionGlobal, FlexProportionLocal};

let mut global = FlexProportionGlobal::new(10_000).unwrap(); // half-life: 10k fills
let mut venues = [FlexProportionLocal::new(); 3];

// Each fill: one update, naming the venue
global.update(&mut venues[fill.venue as usize]);

// Query: shares of recent fills, summing to about 1.0
for (i, v) in venues.iter().enumerate() {
    println!("venue {i}: {:.1}%", 100.0 * v.fraction(&global));
}
```

## Caveats

- **Half-life in events, not time.** A quiet population keeps its last shares until events arrive. For time-based decay use `DecayAccum`.
- **A key that stops seeing events decays on read**, down to zero after 63 periods without a touch; nothing has to iterate over idle locals.
- **Not a leaderboard.** You hold one local per key you already know about. For dynamic-key heavy hitters, use `TopK`.
- **Single writer.** The global is `&mut self` on update; share it across threads behind your own synchronization.

## Cross-references

- [`TopK`](topk.md) — ranked heavy hitters over an unbounded key space.
- [`DecayAccum`](decay-accum.md) — time-decayed per-key score.
