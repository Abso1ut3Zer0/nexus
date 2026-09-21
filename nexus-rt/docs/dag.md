# DAGs — Data-Flow Graphs with Fan-Out and Merge

A `Dag` (directed acyclic graph) is a pipeline that can fan out into
multiple branches, process each branch independently, and merge the
results back. Use a DAG when a single input produces multiple outputs
that need to be computed and combined.

**Use Pipeline when:** the flow is linear — stage 1 → stage 2 → stage 3.

**Use DAG when:** one input feeds multiple branches that must all complete
before a downstream step runs.

---

## Mental Model

```
         ┌── arm_a: parse_trade → update_trade_stats ──┐
event ───┤                                             ├── join → output
         └── arm_b: parse_quote → update_book ────────┘
```

Each arm is a sub-pipeline. The arms run in parallel (conceptually — they
still run on one thread). The `join` step receives references to each arm's
output and produces a single combined value.

---

## Minimal DAG

```rust
use nexus_rt::{DagBuilder, Res, ResMut, WorldBuilder, Handler};

#[derive(nexus_rt::Resource, Default)]
struct Stats {
    count: u64,
    sum: i64,
}

// Root step: takes the event by value, returns the value to propagate
fn root(event: i64) -> i64 {
    event
}

// Arm A: compute double
fn double(x: &i64) -> i64 {
    x * 2
}

// Arm B: compute square
fn square(x: &i64) -> i64 {
    x * x
}

// Merge: takes references to each arm's output, returns combined
fn merge(mut stats: ResMut<Stats>, doubled: &i64, squared: &i64) -> () {
    stats.count += 1;
    stats.sum += *doubled + *squared;
}

fn main() {
    let mut wb = WorldBuilder::new();
    wb.register(Stats::default());
    let mut world = wb.build();

    let mut dag = DagBuilder::<i64>::new()
        .root(root, world.registry())
        .fork()
            .arm(|seed| seed.then(double, world.registry()))
            .arm(|seed| seed.then(square, world.registry()))
        .join(merge, world.registry())
        .build();

    dag.run(&mut world, 5);
    // Stats: count=1, sum = 10 (double) + 25 (square) = 35
}
```

---

## When to Use DAG

### Fan-out with aggregation

```
market_data_update
    ├── update_order_book (arm)
    ├── update_vwap        (arm)
    └── update_spread      (arm)
         ↓
    publish_analytics(book, vwap, spread)
```

One input (market data tick), three independent computations, one
downstream step that sees all three results.

### Parallel validation

```
order
    ├── check_risk_limits   (arm)
    ├── check_credit        (arm)
    └── check_compliance    (arm)
         ↓
    accept_or_reject(risk_ok, credit_ok, compliance_ok)
```

All three checks run. The merge step decides based on all results.

### Dependent computations that share input

A pipeline would force you to pick an order: risk THEN credit THEN
compliance. A DAG expresses that they're independent — any order works,
and conceptually they happen "together."

---

## Root vs Then

The first step in a DAG is special:

```rust
.root(f, registry)   // f takes the event BY VALUE
.then(f, registry)   // f takes &previous_output
```

Root consumes the event. Subsequent `.then` steps take references to the
previous output. This mirrors how data flows: the root owns the event,
everything downstream borrows from the chain.

---

## Arms

An arm is a branch that forks from the main chain:

```rust
.fork()
    .arm(|seed| {
        seed
            .then(parse, reg)
            .then(validate, reg)
            .then(enrich, reg)
    })
    .arm(|seed| seed.then(shortcut, reg))
.join(merge, reg)
```

The `seed` is a starting point that takes `&In` (the fork's input type).
Inside the closure, you build the arm with the same combinators as a
Pipeline: `.then`, `.guard`, `.tap`, `.scan`, etc.

Each arm produces its own output type. The merge function sees all arm
outputs by reference.

---

## Merge Function Signature

```rust
fn merge(
    // Params first
    config: Res<Config>,
    mut state: ResMut<State>,
    // Then references to each arm's output
    arm0: &ArmAOutput,
    arm1: &ArmBOutput,
    arm2: &ArmCOutput,
) -> FinalOutput {
    // Compute from all arms
}
```

Params come first, arm outputs last (by reference). The return type is
the DAG's new output — subsequent `.then` steps see this.

---

## Nested Forks

Arms can fork further:

```rust
.root(root, reg)
.fork()
    .arm(|seed| {
        seed
            .then(parse, reg)
            .fork()
                .arm(|s| s.then(sub_a, reg))
                .arm(|s| s.then(sub_b, reg))
            .join(merge_inner, reg)
    })
    .arm(|seed| seed.then(other, reg))
.join(merge_outer, reg)
```

The nested fork produces a single output (from `merge_inner`) that feeds
back into the outer arm's chain. The outer merge sees the outer arm
outputs.

---

## Complete Example: Market Data Analytics

```rust
use nexus_rt::{DagBuilder, Res, ResMut, WorldBuilder, Handler};

#[derive(Clone, Copy)]
struct MarketTick {
    symbol_id: u32,
    bid: f64,
    ask: f64,
    bid_size: u32,
    ask_size: u32,
}

#[derive(nexus_rt::Resource, Default)]
struct BookState {
    last_mid: f64,
}

#[derive(nexus_rt::Resource, Default)]
struct SpreadStats {
    ewma: f64,
}

#[derive(nexus_rt::Resource, Default)]
struct VwapAccumulator {
    pv: f64,
    volume: u64,
}

// Root: consume the tick, pass it through
fn receive_tick(tick: MarketTick) -> MarketTick {
    tick
}

// Arm 1: compute mid price
fn compute_mid(tick: &MarketTick) -> f64 {
    (tick.bid + tick.ask) / 2.0
}

// Arm 2: compute spread
fn compute_spread(tick: &MarketTick) -> f64 {
    tick.ask - tick.bid
}

// Arm 3: compute size-weighted mid (vwap contribution)
fn compute_vwap_contrib(tick: &MarketTick) -> (f64, u64) {
    let size = (tick.bid_size + tick.ask_size) as u64;
    let pv = (tick.bid + tick.ask) / 2.0 * size as f64;
    (pv, size)
}

// Merge: update all stats
fn update_analytics(
    mut book: ResMut<BookState>,
    mut spread: ResMut<SpreadStats>,
    mut vwap: ResMut<VwapAccumulator>,
    mid: &f64,
    sprd: &f64,
    vwap_contrib: &(f64, u64),
) {
    book.last_mid = *mid;
    spread.ewma = 0.9 * spread.ewma + 0.1 * sprd;
    vwap.pv += vwap_contrib.0;
    vwap.volume += vwap_contrib.1;
}

fn build_analytics_dag(world: &WorldBuilder) -> impl Handler<MarketTick> {
    DagBuilder::<MarketTick>::new()
        .root(receive_tick, world.registry())
        .fork()
            .arm(|seed| seed.then(compute_mid, world.registry()))
            .arm(|seed| seed.then(compute_spread, world.registry()))
            .arm(|seed| seed.then(compute_vwap_contrib, world.registry()))
        .join(update_analytics, world.registry())
        .build()
}
```

---

## Batch Processing

Like Pipeline, DAG supports batch mode with pre-allocated input buffers:

```rust
let mut dag = DagBuilder::<MarketTick>::new()
    .root(receive_tick, reg)
    .fork()
        // ... arms
    .join(merge, reg)
    .build_batch(1024);  // pre-allocate for 1024 ticks per batch
```

Use `build_batch` when you process ticks in bursts (e.g., draining a
network buffer with many messages).

---

## Performance

A DAG compiles to a single monomorphized function — just like Pipeline.
Every arm, every combinator, every merge is inlined. No vtable, no Box,
no dynamic dispatch. The `use<>` capture rules from Rust 2024 apply: if
you return `impl Handler<E>` from a factory, add `+ use<Params, Chain>`
to exclude the registry borrow.

---

## DAG vs Pipeline: Decision Guide

| Question | Use |
|----------|-----|
| Is the flow strictly linear? | Pipeline |
| Do multiple computations need the same input? | DAG |
| Does a downstream step need results from multiple branches? | DAG |
| Are branches independent (no shared intermediate state)? | DAG |
| Is one branch just a side effect (log, metric)? | Pipeline with `.tap()` |
| Do you need to route based on a condition (if/else)? | Pipeline with `.route()` |
| Do you need fan-out to multiple distinct handlers? | Pipeline with `.dispatch()` or DAG |
| Do you need to route to one arm by a runtime key? | `.dispatch_on` — see [dispatch.md](dispatch.md) |

To route a DAG to one of N arms by a discriminant or projected key, use
`.dispatch_on` (the DAG's keyed-dispatch primitive; arms take the value by
reference). See [dispatch.md](dispatch.md).

---

## Need Per-Instance State?

This document covers `DagBuilder` — DAGs composed from `Handler`-style
functions where state lives in the World.

If each arm needs access to per-instance context (per-instrument state,
per-session counters, per-connection metadata), use `CtxDagBuilder`
instead. It's the parallel API for callbacks, threading `&mut C` through
every arm and the merge function. See
[callbacks.md — Callback DAGs](callbacks.md#callback-dags-ctxdag) for the
full guide.

Same fork/arm/join structure, same builder pattern, same monomorphization
— just with a context parameter threaded through every step.

## See Also

- [pipelines.md](pipelines.md) — Linear processing chains
- [dispatch.md](dispatch.md) — Runtime keyed dispatch (`.dispatch_on` is the DAG routing primitive)
- [handlers.md](handlers.md) — Writing the functions used as arms and merges
- [callbacks.md](callbacks.md) — When you need per-instance state, including
  CtxPipeline and CtxDag (the callback parallels of Pipeline and Dag)
