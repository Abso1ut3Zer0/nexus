# Runtime Keyed Dispatch

Routing one value to one of N handlers by a discriminant is a routine need — a
command enum, a per-venue market-data feed, a message-type tag. nexus-rt gives
you two ways to build that fan-out:

- **Runtime dispatch tables** — `#[derive(Dispatchable)]` plus the
  `.dispatch_variant` / `.dispatch_on` / `.dispatch_map` combinators. The arms
  are wired at *runtime* as builder steps, so the table composes: a plugin can
  register arms, a config can decide the wiring, an arm can itself be a
  pre-built pipeline, values returned by the arms bubble up so the pipeline can
  keep going, and the dispatch is a first-class chain step like `.then`.
- **`select!`** — a macro that builds the table at *compile* time. The arms
  inline to a `match` / jump table with a direct call and no indirection.

**Reach for the tables first.** They are the recommended default: easier to
assemble, runtime-composable, and — because the table is a flat array indexed by
a dense ordinal, never a hash — the cost over the compile-time `select!` is *one
indirect call*, roughly a cycle at p50 (see [Performance](#performance)).
`select!` is the power-user tool: reach for it when the arms are fixed at compile
time and you are chasing the last cycle on the very hottest path (see
[pipelines.md — Dispatching by Discriminant](pipelines.md#dispatching-by-discriminant--select)).

---

## Choosing a dispatch

| You are routing on… | Use | Each arm receives | Surfaces |
|---|---|---|---|
| an enum you hold **directly** | **`.dispatch_variant`** | that variant's **typed payload** (already unwrapped) | Pipeline, CtxPipeline |
| a **field** of the value, or an enum key computed from it | **`.dispatch_on`** | the **whole value** | Pipeline, CtxPipeline, DagChain, CtxDagChain |
| a **non-enum** `Hash + Eq` key (string, `usize`, resource-derived tag) | **`.dispatch_map`** | the **whole value** | Pipeline, CtxPipeline |
| arms fixed at compile time, last cycle on the hottest path | **`select!`** | whole value (or projected — see pipelines.md) | a macro at one call site |

Rules of thumb:

- The value **is** the enum → `dispatch_variant`. It is the only form that hands
  each arm the typed payload for free, and the fastest of the tables (nearly
  `select!`).
- The value **carries** the routing key (a `source` field, a `msg_type`) →
  `dispatch_on`. Also the DAG's routing primitive.
- The key is not a `Dispatchable` enum → `dispatch_map`. It is the slowest
  (hash + wrapping), so prefer `dispatch_on` whenever the key can be an enum.
- Arms compile-time-fixed and you need the last cycle → `select!`.

---

## `#[derive(Dispatchable)]`

The derive turns an enum into a dense ordinal space and generates the markers
the combinators consume.

```rust
use nexus_rt::{Dispatchable, VariantOf};

#[derive(Dispatchable)]
enum Cmd {
    RouteAway(u32),    // ordinal 0
    Reprice(u32, i64), // ordinal 1
    Halt,              // ordinal 2
}

assert_eq!(Cmd::VARIANTS, 3);
assert_eq!(Cmd::RouteAway(7).ordinal(), 0);
assert_eq!(Cmd::Halt.ordinal(), 2);
```

What you get:

- **`Cmd::VARIANTS`** — the variant count, and **`ordinal(&self) -> usize`** —
  a dense index in `0..VARIANTS` in declaration order. It is *dense* on purpose:
  it normalizes sparse or explicit discriminants (`enum E { A = 1, B = 100 }`
  still maps to `0, 1`), and it is defined for **data-carrying** variants, where
  `as usize` does not even compile. Dense ordinals are what let the dispatch
  table be a flat `[_; VARIANTS]` array instead of a hash map.

- **Per-variant `VariantOf` markers**, one zero-sized type per variant, in a
  generated module named `<enum_snake_case>_variants` — here `cmd_variants`.
  Each marker ties a variant to its **payload type** (`()` for a unit variant,
  the field type for a single-field variant, a tuple of field types for a
  multi-field variant), its ordinal, and an unchecked `unwrap`. This is the
  bridge `.dispatch_variant` uses to hand each arm its typed payload:

  ```rust
  // (Cmd as above.) The caller knows the value is `RouteAway`, so it is sound.
  let payload: u32 = unsafe { cmd_variants::RouteAway::unwrap(Cmd::RouteAway(7)) };
  assert_eq!(payload, 7);
  ```

  You rarely call `unwrap` yourself — you pass the marker to `.arm()` and the
  combinator does it for you. (Only unit and tuple variants are supported;
  named-field struct variants are rejected by the derive.)

- **Tuple-product composite keys, without hashing.** A pair of `Dispatchable`
  enums is itself `Dispatchable`: `(A, B)` packs the two dense spaces row-major
  into one `0..(A::VARIANTS * B::VARIANTS)` range
  (`a.ordinal() * B::VARIANTS + b.ordinal()`). Distinct pairs map to distinct
  ordinals, so a single flat table stays exact for a two-dimensional key.

  ```rust
  use nexus_rt::Dispatchable;

  #[derive(Dispatchable)]
  enum Coarse { X, Y }          // 2 variants
  #[derive(Dispatchable)]
  enum Fine { P, Q, R }         // 3 variants

  assert_eq!(<(Coarse, Fine)>::VARIANTS, 6);
  ```

  Larger keys nest today — `(A, (B, C))` is `Dispatchable` — or get direct impls
  later.

---

## `.dispatch_variant` — route on the enum's own discriminant

The pipeline input **is** the `Dispatchable` enum. Each arm is wired with its
variant marker and receives that variant's **typed payload** — already
unwrapped. This is the form to use when the message you route on is itself the
enum, and it is the fastest of the tables.

```rust
use nexus_rt::{PipelineBuilder, ResMut, Resource, WorldBuilder, Handler};

#[derive(nexus_rt::Dispatchable)]
enum Cmd {
    RouteAway(u32),    // single field  → payload `u32`
    Reprice(u32, i64), // multi-field   → payload `(u32, i64)`
    Halt,              // unit          → payload `()`
    Cancel(u64),       // left unset below
}

#[derive(Resource, Default)]
struct Book { routed: u64, repriced: i64, halts: u32 }

// Params first, then the variant's typed payload last.
fn on_route_away(mut book: ResMut<Book>, level: u32)      { book.routed += level as u64; }
fn on_reprice(mut book: ResMut<Book>, p: (u32, i64))      { book.repriced += p.1; }
fn on_halt(mut book: ResMut<Book>, _p: ())                { book.halts += 1; }

let mut wb = WorldBuilder::new();
wb.register(Book::default());
let mut world = wb.build();
let reg = world.registry();

let mut pipeline = PipelineBuilder::<Cmd>::new()
    .dispatch_variant(reg, |d| {
        d.arm(cmd_variants::RouteAway, on_route_away)
            .arm(cmd_variants::Reprice, on_reprice)
            .arm(cmd_variants::Halt, on_halt)
            .default_noop() // `Cancel` unset — ignore it (see below)
    })
    .build();

pipeline.run(&mut world, Cmd::RouteAway(42));
pipeline.run(&mut world, Cmd::Reprice(7, -3));
pipeline.run(&mut world, Cmd::Halt);
pipeline.run(&mut world, Cmd::Cancel(999)); // unset → the no-op default
```

- The `.arm(marker, step)` spelling names the variant by its generated marker
  (`cmd_variants::RouteAway`), which is what fixes the arm's payload type. An arm
  is a normal step — a named `fn`, an arity-0 closure `|p: u32| { … }`, an
  `Opaque` `&mut World` closure, or a [pre-built pipeline](#arms-can-be-pre-built-pipelines) —
  following the usual [resolution tiers](pipelines.md#three-resolution-tiers).
- **The table must be exhaustive or carry a `.default`** — see
  [Exhaustive or `.default`](#exhaustive-or-default). Unlike an arm, a `.default`
  receives the **whole enum** (it has no single variant, so no payload):

  ```rust
  // The default takes the whole `Cmd` (no single variant → no payload).
  fn on_other(mut book: ResMut<Book>, _cmd: Cmd) { /* record the unhandled cmd */ }

  let mut pipeline = PipelineBuilder::<Cmd>::new()
      .dispatch_variant(reg, |d| {
          d.arm(cmd_variants::RouteAway, on_route_away)
              .default(on_other) // catches Reprice, Halt, Cancel
      })
      .build();
  ```

- **Values bubble up.** If the arms return `T`, the dispatch returns `T` and you
  can `.then(...)` after it; if they return `()` it is terminal — see
  [Returning values](#returning-values-bubble-up).
- It is available on **`Pipeline` and `CtxPipeline`**, each as a pipeline entry
  point (dispatch is the first step) and as a continuation (dispatch after a
  `.then` that produces the enum). On a `CtxPipeline` every arm threads `&mut C`
  first (`fn(&mut C, Params.., payload)`) and the default is `fn(&mut C, Cmd)` —
  see [callbacks.md](callbacks.md). It is **not** on the DAG surface, because DAG
  steps take their value **by reference** and a by-reference unwrap of a
  moved-out payload does not fit the model — use `.dispatch_on` for DAG routing.

---

## `.dispatch_on` — route on a projected key

Here the dispatch key is a **projection** of the value — `Fn(&V) -> K` for any
`Dispatchable` `K` — not the value's own discriminant. Because the projection
carries no variant guarantee, there is no unchecked unwrap: every arm receives
the **whole value**. Use this when the thing you route on is a *field* of the
message, or a key computed from it.

```rust
use nexus_rt::{PipelineBuilder, ResMut, Resource, WorldBuilder, Handler};

#[derive(nexus_rt::Dispatchable, Clone, Copy)]
enum Source { Binance, Coinbase, Kraken }

#[derive(Clone, Copy)]
struct Tick { source: Source, px: u64 }

#[derive(Resource, Default)]
struct Feeds { binance: u64, coinbase: u64 }

// Arms get the WHOLE `Tick`, not a payload.
fn on_binance(mut f: ResMut<Feeds>, t: Tick)  { f.binance = t.px; }
fn on_coinbase(mut f: ResMut<Feeds>, t: Tick) { f.coinbase = t.px; }

let mut wb = WorldBuilder::new();
wb.register(Feeds::default());
let mut world = wb.build();
let reg = world.registry();

let mut pipeline = PipelineBuilder::<Tick>::new()
    .dispatch_on(
        |t: &Tick| t.source, // projection: value → key
        reg,
        |d| {
            d.arm(Source::Binance, on_binance)
                .arm(Source::Coinbase, on_coinbase)
                .default_noop() // `Kraken` unset — ignore it
        },
    )
    .build();

pipeline.run(&mut world, Tick { source: Source::Binance, px: 100 });
pipeline.run(&mut world, Tick { source: Source::Kraken, px: 300 }); // default no-op
```

- `.arm(key, step)` takes the **key value** directly (`Source::Binance`), not a
  marker — the key is any `Dispatchable`, dispatched by its `ordinal()`.
- Same exhaustive-or-`.default` rule as `.dispatch_variant`; the default also
  receives the whole value.
- Available on **all four surfaces**: `Pipeline`, `CtxPipeline`, `DagChain`, and
  `CtxDagChain`, each as an entry point and a continuation. On the ctx surfaces
  every arm (and the default) threads `&mut C` first. On the **DAG** surfaces the
  arms take the value **by reference** (`fn(Params.., &V)`), matching how DAG
  steps borrow — this is why `.dispatch_on` is the DAG's dispatch primitive:

  ```rust
  use nexus_rt::DagBuilder;

  // (Source / Tick / Feeds as above.) DAG arm: borrowed value last.
  fn dag_on_binance(mut f: ResMut<Feeds>, t: &Tick) { f.binance = t.px; }

  let mut dag = DagBuilder::<Tick>::new()
      .root(|t: Tick| t, reg)
      .dispatch_on(
          |t: &Tick| t.source,
          reg,
          |d| d.arm(Source::Binance, dag_on_binance).default_noop(),
      )
      .build();
  ```

### Composite (tuple-product) key

Because `(A, B)` is `Dispatchable`, `.dispatch_on` routes on a two-dimensional
key with a single flat table and no hashing — the projection just returns the
pair:

```rust
use nexus_rt::{PipelineBuilder, ResMut, Resource, WorldBuilder, Handler};

#[derive(nexus_rt::Dispatchable, Clone, Copy)]
enum Venue { Cex, Dex }
#[derive(nexus_rt::Dispatchable, Clone, Copy)]
enum Side { Bid, Ask }

#[derive(Clone, Copy)]
struct Quote { venue: Venue, side: Side, px: u64 }

#[derive(Resource, Default)]
struct Hits { count: u64 }

fn on_cex_bid(mut h: ResMut<Hits>, _q: Quote) { h.count += 1; }

let mut wb = WorldBuilder::new();
wb.register(Hits::default());
let mut world = wb.build();
let reg = world.registry();

let mut pipeline = PipelineBuilder::<Quote>::new()
    .dispatch_on(
        |q: &Quote| (q.venue, q.side), // composite key: 2 * 2 = 4 dense slots
        reg,
        |d| d.arm((Venue::Cex, Side::Bid), on_cex_bid).default_noop(),
    )
    .build();

pipeline.run(&mut world, Quote { venue: Venue::Cex, side: Side::Bid, px: 10 });
```

---

## `.dispatch_map` — route on a non-enum `Hash + Eq` key

The escape hatch from the ordinal `Vec` table for keys that are **not**
`Dispatchable` enums — an arbitrary or composite key (a `String`, a `usize`, a
protocol tag), or a discriminant produced by a resource lookup upstream.
`.dispatch_map` swaps the flat array for an
[`FxHashMap`](https://docs.rs/rustc-hash) lookup; the projection maps the value
to the key, and every arm receives the **whole value**.

```rust
use nexus_rt::{PipelineBuilder, ResMut, Resource, WorldBuilder, Handler};

#[derive(Clone)]
struct Order { symbol: String, qty: u64 }

#[derive(Resource, Default)]
struct Fills { btc: u64, eth: u64, other: u64 }

fn on_btc(mut f: ResMut<Fills>, o: Order)   { f.btc += o.qty; }
fn on_eth(mut f: ResMut<Fills>, o: Order)   { f.eth += o.qty; }
fn on_other(mut f: ResMut<Fills>, o: Order) { f.other += o.qty; }

let mut wb = WorldBuilder::new();
wb.register(Fills::default());
let mut world = wb.build();
let reg = world.registry();

let mut pipeline = PipelineBuilder::<Order>::new()
    .dispatch_map(
        |o: &Order| o.symbol.clone(), // key: any Hash + Eq
        reg,
        |d| {
            d.arm("BTC-USD".to_string(), on_btc)
                .arm("ETH-USD".to_string(), on_eth)
                .default(on_other) // required — the key space is open
        },
    )
    .build();

pipeline.run(&mut world, Order { symbol: "BTC-USD".into(), qty: 5 });
pipeline.run(&mut world, Order { symbol: "SOL-USD".into(), qty: 9 }); // → default
```

- Because the key space is **open** (any `Hash + Eq` value, not a bounded
  ordinal range), a `.default` — or `.default_noop()` — is **always required**.
  Omitting it panics at construction.
- Same whole-value arms and value bubble-up as `.dispatch_on`; available on
  `Pipeline` and `CtxPipeline`.
- It is the slowest of the tables (hash + probe versus an array index). Prefer
  `.dispatch_on` whenever the key can be a `Dispatchable` enum, and reach for
  `.dispatch_map` only when it genuinely can't.

---

## Returning values (bubble-up)

All three combinators are **`Out`-generic**: `Out` is the type the arms return,
inferred from the arm bodies (every arm and the `.default` must agree on it).

- **Arms return `()`** → the dispatch is **terminal**. It is the end of the
  chain; `.build()` follows. This is the common command-handler case.
- **Arms return `T`** → the dispatch **returns `T`**, and the value bubbles up as
  the chain's output, so you can keep composing:

  ```rust
  use nexus_rt::{PipelineBuilder, Resource, WorldBuilder, Handler};

  #[derive(nexus_rt::Dispatchable, Clone, Copy)]
  enum Req { A(u64), B(u64) }

  #[derive(Resource, Default)]
  struct Log(u64);

  let mut wb = WorldBuilder::new();
  wb.register(Log::default());
  let mut world = wb.build();
  let reg = world.registry();

  let mut pipeline = PipelineBuilder::<Req>::new()
      .dispatch_variant(reg, |d| {
          d.arm(req_variants::A, |x: u64| x + 1) // arms return u64
              .arm(req_variants::B, |x: u64| x * 2)
      })
      .then(|n: u64, mut log: nexus_rt::ResMut<Log>| log.0 = n, reg) // continues on the bubbled-up value
      .build();

  pipeline.run(&mut world, Req::A(41));
  assert_eq!(world.resource::<Log>().0, 42);
  ```

Note `req_variants::A` and `req_variants::B` are exhaustive here, so no
`.default` is needed.

---

## Exhaustive or `.default`

Every dispatch table must either **arm every key** or **carry a `.default`** —
otherwise construction **panics deterministically, before any dispatch runs**.
This is the runtime analog of `select!` requiring a `_` arm for a non-exhaustive
value match: a missing case is a wiring bug, and you find out at build time, not
when the unhandled key finally shows up in production at 3am.

- **`.default(step)`** — the catch-all. It receives the **whole value** (the
  whole enum for `.dispatch_variant`, since a fallback has no single variant),
  and it **wins even when the table is otherwise exhaustive**.
- **`.default_noop()`** — sugar for "ignore any unset key", available **only on
  terminal (`Out = ()`) tables**. Use it when you deliberately want unlisted
  keys to fall through and do nothing. This is the explicit opt-out of the
  exhaustiveness requirement.
- **Fully armed, no `.default`** — fine, and the fastest shape: the fallback slot
  is a never-taken panic arm the compiler can see is unreachable.

Key-space differences:

- `.dispatch_variant` / `.dispatch_on` have a **bounded** key space
  (`0..VARIANTS`), so "exhaustive" is well-defined — arm all `VARIANTS` and you
  need no default.
- `.dispatch_map` has an **open** key space, so a `.default` (or `.default_noop()`)
  is **always** required.

The panic message names the method, the key type, and the armed/total count, so
a partial table is easy to diagnose:

```text
dispatch_variant on `Cmd`: 3/4 keys armed and no `.default` —
arm every key or add `.default`/`.default_noop()`
```

---

## Arms can be pre-built pipelines

A terminal (`Out = ()`) `Pipeline` is itself a resolved step — it implements
`IntoStep` — so you can build a sub-pipeline once and hand it to `.arm()`
directly, no `Opaque` wrapper closure needed:

```rust
use nexus_rt::{PipelineBuilder, ResMut, Resource, WorldBuilder, Handler};

#[derive(nexus_rt::Dispatchable, Clone, Copy)]
enum Cmd { Fast(u64), Slow(u64) }

#[derive(Resource, Default)]
struct Acc(u64);

let mut wb = WorldBuilder::new();
wb.register(Acc::default());
let mut world = wb.build();
let reg = world.registry();

// A whole pipeline, pre-built, used as one dispatch arm.
let slow_path = PipelineBuilder::<u64>::new()
    .then(|x: u64| x * 10, reg)
    .then(|x: u64, mut a: ResMut<Acc>| a.0 += x, reg)
    .build();

let mut pipeline = PipelineBuilder::<Cmd>::new()
    .dispatch_variant(reg, |d| {
        d.arm(cmd_variants::Fast, |x: u64, mut a: ResMut<Acc>| a.0 += x)
            .arm(cmd_variants::Slow, slow_path) // the pre-built pipeline is the arm
    })
    .build();

pipeline.run(&mut world, Cmd::Slow(3)); // runs slow_path: Acc += 30
```

The same holds for a built `CtxPipeline` on the `Ctx*` surfaces (it implements
`IntoCtxStep`). This lets you compose the dispatch out of independently-built,
independently-tested pipelines — the composability that the compile-time
`select!` cannot offer.

---

## Context threading (`Ctx*` surfaces)

On `CtxPipeline` / `CtxDagChain`, every arm and the `.default` thread the
context `&mut C` as their first parameter (`fn(&mut C, Params.., value)`), exactly
as ordinary ctx steps do — see [callbacks.md](callbacks.md). The compile-time
complement `select!` also has a ctx form (`select! { ctx: C, … }`) for when the
arms are fixed and you want context threading on the jump table.

---

## Performance

Cycles per dispatch, 8 keys, all arms doing identical work (accumulate a payload
into a `World` resource) so only the dispatch mechanism differs. Reproduce with
`examples/perf_dispatch.rs`.

| Dispatch | p50 | p90 | p99 | p999 | p9999 |
|---|---|---|---|---|---|
| `select!` (compile-time, inlined) | 4 | 5 | 7 | ~10 | ~70 |
| `.dispatch_variant` (ordinal array, typed) | 5 | 6 | ~8 | ~15 | ~85 |
| `.dispatch_on` (ordinal array, whole value) | 7 | 10 | ~13 | ~18 | ~85 |
| `.dispatch_on` (tuple-product key) | 8 | 9 | ~13 | ~21 | ~75 |
| raw `FxHashMap` (hand-rolled) | 7 | 8 | ~14 | ~22 | ~85 |
| `.dispatch_map` (FxHashMap combinator) | 9 | 9 | ~17 | ~28 | ~90 |

> **Measurement caveat — read the p50/p90, not the tail.** These were taken
> pinned to physical core 0 (`taskset -c 0`), best-of-5, but with **turbo boost
> left ON** (it could not be disabled on the measurement box), timed with
> `rdtsc` (raw TSC ticks), and reported as **percentiles of per-batch means**.
> So **p50 and p90 are the reliable per-op signal**; the p99/p999/p9999 columns
> are dominated by system noise (scheduler tick, IRQ, frequency throttling), not
> the dispatch mechanism. Re-run `examples/perf_dispatch.rs` under `taskset -c 0`
> **with turbo disabled** on a quiescent machine for publication-grade numbers.

What the numbers say:

- **`.dispatch_variant` costs ~+1 cycle over inlined `select!`** (5 vs 4 at
  p50). That is a runtime-composable, typed-payload dispatch table for basically
  nothing — the reason the tables are the recommended default.
- **Ordinal tables match or beat a hashmap at small N and pull ahead as N
  grows.** `.dispatch_on` (7 p50) sits right on the raw `FxHashMap` (7 p50) at 8
  keys, with no hashing and no rehash cliff as the key count rises.
- **`.dispatch_map` is the slowest** (9 p50 — hash + wrapping over the ordinal
  index), so prefer `.dispatch_on` whenever the key is a `Dispatchable` enum and
  keep `.dispatch_map` for genuinely non-enum keys.
- **Beyond p99 everything — including `select!` — converges** to the same
  ~70–100-cycle band. That tail is machine noise, not the mechanism: no dispatch
  strategy escapes a scheduler tick or an IRQ.

See [BENCHMARKS.md](../BENCHMARKS.md) for the workspace benchmark index.

---

## Soundness

`.dispatch_variant`'s typed payload comes from `VariantOf::unwrap`, the feature's
**only** `unsafe`. It is sound because the arm is reached **only** via the
value's own `ordinal()` — the table slot for ordinal *i* holds the arm for
variant *i*, and we only enter it when `value.ordinal() == i`, so the value
provably **is** that variant. Debug builds carry a `debug_assert!` that trips
before the `unreachable_unchecked` if that invariant were ever violated, and the
path is covered by miri. `.dispatch_on` and `.dispatch_map` have **no** unsafe at
all — they hand over the whole value, so there is nothing to unwrap. See
[UNSAFE_AND_SOUNDNESS.md](UNSAFE_AND_SOUNDNESS.md#7-dispatch-payload-unwrap-dispatchrs--2-unsafe-blocks)
for the full argument and the miri coverage.

---

## See Also

- [pipelines.md](pipelines.md) — the pipeline builder and `select!`, the
  compile-time complement to these combinators
- [dag.md](dag.md) — DAGs, where `.dispatch_on` is the routing primitive
- [callbacks.md](callbacks.md) — `CtxPipeline` / `CtxDag`, the ctx-threading
  parallels
- [derives.md](derives.md) — `#[derive(Dispatchable)]` alongside the other
  derives
