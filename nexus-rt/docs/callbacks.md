# Callbacks -- Handlers with Owned Context

Callbacks are handlers that own per-instance state beyond what's in the
World. Each callback instance has its own private context, accessible
both inside and outside dispatch.

## When to Use Callback vs Handler

Use `IntoHandler` when all state lives in the World.

Use `IntoCallback` when each handler instance needs its own private state:

- **Per-timer context** -- each timer carries its own order ID, retry count,
  or deadline metadata
- **Per-connection state** -- each socket handler carries its own codec state,
  read buffer, or session context
- **Protocol state machines** -- each instance tracks its own position in a
  handshake or reconnection sequence

## Creating a Callback

The function signature puts the context first, then resources, then the event:

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoCallback, Handler, Resource};

#[derive(Resource)]
struct TotalBytes(u64);

struct ConnectionCtx {
    connection_id: u64,
    bytes_received: u64,
}

fn on_data(
    ctx: &mut ConnectionCtx,           // owned context -- first param
    mut total: ResMut<TotalBytes>,     // world resource
    event: Vec<u8>,                    // event -- last param
) {
    ctx.bytes_received += event.len() as u64;
    total.0 += event.len() as u64;
}

let mut wb = WorldBuilder::new();
wb.register(TotalBytes(0));
let mut world = wb.build();

let mut cb = on_data.into_callback(
    ConnectionCtx { connection_id: 42, bytes_received: 0 },
    world.registry(),
);

cb.run(&mut world, vec![1, 2, 3]);
cb.run(&mut world, vec![4, 5]);

// Context is pub -- directly accessible
assert_eq!(cb.ctx.connection_id, 42);
assert_eq!(cb.ctx.bytes_received, 5);
assert_eq!(world.resource::<TotalBytes>().0, 5);
```

## Accessing Context Outside Dispatch

The `ctx` field on `Callback` is `pub`. Drivers can read or mutate it
between dispatches -- for example, to update a deadline or check a counter:

```rust
use nexus_rt::{WorldBuilder, IntoCallback, Handler, no_event};

struct RetryCtx {
    attempts: u32,
    max_retries: u32,
}

fn on_retry(ctx: &mut RetryCtx) {
    ctx.attempts += 1;
}

let mut world = WorldBuilder::new().build();

let mut cb = no_event(on_retry).into_callback(
    RetryCtx { attempts: 0, max_retries: 3 },
    world.registry(),
);

cb.run(&mut world, ());
cb.run(&mut world, ());

// Check context between dispatches
if cb.ctx.attempts >= cb.ctx.max_retries {
    // stop retrying
}
assert_eq!(cb.ctx.attempts, 2);

// Mutate context between dispatches
cb.ctx.max_retries = 5;
```

## Multiple Callbacks with Different Contexts

Each callback instance owns its own context. This is the primary use case --
per-connection, per-instrument, or per-order handlers:

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoCallback, Handler, Resource};

#[derive(Resource)]
struct OrderState { total_filled: u64 }

struct OrderCtx {
    order_id: u64,
    filled_qty: u64,
}

fn on_fill(ctx: &mut OrderCtx, mut state: ResMut<OrderState>, fill_qty: u64) {
    ctx.filled_qty += fill_qty;
    state.total_filled += fill_qty;
}

let mut wb = WorldBuilder::new();
wb.register(OrderState { total_filled: 0 });
let mut world = wb.build();
let reg = world.registry();

// Each callback has its own OrderCtx
let mut order_a = on_fill.into_callback(
    OrderCtx { order_id: 100, filled_qty: 0 },
    reg,
);
let mut order_b = on_fill.into_callback(
    OrderCtx { order_id: 200, filled_qty: 0 },
    reg,
);

order_a.run(&mut world, 50u64);
order_b.run(&mut world, 30u64);
order_a.run(&mut world, 20u64);

assert_eq!(order_a.ctx.filled_qty, 70);
assert_eq!(order_b.ctx.filled_qty, 30);
assert_eq!(world.resource::<OrderState>().total_filled, 100);
```

## Callbacks with Local State

Callbacks support `Local<T>` in addition to their owned context. This is
useful when you want both shared-nothing handler state (Local) AND per-instance
metadata (context):

```rust
use nexus_rt::{WorldBuilder, ResMut, Local, IntoCallback, Handler, Resource};

#[derive(Resource)]
struct Log { entries: Vec<String> }

struct Ctx { name: String }

fn on_event(ctx: &mut Ctx, mut call_count: Local<u64>, mut log: ResMut<Log>, event: u32) {
    *call_count += 1;
    log.entries.push(format!("{}: event {} (call #{})", ctx.name, event, *call_count));
}

let mut wb = WorldBuilder::new();
wb.register(Log { entries: vec![] });
let mut world = wb.build();
let reg = world.registry();

let mut cb = on_event.into_callback(Ctx { name: "conn-1".into() }, reg);
cb.run(&mut world, 1u32);
cb.run(&mut world, 2u32);

assert_eq!(world.resource::<Log>().entries.len(), 2);
```

## Callbacks as Box<dyn Handler<E>>

Callbacks implement `Handler<E>`, so they can be stored in heterogeneous
collections alongside regular handlers:

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoHandler, IntoCallback, Handler, Resource, Virtual};

#[derive(Resource)]
struct Counter(u64);

fn add(mut c: ResMut<Counter>, event: u64) { c.0 += event; }
fn mul(ctx: &mut u64, mut c: ResMut<Counter>, _event: u64) { c.0 *= *ctx; }

let mut wb = WorldBuilder::new();
wb.register(Counter(0));
let mut world = wb.build();
let reg = world.registry();

let h1: Virtual<u64> = Box::new(add.into_handler(reg));
let h2: Virtual<u64> = Box::new(mul.into_callback(3u64, reg));

let mut handlers: Vec<Virtual<u64>> = vec![h1, h2];
for h in &mut handlers {
    h.run(&mut world, 5u64);
}

// 0 + 5 = 5, then 5 * 3 = 15
assert_eq!(world.resource::<Counter>().0, 15);
```

**Note:** Boxing erases the concrete type, so you lose direct access to
`cb.ctx`. If you need context access, keep the concrete `Callback` type.

## CallbackTemplate: Stamping Many Callbacks

When you need many callbacks from the same function with different contexts,
use `CallbackTemplate` to resolve parameters once and stamp cheaply.
See [templates.md](templates.md) for the full guide.

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoHandler, Handler, Resource};
use nexus_rt::template::{CallbackTemplate, CallbackBlueprint};

#[derive(Resource)]
struct SharedState { total: u64 }

struct ConnCtx { id: u64, bytes: u64 }

fn on_data(ctx: &mut ConnCtx, mut state: ResMut<SharedState>, event: u64) {
    ctx.bytes += event;
    state.total += event;
}

// Define a blueprint (binds the function signature)
nexus_rt::callback_blueprint!(
    OnDataBp,
    Context = ConnCtx,
    Event = u64,
    Params = (ResMut<'static, SharedState>,)
);

let mut wb = WorldBuilder::new();
wb.register(SharedState { total: 0 });
let mut world = wb.build();
let reg = world.registry();

// Resolve once
let template = CallbackTemplate::<OnDataBp>::new(on_data, reg);

// Stamp 100 callbacks -- no parameter resolution, just memcpy of state
let mut callbacks: Vec<_> = (0..100)
    .map(|id| template.generate(ConnCtx { id, bytes: 0 }))
    .collect();

callbacks[0].run(&mut world, 10u64);
callbacks[99].run(&mut world, 20u64);

assert_eq!(callbacks[0].ctx.bytes, 10);
assert_eq!(callbacks[99].ctx.bytes, 20);
assert_eq!(world.resource::<SharedState>().total, 30);
```

## Self-Rescheduling Callbacks (Periodic Timers, Retries)

`CallbackTemplate` is `Copy`, so a callback's **context can carry its own
template** and use it to stamp its own successor — a periodic re-arm, a
retry-with-backoff, any "produce the next me" pattern. This happens entirely
through the safe API: no `&mut World` reach-in, no unsafe borrow split. The
self-reference is not a cyclic type — the template holds a fn pointer and
pre-resolved state, never the context — so a context can hold a
`CallbackTemplate<K>` field as plain data.

The canonical case is a **self-rearming timer**. The callback fires, does its
work, then stamps a fresh copy of itself and schedules it back into the timer
wheel at the next deadline:

```rust
use std::time::{Duration, Instant};
use nexus_rt::{WorldBuilder, ResMut};
use nexus_rt::timer::{TimerInstaller, TimerWheel, Wheel};
use nexus_rt::template::CallbackTemplate;

// The context carries the callback's OWN template (the self-reference),
// plus whatever per-timer state it needs.
struct HeartbeatCtx {
    template: CallbackTemplate<Heartbeat>,
    interval: Duration,
    remaining: u32,
}

// `now: Instant` is the fire time the timer driver dispatches with.
fn heartbeat(ctx: &mut HeartbeatCtx, mut wheel: ResMut<TimerWheel>, now: Instant) {
    // ... do the periodic work (send a ping, sample a metric) ...

    if ctx.remaining > 0 {
        // Copy our own template out of the context and stamp the successor.
        let next = ctx.template.generate(HeartbeatCtx {
            template: ctx.template,          // `Copy` — no move, template stays usable
            interval: ctx.interval,
            remaining: ctx.remaining - 1,
        });
        // Re-arm: schedule the successor one interval out. The wheel stores
        // `Box<dyn Handler<Instant>>`, so the concrete callback type is erased.
        wheel.schedule_forget(now + ctx.interval, Box::new(next));
    }
}

nexus_rt::callback_blueprint!(
    Heartbeat,
    Context = HeartbeatCtx,
    Event = Instant,
    Params = (ResMut<'static, TimerWheel>,)
);

// Setup: install the timer driver, then prime the first heartbeat.
let mut wb = WorldBuilder::new();
let mut timer = wb.install_driver(TimerInstaller::new(Wheel::unbounded(64, Instant::now())));
let mut world = wb.build();

let template = CallbackTemplate::<Heartbeat>::new(heartbeat, world.registry());
let first = template.generate(HeartbeatCtx {
    template,                                 // the template copies into the context
    interval: Duration::from_millis(10),
    remaining: 5,
});
world.resource_mut::<TimerWheel>().schedule_forget(Instant::now(), Box::new(first));

// In the poll loop, `timer.poll(&mut world, Instant::now())` fires due
// callbacks; each fire re-arms the next until `remaining` reaches 0.
```

**Storing typed callbacks instead of erasing them.** The timer wheel erases to
`Box<dyn Handler<Instant>>`, which sidesteps the type entirely. If instead you
keep a *typed* slot — a resource holding `Option<TemplatedCallback<K>>` or a
`Vec<TemplatedCallback<K>>` — that resource type is **self-referential**
(`Slot` → `TemplatedCallback<K>` → context → reads `Slot`). This is a
well-formed, finite type, and `#[derive(Resource)]` works on it:

```rust
use nexus_rt::Resource;
use nexus_rt::template::TemplatedCallback;

#[derive(Resource)]
struct Pending(Option<TemplatedCallback<Heartbeat>>);
```

(Earlier versions of the `Resource` derive overflowed auto-trait resolution on
this self-referential shape; that is fixed — see [derives.md](derives.md).)

## Returning Callbacks from Functions (Rust 2024)

When a factory function takes `&Registry` and returns `impl Handler<E>`,
Rust 2024 captures the registry borrow. Use `+ use<...>` to exclude it:

```rust
use nexus_rt::{Handler, IntoCallback, ResMut, Resource, no_event};
use nexus_rt::world::Registry;

#[derive(Resource)]
struct State(u64);

fn on_event(ctx: &mut u64, mut s: ResMut<State>) {
    s.0 += *ctx;
}

fn build_callback(ctx: u64, reg: &Registry) -> impl Handler<()> + use<> {
    no_event(on_event).into_callback(ctx, reg)
}
```

## Callback Pipelines (CtxPipeline)

Callbacks have their own pipeline builder: `CtxPipelineBuilder`. It mirrors
the regular `PipelineBuilder` but threads `&mut C` (the callback's context)
through every step. Each step function takes the context FIRST, then
resources, then the input.

This is the parallel of the regular [pipelines.md](pipelines.md), but for
context-owning steps. Use it when a multi-stage processing chain needs
per-instance state at each step.

### Step function convention

```
context first → params → input last
fn step(ctx: &mut C, res: Res<T>, input: In) -> Out
```

Just like callbacks, only named functions work for arity ≥1. Arity-0
closures (context + input only) work everywhere.

### A complete callback pipeline

```rust
use nexus_rt::{
    CtxPipelineBuilder, IntoCallback, Res, ResMut, Resource, WorldBuilder, Handler,
};

#[derive(Resource, Default)]
struct OrderLog { count: u64 }

#[derive(Resource)]
struct RiskLimits { max_qty: u64 }

#[derive(Clone, Copy)]
struct RawOrder { qty: u64, price: f64 }

#[derive(Clone, Copy)]
struct ValidatedOrder { qty: u64, price: f64 }

// Per-session context — holds state across pipeline runs
struct SessionCtx {
    session_id: u32,
    orders_seen: u64,
    last_price: f64,
}

// Step 1: validate against per-session state and risk limits
fn validate(
    ctx: &mut SessionCtx,
    risk: Res<RiskLimits>,
    order: RawOrder,
) -> Option<ValidatedOrder> {
    ctx.orders_seen += 1;
    if order.qty > risk.max_qty { return None; }
    Some(ValidatedOrder { qty: order.qty, price: order.price })
}

// Step 2: tap to update per-session state (no transformation)
fn track_last_price(ctx: &mut SessionCtx, order: &ValidatedOrder) {
    ctx.last_price = order.price;
}

// Step 3: persist to log (terminal — returns ())
fn record(_ctx: &mut SessionCtx, mut log: ResMut<OrderLog>, _order: ValidatedOrder) {
    log.count += 1;
}

// The callback function builds and runs the pipeline.
// We have to embed it in a callback because the pipeline needs &mut Ctx.
fn run_session_pipeline(
    ctx: &mut SessionCtx,
    world_input: (RawOrder, &mut nexus_rt::World),
) {
    // Note: in real use, the world+input are typically threaded via
    // a Callback wrapping the pipeline — see "Wiring it up" below.
    let _ = (ctx, world_input);
}

let mut wb = WorldBuilder::new();
wb.register(OrderLog::default());
wb.register(RiskLimits { max_qty: 1000 });
let mut world = wb.build();
let reg = world.registry();

// Build the pipeline. CtxPipelineBuilder takes no registry at construction
// time; combinators take it the same way as normal PipelineBuilder.
let mut pipeline = CtxPipelineBuilder::<SessionCtx, RawOrder>::new()
    .then(validate, reg)        // Option<ValidatedOrder>
    .map(|_ctx: &mut SessionCtx, v: ValidatedOrder| v, reg)  // unwrap-style passthrough
    // .tap is a ref-step: takes &Out, no transformation
    // (skipping for brevity — see ctx_pipeline source for full combinator list)
    .build();

// Run it manually — the pipeline takes (&mut Ctx, &mut World, In)
let mut ctx = SessionCtx { session_id: 1, orders_seen: 0, last_price: 0.0 };
pipeline.run(&mut ctx, &mut world, RawOrder { qty: 100, price: 50.0 });
```

### Wiring a CtxPipeline into a Callback

The most common pattern: wrap a `CtxPipeline` inside a `Callback` so the
runtime treats it as a regular `Handler<E>`. The callback owns the
context AND the pipeline; its handler function dispatches into the
pipeline:

```rust
use nexus_rt::{CtxPipeline, IntoCallback, Handler};

// (Define the pipeline as above — let's call it `OrderPipeline`)
type OrderPipeline = nexus_rt::CtxPipeline<SessionCtx, RawOrder, /* chain type */ ()>;

struct SessionState {
    pipeline: OrderPipeline,
    ctx: SessionCtx,
}

// In practice you build one of these per session and store it in a
// HashMap<SessionId, SessionState>, then dispatch incoming orders
// to the right session.
```

For the full ergonomic pattern, use a `Callback` whose context IS the
session state, and whose function body invokes the pipeline:

```rust
fn handle_order(state: &mut SessionState, order: RawOrder) {
    // Pipeline run requires &mut World — see the runtime poll loop
    // for how to get one. Inside a Handler<E>::run, you have it.
}
```

### Combinators available on CtxPipeline

All the same names as `PipelineBuilder`, with `&mut C` threaded through:

- `.then(f, reg)` — transform with context
- `.guard(pred, reg)` — filter; pred is `&mut C, &Out -> bool`
- `.tap(observer, reg)` — side effect on `&Out` with context
- `.map(f, reg)` — transform `Option<T>` inner value
- `.and_then(f, reg)` — short-circuit `Option<T>`
- `.catch(f, reg)` — handle `Result<T, E>` error path
- `.map_err(f, reg)` — transform error type
- `.build()` — terminal (when `Out = ()` or `Out = Option<()>`)

Some combinators from `PipelineBuilder` are not yet on `CtxPipeline`
(`scan`, `dispatch`, `route`, `tee`, `splat`, bool combinators, etc.).
They can be added when a use case needs them.

---

## Callback DAGs (CtxDag)

For fan-out + merge with per-instance context, use `CtxDagBuilder`. It
mirrors the regular `DagBuilder` (see [dag.md](dag.md)) but threads
`&mut C` through every arm and the merge function.

### A complete callback DAG

```rust
use nexus_rt::{CtxDagBuilder, Res, ResMut, Resource, WorldBuilder};

#[derive(Resource, Default)]
struct Stats { trades: u64, vwap_pv: f64, vwap_qty: u64 }

#[derive(Clone, Copy)]
struct Trade { price: f64, qty: u64, symbol_id: u32 }

// Per-instrument context
struct InstrumentCtx {
    symbol_id: u32,
    last_price: f64,
    trade_count: u64,
}

// Root: take the trade by value, return it to propagate
fn receive_trade(_ctx: &mut InstrumentCtx, trade: Trade) -> Trade {
    trade
}

// Arm 1: extract price for downstream mid calc
fn extract_price(ctx: &mut InstrumentCtx, trade: &Trade) -> f64 {
    ctx.last_price = trade.price;
    trade.price
}

// Arm 2: extract notional (price * qty) for VWAP
fn extract_notional(_ctx: &mut InstrumentCtx, trade: &Trade) -> (f64, u64) {
    (trade.price * trade.qty as f64, trade.qty)
}

// Merge: combine arm outputs and update both stats and per-instrument ctx
fn update_all(
    ctx: &mut InstrumentCtx,
    mut stats: ResMut<Stats>,
    price: &f64,
    notional: &(f64, u64),
) {
    ctx.trade_count += 1;
    stats.trades += 1;
    stats.vwap_pv += notional.0;
    stats.vwap_qty += notional.1;
    let _ = price;
}

let mut wb = WorldBuilder::new();
wb.register(Stats::default());
let mut world = wb.build();
let reg = world.registry();

let mut dag = CtxDagBuilder::<InstrumentCtx, Trade>::new()
    .root(receive_trade, reg)
    .fork()
        .arm(|seed| seed.then(extract_price, reg))
        .arm(|seed| seed.then(extract_notional, reg))
    .join(update_all, reg)
    .build();

let mut ctx = InstrumentCtx { symbol_id: 42, last_price: 0.0, trade_count: 0 };
dag.run(&mut ctx, &mut world, Trade { price: 100.0, qty: 50, symbol_id: 42 });

assert_eq!(ctx.trade_count, 1);
assert_eq!(world.resource::<Stats>().trades, 1);
```

### When to use CtxDag vs CtxPipeline

Same decision as for handlers (see [dag.md](dag.md)):

- **CtxPipeline** — linear flow, context threaded through stages
- **CtxDag** — one input fans out to multiple branches, all needing the
  same context, results merged downstream

### Wiring a CtxDag into a Callback

Same pattern as CtxPipeline: wrap the dag + context in a `Callback` so
the runtime sees a `Handler<E>`. The callback's function dispatches into
`dag.run(&mut ctx, &mut world, event)`.

---

## Named Functions Only

The same HRTB limitation as `IntoHandler` applies: closures with resource
parameters don't work. Use named `fn` items.

Arity-0 closures (context + event only, no resources) DO work:

```rust
use nexus_rt::{WorldBuilder, IntoCallback, Handler};

struct Ctx { count: u32 }

let mut world = WorldBuilder::new().build();

let mut cb = (|ctx: &mut Ctx, event: u32| {
    ctx.count += event;
}).into_callback(Ctx { count: 0 }, world.registry());

cb.run(&mut world, 5u32);
assert_eq!(cb.ctx.count, 5);
```

---

## Dispatching by Discriminant — `select!` with `ctx:`

The `select!` macro supports callback pipelines via the `ctx:` option.
Adding `ctx: MyContextType` switches the expansion from `resolve_step`
to `resolve_ctx_step`, threading `&mut C` through every arm.

```rust
use nexus_rt::{CtxPipelineBuilder, select};

struct SessionCtx { count: u32 }

fn on_new(ctx: &mut SessionCtx, order: OrderKind) { ctx.count += 1; }
fn on_cancel(ctx: &mut SessionCtx, order: OrderKind) { ctx.count += 10; }

let mut pipeline = CtxPipelineBuilder::<SessionCtx, OrderKind>::new()
    .then(
        select! {
            reg,
            ctx: SessionCtx,
            OrderKind::New    => on_new,
            OrderKind::Cancel => on_cancel,
            OrderKind::Amend  => on_new,
        },
        reg,
    )
    .build();

let mut ctx = SessionCtx { count: 0 };
pipeline.run(&mut ctx, &mut world, OrderKind::Cancel);
assert_eq!(ctx.count, 10);
```

All three tiers (`key:`, `project:`, default arms) work identically
to the handler form. The only difference is `ctx:` triggers callback
resolution and the emitted closure takes `&mut C` as its first parameter.

See [pipelines.md — Dispatching by Discriminant](pipelines.md#dispatching-by-discriminant--select)
for the full tier 1/2/3 guide.
