# Handlers

Handlers are the units of work in nexus-rt. They're plain Rust functions
whose parameters declare what resources they need. The framework resolves
parameters at build time and dispatches with zero overhead.

## Writing a Handler

```rust
use nexus_rt::{Res, ResMut, Resource};

#[derive(Resource)]
struct OrderBook { depth: u64 }
#[derive(Resource)]
struct Config { max_depth: u64 }

fn process_order(
    mut state: ResMut<OrderBook>,   // exclusive write access
    config: Res<Config>,             // shared read access
    event: u64,                      // the event being processed
) {
    state.depth += event.min(config.max_depth);
}
```

**Rules:**
- Must be a **named function** (not a closure -- see below)
- Parameters are `Res<T>`, `ResMut<T>`, `Local<T>`, `Option<Res<T>>`,
  `Seq`, `SeqMut`, `Shutdown`, `RegistryRef`, or the event type
- The event type (if present) must be the last parameter
- Up to 8 resource parameters are supported

## Building and Dispatching a Handler

Convert a function into a `Handler` using `into_handler`, then call `run`:

```rust
use nexus_rt::{WorldBuilder, Res, ResMut, IntoHandler, Handler, Resource};

#[derive(Resource)]
struct Counter(u64);

fn tick(mut counter: ResMut<Counter>, event: u32) {
    counter.0 += event as u64;
}

let mut wb = WorldBuilder::new();
wb.register(Counter(0));
let mut world = wb.build();

let mut handler = tick.into_handler(world.registry());

handler.run(&mut world, 10u32);
handler.run(&mut world, 5u32);

assert_eq!(world.resource::<Counter>().0, 15);
```

`into_handler` resolves all parameter types against the registry at build
time, producing pre-resolved `ResourceId`s. At dispatch time, there's no
type lookup -- just pointer dereferences.

## Handler Trait

Handlers implement the `Handler<E>` trait:

```rust
pub trait Handler<E>: Send {
    fn run(&mut self, world: &mut World, event: E);
    fn name(&self) -> &'static str { "<unnamed>" }
}
```

The framework calls `run()` with the World and the event. The handler's
internal state (resolved ResourceIds, Local storage) handles the rest.

## Parameter Types Reference

| Parameter | Access | When to Use |
|-----------|--------|------------|
| `Res<T>` | `&T` (shared) | Read-only access to a resource |
| `ResMut<T>` | `&mut T` (exclusive) | Read-write access to a resource |
| `Local<T>` | `&mut T` (per-handler) | State private to this handler instance |
| `Option<Res<T>>` | `Option<&T>` | Resource that may not be registered |
| `Option<ResMut<T>>` | `Option<&mut T>` | Same, mutable |
| `Seq` | `Sequence` (read-only) | Current event sequence number |
| `SeqMut<'_>` | mutable sequence | Advance the sequence (stamp outbound) |
| `Shutdown<'_>` | `&AtomicBool` | Trigger cooperative shutdown |
| `RegistryRef<'_>` | `&Registry` | Create handlers at runtime |
| `#[derive(Param)]` struct | grouped fields | Bundle multiple params into one |
| Event type | by value | The event being processed (last param) |

## Multiple Resources

Handlers can access up to 8 resources simultaneously:

```rust
use nexus_rt::{WorldBuilder, Res, ResMut, IntoHandler, Handler, Resource, no_event};

#[derive(Resource)]
struct Prices { best_bid: f64, best_ask: f64 }
#[derive(Resource)]
struct Position { qty: i64 }
#[derive(Resource)]
struct RiskLimits { max_position: i64 }

fn check_risk(
    prices: Res<Prices>,
    position: Res<Position>,
    limits: Res<RiskLimits>,
) {
    let exposure = position.qty.abs() as f64 * prices.best_ask;
    if position.qty.abs() > limits.max_position {
        // breach -- would trigger alert
    }
}

let mut wb = WorldBuilder::new();
wb.register(Prices { best_bid: 100.0, best_ask: 101.0 });
wb.register(Position { qty: 50 });
wb.register(RiskLimits { max_position: 100 });
let mut world = wb.build();

let mut handler = no_event(check_risk).into_handler(world.registry());
handler.run(&mut world, ());
```

## Ignoring the Event

A handler that only reads resources and doesn't need the event can omit the
trailing `_: Event` parameter entirely. Build it with
`into_handler_event_ignored` instead of `into_handler` — the method name says
"drop the event," so no wrapper or `_` placeholder is needed:

```rust
use nexus_rt::{Handler, IntoHandlerIgnoringEvent, ResMut, Resource, WorldBuilder};
use std::time::Instant;

#[derive(Resource)]
struct Ticks(u64);

fn on_tick(mut t: ResMut<Ticks>) {   // no `_: Instant`
    t.0 += 1;
}

let mut wb = WorldBuilder::new();
wb.register(Ticks(0));
let mut world = wb.build();

// The event type (here `Instant`) is inferred from where the handler is stored.
let mut h: Box<dyn Handler<Instant>> =
    Box::new(on_tick.into_handler_event_ignored(world.registry()));
h.run(&mut world, Instant::now());   // the Instant is dropped
assert_eq!(world.resource::<Ticks>().0, 1);
```

This works for **any** event type, including borrowed / non-`'static` events
(e.g. a `&[u8]` wire buffer), because the produced handler stores no event. The
`no_event(f)` wrapper shown above is the shorthand for the special `E = ()` case;
`into_handler_event_ignored` is the general form.

## Optional Resources

Handlers can declare optional dependencies that resolve to `None` if the
resource was not registered:

```rust
use nexus_rt::{WorldBuilder, Res, ResMut, IntoHandler, Handler, Resource};

#[derive(Resource)]
struct Counter(u64);
#[derive(Resource)]
struct DebugConfig { verbose: bool }

fn on_tick(
    mut counter: ResMut<Counter>,
    debug: Option<Res<DebugConfig>>,
    event: u64,
) {
    counter.0 += event;
    if let Some(debug) = debug {
        if debug.verbose {
            // extra logging when debug is registered
        }
    }
}

// DebugConfig is NOT registered -- handler still works
let mut wb = WorldBuilder::new();
wb.register(Counter(0));
let mut world = wb.build();

let mut handler = on_tick.into_handler(world.registry());
handler.run(&mut world, 5u64);
assert_eq!(world.resource::<Counter>().0, 5);
```

## Local Per-Handler State

`Local<T>` stores state private to a handler instance. It lives inside
the handler, not in the World. Each handler instance gets its own copy.
`T` must implement `Default`.

```rust
use nexus_rt::{WorldBuilder, ResMut, Local, IntoHandler, Handler, Resource};

#[derive(Resource)]
struct Total(u64);

fn accumulate(mut local: Local<u64>, mut total: ResMut<Total>, event: u64) {
    *local += 1;  // counts calls for THIS handler instance
    total.0 += event;
}

let mut wb = WorldBuilder::new();
wb.register(Total(0));
let mut world = wb.build();

let mut handler = accumulate.into_handler(world.registry());
handler.run(&mut world, 10u64);
handler.run(&mut world, 20u64);

assert_eq!(world.resource::<Total>().0, 30);
// local counter is 2, but only accessible inside the handler
```

## Seq and SeqMut: Sequence Numbers

`Seq` reads the world's current sequence number. `SeqMut` can advance it --
useful for stamping outbound messages with monotonic sequence numbers.

```rust
use nexus_rt::{WorldBuilder, IntoHandler, Handler, Seq, SeqMut, Resource, ResMut, no_event};

#[derive(Resource)]
struct LastSeq(i64);

fn stamp_outbound(seq: Seq, mut last: ResMut<LastSeq>) {
    last.0 = seq.get().as_i64();
}

let mut wb = WorldBuilder::new();
wb.register(LastSeq(0));
let mut world = wb.build();

// Advance the sequence (normally done by the driver)
world.next_sequence();

let mut handler = no_event(stamp_outbound).into_handler(world.registry());
handler.run(&mut world, ());
assert_eq!(world.resource::<LastSeq>().0, 1);
```

## Shutdown Flag

`Shutdown` accesses the world's cooperative shutdown flag. Handlers trigger
shutdown; the poll loop checks it each iteration.

```rust
use nexus_rt::{WorldBuilder, IntoHandler, Handler, no_event};
use nexus_rt::shutdown::Shutdown;

fn on_fatal(shutdown: Shutdown) {
    shutdown.trigger();
}

let mut world = WorldBuilder::new().build();
let shutdown_handle = world.shutdown_handle();

let mut handler = no_event(on_fatal).into_handler(world.registry());
handler.run(&mut world, ());

assert!(shutdown_handle.is_shutdown());
```

## RegistryRef: Creating Handlers at Runtime

`RegistryRef` gives read-only registry access during dispatch, enabling
dynamic handler creation (e.g., when a new connection arrives):

```rust
use nexus_rt::{
    WorldBuilder, ResMut, IntoHandler, IntoCallback, Handler,
    Resource, RegistryRef, Virtual,
};

#[derive(Resource)]
struct Connections {
    handlers: Vec<Virtual<u64>>,
}

struct ConnCtx { id: u64 }

fn on_data(ctx: &mut ConnCtx, _event: u64) {
    // per-connection processing
}

fn on_new_connection(
    mut conns: ResMut<Connections>,
    reg: RegistryRef,
    event: u64,
) {
    let ctx = ConnCtx { id: event };
    let cb = on_data.into_callback(ctx, &reg);
    conns.handlers.push(Box::new(cb));
}

let mut wb = WorldBuilder::new();
wb.register(Connections { handlers: vec![] });
let mut world = wb.build();

let mut handler = on_new_connection.into_handler(world.registry());
handler.run(&mut world, 42u64);

assert_eq!(world.resource::<Connections>().handlers.len(), 1);
```

## Callback: Handler with Owned Context

For handlers that own per-instance state beyond what's in the World,
use `Callback` via `IntoCallback`. The context is the first parameter:

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoCallback, Handler, Resource};

struct SessionCtx {
    session_id: u64,
    message_count: u64,
}

#[derive(Resource)]
struct TotalMessages(u64);

fn on_message(
    ctx: &mut SessionCtx,           // owned context -- first param
    mut total: ResMut<TotalMessages>, // world resource
    event: u64,
) {
    ctx.message_count += 1;
    total.0 += event;
}

let mut wb = WorldBuilder::new();
wb.register(TotalMessages(0));
let mut world = wb.build();

let mut cb = on_message.into_callback(
    SessionCtx { session_id: 1, message_count: 0 },
    world.registry(),
);

cb.run(&mut world, 10u64);
cb.run(&mut world, 20u64);

// Context is pub -- accessible outside dispatch
assert_eq!(cb.ctx.message_count, 2);
assert_eq!(cb.ctx.session_id, 1);
assert_eq!(world.resource::<TotalMessages>().0, 30);
```

See [callbacks.md](callbacks.md) for the full callback guide including
templates and pipeline integration.

## OpaqueHandler: Raw World Access

When you need `&mut World` directly (e.g., for dynamic resource access),
use `OpaqueHandler`. This is an escape hatch -- prefer typed parameters.

```rust
use nexus_rt::{WorldBuilder, Handler, Resource, OpaqueHandler};

#[derive(Resource)]
struct Counter(u64);

let mut wb = WorldBuilder::new();
wb.register(Counter(0));
let mut world = wb.build();

let mut handler = OpaqueHandler::new(|world: &mut nexus_rt::World, event: u64| {
    world.resource_mut::<Counter>().0 += event;
});

handler.run(&mut world, 5u64);
assert_eq!(world.resource::<Counter>().0, 5);
```

`OpaqueHandler` does a HashMap lookup per resource access (cold path).
Named functions with `Res<T>`/`ResMut<T>` parameters get direct pointer
access (hot path).

## Virtual: Heterogeneous Handler Collections

`Virtual<E>` is `Box<dyn Handler<E>>` -- for storing handlers with different
concrete types in a single collection:

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoHandler, IntoCallback, Handler, Resource, Virtual};

#[derive(Resource)]
struct State(u64);

fn add(mut s: ResMut<State>, event: u64) { s.0 += event; }
fn mul(ctx: &mut u64, mut s: ResMut<State>, _event: u64) { s.0 *= *ctx; }

let mut wb = WorldBuilder::new();
wb.register(State(0));
let mut world = wb.build();
let reg = world.registry();

let h1: Virtual<u64> = Box::new(add.into_handler(reg));
let h2: Virtual<u64> = Box::new(mul.into_callback(3u64, reg));

let mut handlers: Vec<Virtual<u64>> = vec![h1, h2];

for h in &mut handlers {
    h.run(&mut world, 5u64);
}

// 0 + 5 = 5, then 5 * 3 = 15
assert_eq!(world.resource::<State>().0, 15);
```

With the `smartptr` feature, `FlatVirtual<E>` stores handlers inline (no
heap allocation, panics if too large) and `FlexVirtual<E>` stores inline
with heap fallback.

## HandlerFn Type Alias

`HandlerFn<F, Params>` is the concrete type produced by `into_handler`.
Use it when you need to name the type rather than box it:

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoHandler, Handler, Resource, HandlerFn};

#[derive(Resource)]
struct Val(u64);

fn inc(mut v: ResMut<Val>, event: u64) { v.0 += event; }

let mut wb = WorldBuilder::new();
wb.register(Val(0));
let mut world = wb.build();

// HandlerFn names the concrete type -- no heap allocation
let mut handler: HandlerFn<fn(ResMut<Val>, u64), _> = inc.into_handler(world.registry());
handler.run(&mut world, 1u64);
assert_eq!(world.resource::<Val>().0, 1);
```

In practice, `let mut h = f.into_handler(reg)` with type inference is
simpler. `HandlerFn` is useful when you need the type for struct fields
or explicit annotations.

## Pre-built Handlers as IntoHandler

Any type that already implements `Handler<E>` -- including `Pipeline`,
`Dag`, `Callback`, and `TemplatedHandler` -- satisfies `IntoHandler<E, Resolved>`
via a blanket impl. This means you can pass a built pipeline directly
to any API that expects `impl IntoHandler`:

```rust
use nexus_rt::{WorldBuilder, PipelineBuilder, ResMut, IntoHandler, Handler, Resource};

#[derive(Resource)]
struct Out(u64);

fn double(x: u32) -> u64 { x as u64 * 2 }
fn store(mut out: ResMut<Out>, x: u64) { out.0 = x; }

let mut wb = WorldBuilder::new();
wb.register(Out(0));
let mut world = wb.build();
let reg = world.registry();

let pipeline = PipelineBuilder::<u32>::new()
    .then(double, reg)
    .then(store, reg)
    .build();

// Pipeline IS a Handler -- pass it directly where Handler is expected
let mut handler: Box<dyn Handler<u32>> = Box::new(pipeline);
handler.run(&mut world, 5u32);
assert_eq!(world.resource::<Out>().0, 10);
```

## Returning Handlers from Functions (Rust 2024)

When you write a factory function that takes `&Registry` and returns
`impl Handler<E>`, Rust 2024's default capture rules hold the registry
borrow in the return type -- blocking subsequent `WorldBuilder` calls.

Add `+ use<...>` listing only the type parameters the return type holds:

```rust
use nexus_rt::{Handler, IntoHandler, Res, ResMut, Resource};
use nexus_rt::world::Registry;

fn build_handler(reg: &Registry) -> impl Handler<u32> + use<> {
    tick.into_handler(reg)
}

#[derive(Resource)]
struct Counter(u64);

fn tick(mut c: ResMut<Counter>, event: u32) {
    c.0 += event as u64;
}
```

The `&Registry` is consumed during `into_handler` -- the returned handler
holds pre-resolved `ResourceId`s, not a reference to the registry. The
`use<>` annotation tells the compiler exactly that.

This applies to all handler-producing patterns: `into_handler`,
`into_callback`, `PipelineBuilder::build()`, `DagBuilder::build()`,
and `template.generate()`.

## Why Named Functions?

```rust
// Works
fn my_handler(state: ResMut<MyState>, event: MyEvent) { /* ... */ }

// Does not compile
let h = (|state: ResMut<MyState>, event: MyEvent| { /* ... */ }).into_handler(registry);
```

The parameter resolution uses Higher-Ranked Trait Bounds (HRTBs) with
a double-bound pattern: one bound for type inference, another for
dispatch. Closure types are unnameable and interact poorly with this
pattern -- the compiler can't infer the parameter types through the
HRTB. Named functions have concrete types that resolve cleanly.

This is the same limitation Bevy has with its systems. In practice,
handlers are typically standalone functions -- it's a natural code
organization pattern.

**Exception:** Arity-0 closures (no resource parameters) DO work:

```rust
use nexus_rt::{WorldBuilder, IntoHandler, Handler};

let world = WorldBuilder::new().build();
// Works -- no Res/ResMut parameters
let mut h = (|event: u32| { let _ = event; }).into_handler(world.registry());
h.run(&mut { WorldBuilder::new().build() }, 42u32);
```
