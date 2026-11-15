# nexus-rt

Single-threaded, event-driven runtime primitives with pre-resolved dispatch.

`nexus-rt` provides the building blocks for constructing runtimes where
user code runs as handlers dispatched over shared state. It is **not** an
async runtime — there is no task scheduler, no work stealing, no `Future`
polling. Your `main()` is the executor.

## Philosophy

`nexus-rt` is a lightweight, single-threaded runtime for event-driven
systems. It provides the state container, dependency injection, lifecycle
management, and dispatch infrastructure — but no implicit executor. Your
`main()` is the event loop. You decide what polls, in what order, and when.

The core idea: **declare what your functions need, and the framework wires
it up at build time.** Write plain Rust functions with `Res<T>` and
`ResMut<T>` parameters. The framework resolves those dependencies once when
you build the handler, then dispatches with zero framework overhead — a
single pointer deref per resource, no hashing, no lookups, no allocation.

**What nexus-rt is:**
- A typed singleton store (`World`) with direct-pointer access
- A dependency injection system for plain functions
- Composable handler and pipeline abstractions
- Single-threaded by design — for latency, not by accident

**What nexus-rt is not:**
- Not an async runtime (no `Future`, no `async`/`await`)
- Not a game engine ECS (no entities, no components, no archetypes)
- Not opinionated about IO, networking, or wire protocols — bring your own

If you need an analogy: it's the Bevy `SystemParam` + `World` model,
stripped down to singletons and adapted for sequential event processing
instead of parallel frame-based simulation.

## What in the World?!

### The World

Everything in `nexus-rt` revolves around the `World` — a typed singleton
store where each registered type gets exactly one value:

```rust
use nexus_rt::WorldBuilder;

let mut builder = WorldBuilder::new();
builder.register::<u64>(0);                   // one u64, initialized to 0
builder.register::<String>("hello".into());   // one String
let mut world = builder.build();              // freeze — no more registration
```

`WorldBuilder` is mutable — you register types into it. `build()` produces
a frozen `World`. After that, no types can be added or removed. This
constraint enables direct pointer access: each type gets a `ResourceId`
that is a direct pointer to its storage, and dispatch-time access is a
single pointer deref — zero framework overhead.

Outside of handlers, you can read and write resources directly:

```rust
let mut builder = nexus_rt::WorldBuilder::new();
builder.register::<u64>(0);
let mut world = builder.build();

assert_eq!(*world.resource::<u64>(), 0);
*world.resource_mut::<u64>() = 42;
assert_eq!(*world.resource::<u64>(), 42);
```

### Res\<T\> and ResMut\<T\> — Dependency Injection

The real power is that handler functions **declare** their dependencies in
their signatures. You don't pass resources manually — the framework
resolves them:

```rust
use nexus_rt::{Res, ResMut};

fn process(config: Res<u64>, mut state: ResMut<String>, event: f64) {
    if *config > 10 {
        *state = format!("processed {event}");
    }
}
```

This function declares:
- `Res<u64>` — "I need shared read access to the `u64` resource"
- `ResMut<String>` — "I need exclusive write access to the `String` resource"
- `event: f64` — "I receive an `f64` as my event" (always the last parameter)

When you convert this function into a handler, the framework resolves each
parameter against the `World`'s registry. At dispatch time, it fetches
the resources by direct pointer — no `HashMap` lookup, no type checking,
just a pointer deref.

`ResMut<T>` provides exclusive write access via `DerefMut`. For change
detection, use the reactor system's interest-based notification — mark
data sources when resources change, and subscribed reactors wake
automatically.

### Handlers — Connecting Functions to the World

`IntoHandler` converts a plain function into a `Handler` — the object-safe
dispatch trait. The conversion resolves parameters; after that, calling
`.run()` is a direct dispatch through pre-resolved indices:

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoHandler, Handler};

fn tick(mut counter: ResMut<u64>, event: u32) {
    *counter += event as u64;
}

let mut builder = WorldBuilder::new();
builder.register::<u64>(0);
let mut world = builder.build();

let mut handler = tick.into_handler(world.registry());

handler.run(&mut world, 10u32);
handler.run(&mut world, 20u32);
assert_eq!(*world.resource::<u64>(), 30);
```

The event parameter is always last. Everything before it is resolved as a
`Param` from the registry. If a required resource isn't registered,
`into_handler` panics at build time — not at dispatch time. Fail fast.

> **Named functions only.** Closures do not work with `IntoHandler` for
> arity-1+ (functions with `Param` arguments). This is a Rust type
> inference limitation with HRTBs and GATs — the same limitation Bevy has.
> Arity-0 pipeline steps (no `Param`) do accept closures.

### Plugins — Composable Registration

When you have a group of related resources, package them as a `Plugin`:

```rust
use nexus_rt::{Plugin, WorldBuilder};

struct PriceCache { prices: Vec<f64> }
struct RiskLimits { max_position: u64 }

struct TradingPlugin {
    risk_cap: u64,
}

impl Plugin for TradingPlugin {
    fn build(self, world: &mut WorldBuilder) {
        world.register(PriceCache { prices: Vec::new() });
        world.register(RiskLimits { max_position: self.risk_cap });
    }
}

let mut builder = WorldBuilder::new();
builder.install_plugin(TradingPlugin { risk_cap: 1000 });
// PriceCache and RiskLimits are now registered
```

Plugins are consumed by value — fire and forget. They're for organizing
registration, not for runtime behavior. Compose your system from multiple
plugins, each owning a domain's resources.

### Lifecycle — Startup, Run, Shutdown

After `build()`, you often need to initialize state that depends on
multiple resources being present. `run_startup` runs a system once with
full dependency injection:

```rust
use nexus_rt::{WorldBuilder, Res, ResMut};

struct PriceCache { prices: Vec<f64> }
struct RiskLimits { max_position: u64 }

let mut builder = WorldBuilder::new();
builder.register(PriceCache { prices: Vec::new() });
builder.register(RiskLimits { max_position: 100 });

fn initialize(mut cache: ResMut<PriceCache>, config: Res<RiskLimits>) {
    // Both resources are available — set up initial state
    cache.prices.extend_from_slice(&[100.0, 200.0, 300.0]);
}

let mut world = builder.build();
world.run_startup(initialize);
```

For the event loop itself, `world.run()` polls until a handler triggers
shutdown:

```rust,ignore
use nexus_rt::shutdown::Shutdown;

// Handler triggers shutdown when done
fn check_done(counter: Res<u64>, shutdown: Res<Shutdown>) {
    if *counter >= 100 {
        shutdown.shutdown();
    }
}

world.run(|world| {
    // Your poll loop — called every iteration until shutdown
    timer.poll(world, Instant::now());
    io.poll(world, timeout);
    scheduler.run(world);
});
```

`world.run()` is a convenience — it's just `while !shutdown { f(self) }`.
You can also write the loop yourself if you need access to the shutdown
handle, custom exit conditions, or pre/post-iteration bookkeeping. Both
patterns are equivalent; `world.run()` is shorter when a shutdown flag is
all you need.

`Shutdown` is automatically registered by `WorldBuilder::build()`. The
event loop owns a `ShutdownHandle` (obtained via `world.shutdown_handle()`
if needed outside `world.run()`). With the `signals` feature,
`shutdown.enable_signals()` registers SIGINT/SIGTERM handlers
automatically.

The full lifecycle:

```text
WorldBuilder::new()
    → register resources
    → install_plugin(plugin)
    → install_driver(installer) → returns poller
    → build()
    → World (frozen)
        → run_startup(init_fn)     // one-shot init
        → run(|world| { ... })     // poll loop until shutdown
```

## Design

`nexus-rt` is heavily inspired by [Bevy ECS](https://bevyengine.org/).
Handlers as plain functions, `Param` for declarative dependency
injection, `Res<T>` / `ResMut<T>` wrappers, the `Plugin` trait for
composable registration — these
are Bevy's ideas, and in many cases the implementation follows Bevy's
patterns closely (including the HRTB double-bound trick that makes
`IntoHandler` work). Credit where it's due: Bevy's system model is
an excellent piece of API design.

Where `nexus-rt` diverges is the target workload. Bevy is built for
simulation: many entities mutated per frame, parallel schedules,
component queries over archetypes. `nexus-rt` is built for event-driven
systems: singleton resources, sequential dispatch, and monotonic sequence
numbers instead of frame ticks. There are no entities, no components,
no archetypes — just a typed resource store where each event advances
a sequence counter and causality is tracked per-resource.

The result is a much smaller surface area tuned for low-latency event
processing rather than game-world state management.

## Architecture

```text
                        Build Time                          Dispatch Time
                   ┌──────────────────┐               ┌──────────────────────┐
                   │                  │               │                      │
                   │  WorldBuilder    │               │       World          │
                   │                  │               │                      │
                   │  ┌────────────┐  │    build()    │  ┌────────────────┐  │
                   │  │ Registry   │──┼──────────────►│  │ ResourceSlot[] │  │
                   │  │ TypeId→Idx │  │               │  │ ptr → value    │  │
                   │  └────────────┘  │               │  └───────┬────────┘  │
                   │                  │               │          │           │
                   │  install_plugin  │               │    get(id) ~3 cyc    │
                   │  install_driver  │               │          │           │
                   └──────────────────┘               └──────────┼───────────┘
                          │                                      │
                          │ returns Poller                       │
                          ▼                                      ▼
                   ┌──────────────────┐               ┌──────────────────────┐
                   │  Driver Poller   │               │  poll(&mut World)    │
                   │                  │               │                      │
                   │  Pre-resolved    │──────────────►│  1. next_sequence()  │
                   │  ResourceIds     │               │  2. get resources    │
                   │                  │               │  3. poll IO source   │
                   │  Owns pipeline   │               │  4. dispatch events  │
                   │  or handlers     │               │     via pipeline     │
                   └──────────────────┘               └──────────────────────┘
```

### Flow

1. **Build** — Register resources into `WorldBuilder`. Install plugins
   (fire-and-forget resource registration) and drivers (returns a poller).
2. **Freeze** — `builder.build()` produces an immutable `World`. All
   `ResourceId` values are direct pointers, valid for the lifetime of the World.
3. **Poll loop** — Your code calls `driver.poll(&mut world)` in a loop.
   Each driver owns its event lifecycle internally: poll IO, decode events,
   dispatch through its pipeline, mutate world state.
4. **Sequence** — Each event gets a monotonic sequence number via
   `world.next_sequence()`. **Drivers are responsible for calling this**
   before dispatching each event — the built-in timer and mio pollers
   do this automatically. `world.run()` does not advance the sequence;
   it is purely a shutdown-checked loop.

### Dispatch tiers

| Tier | Purpose | Overhead |
|------|---------|----------|
| **Pipeline** | Pre-resolved step chains inside drivers. The workhorse. | ~2 cycles p50 |
| **Callback** | Dynamic per-instance context + pre-resolved params. | ~2 cycles p50 |
| **Handler** | `Box<dyn Handler<E>>` for type-erased dispatch. | ~2 cycles p50 |
| **Template** | Pre-resolved handler stamping for re-registration. | ~1 cycle p50 (generate) |
| **DAG** | Monomorphized fan-out / merge data-flow graphs. | ~1-3 cycles p50 |
| **FanOut / Broadcast** | Static or dynamic fan-out by reference. | ~2 cycles p50 |
| **Reactor** | Interest-based per-instance dispatch with dedup. | ~19 cycles p50 (amortized) |

All tiers resolve `Param` state at build time. Dispatch-time cost is
a direct pointer deref — no hashing, no searching, no bounds check,
no Vec indirection.

See [BENCHMARKS.md](BENCHMARKS.md) for full criterion numbers.

## Driver Model

Drivers are event sources. The `Installer` trait handles installation;
the returned poller is a concrete type with its own `poll()` signature.

```rust
use nexus_rt::{Installer, WorldBuilder, World, ResourceId};

struct TimerInstaller { resolution_ms: u64 }
struct TimerPoller { timers_id: ResourceId }

impl Installer for TimerInstaller {
    type Poller = TimerPoller;

    fn install(self, world: &mut WorldBuilder) -> TimerPoller {
        world.register(Vec::<u64>::new());
        // ... register other resources ...
        let timers_id = world.registry().id::<Vec<u64>>();
        TimerPoller { timers_id }
    }
}

// Poller defines its own poll signature — NOT a trait method.
impl TimerPoller {
    fn poll(&mut self, world: &mut World, now_ms: u64) {
        // get resources via pre-resolved IDs, fire expired timers
    }
}
```

The executor is your `main()`:

```rust
let mut wb = WorldBuilder::new();
wb.install_plugin(TradingPlugin { /* config */ });
let timer = wb.install_driver(TimerInstaller { resolution_ms: 100 });
let io = wb.install_driver(IoInstaller::new());
let mut world = wb.build();

loop {
    let now = std::time::Instant::now();
    timer.poll(&mut world, now);
    io.poll(&mut world);
}
```

## Features

> **For Bevy users:** Many concepts map directly — `World` (singletons
> only, no entities/archetypes), `Res<T>`/`ResMut<T>` (same semantics),
> `SystemParam` → `Param`, `IntoSystem`/`System` → `IntoHandler`/`Handler`,
> `Plugin` (same pattern), `Local<T>` (same). The divergence is the
> execution model: sequential event dispatch instead of parallel
> frame-based schedules.

### World — typed singleton store

Type-erased resource storage with direct `ResourceId` pointers.
Dispatch-time access is a single pointer deref — zero framework overhead.
Frozen after build — no inserts, no removes.

### Res / ResMut — resource parameters

Declare resource dependencies in function signatures. `Res<T>` for shared
reads, `ResMut<T>` for exclusive writes. See
[Dependency Injection](#rest-and-resmutt--dependency-injection) above.

### Optional resources

`Option<Res<T>>` and `Option<ResMut<T>>` resolve to `None` if the type
was not registered, rather than panicking at build time. Useful for
handlers that can operate with or without a particular resource.

```rust
fn maybe_log(logger: Option<Res<Logger>>, event: u32) {
    if let Some(log) = logger {
        log.info(event);
    }
}
```

### Param — build-time / dispatch-time resolution

The `Param` trait is the mechanism behind `Res<T>`, `ResMut<T>`,
`Local<T>`, and all other handler parameters. Two-phase resolution:

1. **Build time** — `Param::init(registry)` resolves opaque state (e.g.
   a `ResourceId`) and panics if the required type isn't registered.
2. **Dispatch time** — `Param::fetch(world, state)` uses the cached state
   to produce a reference via a single pointer deref — zero framework
   overhead.

Built-in impls: `Res<T>`, `ResMut<T>`, `Option<Res<T>>`,
`Option<ResMut<T>>`, `Local<T>`, `RegistryRef`, `()`, and tuples up to
8 params.

**Access conflicts** are caught at build time. If two parameters in the
same handler would borrow the same resource (e.g. `Res<T>` + `ResMut<T>`,
or two `ResMut<T>` for the same `T`), `into_handler` / `.then()` panics
with `"conflicting access"`. Pipeline and DAG steps enforce the same check
per-step. This is a build-time guarantee — dispatch never hits a conflict.

### Handler / IntoHandler — fn-to-handler conversion

`IntoHandler` converts a plain `fn` into a `Handler` trait object.
Event `E` is always the last parameter; everything before it is resolved
as `Param` from a `Registry`. Named functions only — closures do not
work with `IntoHandler` due to Rust's HRTB inference limitations with
GATs. See [Handlers](#handlers--connecting-functions-to-the-world)
above.

### Pipeline — pre-resolved processing chains

Typed composition chains where each step is a named function with
`Param` dependencies resolved at build time.

```rust
let reg = world.registry();
let mut pipeline = PipelineBuilder::<Order>::new()
    .then(validate, &reg)            // Order → Result<Order, Error>
    .and_then(enrich, &reg)          // Order → Result<Order, Error>
    .catch(log_error, &reg)          // Error → () (side effect)
    .map(submit, &reg)              // Order → Receipt
    .build();                        // → Pipeline<Order, _> (concrete)

pipeline.run(&mut world, order);
```

Option and Result combinators (`.map()`, `.and_then()`, `.catch()`,
`.filter()`, `.unwrap_or()`, etc.) enable typed flow control without
runtime overhead. `.splat()` destructures a tuple output (2-5 elements)
into individual function arguments for the next step — see
[Splat](#splat--tuple-destructuring) below. `Pipeline` implements
`Handler<In>`, so it can be boxed or stored alongside other handlers.

### Batch pipeline — per-item processing over a buffer

`build_batch(capacity)` produces a `BatchPipeline` that owns a
pre-allocated input buffer. Each item flows through the same chain
independently — errors are handled per-item, not per-batch.

```rust
let reg = world.registry();
let mut batch = PipelineBuilder::<Order>::new()
    .then(validate, &reg)            // Order → Result<Order, Error>
    .catch(log_error, &reg)          // handle error, continue batch
    .map(enrich, &reg)              // runs for valid items only
    .then(submit, &reg)
    .build_batch(1024);

// Driver fills input buffer
batch.input_mut().extend_from_slice(&orders);
batch.run(&mut world);  // drains buffer, no allocation
```

No intermediate buffers between steps. The compiler monomorphizes
the per-item chain identically to the single-event pipeline.

### DAG Pipeline — fan-out, merge, and data-flow graphs

`DagBuilder` builds a monomorphized data-flow graph where topology is
encoded in the type system. After monomorphization the entire DAG is
a single flat function — all values are stack locals, no arena, no
vtable dispatch.

```rust
use nexus_rt::{WorldBuilder, ResMut, Handler};
use nexus_rt::dag::DagBuilder;

let mut wb = WorldBuilder::new();
wb.register::<u64>(0);
let mut world = wb.build();
let reg = world.registry();

fn decode(raw: u32) -> u64 { raw as u64 * 2 }
fn add_one(val: &u64) -> u64 { *val + 1 }
fn mul3(val: &u64) -> u64 { *val * 3 }
fn merge_add(a: &u64, b: &u64) -> u64 { *a + *b }
fn store(mut out: ResMut<u64>, val: &u64) { *out = *val; }

let mut dag = DagBuilder::<u32>::new()
    .root(decode, reg)
    .fork()
    .arm(|a| a.then(add_one, reg))
    .arm(|b| b.then(mul3, reg))
    .merge(merge_add, reg)
    .then(store, reg)
    .build();

dag.run(&mut world, 5u32);
// root: 10, arm_a: 11, arm_b: 30, merge: 41
assert_eq!(*world.resource::<u64>(), 41);
```

Fan-out arms borrow the fork output by reference — no `Clone` needed.
Option and Result combinators (`.map()`, `.and_then()`, `.catch()`,
etc.) work on both the main chain and within arms. `Dag` implements
`Handler<E>`, so it can be boxed or stored alongside other handlers.

For linear chains without fan-out, prefer
[Pipeline](#pipeline--pre-resolved-processing-chains).

#### DAG combinator quick reference

| Category | Combinator | Signature | Effect |
|----------|-----------|-----------|--------|
| **Topology** | `.root(fn, reg)` | `E → T` | Entry point — takes event by value |
| | `.then(fn, reg)` | `&T → U` | Chain step — input by reference |
| | `.fork()` | | Begin fan-out — arms observe `&T` |
| | `.arm(\|a\| a.then(...))` | | Build one arm of a fork |
| | `.merge(fn, reg)` | `&A, &B → T` | Combine arm outputs |
| | `.join()` | | Terminate fork without merge (all arms → `()`) |
| **Flow control** | `.guard(fn, reg)` | `&T → Option<T>` | Wrap in Option via predicate |
| | `.tap(fn, reg)` | `&T → &T` | Observe without consuming |
| | `.route(pred, reg, arm_t, arm_f)` | `&T → U` | Binary conditional routing |
| | `.tee(arm)` | `&T → &T` | Side-effect arm, chain continues |
| | `.scan(init, fn, reg)` | `&mut Acc, &T → U` | Stateful transform with accumulator |
| | `.dedup()` | `T → Option<T>` | Suppress consecutive duplicates |
| **Option\<T\>** | `.map(fn, reg)` | `&T → U` | Map inner value (Some only) |
| | `.filter(fn, reg)` | `&T → Option<T>` | Keep on true, None on false |
| | `.inspect(fn, reg)` | `&T → &T` | Observe Some values |
| | `.and_then(fn, reg)` | `&T → Option<U>` | Flat-map inner value |
| | `.on_none(fn, reg)` | | Side effect on None |
| | `.ok_or(fn, reg)` | `→ Result<T, E>` | Convert None to Err |
| | `.ok_or_else(fn, reg)` | `→ Result<T, E>` | Convert None to Err (produced) |
| | `.unwrap_or(default)` | `→ T` | Unwrap with fallback |
| | `.unwrap_or_else(fn, reg)` | `→ T` | Unwrap with produced fallback |
| **Result\<T, E\>** | `.map(fn, reg)` | `&T → U` | Map Ok value |
| | `.and_then(fn, reg)` | `&T → Result<U, E>` | Flat-map Ok value |
| | `.catch(fn, reg)` | `E → ()` | Handle Err, continue with Ok |
| | `.map_err(fn, reg)` | `E → E2` | Transform error type |
| | `.or_else(fn, reg)` | `E → Result<T, E2>` | Recover from error |
| | `.inspect(fn, reg)` | `&T → &T` | Observe Ok values |
| | `.inspect_err(fn, reg)` | `&E → &E` | Observe Err values |
| | `.ok()` | `→ Option<T>` | Discard Err |
| | `.unwrap_or(default)` | `→ T` | Unwrap with fallback |
| | `.unwrap_or_else(fn, reg)` | `→ T` | Unwrap Err with produced fallback |
| **Bool** | `.not()` | `bool → bool` | Logical NOT |
| | `.and(fn, reg)` | `bool → bool` | Short-circuit AND |
| | `.or(fn, reg)` | `bool → bool` | Short-circuit OR |
| | `.xor(fn, reg)` | `bool → bool` | Logical XOR |
| **Tuple** | `.splat()` | `&(A, B, ...) → (&A, &B, ...)` | Destructure tuple so next `.then()` sees `&A, &B, ...` args |
| **Terminal** | `.dispatch(handler)` | `&T → ()` | Hand off to a Handler |
| | `.cloned()` | `&T → T` | Clone reference to owned |
| | `.build()` | | Finalize into `Dag<E>` |

All combinators accepting functions resolve `Param` dependencies at build
time via `IntoStep`, `IntoRefStep`, or `IntoProducer` — named functions
get direct-pointer access. Arity-0 closures work everywhere. Raw
`&mut World` closures are available as an escape hatch via `Opaque`.

#### Splat — tuple destructuring

Pipeline and DAG steps follow a single-value-in, single-value-out convention.
When a step naturally produces multiple outputs (e.g. splitting an order into
an ID and a price), `.splat()` destructures the tuple so the next step
receives individual arguments instead of the whole tuple:

```rust
// Pipeline (by value): fn(Params..., A, B) -> Out
fn split(order: Order) -> (OrderId, f64) { (order.id, order.price) }
fn process(id: OrderId, price: f64) -> bool { price > 0.0 }

PipelineBuilder::<Order>::new()
    .then(split, reg)
    .splat()            // (OrderId, f64) → individual args
    .then(process, reg) // receives OrderId, f64 separately
    .build();

// DAG (by reference): fn(Params..., &A, &B) -> Out
fn process_ref(id: &OrderId, price: &f64) -> bool { *price > 0.0 }

DagBuilder::<Order>::new()
    .root(split, reg)
    .splat()                // (OrderId, f64) → &OrderId, &f64
    .then(process_ref, reg)
    .build();
```

Supported for tuples of 2-5 elements. Beyond 5 arguments, use a named struct
— if a combinator stage needs that many inputs, the data likely deserves its
own type.

### FanOut / Broadcast — handler-level fan-out

`FanOut` dispatches the same event by reference to a fixed set of
handlers. Zero allocation, concrete types, monomorphizes to direct
calls. Macro-generated for arities 2-8.

`Broadcast` is the dynamic variant — stores `Vec<Box<dyn RefHandler<E>>>`
for runtime-determined handler counts.

```rust
use nexus_rt::{WorldBuilder, ResMut, IntoHandler, Handler};
use nexus_rt::{fan_out, Broadcast, Cloned};

fn write_a(mut sink: ResMut<u64>, event: &u32) { *sink += *event as u64; }
fn write_b(mut sink: ResMut<i64>, event: &u32) { *sink += *event as i64; }

let mut builder = WorldBuilder::new();
builder.register::<u64>(0);
builder.register::<i64>(0);
let mut world = builder.build();

let h1 = write_a.into_handler(world.registry());
let h2 = write_b.into_handler(world.registry());
let mut fan = fan_out!(h1, h2);
fan.run(&mut world, 5u32);
assert_eq!(*world.resource::<u64>(), 5);
assert_eq!(*world.resource::<i64>(), 5);
```

Handlers inside combinators receive `&E`. Use `Cloned` or `Owned`
adapters for handlers that expect owned events.

For fan-out with merge (data flowing back together), use
[DagBuilder](#dag-pipeline--fan-out-merge-and-data-flow-graphs).

### Change detection

Per-resource change detection has been replaced by the **reactor system**
(behind the `reactors` feature). Event handlers call `ReactorNotify::mark(source)`
to signal which data changed. Subscribed reactors wake automatically with
dedup — per-instrument, per-strategy granularity.

```rust
// Setup: register data sources and spawn reactors
let btc_md = world.register_source();
world.spawn_reactor(
    |id| QuotingCtx { reactor_id: id, instrument: BTC },
    quoting_step,
).subscribe(btc_md);

// Event handler: mark which data changed
fn on_btc_tick(event: Tick, mut books: ResMut<OrderBooks>, mut notify: ResMut<ReactorNotify>) {
    books.apply(event);
    notify.mark(btc_md);  // O(1), wakes only BTC-subscribed reactors
}

// Post-frame: dispatch woken reactors (deduped)
world.dispatch_reactors();
```

### Local — per-handler state

`Local<T>` is state stored inside the handler instance, not in World.
Initialized with `Default::default()` at handler creation time. Each
handler instance gets its own independent copy — two handlers created
from the same function have separate `Local` values.

```rust
fn count_events(mut count: Local<u64>, mut total: ResMut<u64>, _event: u32) {
    *count += 1;
    *total = *count;
}

let mut handler_a = count_events.into_handler(registry);
let mut handler_b = count_events.into_handler(registry);

handler_a.run(&mut world, 0);  // handler_a local=1
handler_b.run(&mut world, 0);  // handler_b local=1 (independent)
handler_a.run(&mut world, 0);  // handler_a local=2
```

### Callback — context-owning handlers

`Callback<C, F, Params>` is a handler with per-instance owned context.
Use it when each handler instance needs private state that isn't shared
via World — per-timer metadata, per-connection codec state, protocol
state machines.

Convention: `fn handler(ctx: &mut C, params..., event: E)` — context
first, `Param`-resolved resources in the middle, event last.

```rust
struct TimerCtx { order_id: u64, fires: u64 }

fn on_timeout(ctx: &mut TimerCtx, mut counter: ResMut<u64>) {
    ctx.fires += 1;
    *counter += ctx.order_id;
}

let mut cb = no_event(on_timeout).into_callback(
    TimerCtx { order_id: 42, fires: 0 },
    registry,
);
cb.run(&mut world, ());

// Context is pub — accessible outside dispatch
assert_eq!(cb.ctx.fires, 1);
```

### HandlerTemplate / CallbackTemplate — resolve once, stamp many

When handlers are created repeatedly on the hot path — IO readiness
re-registration, timer rescheduling, connection accept loops — each
`into_handler(registry)` call pays for HashMap lookups to resolve the
same `ResourceId` values every time.

Templates resolve parameters once, then `generate()` stamps out
handlers by copying pre-resolved state — a flat memcpy vs ~20-70 cycles
of HashMap lookups for `into_handler`.

A [`Blueprint`] declares the event and parameter types. The template
resolves them against the registry once:

```rust
use nexus_rt::{WorldBuilder, ResMut, Handler};
use nexus_rt::template::{Blueprint, HandlerTemplate, CallbackTemplate, CallbackBlueprint};

struct OnTick;
impl Blueprint for OnTick {
    type Event = u32;
    type Params = (ResMut<'static, u64>,);
}

fn tick(mut counter: ResMut<u64>, event: u32) {
    *counter += event as u64;
}

let mut builder = WorldBuilder::new();
builder.register::<u64>(0);
let mut world = builder.build();

let template = HandlerTemplate::<OnTick>::new(tick, world.registry());

// Stamp out handlers — no HashMap lookups, just Copy.
let mut h1 = template.generate();
let mut h2 = template.generate();

h1.run(&mut world, 10);
h2.run(&mut world, 5);
assert_eq!(*world.resource::<u64>(), 15);
```

For context-owning handlers, `CallbackTemplate` works the same way —
each `generate(ctx)` takes an owned context value:

```rust
struct TimerCtx { order_id: u64 }

struct OnTimeout;
impl Blueprint for OnTimeout {
    type Event = ();
    type Params = (ResMut<'static, u64>,);
}
impl CallbackBlueprint for OnTimeout {
    type Context = TimerCtx;
}

fn on_timeout(ctx: &mut TimerCtx, mut counter: ResMut<u64>) {
    *counter += ctx.order_id;
}

let mut builder = WorldBuilder::new();
builder.register::<u64>(0);
let mut world = builder.build();

let cb_template = CallbackTemplate::<OnTimeout>::new(no_event(on_timeout), world.registry());
let mut cb = cb_template.generate(TimerCtx { order_id: 42 });
cb.run(&mut world, ());
assert_eq!(*world.resource::<u64>(), 42);
```

Convenience macros reduce Blueprint boilerplate:

```rust
use nexus_rt::handler_blueprint;
handler_blueprint!(OnTick, Event = u32, Params = (ResMut<'static, u64>,));
```

**Constraints:**
- `P::State: Copy` — excludes `Local<T>` with non-Copy state
  (incompatible with template stamping). All World-backed params
  (`Res`, `ResMut`, `Option` variants) have `State = ResourceId`
  which is `Copy`.
- Zero-sized callables only — named functions and captureless closures.
  Capturing closures and function pointers are rejected at compile time.

**Handler state sizes** (for capacity planning with inline storage):

`ResourceId` is pointer-sized (8 bytes on 64-bit). Each resource param
(`Res<T>`, `ResMut<T>`, `Option<Res<T>>`, `Option<ResMut<T>>`) stores
one `ResourceId` (8 bytes). Handler base overhead is 16 bytes (`&str`
name). Callbacks add the context size.

| Handler type | 0 params | 1 param | 2 params | 4 params | 8 params |
|-------------|----------|---------|----------|----------|----------|
| HandlerFn (no ctx) | 16 B | 24 B | 32 B | 48 B | 80 B |
| Callback (8 B ctx) | 24 B | 32 B | 40 B | 56 B | 88 B |

Formula: `16 + (8 × params) + context_size`. All fit comfortably
within 256-byte inline buffers (`FlatVirtual`, `InlineTimerWheel`).

### RegistryRef — runtime handler creation

`RegistryRef` is a `Param` that provides read-only access to the
`Registry` during handler dispatch. Enables handlers to create new
handlers at runtime via `IntoHandler::into_handler` or
`IntoCallback::into_callback`.

```rust
fn spawner(reg: RegistryRef) {
    let handler = some_fn.into_handler(&reg);
    // store handler somewhere...
}
```

### Installer — event source installation

`Installer` is the install-time trait for event sources. The installer
registers its resources into `WorldBuilder` and returns a concrete
poller whose `poll()` method drives the event lifecycle. See the
[Driver Model](#driver-model) section for the full pattern.

### Timer driver (feature: `timer`)

Integrates `nexus_timer::Wheel` as a driver. `TimerInstaller` registers
the wheel into `WorldBuilder` and returns a `TimerPoller`.

- `TimerPoller::poll(world, now)` drains expired timers and fires handlers
- Handlers reschedule themselves via `ResMut<TimerWheel<S>>`
- `Periodic` helper for recurring timers
- Inline storage variants behind `smartptr` feature: `InlineTimerWheel`,
  `FlexTimerWheel`

### Mio driver (feature: `mio`)

Integrates `mio` as an IO driver. `MioInstaller` registers the
`MioDriver` (wrapping `mio::Poll` + handler slab) and returns a
`MioPoller`.

- `MioPoller::poll(world, timeout)` polls for readiness and fires handlers
- Move-out-fire pattern: handler is removed from slab, fired, and must
  re-insert itself to receive more events
- Stale tokens (already removed) are silently skipped
- Inline storage variants behind `smartptr` feature: `InlineMio`, `FlexMio`

### Virtual / FlatVirtual / FlexVirtual — storage aliases

Type aliases for type-erased handler storage:

```rust
use nexus_rt::Virtual;

// Heap-allocated (default)
let handler: Virtual<Event> = Box::new(my_handler.into_handler(registry));

// Behind "smartptr" feature — inline storage via nexus-smartptr
// use nexus_rt::FlatVirtual;
// let handler: FlatVirtual<Event> = flat!(my_handler.into_handler(registry));
```

`Virtual<E>` for heap-allocated. `FlatVirtual<E>` for fixed inline
(panics if handler doesn't fit). `FlexVirtual<E>` for inline with
heap fallback.

### System / IntoSystem — reconciliation logic

Handlers react to individual events. But some computations need to run
*after* a batch of events has been processed — recomputing a theoretical
price after market data updates, checking risk limits after fills, etc.
These are reconciliation passes: they read the current state of the world,
decide if anything changed, and propagate downstream if so.

`System` is the dispatch trait for this. Distinct from `Handler<E>`,
systems take no event parameter and return `bool` to control downstream
propagation in a DAG scheduler.

| | Handler | System |
|---|---------|--------|
| Trigger | Per-event | Per-scheduler-pass |
| Event param | Yes (`E`) | No |
| Return | `()` | `bool` |
| Purpose | React | Reconcile |

`IntoSystem` accepts two signatures:
- `fn(params...) -> bool` — returns propagation decision for scheduler DAGs
- `fn(params...)` — void return, always propagates (`true`). Useful for
  `run_startup` and systems that unconditionally propagate.

```rust
// Bool-returning: controls DAG propagation
fn compute_theo(mid: Res<MidPrice>, mut theo: ResMut<TheoValue>) -> bool {
    let new_theo = mid.0 * 1.001;
    if (new_theo - theo.0).abs() > f64::EPSILON {
        theo.0 = new_theo;
        true  // outputs changed — run downstream
    } else {
        false // nothing changed — skip downstream
    }
}

// Void-returning: always propagates
fn initialize(mut cache: ResMut<PriceCache>) {
    cache.prices.extend_from_slice(&[100.0, 200.0]);
}
```

Convert via `IntoSystem` (same HRTB pattern as `IntoHandler`):

```rust
use nexus_rt::{IntoSystem, System};
let mut system = compute_theo.into_system(registry);
let changed = system.run(&mut world);
```

### Staged Scheduler — monomorphized system execution

`SchedulerBuilder` creates a staged chain of `System`s. Each `.then()` call
adds a stage. The first stage always runs. Subsequent stages run only if
at least one system in the previous stage returned `true` (OR semantics).

```rust
use nexus_rt::scheduler::SchedulerBuilder;

let mut scheduler = wb.install_driver(
    SchedulerBuilder::new()
        .root(compute_theo, &reg)
        .then(compute_quotes, &reg)
        .then(check_risk, &reg)
);
let mut world = wb.build();

// In event loop: run scheduler after event processing
let systems_run = scheduler.run(&mut world);
```

Stages can contain multiple systems via tuples (up to 8 per stage). All
systems in a stage run regardless of individual return values — the stage
result is the OR of all returns. The entire chain is monomorphized; no
vtable dispatch, no system limit. Systems return `bool` to control
downstream execution — `true` means "my outputs changed, run downstream."
For per-item change detection, use the reactor system.

### Reactor system (feature: `reactors`)

Interest-based per-instance dispatch with O(1) dedup. Replaces
per-resource change detection with explicit, fine-grained notification.

```rust
// Setup — auto-registered by WorldBuilder::build()
let btc_md = world.register_source();

world.spawn_reactor(
    |id| QuotingCtx { reactor_id: id, instrument: BTC, layer: 1 },
    quoting_step,
).subscribe(btc_md);

// Event handler marks data source
fn on_btc_tick(mut books: ResMut<OrderBooks>, mut notify: ResMut<ReactorNotify>, event: Tick) {
    books.apply(event);
    notify.mark(btc_md);  // wakes BTC-subscribed reactors only
}

// Post-frame dispatch (deduped — each reactor runs at most once)
world.dispatch_reactors();
```

- `ReactorNotify` — World resource: reactor storage, data source
  fan-out, registration. Event handlers mark via `ResMut`.
- `SourceRegistry` — maps domain keys (`InstrumentId`, `StrategyId`,
  tuples) to `DataSource` values for runtime lookup.
- `DeferredRemovals` — reactors self-remove by pushing their token.
  Cleanup runs after dispatch completes.
- `PipelineReactor` — reactor body is a `CtxPipeline` or `CtxDag`.
  Pipeline internals fully monomorphized; one `Box` per reactor.
- ~19 cycles per reactor (amortized at 50 reactors). See
  [BENCHMARKS.md](BENCHMARKS.md).

### Startup & Lifecycle

`Shutdown` is an interior-mutable flag automatically registered by
`WorldBuilder::build()`. Handlers trigger shutdown via `Res<Shutdown>`;
the event loop checks via `ShutdownHandle`:

```rust
use nexus_rt::{Res, WorldBuilder};
use nexus_rt::shutdown::Shutdown;

// Handler side
fn on_fatal(shutdown: Res<Shutdown>) {
    shutdown.shutdown();
}

// Event loop side
let mut world = WorldBuilder::new().build();
let shutdown = world.shutdown_handle();

while !shutdown.is_shutdown() {
    // poll drivers ...
    break; // (for example only)
}
```

With the `signals` feature, `ShutdownHandle::enable_signals()` registers
SIGINT/SIGTERM handlers (Linux only) that flip the shutdown flag
automatically.

### CatchAssertUnwindSafe — panic resilience

Wraps a handler to catch panics during `run()`, ensuring the handler is
never lost during move-out-fire dispatch (timer wheels, IO slabs). The
caller asserts that the handler and resources can tolerate partial writes.

```rust
use nexus_rt::{CatchAssertUnwindSafe, IntoHandler, Handler, Virtual};

let handler = tick.into_handler(registry);
let guarded = CatchAssertUnwindSafe::new(handler);
let mut boxed: Virtual<u32> = Box::new(guarded);
// Panics inside run() are caught — handler survives for re-dispatch
```

### Testing — TestHarness and TestTimerDriver

`TestHarness` provides isolated handler testing without wiring up drivers.
It owns a `World` and auto-advances the sequence counter before each dispatch.

```rust
use nexus_rt::testing::TestHarness;
use nexus_rt::{WorldBuilder, ResMut, IntoHandler};

fn accumulate(mut counter: ResMut<u64>, event: u64) {
    *counter += event;
}

let mut builder = WorldBuilder::new();
builder.register::<u64>(0);
let mut harness = TestHarness::new(builder);

let mut handler = accumulate.into_handler(harness.registry());
harness.dispatch(&mut handler, 10u64);
harness.dispatch(&mut handler, 5u64);

assert_eq!(*harness.world().resource::<u64>(), 15);
```

`TestTimerDriver` (feature: `timer`) wraps `TimerPoller` with virtual time
control — `advance(duration)`, `set_now(instant)`, `poll(world)` — for
deterministic timer testing without wall-clock waits.

### ByRef / Cloned / Owned — event-type adapters

Adapters bridge between owned and reference event types:

- `ByRef<H>` — wraps `Handler<&E>` to implement `Handler<E>` (borrow before dispatch)
- `Cloned<H>` — wraps `Handler<E>` to implement `Handler<&E>` (clone before dispatch)
- `Owned<H, E>` — wraps `Handler<E::Owned>` to implement `Handler<&E>` via `ToOwned`

Primary use: including owned-event handlers in reference-based contexts
(`FanOut`, `Broadcast`), or vice versa.

```rust
use nexus_rt::{Cloned, Owned, fan_out, IntoHandler, Handler};

// Handler expects owned u32
fn process(mut n: ResMut<u64>, event: u32) { *n += event as u64; }

// Adapt for &u32 context (FanOut dispatches by reference)
let h = process.into_handler(registry);
let adapted = Cloned(h);  // now implements Handler<&u32>

// For &str → String:
fn append(mut buf: ResMut<String>, event: String) { buf.push_str(&event); }
let h = append.into_handler(registry);
let adapted = Owned::<_, str>::new(h);  // implements Handler<&str>
```

`Adapt<F, H>` is a separate adapter for wire-format decoding: `F: FnMut(Wire) -> Option<T>`
filters and transforms before dispatching to `Handler<T>`.

## When to Use What

| Situation | Use | Why |
|-----------|-----|-----|
| One-time setup, test harness | `IntoHandler` / `IntoCallback` | Simple, direct. Construction cost paid once. |
| Pipeline steps inside a driver | `Pipeline` / `BatchPipeline` | Zero-cost monomorphized chains, typed flow control. |
| IO re-registration (accept, echo) | `HandlerTemplate` / `CallbackTemplate` | Handler recreated every event — template eliminates per-event HashMap lookups. |
| Timer rescheduling | `HandlerTemplate` / `CallbackTemplate` | Same pattern — recurring handlers should not pay construction cost repeatedly. |
| Type-erased handler storage | `Box<dyn Handler<E>>` / `Virtual<E>` | When you need heterogeneous collections (driver slabs, timer wheels). |
| Per-instance private state | `Callback` (via `IntoCallback`) or `CallbackTemplate` | Context-owning handlers for connection state, timer metadata, etc. |
| Composable resource registration | `Plugin` | Fire-and-forget, consumed by `WorldBuilder`. |
| Fan-out with merge | `DagBuilder` → `Dag` | Monomorphized data-flow graph. Zero vtable, all stack locals. |
| Static fan-out (known count) | `FanOut` / `fan_out!` | Dispatch `&E` to N handlers. Zero allocation, concrete types. |
| Dynamic fan-out (runtime count) | `Broadcast` | `Vec<Box<dyn RefHandler>>`. One heap alloc per handler, zero clones. |

**Rule of thumb:** If a handler is created once, use `IntoHandler`. If
it's created repeatedly on every event (move-out-fire pattern), use a
template. For data that must fan out and merge back, use `DagBuilder`.
For fire-and-forget fan-out, use `FanOut` (static) or `Broadcast`
(dynamic).

## Practical Guidance

### Boxing recommendation

Pipeline, DAG, and composed handler types are fully monomorphized — the
concrete types are deeply nested generics, often unnameable, and can be
very large. **Strongly recommend `Box<dyn Handler<E>>` (or `Virtual<E>`)
for storage.**

The cost is a single vtable dispatch at the handler boundary. All internal
dispatch within the handler/pipeline/DAG remains zero-cost monomorphized.
One vtable call amortized over many internal steps is the design:

```rust
// Concrete type is unnameable — box it
let handler: Box<dyn Handler<Order>> = Box::new(
    DagBuilder::<Order>::new()
        .root(decode, reg)
        .fork()
        .arm(|a| a.then(process, reg))
        .arm(|b| b.then(log, reg))
        .merge(combine, reg)
        .build()
);
```

### Named functions vs closures

Arity-0 closures work in Pipeline and DAG steps. Arity-1+ (with `Param`
arguments) requires named functions. This is a feature, not a limitation:

- Named functions are **testable** in isolation
- Named functions are **inspectable** (handler `.name()` returns the function path)
- Named functions are **reusable** across pipelines

For cases where you need `&mut World` access in a closure (e.g. dynamic
resource lookup), pass a `|world: &mut World, input| { ... }` closure —
it resolves via the `Opaque` marker with no `Param` overhead. The same
pattern works for `OpaqueHandler` (closures as `Handler<E>`).

Keep step functions small and focused — one function per transformation.

### Pipeline vs DAG

| | Pipeline | DAG |
|---|----------|-----|
| Topology | Linear chain | Fan-out / merge |
| Value flow | By value (move) | By reference within arms |
| Clone needed | No | No (shared `&T`) |
| Use when | Steps are sequential | Data needs to go to multiple places |

Both compose into `Handler<E>` via `.build()`. Use Pipeline for the common
case; reach for DAG when you need `.fork()`.

## Performance

All measurements in CPU cycles, pinned to a single core with turbo
boost disabled.

### Dispatch (hot path)

| Operation | p50 | p99 | p999 |
|-----------|-----|-----|------|
| Baseline hand-written fn | 2 | 3 | 4 |
| 3-stage pipeline (bare) | 2 | 2 | 4 |
| 3-stage pipeline (Res\<T\>) | 2 | 3 | 5 |
| Handler + Res\<T\> (read) | 2 | 4 | 5 |
| Handler + ResMut\<T\> (write) | 3 | 8 | 8 |
| Box\<dyn Handler\> | 2 | 9 | 9 |

Pipeline dispatch matches hand-written code — zero-cost abstraction
confirmed.

### Batch throughput

Total cycles for 100 items through the same pipeline chain.

| Operation | p50 | p99 | p999 |
|-----------|-----|-----|------|
| Batch bare (100 items) | 130 | 264 | 534 |
| Linear bare (100 calls) | 196 | 512 | 528 |
| Batch Res\<T\> (100 items) | 390 | 466 | 612 |
| Linear Res\<T\> (100 calls) | 406 | 550 | 720 |

Batch dispatch amortizes to ~1.3 cycles/item for compute-heavy chains
(~1.5x faster than individual calls).

### Construction (cold path)

| Operation | p50 | p99 | p999 |
|-----------|-----|-----|------|
| into_handler (1 param) | 21 | 30 | 79 |
| into_handler (4 params) | 45 | 86 | 147 |
| into_handler (8 params) | 93 | 156 | 221 |
| .then() (2 params) | 28 | 48 | 96 |

Construction cost is paid once at build time, never on the dispatch
hot path.

### Template generation (hot path handler creation)

| Operation | p50 | p99 | p999 |
|-----------|-----|-----|------|
| generate (1 param) | 1 | 1 | 2 |
| generate (2 params) | 1 | 1 | 2 |
| generate (4 params) | 1 | 1 | 1 |
| generate (8 params) | 1 | 1 | 1 |
| generate callback (2 params) | 1 | 2 | 2 |
| generate callback (4 params) | 1 | 1 | 1 |

`generate()` copies pre-resolved `ResourceId` values — a flat memcpy
at every arity. Compare with `into_handler` above: 24-70x faster for
handlers created on every event (IO re-registration, timer rescheduling).

### Running benchmarks

```bash
taskset -c 0 cargo run --release -p nexus-rt --example perf_pipeline
taskset -c 0 cargo run --release -p nexus-rt --example perf_construction
taskset -c 0 cargo run --release -p nexus-rt --example perf_template
taskset -c 0 cargo run --release -p nexus-rt --example perf_dag
taskset -c 0 cargo run --release -p nexus-rt --example perf_scheduler
taskset -c 0 cargo run --release -p nexus-rt --example mio_timer --features mio,timer
```

### DAG dispatch (hot path)

| Operation | p50 | p99 | p999 |
|-----------|-----|-----|------|
| DAG linear 3 stages | 1 | 2 | 3 |
| DAG linear 5 stages | 1 | 2 | 3 |
| DAG diamond fan=2 (5 stages) | 1 | 3 | 5 |
| DAG fan-out 2 (join) | 2 | 6 | 9 |
| DAG complex (fan+linear+merge) | 1 | 4 | 5 |
| DAG complex+Res\<T\> (Param fetch) | 3 | 3 | 5 |
| DAG linear 3 via Box\<dyn Handler\> | 1 | 4 | 4 |
| DAG diamond-2 via Box\<dyn Handler\> | 2 | 2 | 5 |

DAG dispatch matches Pipeline dispatch — topology adds no measurable
overhead. Boxing adds ~1 cycle at the boundary.

### Scheduler dispatch

| Operation | p50 | p99 | p999 |
|-----------|-----|-----|------|
| Flat 1 system | 11 | 20 | 48 |
| Flat 4 systems | 25 | 41 | 82 |
| Flat 8 systems | 43 | 67 | 124 |
| Chain 4 systems (all propagate) | 25 | 42 | 84 |
| Chain 8 systems (all propagate) | 44 | 73 | 124 |
| Diamond fan=4 (6 systems) | 35 | 53 | 93 |
| Skipped chain 8 (1 runs, 7 skip) | 17 | 28 | 68 |
| Skipped chain 32 (1 runs, 31 skip) | 46 | 76 | 118 |

Scheduler overhead is ~8-12 cycles per system. Skipped stages
(previous stage returned all `false`) short-circuit via a single
branch — no per-system cost for skipped stages.

## Limitations

### Named functions only

`IntoHandler`, `IntoCallback`, and `IntoStep` (arity 1+) require named
`fn` items — closures do not work due to Rust's HRTB inference limitations
with GATs. This is the same limitation as Bevy's system registration.

Arity-0 pipeline steps (no `Param`) do accept closures:
```rust
// Works — arity-0 closure
pipeline.then(|x: u32| x * 2, registry);

// Does NOT work — arity-1 closure with Param
// pipeline.then(|config: Res<Config>, x: u32| x, registry);

// Works — named function
fn transform(config: Res<Config>, x: u32) -> u32 { x + *config as u32 }
pipeline.then(transform, registry);
```

### Single-threaded

`World` is `!Sync` by design. All dispatch is single-threaded, sequential.
This is intentional — for latency-sensitive event processing, eliminating
coordination overhead matters more than parallelism.

### Frozen after build

No resources can be added or removed after `WorldBuilder::build()`. All
registration happens at build time. This enables stable pointers and
eliminates runtime bookkeeping.

## Examples

- [`mock_runtime`](examples/mock_runtime.rs) — Complete driver model:
  plugin registration, driver installation, explicit poll loop
- [`pipeline`](examples/pipeline.rs) — Pipeline composition: bare value,
  Option, Result with catch, combinators, build into Handler
- [`dag`](examples/dag.rs) — DAG pipeline: linear, diamond, fan-out,
  route, tap, tee, dedup, guard, boxing
- [`scheduler_dag`](examples/scheduler_dag.rs) — DAG scheduler:
  reconciliation systems, boolean propagation, change detection
- [`handlers`](examples/handlers.rs) — Handler composition: IntoHandler,
  Callback, boxing, FanOut, Broadcast, adapters
- [`templates`](examples/templates.rs) — Template generation:
  HandlerTemplate, CallbackTemplate, handler_blueprint macro
- [`testing_example`](examples/testing_example.rs) — TestHarness usage
  for isolated handler unit testing
- [`local_state`](examples/local_state.rs) — Per-handler state with
  `Local<T>`, independent across handler instances
- [`optional_resources`](examples/optional_resources.rs) — Optional
  dependencies with `Option<Res<T>>` / `Option<ResMut<T>>`
- [`perf_pipeline`](examples/perf_pipeline.rs) — Dispatch latency
  benchmarks with codegen inspection probes
- [`perf_dag`](examples/perf_dag.rs) — DAG dispatch latency benchmarks
  across topologies
- [`perf_scheduler`](examples/perf_scheduler.rs) — Scheduler dispatch
  latency benchmarks
- [`perf_construction`](examples/perf_construction.rs) — Construction-time
  latency benchmarks at various arities
- [`perf_template`](examples/perf_template.rs) — Template generation
  vs `into_handler` construction benchmarks
- [`perf_fetch`](examples/perf_fetch.rs) — Fetch dispatch strategy
  benchmarks
- [`mio_timer`](examples/mio_timer.rs) — Echo server combining mio
  and timer drivers with template construction benchmarks

## License

See workspace root for license details.
