# Derive Macros

nexus-rt provides derive macros for common patterns: marking types as
resources, grouping handler parameters, and newtype delegation.

## `#[derive(Resource)]`

Every type stored in the World must implement the `Resource` trait
(`Send + 'static`). The derive macro generates this impl for you.

```rust
use nexus_rt::Resource;

#[derive(Resource)]
struct OrderBook {
    bids: Vec<Level>,
    asks: Vec<Level>,
}

#[derive(Resource, Default)]
struct RiskState {
    exposure: f64,
}
```

Without `#[derive(Resource)]`, calling `wb.register(value)` produces a
compile error with a diagnostic hint:

```
error: this type cannot be stored as a resource in the World
note: add `#[derive(Resource)]` to your type, or use `new_resource!` for a newtype wrapper
```

Use `#[derive(Resource)]` on any struct you pass to
`WorldBuilder::register()`.

A genuinely non-`Send` type (e.g. one holding an `Rc`) is still rejected — the
error points at the derived struct and names the offending field, via the
`Resource: Send + 'static` supertrait.

### Self-referential resource types

Some resources are legitimately self-referential — most commonly a slot that
holds callbacks which themselves read that slot. For a concrete callback
blueprint `Heartbeat`, that slot is
`struct Pending(Option<TemplatedCallback<Heartbeat>>)`, as used by the
[self-rescheduling pattern](callbacks.md#self-rescheduling-callbacks-periodic-timers-retries).
The referenced type is finite (a callback holds a fn pointer and pre-resolved
state, never the slot), so `#[derive(Resource)]` works on it. (For a concrete
type the derive no longer emits an explicit `Send` bound, which previously
overflowed auto-trait resolution on exactly this shape.)

## `new_resource!`

Shorthand for a newtype wrapper that implements `Resource`, `Deref`,
`DerefMut`, and `From<Inner>`:

```rust
use nexus_rt::new_resource;

new_resource!(
    /// Trade counter.
    #[derive(Debug, Default)]
    pub TradeCount(u64)
);

let mut c = TradeCount::from(0u64);
*c += 1;
assert_eq!(*c, 1);
```

Use this when the inner type is a primitive or a standard library type.
The World requires one resource per type, so wrapping `u64` in a named
newtype avoids collisions.

## `#[derive(Param)]`

Groups multiple handler parameters into a single struct. The struct must
have exactly one lifetime parameter (`'w`).

```rust
use nexus_rt::{Param, Res, ResMut, Resource};

#[derive(Resource, Default)]
struct OrderBook { best_bid: f64, best_ask: f64 }

#[derive(Resource, Default)]
struct RiskState { exposure: f64 }

#[derive(Resource, Default)]
struct Config { max_exposure: f64 }

#[derive(Param)]
struct TradingParams<'w> {
    book: Res<'w, OrderBook>,
    risk: ResMut<'w, RiskState>,
    config: Res<'w, Config>,
}

fn on_trade(mut params: TradingParams<'_>, event: TradeEvent) {
    let spread = params.book.best_ask - params.book.best_bid;
    params.risk.exposure += spread;
    if params.risk.exposure > params.config.max_exposure {
        // reject
    }
}
```

### `#[param(ignore)]`

Fields marked `#[param(ignore)]` are excluded from parameter resolution.
They must implement `Default` and are initialized to their default value.

```rust
#[derive(Param)]
struct MyParams<'w> {
    book: Res<'w, OrderBook>,
    #[param(ignore)]
    scratch: Vec<u8>,  // Default::default(), not resolved from World
}
```

### Limitations

`#[derive(Param)]` does not support type or const generics. Only the
required `'w` lifetime is allowed:

```rust
// Does NOT compile
#[derive(Param)]
struct Bad<'w, T> {  // type generic not supported
    val: Res<'w, T>,
}
```

## `#[derive(Deref)]` / `#[derive(DerefMut)]`

Delegate `Deref` and `DerefMut` to an inner field. For tuple structs,
delegates to field `.0`. For named structs with multiple fields, mark
the target with `#[deref]`.

```rust
use nexus_rt::{Deref, DerefMut};

// Tuple struct — delegates to .0
#[derive(Deref, DerefMut)]
struct Wrapper(Vec<u8>);

// Named struct — #[deref] selects the field
#[derive(Deref, DerefMut)]
struct Named {
    #[deref]
    data: Vec<u8>,
    label: String,
}
```

Use alongside `#[derive(Resource)]` for newtype resources that should
expose the inner type's API:

```rust
use nexus_rt::{Resource, Deref, DerefMut};

#[derive(Resource, Deref, DerefMut)]
struct PriceCache(Vec<f64>);
```

This is equivalent to what `new_resource!` generates, but gives you
control over additional derives and visibility.

## `#[derive(Dispatchable)]`

Turns an enum into a dense ordinal space (`0..VARIANTS`) for runtime keyed
dispatch — the substrate the `.dispatch_variant` / `.dispatch_on` combinators
build a flat-array dispatch table on. It is also a useful `enum-map`-style
primitive on its own.

```rust
use nexus_rt::{Dispatchable, VariantOf};

#[derive(Dispatchable)]
enum Cmd {
    RouteAway(u32), // ordinal 0
    Reprice(u32, i64), // ordinal 1
    Halt, // ordinal 2
}

assert_eq!(Cmd::VARIANTS, 3);
assert_eq!(Cmd::RouteAway(7).ordinal(), 0);
```

The derive emits:

- `impl Dispatchable` — `const VARIANTS` and `ordinal(&self) -> usize`, a dense
  index in declaration order. Dense on purpose: it normalizes sparse/explicit
  discriminants and is defined for data-carrying variants (where `as usize` is
  not).
- A module `<enum_snake_case>_variants` (here `cmd_variants`) of zero-sized
  per-variant marker types, each implementing `VariantOf<Cmd>` — exposing the
  variant's `Payload` type, its `ORDINAL`, and an `unwrap_unchecked`. These are
  what you pass to `.dispatch_variant`'s `.arm(...)`.

A pair of `Dispatchable` enums is itself `Dispatchable` (`(A, B)`, a row-major
tuple-product key — no hashing). Only unit and tuple variants are supported;
named-field struct variants and generic enums (including lifetime-generic, so no
borrowed/zero-copy enums) are rejected by the derive.

`Dispatchable` and `VariantOf` are **`unsafe` traits**: the payload unwrap skips
the discriminant check and relies on `ordinal()` and `ORDINAL` being consistent.
`#[derive(Dispatchable)]` is the supported, safe way to implement them and cannot
get the correspondence wrong; a hand-written `unsafe impl` takes on that
obligation (see
[UNSAFE_AND_SOUNDNESS.md](UNSAFE_AND_SOUNDNESS.md#7-dispatch-payload-unwrap-dispatchrs--2-unsafe-blocks)).

Two derive errors worth knowing:

- **A payload that names `Self`** (e.g. `Node(Box<Self>)`) resolves against the
  generated marker impl and produces a confusing type error. Name the concrete
  enum in the field type instead of `Self`.
- **An enum that implements `Drop`** with a non-`Copy` payload fails to compile
  with `E0509` ("cannot move out of a type which implements `Drop`"): the
  generated `unwrap_unchecked` moves the payload out. Do not implement `Drop` on
  a `Dispatchable` enum.

See [dispatch.md](dispatch.md) for the full cookbook — the combinators, the
payload-vs-whole-value distinction, and the soundness argument for the unwrap.
