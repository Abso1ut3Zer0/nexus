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
holds callbacks which themselves read that slot, e.g. a timer-wheel-like
`struct Pending(Option<TemplatedCallback<K>>)` used by the
[self-rescheduling pattern](callbacks.md#self-rescheduling-callbacks-periodic-timers-retries).
The referenced type is finite (a callback holds a fn pointer and pre-resolved
state, never the slot), so `#[derive(Resource)]` works on it. (The derive no
longer emits an explicit `Send` bound, which previously overflowed auto-trait
resolution on exactly this shape.)

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
