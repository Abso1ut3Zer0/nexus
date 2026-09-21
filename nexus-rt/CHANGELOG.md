# Changelog

All notable changes to nexus-rt are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- **Runtime keyed dispatch — `#[derive(Dispatchable)]` + `.dispatch_variant` /
  `.dispatch_on` / `.dispatch_map`.** Flat-array dispatch tables indexed by a
  dense variant ordinal, complementing the compile-time `select!` for when arms
  are chosen at runtime from a value — and now the recommended default (see
  `docs/dispatch.md`), since the cost over `select!` is a few cycles at p50.
  `#[derive(Dispatchable)]` gives an enum a dense `ordinal()` (`0..VARIANTS`,
  declaration order — normalizing sparse/explicit discriminants, and defined for
  data-carrying variants where `as usize` is not) plus, per variant, a
  zero-sized `VariantOf` marker (in a generated `<enum_snake_case>_variants`
  module) tying the variant to its payload type, its ordinal, and an
  `unwrap_unchecked`. `Dispatchable` and `VariantOf` are `unsafe` traits (the
  derive is the safe, supported way to implement them; a hand `unsafe impl`
  takes on the ordinal/payload correspondence obligation). A pair of
  `Dispatchable` enums is itself `Dispatchable` (row-major
  tuple-product key, no hashing). Three pipeline combinators consume it:
  - `.dispatch_variant` (on `Pipeline` + `CtxPipeline`) — keyed dispatch on the
    input enum's own discriminant; each arm receives its variant's **typed
    payload** (`()`, the field type, or a tuple of field types). The payload
    unwrap is the feature's only `unsafe` — sound because the arm is reached only
    via the value's own `ordinal()` — and is debug-asserted.
  - `.dispatch_on` (on `Pipeline` / `CtxPipeline` / `DagChain` / `CtxDagChain`)
    — keyed dispatch on a **projected** key (`Fn(&V) -> K` for any
    `Dispatchable` K); the projection carries no variant guarantee, so every arm
    receives the **whole value** (no unchecked unwrap). DAG arms borrow `&V`,
    and `.dispatch_on` is available inside a fork arm (`DagArm` / `CtxDagArm`),
    not just on the chain.
  - `.dispatch_map` (on `Pipeline` + `CtxPipeline`) — keyed dispatch on an
    arbitrary `Hash + Eq` (non-enum) key via an `FxHashMap`, for keys that aren't
    `Dispatchable`. Whole-value arms; the open key space **always** requires a
    `.default`.

  All forms are **`Out`-generic**: if the arms return a value it bubbles up as
  the dispatch's output so the pipeline can `.then(...)` after it; if they return
  `()` the dispatch is terminal. Each table must be **exhaustive or carry a
  `.default`** (which receives the whole value/enum) — enforced by a
  **construction-time panic** (deterministic, before any dispatch), the runtime
  analog of `select!` requiring a `_`; arming the same key twice is likewise a
  construction-time panic (a duplicate arm is a wiring bug, the analog of
  `select!`'s `unreachable_patterns`). `.default_noop()` is sugar for "ignore
  unset keys" on terminal (`Out = ()`) tables. An arm can itself be a **pre-built
  pipeline** (a terminal `Pipeline`/`CtxPipeline` is a resolved step — see the
  next entry). `CtxPipeline`/`CtxDag` arms thread `&mut C`. Every form exists as
  both a pipeline entry point and a continuation node. Benchmarks in
  `examples/perf_dispatch.rs` / `BENCHMARKS.md`. See issue \#723.
- **A built pipeline can be a `select!` arm / `.then()` step / dispatch arm
  directly.** A built
  `CtxPipeline` now implements `IntoCtxStep` (and a built plain `Pipeline` now
  implements `StepCall` + `IntoStep`), so a terminal (`Out = ()`) sub-pipeline
  can be used as a `select!` arm or a nested `.then()` step **without** a
  hand-written `Opaque` wrapper closure (`|ctx, w, m| pipe.run(ctx, w, m)`). This
  is a passthrough — a built pipeline is already a resolved step — with no
  coherence conflict (pipelines don't implement `FnMut`) and no `select!` codegen
  change. See the "Terminal fork" sections in `docs/callbacks.md` and
  `docs/pipelines.md`. The `Opaque`-closure arm form remains for arms that need
  raw `&mut World`.

### Fixed

- **The static conflict check now sees resources nested inside
  `#[derive(Param)]` bundles and tuples.** `Registry::check_access` previously
  only inspected top-level params, so a conflicting borrow hidden in a bundle
  (or a nested tuple) — the very escape hatch used to exceed the 8-param arity
  ceiling — silently bypassed the always-on aliasing guard; only the
  debug-only runtime borrow tracker could catch it, and only on dispatch. Access
  reporting is now recursive, so bundle-vs-top-level, two-bundle, bundle-in-bundle,
  and tuple-in-bundle conflicts are all caught at handler construction time. The
  hot path (`Param::fetch`) is unchanged — this is build-time only.

### Changed

- **`Param` gains a defaulted `collect_access` method** (the recursive access
  collector behind the fix above). The default reports the param's own
  `resource_id`, so all leaf impls (`Res`, `ResMut`, `Local`, …) and any existing
  hand-written impls keep working unchanged; the tuple impl and `#[derive(Param)]`
  override it to forward each child. `resource_id` is retained as the per-leaf
  building block. `Registry::check_access` now takes `&[(ResourceId, &str)]`
  instead of `&[(Option<ResourceId>, &str)]` (the collector never yields empty
  entries). Both are extension-point / low-level surfaces; the derive and
  built-ins are unaffected.

## [2.5.1] — 2026-08-13

## [2.5.0] — 2026-08-13

### Added

- **Ignore the event without naming it.** A handler or callback that doesn't use
  the event can omit the trailing `_: Event` parameter and say so at the build
  site instead:
  - Raw handlers: `f.into_handler_event_ignored(reg)` (trait
    `IntoHandlerIgnoringEvent`) produces a `Handler<E>` that drops the event —
    for **any** `E`, including borrowed / non-`'static` wire events (the handler
    stores no `E`, so there's no `'static` bound).
  - Templates: `HandlerTemplate::new_event_ignored(f, reg)` and
    `CallbackTemplate::new_event_ignored(f, reg)`.

  Common for timers (ignore the `Instant`) and event-triggered handlers that only
  read resources. The event is still dispatched and then dropped — zero runtime
  cost, identical to writing `_: Event`. These are the preferred form. `no_event`
  / `NoEvent` remain — the `E = ()` shorthand on the raw path, and the
  template-dispatch mechanism `new_event_ignored` builds on (its `NoEvent<F>`
  template impls now cover any blueprint `Event`, not just `()`).
- **Self-referential blueprints — `CallbackTemplate` is now `Copy` / `Clone`.**
  A callback can carry its own template in its context and stamp its own successor
  (a periodic re-arm, a retry timer, any "produce the next me" pattern) through the
  safe API — no `&mut World` reach-in, no unsafe borrow split. The impls are
  hand-written (not derived) so the `K` blueprint marker needn't be `Copy`/`Clone`;
  the copy is `State` (already `Copy`), a fn pointer, and a `&'static str`.
  Paired with a `nexus-rt-derive` fix so `#[derive(Resource)]` works on the
  self-referential slot type this pattern uses
  (`struct Pending(Option<TemplatedCallback<K>>)`), which previously overflowed
  auto-trait resolution.
- **`WorldBuilder::try_register`** — a non-dropping fallible register. Returns
  `Err(value)` (the value handed back, not dropped) when the type is already
  registered, so a plugin can detect that another plugin registered a different
  configuration of the same type. `ensure` now delegates to it. The
  duplicate-registration panic in `register` also gained a hint pointing at
  `ensure()` / `try_register()` / `contains::<T>()`.
- **`WorldBuilder::id` / `try_id`** — resolve the `ResourceId` of a type
  registered so far, for a driver/plugin that requires a dependency another one
  provides (`id` panics at setup if absent; `try_id` returns `None`). Mirrors the
  `id`/`try_id` already on `World` and `Registry` — `WorldBuilder` previously had
  only `contains`.
- **Clock pollers return the time they compute.** `RealtimeClockPoller`,
  `TestClockPoller`, and `HistoricalClockPoller` `sync()` now return the `Clock`
  they wrote (`Copy`), so event-loop code holding a poller can stamp/log the
  timestamp without a second `world.resource::<Clock>()` lookup. Source-compatible
  for the common case — the return is not `#[must_use]`, so statement-position
  `poller.sync(...)` calls compile unchanged — but it is a return-type signature
  change: code that named the old `-> ()` shape (a `fn` pointer, or a closure bound
  to `FnMut(&mut World)`) would need updating.

### Changed

- **Clock installers register `Clock` with `ensure_default` instead of
  `register`.** A `Clock` is a shared read dependency, not installer-owned state,
  so a clock source now composes with anything that already registered a `Clock`
  (e.g. a baseline default) instead of panicking on install order. The three
  installers drive the value of whichever `Clock` slot exists. The owned-vs-shared
  registration pattern behind this is now documented on the `Installer` trait
  (own → `register`, share → `ensure`/`ensure_default`, require → resolve via
  `id`, which panics at setup if absent — a missing dependency is a wiring error,
  not a `Result`), cross-referenced from `register`, `Resource`, and `Plugin`.

## [2.4.1] — 2026-06-02

### Added

- `SeqMut::reset()` — reset the sequence counter to 0 and return `Sequence::ZERO`.
- `World::reset_sequence()` — reset the world's current sequence to 0.

## [2.4.0] — 2026-05-17

Eventless handlers and monomorphized scheduler.

### Added

- **`NoEvent<F>` wrapper + `no_event()` function.** Handlers with
  `E = ()` no longer need a trailing `_: ()` parameter. Arity-0
  functions work automatically; for 1+ params, wrap with
  `no_event(tick)` to disambiguate from the event-taking impls.
  Same coherence trick as `CtxFree` — `NoEvent<F>` never satisfies
  `FnMut`, so impls are provably disjoint.
- **Diagnostic hint** on `IntoHandler` for `no_event()` usage.

### Changed

- **Monomorphized scheduler.** `SchedulerBuilder` replaces
  `SchedulerInstaller`. The schedule is a nested
  `StageNode<Prev, S>` type chain — fully inlined by the compiler,
  no vtable dispatch, no bitmask, no 64-system limit.
  Builder API: `.root(sys, &reg).then(sys, &reg)`.
- **nexus-timer dependency** tightened from `>=1.2` to `>=1.4`
  (picks up reciprocal precision and deadline cache improvements).

### Removed

- `SchedulerInstaller`, `SystemId`, `MAX_SYSTEMS` — replaced by
  `SchedulerBuilder`.

### Notes on breakage

- The scheduler API is fully replaced. `SchedulerInstaller::new()` +
  `.add()` + `.after()` becomes `SchedulerBuilder::new().root().then()`.
  Blast radius is narrow — scheduler is internal infrastructure, not
  a user-facing hot path.

## [2.3.0] — 2026-05-08

Ergonomics around `Res<T>` and `ResMut<T>`. Lets handler bodies pass
the wrappers themselves (not just `&T` / `&mut T`) into inner functions
without moving.

### Added

- **`Res<T>: Copy + Clone`**, regardless of `T`. Manual impls (not
  derived) so the bounds depend only on the inner `&T` field, which is
  always `Copy`. A derive would have erroneously required `T: Clone`.
  This means user code can now pass `Res<T>` to inner functions
  multiple times without `.clone()` ceremony.
- **`ResMut::reborrow(&mut self) -> ResMut<'_, T>`**. The exclusive-
  borrow counterpart to `Res<T>: Copy`. Pass `ResMut<T>` to inner
  functions without moving — the original is frozen for the duration
  of the reborrow, then usable again. Analogous to `&mut *x` reborrow
  for `&mut T`.

### Notes on breakage

- This release is a **minor bump** even though existing user code that
  shadowed an outer `Res<T>` with a different value via something like
  `let res = res.clone();` will now silently `Copy` instead. Behavior
  is the same in practice, but the inferred `Clone` bound on user
  generics may shift. Watch for diagnostic regressions, not runtime
  ones.

## [2.2.0] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
