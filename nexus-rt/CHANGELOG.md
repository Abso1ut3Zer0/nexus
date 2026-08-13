# Changelog

All notable changes to nexus-rt are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

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
