# Changelog

All notable changes to nexus-rt are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- **`WorldBuilder::try_register`** — a non-dropping fallible register. Returns
  `Err(value)` (the value handed back, not dropped) when the type is already
  registered, so a plugin can detect that another plugin registered a different
  configuration of the same type. `ensure` now delegates to it. The
  duplicate-registration panic in `register` also gained a hint pointing at
  `ensure()` / `try_register()` / `contains::<T>()`.
- **Clock pollers return the time they compute.** `RealtimeClockPoller`,
  `TestClockPoller`, and `HistoricalClockPoller` `sync()` now return the `Clock`
  they wrote (`Copy`), so event-loop code holding a poller can stamp/log the
  timestamp without a second `world.resource::<Clock>()` lookup. Non-breaking —
  the return is not `#[must_use]`, so callers that ignore it keep compiling.

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
