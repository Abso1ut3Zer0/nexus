# Changelog

All notable changes to nexus-slab are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

<<<<<<< HEAD
- `rc::unbounded::Slab` reaches parity with `unbounded::Slab`: `Builder`
  (`chunk_capacity`, `initial_chunks`, `unsafe build`, `Default`),
  `capacity`, `chunk_capacity`, `chunk_count`, `reserve_chunks`,
  `contains_ptr`. `rc::bounded::Slab` gains `contains_ptr`. `take` stays
  absent by design (unsound while other handles are live) and the struct
  docs now say so; `claim` is parked. Parity tests guard against the drift
  recurring ([#702](https://github.com/Abso1ut3Zer0/nexus/issues/702)).
- `unbounded::Builder` and `byte::unbounded::Builder` are now `Clone`.
=======
- `PinnedSlot<T>` and `byte::PinnedSlot<T>`: a sound pinned slot handle.
  `Slot::into_pinned` consumes the movable handle; the pinned handle hands
  out `Pin<&T>` / `Pin<&mut T>` and nothing that could move the value (no
  `DerefMut`, no `BorrowMut`, no `take`). `Slab::free_pinned` on all four
  slab types drops it in place. The `Box::into_pin` analogue for slab
  storage ([#751](https://github.com/Abso1ut3Zer0/nexus/issues/751)).

### Removed

- `Slot::pin` / `pin_mut`, `byte::Slot::pin` / `pin_mut` and `RcSlot::pin` /
  `pin_mut`, deprecated in 2.3.5 as unsound
  ([#750](https://github.com/Abso1ut3Zer0/nexus/issues/750)). Use
  `PinnedSlot` for `!Unpin` values and `Pin::new` for `Unpin` ones. `RcSlot`
  gets no pinned form: pinned-ness would be a whole-slot property across
  clones and has no caller. Shipped in a minor per this crate's stated
  policy on narrowly scoped breaks with contained blast radius; no workspace
  crate called these methods.
>>>>>>> ebd3c8b2 (establishing new pin api patterns for slab crate)

## [2.3.5] — 2026-10-01

### Deprecated

- `Slot::pin` / `pin_mut`, `byte::Slot::pin` / `pin_mut` and `RcSlot::pin` /
  `pin_mut` are unsound for `!Unpin` types and will be removed in 2.4.0. They
  build a `Pin` from a handle that also offers safe `take()` and `DerefMut`
  (or `borrow_mut()` for `RcSlot`), so safe code can move a pinned value out
  from under the `Pin`. Signatures are unchanged in this release; callers get
  a deprecation warning. For `T: Unpin` use `Pin::new`. A sound pinned handle
  that consumes the `Slot` ships in 2.4.0
  ([#750](https://github.com/Abso1ut3Zer0/nexus/issues/750),
  [#751](https://github.com/Abso1ut3Zer0/nexus/issues/751)).

### Fixed

- Docs: the slab safety contracts now state that a `Slot` must not outlive
  its slab (dropping the slab frees the storage; a dangling `Slot` derefs
  through safe code) and no longer claim cross-slab misuse is the only
  remaining hazard. `SlotCell` docs no longer call `Slot` an RAII handle.

## [2.3.4] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
