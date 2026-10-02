# Changelog

All notable changes to nexus-slab are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

## [2.4.0] — 2026-10-02

### Added

- `PinnedSlot<T>` and `byte::PinnedSlot<T>`: a sound pinned slot handle.
  `Slot::into_pinned` consumes the movable handle; the pinned handle hands
  out `Pin<&T>` / `Pin<&mut T>` and nothing that could move the value (no
  `DerefMut`, no `BorrowMut`, no `take`). `Slab::free_pinned` on all four
  slab types drops it in place, and must run before the slab is dropped:
  a pinned value left occupied at slab drop loses its storage without its
  destructor running (`Pin`'s drop guarantee). The `Box::into_pin` analogue
  for slab storage ([#751](https://github.com/Abso1ut3Zer0/nexus/issues/751)).
- Debug builds panic when a slab is dropped while any slot is still occupied
  (the freelist is walked on drop; corrupt freelists are reported as a double
  free or a cross-slab free). Release builds are unchanged. `Slab<T>` now has
  a `Drop` impl in every profile, so the drop checker requires `T` to outlive
  the slab.
- `rc::unbounded::Slab` reaches parity with `unbounded::Slab`: `Builder`
  (`chunk_capacity`, `initial_chunks`, `unsafe build`, `Default`),
  `capacity`, `chunk_capacity`, `chunk_count`, `reserve_chunks`,
  `contains_ptr`. `rc::bounded::Slab` gains `contains_ptr`. `take` stays
  absent by design (unsound while other handles are live) and the struct
  docs now say so; `claim` is parked. Parity tests guard against the drift
  recurring ([#702](https://github.com/Abso1ut3Zer0/nexus/issues/702)).
- `unbounded::Builder` and `byte::unbounded::Builder` are now `Clone`.
- `bounded::Slab`, `unbounded::Slab`, `byte::bounded::Slab` and
  `byte::unbounded::Slab` are now `Send` (`T: Send` for the typed slabs) and
  stay `!Sync`. Handles (`Slot`, `PinnedSlot`, claims) stay `!Send`, so a slab
  moves between threads whole and nothing can race on its freelist; a handle
  left behind can only touch its own slot. The `rc` slabs and `RcSlot` stay
  `!Send` (non-atomic refcount) and now carry a marker and `compile_fail`
  assertions saying so. Removes the `unsafe impl Send` boilerplate on
  slab-backed resources in single-threaded runtimes
  ([#724](https://github.com/Abso1ut3Zer0/nexus/issues/724)).

### Removed

- `Slot::pin` / `pin_mut`, `byte::Slot::pin` / `pin_mut` and `RcSlot::pin` /
  `pin_mut`, deprecated in 2.3.5 as unsound
  ([#750](https://github.com/Abso1ut3Zer0/nexus/issues/750)). Use
  `PinnedSlot` for `!Unpin` values and `Pin::new` for `Unpin` ones. `RcSlot`
  gets no pinned form: pinned-ness would be a whole-slot property across
  clones and has no caller. Shipped in a minor per this crate's stated
  policy on narrowly scoped breaks with contained blast radius; no workspace
  crate called these methods.

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
