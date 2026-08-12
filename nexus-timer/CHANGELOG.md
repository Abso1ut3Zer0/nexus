# Changelog

All notable changes to nexus-timer are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- `TimeoutList<T, S>` — a fixed-duration timeout list front-end over the same
  slab / entry / handle machinery as the wheel. The timeout is fixed at
  construction (no per-call `deadline` parameter), so deadlines are monotone in
  insertion order: entries append at the tail of one intrusive DLL and poll
  walks from the head, giving **O(fired)** poll and **O(1)** exact
  `next_deadline()` (the head is the min — no cache). Same
  `schedule` / `schedule_forget` / `try_schedule` / `try_schedule_forget` /
  `cancel` / `free` / `poll` / `poll_with_limit` surface as the wheel. No
  `reschedule` (cancel and re-schedule instead). Builder mirrors
  `WheelBuilder`: `TimeoutListBuilder::new(timeout).tick_duration(..)
  .unbounded(chunk)|.bounded(cap).build(now)`. Exports: `TimeoutList`,
  `BoundedTimeoutList`, `TimeoutListBuilder`, `UnboundedTimeoutListBuilder`,
  `BoundedTimeoutListBuilder`. Nothing-due poll is flat across live population
  (~12 cycles/op, amortized, at 100 / 1k / 10k / 50k), versus the wheel's
  O(population) 0.2 µs → 2.4 ms.

- Timer wheel poll fast path — a cached global-minimum early-exit plus a
  per-slot minimum deadline. A nothing-due poll returns after a single compare
  instead of walking every active level, and the global minimum is recomputed
  from ~one compare per populated slot rather than one per entry.

### Changed

- `TimerWheel::next_deadline()` now returns a **lower bound** rather than the
  exact next deadline. Per-slot minima are left stale-low after a cancel or fire
  (not recomputed on removal), so the result may be earlier than the true next
  deadline, never later — safe as a sleep/wake bound (wake early, never miss).

## [1.4.2] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
