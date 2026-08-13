# Changelog

All notable changes to nexus-notify are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

## [1.1.0] — 2026-08-13

### Added

- `Events::drain()`, a cursor-based draining iterator that removes
  tokens as they're consumed. Unlike `Vec::drain`, stopping early
  leaves the untaken remainder in the buffer instead of discarding it.

### Breaking

- **`Poller::poll_limit` / `LocalNotify::poll_limit` now `debug_assert!`
  the previous batch was fully drained before clearing and refilling.**
  Code that polled again without draining (or explicitly clearing) the
  prior `Events` batch — previously legal, silently discarding the
  leftover tokens — now panics in debug/test builds. Release builds
  are unaffected (`debug_assertions` off).

### Migration notes

Most consumers are unaffected — `cargo update -p nexus-notify` is
sufficient for any poll loop that already fully consumes `Events` each
cycle. If a debug/test build starts panicking with "poll_limit called
with undrained tokens still in the buffer," drain (`events.drain()`)
or clear (`events.clear()`) the buffer before the next
`poll`/`poll_limit` call.

## [1.0.2] and earlier

Earlier history is not documented in this CHANGELOG. See git history
and GitHub release notes for details.
