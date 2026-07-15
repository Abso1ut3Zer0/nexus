# Changelog

All notable changes to nexus-journal are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- `RotatingJournal::meta` / `set_meta`: an opaque `u64` manifest meta-slot,
  written in place and recovered on reopen (mirrors `epoch`/`set_epoch`). The
  journal never interprets it; callers use it as a durable checkpoint (e.g. a
  FIX sequence number).
- `RotatingJournal::log_offset_at`: reconstruct a ring-usable `LogOffset` from a
  frame's global offset (as returned by `Frame::offset()` during a `read_next`
  scan), using the current `slot_gen`. Frames outside the readable window fail
  the gen-check on `read()` and yield `None`.
- `RotatingJournal::append_prefixed`: write a prefix and body contiguously into
  one frame in a single copy. `append` is now `append_prefixed(&[], body)`.
