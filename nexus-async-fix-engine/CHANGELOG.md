# Changelog

All notable changes to nexus-async-fix-engine are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- Inbound message journaling: well-framed, comp-id-valid inbound frames are
  archived to the session's inbound journal for visibility/audit, mirroring the
  sync engine.
- Outbound admin journaling: outbound admin frames (Logon, Heartbeat, Logout,
  TestRequest, ResendRequest, SequenceReset, Reject) are now journaled to the
  outbound journal, mirroring the sync engine's `store_admin`. Previously async
  sessions journaled inbound + app but dropped their own admin, leaving the
  both-sides archive incomplete.
- `Error::Journal(WriteError)`: journal write-path failures now surface through
  the connection error type. Both journaling sites use the existing transient
  backpressure pattern (retry on `StandbyNotReady` via `tokio::task::yield_now`).

### Changed

- `AsyncFixConnection::encode_admin` returns `Result<(), Error>` (was `()`) so
  outbound-admin journal writes can propagate; `flush_out` forwards the error.
