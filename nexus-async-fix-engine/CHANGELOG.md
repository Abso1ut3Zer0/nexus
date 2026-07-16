# Changelog

All notable changes to nexus-async-fix-engine are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Internal

- Test scratch directories are now removed on drop. The `tmp_dir` helpers in
  `tests/async_conformance.rs`, `tests/journal_outbound_admin.rs`, and
  `tests/frame_too_large.rs` return an RAII `TempDir` guard instead of a bare
  `PathBuf`. Each test opens a `FixJournal`, which preallocates ~25M, and the
  directories were never removed — a full run leaked into `$TMPDIR`, and the
  PID in each name meant every run minted a fresh set rather than reusing the
  last. The guard's `Drop` also runs while unwinding, so a *failing* test now
  cleans up too. Mirrors the existing guard in
  `nexus-journal/src/rotating/tests.rs`.

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

- `AsyncFixConnection<S>` renamed to `FixConnection<S, D>` (now generic over the
  `FixDictionary` `D`) and rewritten as a thin tokio wrapper over the shared
  sans-IO `FixSession<D>` core (the thin-adapter half of #544). The hand-rolled
  inbound frame parsing, admin encoding, resend loop, and UNIX-nanos timestamp
  code are deleted — all of that now lives in `FixSession`; the wrapper does only
  the `.await`ed socket I/O.
- `recv` is no longer callback-based. It is now
  `recv(now) -> Result<Option<Message<'_, D>>, Error>`, returning the next typed
  `Message` borrowed from the session buffer (was
  `recv(on_app: &mut impl FnMut(&[u8])) -> Result<Option<DisconnectReason>, Error>`).
  Outbound admin, journaling, and resend that the old `recv` drove by hand are
  now handled inside the core.
