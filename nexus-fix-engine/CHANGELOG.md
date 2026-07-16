# Changelog

All notable changes to nexus-fix-engine are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Internal

- Test scratch directories are now removed on drop. The `tmp_dir` helpers in
  `tests/transport.rs`, `tests/fix_conformance.rs`, `src/fix_session.rs`, and
  `src/persist.rs` return an RAII `TempDir` guard instead of a bare `PathBuf`.
  Each test opens a `FixJournal`, which preallocates ~25M, and the directories
  were never removed — a full run leaked hundreds of megabytes into `$TMPDIR`,
  and the PID in each name meant every run minted a fresh set rather than
  reusing the last. The guard's `Drop` also runs while unwinding, so a
  *failing* test now cleans up too; the manual `cleanup(&dir)` calls it
  replaces did not. Mirrors the existing guard in
  `nexus-journal/src/rotating/tests.rs`.

### Changed

- `SessionState` handler API reworked: the `Out` and `Event` types are
  removed. Each handler (`on_logon`, `on_app`, `on_timeout`, …) now takes an
  `emit: &mut F` closure (`F: FnMut(AdminMsg) -> Result<(), E>`) for outbound
  admin messages and returns the owned `Control` verdict instead of an `Out`
  bundling admin messages plus an `Event`. `Control` (re-exported from the
  crate root, replacing `Event`) is the single owned enum the state machine
  returns; the driver reconstructs the borrowed `Message` from it. Reset
  initiators (`connect_reset`, `reset_sequence`) require `E: From<SessionError>`
  for the wrong-state guard; a new `From<SessionError>` impl on the session-core
  `Error` covers production callers.
- Out-of-sequence and duplicate admin messages are now **suppressed** rather than
  surfaced. On a sequence gap the handler emits a `ResendRequest` and returns
  `Control::None`; a `PossDup` duplicate below the expected seqnum is ignored
  (no resend, no disconnect, not surfaced). This makes `on_heartbeat`,
  `on_test_request`, `on_reject`, `on_logout`, and GapFill-mode
  `on_sequence_reset` consistent with `on_app`/`on_resend_request`: only
  in-sequence, first-time messages reach the application via `message()`.
  Proceed-only work (the TestRequest Heartbeat echo, the GapFill `next_inbound`
  advance, the Logout exchange) no longer runs on a gap or duplicate.
- `FixConnection<S, D>` is now a thin socket wrapper over a new sans-IO
  `FixSession<D>` core (the thin-adapter half of #544). All protocol logic —
  frame decode, the `SessionState` machine, journaling, encode, and resend —
  lives in `FixSession`; the connection does only the blocking socket I/O.
  Resend is resumable: `FixSession::poll` surfaces `PollOutcome::ResendPending`
  so a partial retransmission resumes across reads instead of restarting. The
  public `FixConnection` API is unchanged.
- `FixJournal` reworked from an outbound-only resend log into a **two-journal**
  (outbound + inbound) both-sides archive that serves resend *and* visibility.
  Direction is implicit in which journal a frame lands in — no per-frame
  direction flag. Each stored payload is prefixed with an 8-byte LE UNIX-nanos
  timestamp (`[ts:8][wire msg]`); resend strips the prefix before replay.
- Sequence-number recovery is now O(1) from a per-journal manifest meta-slot
  (`next_outbound` in the outbound manifest, `next_inbound` in the inbound
  manifest), replacing the O(n) tag-34 recovery scan and the `NI=` inbound
  sentinel messages. Counters now survive even when the messages that carried
  them age out of the hot window.
- On recovery, the resend ring is rebuilt by scanning the bounded outbound hot
  window, restoring cross-restart resend (previously a restart replayed
  gap-fills for everything).

### Added

- `FixJournal::open_in`: primary constructor that opens the two per-session
  journals through a shared `&mut Conductor` (folds in the shared-conductor
  work). The convenience `open` / `open_existing` constructors own a
  private archive-enabled conductor for single-session callers (harness, tests).
  Conductor-outlives-journals is a documented drop-order invariant.
- `FixJournal::store_inbound`: archive an inbound frame for visibility/audit.
- `Error::Journal(WriteError)`: journal write-path failures now surface through
  the transport error type; `WriteError` is re-exported for callers matching on it.

### Removed

- `Message::LogoutAcknowledged`, and the `acknowledged` field on
  `Control::Logout` (now a unit variant). A completed logout exchange
  disconnects and surfaces as `Message::Disconnected { reason: Logout }`, so
  the acknowledging variant was unreachable: the only path that ever produced a
  `Logout` *message* was the out-of-sequence one, which was itself a bug (see
  the suppression fix above). `Message::LogoutRequest` remains, reachable when
  a Logout arrives out-of-state (e.g. mid-reset).

### Fixed

- `SessionState::on_reject_inbound` did not clear `test_request_sent`, unlike
  the eight other inbound handlers. A counterparty that answered a TestRequest
  probe with a frame the engine could not dispatch (e.g. missing `MsgType(35)`)
  left the probe armed, so the next timeout dropped a live session with
  `TestRequestTimeout` despite the inbound message proving liveness.
