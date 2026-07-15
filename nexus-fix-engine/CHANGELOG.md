# Changelog

All notable changes to nexus-fix-engine are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed

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
