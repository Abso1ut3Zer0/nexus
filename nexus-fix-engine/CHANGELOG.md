# Changelog

All notable changes to nexus-fix-engine are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Changed

- **Repositioned as a sans-IO FIX session _framework_** (mechanism, not policy):
  the caller owns the loop, the timers, and every protocol decision. This is a
  large, breaking reshaping of the session API.
  - **Three-object trio.** `FixSession` (the state-machine brain) plus caller-held
    `MessageReader` / `MessageWriter`, with the transport passed per call — the
    session no longer owns the socket, so reconnect is "same session, new socket"
    (sequence numbers and the journal survive). The caller holds a `FixParts` trio.
  - **Deterministic clock.** The internal `SystemTime::now()` reads are gone; every
    `SendingTime(52)` stamps from a caller-supplied `now: i128` (UTC unix-nanos)
    passed to `recv` and the send helpers, making the core a pure function of
    `(bytes, now)` — fully replayable for testing and historical replay.
  - **No timers.** The `Instant`-based timer state, `on_timeout` / `next_timeout`,
    and every auto-emit (auto-Heartbeat answering a TestRequest, auto-Logon reply,
    auto-ResendRequest on a gap, auto-driven resend) are removed. The session
    exposes only `heartbeat_interval()`; you build the heartbeat, two-phase
    peer-liveness, and handshake timers yourself. Worked, runnable blocking and
    tokio recipes ship as `examples/timer_recipes.rs`.
  - **User-driven replies.** `recv(.., now)` returns a `Message` whose every variant
    names its one required response, which you send with a helper. `LogonRequest`
    splits from `LogonResetRequest`, and gap detection surfaces as `GapDetected`
    rather than the engine silently emitting a ResendRequest. Each protocol action
    has an encode-only form (custom / kernel-bypass transport) and a combined
    (encode + flush) form.
  - **Resend cursor.** An inbound ResendRequest surfaces a user-pumped
    `ResendCursor` (drop = refuse) instead of driving the whole replay inside
    `recv` with blocking writes; a request outside the journal's retained window
    surfaces `ResendOutOfRange` (no cursor) to answer with `sequence_reset` /
    `gap_fill` or a logout.

### Added

- **Socket-setup batteries**, in the primary/secondary split `nexus-web` uses for
  WebSocket (`WsStreamBuilder` → raw parts, `WsStream` → owns-everything).
  - **Primary — `FixConnectionBuilder` → raw parts.** `connect(addr, state, config,
    journal)` opens the socket and returns the raw `(FixParts, TcpStream)`; `accept(
    stream, …)` pairs a preexisting stream. You run the ordinary three-object loop,
    so admin replies stay **zero-copy** (`recv`'s `Message` borrows only `reader`).
    Reconnect is "keep the `FixParts`, grab a new socket" via
    `connect_socket(addr)` — no re-bundling; the sequence numbers and journal live in
    the retained parts. Builder config: `reader_capacity` / `writer_capacity` /
    `customizer` / `disable_nagle` / `read_timeout`.
  - **Secondary — `FixConnection` owns everything.** Bundles the trio *and* the
    socket into one object with `recv` + delegating send helpers (`connect` (Logon) /
    `heartbeat` / `logout` / `send_app` / …), for callers who want a single value to
    pass around. Build it one-step with `FixConnection::open(addr, …)`, or from B's
    parts with `from_parts(parts, socket)`; `into_parts()` returns `(FixParts, S)`.
    Because it owns everything, `recv` borrows the whole connection, so an admin
    reply field (a `TestReqID`) is copied out before the reply — which is exactly why
    the raw parts are primary. `parts_mut()` is the escape hatch for a raw verb the
    bundle does not wrap (e.g. pumping a `ResendCursor`).

- `Text(58)` reason on Logout and Reject. `logout` / `encode_logout`,
  `LogonDecision::reject` / `encode_reject`, and `FixSession::encode_reject_logon`
  take `reason: Option<&AsciiTextStr>`, encoded as `Text(58)` when `Some` and
  omitted when `None`. The codec `Logout` / `Reject` encode structs gain the
  optional printable-ASCII field (SOH-safe by construction), and `58` joins their
  `*_OWNED` customizer tripwire lists.

- `FixSession` now implements `nexus_net::ParserSink` (forwarding to
  `read_spare`/`read_filled`), so a `WireStream` can fill the session's inbound
  buffer copy-free via `poll_fill_into` — the seam the async client's transport
  now uses (see nexus-async-fix-engine).

- Venue Logon auth. `FixSession`, `FixConnection`, and `MessageWriter` take a
  per-venue `SessionCustomizer` (from `nexus-fix-codec`) as a trailing type
  parameter defaulting to `NoCustomizer`, so existing plain-FIX call sites —
  `FixConnection<TcpStream, Fix44>`, `MessageWriter::new()`,
  `FixSession::from_buffers(...)` — compile and behave exactly as before, and
  produce byte-identical frames.

  Attach one with `FixConnectionBuilder::customizer(c)`, or the
  `*_with_customizer` constructors (`FixSession::new_with_customizer`,
  `FixConnection::from_parts_with_customizer`,
  `MessageWriter::with_customizer`, `MessageWriter::with_frame_writer_and_customizer`).

  `MessageWriter::encode_admin` now owns the frame lifecycle so the hook runs
  where it must: after the session header (`8`/`35`/`34`/`49`/`56`/`52`) is
  stamped — so a venue can sign over it — and before `finish()` computes
  `BodyLength(9)`/`CheckSum(10)` — so injected fields are covered by both.

  `MessageWriter::encode_admin` now returns `Result<(), Error>` (previously it
  returned nothing). A hook that overflows the writer — an oversized
  `RawData(96)` or a too-small buffer — poisons the frame, and the encode now
  surfaces `Error::MessageTooLarge` instead of silently committing nothing.
  Without this, the outbound seqnum had already been bumped and the state moved
  on, so the session wedged until a logon/heartbeat timeout reported a cause
  that pointed away from the encode. `store_admin` and the missing-tag-35 reject
  path both propagate the error; nothing is committed or journaled on failure.

  Note: `store_admin` journals the encoded frame, so hook-injected fields
  (including a plaintext `Password(554)`) land in the outbound journal. This is
  deliberate: the journal is local to the box, and an archive that matches the
  wire byte-for-byte is worth more than redaction. QuickFIX/J has the same
  property (it persists after `toAdmin`).

  Resend gap-fills are unaffected — they are reframed directly and never run the
  hook, so PossDup traffic cannot carry credentials.

- Malformed inbound frames now surface as a recoverable `TransportError::Malformed`
  instead of being silently counted and dropped. `recv()` (sync and async) returns
  `Err(Malformed { skipped, count, reason })` — `skipped` bytes discarded to resync
  to the next `8=`, `count` the running total this session, and `reason` a new
  `MalformedReason` (`Framing` / `BodyLength` / `Checksum`) saying how the frame
  broke. It sits in the error channel because receiving the frame *failed*, but it
  is the one **recoverable** error: the reader has resynced, the inbound seqnum is
  unchanged (FIX's optimistic recovery), and the session is intact —
  `TransportError::is_fatal()` returns `false` for it (and `true` for every other
  variant). The caller owns the policy: `recv()?` to tear down on the first bad
  byte, or match `Malformed` and keep receiving, disconnecting only on a sustained
  flood. `garbage_frame_count()` remains as the cumulative accessor. (#583)

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

- Session end is split by outcome. A clean, negotiated logout surfaces as
  `Message::LoggedOut { msg }` (`Ok`, carrying the peer's Logout 35=5 so the caller
  can read `Text(58)`); an abnormal disconnect surfaces as
  `Err(TransportError::UnexpectedDisconnect { reason })`, never a message. The old
  `Message::Disconnected { reason }` is removed. So `recv()?` now propagates a fault
  disconnect toward reconnect/alert logic, while a graceful shutdown is a distinct
  terminal event on the `Ok` side.
  - `DisconnectReason` drops `Logout` (now represented by `Message::LoggedOut`) and
    adds `PeerClosed` — a socket EOF with no FIX Logout, previously misreported as a
    clean `Logout`. It is now purely the fault set.
  - `TransportError` gains `UnexpectedDisconnect { reason }` and `Closed`. Calling
    `recv()` after any terminal outcome returns `Closed` (mirrors tungstenite's
    `AlreadyClosed`), tracked per connection. Both are fatal (`is_fatal()` is `true`;
    only `Malformed` is recoverable). (#612)

- `FrameError::Garbage { skipped }` is renamed to
  `FrameError::Malformed { skipped, reason }`, carrying a `MalformedReason`. The
  old name implied random bytes, but the reader also reports a bad
  `BodyLength(9)` or a failed `CheckSum(10)` — neither is garbage. (#583)

- Outbound admin dispatch is now typed structs through a trait, replacing the
  `AdminMsg` enum and its `MessageWriter::encode_admin` match (both introduced
  earlier this cycle). Each admin message — `Logon`, `LogonReset`, `Logout`,
  `Heartbeat`, `TestRequest`, `ResendRequest`, `SequenceReset`, `Reject` — is now
  a struct in `nexus-fix-codec` implementing the new `AdminEncode` trait (a pure
  naming bridge to `FixDictionary::encode_*` / `SessionCustomizer::customize_*` /
  `FixDictionary::*_OWNED`). `SessionState` handlers take a `sink: &mut S`
  (`S: AdminSink`) — one generic `emit<M: AdminEncode>(msg)` method — instead of
  an `emit: &mut F` closure, and return `Result<Control, S::Error>` (reset
  initiators require `S::Error: From<SessionError>`). The concrete admin type is
  never erased into a sum and matched back apart, so cross-message mis-wiring is
  unrepresentable. The driver's production `AdminSink` is the new
  `Emitter<'a, D, C, J>`, which owns the encode-and-commit path (session-header
  stamp → dictionary encode → `SessionCustomizer` hook → `finish`) and runs an
  injected `after(seq, frame)` closure — the journaling policy the driver picks
  per emit context (journal for most admin, a no-op for the encode-only
  missing-tag-35 reject). `MessageWriter::encode_admin` and the driver's
  `store_admin` are gone, folded into `Emitter`. Wire output is byte-identical;
  the byte-identity oracles and the FIX/async conformance suites pass unchanged.
  `Heartbeat`'s `echo` field borrows the `TestReqID` (`Option<&[u8]>`), so it is
  echoed verbatim with no length cap.
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
