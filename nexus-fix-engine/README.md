# nexus-fix-engine

A sans-IO FIX session **framework** built on
[`nexus-fix-codec`](../nexus-fix-codec). Mechanism, not policy: we frame,
checksum, sequence, journal, and track protocol state; you own the loop, the
timers, and every decision.

## The three-object trio

The caller holds a `FixParts` trio and passes the buffers plus a transport per
call — the session never owns the socket, so reconnect is "same session, new
socket" (sequence numbers and the journal survive):

- **`FixSession`** — the sans-IO brain: state machine + journal + encode. Owns
  every protocol verb, no buffers, no socket.
- **`MessageReader`** — the inbound buffer and reassembled frame.
- **`MessageWriter`** — the outbound buffer and per-venue customizer.

```
Disconnected -> LogonSent -> Active <-> Resending -> LogoutPending -> Disconnected
```

## Receive: one variant, one required response

`recv` fills `reader`, advances the state machine, and returns a `Message`
borrowing `reader` only — so `&mut session` / `&mut writer` stay free to send the
reply while the borrowed payload is still alive.

```rust
let FixParts { mut session, mut reader, mut writer } =
    FixSession::<Fix44>::builder().build(state, config, journal);

session.connect(&mut writer, &mut stream, now)?;   // initiator; acceptors feed the inbound Logon

loop {
    match session.recv(&mut reader, &mut writer, &mut stream, now)? {
        Some(Message::TestRequest { id }) =>
            session.heartbeat(&mut writer, &mut stream, now, Some(id))?,
        Some(Message::GapDetected { begin }) =>
            session.resend_request(&mut writer, &mut stream, now, begin)?,
        Some(Message::LogonRequest(d) | Message::LogonResetRequest(d)) =>
            d.accept(&mut session, &mut writer, &mut stream, now)?,   // or d.reject(.., reason)
        Some(Message::LogoutRequest { .. }) =>
            session.logout(&mut writer, &mut stream, now, None)?,     // reason: Option<&AsciiTextStr> → Text(58)
        Some(Message::ResendRequest { cursor }) => {
            let mut c = cursor;                                       // pump it, or drop = refuse
            while let Some(bytes) = c.next(&mut session, &mut writer, now)? {
                stream.write_all(bytes)?;                             // pace / bound / abort is yours
            }
        }
        Some(Message::Application { header }) => { /* your business logic */ }
        Some(_) | None => {}
        // an abnormal end surfaces as Err(TransportError::UnexpectedDisconnect { .. })
    }
}
```

Every variant's docs state its single obligation. Application messages surface as
`Message::Application`; outbound app messages take their `MsgSeqNum` from
`allocate_seq`.

## Send helpers — two forms each

Each protocol action has an **encode-only** form (`encode_heartbeat`,
`encode_logout`, …) that fills `writer` for a custom / kernel-bypass transport
(drain via `writer.data()`), and a **combined** form (`heartbeat`, `logout`, …)
that encodes and flushes through the transport in one call. `logout` and
`LogonDecision::reject` take `reason: Option<&AsciiTextStr>`, encoded as `Text(58)`
when `Some`.

## Deterministic clock

The core reads no clock of its own. Every `SendingTime(52)` stamps from a
caller-supplied `now: i128` (UTC unix-nanos) passed to `recv` and the send
helpers, so the core is a pure function of `(bytes, now)` — replayable for testing
and historical replay. `now` is the wall clock; it has nothing to do with timers.

## Timers are yours

The session holds **no timers** — it exposes only `heartbeat_interval()`. You own
three: a heartbeat ticker, a **two-phase** peer-liveness probe (reset on *any*
inbound message; probe, then disconnect), and a handshake/logout deadline. Forget
the liveness probe and a dead peer sits unnoticed — so the worked, runnable
recipes are a first-class deliverable: see
[`examples/timer_recipes.rs`](examples/timer_recipes.rs) (blocking) and its tokio
twin in [`nexus-async-fix-engine`](../nexus-async-fix-engine).

## Resend

An inbound ResendRequest whose range is within the journal's retained window
surfaces a `ResendCursor` you pump one write at a time (dropping it refuses the
resend). A request outside the window surfaces `ResendOutOfRange` — no cursor, you
answer with `sequence_reset` / `gap_fill` or log out. Replay comes from
`FixJournal`, a both-sides (outbound + inbound) archive.

## Async

The tokio twin, [`nexus-async-fix-engine`](../nexus-async-fix-engine), is a
newtype that `Deref`s to this core: the whole sans-IO seam is available unchanged,
and it adds a `recv` that `.await`s I/O over any `WireStream`.
