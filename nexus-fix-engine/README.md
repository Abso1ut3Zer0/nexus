# nexus-fix-engine

Sans-IO FIX session layer built on [`nexus-fix-codec`](../nexus-fix-codec).

## Session

`Session` is a pure state machine. The caller owns the transport, the
clock, and the encode buffer; the session never allocates after
construction.

```
Disconnected -> LogonSent -> Active <-> Resending -> LogoutPending -> Disconnected
```

```rust
let mut session = Session::new(SessionConfig {
    begin_string: b"FIX.4.4",
    sender_comp_id: b"US",
    target_comp_id: b"THEM",
    heart_bt_int: Duration::from_secs(30),
});

session.connect(now);                       // initiator; acceptors just feed the inbound Logon
while let Some(n) = session.encode_pending(&mut buf, now, unix_nanos) {
    socket.write_all(&buf[..n])?;           // flush queued admin messages
}
session.handle_message(framed_msg, now);    // one framed message from the wire
while let Some(event) = session.poll_event() {
    match event {
        Event::App { seq_num, .. } => { /* decode from framed_msg */ }
        Event::Disconnected { reason } => { /* tear down */ }
        _ => {}
    }
}
session.handle_timeout(now);                // drive at session.next_timeout()
```

Admin messages (Logon, Logout, Heartbeat, TestRequest, ResendRequest,
SequenceReset, Reject) are handled internally. Application messages
surface as `Event::App`; the caller decodes them from its own buffer,
e.g. with `nexus-fix-codegen` decoders. Outbound application messages
take their MsgSeqNum from `allocate_seq`.

Timers are delegated: the session stores deadlines and exposes them via
`next_timeout()`; the caller wires that into its timer wheel and calls
`handle_timeout(now)`. No inbound traffic for 1.2x the heartbeat
interval sends a TestRequest; no answer within another interval
disconnects.

Inbound ResendRequests are answered with a gap-fill SequenceReset and
surfaced as `Event::ResendRange`; store-backed retransmission replays
the original messages from `FixJournal`, a two-journal (outbound +
inbound) both-sides archive. TCP framing and checksum validation
happen before `handle_message` (#410).
