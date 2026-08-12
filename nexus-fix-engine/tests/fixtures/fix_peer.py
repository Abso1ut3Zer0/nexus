"""FIX 4.4 conformance peer. Accepts one connection, runs one scenario, exits.

The engine under test is always the INITIATOR (it sends the opening Logon); this
peer is the acceptor counterparty. One process handles exactly one connection, so
`recv_msg` keeps leftover bytes in a module-global buffer — pipelined frames (a
resend burst written in one TCP segment) are parsed one at a time, never dropped.

Scenario shutdown discipline (the engine never closes the socket itself — the
Rust side drops the connection only after `child.wait()`): a scenario ends
either by reading the engine's own Logout (`35=5`) and returning, or by simply
returning so the `finally` closes the socket and the engine sees EOF. Never
block waiting for the engine to close first — that deadlocks against
`child.wait()`.
"""

import socket
import sys

SENDER = "PEER"
TARGET = "ENGINE"
TS = "20260101-00:00:00.000"

# The engine runs the deterministic core with a FIXED caller clock
# (`now = 1_780_505_733_000_000_000` unix-nanos), so every `SendingTime(52)` it
# stamps is exactly this value. Scenarios that read an engine message assert it,
# proving the caller-supplied-clock determinism end to end.
ENGINE_ST = "20260603-16:55:33.000"


def checksum(data: bytes) -> int:
    return sum(data) % 256


def build(msg_type: str, seq: int, extra: list = None) -> bytes:
    body = (
        f"35={msg_type}\x01"
        f"49={SENDER}\x01"
        f"56={TARGET}\x01"
        f"34={seq}\x01"
        f"52={TS}\x01"
    )
    if extra:
        for tag, val in extra:
            body += f"{tag}={val}\x01"
    body_b = body.encode()
    header = f"8=FIX.4.4\x019={len(body_b)}\x01".encode()
    ck = checksum(header + body_b)
    return header + body_b + f"10={ck:03d}\x01".encode()


_RECV_BUF = bytearray()


def _parse_fields(msg_bytes: bytes) -> dict:
    fields = {}
    for field in msg_bytes.split(b"\x01"):
        if b"=" in field:
            k, _, v = field.partition(b"=")
            fields[k.decode()] = v.decode()
    return fields


def recv_msg(conn: socket.socket) -> dict:
    """Parse the next full FIX message, preserving any trailing pipelined bytes."""
    while True:
        buf = _RECV_BUF
        i = buf.find(b"\x019=")
        if i >= 0:
            j = buf.find(b"\x01", i + 3)
            if j >= 0:
                body_len = int(buf[i + 3 : j])
                total = (j + 1) + body_len + 7
                if len(buf) >= total:
                    msg_bytes = bytes(buf[:total])
                    del _RECV_BUF[:total]
                    return _parse_fields(msg_bytes)
        chunk = conn.recv(4096)
        if not chunk:
            raise EOFError("connection closed")
        _RECV_BUF.extend(chunk)


# ── existing scenarios ───────────────────────────────────────────────────────


def logon_logout(conn: socket.socket):
    seq = 1
    msg = recv_msg(conn)
    assert msg.get("35") == "A", f"expected Logon, got {msg.get('35')}"
    # The engine's SendingTime(52) comes from the fixed caller clock — assert it
    # exactly (the deterministic-core payoff).
    assert msg.get("52") == ENGINE_ST, f"engine SendingTime {msg.get('52')} != {ENGINE_ST}"
    conn.sendall(build("A", seq, [(108, "30")]))
    seq += 1
    conn.sendall(build("5", seq))
    seq += 1
    msg = recv_msg(conn)
    assert msg.get("35") == "5", f"expected Logout, got {msg.get('35')}"
    assert msg.get("52") == ENGINE_ST, f"engine Logout SendingTime {msg.get('52')} != {ENGINE_ST}"


def heartbeat(conn: socket.socket):
    seq = 1
    msg = recv_msg(conn)
    assert msg.get("35") == "A"
    conn.sendall(build("A", seq, [(108, "30")]))
    seq += 1
    conn.sendall(build("1", seq, [(112, "TEST1")]))
    seq += 1
    while True:
        msg = recv_msg(conn)
        if msg.get("35") == "0" and msg.get("112") == "TEST1":
            # The user-driven Heartbeat echo also carries the fixed SendingTime.
            assert msg.get("52") == ENGINE_ST, f"engine HB SendingTime {msg.get('52')} != {ENGINE_ST}"
            break
    conn.sendall(build("5", seq))
    seq += 1
    msg = recv_msg(conn)
    assert msg.get("35") == "5"


def resend(conn: socket.socket):
    seq = 1
    msg = recv_msg(conn)
    assert msg.get("35") == "A"
    conn.sendall(build("A", seq, [(108, "30")]))
    seq += 1
    msg = recv_msg(conn)
    assert msg.get("35") == "D", f"expected NewOrder, got {msg.get('35')}"
    conn.sendall(build("2", seq, [(7, "2"), (16, "2")]))
    seq += 1
    while True:
        msg = recv_msg(conn)
        if msg.get("43") == "Y":
            assert msg.get("122"), "OrigSendingTime (122) must be set on PossDup replay"
            break
        if msg.get("35") == "4":
            break
    conn.sendall(build("5", seq))
    seq += 1
    msg = recv_msg(conn)
    assert msg.get("35") == "5"


def gap_fill(conn: socket.socket):
    seq = 1
    msg = recv_msg(conn)
    assert msg.get("35") == "A"
    conn.sendall(build("A", seq, [(108, "30")]))
    seq += 1
    conn.sendall(build("4", seq, [(123, "Y"), (36, "5")]))
    seq = 5
    conn.sendall(build("5", seq))
    seq += 1
    msg = recv_msg(conn)
    assert msg.get("35") == "5"


def seq_reset(conn: socket.socket):
    seq = 1
    msg = recv_msg(conn)
    assert msg.get("35") == "A"
    conn.sendall(build("A", seq, [(108, "30")]))
    seq += 1
    conn.sendall(build("4", seq, [(36, "10")]))
    seq = 10
    conn.sendall(build("5", seq))
    seq += 1
    msg = recv_msg(conn)
    assert msg.get("35") == "5"


# ── helpers for the battle-test scenarios ────────────────────────────────────


def _logon(conn, hbi: str = "30"):
    """Complete the initiator handshake: read the engine's Logon, send our ack."""
    msg = recv_msg(conn)
    assert msg.get("35") == "A", f"expected Logon, got {msg.get('35')}"
    conn.sendall(build("A", 1, [(108, hbi)]))  # peer Logon seq 1 → engine next_inbound=2


def _read_until_logout(conn):
    """Read (discarding leftovers) until the engine's Logout (35=5), then return."""
    try:
        while True:
            if recv_msg(conn).get("35") == "5":
                return
    except EOFError:
        pass


# ── Tier 1 — sequence-number correctness ─────────────────────────────────────


def app_seq_too_high(conn):
    """Case 1: app seq higher than expected → engine sends ResendRequest."""
    _logon(conn)
    conn.sendall(build("D", 5, [(11, "ORD-GAP")]))  # seq 5, expected 2 → gap
    msg = recv_msg(conn)
    assert msg.get("35") == "2", f"expected ResendRequest, got {msg.get('35')}"
    assert msg.get("7") == "2", f"BeginSeqNo must be next_inbound=2, got {msg.get('7')}"
    assert msg.get("16") == "0", f"EndSeqNo must be 0 (open-ended), got {msg.get('16')}"
    # Return → finally closes the socket → engine sees EOF while Resending.


def app_seq_too_low(conn):
    """Case 2: app seq below expected, no PossDup → SeqNumTooLow disconnect."""
    _logon(conn)
    conn.sendall(build("D", 2, [(11, "ORD-1")]))  # in-order → engine next_inbound=3
    conn.sendall(build("D", 2, [(11, "ORD-DUP")]))  # 2 < 3, no PossDup → SeqNumTooLow
    _read_until_logout(conn)  # engine emits Logout before disconnecting


def seq_too_low_poss_dup(conn):
    """Case 3: seq below expected WITH PossDup=Y → ignored, session continues."""
    _logon(conn)
    conn.sendall(build("0", 2))  # heartbeat seq 2 → engine next_inbound=3
    conn.sendall(build("0", 2, [(43, "Y")]))  # dup seq 2, PossDup=Y → must be ignored
    # Prove liveness: a TestRequest at the expected seq must still be echoed.
    conn.sendall(build("1", 3, [(112, "ALIVE")]))
    while True:
        m = recv_msg(conn)
        if m.get("35") == "0" and m.get("112") == "ALIVE":
            break
    conn.sendall(build("5", 4))
    _read_until_logout(conn)


def app_in_order(conn):
    """Case 4: in-order app → surfaced as Application, then clean logout."""
    _logon(conn)
    conn.sendall(build("D", 2, [(11, "ORD-INSEQ")]))  # in-order app seq 2
    conn.sendall(build("5", 3))  # Logout seq 3
    _read_until_logout(conn)


def resend_open_ended(conn):
    """Case 6: ResendRequest EndSeqNo=0 → replay everything sent."""
    _logon(conn)
    m = recv_msg(conn)
    assert m.get("35") == "D", f"expected the engine's app, got {m.get('35')}"
    conn.sendall(build("2", 2, [(7, "1"), (16, "0")]))  # open-ended resend from 1
    saw_replay = False
    while not saw_replay:
        m = recv_msg(conn)
        # A GapFill (35=4) also carries 43=Y, so match it FIRST — only a real app
        # replay (35=D) must carry OrigSendingTime(122).
        if m.get("35") == "4" and m.get("123") == "Y":  # GapFill for admin holes
            saw_replay = True
        elif m.get("35") == "D" and m.get("43") == "Y":  # PossDup app replay
            assert m.get("122"), "PossDup app replay must carry OrigSendingTime(122)"
            saw_replay = True
    conn.sendall(build("5", 3))
    _read_until_logout(conn)


def resend_admin_and_app(conn):
    """Case 7: ResendRequest spanning admin+app → GapFill admin, replay app."""
    _logon(conn)
    assert recv_msg(conn).get("35") == "D"  # engine app seq 2
    assert recv_msg(conn).get("35") == "D"  # engine app seq 3
    conn.sendall(build("2", 2, [(7, "1"), (16, "3")]))  # resend [1,3]
    saw_gapfill = False
    saw_app_replay = False
    while not (saw_gapfill and saw_app_replay):
        m = recv_msg(conn)
        if m.get("35") == "4" and m.get("123") == "Y":  # admin hole (seq 1 Logon) gap-filled
            saw_gapfill = True
        elif m.get("35") == "D" and m.get("43") == "Y":  # app replay with PossDup
            assert m.get("122"), "app replay must carry OrigSendingTime(122)"
            saw_app_replay = True
    conn.sendall(build("5", 3))  # seq 3 (contiguous after the ResendRequest at seq 2)
    _read_until_logout(conn)


def resend_during_resend(conn):
    """Case 8: ResendRequest arriving while engine is already Resending."""
    _logon(conn)
    conn.sendall(build("0", 5))  # gap (expected 2) → engine sends ResendRequest, Resending
    m = recv_msg(conn)
    assert m.get("35") == "2", f"expected engine ResendRequest, got {m.get('35')}"
    # While the engine is Resending, ask IT to resend — in-sequence (seq 2) so it
    # must be honored despite the in-progress inbound recovery.
    conn.sendall(build("2", 2, [(7, "1"), (16, "0")]))
    saw_replay = False
    while not saw_replay:
        m = recv_msg(conn)
        if m.get("43") == "Y" or (m.get("35") == "4" and m.get("123") == "Y"):
            saw_replay = True
    # Return → close → engine sees EOF while still Resending its own gap.


def seq_reset_backward(conn):
    """Case 11: SequenceReset-Reset NewSeqNo < expected → Reject, no rewind."""
    _logon(conn)
    conn.sendall(build("0", 2))  # heartbeat seq 2 → engine next_inbound=3
    conn.sendall(build("4", 99, [(36, "1")]))  # Reset mode, NewSeqNo=1 < 3 → backward
    m = recv_msg(conn)
    assert m.get("35") == "3", f"expected Reject, got {m.get('35')}"
    assert m.get("371") == "36", f"Reject RefTagID must be 36, got {m.get('371')}"
    # Session must NOT have disconnected: prove it with a TestRequest at seq 3.
    conn.sendall(build("1", 3, [(112, "STILLUP")]))
    while True:
        m = recv_msg(conn)
        if m.get("35") == "0" and m.get("112") == "STILLUP":
            break
    conn.sendall(build("5", 4))
    _read_until_logout(conn)


def seq_reset_gap_fill_oos(conn):
    """Case 12: SequenceReset-GapFill out of sequence → ResendRequest, no advance."""
    _logon(conn)
    # GapFill at MsgSeqNum 5 (expected 2) with NewSeqNo 10: itself a gap.
    conn.sendall(build("4", 5, [(123, "Y"), (36, "10")]))
    m = recv_msg(conn)
    assert m.get("35") == "2", f"expected ResendRequest, got {m.get('35')}"
    assert m.get("7") == "2", f"BeginSeqNo must stay 2 (no advance to 10), got {m.get('7')}"
    # Return → close → engine sees EOF while Resending.


# ── Tier 3 — liveness ────────────────────────────────────────────────────────


def test_request_long_id(conn):
    """Case 24: TestRequest with a >64-byte TestReqID → verbatim echo, no truncation."""
    _logon(conn)
    long_id = "X" * 200
    conn.sendall(build("1", 2, [(112, long_id)]))  # TestRequest seq 2
    while True:
        m = recv_msg(conn)
        if m.get("35") == "0":
            assert m.get("112") == long_id, "TestReqID must echo verbatim (no truncation)"
            break
    conn.sendall(build("5", 3))
    _read_until_logout(conn)


# ── regression (finding Q1 — currently a confirmed engine bug) ───────────────


def seq_reset_gap_fill_below_possdup(conn):
    """Q1 regression: a below-expected SequenceReset-GapFill carrying PossDup=Y
    must be DISCARDED (session survives), not treated as SeqNumTooLow.

    Choreographs the SPEC-CORRECT outcome; the paired Rust test is `#[ignore]`'d
    until the engine bug (`on_sequence_reset` hard-codes poss_dup=false) is fixed.
    """
    _logon(conn)  # engine next_inbound=2
    conn.sendall(build("0", 2))  # heartbeat seq 2 → engine next_inbound=3
    # GapFill whose OWN MsgSeqNum (2) is below expected (3), with PossDupFlag=Y →
    # per FIX 4.4 + QuickFIX this is discarded, and the session stays up.
    conn.sendall(build("4", 2, [(43, "Y"), (123, "Y"), (36, "10")]))
    # Prove survival: a TestRequest at the expected seq must still be echoed.
    conn.sendall(build("1", 3, [(112, "SURVIVED")]))
    while True:
        m = recv_msg(conn)
        if m.get("35") == "0" and m.get("112") == "SURVIVED":
            break
    conn.sendall(build("5", 4))
    _read_until_logout(conn)


SCENARIOS = {
    "logon_logout": logon_logout,
    "heartbeat": heartbeat,
    "resend": resend,
    "gap_fill": gap_fill,
    "seq_reset": seq_reset,
    # battle-test — Tier 1
    "app_seq_too_high": app_seq_too_high,
    "app_seq_too_low": app_seq_too_low,
    "seq_too_low_poss_dup": seq_too_low_poss_dup,
    "app_in_order": app_in_order,
    "resend_open_ended": resend_open_ended,
    "resend_admin_and_app": resend_admin_and_app,
    "resend_during_resend": resend_during_resend,
    "seq_reset_backward": seq_reset_backward,
    "seq_reset_gap_fill_oos": seq_reset_gap_fill_oos,
    # battle-test — Tier 3
    "test_request_long_id": test_request_long_id,
    # regression (finding Q1)
    "seq_reset_gap_fill_below_possdup": seq_reset_gap_fill_below_possdup,
}

if __name__ == "__main__":
    scenario = sys.argv[1] if len(sys.argv) > 1 else "logon_logout"
    fn = SCENARIOS.get(scenario)
    if fn is None:
        print(f"unknown scenario: {scenario}", file=sys.stderr)
        sys.exit(1)

    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind(("127.0.0.1", 0))
    srv.listen(1)
    port = srv.getsockname()[1]
    print(port, flush=True)

    conn, _ = srv.accept()
    conn.settimeout(10.0)
    try:
        fn(conn)
    finally:
        conn.close()
        srv.close()
