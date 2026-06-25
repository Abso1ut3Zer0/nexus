"""FIX 4.4 conformance peer. Accepts one connection, runs one scenario, exits."""

import socket
import sys

SENDER = "PEER"
TARGET = "ENGINE"
TS = "20260101-00:00:00.000"


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


def recv_msg(conn: socket.socket) -> dict:
    buf = b""
    body_len = None
    header_end = 0
    while True:
        chunk = conn.recv(4096)
        if not chunk:
            raise EOFError("connection closed")
        buf += chunk
        if body_len is None:
            i = buf.find(b"\x019=")
            if i >= 0:
                j = buf.find(b"\x01", i + 3)
                if j >= 0:
                    body_len = int(buf[i + 3 : j])
                    header_end = j + 1
        if body_len is not None and len(buf) >= header_end + body_len + 7:
            msg_bytes = buf[: header_end + body_len + 7]
            fields = {}
            for field in msg_bytes.split(b"\x01"):
                if b"=" in field:
                    k, _, v = field.partition(b"=")
                    fields[k.decode()] = v.decode()
            return fields


def logon_logout(conn: socket.socket):
    seq = 1
    msg = recv_msg(conn)
    assert msg.get("35") == "A", f"expected Logon, got {msg.get('35')}"
    conn.sendall(build("A", seq, [(108, "30")]))
    seq += 1
    conn.sendall(build("5", seq))
    seq += 1
    msg = recv_msg(conn)
    assert msg.get("35") == "5", f"expected Logout, got {msg.get('35')}"


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
    msg = recv_msg(conn)
    assert msg.get("43") == "Y", f"expected replay (43=Y), got 35={msg.get('35')}"
    assert msg.get("122"), "OrigSendingTime (122) must be set on PossDup replay"
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
    assert msg.get("35") == "5", f"expected Logout, got 35={msg.get('35')}"


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
    assert msg.get("35") == "5", f"expected Logout, got 35={msg.get('35')}"


SCENARIOS = {
    "logon_logout": logon_logout,
    "heartbeat": heartbeat,
    "resend": resend,
    "gap_fill": gap_fill,
    "seq_reset": seq_reset,
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
