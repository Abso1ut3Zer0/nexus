import os
import socket
import time

from behave import given, when, then

FIX_PORT = int(os.environ.get("FIX_PORT", "9878"))

_SENDER = "INITIATOR"
_TARGET = "ACCEPTOR"
_TS = "20260101-00:00:00.000"


def _checksum(data: bytes) -> int:
    return sum(data) % 256


def _build(msg_type, seq, extra=None, bad_checksum=False, body_len_override=None):
    body = (
        f"35={msg_type}\x01"
        f"49={_SENDER}\x01"
        f"56={_TARGET}\x01"
        f"34={seq}\x01"
        f"52={_TS}\x01"
    )
    if extra:
        for tag, val in extra:
            body += f"{tag}={val}\x01"
    body_b = body.encode()
    declared = body_len_override if body_len_override is not None else len(body_b)
    header = f"8=FIX.4.4\x019={declared}\x01".encode()
    ck = _checksum(header + body_b)
    if bad_checksum:
        ck = (ck + 1) % 256
    return header + body_b + f"10={ck:03d}\x01".encode()


def _recv(sock, buf):
    body_len = None
    header_end = 0
    while True:
        chunk = sock.recv(4096)
        if not chunk:
            raise EOFError
        buf += chunk
        if body_len is None:
            i = buf.find(b"\x019=")
            if i >= 0:
                j = buf.find(b"\x01", i + 3)
                if j >= 0:
                    body_len = int(buf[i + 3:j])
                    header_end = j + 1
        if body_len is not None and len(buf) >= header_end + body_len + 7:
            end = header_end + body_len + 7
            fields = {}
            for part in buf[:end].split(b"\x01"):
                if b"=" in part:
                    k, _, v = part.partition(b"=")
                    fields[k.decode(errors="replace")] = v.decode(errors="replace")
            return fields, buf[end:]


class RawPeer:
    def __init__(self, port):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.connect(("127.0.0.1", port))
        self.sock.settimeout(5.0)
        self._seq = 1
        self._buf = b""

    def send(self, msg_type, extra=None, seq=None, **kw):
        s = self._seq if seq is None else seq
        self.sock.sendall(_build(msg_type, s, extra, **kw))
        if seq is None:
            self._seq += 1

    def send_raw(self, data: bytes):
        self.sock.sendall(data)

    def recv(self):
        msg, self._buf = _recv(self.sock, self._buf)
        return msg

    def logon(self):
        self.send("A", [(108, "30")])
        msg = self.recv()
        assert msg.get("35") == "A", f"expected Logon from engine, got {msg}"

    def gone(self, timeout=5.0):
        self.sock.settimeout(timeout)
        try:
            while True:
                data = self.sock.recv(4096)
                if not data:
                    return True
        except socket.timeout:
            return False
        except OSError:
            return True

    def close(self):
        try:
            self.sock.close()
        except OSError:
            pass


@given("a raw FIX 4.4 peer connects to the harness")
def step_raw_connect(context):
    time.sleep(0.3)
    context.raw_peer = RawPeer(FIX_PORT)


@when("the peer performs a Logon handshake")
def step_raw_logon(context):
    context.raw_peer.logon()


@when("the peer sends a Heartbeat with a bad checksum")
def step_raw_bad_checksum(context):
    context.raw_peer.send("0", bad_checksum=True)


@when("the peer sends a Heartbeat with BodyLength {n:d}")
def step_raw_bad_body_len(context, n):
    context.raw_peer.send("0", body_len_override=n)


@when("the peer sends garbage bytes")
def step_raw_garbage(context):
    context.raw_peer.send_raw(b"not a fix message\x01junk\x01")


@when("the peer sends a Heartbeat with seqnum {n:d}")
def step_raw_explicit_seq(context, n):
    context.raw_peer.send("0", seq=n)


@when("the peer sends a ResendRequest with EndSeqNo {n:d}")
def step_raw_resend_request(context, n):
    context.raw_peer.send("2", [(7, "1"), (16, str(n))])


@then("the engine closes the connection")
def step_raw_gone(context):
    assert context.raw_peer.gone(timeout=8.0), \
        "engine did not close the connection within 8s"


@then("the engine replies with SequenceReset")
def step_raw_seq_reset(context):
    deadline = time.monotonic() + 10.0
    while time.monotonic() < deadline:
        try:
            msg = context.raw_peer.recv()
            if msg.get("35") == "4":
                return
        except (EOFError, socket.timeout, OSError):
            break
    assert False, "engine did not reply with SequenceReset within 10s"
