//! Fix B (async): a single inbound frame larger than the reader buffer must
//! surface as `MessageTooLarge`, not a false disconnect. The async wrapper's
//! `NeedMoreBytes` guard must behave identically to the sync wrapper's: when
//! `read_spare()` is empty (the buffer is full with one incomplete frame that
//! cannot grow), return `MessageTooLarge` instead of reading into a zero-length
//! slice and misreading `Ok(0)` as EOF.

#![cfg(unix)]

use std::collections::VecDeque;
use std::io;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

use nexus_async_fix_engine::{AsyncReadAdapter, Error as TransportError, FixConnection};
use nexus_fix_codec::{
    FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{CompId, DisconnectReason, FixJournal, SessionConfig, SessionState};
use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};

// ── mock dictionary (mirrors the sync engine's tests) ────────────────────────

struct MockDict;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum MockMsgType {}

struct AdminDecoder<'buf> {
    _buf: &'buf [u8],
}

impl<'buf> FixAdminMsg<'buf> for AdminDecoder<'buf> {
    fn decode(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError> {
        Ok(Self { _buf: buf })
    }
}

impl FixDictionary for MockDict {
    type MsgType = MockMsgType;
    type Header<'buf> = MockHeader<'buf>;
    type Logon<'buf> = AdminDecoder<'buf>;
    type Logout<'buf> = AdminDecoder<'buf>;
    type Heartbeat<'buf> = AdminDecoder<'buf>;
    type TestRequest<'buf> = AdminDecoder<'buf>;
    type ResendRequest<'buf> = AdminDecoder<'buf>;
    type SequenceReset<'buf> = AdminDecoder<'buf>;
    type Reject<'buf> = AdminDecoder<'buf>;
    const BEGIN_STRING: &'static [u8] = b"FIX.4.4";
    fn is_admin(_: MockMsgType) -> bool {
        false
    }
}

struct MockHeader<'buf> {
    buf: &'buf [u8],
}

impl<'buf> FixHeader<'buf> for MockHeader<'buf> {
    fn decode(buf: &'buf [u8]) -> Self {
        Self { buf }
    }

    fn raw_msg_type(&self) -> Option<FieldView<'buf, &'buf [u8]>> {
        find_tag(self.buf, 0, 35).and_then(|s| FieldView::new(s, self.buf))
    }

    fn msg_seq_num(&self) -> Option<FieldView<'buf, u64>> {
        find_tag(self.buf, 0, 34).and_then(|s| FieldView::new(s, self.buf))
    }

    fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf nexus_fix_codec::AsciiTextStr>> {
        find_tag(self.buf, 0, 49).and_then(|s| FieldView::new(s, self.buf))
    }

    fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf nexus_fix_codec::AsciiTextStr>> {
        find_tag(self.buf, 0, 56).and_then(|s| FieldView::new(s, self.buf))
    }

    fn poss_dup_flag(&self) -> Option<FieldView<'buf, bool>> {
        find_tag(self.buf, 0, 43).and_then(|s| FieldView::new(s, self.buf))
    }

    fn sending_time(&self) -> Option<FieldView<'buf, FixTimestamp>> {
        None
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────

fn sender() -> CompId {
    CompId::new(b"INITIATOR").unwrap()
}
fn target() -> CompId {
    CompId::new(b"ACCEPTOR").unwrap()
}

/// RAII scratch directory. `FixJournal::open` preallocates tens of megabytes
/// into each of these, so they must not outlive the test that made them.
/// `Drop` also runs while unwinding, so a *failing* test cleans up too — which
/// a manual `cleanup(&dir)` at the end of the body would not.
///
/// Bind it to a live local (`let dir = tmp_dir(..)`), never `let _ = ..`, or
/// the directory is removed before the test can use it.
struct TempDir(std::path::PathBuf);

impl TempDir {
    fn new(suffix: &str) -> Self {
        let mut p = std::env::temp_dir();
        p.push(format!(
            "nexus_async_fix_toolarge_{}_{}",
            std::process::id(),
            suffix
        ));
        // A previous run killed by a signal can leave the tree behind, and PIDs
        // get recycled -- start from a clean slate.
        let _ = std::fs::remove_dir_all(&p);
        std::fs::create_dir_all(&p).unwrap();
        Self(p)
    }

    fn path(&self) -> &std::path::Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn tmp_dir(suffix: &str) -> TempDir {
    TempDir::new(suffix)
}

/// Async stream that hands out queued inbound bytes (never more than the
/// caller's `ReadBuf` room) and swallows writes. The mirror of the sync
/// `ChunkStream` in `nexus-fix-engine/tests/transport.rs`.
struct ChunkStream {
    inbound: VecDeque<u8>,
}

impl ChunkStream {
    fn new(bytes: &[u8]) -> Self {
        Self {
            inbound: bytes.iter().copied().collect(),
        }
    }
}

impl AsyncRead for ChunkStream {
    fn poll_read(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let n = buf.remaining().min(self.inbound.len());
        for _ in 0..n {
            buf.put_slice(&[self.inbound.pop_front().unwrap()]);
        }
        Poll::Ready(Ok(()))
    }
}

impl AsyncWrite for ChunkStream {
    fn poll_write(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        Poll::Ready(Ok(buf.len()))
    }
    fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
    }
    fn poll_shutdown(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
    }
}

#[tokio::test]
async fn frame_exceeding_reader_buffer_is_message_too_large_not_disconnect() {
    let dir = tmp_dir("reader_buf_too_large");

    // One valid, self-delimiting FIX frame larger than a tiny reader buffer but
    // well under the 1 MiB frame-reader max.
    const READER_CAP: usize = 256;
    let mut buf = vec![0u8; 4096];
    let big_filler = vec![b'x'; 512]; // frame ~570 bytes > READER_CAP
    let frame = {
        let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        let mut seq_buf = [0u8; 10];
        let seq_n = encode_fix_uint(1, &mut seq_buf);
        fmt.field(34, &seq_buf[..seq_n]);
        fmt.field(49, sender().as_bytes());
        fmt.field(56, target().as_bytes());
        fmt.field(52, b"20260615-12:00:00.000");
        fmt.field(58, &big_filler);
        let (start, len) = fmt.finish().unwrap();
        buf[start..start + len].to_vec()
    };
    assert!(
        frame.len() > READER_CAP,
        "frame must exceed the reader buffer to trip the guard"
    );

    let stream = ChunkStream::new(&frame);
    let mut conn: FixConnection<AsyncReadAdapter<ChunkStream>, MockDict> =
        FixConnection::builder().reader_capacity(READER_CAP).accept(
            AsyncReadAdapter::new(stream),
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: target(),
                target: sender(),
            },
            FixJournal::open(dir.path(), 0, 256).unwrap(),
        );

    match conn.recv(Instant::now()).await {
        Err(TransportError::MessageTooLarge(_)) => {}
        Err(TransportError::UnexpectedDisconnect { reason }) => {
            panic!("frame exceeding reader buffer was misread as a disconnect: {reason:?}")
        }
        Err(other) => panic!(
            "an inbound frame exceeding the reader buffer must be MessageTooLarge, got {other:?}"
        ),
        Ok(_) => panic!("frame exceeding reader buffer must not surface a message"),
    }
}

#[tokio::test]
async fn peer_eof_is_peer_closed_then_recv_is_closed() {
    // Async parity with the sync engine: a peer EOF (empty stream, no Logout) is
    // an abnormal `UnexpectedDisconnect { PeerClosed }`, not a fake clean logout,
    // and every recv after that terminal is `Closed`.
    let dir = tmp_dir("async_peer_eof");
    let mut conn: FixConnection<AsyncReadAdapter<ChunkStream>, MockDict> = FixConnection::builder()
        .accept(
            AsyncReadAdapter::new(ChunkStream::new(b"")),
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: target(),
                target: sender(),
            },
            FixJournal::open(dir.path(), 0, 256).unwrap(),
        );

    let Err(err) = conn.recv(Instant::now()).await else {
        panic!("expected an error on peer EOF");
    };
    assert!(err.is_fatal());
    assert!(matches!(
        err,
        TransportError::UnexpectedDisconnect {
            reason: DisconnectReason::PeerClosed
        }
    ));

    // Session terminated → every subsequent recv is Closed.
    let Err(err2) = conn.recv(Instant::now()).await else {
        panic!("expected Closed on a terminated session");
    };
    assert!(matches!(err2, TransportError::Closed));
}
