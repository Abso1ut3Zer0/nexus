//! Outbound admin messages sent by an async session must land in the session's
//! outbound journal, mirroring the sync engine's `store_admin` behavior. The
//! both-sides archive is incomplete if async sessions journal inbound + app but
//! drop their own Logon/Heartbeat/Logout/... admin frames.

#![cfg(unix)]

use std::io;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

use nexus_async_fix_engine::FixConnection;
use nexus_fix_codec::{FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, find_tag};
use nexus_fix_engine::{CompId, FixJournal, SessionConfig, SessionState};
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
            "nexus_async_fix_admin_{}_{}",
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

/// In-memory stream: writes are accepted (and buffered), reads block forever.
///
/// `connect()` only exercises the write path — it encodes the opening Logon and
/// flushes it — so the read side never needs data. A perpetually-pending read
/// keeps `recv` from ever being reached in this test.
#[derive(Default)]
struct SinkStream {
    written: Vec<u8>,
}

impl AsyncRead for SinkStream {
    fn poll_read(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        _buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        // Never completes: connect() does not read.
        Poll::Pending
    }
}

impl AsyncWrite for SinkStream {
    fn poll_write(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        self.written.extend_from_slice(buf);
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
async fn outbound_admin_is_journaled() {
    let dir = tmp_dir("logon");

    {
        let mut conn: FixConnection<SinkStream, MockDict> = FixConnection::from_parts(
            SinkStream::default(),
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: CompId::new(b"ENGINE").unwrap(),
                target: CompId::new(b"PEER").unwrap(),
            },
            FixJournal::open(dir.path(), 0, 256).unwrap(),
        );
        // Sends the opening Logon at seq 1; the write is accepted by the sink.
        conn.connect(Instant::now()).await.unwrap();
    }

    // The Logon (seq 1) must be present in the outbound journal: recovering the
    // outbound counter from the meta-slot yields 2 only if `store(1, ..)` ran.
    // A journal that never stored anything recovers to 1.
    let recovered = FixJournal::open(dir.path(), 0, 256).unwrap();
    assert_eq!(
        recovered.next_outbound(),
        2,
        "outbound Logon admin must be journaled"
    );
}
