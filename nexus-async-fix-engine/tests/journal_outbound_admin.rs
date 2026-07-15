//! Outbound admin messages sent by an async session must land in the session's
//! outbound journal, mirroring the sync engine's `store_admin` behavior. The
//! both-sides archive is incomplete if async sessions journal inbound + app but
//! drop their own Logon/Heartbeat/Logout/... admin frames.

#![cfg(unix)]

use std::io;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

use nexus_async_fix_engine::AsyncFixConnection;
use nexus_fix_engine::{CompId, FixJournal, SessionConfig, SessionState};
use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};

const BEGIN: &[u8] = b"FIX.4.4";

fn tmp_dir(suffix: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!(
        "nexus_async_fix_admin_{}_{}",
        std::process::id(),
        suffix
    ));
    std::fs::create_dir_all(&p).unwrap();
    p
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
        let mut conn = AsyncFixConnection::from_parts(
            SinkStream::default(),
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: CompId::new(b"ENGINE").unwrap(),
                target: CompId::new(b"PEER").unwrap(),
            },
            FixJournal::open(&dir, 0, 256).unwrap(),
            BEGIN,
        );
        // Sends the opening Logon at seq 1; the write is accepted by the sink.
        conn.connect().await.unwrap();
    }

    // The Logon (seq 1) must be present in the outbound journal: recovering the
    // outbound counter from the meta-slot yields 2 only if `store(1, ..)` ran.
    // A journal that never stored anything recovers to 1.
    let recovered = FixJournal::open(&dir, 0, 256).unwrap();
    assert_eq!(
        recovered.next_outbound(),
        2,
        "outbound Logon admin must be journaled"
    );
}
