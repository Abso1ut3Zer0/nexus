//! Outbound admin messages sent by an async session must land in the session's
//! outbound journal, mirroring the sync engine's `store_admin` behavior. The
//! both-sides archive is incomplete if async sessions journal inbound + app but
//! drop their own Logon/Heartbeat/Logout/... admin frames.

#![cfg(unix)]

use std::time::Duration;

use nexus_async_fix_engine::{FixParts, FixSession};
use nexus_fix_codec::{FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, find_tag};
use nexus_fix_engine::{CompId, FixJournal, SessionConfig, SessionState};

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

#[tokio::test]
async fn outbound_admin_is_journaled() {
    let dir = tmp_dir("logon");

    {
        // No transport needed: the encode-only `encode_connect` journals the Logon
        // as it stages it into the writer — the write to a socket is a separate step
        // (`recv` drains it) and is not what this test pins.
        let FixParts {
            mut session,
            reader: _reader,
            mut writer,
        } = FixSession::<MockDict>::builder().build(
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: CompId::new(b"ENGINE").unwrap(),
                target: CompId::new(b"PEER").unwrap(),
            },
            FixJournal::open(dir.path(), 0, 256).unwrap(),
        );
        // Encodes + journals the opening Logon at seq 1 into the writer.
        session
            .encode_connect(&mut writer, 1_780_505_733_000_000_000)
            .unwrap();
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
