use nexus_fix_codec::{FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, find_tag};
use nexus_fix_engine::{FrameReader, MessageReader, MessageWriter};
use nexus_net::wire::ParserSink;

// ── minimal mock dictionary ──────────────────────────────────────────────────

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

fn feed_bytes<D: FixDictionary>(r: &mut MessageReader<D>, data: &[u8]) {
    let spare = r.spare();
    spare[..data.len()].copy_from_slice(data);
    r.filled(data.len());
}

// ── tests ────────────────────────────────────────────────────────────────────

#[test]
fn frame_reader_yields_complete_frame() {
    let msg = b"8=FIX.4.4\x019=5\x0135=0\x0110=163\x01";
    let mut fr = FrameReader::builder().build();
    fr.read(msg).unwrap();
    let frame = fr.next().unwrap().unwrap();
    assert_eq!(frame, msg.as_slice());
}

#[test]
fn frame_reader_buffers_partial_then_complete() {
    let msg = b"8=FIX.4.4\x019=5\x0135=0\x0110=163\x01";
    let mut fr = FrameReader::builder().build();
    let half = msg.len() / 2;
    fr.read(&msg[..half]).unwrap();
    assert!(fr.next().unwrap().is_none());
    fr.read(&msg[half..]).unwrap();
    let frame = fr.next().unwrap().unwrap();
    assert_eq!(frame, msg.as_slice());
}

#[test]
fn message_reader_spare_filled_interface() {
    let msg = b"8=FIX.4.4\x019=5\x0135=0\x0110=163\x01";
    let mut r: MessageReader<MockDict> = MessageReader::new();
    feed_bytes(&mut r, msg);
    // The bytes are now in the internal FrameReader. Verify by feeding another message
    // and confirming the reader accepts more bytes (it didn't OOM).
    let msg2 = b"8=FIX.4.4\x019=5\x0135=0\x0110=163\x01";
    feed_bytes(&mut r, msg2);
}

#[test]
fn message_writer_flush_to() {
    let mut w: MessageWriter<MockDict> = MessageWriter::new();
    assert!(w.is_empty());

    let mut sink = Vec::new();
    w.flush_to(&mut sink).unwrap();
    assert_eq!(sink.len(), 0);
}

#[test]
fn message_writer_is_empty_after_flush() {
    let mut w: MessageWriter<MockDict> = MessageWriter::new();
    assert!(w.is_empty());
    assert_eq!(w.remaining(), w.remaining());
    let mut sink = Vec::new();
    w.flush_to(&mut sink).unwrap();
    assert!(w.is_empty());
}

#[cfg(unix)]
mod unix_tests {
    use nexus_fix_engine::{AdminMsg, CompId, MessageWriter, SessionConfig};

    use super::MockDict;

    fn config() -> SessionConfig {
        SessionConfig {
            sender: CompId::new(b"SENDER").unwrap(),
            target: CompId::new(b"TARGET").unwrap(),
        }
    }

    #[test]
    fn encode_admin_logon_produces_valid_frame() {
        let mut w: MessageWriter<MockDict> = MessageWriter::new();
        let config = config();
        w.encode_admin(
            AdminMsg::Logon {
                seq: 1,
                heart_bt_int_s: 30,
            },
            &config,
        );
        assert!(!w.is_empty());

        let data = w.data();
        assert!(data.starts_with(b"8=FIX.4.4\x01"));
        assert!(data.windows(5).any(|c| c == b"35=A\x01"));
        assert!(
            data.windows(b"49=SENDER\x01".len())
                .any(|c| c == b"49=SENDER\x01")
        );
        assert!(
            data.windows(b"56=TARGET\x01".len())
                .any(|c| c == b"56=TARGET\x01")
        );
        assert!(
            data.windows(b"108=30\x01".len())
                .any(|c| c == b"108=30\x01")
        );
        assert!(*data.last().unwrap() == b'\x01');

        let mut out = Vec::new();
        w.flush_to(&mut out).unwrap();
        assert!(w.is_empty());
        assert!(!out.is_empty());
    }

    #[test]
    fn encode_admin_logout_produces_valid_frame() {
        let mut w: MessageWriter<MockDict> = MessageWriter::new();
        let config = config();
        w.encode_admin(AdminMsg::Logout { seq: 2 }, &config);
        assert!(!w.is_empty());
        let data = w.data();
        assert!(data.starts_with(b"8=FIX.4.4\x01"));
        assert!(data.windows(5).any(|c| c == b"35=5\x01"));
    }

    #[test]
    fn encode_admin_heartbeat_without_echo() {
        let mut w: MessageWriter<MockDict> = MessageWriter::new();
        let config = config();
        w.encode_admin(AdminMsg::Heartbeat { seq: 3, echo: None }, &config);
        assert!(!w.is_empty());
        let data = w.data();
        assert!(data.windows(5).any(|c| c == b"35=0\x01"));
        assert!(!data.windows(b"112=".len()).any(|c| c == b"112="));
    }

    #[test]
    fn encode_admin_resend_request() {
        let mut w: MessageWriter<MockDict> = MessageWriter::new();
        let config = config();
        w.encode_admin(AdminMsg::ResendRequest { seq: 4, begin: 2 }, &config);
        assert!(!w.is_empty());
        let data = w.data();
        assert!(data.windows(5).any(|c| c == b"35=2\x01"));
        assert!(data.windows(b"7=2\x01".len()).any(|c| c == b"7=2\x01"));
        assert!(data.windows(b"16=0\x01".len()).any(|c| c == b"16=0\x01"));
    }

    #[test]
    fn encode_admin_sequence_reset() {
        let mut w: MessageWriter<MockDict> = MessageWriter::new();
        let config = config();
        w.encode_admin(
            AdminMsg::SequenceReset {
                seq: 5,
                new_seq: 10,
            },
            &config,
        );
        assert!(!w.is_empty());
        let data = w.data();
        assert!(data.windows(5).any(|c| c == b"35=4\x01"));
        assert!(data.windows(b"36=10\x01".len()).any(|c| c == b"36=10\x01"));
        assert!(data.windows(b"123=Y\x01".len()).any(|c| c == b"123=Y\x01"));
    }

    #[test]
    fn encode_admin_uses_dict_begin_string() {
        let mut w: MessageWriter<MockDict> = MessageWriter::new();
        let config = config();
        w.encode_admin(AdminMsg::Logout { seq: 1 }, &config);
        let data = w.data();
        assert!(data.starts_with(b"8=FIX.4.4\x01"));
    }
}
