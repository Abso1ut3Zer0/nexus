#[cfg(not(unix))]
fn main() {}

#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::net::TcpListener;
#[cfg(unix)]
use std::path::Path;
#[cfg(unix)]
use std::time::{Duration, Instant};

#[cfg(unix)]
use nexus_fix_codec::{
    AsciiTextStr, FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, find_tag,
};
#[cfg(unix)]
use nexus_fix_engine::{CompId, FixConnection, FixJournal, Message, SessionConfig, SessionState};

#[cfg(unix)]
struct Fix44;

#[cfg(unix)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Fix44MsgType {}

#[cfg(unix)]
struct Decoder<'buf> {
    _buf: &'buf [u8],
}

#[cfg(unix)]
impl<'buf> FixAdminMsg<'buf> for Decoder<'buf> {
    fn decode(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError> {
        Ok(Self { _buf: buf })
    }
}

#[cfg(unix)]
impl FixDictionary for Fix44 {
    type MsgType = Fix44MsgType;
    type Header<'buf> = Fix44Header<'buf>;
    type Logon<'buf> = Decoder<'buf>;
    type Logout<'buf> = Decoder<'buf>;
    type Heartbeat<'buf> = Decoder<'buf>;
    type TestRequest<'buf> = Decoder<'buf>;
    type ResendRequest<'buf> = Decoder<'buf>;
    type SequenceReset<'buf> = Decoder<'buf>;
    type Reject<'buf> = Decoder<'buf>;
    const BEGIN_STRING: &'static [u8] = b"FIX.4.4";
    fn is_admin(_: Fix44MsgType) -> bool {
        false
    }
}

#[cfg(unix)]
struct Fix44Header<'buf> {
    buf: &'buf [u8],
}

#[cfg(unix)]
impl<'buf> FixHeader<'buf> for Fix44Header<'buf> {
    fn decode(buf: &'buf [u8]) -> Self {
        Self { buf }
    }

    fn raw_msg_type(&self) -> Option<FieldView<'buf, &'buf [u8]>> {
        find_tag(self.buf, 0, 35).and_then(|s| FieldView::new(s, self.buf))
    }

    fn msg_seq_num(&self) -> Option<FieldView<'buf, u64>> {
        find_tag(self.buf, 0, 34).and_then(|s| FieldView::new(s, self.buf))
    }

    fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>> {
        find_tag(self.buf, 0, 49).and_then(|s| FieldView::new(s, self.buf))
    }

    fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>> {
        find_tag(self.buf, 0, 56).and_then(|s| FieldView::new(s, self.buf))
    }

    fn poss_dup_flag(&self) -> Option<FieldView<'buf, bool>> {
        find_tag(self.buf, 0, 43).and_then(|s| FieldView::new(s, self.buf))
    }

    fn sending_time(&self) -> Option<FieldView<'buf, FixTimestamp>> {
        None
    }
}

#[cfg(unix)]
fn reset_journal(dir: &Path) {
    fs::remove_dir_all(dir).ok();
    fs::create_dir_all(dir).expect("failed to create journal dir");
}

#[cfg(unix)]
fn main() {
    let port: u16 = std::env::var("FIX_PORT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(9878);

    let listener = TcpListener::bind(("127.0.0.1", port)).expect("bind failed");
    println!("listening on {}", listener.local_addr().unwrap());

    let dir = {
        let mut p = std::env::temp_dir();
        p.push("nexus_harness");
        p
    };

    loop {
        reset_journal(&dir);
        let (stream, peer) = listener.accept().expect("accept failed");
        stream
            .set_read_timeout(Some(Duration::from_secs(5)))
            .expect("set_read_timeout failed");
        println!("accepted {peer}");

        let mut conn: FixConnection<_, Fix44> = FixConnection::builder().accept(
            stream,
            SessionState::new(Duration::from_secs(30)),
            SessionConfig {
                sender: CompId::new(b"ACCEPTOR").unwrap(),
                target: CompId::new(b"INITIATOR").unwrap(),
            },
            FixJournal::open(&dir, 0, 256).unwrap(),
        );

        let mut app_msgs = 0usize;
        loop {
            match conn.recv(Instant::now()) {
                Ok(Some(Message::Disconnected { reason })) => {
                    println!("disconnected: {reason:?}, {app_msgs} app message(s)");
                    break;
                }
                Ok(Some(Message::Application { .. })) => {
                    app_msgs += 1;
                }
                Ok(Some(_) | None) => {}
                Err(e) => {
                    eprintln!("error: {e}");
                    break;
                }
            }
        }
    }
}
