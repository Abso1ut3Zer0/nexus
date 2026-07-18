use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

use nexus_fix_codec::reader::FieldReader;

const MAGIC: u32 = u32::from_le_bytes(*b"NXLG");
const FRAME_HDR: usize = 8;
const ALIGN: usize = 8;
// Each stored frame's payload is [ts:8 LE UNIX-nanos][FIX wire message].
const TS_LEN: usize = 8;

struct SessionMeta {
    // Conductor-level session id as stored in the manifest.
    conductor_id: u32,
    segment_size: usize,
    epoch: u64,
}

impl SessionMeta {
    fn fix_session_id(&self) -> u32 {
        self.conductor_id / 2
    }

    fn is_outbound(&self) -> bool {
        self.conductor_id.is_multiple_of(2)
    }
}

fn read_manifest(path: &Path) -> Option<SessionMeta> {
    let data = fs::read(path).ok()?;
    if data.len() < 96 {
        return None;
    }
    let magic = u32::from_le_bytes(data[80..84].try_into().ok()?);
    if magic != MAGIC {
        return None;
    }
    let segment_size = u64::from_le_bytes(data[64..72].try_into().ok()?) as usize;
    let epoch = u64::from_le_bytes(data[72..80].try_into().ok()?);
    let conductor_id = u32::from_le_bytes(data[84..88].try_into().ok()?);
    Some(SessionMeta {
        conductor_id,
        segment_size,
        epoch,
    })
}

fn align_up(n: usize) -> usize {
    (n + ALIGN - 1) & !(ALIGN - 1)
}

fn scan_segment(path: &Path, global_base: u64, meta: &SessionMeta) {
    let Ok(data) = fs::read(path) else { return };
    let mut pos = 0usize;
    while pos + FRAME_HDR <= data.len() {
        let commit_len = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
        if commit_len == 0 {
            break;
        }
        let body = (commit_len - 1) as usize;
        let payload_start = pos + FRAME_HDR;
        let payload_end = payload_start + body;
        if payload_end > data.len() {
            break;
        }
        let payload = &data[payload_start..payload_end];
        let global_off = global_base + pos as u64;
        if payload.len() > TS_LEN {
            let ts = u64::from_le_bytes(payload[..TS_LEN].try_into().unwrap());
            let fix_msg = &payload[TS_LEN..];
            print_message(meta, global_off, ts, fix_msg);
        }
        pos = payload_start + align_up(body);
    }
}

fn scan_session(session_dir: &Path, meta: &SessionMeta) {
    let epoch = meta.epoch;
    let seg_size = meta.segment_size as u64;

    if epoch == 0 {
        scan_segment(&session_dir.join("seg0.dat"), 0, meta);
    } else {
        let prev_slot = (epoch - 1) % 3;
        scan_segment(
            &session_dir.join(format!("seg{prev_slot}.dat")),
            (epoch - 1) * seg_size,
            meta,
        );
        let cur_slot = epoch % 3;
        scan_segment(
            &session_dir.join(format!("seg{cur_slot}.dat")),
            epoch * seg_size,
            meta,
        );
    }
}

fn fmt_ts(nanos: u64) -> String {
    let secs = nanos / 1_000_000_000;
    let ns = nanos % 1_000_000_000;
    format!("{secs}.{ns:09}")
}

fn print_message(meta: &SessionMeta, offset: u64, ts: u64, fix_msg: &[u8]) {
    let dir = if meta.is_outbound() { "out" } else { "in " };
    let prefix = format!("[session={} {dir} +{offset}]", meta.fix_session_id());
    print!("{prefix:<32} {} |", fmt_ts(ts));
    for field in FieldReader::new(fix_msg, 0) {
        let val = field.value.slice(fix_msg);
        let val_str = std::str::from_utf8(val).unwrap_or("?");
        print!(" {}={} |", field.tag, val_str);
    }
    println!();
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let mut journal_dir: Option<PathBuf> = None;
    let mut filter_session: Option<u32> = None;
    let mut i = 1;

    while i < args.len() {
        match args[i].as_str() {
            "--session-id" => {
                i += 1;
                filter_session = args.get(i).and_then(|s| s.parse().ok());
            }
            arg if !arg.starts_with('-') => {
                journal_dir = Some(PathBuf::from(arg));
            }
            other => {
                eprintln!("unknown flag: {other}");
                process::exit(1);
            }
        }
        i += 1;
    }

    let Some(dir) = journal_dir else {
        eprintln!("usage: nexus-fix-log <journal-dir> [--session-id <N>]");
        process::exit(1);
    };

    let entries = match fs::read_dir(&dir) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("cannot read {}: {e}", dir.display());
            process::exit(1);
        }
    };

    let mut sessions: Vec<(PathBuf, SessionMeta)> = entries
        .flatten()
        .filter_map(|entry| {
            let path = entry.path();
            if !path.is_dir() {
                return None;
            }
            let manifest = path.join("journal.manifest");
            if !manifest.exists() {
                return None;
            }
            let meta = read_manifest(&manifest)?;
            if filter_session.is_some_and(|id| id != meta.fix_session_id()) {
                return None;
            }
            Some((path, meta))
        })
        .collect();

    // Sort by conductor_id so outbound (even) and inbound (odd) of the same
    // FIX session appear together and in chronological order.
    sessions.sort_by_key(|(_, m)| m.conductor_id);

    if sessions.is_empty() {
        eprintln!("no sessions found in {}", dir.display());
        process::exit(1);
    }

    for (path, meta) in &sessions {
        eprintln!(
            "# session {} ({})",
            meta.fix_session_id(),
            if meta.is_outbound() {
                "outbound"
            } else {
                "inbound"
            }
        );
        scan_session(path, meta);
    }
}
