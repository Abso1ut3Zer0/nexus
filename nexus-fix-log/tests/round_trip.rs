use std::path::{Path, PathBuf};
use std::process::Command;

use nexus_journal::{ConductorBuilder, OpenMode};

struct TempDir(PathBuf);

impl TempDir {
    fn new(name: &str) -> Self {
        let p = std::env::temp_dir().join(format!(
            "nexus-fix-log-{}-{}",
            std::process::id(),
            name
        ));
        let _ = std::fs::remove_dir_all(&p);
        Self(p)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn fix_msg(seq: u32) -> Vec<u8> {
    format!("8=FIX.4.2\x0134={seq}\x0135=D\x0110=000\x01").into_bytes()
}

/// Write N outbound messages plus one inbound through journals sized to force one rotation.
/// The viewer must read both segments in order and surface every message.
///
/// Frame footprint: 8 (header) + 8 (ts prefix) + ~27 (fix_msg) → 43 → aligned 48.
/// Segment size 128 fits exactly 2 frames → rotation on the 3rd append (epoch → 1).
/// After 4 outbound appends: seqs 1-2 land in seg0 (epoch 0), seqs 3-4 in seg1 (epoch 1).
/// Viewer reads prev (slot 0 = seg0) and current (slot 1 = seg1) → all 4 seqnums visible.
#[test]
fn round_trip_with_rotation() {
    let dir = TempDir::new("rt");

    // 2024-01-01 00:00:00 UTC in nanoseconds — fixed timestamp for deterministic output.
    let ts_bytes = 1_704_067_200_000_000_000u64.to_le_bytes();

    const SEG_SIZE: usize = 128;

    {
        let mut c = ConductorBuilder::new(dir.path())
            .archive(true)
            .open()
            .unwrap();
        // FIX session 0: outbound = conductor session id 0, inbound = conductor session id 1.
        // Variables declared in this order drop LIFO: inb → out → c (conductor last).
        let mut out = c
            .session()
            .segment_size(SEG_SIZE)
            .session_id(0)
            .open(OpenMode::OpenOrCreate)
            .unwrap();
        let mut inb = c
            .session()
            .segment_size(SEG_SIZE)
            .session_id(1)
            .open(OpenMode::OpenOrCreate)
            .unwrap();
        for seq in 1u32..=4 {
            out.append_prefixed(&ts_bytes, &fix_msg(seq)).unwrap();
        }
        inb.append_prefixed(&ts_bytes, &fix_msg(50)).unwrap();
    }

    let result = Command::new(env!("CARGO_BIN_EXE_nexus-fix-log"))
        .arg(dir.path())
        .output()
        .expect("nexus-fix-log failed to start");

    assert!(
        result.status.success(),
        "non-zero exit: {:?}\nstderr: {}",
        result.status,
        String::from_utf8_lossy(&result.stderr),
    );

    let stdout = String::from_utf8(result.stdout).unwrap();

    for seq in 1u32..=4 {
        assert!(
            stdout.contains(&format!(" 34={seq} ")),
            "outbound seqnum {seq} missing from output:\n{stdout}",
        );
    }
    assert!(
        stdout.contains(" 34=50 "),
        "inbound seqnum 50 missing from output:\n{stdout}",
    );
    assert!(stdout.contains(" out "), "no outbound direction tag in output:\n{stdout}");
    assert!(stdout.contains(" in  "), "no inbound direction tag in output:\n{stdout}");
}
