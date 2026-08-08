//! Head-to-head: nexus-web vs tungstenite WebSocket frame parsing.
//!
//! Both parse the same pre-built wire frames. Measures cycles per message.
//!
//! Usage:
//!   cargo run --release -p nexus-web --example perf_vs_tungstenite

use std::hint::black_box;
use std::io::Cursor;

// ============================================================================
// Timing
// ============================================================================

#[inline(always)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsic; this example targets x86_64 only.
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsic; this example targets x86_64 only.
    unsafe {
        let mut aux = 0u32;
        let tsc = std::arch::x86_64::__rdtscp(&raw mut aux);
        std::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_row(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {:<50} {:>6} {:>6} {:>6} {:>7} {:>7}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

fn print_header() {
    println!(
        "  {:<50} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );
}

fn section(name: &str) {
    println!("\n  --- {name} ---");
}

const SAMPLES: usize = 100_000;
const BATCH: u64 = 16;

// ============================================================================
// Frame construction
// ============================================================================

fn make_frame(fin: bool, opcode: u8, payload: &[u8]) -> Vec<u8> {
    let mut frame = Vec::new();
    let byte0 = if fin { 0x80 } else { 0x00 } | opcode;
    frame.push(byte0);
    if payload.len() <= 125 {
        frame.push(payload.len() as u8);
    } else if payload.len() <= 65535 {
        frame.push(126);
        frame.extend_from_slice(&(payload.len() as u16).to_be_bytes());
    } else {
        frame.push(127);
        frame.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    }
    frame.extend_from_slice(payload);
    frame
}

// ============================================================================
// nexus-web benchmark
// ============================================================================

fn bench_nexus(label: &str, frame: &[u8], n_frames: usize) {
    use nexus_web::ws::{FrameReader, Role};

    // Build a buffer with n_frames copies
    let mut wire = Vec::new();
    for _ in 0..n_frames {
        wire.extend_from_slice(frame);
    }

    let mut samples = vec![0u64; SAMPLES];
    let buf_size = wire.len() * BATCH as usize + 4096;

    let total = BATCH as usize * n_frames;

    for s in &mut samples {
        let mut reader = FrameReader::builder()
            .role(Role::Client)
            .buffer_capacity(buf_size)
            .max_message_size(buf_size)
            .build();

        // Time read + parse together (fair comparison — tungstenite
        // does its read inside ws.read())
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            reader.read(&wire).unwrap();
            for _ in 0..n_frames {
                let msg = reader.next().unwrap().unwrap();
                black_box(&msg);
            }
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / total as u64;
    }

    print_row(&format!("nexus-web  {label}"), &mut samples);
}

// ============================================================================
// tungstenite benchmark
// ============================================================================

/// A Read+Write wrapper: reads from a buffer, writes to a sink.
struct ReadWriteCursor {
    read: Cursor<Vec<u8>>,
}

impl std::io::Read for ReadWriteCursor {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.read.read(buf)
    }
}

impl std::io::Write for ReadWriteCursor {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(buf.len()) // sink
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn bench_tungstenite(label: &str, frame: &[u8], n_frames: usize) {
    use tungstenite::protocol::Role;

    // Build wire data: BATCH * n_frames copies
    let mut wire = Vec::new();
    for _ in 0..BATCH as usize * n_frames {
        wire.extend_from_slice(frame);
    }

    let mut config = tungstenite::protocol::WebSocketConfig::default();
    config.max_frame_size = Some(16 * 1024 * 1024);
    config.max_message_size = Some(16 * 1024 * 1024);

    let mut samples = vec![0u64; SAMPLES];
    let total = BATCH as usize * n_frames;

    for s in &mut samples {
        // Setup outside timing: construct WebSocket with all data preloaded
        let cursor = ReadWriteCursor {
            read: Cursor::new(wire.clone()),
        };
        let mut ws =
            tungstenite::protocol::WebSocket::from_raw_socket(cursor, Role::Client, Some(config));

        // Time only the parsing
        let t0 = rdtsc_start();
        for _ in 0..total {
            match ws.read() {
                Ok(msg) => {
                    black_box(&msg);
                }
                Err(_) => break,
            }
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / total as u64;
    }

    print_row(&format!("tungstenite {label}"), &mut samples);
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    println!("\n  nexus-web vs tungstenite — WebSocket frame parsing");
    println!("  CPU: rdtsc, batch={BATCH}, {SAMPLES} samples\n");
    print_header();

    for &(size, label) in &[
        (32, "text 32B"),
        (128, "text 128B"),
        (512, "text 512B"),
        (2048, "text 2048B"),
    ] {
        section(label);
        let payload = vec![b'x'; size];
        let frame = make_frame(true, 0x1, &payload);
        bench_nexus(label, &frame, 1);
        bench_tungstenite(label, &frame, 1);
    }

    for &(size, label) in &[(128, "binary 128B"), (1024, "binary 1024B")] {
        section(label);
        let payload = vec![0x42u8; size];
        let frame = make_frame(true, 0x2, &payload);
        bench_nexus(label, &frame, 1);
        bench_tungstenite(label, &frame, 1);
    }

    // Throughput: many messages in one batch
    section("throughput 100x 128B binary");
    {
        let payload = vec![0x42u8; 128];
        let frame = make_frame(true, 0x2, &payload);
        bench_nexus("100x 128B binary", &frame, 100);
        bench_tungstenite("100x 128B binary", &frame, 100);
    }

    // ================================================================
    // Write path
    // ================================================================

    println!("\n\n  === WRITE PATH (encode) ===\n");
    print_header();

    for &(size, label) in &[
        (32, "text 32B"),
        (128, "text 128B"),
        (512, "text 512B"),
        (2048, "text 2048B"),
    ] {
        section(label);
        let payload = vec![b'x'; size];
        bench_nexus_write(label, &payload, false);
        bench_tungstenite_write(label, &payload, false);
    }

    for &(size, label) in &[(128, "binary 128B"), (1024, "binary 1024B")] {
        section(label);
        let payload = vec![0x42u8; size];
        bench_nexus_write(label, &payload, true);
        bench_tungstenite_write(label, &payload, true);
    }

    println!();
}

// ============================================================================
// Write benchmarks
// ============================================================================

fn bench_nexus_write(label: &str, payload: &[u8], binary: bool) {
    use nexus_web::ws::{FrameWriter, Role};

    let mut writer = FrameWriter::new(Role::Client, payload.len() + 14); // Client = masked (harder case)
    let mut dst = vec![0u8; writer.max_encoded_len(payload.len())];
    let mut samples = vec![0u64; SAMPLES];

    for s in &mut samples {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            let n = if binary {
                writer.encode_binary_raw(payload, &mut dst)
            } else {
                writer.encode_text_raw(payload, &mut dst)
            };
            black_box(n);
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row(&format!("nexus-web  {label} (masked)"), &mut samples);

    // Also server (unmasked) — the market data relay path
    let mut writer = FrameWriter::new(Role::Server, payload.len() + 14);
    let mut dst = vec![0u8; writer.max_encoded_len(payload.len())];

    for s in &mut samples {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            let n = if binary {
                writer.encode_binary_raw(payload, &mut dst)
            } else {
                writer.encode_text_raw(payload, &mut dst)
            };
            black_box(n);
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row(&format!("nexus-web  {label} (unmasked)"), &mut samples);
}

fn bench_tungstenite_write(label: &str, payload: &[u8], binary: bool) {
    use tungstenite::Message;
    use tungstenite::protocol::Role;

    // tungstenite needs a Read+Write socket. We only care about write.
    // Use a Vec-backed sink.
    let mut samples = vec![0u64; SAMPLES];

    let msg = if binary {
        Message::Binary(payload.to_vec().into())
    } else {
        Message::Text(String::from_utf8(payload.to_vec()).unwrap().into())
    };

    for s in &mut samples {
        let sink = ReadWriteCursor {
            read: Cursor::new(Vec::new()),
        };
        let mut ws = tungstenite::protocol::WebSocket::from_raw_socket(
            sink,
            Role::Client, // Client = masked
            None,
        );

        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            // tungstenite write() takes ownership, need to clone
            let _ = ws.write(msg.clone());
            let _ = ws.flush();
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row(&format!("tungstenite {label} (masked)"), &mut samples);
}
