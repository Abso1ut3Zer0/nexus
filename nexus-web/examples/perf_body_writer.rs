//! Benchmark: body(&[u8]) with serde_json::to_vec vs body_writer with serde_json::to_writer.
//!
//! Measures the REAL difference — actual JSON serialization, not just copying a static slice.
//!
//! Usage:
//!   cargo run --release -p nexus-web --example perf_body_writer

use std::hint::black_box;
use std::io::{self, Cursor, Read, Write};

use serde::Serialize;

#[derive(Serialize)]
struct Order {
    symbol: &'static str,
    side: &'static str,
    r#type: &'static str,
    time_in_force: &'static str,
    quantity: &'static str,
    price: &'static str,
}

const ORDER: Order = Order {
    symbol: "BTCUSDT",
    side: "BUY",
    r#type: "LIMIT",
    time_in_force: "GTC",
    quantity: "0.001",
    price: "67234.50",
};

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
        "  {:<55} {:>6} {:>6} {:>6} {:>7} {:>7}",
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
        "  {:<55} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles)", "p50", "p90", "p99", "p99.9", "max"
    );
}

// ============================================================================
// Mock stream
// ============================================================================

const CANNED_RESPONSE: &[u8] = b"HTTP/1.1 200 OK\r\nContent-Length: 15\r\n\r\n{\"orderId\":123}";

struct MockStream(Cursor<&'static [u8]>);

impl MockStream {
    fn new() -> Self {
        Self(Cursor::new(CANNED_RESPONSE))
    }
    fn reset(&mut self) {
        self.0.set_position(0);
    }
}

impl Read for MockStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }
}

impl Write for MockStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

const SAMPLES: usize = 100_000;
const BATCH: u64 = 16;

fn main() {
    use nexus_web::http::ResponseReader;
    use nexus_web::rest::{Client, RequestWriter};

    let mut writer = RequestWriter::new("api.binance.com").unwrap();
    writer
        .default_header("Content-Type", "application/json")
        .unwrap();
    let mut reader = ResponseReader::new(4096);
    let mut conn = Client::new(MockStream::new());

    // Reusable buffer for the to_vec path
    let mut json_buf: Vec<u8> = Vec::with_capacity(256);

    println!("\n  body_writer vs body(&[u8]) with REAL serde_json serialization");
    println!("  Struct: Order (6 fields, ~100B JSON)\n");
    print_header();
    println!();

    // --- Path 1: serde_json::to_vec + body(&[u8]) ---
    let mut samples = vec![0u64; SAMPLES];

    for _ in 0..1000 {
        conn.stream_mut().reset();
        json_buf.clear();
        serde_json::to_writer(&mut json_buf, &ORDER).unwrap();
        let req = writer.post("/order").body(&json_buf).finish().unwrap();
        let _ = conn.send(req, &mut reader);
    }

    for s in &mut samples {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            conn.stream_mut().reset();
            json_buf.clear();
            serde_json::to_writer(&mut json_buf, &ORDER).unwrap();
            let req = writer.post("/order").body(&json_buf).finish().unwrap();
            let resp = conn.send(req, &mut reader).unwrap();
            black_box(resp.status());
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row("serde → Vec → body(&[u8])  (alloc + copy)", &mut samples);

    // --- Path 2: body_writer with serde_json::to_writer ---
    let mut samples = vec![0u64; SAMPLES];

    for _ in 0..1000 {
        conn.stream_mut().reset();
        let req = writer
            .post("/order")
            .body_writer(|w| serde_json::to_writer(w, &ORDER).map_err(io::Error::other))
            .finish()
            .unwrap();
        let _ = conn.send(req, &mut reader);
    }

    for s in &mut samples {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            conn.stream_mut().reset();
            let req = writer
                .post("/order")
                .body_writer(|w| serde_json::to_writer(w, &ORDER).map_err(io::Error::other))
                .finish()
                .unwrap();
            let resp = conn.send(req, &mut reader).unwrap();
            black_box(resp.status());
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row("serde → body_writer (direct, no alloc)", &mut samples);

    // --- Path 3: pre-serialized static body for reference ---
    let static_body = serde_json::to_vec(&ORDER).unwrap();
    let mut samples = vec![0u64; SAMPLES];

    for _ in 0..1000 {
        conn.stream_mut().reset();
        let req = writer.post("/order").body(&static_body).finish().unwrap();
        let _ = conn.send(req, &mut reader);
    }

    for s in &mut samples {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            conn.stream_mut().reset();
            let req = writer.post("/order").body(&static_body).finish().unwrap();
            let resp = conn.send(req, &mut reader).unwrap();
            black_box(resp.status());
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row(
        "pre-serialized body(&[u8]) (baseline, no serde)",
        &mut samples,
    );

    // --- Path 4: manual write into body_writer (no serde overhead) ---
    let mut samples = vec![0u64; SAMPLES];

    for _ in 0..1000 {
        conn.stream_mut().reset();
        let req = writer
            .post("/order")
            .body_writer(|w| {
                use std::io::Write;
                write!(
                    w,
                    r#"{{"symbol":"BTCUSDT","side":"BUY","type":"LIMIT","timeInForce":"GTC","quantity":"0.001","price":"67234.50"}}"#
                )
            })
            .finish()
            .unwrap();
        let _ = conn.send(req, &mut reader);
    }

    for s in &mut samples {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            conn.stream_mut().reset();
            let req = writer
                .post("/order")
                .body_writer(|w| {
                    use std::io::Write;
                    write!(
                        w,
                        r#"{{"symbol":"BTCUSDT","side":"BUY","type":"LIMIT","timeInForce":"GTC","quantity":"0.001","price":"67234.50"}}"#
                    )
                })
                .finish()
                .unwrap();
            let resp = conn.send(req, &mut reader).unwrap();
            black_box(resp.status());
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row(
        "write!() → body_writer (manual format, no serde)",
        &mut samples,
    );

    println!();
    println!("  At 3GHz: 100 cycles ≈ 33ns, 1000 cycles ≈ 333ns");
    println!();
}
