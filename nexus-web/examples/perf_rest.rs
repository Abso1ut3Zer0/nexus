//! REST request construction + round-trip benchmark: nexus-web vs reqwest.
//!
//! Uses a mock stream that accepts writes (sink) and returns a canned
//! 200 OK response. Measures the full send path including WriteBuf
//! construction, write_all, and response parsing.
//!
//! Usage:
//!   cargo run --release -p nexus-web --example perf_rest

use std::hint::black_box;
use std::io::{self, Cursor, Read, Write};

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
        "(cycles)", "p50", "p90", "p99", "p99.9", "max"
    );
}

const SAMPLES: usize = 100_000;
const BATCH: u64 = 16;

// ============================================================================
// Mock stream: sink writes, canned response on read
// ============================================================================

const CANNED_RESPONSE: &[u8] = b"HTTP/1.1 200 OK\r\nContent-Length: 15\r\n\r\n{\"orderId\":123}";

struct MockRestStream {
    response: Cursor<&'static [u8]>,
}

impl MockRestStream {
    fn new() -> Self {
        Self {
            response: Cursor::new(CANNED_RESPONSE),
        }
    }

    fn reset(&mut self) {
        self.response.set_position(0);
    }
}

impl Read for MockRestStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.response.read(buf)
    }
}

impl Write for MockRestStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        Ok(buf.len()) // sink
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

// ============================================================================
// nexus-web benchmark
// ============================================================================

fn bench_nexus() {
    use nexus_web::http::ResponseReader;
    use nexus_web::rest::{Client, RequestWriter};

    let mock = MockRestStream::new();
    let mut writer = RequestWriter::new("api.binance.com").unwrap();
    writer
        .default_header(
            "X-MBX-APIKEY",
            "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
        )
        .unwrap();
    writer
        .default_header("Content-Type", "application/json")
        .unwrap();
    let mut reader = ResponseReader::new(4096);
    let mut conn = Client::new(mock);

    let order_body = r#"{"symbol":"BTCUSDT","side":"BUY","type":"LIMIT","timeInForce":"GTC","quantity":"0.001","price":"67234.50"}"#;
    let timestamp = "1700000000000";
    let signature = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";

    let mut samples = vec![0u64; SAMPLES];

    // Warmup
    for _ in 0..1000 {
        conn.stream_mut().reset();
        let req = writer
            .post("/api/v3/order")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body(order_body.as_bytes())
            .finish()
            .unwrap();
        let _ = conn.send(req, &mut reader);
    }

    // Benchmark: full send path — build request + write + read response
    for s in &mut samples {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            conn.stream_mut().reset();
            let req = writer
                .post("/api/v3/order")
                .header("X-MBX-TIMESTAMP", timestamp)
                .header("X-MBX-SIGNATURE", signature)
                .body(order_body.as_bytes())
                .finish()
                .unwrap();
            let resp = conn.send(req, &mut reader).unwrap();
            black_box(resp.status());
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row(
        "nexus-web  POST body(&[u8])  (build+write+parse)",
        &mut samples,
    );

    // body_writer variant — direct write, no intermediate copy
    let mut samples_bw = vec![0u64; SAMPLES];

    for _ in 0..1000 {
        conn.stream_mut().reset();
        let req = writer
            .post("/api/v3/order")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body_writer(|w| {
                use std::io::Write;
                w.write_all(order_body.as_bytes())
            })
            .finish()
            .unwrap();
        let _ = conn.send(req, &mut reader);
    }

    for s in &mut samples_bw {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            conn.stream_mut().reset();
            let req = writer
                .post("/api/v3/order")
                .header("X-MBX-TIMESTAMP", timestamp)
                .header("X-MBX-SIGNATURE", signature)
                .body_writer(|w| {
                    use std::io::Write;
                    w.write_all(order_body.as_bytes())
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
        "nexus-web  POST body_writer (build+write+parse)",
        &mut samples_bw,
    );
}

// ============================================================================
// reqwest benchmark
// ============================================================================

fn bench_reqwest() {
    let client = reqwest::blocking::Client::new();

    let order_body = r#"{"symbol":"BTCUSDT","side":"BUY","type":"LIMIT","timeInForce":"GTC","quantity":"0.001","price":"67234.50"}"#;
    let timestamp = "1700000000000";
    let signature = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";

    let mut samples = vec![0u64; SAMPLES];

    // Warmup
    for _ in 0..1000 {
        let _ = client
            .post("https://api.binance.com/api/v3/order")
            .header(
                "X-MBX-APIKEY",
                "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
            )
            .header("Content-Type", "application/json")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body(order_body)
            .build()
            .unwrap();
    }

    // Benchmark: just .build() — request construction only (no I/O)
    for s in &mut samples {
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            let req = client
                .post("https://api.binance.com/api/v3/order")
                .header(
                    "X-MBX-APIKEY",
                    "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
                )
                .header("Content-Type", "application/json")
                .header("X-MBX-TIMESTAMP", timestamp)
                .header("X-MBX-SIGNATURE", signature)
                .body(order_body)
                .build()
                .unwrap();
            black_box(&req);
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row("reqwest    build() only (no I/O)", &mut samples);
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    println!("\n  REST request benchmark: nexus-web vs reqwest");
    println!("  Simulates Binance order entry: POST + 4 headers + JSON body");
    println!("  nexus-web: full send() with mock stream (build + write + parse response)");
    println!("  reqwest: build() only (no I/O — just request construction)\n");
    print_header();

    println!();
    bench_nexus();
    bench_reqwest();

    println!();
    println!("  Note: nexus-web measures MORE work (write + response parse).");
    println!("  reqwest measures LESS work (build only, no write/parse).");
    println!("  At 3GHz: 100 cycles ≈ 33ns, 1000 cycles ≈ 333ns, 3000 cycles ≈ 1μs");
    println!();
}
