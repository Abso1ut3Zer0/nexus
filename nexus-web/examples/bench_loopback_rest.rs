//! REST loopback benchmark: real TCP, real syscalls.
//!
//! Spawns a local HTTP server that echoes a canned response,
//! then measures full round-trip latency and throughput over
//! a real TCP connection.
//!
//! Usage:
//!   cargo run --release -p nexus-web --example bench_loopback_rest

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::time::Instant;

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
        "  {:<45} {:>7} {:>7} {:>7} {:>8} {:>8}",
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
        "  {:<45} {:>7} {:>7} {:>7} {:>8} {:>8}",
        "(cycles)", "p50", "p90", "p99", "p99.9", "max"
    );
}

// ============================================================================
// Server: minimal HTTP responder
// ============================================================================

const RESPONSE_BODY: &[u8] = b"{\"orderId\":12345,\"status\":\"FILLED\"}";

#[allow(clippy::needless_pass_by_value)] // moved into thread
fn server_thread(listener: TcpListener) {
    let (mut tcp, _) = listener.accept().unwrap();
    tcp.set_nodelay(true).unwrap();

    let response = format!(
        "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nX-RateLimit-Remaining: 1200\r\n\r\n{}",
        RESPONSE_BODY.len(),
        std::str::from_utf8(RESPONSE_BODY).unwrap(),
    );
    let resp_bytes = response.as_bytes();

    let mut buf = [0u8; 4096];
    loop {
        // Read until we see \r\n\r\n (end of request)
        let n = match tcp.read(&mut buf) {
            Ok(0) | Err(_) => break,
            Ok(n) => n,
        };

        // Simple: assume full request arrived in one read.
        // For a benchmark this is fine — Nagle is off, requests are small.
        let _ = n;

        // Send response
        if tcp.write_all(resp_bytes).is_err() {
            break;
        }
    }
}

// ============================================================================
// nexus-web benchmark
// ============================================================================

fn bench_nexus(addr: std::net::SocketAddr) {
    use nexus_web::http::ResponseReader;
    use nexus_web::rest::{Client, RequestWriter};

    const WARMUP: usize = 5_000;
    const SAMPLES: usize = 100_000;

    let tcp = TcpStream::connect(addr).unwrap();
    tcp.set_nodelay(true).unwrap();

    let mut writer = RequestWriter::new(&addr.to_string()).unwrap();
    writer
        .default_header(
            "X-MBX-APIKEY",
            "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
        )
        .unwrap();
    writer
        .default_header("Content-Type", "application/json")
        .unwrap();
    let mut reader = ResponseReader::new(4096).max_body_size(32 * 1024);
    let mut conn = Client::new(tcp);

    let order_body = br#"{"symbol":"BTCUSDT","side":"BUY","type":"LIMIT","quantity":"0.001","price":"67234.50"}"#;
    let timestamp = "1700000000000";
    let signature = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";

    // Warmup
    for _ in 0..WARMUP {
        let req = writer
            .post("/api/v3/order")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body(order_body)
            .finish()
            .unwrap();
        let resp = conn.send(req, &mut reader).unwrap();
        std::hint::black_box(resp.status());
    }

    // Latency samples
    let mut samples = vec![0u64; SAMPLES];
    for s in &mut samples {
        let t0 = rdtsc_start();
        let req = writer
            .post("/api/v3/order")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body(order_body)
            .finish()
            .unwrap();
        let resp = conn.send(req, &mut reader).unwrap();
        std::hint::black_box(resp.status());
        let t1 = rdtsc_end();
        *s = t1 - t0;
    }

    print_row("nexus-web  loopback (full round-trip)", &mut samples);

    // Throughput
    let iterations = 200_000u64;
    let start = Instant::now();
    for _ in 0..iterations {
        let req = writer
            .post("/api/v3/order")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body(order_body)
            .finish()
            .unwrap();
        let resp = conn.send(req, &mut reader).unwrap();
        std::hint::black_box(resp.status());
    }
    let elapsed = start.elapsed();
    let rps = iterations as f64 / elapsed.as_secs_f64();
    println!(
        "  {:<45} {:>7.0} req/sec  ({:.2?} for {iterations} reqs)",
        "nexus-web  throughput", rps, elapsed,
    );
}

// ============================================================================
// reqwest benchmark (blocking, real TCP)
// ============================================================================

fn bench_reqwest(addr: std::net::SocketAddr) {
    const WARMUP: usize = 1_000;
    const SAMPLES: usize = 50_000;

    let client = reqwest::blocking::ClientBuilder::new()
        .no_proxy()
        .tcp_nodelay(true)
        .pool_max_idle_per_host(1)
        .build()
        .unwrap();

    let url = format!("http://{addr}/api/v3/order");
    let order_body =
        r#"{"symbol":"BTCUSDT","side":"BUY","type":"LIMIT","quantity":"0.001","price":"67234.50"}"#;
    let timestamp = "1700000000000";
    let signature = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";

    // Warmup
    for _ in 0..WARMUP {
        let resp = client
            .post(&url)
            .header(
                "X-MBX-APIKEY",
                "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
            )
            .header("Content-Type", "application/json")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body(order_body)
            .send()
            .unwrap();
        std::hint::black_box(resp.status());
    }

    // Latency samples
    let mut samples = vec![0u64; SAMPLES];
    for s in &mut samples {
        let t0 = rdtsc_start();
        let resp = client
            .post(&url)
            .header(
                "X-MBX-APIKEY",
                "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
            )
            .header("Content-Type", "application/json")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body(order_body)
            .send()
            .unwrap();
        std::hint::black_box(resp.status());
        let t1 = rdtsc_end();
        *s = t1 - t0;
    }

    print_row("reqwest    loopback (full round-trip)", &mut samples);

    // Throughput
    let iterations = 50_000u64;
    let start = Instant::now();
    for _ in 0..iterations {
        let resp = client
            .post(&url)
            .header(
                "X-MBX-APIKEY",
                "abcdef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
            )
            .header("Content-Type", "application/json")
            .header("X-MBX-TIMESTAMP", timestamp)
            .header("X-MBX-SIGNATURE", signature)
            .body(order_body)
            .send()
            .unwrap();
        std::hint::black_box(resp.status());
    }
    let elapsed = start.elapsed();
    let rps = iterations as f64 / elapsed.as_secs_f64();
    println!(
        "  {:<45} {:>7.0} req/sec  ({:.2?} for {iterations} reqs)",
        "reqwest    throughput", rps, elapsed,
    );
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    println!("\n  REST loopback benchmark: real TCP, localhost");
    println!("  POST + 4 headers + JSON body → 200 OK + JSON response");
    println!("  Nagle disabled on both sides\n");
    print_header();
    println!();

    // Start server for nexus-web
    let listener1 = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr1 = listener1.local_addr().unwrap();
    let server1 = std::thread::spawn(move || server_thread(listener1));

    bench_nexus(addr1);
    drop(server1);

    // Start server for reqwest
    let listener2 = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr2 = listener2.local_addr().unwrap();
    let server2 = std::thread::spawn(move || server_thread(listener2));

    bench_reqwest(addr2);
    drop(server2);

    println!();
}
