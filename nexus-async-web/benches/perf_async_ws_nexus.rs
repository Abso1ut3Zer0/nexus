//! Async throughput benchmark: nexus-async-web (nexus-async-rt backend).
//!
//! Mirrors perf_async_ws.rs but uses the nexus-async-rt backend.
//! Separate file because tokio-rt and nexus features are mutually exclusive.
//!
//! Usage:
//!   cargo run --release -p nexus-async-web --no-default-features --features nexus \
//!     --example perf_async_ws_nexus

use std::hint::black_box;
use std::io;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::time::{Duration, Instant};

use nexus_async_rt::{AsyncRead, AsyncWrite};
use nexus_async_web::NexusAsyncReadAdapter;

// =============================================================================
// Frame construction
// =============================================================================

fn make_text_frame(payload: &[u8]) -> Vec<u8> {
    let mut frame = Vec::new();
    frame.push(0x81); // FIN + Text
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

fn make_binary_frame(payload: &[u8]) -> Vec<u8> {
    let mut frame = Vec::new();
    frame.push(0x82); // FIN + Binary
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

fn build_binary_wire(size: usize, count: u64) -> Vec<u8> {
    let payload = vec![0x42u8; size];
    let frame = make_binary_frame(&payload);
    let mut wire = Vec::with_capacity(frame.len() * count as usize);
    for _ in 0..count {
        wire.extend_from_slice(&frame);
    }
    wire
}

fn build_text_wire(json: &str, count: u64) -> Vec<u8> {
    let frame = make_text_frame(json.as_bytes());
    let mut wire = Vec::with_capacity(frame.len() * count as usize);
    for _ in 0..count {
        wire.extend_from_slice(&frame);
    }
    wire
}

// =============================================================================
// Mock async stream (nexus-async-rt traits)
// =============================================================================

struct MockAsyncReader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl AsyncRead for MockAsyncReader<'_> {
    fn poll_read(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &mut [u8],
    ) -> Poll<io::Result<usize>> {
        let remaining = &self.data[self.pos..];
        let n = remaining.len().min(buf.len());
        buf[..n].copy_from_slice(&remaining[..n]);
        self.pos += n;
        Poll::Ready(Ok(n))
    }
}

impl AsyncWrite for MockAsyncReader<'_> {
    fn poll_write(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        Poll::Ready(Ok(buf.len()))
    }
    fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
    }
    fn poll_shutdown(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
    }
}

// =============================================================================
// Noop-waker executor
// =============================================================================

fn noop_waker() -> Waker {
    fn noop(_: *const ()) {}
    fn clone(p: *const ()) -> RawWaker {
        RawWaker::new(p, &VTABLE)
    }
    const VTABLE: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    // SAFETY: null data is valid; all vtable functions are noop and accept a null data pointer.
    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
}

fn block_on<F: std::future::Future>(f: F) -> F::Output {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut f = std::pin::pin!(f);
    match f.as_mut().poll(&mut cx) {
        Poll::Ready(v) => v,
        Poll::Pending => panic!("future returned Pending with synchronous mock"),
    }
}

// =============================================================================
// In-memory benchmarks
// =============================================================================

fn bench_inmemory(wire: &[u8], msg_count: u64) -> (Duration, u64) {
    use nexus_async_web::ws::WsReader;
    use nexus_web::ws::{FrameReader, Message, Role};

    let mut conn = NexusAsyncReadAdapter::new(MockAsyncReader { data: wire, pos: 0 });
    let mut reader = WsReader::from_raw_parts(
        FrameReader::builder()
            .role(Role::Client)
            .buffer_capacity(64 * 1024)
            .build(),
        usize::MAX,
    );

    let start = Instant::now();
    let mut received = 0u64;
    block_on(async {
        while received < msg_count {
            match reader.recv(&mut conn).await.unwrap() {
                Some(Message::Binary(d)) => {
                    black_box(&d);
                    received += 1;
                }
                Some(Message::Text(s)) => {
                    black_box(&s);
                    received += 1;
                }
                Some(_) => {}
                None => break,
            }
        }
    });
    (start.elapsed(), received)
}

// =============================================================================
// JSON payloads
// =============================================================================

fn quote_tick_json() -> String {
    r#"{"s":"BTC-USD","b":67234.50,"a":67234.75,"bs":1.5,"as":2.3,"t":1700000000000}"#.to_string()
}

fn order_update_json() -> String {
    r#"{"s":"BTC-USD","bids":[[67234.50,1.5],[67234.25,3.2],[67234.00,5.0]],"asks":[[67234.75,2.3],[67235.00,4.1],[67235.25,1.8]],"t":1700000000000,"u":42}"#.to_string()
}

fn book_snapshot_json() -> String {
    let mut bids = Vec::new();
    let mut asks = Vec::new();
    for i in 0..20 {
        bids.push(format!(
            "[{:.2},{:.1}]",
            (i as f64).mul_add(-0.25, 67234.50),
            (i as f64).mul_add(0.3, 1.0)
        ));
        asks.push(format!(
            "[{:.2},{:.1}]",
            (i as f64).mul_add(0.25, 67234.75),
            (i as f64).mul_add(0.2, 1.0)
        ));
    }
    format!(
        r#"{{"s":"BTC-USD","bids":[{}],"asks":[{}],"t":1700000000000,"u":42,"type":"snapshot"}}"#,
        bids.join(","),
        asks.join(","),
    )
}

// =============================================================================
// Blocking comparison (nexus-net sync)
// =============================================================================

fn bench_blocking(wire: &[u8], msg_count: u64) -> (Duration, u64) {
    use nexus_web::ws::{Client, FrameReader, FrameWriter, Message, Role};
    use std::io::{Cursor, Read, Write};

    struct CursorWrap<'a>(Cursor<&'a [u8]>);
    impl Read for CursorWrap<'_> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            self.0.read(buf)
        }
    }
    impl Write for CursorWrap<'_> {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            Ok(buf.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    let cursor = CursorWrap(Cursor::new(wire));
    let reader = FrameReader::builder()
        .role(Role::Client)
        .buffer_capacity(64 * 1024)
        .build();
    let mut ws = Client::from_parts(cursor, reader, FrameWriter::new(Role::Client, 65_536));

    let start = Instant::now();
    let mut received = 0u64;
    while received < msg_count {
        match ws.recv().unwrap() {
            Some(Message::Binary(d)) => {
                black_box(&d);
                received += 1;
            }
            Some(Message::Text(s)) => {
                black_box(&s);
                received += 1;
            }
            Some(_) => {}
            None => break,
        }
    }
    (start.elapsed(), received)
}

// =============================================================================
// Reporting
// =============================================================================

fn report(label: &str, elapsed: Duration, count: u64) {
    let secs = elapsed.as_secs_f64();
    let rate = count as f64 / secs;
    let ns_per = (secs * 1e9) / count as f64;
    let rate_str = if rate >= 1_000_000.0 {
        format!("{:.1}M msg/sec", rate / 1_000_000.0)
    } else {
        format!("{:.0}K msg/sec", rate / 1_000.0)
    };
    println!("  {:<45} {:>12} = {:>7.0}ns/msg", label, rate_str, ns_per);
}

fn section(name: &str) {
    println!("\n  --- {name} ---");
}

// =============================================================================
// Main
// =============================================================================

fn main() {
    let n = 1_000_000u64;

    // =================================================================
    // 1. In-memory parse (binary, recv — zero-copy)
    // =================================================================

    println!("\n  === In-Memory Parse (binary, nexus-async-rt recv — zero-copy) ===");

    for &(size, label) in &[(40, "40B"), (128, "128B"), (512, "512B")] {
        section(label);
        let wire = build_binary_wire(size, n);

        // warmup
        let _ = bench_inmemory(&wire, n);

        let (e, c) = bench_inmemory(&wire, n);
        report("nexus-async-web (nexus-rt recv)", e, c);

        let (e, c) = bench_blocking(&wire, n);
        report("nexus-net (blocking recv)", e, c);
    }

    // =================================================================
    // 2. JSON parse+deser (text frames)
    // =================================================================

    println!("\n\n  === JSON Parse + Deserialize (text frames, nexus-async-rt) ===");

    {
        let json = quote_tick_json();
        section(&format!("quote tick ({}B JSON)", json.len()));
        let wire = build_text_wire(&json, n);

        let _ = bench_inmemory(&wire, n);

        let (e, c) = bench_inmemory(&wire, n);
        report("nexus-rt (recv+deser=no)", e, c);

        let (e, c) = bench_blocking(&wire, n);
        report("blocking (recv)", e, c);
    }

    {
        let json = order_update_json();
        section(&format!("order update ({}B JSON)", json.len()));
        let wire = build_text_wire(&json, n);

        let _ = bench_inmemory(&wire, n);

        let (e, c) = bench_inmemory(&wire, n);
        report("nexus-rt (recv)", e, c);

        let (e, c) = bench_blocking(&wire, n);
        report("blocking (recv)", e, c);
    }

    {
        let json = book_snapshot_json();
        let snap_n = 500_000;
        section(&format!("book snapshot ({}B JSON)", json.len()));
        let wire = build_text_wire(&json, snap_n);

        let _ = bench_inmemory(&wire, snap_n);

        let (e, c) = bench_inmemory(&wire, snap_n);
        report("nexus-rt (recv)", e, c);

        let (e, c) = bench_blocking(&wire, snap_n);
        report("blocking (recv)", e, c);
    }

    // =================================================================
    // 3. Async vs Blocking comparison
    // =================================================================

    println!("\n\n  === Async (nexus-rt) vs Blocking — In-Memory ===");

    for &(size, label) in &[(40, "40B"), (128, "128B"), (512, "512B")] {
        section(label);
        let wire = build_binary_wire(size, n);

        let (e, c) = bench_inmemory(&wire, n);
        report("nexus-async-web (nexus-rt)", e, c);

        let (e, c) = bench_blocking(&wire, n);
        report("nexus-net (blocking)", e, c);
    }

    println!();
}
