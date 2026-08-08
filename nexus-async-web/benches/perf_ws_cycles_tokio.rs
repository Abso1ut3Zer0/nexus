//! Cycle-level WebSocket benchmark — tokio backend.
//!
//! Pure userspace: no runtime, no scheduler, no kernel.
//! Fenced rdtsc, noop-waker executor, memory-backed mock.
//!
//! Run with:
//!   cargo build --release -p nexus-async-web --example perf_ws_cycles_tokio
//!   taskset -c 0 ./target/release/examples/perf_ws_cycles_tokio

use std::hint::black_box;
use std::io;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use nexus_async_web::AsyncReadAdapter;
use nexus_async_web::ws::{WsReader, WsWriter};
use nexus_web::ws::{FrameReader, FrameWriter, Role};
use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};

// =============================================================================
// Timing
// =============================================================================

#[inline(always)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe {
        let tsc = core::arch::x86_64::__rdtscp(&mut 0u32 as *mut _);
        core::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_header() {
    println!(
        "  {:<45} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "operation", "p50", "p90", "p99", "p99.9", "max"
    );
    println!("  {}", "-".repeat(83));
}

fn print_row(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {:<45} {:>6} {:>6} {:>6} {:>7} {:>7}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
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
    // SAFETY: VTABLE is valid (clone/wake/wake_by_ref/drop are all correct noop
    // implementations), and the null data pointer is valid because all vtable
    // functions ignore it.
    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
}

/// Single-poll executor. Mock stream is always Ready — if this panics,
/// the future has a real await point we didn't expect.
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
// Mock stream (tokio traits)
// =============================================================================

/// Simulates TCP segment delivery. Returns at most one MSS per read,
/// wraps around the wire buffer to stay cache-hot (steady-state behavior).
struct MockStream<'a> {
    data: &'a [u8],
    pos: usize,
    /// Bytes remaining before EOF. Separate from pos to allow wrap-around.
    remaining: usize,
}

/// Typical TCP maximum segment size.
const TCP_MSS: usize = 1460;

impl<'a> MockStream<'a> {
    fn new(data: &'a [u8], total_bytes: usize) -> Self {
        Self {
            data,
            pos: 0,
            remaining: total_bytes,
        }
    }
}

impl AsyncRead for MockStream<'_> {
    fn poll_read(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        if self.remaining == 0 {
            return Poll::Ready(Ok(())); // EOF
        }
        let avail = (self.data.len() - self.pos).min(self.remaining);
        let n = avail.min(buf.remaining()).min(TCP_MSS);
        buf.put_slice(&self.data[self.pos..self.pos + n]);
        self.pos += n;
        self.remaining -= n;
        // Wrap around to stay cache-hot
        if self.pos >= self.data.len() {
            self.pos = 0;
        }
        Poll::Ready(Ok(()))
    }
}

impl AsyncWrite for MockStream<'_> {
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
// Frame construction
// =============================================================================

fn make_frame(payload: &[u8], opcode: u8) -> Vec<u8> {
    let mut frame = Vec::new();
    frame.push(0x80 | opcode);
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

/// Build a small wire chunk (~16KB) of repeated frames. The mock wraps
/// around this buffer, keeping it L1-hot — simulates steady-state where
/// kernel socket buffers are always warm.
fn build_wire_chunk(payload_size: usize) -> Vec<u8> {
    let payload = vec![0x42u8; payload_size];
    let frame = make_frame(&payload, 0x2); // binary
    // ~16KB chunk — fits comfortably in L1D (32KB)
    let frames_per_chunk = (16 * 1024 / frame.len()).max(1);
    let mut wire = Vec::with_capacity(frame.len() * frames_per_chunk);
    for _ in 0..frames_per_chunk {
        wire.extend_from_slice(&frame);
    }
    wire
}

/// Total wire bytes needed for `count` messages at given payload size.
fn wire_bytes(payload_size: usize, count: usize) -> usize {
    let frame_len = payload_size + if payload_size <= 125 { 2 } else { 4 };
    frame_len * count
}

fn make_parts(
    wire: &[u8],
    total_bytes: usize,
) -> (WsReader, WsWriter, AsyncReadAdapter<MockStream<'_>>) {
    let mock = AsyncReadAdapter::new(MockStream::new(wire, total_bytes));
    let reader = FrameReader::builder()
        .role(Role::Client)
        .buffer_capacity(256 * 1024)
        .build();
    (
        WsReader::from_raw_parts(reader, usize::MAX),
        WsWriter::from_raw_parts(FrameWriter::new(Role::Client, 65_536)),
        mock,
    )
}

// =============================================================================
// Constants
// =============================================================================

const WARMUP: usize = 5_000;
const SAMPLES: usize = 50_000;
const BATCH: u64 = 64;
const BATCH_WARMUP: usize = 500;
const BATCH_SAMPLES: usize = 10_000;

// =============================================================================
// recv benchmarks
// =============================================================================

fn bench_recv_per_msg(label: &str, payload_size: usize) {
    let total = WARMUP + SAMPLES;
    let wire = build_wire_chunk(payload_size);
    let total_bytes = wire_bytes(payload_size, total);
    let (mut reader, _writer, mut conn) = make_parts(&wire, total_bytes);
    let mut samples = Vec::with_capacity(SAMPLES);

    for i in 0..total {
        let start = rdtsc_start();
        block_on(async {
            let msg = reader.recv(&mut conn).await.unwrap();
            black_box(&msg);
        });
        let end = rdtsc_end();
        if i >= WARMUP {
            samples.push(end - start);
        }
    }

    print_row(label, &mut samples);
}

fn bench_recv_batched(label: &str, payload_size: usize) {
    let total_batches = BATCH_WARMUP + BATCH_SAMPLES;
    let total_msgs = total_batches * BATCH as usize;
    let wire = build_wire_chunk(payload_size);
    let total_bytes = wire_bytes(payload_size, total_msgs);
    let (mut reader, _writer, mut conn) = make_parts(&wire, total_bytes);
    let mut samples = Vec::with_capacity(BATCH_SAMPLES);

    for i in 0..total_batches {
        let start = rdtsc_start();
        block_on(async {
            for _ in 0..BATCH {
                let msg = reader.recv(&mut conn).await.unwrap();
                black_box(&msg);
            }
        });
        let end = rdtsc_end();
        if i >= BATCH_WARMUP {
            samples.push((end - start) / BATCH);
        }
    }

    print_row(label, &mut samples);
}

// =============================================================================
// send benchmarks
// =============================================================================

fn bench_send_per_msg(label: &str, payload_size: usize) {
    let text = "x".repeat(payload_size);
    let wire = build_wire_chunk(payload_size);
    let (_reader, mut writer, mut conn) = make_parts(&wire, 0);
    let mut samples = Vec::with_capacity(SAMPLES);
    let total = WARMUP + SAMPLES;

    for i in 0..total {
        let start = rdtsc_start();
        block_on(writer.send_text(&mut conn, &text)).unwrap();
        let end = rdtsc_end();
        if i >= WARMUP {
            samples.push(end - start);
        }
    }

    print_row(label, &mut samples);
}

fn bench_send_batched(label: &str, payload_size: usize) {
    let text = "x".repeat(payload_size);
    let wire = build_wire_chunk(payload_size);
    let (_reader, mut writer, mut conn) = make_parts(&wire, 0);
    let mut samples = Vec::with_capacity(BATCH_SAMPLES);
    let total_batches = BATCH_WARMUP + BATCH_SAMPLES;

    for i in 0..total_batches {
        let start = rdtsc_start();
        block_on(async {
            for _ in 0..BATCH {
                writer.send_text(&mut conn, &text).await.unwrap();
            }
        });
        let end = rdtsc_end();
        if i >= BATCH_WARMUP {
            samples.push((end - start) / BATCH);
        }
    }

    print_row(label, &mut samples);
}

// =============================================================================
// main
// =============================================================================

fn main() {
    println!("\n  === WebSocket Cycle Benchmark (tokio backend) ===");
    println!("  Pure userspace, noop waker, memory-backed mock");
    println!("  Per-message: {} warmup + {} samples", WARMUP, SAMPLES);
    println!(
        "  Batched: {} warmup + {} samples x {} ops\n",
        BATCH_WARMUP, BATCH_SAMPLES, BATCH
    );

    println!("  --- recv per-message (cycles) ---");
    print_header();
    bench_recv_per_msg("recv binary 40B", 40);
    bench_recv_per_msg("recv binary 128B", 128);
    bench_recv_per_msg("recv binary 1024B", 1024);

    println!("\n  --- recv batched x64 (amortized cycles/msg) ---");
    print_header();
    bench_recv_batched("recv binary 40B (batched)", 40);
    bench_recv_batched("recv binary 128B (batched)", 128);

    println!("\n  --- send_text per-message (cycles) ---");
    print_header();
    bench_send_per_msg("send_text 40B", 40);
    bench_send_per_msg("send_text 128B", 128);
    bench_send_per_msg("send_text 1024B", 1024);

    println!("\n  --- send_text batched x64 (amortized cycles/msg) ---");
    print_header();
    bench_send_batched("send_text 40B (batched)", 40);
    bench_send_batched("send_text 128B (batched)", 128);

    println!();
}
