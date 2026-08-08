//! Cycles-per-operation benchmark for nexus-net buffer primitives.
//!
//! Batches 64 operations per measurement to amortize rdtsc overhead (~20 cycles).
//!
//! Usage:
//!   cargo build --release -p nexus-net --example perf_buf
//!   taskset -c 0 ./target/release/examples/perf_buf

use nexus_net::buf::{ReadBuf, WriteBuf};
use std::hint::black_box;

// ============================================================================
// Timing
// ============================================================================

#[inline(always)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
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
        "  {:<40} {:>6} {:>6} {:>6} {:>7} {:>7}",
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
        "  {:<40} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );
}

fn section(name: &str) {
    println!("\n  --- {name} ---");
}

const SAMPLES: usize = 100_000;
const WARMUP: usize = 10_000;
const BATCH: u64 = 64;

#[allow(dead_code)]
#[inline(always)]
fn next_val(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

// ============================================================================
// ReadBuf benchmarks
// ============================================================================

fn bench_readbuf_spare_filled_advance(samples: &mut [u64]) {
    // Hot path: spare() → filled() → data() → advance()
    // One full cycle simulating a socket read + parse + consume.
    let mut buf = ReadBuf::with_capacity(65_536);
    let payload = [0x42u8; 128];

    // Warmup
    for _ in 0..WARMUP {
        buf.spare()[..128].copy_from_slice(&payload);
        buf.filled(128);
        black_box(buf.data());
        buf.advance(128);
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            buf.spare()[..128].copy_from_slice(black_box(&payload));
            buf.filled(128);
            black_box(buf.data());
            buf.advance(128);
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_readbuf_data_only(samples: &mut [u64]) {
    // Pure read: data() call only (no write/advance).
    // Measures the cost of the slice construction.
    let mut buf = ReadBuf::with_capacity(65_536);
    buf.spare()[..4096].copy_from_slice(&[0u8; 4096]);
    buf.filled(4096);

    for _ in 0..WARMUP {
        black_box(buf.data());
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            black_box(buf.data());
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_readbuf_advance_auto_reset(samples: &mut [u64]) {
    // Advance that triggers auto-reset (head == tail → reset to pre_padding).
    let mut buf = ReadBuf::with_capacity(65_536);
    let payload = [0x42u8; 128];

    for _ in 0..WARMUP {
        buf.spare()[..128].copy_from_slice(&payload);
        buf.filled(128);
        buf.advance(128); // triggers auto-reset
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            buf.spare()[..128].copy_from_slice(black_box(&payload));
            buf.filled(128);
            buf.advance(128);
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_readbuf_partial_advance(samples: &mut [u64]) {
    // Partial advance (doesn't trigger reset — simulates multi-frame parsing).
    let mut buf = ReadBuf::with_capacity(65_536);

    for _ in 0..WARMUP {
        buf.clear();
        buf.spare()[..1024].copy_from_slice(&[0u8; 1024]);
        buf.filled(1024);
        for _ in 0..8 {
            buf.advance(128);
        }
    }

    for s in samples.iter_mut() {
        buf.clear();
        buf.spare()[..1024].copy_from_slice(&[0u8; 1024]);
        buf.filled(1024);
        let start = rdtsc_start();
        for _ in 0..BATCH {
            buf.advance(black_box(16));
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_readbuf_data_mut_xor(samples: &mut [u64]) {
    // In-place XOR mask (simulates WS unmasking on data_mut()).
    let mut buf = ReadBuf::new(65_536, 0, 4); // 4 post-padding for mask overrun
    buf.spare()[..128].copy_from_slice(&[0x42; 128]);
    buf.filled(128);
    let mask = [0xDE, 0xAD, 0xBE, 0xEF];

    for _ in 0..WARMUP {
        let data = buf.data_mut();
        for (i, b) in data.iter_mut().enumerate() {
            *b ^= mask[i % 4];
        }
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let data = buf.data_mut();
            for (i, b) in data.iter_mut().enumerate() {
                *b ^= black_box(mask[i % 4]);
            }
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_readbuf_pre_padding_mut(samples: &mut [u64]) {
    // Access pre-padding region for header reassembly.
    let mut buf = ReadBuf::new(65_536, 16, 4);
    buf.spare()[..128].copy_from_slice(&[0; 128]);
    buf.filled(128);

    for _ in 0..WARMUP {
        let padding = buf.pre_padding_mut();
        black_box(&padding[12..16]);
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let padding = buf.pre_padding_mut();
            black_box(&mut padding[12..16]);
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// WriteBuf benchmarks
// ============================================================================

fn bench_writebuf_append_prepend(samples: &mut [u64]) {
    // Full write cycle: append payload → prepend header → data() → clear()
    let mut buf = WriteBuf::new(4096, 14);
    let payload = [0x42u8; 128];
    let header = [0x81, 0x7E, 0x00, 0x80]; // 4-byte WS header

    for _ in 0..WARMUP {
        buf.clear();
        buf.append(&payload);
        buf.prepend(&header);
        black_box(buf.data());
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            buf.clear();
            buf.append(black_box(&payload));
            buf.prepend(black_box(&header));
            black_box(buf.data());
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_writebuf_data_only(samples: &mut [u64]) {
    // Pure data() call — slice construction cost.
    let mut buf = WriteBuf::new(4096, 14);
    buf.append(&[0u8; 128]);

    for _ in 0..WARMUP {
        black_box(buf.data());
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            black_box(buf.data());
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_writebuf_partial_advance(samples: &mut [u64]) {
    // Simulate partial socket write: data() → advance(n) → data() → advance(rest)
    let mut buf = WriteBuf::new(4096, 14);

    for _ in 0..WARMUP {
        buf.clear();
        buf.append(&[0u8; 256]);
        buf.advance(128);
        buf.advance(128);
    }

    for s in samples.iter_mut() {
        buf.clear();
        buf.append(&[0u8; 256]);
        let start = rdtsc_start();
        for _ in 0..BATCH {
            buf.advance(black_box(4));
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_writebuf_large_payload(samples: &mut [u64]) {
    // Large payload append + small header prepend.
    // Measures copy throughput via append().
    let mut buf = WriteBuf::new(65_536, 14);
    let payload = vec![0x42u8; 4096];
    let header = [0x82, 0x7F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00]; // 10-byte header

    for _ in 0..WARMUP {
        buf.clear();
        buf.append(&payload);
        buf.prepend(&header);
        black_box(buf.data());
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            buf.clear();
            buf.append(black_box(&payload));
            buf.prepend(black_box(&header));
            black_box(buf.data());
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    println!(
        "\n  nexus-net buffer performance (rdtsc, batch={})\n",
        BATCH
    );
    print_header();

    let mut buf = vec![0u64; SAMPLES];

    section("ReadBuf — hot path");
    bench_readbuf_spare_filled_advance(&mut buf);
    print_row("spare+filled+data+advance (128B)", &mut buf);

    bench_readbuf_data_only(&mut buf);
    print_row("data() only (4KB buffered)", &mut buf);

    bench_readbuf_advance_auto_reset(&mut buf);
    print_row("advance auto-reset (128B drain)", &mut buf);

    bench_readbuf_partial_advance(&mut buf);
    print_row("advance partial (16B, no reset)", &mut buf);

    bench_readbuf_data_mut_xor(&mut buf);
    print_row("data_mut() XOR mask 128B", &mut buf);

    bench_readbuf_pre_padding_mut(&mut buf);
    print_row("pre_padding_mut() access", &mut buf);

    section("WriteBuf — hot path");
    bench_writebuf_append_prepend(&mut buf);
    print_row("clear+append+prepend+data (128B)", &mut buf);

    bench_writebuf_data_only(&mut buf);
    print_row("data() only", &mut buf);

    bench_writebuf_partial_advance(&mut buf);
    print_row("advance partial (4B)", &mut buf);

    bench_writebuf_large_payload(&mut buf);
    print_row("clear+append+prepend+data (4KB)", &mut buf);
}
