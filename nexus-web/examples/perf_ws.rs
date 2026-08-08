//! Cycles-per-operation benchmark for nexus-web WebSocket primitives.
//!
//! Batches 64 operations per measurement to amortize rdtsc overhead (~20 cycles).
//!
//! Usage:
//!   cargo build --release -p nexus-web --example perf_ws
//!   taskset -c 0 ./target/release/examples/perf_ws

use nexus_web::ws::{FrameReader, FrameWriter, Role, apply_mask};
use std::hint::black_box;

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
        "  {:<45} {:>6} {:>6} {:>6} {:>7} {:>7}",
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
        "  {:<45} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );
}

fn section(name: &str) {
    println!("\n  --- {name} ---");
}

const SAMPLES: usize = 100_000;
const BATCH: u64 = 64;

// ============================================================================
// Frame construction helpers
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

fn make_masked_frame(fin: bool, opcode: u8, payload: &[u8], mask: [u8; 4]) -> Vec<u8> {
    let mut frame = Vec::new();
    let byte0 = if fin { 0x80 } else { 0x00 } | opcode;
    frame.push(byte0);
    let len_byte = if payload.len() <= 125 {
        payload.len() as u8
    } else {
        126
    };
    frame.push(0x80 | len_byte);
    if payload.len() > 125 {
        frame.extend_from_slice(&(payload.len() as u16).to_be_bytes());
    }
    frame.extend_from_slice(&mask);
    let mut masked = payload.to_vec();
    apply_mask(&mut masked, mask);
    frame.extend_from_slice(&masked);
    frame
}

// ============================================================================
// Benchmarks
// ============================================================================

fn bench_read_next(samples: &mut [u64], label: &str, frame: &[u8], role: Role) {
    // Batch multiple frames into one read(), drain via next() loop.
    // This is the real-world pattern: socket delivers N frames, parser drains all.
    // Cleanup happens at the start of each next() call — amortized naturally.
    let batch = 16usize;
    let mut wire = Vec::with_capacity(frame.len() * batch);
    for _ in 0..batch {
        wire.extend_from_slice(frame);
    }

    let mut reader = FrameReader::builder()
        .role(role)
        .buffer_capacity(wire.len() + 4096)
        .build();

    // Warmup
    for _ in 0..1000 {
        reader.read(&wire).unwrap();
        for _ in 0..batch {
            let msg = reader.next().unwrap().unwrap();
            black_box(&msg);
        }
        // Flush cleanup from last message
        let _ = reader.next();
    }

    for s in samples.iter_mut() {
        // Flush any pending cleanup before reading
        let _ = reader.next();
        reader.read(&wire).unwrap();
        let start = rdtsc_start();
        for _ in 0..batch {
            let msg = reader.next().unwrap().unwrap();
            black_box(&msg);
        }
        let end = rdtsc_end();
        *s = (end - start) / batch as u64;
    }
    print_row(label, samples);
}

fn bench_unmask_cycles(samples: &mut [u64], size: usize) {
    let mut data = vec![0x42u8; size];
    let mask = [0x37, 0xFA, 0x21, 0x3D];

    for _ in 0..10_000 {
        apply_mask(&mut data, mask);
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            apply_mask(&mut data, mask);
            black_box(&data);
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    print_row(&format!("apply_mask ({size}B)"), samples);
}

fn bench_utf8_cycles(samples: &mut [u64], size: usize) {
    let data = vec![b'x'; size];

    for _ in 0..10_000 {
        black_box(std::str::from_utf8(&data).unwrap());
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            black_box(std::str::from_utf8(&data).unwrap());
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    print_row(&format!("std::str::from_utf8 ({size}B)"), samples);
}

fn bench_simdutf8_cycles(samples: &mut [u64], size: usize) {
    let data = vec![b'x'; size];

    for _ in 0..10_000 {
        black_box(simdutf8::basic::from_utf8(&data).unwrap());
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            black_box(simdutf8::basic::from_utf8(&data).unwrap());
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    print_row(&format!("simdutf8::basic::from_utf8 ({size}B)"), samples);
}

fn bench_encode_cycles(samples: &mut [u64], size: usize, role: Role) {
    let mut writer = FrameWriter::new(role, size + 14);
    let payload = vec![b'x'; size];
    let mut dst = vec![0u8; writer.max_encoded_len(size)];

    for _ in 0..10_000 {
        writer.encode_text_raw(&payload, &mut dst);
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let n = writer.encode_text_raw(&payload, &mut dst);
            black_box(n);
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    let label = format!(
        "encode_text_raw ({size}B, {})",
        if role == Role::Server {
            "server"
        } else {
            "client"
        }
    );
    print_row(&label, samples);
}

fn bench_encode_into_cycles(samples: &mut [u64], size: usize) {
    let mut writer = FrameWriter::new(Role::Server, size + 14);
    let payload = vec![b'x'; size];

    for _ in 0..10_000 {
        writer.encode_text(&payload);
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            writer.encode_text(&payload);
            black_box(writer.data());
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    print_row(&format!("encode_text ({size}B, server)"), samples);
}

fn bench_throughput_cycles(samples: &mut [u64], msg_count: usize) {
    let payload = vec![0x42u8; 128];
    let frame = make_frame(true, 0x2, &payload);
    let mut wire = Vec::new();
    for _ in 0..msg_count {
        wire.extend(&frame);
    }

    let mut reader = FrameReader::builder()
        .role(Role::Client)
        .buffer_capacity(wire.len() + 4096)
        .build();

    for _ in 0..1000 {
        reader.read(&wire).unwrap();
        while reader.next().unwrap().is_some() {}
    }

    for s in samples.iter_mut() {
        let start = rdtsc_start();
        reader.read(&wire).unwrap();
        let mut count = 0;
        while reader.next().unwrap().is_some() {
            count += 1;
        }
        let end = rdtsc_end();
        assert_eq!(count, msg_count);
        *s = (end - start) / count as u64;
    }
    print_row(
        &format!("throughput ({msg_count}× 128B binary, /msg)"),
        samples,
    );
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    println!("\n  nexus-web WS performance (rdtsc, batch={})\n", BATCH);
    print_header();

    let mut buf = vec![0u64; SAMPLES];

    section("FrameReader — single frame, unmasked (client role)");
    for size in [32, 128, 512, 2048] {
        let frame = make_frame(true, 0x1, &vec![b'x'; size]);
        bench_read_next(
            &mut buf,
            &format!("text unmasked ({size}B)"),
            &frame,
            Role::Client,
        );
    }

    section("FrameReader — single frame, binary unmasked");
    for size in [128, 1024] {
        let frame = make_frame(true, 0x2, &vec![0x42; size]);
        bench_read_next(
            &mut buf,
            &format!("binary unmasked ({size}B)"),
            &frame,
            Role::Client,
        );
    }

    section("FrameReader — single frame, masked (server role)");
    let mask = [0x37, 0xFA, 0x21, 0x3D];
    for size in [128, 512, 2048] {
        let frame = make_masked_frame(true, 0x1, &vec![b'x'; size], mask);
        bench_read_next(
            &mut buf,
            &format!("text masked ({size}B)"),
            &frame,
            Role::Server,
        );
    }

    section("Components — apply_mask");
    for size in [64, 128, 256, 512, 1024, 4096] {
        bench_unmask_cycles(&mut buf, size);
    }

    section("Components — UTF-8 validation (std)");
    for size in [64, 128, 256, 512, 1024, 4096] {
        bench_utf8_cycles(&mut buf, size);
    }

    section("Components — UTF-8 validation (simdutf8)");
    for size in [64, 128, 256, 512, 1024, 4096] {
        bench_simdutf8_cycles(&mut buf, size);
    }

    section("FrameWriter — encode");
    for size in [128, 512, 2048] {
        bench_encode_cycles(&mut buf, size, Role::Server);
    }
    for size in [128, 512] {
        bench_encode_cycles(&mut buf, size, Role::Client);
    }

    section("FrameWriter — encode (internal buf)");
    for size in [128, 512, 2048] {
        bench_encode_into_cycles(&mut buf, size);
    }

    section("Throughput — messages per second");
    bench_throughput_cycles(&mut buf, 10);
    bench_throughput_cycles(&mut buf, 100);
    bench_throughput_cycles(&mut buf, 1000);
}
