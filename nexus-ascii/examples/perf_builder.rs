//! AsciiStringBuilder performance benchmark.
//!
//! Measures construction, push operations, and build finalization.
//!
//! Run with:
//! ```bash
//! cargo run --release --example perf_builder
//!
//! # With perf stat for IPC/branch analysis:
//! perf stat -r 10 ./target/release/examples/perf_builder
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench_wide, print_header_wide, print_intro};
use nexus_ascii::{AsciiChar, AsciiStr, AsciiString, AsciiStringBuilder};
use std::hint::black_box;

fn main() {
    print_intro("ASCIISTRING BUILDER BENCHMARK");

    // =========================================================================
    // Construction
    // =========================================================================
    print_header_wide("CONSTRUCTION");

    bench_wide("AsciiStringBuilder::new()", || {
        let builder: AsciiStringBuilder<32> = black_box(AsciiStringBuilder::new());
        builder.len() as u64
    });

    let source: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
    bench_wide("AsciiStringBuilder::from_ascii_string()", || {
        let builder = AsciiStringBuilder::from_ascii_string(black_box(source));
        builder.len() as u64
    });

    // =========================================================================
    // Push operations
    // =========================================================================
    println!();
    print_header_wide("PUSH OPERATIONS");

    bench_wide("push(AsciiChar)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push(black_box(AsciiChar::A)).unwrap();
        builder.len() as u64
    });

    bench_wide("push_byte(b'A')", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_byte(black_box(b'A')).unwrap();
        builder.len() as u64
    });

    bench_wide("push_str (7B \"BTC-USD\")", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str(black_box("BTC-USD")).unwrap();
        builder.len() as u64
    });

    bench_wide("push_str (20B)", || {
        let mut builder: AsciiStringBuilder<64> = AsciiStringBuilder::new();
        builder.push_str(black_box("ORDER-ID-1234567890")).unwrap();
        builder.len() as u64
    });

    bench_wide("push_bytes (7B)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_bytes(black_box(b"BTC-USD")).unwrap();
        builder.len() as u64
    });

    bench_wide("push_bytes_unchecked (7B)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        // SAFETY: b"BTC-USD" is valid ASCII.
        unsafe { builder.push_bytes_unchecked(black_box(b"BTC-USD")) };
        builder.len() as u64
    });

    let ascii_str = AsciiStr::try_from_bytes(b"BTC-USD").unwrap();
    bench_wide("push_ascii_str (7B)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_ascii_str(black_box(ascii_str)).unwrap();
        builder.len() as u64
    });

    let ascii_string: AsciiString<16> = AsciiString::try_from("BTC-USD").unwrap();
    bench_wide("push_ascii_string (7B)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_ascii_string(black_box(&ascii_string)).unwrap();
        builder.len() as u64
    });

    let raw_buffer: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
    bench_wide("push_raw (7B in 16B buffer)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_raw(black_box(raw_buffer)).unwrap();
        builder.len() as u64
    });

    bench_wide("push_raw_unchecked (7B in 16B buffer)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        // SAFETY: raw_buffer contains valid ASCII followed by null padding.
        unsafe { builder.push_raw_unchecked(black_box(raw_buffer)) };
        builder.len() as u64
    });

    // =========================================================================
    // Multiple pushes
    // =========================================================================
    println!();
    print_header_wide("MULTIPLE PUSHES");

    bench_wide("push_str x3 (BTC + - + USD)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str(black_box("BTC")).unwrap();
        builder.push_str(black_box("-")).unwrap();
        builder.push_str(black_box("USD")).unwrap();
        builder.len() as u64
    });

    bench_wide("push_byte x7 (B-T-C--U-S-D)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        for b in b"BTC-USD" {
            builder.push_byte(black_box(*b)).unwrap();
        }
        builder.len() as u64
    });

    // =========================================================================
    // Build finalization
    // =========================================================================
    println!();
    print_header_wide("BUILD FINALIZATION");

    bench_wide("build() (7B content)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("BTC-USD").unwrap();
        let s = black_box(builder).build();
        s.len() as u64
    });

    bench_wide("build() (20B content)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("ORDER-ID-1234567890").unwrap();
        let s = black_box(builder).build();
        s.len() as u64
    });

    bench_wide("build() (empty)", || {
        let builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        let s = black_box(builder).build();
        s.len() as u64
    });

    // =========================================================================
    // Full pipeline comparison
    // =========================================================================
    println!();
    print_header_wide("FULL PIPELINE");

    bench_wide("builder: push_str + build (7B)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str(black_box("BTC-USD")).unwrap();
        let s = builder.build();
        s.len() as u64
    });

    bench_wide("direct: AsciiString::try_from (7B)", || {
        let s: AsciiString<32> = AsciiString::try_from(black_box("BTC-USD")).unwrap();
        s.len() as u64
    });

    bench_wide("builder: 3x push_str + build", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str(black_box("BTC")).unwrap();
        builder.push_str(black_box("-")).unwrap();
        builder.push_str(black_box("USD")).unwrap();
        let s = builder.build();
        s.len() as u64
    });

    // =========================================================================
    // Mutation operations
    // =========================================================================
    println!();
    print_header_wide("MUTATION");

    bench_wide("clear()", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello, World!").unwrap();
        black_box(&mut builder).clear();
        builder.len() as u64
    });

    bench_wide("truncate(5)", || {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello, World!").unwrap();
        black_box(&mut builder).truncate(5);
        builder.len() as u64
    });

    println!();
}
