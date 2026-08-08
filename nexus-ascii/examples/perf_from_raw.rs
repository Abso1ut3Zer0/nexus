//! Performance benchmark for try_from_raw and related methods.
//!
//! Measures the overhead of null-byte detection and buffer construction.
//!
//! Run with:
//! ```bash
//! cargo run --release --example perf_from_raw
//!
//! # With perf stat for IPC/branch analysis:
//! perf stat -r 10 ./target/release/examples/perf_from_raw
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench_wide, print_header_wide, print_intro};
use nexus_ascii::{AsciiString, AsciiText};
use std::hint::black_box;

fn main() {
    print_intro("FROM_RAW BENCHMARK");

    // =========================================================================
    // try_from_raw vs try_from_bytes
    // =========================================================================
    print_header_wide("try_from_raw vs try_from_bytes");

    // 7-byte string (typical symbol like "BTC-USD")
    let buffer_7: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
    let bytes_7 = b"BTC-USD";

    bench_wide("try_from_bytes (7B slice)", || {
        let s: AsciiString<16> = AsciiString::try_from_bytes(black_box(bytes_7)).unwrap();
        s.len() as u64
    });

    bench_wide("try_from_raw (7B in 16B buffer)", || {
        let s: AsciiString<16> = AsciiString::try_from_raw(black_box(buffer_7)).unwrap();
        s.len() as u64
    });

    bench_wide("from_raw_unchecked (7B in 16B buffer)", || {
        // SAFETY: buffer_7 contains valid ASCII followed by null padding.
        let s: AsciiString<16> = unsafe { AsciiString::from_raw_unchecked(black_box(buffer_7)) };
        s.len() as u64
    });

    // 8-byte string (boundary case)
    let buffer_8: [u8; 16] = *b"BTCUSDT!\0\0\0\0\0\0\0\0";
    let bytes_8 = b"BTCUSDT!";

    bench_wide("try_from_bytes (8B slice)", || {
        let s: AsciiString<16> = AsciiString::try_from_bytes(black_box(bytes_8)).unwrap();
        s.len() as u64
    });

    bench_wide("try_from_raw (8B in 16B buffer)", || {
        let s: AsciiString<16> = AsciiString::try_from_raw(black_box(buffer_8)).unwrap();
        s.len() as u64
    });

    // 20-byte string (spans multiple 8-byte chunks)
    let buffer_20: [u8; 32] = *b"ORDER-ID-12345678901\0\0\0\0\0\0\0\0\0\0\0\0";
    let bytes_20 = b"ORDER-ID-12345678901";

    bench_wide("try_from_bytes (20B slice)", || {
        let s: AsciiString<32> = AsciiString::try_from_bytes(black_box(bytes_20)).unwrap();
        s.len() as u64
    });

    bench_wide("try_from_raw (20B in 32B buffer)", || {
        let s: AsciiString<32> = AsciiString::try_from_raw(black_box(buffer_20)).unwrap();
        s.len() as u64
    });

    bench_wide("from_raw_unchecked (20B in 32B buffer)", || {
        // SAFETY: buffer_20 contains valid ASCII followed by null padding.
        let s: AsciiString<32> = unsafe { AsciiString::from_raw_unchecked(black_box(buffer_20)) };
        s.len() as u64
    });

    // =========================================================================
    // try_from_null_terminated (slice-based)
    // =========================================================================
    println!();
    print_header_wide("try_from_null_terminated (slice)");

    // Reference to fixed buffer (common wire format pattern)
    let slice_7: &[u8; 16] = b"BTC-USD\0\0\0\0\0\0\0\0\0";
    bench_wide("try_from_null_terminated (7B in &[u8;16])", || {
        let s: AsciiString<16> = AsciiString::try_from_null_terminated(black_box(slice_7)).unwrap();
        s.len() as u64
    });

    let slice_20: &[u8; 32] = b"ORDER-ID-12345678901\0\0\0\0\0\0\0\0\0\0\0\0";
    bench_wide("try_from_null_terminated (20B in &[u8;32])", || {
        let s: AsciiString<32> =
            AsciiString::try_from_null_terminated(black_box(slice_20)).unwrap();
        s.len() as u64
    });

    // Slice without fixed size
    let dyn_slice: &[u8] = b"ETH-USD\0garbage_after_null";
    bench_wide("try_from_null_terminated (7B in &[u8])", || {
        let s: AsciiString<16> =
            AsciiString::try_from_null_terminated(black_box(dyn_slice)).unwrap();
        s.len() as u64
    });

    // =========================================================================
    // try_from_raw_ref (typed array reference)
    // =========================================================================
    println!();
    print_header_wide("try_from_raw_ref (&[u8; CAP])");

    bench_wide("try_from_raw_ref (7B in &[u8;16])", || {
        let s: AsciiString<16> = AsciiString::try_from_raw_ref(black_box(slice_7)).unwrap();
        s.len() as u64
    });

    bench_wide("try_from_raw_ref (20B in &[u8;32])", || {
        let s: AsciiString<32> = AsciiString::try_from_raw_ref(black_box(slice_20)).unwrap();
        s.len() as u64
    });

    // Compare with try_from_null_terminated on same data
    bench_wide("try_from_null_terminated (same 7B)", || {
        let s: AsciiString<16> = AsciiString::try_from_null_terminated(black_box(slice_7)).unwrap();
        s.len() as u64
    });

    // =========================================================================
    // AsciiText (double validation overhead)
    // =========================================================================
    println!();
    print_header_wide("AsciiText (ASCII + printable validation)");

    bench_wide("AsciiText::try_from_null_terminated (7B)", || {
        let t: AsciiText<16> = AsciiText::try_from_null_terminated(black_box(slice_7)).unwrap();
        t.len() as u64
    });

    bench_wide("AsciiText::try_from_null_terminated (20B)", || {
        let t: AsciiText<32> = AsciiText::try_from_null_terminated(black_box(slice_20)).unwrap();
        t.len() as u64
    });

    let text_buffer_7: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
    bench_wide("AsciiText::try_from_raw (7B)", || {
        let t: AsciiText<16> = AsciiText::try_from_raw(black_box(text_buffer_7)).unwrap();
        t.len() as u64
    });

    let text_padded_7: [u8; 16] = *b"BTC-USD         ";
    bench_wide("AsciiText::try_from_right_padded (7B)", || {
        let t: AsciiText<16> =
            AsciiText::try_from_right_padded(black_box(text_padded_7), b' ').unwrap();
        t.len() as u64
    });

    // =========================================================================
    // try_from_right_padded
    // =========================================================================
    println!();
    print_header_wide("try_from_right_padded");

    let padded_7: [u8; 16] = *b"BTC-USD         ";

    bench_wide("try_from_right_padded (7B, space pad)", || {
        let s: AsciiString<16> =
            AsciiString::try_from_right_padded(black_box(padded_7), b' ').unwrap();
        s.len() as u64
    });

    let padded_20: [u8; 32] = *b"ORDER-ID-1234567890             ";

    bench_wide("try_from_right_padded (20B, space pad)", || {
        let s: AsciiString<32> =
            AsciiString::try_from_right_padded(black_box(padded_20), b' ').unwrap();
        s.len() as u64
    });

    // =========================================================================
    // Null byte at various positions
    // =========================================================================
    println!();
    print_header_wide("Null position impact");

    // Null at position 0 (empty)
    let buffer_null_0: [u8; 32] = [0u8; 32];
    bench_wide("try_from_raw (null at 0)", || {
        let s: AsciiString<32> = AsciiString::try_from_raw(black_box(buffer_null_0)).unwrap();
        s.len() as u64
    });

    // Null at position 7 (within first chunk)
    let mut buffer_null_7 = [b'X'; 32];
    buffer_null_7[7] = 0;
    bench_wide("try_from_raw (null at 7)", || {
        let s: AsciiString<32> = AsciiString::try_from_raw(black_box(buffer_null_7)).unwrap();
        s.len() as u64
    });

    // Null at position 15 (end of second chunk)
    let mut buffer_null_15 = [b'X'; 32];
    buffer_null_15[15] = 0;
    bench_wide("try_from_raw (null at 15)", || {
        let s: AsciiString<32> = AsciiString::try_from_raw(black_box(buffer_null_15)).unwrap();
        s.len() as u64
    });

    // Null at position 24 (third chunk)
    let mut buffer_null_24 = [b'X'; 32];
    buffer_null_24[24] = 0;
    bench_wide("try_from_raw (null at 24)", || {
        let s: AsciiString<32> = AsciiString::try_from_raw(black_box(buffer_null_24)).unwrap();
        s.len() as u64
    });

    // No null (full buffer)
    let buffer_full: [u8; 32] = [b'X'; 32];
    bench_wide("try_from_raw (no null, full 32B)", || {
        let s: AsciiString<32> = AsciiString::try_from_raw(black_box(buffer_full)).unwrap();
        s.len() as u64
    });

    // =========================================================================
    // Baseline comparisons
    // =========================================================================
    println!();
    print_header_wide("Baselines");

    // memchr-style null search baseline
    let search_buffer: [u8; 32] = *b"ABCDEFGHIJKLMNOP\0...............";
    bench_wide("memchr find null (16B content)", || {
        let pos = black_box(&search_buffer)
            .iter()
            .position(|&b| b == 0)
            .unwrap_or(32);
        pos as u64
    });

    // from_bytes_unchecked (no null search, no validation)
    bench_wide("from_bytes_unchecked (7B, no null search)", || {
        // SAFETY: bytes_7 is valid ASCII.
        let s: AsciiString<16> = unsafe { AsciiString::from_bytes_unchecked(black_box(bytes_7)) };
        s.len() as u64
    });

    println!();
}
