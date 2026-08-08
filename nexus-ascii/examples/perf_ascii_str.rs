//! AsciiStr performance benchmark.
//!
//! Measures Deref coercion, construction, and cross-type equality performance.
//!
//! Run with:
//! ```bash
//! cargo run --release --example perf_ascii_str
//!
//! # With perf stat for IPC/branch analysis:
//! perf stat -r 10 ./target/release/examples/perf_ascii_str
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench, print_header, print_intro};
use nexus_ascii::{AsciiStr, AsciiString};
use std::hint::black_box;

#[inline(never)]
fn process_ascii_str(s: &AsciiStr) -> u64 {
    s.len() as u64
}

fn main() {
    print_intro("ASCIISTR BENCHMARK");

    // =========================================================================
    // Construction
    // =========================================================================
    print_header("CONSTRUCTION");

    let bytes_7 = b"BTC-USD";
    let bytes_32 = b"ORDER-ID-12345678901234567890123";

    bench("try_from_bytes (7B)", || {
        let s = AsciiStr::try_from_bytes(black_box(bytes_7)).unwrap();
        s.len() as u64
    });

    bench("try_from_bytes (32B)", || {
        let s = AsciiStr::try_from_bytes(black_box(bytes_32)).unwrap();
        s.len() as u64
    });

    bench("try_from_str (7B)", || {
        let s = AsciiStr::try_from_str(black_box("BTC-USD")).unwrap();
        s.len() as u64
    });

    bench("from_bytes_unchecked (7B)", || {
        // SAFETY: bytes_7 is valid ASCII.
        let s = unsafe { AsciiStr::from_bytes_unchecked(black_box(bytes_7)) };
        s.len() as u64
    });

    bench("from_bytes_unchecked (32B)", || {
        // SAFETY: bytes_32 is valid ASCII.
        let s = unsafe { AsciiStr::from_bytes_unchecked(black_box(bytes_32)) };
        s.len() as u64
    });

    // =========================================================================
    // Deref from AsciiString
    // =========================================================================
    println!();
    print_header("DEREF FROM ASCIISTRING");

    let ascii_string: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();

    bench("as_ascii_str()", || {
        let s = black_box(&ascii_string).as_ascii_str();
        s.len() as u64
    });

    bench("deref coercion", || {
        let s: &AsciiStr = black_box(&ascii_string);
        s.len() as u64
    });

    // Compare direct method vs deref method
    bench("AsciiString.len() direct", || {
        black_box(&ascii_string).len() as u64
    });

    bench("(&AsciiStr).len() via deref", || {
        let s: &AsciiStr = black_box(&ascii_string);
        s.len() as u64
    });

    // =========================================================================
    // Accessors
    // =========================================================================
    println!();
    print_header("ACCESSORS");

    let ascii_str = AsciiStr::try_from_bytes(b"BTC-USD").unwrap();

    bench("len()", || black_box(ascii_str).len() as u64);

    bench("as_bytes()", || {
        black_box(ascii_str).as_bytes().len() as u64
    });

    bench("as_str()", || black_box(ascii_str).as_str().len() as u64);

    bench("get(0)", || {
        black_box(ascii_str).get(0).map_or(0, |c| c.as_u8() as u64)
    });

    bench("first()", || {
        black_box(ascii_str).first().map_or(0, |c| c.as_u8() as u64)
    });

    bench("last()", || {
        black_box(ascii_str).last().map_or(0, |c| c.as_u8() as u64)
    });

    // =========================================================================
    // Cross-type equality
    // =========================================================================
    println!();
    print_header("CROSS-TYPE EQUALITY");

    let ascii_str = AsciiStr::try_from_bytes(b"BTC-USD").unwrap();
    let ascii_string: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();

    bench("AsciiStr == AsciiStr", || {
        u64::from(black_box(ascii_str) == black_box(ascii_str))
    });

    bench("AsciiString == AsciiStr", || {
        u64::from(black_box(&ascii_string) == black_box(ascii_str))
    });

    bench("AsciiStr == str", || {
        u64::from(black_box(ascii_str) == black_box("BTC-USD"))
    });

    bench("AsciiStr == &[u8]", || {
        u64::from(*black_box(ascii_str) == black_box(b"BTC-USD")[..])
    });

    // =========================================================================
    // Function accepting &AsciiStr
    // =========================================================================
    println!();
    print_header("FUNCTION ACCEPTING &AsciiStr");

    bench("call with &AsciiStr directly", || {
        process_ascii_str(black_box(ascii_str))
    });

    bench("call with &AsciiString (deref)", || {
        process_ascii_str(black_box(&ascii_string))
    });

    // =========================================================================
    // Baseline comparisons
    // =========================================================================
    println!();
    print_header("BASELINE COMPARISONS");

    let str_ref: &str = "BTC-USD";
    let byte_slice: &[u8] = b"BTC-USD";

    bench("&str.len() (baseline)", || black_box(str_ref).len() as u64);

    bench("&[u8].len() (baseline)", || {
        black_box(byte_slice).len() as u64
    });

    bench("&str == &str (baseline)", || {
        u64::from(black_box(str_ref) == black_box("BTC-USD"))
    });

    bench("&[u8] == &[u8] (baseline)", || {
        u64::from(black_box(byte_slice) == black_box(b"BTC-USD"))
    });

    println!();
}
