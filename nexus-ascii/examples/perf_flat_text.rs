//! FlatAsciiText performance benchmark (batched).
//!
//! Uses 100-op batched measurements with serializing fences for sub-rdtsc-floor
//! resolution. Measures construction, checked vs unchecked replacement, and
//! promotion cost in CPU cycles.
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release --example perf_flat_text
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench_batched, print_header, print_intro};
use nexus_ascii::{AsciiChar, FlatAsciiString, FlatAsciiText};
use std::hint::black_box;

fn main() {
    print_intro("FLATASCIITEXT PERFORMANCE BENCHMARK (batched, 100 ops/sample)");

    // =========================================================================
    // Construction
    // =========================================================================
    print_header("CONSTRUCTION");

    bench_batched("empty()", || {
        let t: FlatAsciiText<32> = FlatAsciiText::empty();
        black_box(t).as_raw()[0] as u64
    });

    bench_batched("try_from str (7B \"BTC-USD\")", || {
        let t: FlatAsciiText<32> = FlatAsciiText::try_from(black_box("BTC-USD")).unwrap();
        t.as_raw()[0] as u64
    });

    bench_batched("try_from str (20B)", || {
        let t: FlatAsciiText<32> =
            FlatAsciiText::try_from(black_box("ABCDEFGHIJ1234567890")).unwrap();
        t.as_raw()[0] as u64
    });

    // Wire format
    let buffer_7: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
    bench_batched("try_from_null_terminated (7B)", || {
        let t: FlatAsciiText<16> =
            FlatAsciiText::try_from_null_terminated(black_box(&buffer_7[..])).unwrap();
        t.as_raw()[0] as u64
    });

    bench_batched("try_from_raw (7B in 16B)", || {
        let t: FlatAsciiText<16> = FlatAsciiText::try_from_raw(black_box(buffer_7)).unwrap();
        t.as_raw()[0] as u64
    });

    let padded: [u8; 16] = *b"BTC-USD         ";
    bench_batched("try_from_right_padded (7B)", || {
        let t: FlatAsciiText<16> =
            FlatAsciiText::try_from_right_padded(black_box(padded), b' ').unwrap();
        t.as_raw()[0] as u64
    });

    // From FlatAsciiString
    let raw: FlatAsciiString<32> = FlatAsciiString::try_from("BTC-USD").unwrap();
    bench_batched("try_from FlatAsciiString", || {
        let t: FlatAsciiText<32> = FlatAsciiText::try_from(black_box(raw)).unwrap();
        t.as_raw()[0] as u64
    });

    // =========================================================================
    // Accessors
    // =========================================================================
    println!();
    print_header("ACCESSORS");

    let t7: FlatAsciiText<32> = FlatAsciiText::try_from("BTC-USD").unwrap();

    bench_batched("len() (7B)", || black_box(t7).len() as u64);
    bench_batched("as_str() (7B)", || black_box(t7).as_str().len() as u64);
    bench_batched("is_empty()", || u64::from(!black_box(t7).is_empty()));

    // =========================================================================
    // Replacement: checked vs unchecked
    // =========================================================================
    println!();
    print_header("REPLACEMENT (checked vs unchecked)");

    let sym: FlatAsciiText<32> = FlatAsciiText::try_from("BTC-USD-PERP").unwrap();
    let minus = AsciiChar::try_new(b'-').unwrap();
    let underscore = AsciiChar::try_new(b'_').unwrap();

    bench_batched("replaced_char (checked)", || {
        black_box(sym)
            .replaced_char(minus, underscore)
            .unwrap()
            .len() as u64
    });

    bench_batched("replaced_char_unchecked (unsafe)", || {
        // SAFETY: underscore is a valid printable ASCII char.
        unsafe { black_box(sym).replaced_char_unchecked(minus, underscore) }.len() as u64
    });

    bench_batched("replace_first_char (checked)", || {
        black_box(sym)
            .replace_first_char(minus, underscore)
            .unwrap()
            .len() as u64
    });

    bench_batched("replace_first_char_unchecked (unsafe)", || {
        // SAFETY: underscore is a valid printable ASCII char.
        unsafe { black_box(sym).replace_first_char_unchecked(minus, underscore) }.len() as u64
    });

    // =========================================================================
    // Promotion to AsciiText
    // =========================================================================
    println!();
    print_header("PROMOTION (to_ascii_text)");

    bench_batched("to_ascii_text (7B)", || {
        black_box(t7).to_ascii_text().header()
    });

    let t20: FlatAsciiText<32> = FlatAsciiText::try_from("ABCDEFGHIJ1234567890").unwrap();
    bench_batched("to_ascii_text (20B)", || {
        black_box(t20).to_ascii_text().header()
    });

    // =========================================================================
    println!();
}
