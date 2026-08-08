//! FlatAsciiString performance benchmark (batched).
//!
//! Uses 100-op batched measurements with serializing fences for sub-rdtsc-floor
//! resolution. Measures construction, accessors, operations, and promotion cost
//! in CPU cycles. Compares against AsciiString where relevant.
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release --example perf_flat_string
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench_batched, print_header, print_intro};
use nexus_ascii::{AsciiChar, AsciiString, FlatAsciiString};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::hint::black_box;

fn main() {
    print_intro("FLATASCIISTRING PERFORMANCE BENCHMARK (batched, 100 ops/sample)");

    // =========================================================================
    // Construction
    // =========================================================================
    print_header("CONSTRUCTION");

    bench_batched("empty()", || {
        let s: FlatAsciiString<32> = FlatAsciiString::empty();
        black_box(s).as_raw()[0] as u64
    });

    bench_batched("try_from str (7B \"BTC-USD\")", || {
        let s: FlatAsciiString<32> = FlatAsciiString::try_from(black_box("BTC-USD")).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("try_from str (20B)", || {
        let s: FlatAsciiString<32> =
            FlatAsciiString::try_from(black_box("ABCDEFGHIJ1234567890")).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("try_from str (32B, full cap)", || {
        let s: FlatAsciiString<32> =
            FlatAsciiString::try_from(black_box("ABCDEFGHIJKLMNOPQRSTUVWXYZ123456")).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("try_from_bytes (7B)", || {
        let s: FlatAsciiString<32> =
            FlatAsciiString::try_from_bytes(black_box(b"BTC-USD")).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("from_bytes_unchecked (7B)", || {
        // SAFETY: b"BTC-USD" is valid ASCII.
        let s: FlatAsciiString<32> =
            unsafe { FlatAsciiString::from_bytes_unchecked(black_box(b"BTC-USD")) };
        s.as_raw()[0] as u64
    });

    // =========================================================================
    // Wire format construction (null-terminated / raw buffer)
    // =========================================================================
    println!();
    print_header("WIRE FORMAT CONSTRUCTION");

    let buffer_7: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
    bench_batched("try_from_null_terminated (7B)", || {
        let s: FlatAsciiString<16> =
            FlatAsciiString::try_from_null_terminated(black_box(&buffer_7[..])).unwrap();
        s.as_raw()[0] as u64
    });

    let buffer_full: [u8; 16] = *b"ABCDEFGHIJKLMNOP";
    bench_batched("try_from_null_terminated (16B full)", || {
        let s: FlatAsciiString<16> =
            FlatAsciiString::try_from_null_terminated(black_box(&buffer_full[..])).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("try_from_raw (7B in 16B)", || {
        let s: FlatAsciiString<16> = FlatAsciiString::try_from_raw(black_box(buffer_7)).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("try_from_raw_ref (7B in &[u8;16])", || {
        let s: FlatAsciiString<16> =
            FlatAsciiString::try_from_raw_ref(black_box(&buffer_7)).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("from_raw_unchecked (7B in 16B)", || {
        // SAFETY: buffer_7 contains valid ASCII followed by null padding.
        let s: FlatAsciiString<16> =
            unsafe { FlatAsciiString::from_raw_unchecked(black_box(buffer_7)) };
        s.as_raw()[0] as u64
    });

    let padded: [u8; 16] = *b"BTC-USD         ";
    bench_batched("try_from_right_padded (7B)", || {
        let s: FlatAsciiString<16> =
            FlatAsciiString::try_from_right_padded(black_box(padded), b' ').unwrap();
        s.as_raw()[0] as u64
    });

    // =========================================================================
    // Accessors — len() is the key cost (SIMD null scan)
    // =========================================================================
    println!();
    print_header("ACCESSORS");

    let s7: FlatAsciiString<32> = FlatAsciiString::try_from("BTC-USD").unwrap();
    let s20: FlatAsciiString<32> = FlatAsciiString::try_from("ABCDEFGHIJ1234567890").unwrap();
    let s_full: FlatAsciiString<32> =
        FlatAsciiString::try_from("ABCDEFGHIJKLMNOPQRSTUVWXYZ123456").unwrap();

    bench_batched("len() (7B content)", || black_box(s7).len() as u64);

    bench_batched("len() (20B content)", || black_box(s20).len() as u64);

    bench_batched("len() (32B full buffer)", || black_box(s_full).len() as u64);

    bench_batched("as_str() (7B)", || black_box(s7).as_str().len() as u64);

    bench_batched("as_bytes() (7B)", || black_box(s7).as_bytes().len() as u64);

    bench_batched("is_empty()", || u64::from(!black_box(s7).is_empty()));

    // =========================================================================
    // String operations
    // =========================================================================
    println!();
    print_header("OPERATIONS");

    let s: FlatAsciiString<32> = FlatAsciiString::try_from("BTC-USD").unwrap();

    let padded_s: FlatAsciiString<32> = FlatAsciiString::try_from("  BTC-USD  ").unwrap();
    bench_batched("trimmed()", || black_box(padded_s).trimmed().len() as u64);

    bench_batched("trimmed_start()", || {
        black_box(padded_s).trimmed_start().len() as u64
    });

    bench_batched("trimmed_end()", || {
        black_box(padded_s).trimmed_end().len() as u64
    });

    bench_batched("contains (found, 3B)", || {
        u64::from(black_box(&s).contains(black_box(b"USD")))
    });

    bench_batched("contains (not found)", || {
        u64::from(black_box(&s).contains(black_box(b"EUR")))
    });

    bench_batched("split_once (found)", || {
        u64::from(black_box(&s).split_once(b'-').is_some())
    });

    // =========================================================================
    // Replacement
    // =========================================================================
    println!();
    print_header("REPLACEMENT");

    let sym: FlatAsciiString<32> = FlatAsciiString::try_from("BTC-USD-PERP").unwrap();
    let minus = AsciiChar::try_new(b'-').unwrap();
    let underscore = AsciiChar::try_new(b'_').unwrap();

    bench_batched("replaced_char (AsciiChar)", || {
        black_box(sym).replaced_char(minus, underscore).len() as u64
    });

    bench_batched("replace_first_char (AsciiChar)", || {
        black_box(sym).replace_first_char(minus, underscore).len() as u64
    });

    bench_batched("replaced_byte (unsafe)", || {
        // SAFETY: b'_' is valid ASCII.
        unsafe { black_box(sym).replaced_byte(b'-', b'_') }.len() as u64
    });

    bench_batched("replace_first_byte (unsafe)", || {
        // SAFETY: b'_' is valid ASCII.
        unsafe { black_box(sym).replace_first_byte(b'-', b'_') }.len() as u64
    });

    // Multi-byte replacement
    let long: FlatAsciiString<32> = FlatAsciiString::try_from("foo bar foo baz").unwrap();
    bench_batched("replaced (3B->3B, multi)", || {
        // SAFETY: b"qux" is valid ASCII
        unsafe { black_box(long).replaced(b"foo", b"qux") }.len() as u64
    });

    bench_batched("replace_first (3B->3B)", || {
        // SAFETY: b"qux" is valid ASCII
        unsafe { black_box(long).replace_first(b"foo", b"qux") }.len() as u64
    });

    // =========================================================================
    // Integer parsing / formatting
    // =========================================================================
    println!();
    print_header("INTEGER PARSING / FORMATTING");

    let num_str: FlatAsciiString<32> = FlatAsciiString::try_from("18446744073709551615").unwrap();
    bench_batched("parse_u64 (20 digits)", || {
        black_box(&num_str).parse_u64().unwrap()
    });

    let i64_str: FlatAsciiString<32> = FlatAsciiString::try_from("-9223372036854775808").unwrap();
    bench_batched("parse_i64 (negative, 20 chars)", || {
        black_box(&i64_str).parse_i64().unwrap() as u64
    });

    bench_batched("from_u64 (max)", || {
        let s: FlatAsciiString<32> = FlatAsciiString::from_u64(black_box(u64::MAX)).unwrap();
        s.len() as u64
    });

    // =========================================================================
    // Promotion to AsciiString (adds header/hash)
    // =========================================================================
    println!();
    print_header("PROMOTION (to_ascii_string)");

    bench_batched("to_ascii_string (7B)", || {
        black_box(s7).to_ascii_string().header()
    });

    bench_batched("to_ascii_string (20B)", || {
        black_box(s20).to_ascii_string().header()
    });

    bench_batched("to_ascii_string (32B full)", || {
        black_box(s_full).to_ascii_string().header()
    });

    // =========================================================================
    // Hashing: Flat (on-the-fly) vs AsciiString (precomputed)
    // =========================================================================
    println!();
    print_header("HASHING (Flat vs AsciiString)");

    let flat7: FlatAsciiString<32> = FlatAsciiString::try_from("BTC-USD").unwrap();
    let ascii7: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
    let flat32: FlatAsciiString<32> =
        FlatAsciiString::try_from("ABCDEFGHIJKLMNOPQRSTUVWXYZ123456").unwrap();
    let ascii32: AsciiString<32> =
        AsciiString::try_from("ABCDEFGHIJKLMNOPQRSTUVWXYZ123456").unwrap();

    bench_batched("Flat Hash::hash (7B)", || {
        let mut hasher = DefaultHasher::new();
        black_box(flat7).hash(&mut hasher);
        hasher.finish()
    });

    bench_batched("AsciiString Hash::hash (7B)", || {
        let mut hasher = DefaultHasher::new();
        black_box(ascii7).hash(&mut hasher);
        hasher.finish()
    });

    bench_batched("Flat Hash::hash (32B)", || {
        let mut hasher = DefaultHasher::new();
        black_box(flat32).hash(&mut hasher);
        hasher.finish()
    });

    bench_batched("AsciiString Hash::hash (32B)", || {
        let mut hasher = DefaultHasher::new();
        black_box(ascii32).hash(&mut hasher);
        hasher.finish()
    });

    // =========================================================================
    // Equality: Flat (content compare) vs AsciiString (header compare)
    // =========================================================================
    println!();
    print_header("EQUALITY (Flat vs AsciiString)");

    let flat7b: FlatAsciiString<32> = FlatAsciiString::try_from("BTC-USD").unwrap();
    let ascii7b: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();

    bench_batched("Flat == (7B, equal)", || {
        u64::from(black_box(flat7) == black_box(flat7b))
    });

    bench_batched("AsciiString == (7B, equal)", || {
        u64::from(black_box(ascii7) == black_box(ascii7b))
    });

    let flat_diff: FlatAsciiString<32> = FlatAsciiString::try_from("ETH-USD").unwrap();
    let ascii_diff: AsciiString<32> = AsciiString::try_from("ETH-USD").unwrap();

    bench_batched("Flat == (7B, not equal)", || {
        u64::from(black_box(flat7) == black_box(flat_diff))
    });

    bench_batched("AsciiString == (7B, not equal)", || {
        u64::from(black_box(ascii7) == black_box(ascii_diff))
    });

    // =========================================================================
    println!();
}
