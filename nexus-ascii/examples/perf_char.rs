//! AsciiChar performance benchmark.
//!
//! Measures construction, classification, and transformation performance in CPU cycles.
//!
//! Run with:
//! ```bash
//! cargo run --release --example perf_char
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench, print_header, print_intro};
use nexus_ascii::AsciiChar;
use std::hint::black_box;

fn main() {
    print_intro("ASCIICHAR BENCHMARK");

    // =========================================================================
    // Construction
    // =========================================================================
    print_header("CONSTRUCTION");

    bench("try_new (valid)", || {
        let c = AsciiChar::try_new(black_box(b'A')).unwrap();
        c.as_u8() as u64
    });

    bench("try_new (invalid)", || {
        let r = AsciiChar::try_new(black_box(0x80));
        u64::from(r.is_err())
    });

    bench("new_unchecked", || {
        // SAFETY: b'A' is valid ASCII.
        let c = unsafe { AsciiChar::new_unchecked(black_box(b'A')) };
        c.as_u8() as u64
    });

    bench("from_char (valid)", || {
        let c = AsciiChar::from_char(black_box('A')).unwrap();
        c.as_u8() as u64
    });

    bench("from_char (invalid)", || {
        let r = AsciiChar::from_char(black_box('\u{00e9}'));
        u64::from(r.is_err())
    });

    // =========================================================================
    // Accessors
    // =========================================================================
    println!();
    print_header("ACCESSORS");

    let c = AsciiChar::A;

    bench("as_u8", || black_box(c).as_u8() as u64);

    bench("as_char", || black_box(c).as_char() as u64);

    // =========================================================================
    // Classification
    // =========================================================================
    println!();
    print_header("CLASSIFICATION");

    let upper = AsciiChar::A;
    let lower = AsciiChar::a;
    let digit = AsciiChar::DIGIT_5;
    let space = AsciiChar::SPACE;
    let ctrl = AsciiChar::SOH;

    bench("is_uppercase (true)", || {
        u64::from(black_box(upper).is_uppercase())
    });

    bench("is_uppercase (false)", || {
        u64::from(black_box(lower).is_uppercase())
    });

    bench("is_lowercase", || {
        u64::from(black_box(lower).is_lowercase())
    });

    bench("is_alphabetic", || {
        u64::from(black_box(upper).is_alphabetic())
    });

    bench("is_digit", || u64::from(black_box(digit).is_digit()));

    bench("is_alphanumeric", || {
        u64::from(black_box(upper).is_alphanumeric())
    });

    bench("is_whitespace", || {
        u64::from(black_box(space).is_whitespace())
    });

    bench("is_printable", || {
        u64::from(black_box(upper).is_printable())
    });

    bench("is_control", || u64::from(black_box(ctrl).is_control()));

    bench("is_hex_digit", || {
        u64::from(black_box(upper).is_hex_digit())
    });

    // =========================================================================
    // Transformations
    // =========================================================================
    println!();
    print_header("TRANSFORMATIONS");

    bench("to_uppercase (from lower)", || {
        black_box(lower).to_uppercase().as_u8() as u64
    });

    bench("to_uppercase (already upper)", || {
        black_box(upper).to_uppercase().as_u8() as u64
    });

    bench("to_lowercase (from upper)", || {
        black_box(upper).to_lowercase().as_u8() as u64
    });

    bench("to_lowercase (already lower)", || {
        black_box(lower).to_lowercase().as_u8() as u64
    });

    bench("eq_ignore_case (same case)", || {
        u64::from(black_box(upper).eq_ignore_case(black_box(upper)))
    });

    bench("eq_ignore_case (diff case)", || {
        u64::from(black_box(upper).eq_ignore_case(black_box(lower)))
    });

    // =========================================================================
    // Baseline comparisons
    // =========================================================================
    println!();
    print_header("BASELINE COMPARISONS");

    // Raw u8 comparison
    let a: u8 = b'A';
    let b: u8 = b'A';
    bench("u8 == u8 (baseline)", || {
        u64::from(black_box(a) == black_box(b))
    });

    // Raw u8 range check (like is_uppercase)
    bench("u8 range check (baseline)", || {
        let x = black_box(a);
        u64::from(x >= b'A' && x <= b'Z')
    });

    // char.is_ascii_uppercase (std)
    let ch: char = 'A';
    bench("char.is_ascii_uppercase (std)", || {
        u64::from(black_box(ch).is_ascii_uppercase())
    });

    // char.to_ascii_lowercase (std)
    bench("char.to_ascii_lowercase (std)", || {
        black_box(ch).to_ascii_lowercase() as u64
    });

    println!();
}
