//! Iteration and indexing performance benchmark.
//!
//! Measures iteration, indexing, and accessor performance in CPU cycles.
//!
//! Run with:
//! ```bash
//! cargo run --release --example perf_iteration
//!
//! # With perf stat for IPC/branch analysis:
//! perf stat -r 10 ./target/release/examples/perf_iteration
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench, print_header, print_intro};
use nexus_ascii::{AsciiChar, AsciiString};
use std::hint::black_box;

fn main() {
    print_intro("ITERATION & INDEXING BENCHMARK");

    // =========================================================================
    // Indexing
    // =========================================================================
    print_header("INDEXING");

    let s8: AsciiString<32> = AsciiString::try_from("BTC-USD!").unwrap();
    let s32: AsciiString<64> = AsciiString::try_from("ORDER-ID-1234567890123456789012").unwrap();

    bench("Index s[0] (8B string)", || black_box(s8)[0].as_u8() as u64);

    bench("Index s[7] (8B string, last)", || {
        black_box(s8)[7].as_u8() as u64
    });

    bench("Index s[15] (32B string, middle)", || {
        black_box(s32)[15].as_u8() as u64
    });

    bench("get(0) (8B string)", || {
        black_box(&s8).get(0).map_or(0, |c| c.as_u8() as u64)
    });

    bench("get(7) (8B string, last)", || {
        black_box(&s8).get(7).map_or(0, |c| c.as_u8() as u64)
    });

    bench("get(100) (out of bounds)", || {
        black_box(&s8).get(100).map_or(0, |c| c.as_u8() as u64)
    });

    bench("get_unchecked(0)", || {
        // SAFETY: index 0 is within bounds of an 8-byte string.
        unsafe { black_box(&s8).get_unchecked(0).as_u8() as u64 }
    });

    // =========================================================================
    // first() / last()
    // =========================================================================
    println!();
    print_header("FIRST / LAST");

    bench("first() (8B string)", || {
        black_box(&s8).first().map_or(0, |c| c.as_u8() as u64)
    });

    bench("last() (8B string)", || {
        black_box(&s8).last().map_or(0, |c| c.as_u8() as u64)
    });

    bench("first() (32B string)", || {
        black_box(&s32).first().map_or(0, |c| c.as_u8() as u64)
    });

    bench("last() (32B string)", || {
        black_box(&s32).last().map_or(0, |c| c.as_u8() as u64)
    });

    let empty: AsciiString<32> = AsciiString::empty();
    bench("first() (empty string)", || {
        black_box(&empty).first().map_or(0, |c| c.as_u8() as u64)
    });

    bench("last() (empty string)", || {
        black_box(&empty).last().map_or(0, |c| c.as_u8() as u64)
    });

    // =========================================================================
    // Iteration
    // =========================================================================
    println!();
    print_header("ITERATION");

    bench("chars().count() (8B)", || {
        black_box(&s8).chars().count() as u64
    });

    bench("chars().count() (32B)", || {
        black_box(&s32).chars().count() as u64
    });

    bench("bytes().count() (8B)", || {
        black_box(&s8).bytes().count() as u64
    });

    bench("bytes().count() (32B)", || {
        black_box(&s32).bytes().count() as u64
    });

    // Sum all bytes (forces actual iteration)
    bench("chars().map(as_u8).sum() (8B)", || {
        black_box(&s8).chars().map(|c| c.as_u8() as u64).sum()
    });

    bench("chars().map(as_u8).sum() (32B)", || {
        black_box(&s32).chars().map(|c| c.as_u8() as u64).sum()
    });

    bench("bytes().sum() (8B)", || {
        black_box(&s8).bytes().map(|b| b as u64).sum()
    });

    bench("bytes().sum() (32B)", || {
        black_box(&s32).bytes().map(|b| b as u64).sum()
    });

    // =========================================================================
    // Manual indexing loop vs iterator
    // =========================================================================
    println!();
    print_header("MANUAL LOOP VS ITERATOR");

    bench("manual index loop sum (8B)", || {
        let s = black_box(&s8);
        let mut sum: u64 = 0;
        for i in 0..s.len() {
            sum += s[i].as_u8() as u64;
        }
        sum
    });

    bench("manual index loop sum (32B)", || {
        let s = black_box(&s32);
        let mut sum: u64 = 0;
        for i in 0..s.len() {
            sum += s[i].as_u8() as u64;
        }
        sum
    });

    bench("as_bytes() iter sum (8B)", || {
        black_box(&s8).as_bytes().iter().map(|&b| b as u64).sum()
    });

    bench("as_bytes() iter sum (32B)", || {
        black_box(&s32).as_bytes().iter().map(|&b| b as u64).sum()
    });

    // =========================================================================
    // Baseline comparisons
    // =========================================================================
    println!();
    print_header("BASELINE COMPARISONS");

    let raw_bytes: [u8; 8] = *b"BTC-USD!";
    bench("[u8; 8] index (baseline)", || {
        black_box(raw_bytes)[0] as u64
    });

    bench("[u8; 8] iter sum (baseline)", || {
        black_box(&raw_bytes).iter().map(|&b| b as u64).sum()
    });

    let std_str = "BTC-USD!";
    bench("&str chars().count() (baseline)", || {
        black_box(std_str).chars().count() as u64
    });

    bench("&str bytes().sum() (baseline)", || {
        black_box(std_str).bytes().map(|b| b as u64).sum()
    });

    // =========================================================================
    // Classification during iteration
    // =========================================================================
    println!();
    print_header("CLASSIFICATION DURING ITERATION");

    let mixed: AsciiString<32> = AsciiString::try_from("Hello123World").unwrap();

    bench("count alphabetic (13B)", || {
        black_box(&mixed)
            .chars()
            .filter(|c| c.is_alphabetic())
            .count() as u64
    });

    bench("count digits (13B)", || {
        black_box(&mixed).chars().filter(|c| c.is_digit()).count() as u64
    });

    bench("all uppercase check (8B)", || {
        u64::from(black_box(&s8).chars().all(AsciiChar::is_uppercase))
    });

    bench("any digit check (13B)", || {
        u64::from(black_box(&mixed).chars().any(AsciiChar::is_digit))
    });

    println!();
}
