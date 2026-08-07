//! AsciiString performance benchmark.
//!
//! Measures construction, equality, and hashing performance in CPU cycles.
//!
//! Run with:
//! ```bash
//! cargo run --release --example perf_string
//!
//! # With perf stat for IPC/branch analysis:
//! perf stat -r 10 ./target/release/examples/perf_string
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench, bench_batched, bench_raw, print_header, print_intro, rdtsc};
use nexus_ascii::AsciiString;
use std::collections::HashMap;
use std::hint::black_box;

fn main() {
    print_intro("ASCIISTRING PERFORMANCE BENCHMARK");

    // =========================================================================
    // Construction
    // =========================================================================
    print_header("CONSTRUCTION");

    // Empty
    bench_batched("empty()", || {
        let s: AsciiString<32> = AsciiString::empty();
        black_box(s).as_raw()[0] as u64
    });

    // try_from_str - various sizes
    bench_batched("try_from (7B \"BTC-USD\")", || {
        let s: AsciiString<32> = AsciiString::try_from(black_box("BTC-USD")).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("try_from (20B)", || {
        let s: AsciiString<32> = AsciiString::try_from(black_box("ABCDEFGHIJ1234567890")).unwrap();
        s.as_raw()[0] as u64
    });

    bench_batched("try_from (32B, full cap)", || {
        let s: AsciiString<32> =
            AsciiString::try_from(black_box("ABCDEFGHIJKLMNOPQRSTUVWXYZ123456")).unwrap();
        s.as_raw()[0] as u64
    });

    // from_bytes_unchecked
    bench_batched("from_bytes_unchecked (7B)", || {
        // SAFETY: b"BTC-USD" is valid ASCII.
        let s: AsciiString<32> =
            unsafe { AsciiString::from_bytes_unchecked(black_box(b"BTC-USD")) };
        s.as_raw()[0] as u64
    });

    // =========================================================================
    // Equality
    // =========================================================================
    println!();
    print_header("EQUALITY");

    let s1: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
    let s2: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
    let s3: AsciiString<32> = AsciiString::try_from("ETH-USD").unwrap();
    let s4: AsciiString<32> = AsciiString::try_from("BTC").unwrap();

    bench("eq (same content)", || {
        u64::from(black_box(s1) == black_box(s2))
    });

    bench("eq (different content)", || {
        u64::from(black_box(s1) == black_box(s3))
    });

    bench("eq (different length)", || {
        u64::from(black_box(s1) == black_box(s4))
    });

    // Baseline: raw u64 comparison (what our header compare should match)
    let h1 = s1.header();
    let h2 = s2.header();
    bench("baseline: u64 == u64", || {
        u64::from(black_box(h1) == black_box(h2))
    });

    // =========================================================================
    // HashMap
    // =========================================================================
    println!();
    print_header("HASHMAP");

    let mut map: HashMap<AsciiString<32>, u64> = HashMap::new();
    for i in 0..100 {
        let key = AsciiString::try_from(format!("KEY-{:03}", i).as_str()).unwrap();
        map.insert(key, i as u64);
    }

    let lookup_key: AsciiString<32> = AsciiString::try_from("KEY-050").unwrap();

    bench("HashMap::get (100 entries)", || {
        map.get(black_box(&lookup_key)).copied().unwrap_or(0)
    });

    let insert_key: AsciiString<32> = AsciiString::try_from("NEW-KEY").unwrap();
    bench_raw("HashMap::insert (new key)", || {
        let start = rdtsc();
        black_box(map.insert(insert_key, black_box(999u64)));
        let elapsed = rdtsc().wrapping_sub(start);
        map.remove(&insert_key);
        elapsed
    });

    // =========================================================================
    // Accessors
    // =========================================================================
    println!();
    print_header("ACCESSORS");

    let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();

    bench("len()", || black_box(s).len() as u64);

    bench("as_str()", || black_box(s).as_str().len() as u64);

    bench("as_bytes()", || black_box(s).as_bytes().len() as u64);

    bench("header()", || black_box(s).header());

    println!();
}
