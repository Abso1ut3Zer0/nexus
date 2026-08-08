//! Comparison benchmark: nexus-ascii vs the `ascii` crate.
//!
//! The `ascii` crate provides heap-allocated AsciiString (like std String) and
//! AsciiStr (like &str). nexus-ascii provides fixed-capacity inline strings
//! with SIMD-accelerated operations and precomputed hashing.
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release --example perf_vs_ascii_crate
//! ```

#[path = "_bench_utils.rs"]
mod bench_utils;

use bench_utils::{bench_wide, print_header_wide, print_intro};
use std::hint::black_box;

fn main() {
    print_intro("NEXUS-ASCII vs ASCII CRATE BENCHMARK");

    // =========================================================================
    // Construction from &str
    // =========================================================================
    println!();
    print_header_wide("CONSTRUCTION (from &str)");

    // 7B - typical trading symbol
    bench_wide("nexus: AsciiString<16>::try_from (7B)", || {
        let s = nexus_ascii::AsciiString::<16>::try_from(black_box("BTC-USD")).unwrap();
        s.len() as u64
    });
    bench_wide("ascii: AsciiString::from_ascii (7B)", || {
        let s = ascii::AsciiString::from_ascii(black_box("BTC-USD")).unwrap();
        s.len() as u64
    });
    bench_wide("std: String::from (7B)", || {
        let s = String::from(black_box("BTC-USD"));
        s.len() as u64
    });

    println!();

    // 20B - order ID
    bench_wide("nexus: AsciiString<32>::try_from (20B)", || {
        let s = nexus_ascii::AsciiString::<32>::try_from(black_box("order-id-1234567890")).unwrap();
        s.len() as u64
    });
    bench_wide("ascii: AsciiString::from_ascii (20B)", || {
        let s = ascii::AsciiString::from_ascii(black_box("order-id-1234567890")).unwrap();
        s.len() as u64
    });
    bench_wide("std: String::from (20B)", || {
        let s = String::from(black_box("order-id-1234567890"));
        s.len() as u64
    });

    println!();

    // 38B - long identifier
    let long = "ABCDEFGHIJKLMNOPQRSTUVWXYZ-0123456789a";
    bench_wide("nexus: AsciiString<64>::try_from (38B)", || {
        let s = nexus_ascii::AsciiString::<64>::try_from(black_box(long)).unwrap();
        s.len() as u64
    });
    bench_wide("ascii: AsciiString::from_ascii (38B)", || {
        let s = ascii::AsciiString::from_ascii(black_box(long)).unwrap();
        s.len() as u64
    });
    bench_wide("std: String::from (38B)", || {
        let s = String::from(black_box(long));
        s.len() as u64
    });

    // =========================================================================
    // Equality
    // =========================================================================
    println!();
    print_header_wide("EQUALITY (same content)");

    let na: nexus_ascii::AsciiString<16> = nexus_ascii::AsciiString::try_from("BTC-USD").unwrap();
    let nb: nexus_ascii::AsciiString<16> = nexus_ascii::AsciiString::try_from("BTC-USD").unwrap();
    bench_wide("nexus: eq (7B, same)", || {
        black_box(black_box(&na) == black_box(&nb)) as u64
    });

    let aa = ascii::AsciiString::from_ascii("BTC-USD").unwrap();
    let ab = ascii::AsciiString::from_ascii("BTC-USD").unwrap();
    bench_wide("ascii: eq (7B, same)", || {
        black_box(black_box(&aa) == black_box(&ab)) as u64
    });

    let sa = String::from("BTC-USD");
    let sb = String::from("BTC-USD");
    bench_wide("std: eq (7B, same)", || {
        black_box(black_box(&sa) == black_box(&sb)) as u64
    });

    println!();

    let na2: nexus_ascii::AsciiString<16> = nexus_ascii::AsciiString::try_from("BTC-USD").unwrap();
    let nb2: nexus_ascii::AsciiString<16> = nexus_ascii::AsciiString::try_from("ETH-USD").unwrap();
    bench_wide("nexus: eq (7B, different)", || {
        black_box(black_box(&na2) == black_box(&nb2)) as u64
    });

    let aa2 = ascii::AsciiString::from_ascii("BTC-USD").unwrap();
    let ab2 = ascii::AsciiString::from_ascii("ETH-USD").unwrap();
    bench_wide("ascii: eq (7B, different)", || {
        black_box(black_box(&aa2) == black_box(&ab2)) as u64
    });

    let sa2 = String::from("BTC-USD");
    let sb2 = String::from("ETH-USD");
    bench_wide("std: eq (7B, different)", || {
        black_box(black_box(&sa2) == black_box(&sb2)) as u64
    });

    // =========================================================================
    // Case Conversion
    // =========================================================================
    println!();
    print_header_wide("CASE CONVERSION (to_uppercase)");

    // 7B
    let ns7: nexus_ascii::AsciiString<16> = nexus_ascii::AsciiString::try_from("btc-usd").unwrap();
    bench_wide("nexus: to_ascii_uppercase (7B)", || {
        black_box(black_box(&ns7).to_ascii_uppercase()).len() as u64
    });

    let as7 = ascii::AsciiString::from_ascii("btc-usd").unwrap();
    bench_wide("ascii: to_ascii_uppercase (7B)", || {
        let mut s = black_box(&as7).clone();
        s.make_ascii_uppercase();
        black_box(s.len() as u64)
    });

    let mut ss7_buf = String::from("btc-usd");
    bench_wide("std: make_ascii_uppercase (7B, in-place)", || {
        ss7_buf.as_mut_str().make_ascii_uppercase();
        // Reset for next iteration
        // SAFETY: b"btc-usd" is valid UTF-8 and same length as the string.
        unsafe { ss7_buf.as_bytes_mut().copy_from_slice(b"btc-usd") };
        black_box(ss7_buf.len() as u64)
    });

    println!();

    // 20B
    let ns20: nexus_ascii::AsciiString<32> =
        nexus_ascii::AsciiString::try_from("order-id-abcdefghij").unwrap();
    bench_wide("nexus: to_ascii_uppercase (20B)", || {
        black_box(black_box(&ns20).to_ascii_uppercase()).len() as u64
    });

    let as20 = ascii::AsciiString::from_ascii("order-id-abcdefghij").unwrap();
    bench_wide("ascii: to_ascii_uppercase (20B)", || {
        let mut s = black_box(&as20).clone();
        s.make_ascii_uppercase();
        black_box(s.len() as u64)
    });

    let mut ss20_buf = String::from("order-id-abcdefghij");
    bench_wide("std: make_ascii_uppercase (20B, in-place)", || {
        ss20_buf.as_mut_str().make_ascii_uppercase();
        // SAFETY: b"order-id-abcdefghij" is valid UTF-8 and same length as the string.
        unsafe {
            ss20_buf
                .as_bytes_mut()
                .copy_from_slice(b"order-id-abcdefghij");
        }
        black_box(ss20_buf.len() as u64)
    });

    println!();

    // 38B
    let ns38: nexus_ascii::AsciiString<64> =
        nexus_ascii::AsciiString::try_from("abcdefghijklmnopqrstuvwxyz-0123456789a").unwrap();
    bench_wide("nexus: to_ascii_uppercase (38B)", || {
        black_box(black_box(&ns38).to_ascii_uppercase()).len() as u64
    });

    let as38 = ascii::AsciiString::from_ascii("abcdefghijklmnopqrstuvwxyz-0123456789a").unwrap();
    bench_wide("ascii: to_ascii_uppercase (38B)", || {
        let mut s = black_box(&as38).clone();
        s.make_ascii_uppercase();
        black_box(s.len() as u64)
    });

    let mut ss38_buf = String::from("abcdefghijklmnopqrstuvwxyz-0123456789a");
    bench_wide("std: make_ascii_uppercase (38B, in-place)", || {
        ss38_buf.as_mut_str().make_ascii_uppercase();
        // SAFETY: replacement is valid UTF-8 and same length as the original string.
        unsafe {
            ss38_buf
                .as_bytes_mut()
                .copy_from_slice(b"abcdefghijklmnopqrstuvwxyz-0123456789a");
        }
        black_box(ss38_buf.len() as u64)
    });

    // =========================================================================
    // Case-Insensitive Comparison
    // =========================================================================
    println!();
    print_header_wide("CASE-INSENSITIVE COMPARISON");

    let na_upper: nexus_ascii::AsciiString<16> =
        nexus_ascii::AsciiString::try_from("BTC-USD").unwrap();
    let na_lower: nexus_ascii::AsciiString<16> =
        nexus_ascii::AsciiString::try_from("btc-usd").unwrap();
    bench_wide("nexus: eq_ignore_ascii_case (7B)", || {
        black_box(black_box(&na_upper).eq_ignore_ascii_case(black_box(&na_lower))) as u64
    });

    let aa_upper = ascii::AsciiString::from_ascii("BTC-USD").unwrap();
    let aa_lower = ascii::AsciiString::from_ascii("btc-usd").unwrap();
    bench_wide("ascii: eq_ignore_ascii_case (7B)", || {
        black_box(
            black_box(aa_upper.as_ref() as &ascii::AsciiStr)
                .eq_ignore_ascii_case(black_box(aa_lower.as_ref())),
        ) as u64
    });

    bench_wide("std: eq_ignore_ascii_case (7B)", || {
        black_box(black_box("BTC-USD").eq_ignore_ascii_case(black_box("btc-usd"))) as u64
    });

    println!();

    // 38B
    let long_upper = "ABCDEFGHIJKLMNOPQRSTUVWXYZ-0123456789A";
    let long_lower = "abcdefghijklmnopqrstuvwxyz-0123456789a";

    let na38_upper: nexus_ascii::AsciiString<64> =
        nexus_ascii::AsciiString::try_from(long_upper).unwrap();
    let na38_lower: nexus_ascii::AsciiString<64> =
        nexus_ascii::AsciiString::try_from(long_lower).unwrap();
    bench_wide("nexus: eq_ignore_ascii_case (38B)", || {
        black_box(black_box(&na38_upper).eq_ignore_ascii_case(black_box(&na38_lower))) as u64
    });

    let aa38_upper = ascii::AsciiString::from_ascii(long_upper).unwrap();
    let aa38_lower = ascii::AsciiString::from_ascii(long_lower).unwrap();
    bench_wide("ascii: eq_ignore_ascii_case (38B)", || {
        black_box(
            black_box(aa38_upper.as_ref() as &ascii::AsciiStr)
                .eq_ignore_ascii_case(black_box(aa38_lower.as_ref())),
        ) as u64
    });

    bench_wide("std: eq_ignore_ascii_case (38B)", || {
        black_box(black_box(long_upper).eq_ignore_ascii_case(black_box(long_lower))) as u64
    });

    // =========================================================================
    // Ordering (cmp)
    // =========================================================================
    println!();
    print_header_wide("ORDERING (cmp)");

    let na_cmp1: nexus_ascii::AsciiString<16> =
        nexus_ascii::AsciiString::try_from("BTC-USD").unwrap();
    let na_cmp2: nexus_ascii::AsciiString<16> =
        nexus_ascii::AsciiString::try_from("ETH-USD").unwrap();
    bench_wide("nexus: cmp (7B, different)", || {
        black_box(black_box(&na_cmp1).cmp(black_box(&na_cmp2))) as u64
    });

    let aa_cmp1 = ascii::AsciiString::from_ascii("BTC-USD").unwrap();
    let aa_cmp2 = ascii::AsciiString::from_ascii("ETH-USD").unwrap();
    bench_wide("ascii: cmp (7B, different)", || {
        black_box(black_box(&aa_cmp1).cmp(black_box(&aa_cmp2))) as u64
    });

    let sa_cmp1 = String::from("BTC-USD");
    let sa_cmp2 = String::from("ETH-USD");
    bench_wide("std: cmp (7B, different)", || {
        black_box(black_box(&sa_cmp1).cmp(black_box(&sa_cmp2))) as u64
    });

    // =========================================================================
    // HashMap Lookup
    // =========================================================================
    println!();
    print_header_wide("HASHMAP LOOKUP (100 entries)");

    // nexus-ascii with default hasher
    let mut nmap: std::collections::HashMap<nexus_ascii::AsciiString<32>, u64> =
        std::collections::HashMap::new();
    for i in 0..100u64 {
        let key =
            nexus_ascii::AsciiString::<32>::try_from(format!("key-{:04}", i).as_str()).unwrap();
        nmap.insert(key, i);
    }
    let nkey = nexus_ascii::AsciiString::<32>::try_from("key-0050").unwrap();
    bench_wide("nexus: HashMap::get (default hasher)", || {
        black_box(*black_box(&nmap).get(black_box(&nkey)).unwrap())
    });

    // ascii crate
    let mut amap: std::collections::HashMap<ascii::AsciiString, u64> =
        std::collections::HashMap::new();
    for i in 0..100u64 {
        let key = ascii::AsciiString::from_ascii(format!("key-{:04}", i)).unwrap();
        amap.insert(key, i);
    }
    let akey = ascii::AsciiString::from_ascii("key-0050").unwrap();
    bench_wide("ascii: HashMap::get (default hasher)", || {
        black_box(*black_box(&amap).get(black_box(&akey)).unwrap())
    });

    // std String
    let mut smap: std::collections::HashMap<String, u64> = std::collections::HashMap::new();
    for i in 0..100u64 {
        smap.insert(format!("key-{:04}", i), i);
    }
    let skey = String::from("key-0050");
    bench_wide("std: HashMap::get (default hasher)", || {
        black_box(*black_box(&smap).get(black_box(&skey)).unwrap())
    });

    println!();
}
