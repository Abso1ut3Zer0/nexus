#![allow(unused_must_use)]
//! Comprehensive benchmark for nexus-id newtypes, parsing, encoding, and TypeId.
//!
//! Measures cycle-accurate latency for:
//! - Snowflake ID newtype operations (next_id, next_mixed, mix, unmix, unpack)
//! - String parsing (Uuid, UuidCompact, Ulid, HexId64, Base62Id, Base36Id)
//! - String encoding (hex, base62, base36, uuid_dashed, ulid_encode)
//! - TypeId construction and parsing
//!
//! Run with:
//! ```bash
//! # Disable turbo boost for consistent results
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//!
//! # Pin to a single core
//! cargo build --release --example perf_benchmark
//! sudo taskset -c 2 ./target/release/examples/perf_benchmark
//!
//! # Re-enable turbo
//! echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! ```

use hdrhistogram::Histogram;
use nexus_id::ulid::UlidGenerator;
use nexus_id::{
    Base36Id, Base62Id, HexId64, Snowflake64, SnowflakeId64, TypeId, Ulid, Uuid, UuidCompact,
};
use std::hint::black_box;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const OPERATIONS: usize = 1_000_000;
const WARMUP: usize = 10_000;

#[inline(always)]
fn rdtscp() -> u64 {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: x86_64 intrinsic; block is only compiled for x86_64.
    unsafe {
        let mut aux: u32 = 0;
        std::arch::x86_64::__rdtscp(&raw mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        std::time::Instant::now().elapsed().as_nanos() as u64
    }
}

fn print_stats(name: &str, hist: &Histogram<u64>) {
    println!(
        "  {:<35} p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}",
        name,
        hist.value_at_quantile(0.50),
        hist.value_at_quantile(0.99),
        hist.value_at_quantile(0.999),
        hist.max(),
    );
}

// =============================================================================
// Snowflake ID Newtypes
// =============================================================================

fn bench_next_id() -> Histogram<u64> {
    type Id = Snowflake64<42, 6, 16>;
    let mut generator = Id::new(5);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup
    for i in 0..WARMUP {
        let _ = black_box(generator.next_id(i as u64));
    }

    generator = Id::new(5);

    // Benchmark: each call advances 1 (new timestamp path)
    for i in 0..OPERATIONS {
        let ts = WARMUP as u64 + i as u64;
        let start = rdtscp();
        let id = generator.next_id(ts);
        let end = rdtscp();
        black_box(id);
        if id.is_ok() {
            let _ = hist.record(end.wrapping_sub(start));
        }
    }

    hist
}

fn bench_next_mixed() -> Histogram<u64> {
    type Id = Snowflake64<42, 6, 16>;
    let mut generator = Id::new(5);
    let mut hist = Histogram::new(3).unwrap();

    for i in 0..WARMUP {
        let _ = black_box(generator.next_mixed(i as u64));
    }

    generator = Id::new(5);

    for i in 0..OPERATIONS {
        let ts = WARMUP as u64 + i as u64;
        let start = rdtscp();
        let id = generator.next_mixed(ts);
        let end = rdtscp();
        black_box(id);
        if id.is_ok() {
            let _ = hist.record(end.wrapping_sub(start));
        }
    }

    hist
}

fn bench_mix() -> Histogram<u64> {
    let id = SnowflakeId64::<42, 6, 16>::from_raw(0xDEAD_BEEF_CAFE_0001);
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(id.mixed());
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let mixed = id.mixed();
        let end = rdtscp();
        black_box(mixed);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_unmix() -> Histogram<u64> {
    let id = SnowflakeId64::<42, 6, 16>::from_raw(0xDEAD_BEEF_CAFE_0001);
    let mixed = id.mixed();
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(mixed.unmix());
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let recovered = mixed.unmix();
        let end = rdtscp();
        black_box(recovered);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_unpack() -> Histogram<u64> {
    let id = SnowflakeId64::<42, 6, 16>::from_raw(0xDEAD_BEEF_CAFE_0001);
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(id.unpack());
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let parts = id.unpack();
        let end = rdtscp();
        black_box(parts);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

// =============================================================================
// String Parsing
// =============================================================================

fn bench_parse_uuid() -> Histogram<u64> {
    let input = "01234567-89ab-cdef-fedc-ba9876543210";
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(Uuid::<40>::parse(input));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = Uuid::<40>::parse(black_box(input));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_parse_uuid_compact() -> Histogram<u64> {
    let input = "0123456789abcdeffedcba9876543210";
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(UuidCompact::<32>::parse(input));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = UuidCompact::<32>::parse(black_box(input));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_parse_ulid() -> Histogram<u64> {
    let input = "01ARZ3NDEKTSV4RRFFQ69G5FAV";
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(Ulid::<32>::parse(input));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = Ulid::<32>::parse(black_box(input));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_parse_hex64() -> Histogram<u64> {
    let input = "deadbeefcafebabe";
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(HexId64::<16>::parse(input));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = HexId64::<16>::parse(black_box(input));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_parse_base62() -> Histogram<u64> {
    let input = "00000000dS8";
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(Base62Id::<16>::parse(input));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = Base62Id::<16>::parse(black_box(input));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_parse_base36() -> Histogram<u64> {
    let input = "0000000000009";
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(Base36Id::<16>::parse(input));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = Base36Id::<16>::parse(black_box(input));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

// =============================================================================
// String Encoding
// =============================================================================

fn bench_encode_hex() -> Histogram<u64> {
    let val = 0xDEAD_BEEF_CAFE_BABEu64;
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(HexId64::<16>::encode(val));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = HexId64::<16>::encode(black_box(val));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_encode_base62() -> Histogram<u64> {
    let val = 0xDEAD_BEEF_CAFE_BABEu64;
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(Base62Id::<16>::encode(val));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = Base62Id::<16>::encode(black_box(val));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_encode_base36() -> Histogram<u64> {
    let val = 0xDEAD_BEEF_CAFE_BABEu64;
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(Base36Id::<16>::encode(val));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = Base36Id::<16>::encode(black_box(val));
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_encode_to_hex() -> Histogram<u64> {
    let id = SnowflakeId64::<42, 6, 16>::from_raw(0xDEAD_BEEF_CAFE_0001);
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(id.to_hex());
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let hex = id.to_hex();
        let end = rdtscp();
        black_box(hex);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_encode_to_base62() -> Histogram<u64> {
    let id = SnowflakeId64::<42, 6, 16>::from_raw(0xDEAD_BEEF_CAFE_0001);
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(id.to_base62());
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let b62 = id.to_base62();
        let end = rdtscp();
        black_box(b62);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

// =============================================================================
// TypeId
// =============================================================================

fn bench_typeid_new() -> Histogram<u64> {
    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let mut generator = UlidGenerator::new(epoch, unix_base, 42);
    let mut hist = Histogram::new(3).unwrap();

    // Pre-generate ULIDs
    let ulids: Vec<Ulid> = (0..WARMUP + OPERATIONS)
        .map(|i| {
            let now = epoch + Duration::from_millis(i as u64);
            generator.next(now)
        })
        .collect();

    for i in 0..WARMUP {
        black_box(TypeId::<32>::new("user", ulids[i]));
    }

    for i in 0..OPERATIONS {
        let start = rdtscp();
        let id = TypeId::<32>::new("user", ulids[WARMUP + i]);
        let end = rdtscp();
        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_typeid_parse() -> Histogram<u64> {
    // Generate a valid TypeId string to parse
    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let mut generator = UlidGenerator::new(epoch, unix_base, 42);
    let ulid = generator.next(epoch);
    let id = TypeId::<32>::new("user", ulid).unwrap();
    let input = id.as_str();
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(TypeId::<32>::parse(input));
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let parsed = TypeId::<32>::parse(black_box(input));
        let end = rdtscp();
        black_box(parsed);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_typeid_prefix() -> Histogram<u64> {
    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let mut generator = UlidGenerator::new(epoch, unix_base, 42);
    let ulid = generator.next(epoch);
    let id = TypeId::<32>::new("user", ulid).unwrap();
    let mut hist = Histogram::new(3).unwrap();

    for _ in 0..WARMUP {
        black_box(id.prefix());
    }

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let prefix = id.prefix();
        let end = rdtscp();
        black_box(prefix);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

// =============================================================================
// Snowflake ID -> String conversions (combined generate + encode)
// =============================================================================

fn bench_generate_and_encode_hex() -> Histogram<u64> {
    type Id = Snowflake64<42, 6, 16>;
    let mut generator = Id::new(5);
    let mut hist = Histogram::new(3).unwrap();

    for i in 0..WARMUP {
        if let Ok(id) = generator.next_id(i as u64) {
            black_box(id.to_hex());
        }
    }

    generator = Id::new(5);

    for i in 0..OPERATIONS {
        let ts = WARMUP as u64 + i as u64;
        let start = rdtscp();
        let id = generator.next_id(ts).unwrap();
        let hex = id.to_hex();
        let end = rdtscp();
        black_box(hex);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_generate_and_encode_base62() -> Histogram<u64> {
    type Id = Snowflake64<42, 6, 16>;
    let mut generator = Id::new(5);
    let mut hist = Histogram::new(3).unwrap();

    for i in 0..WARMUP {
        if let Ok(id) = generator.next_id(i as u64) {
            black_box(id.to_base62());
        }
    }

    generator = Id::new(5);

    for i in 0..OPERATIONS {
        let ts = WARMUP as u64 + i as u64;
        let start = rdtscp();
        let id = generator.next_id(ts).unwrap();
        let b62 = id.to_base62();
        let end = rdtscp();
        black_box(b62);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

// =============================================================================
// Mix/Unmix with HashMap simulation
// =============================================================================

fn bench_mix_for_hashmap() -> Histogram<u64> {
    // Simulate: generate ID, mix it, use as key
    type Id = Snowflake64<42, 6, 16>;
    let mut generator = Id::new(5);
    let mut hist = Histogram::new(3).unwrap();

    for i in 0..WARMUP {
        if let Ok(id) = generator.next_id(i as u64) {
            black_box(id.mixed());
        }
    }

    generator = Id::new(5);

    for i in 0..OPERATIONS {
        let ts = WARMUP as u64 + i as u64;
        let start = rdtscp();
        let id = generator.next_id(ts).unwrap();
        let mixed = id.mixed();
        let end = rdtscp();
        black_box(mixed);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

// =============================================================================
// Main
// =============================================================================

fn main() {
    println!("NEXUS-ID COMPREHENSIVE BENCHMARK");
    println!("Operations: {}, Warmup: {}", OPERATIONS, WARMUP);
    println!("All times in CPU cycles");
    println!("================================================================\n");

    // -- Snowflake ID Newtypes --
    println!("SNOWFLAKE ID NEWTYPES:");
    println!("----------------------------------------------------------------");
    print_stats("next_id() [new ts each]", &bench_next_id());
    print_stats("next_mixed() [new ts each]", &bench_next_mixed());
    print_stats("mix() [isolated]", &bench_mix());
    print_stats("unmix() [isolated]", &bench_unmix());
    print_stats("unpack() [isolated]", &bench_unpack());

    println!();

    // -- String Parsing --
    println!("STRING PARSING:");
    println!("----------------------------------------------------------------");
    print_stats("Uuid::parse(36-char)", &bench_parse_uuid());
    print_stats("UuidCompact::parse(32-char)", &bench_parse_uuid_compact());
    print_stats("Ulid::parse(26-char)", &bench_parse_ulid());
    print_stats("HexId64::parse(16-char)", &bench_parse_hex64());
    print_stats("Base62Id::parse(11-char)", &bench_parse_base62());
    print_stats("Base36Id::parse(13-char)", &bench_parse_base36());

    println!();

    // -- String Encoding --
    println!("STRING ENCODING:");
    println!("----------------------------------------------------------------");
    print_stats("HexId64::encode(u64)", &bench_encode_hex());
    print_stats("Base62Id::encode(u64)", &bench_encode_base62());
    print_stats("Base36Id::encode(u64)", &bench_encode_base36());
    print_stats("SnowflakeId64::to_hex()", &bench_encode_to_hex());
    print_stats("SnowflakeId64::to_base62()", &bench_encode_to_base62());

    println!();

    // -- TypeId --
    println!("TYPEID:");
    println!("----------------------------------------------------------------");
    print_stats("TypeId::new(\"user\", ulid)", &bench_typeid_new());
    print_stats("TypeId::parse(\"user_...\")", &bench_typeid_parse());
    print_stats("TypeId::prefix()", &bench_typeid_prefix());

    println!();

    // -- Combined Operations --
    println!("COMBINED OPERATIONS (generate + encode):");
    println!("----------------------------------------------------------------");
    print_stats("next_id() + to_hex()", &bench_generate_and_encode_hex());
    print_stats(
        "next_id() + to_base62()",
        &bench_generate_and_encode_base62(),
    );
    print_stats("next_id() + mixed()", &bench_mix_for_hashmap());

    println!();
    println!("================================================================");

    // Summary table
    let mix_h = bench_mix();
    let unmix_h = bench_unmix();
    let unpack_h = bench_unpack();
    let hex_enc = bench_encode_hex();
    let b62_enc = bench_encode_base62();
    let uuid_parse = bench_parse_uuid();
    let ulid_parse = bench_parse_ulid();

    println!("SUMMARY (p50 cycles):");
    println!("----------------------------------------------------------------");
    println!(
        "  mix():            {:>4}   (Fibonacci multiply)",
        mix_h.value_at_quantile(0.50)
    );
    println!(
        "  unmix():          {:>4}   (inverse multiply)",
        unmix_h.value_at_quantile(0.50)
    );
    println!(
        "  unpack():         {:>4}   (3 shifts + masks)",
        unpack_h.value_at_quantile(0.50)
    );
    println!(
        "  hex encode:       {:>4}   (table lookup)",
        hex_enc.value_at_quantile(0.50)
    );
    println!(
        "  base62 encode:    {:>4}   (division chain)",
        b62_enc.value_at_quantile(0.50)
    );
    println!(
        "  UUID parse:       {:>4}   (36-char validate+decode)",
        uuid_parse.value_at_quantile(0.50)
    );
    println!(
        "  ULID parse:       {:>4}   (26-char Crockford)",
        ulid_parse.value_at_quantile(0.50)
    );
}
