//! UUID and ULID benchmark: ID generation latency measurement
//!
//! Measures cycle-accurate latency for UUID v4, v7, and ULID generation.
//!
//! Run with:
//! ```bash
//! # Disable turbo boost for consistent results
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//!
//! # Pin to a single core
//! cargo build --release --example perf_uuid
//! sudo taskset -c 2 ./target/release/examples/perf_uuid
//! ```

use hdrhistogram::Histogram;
use nexus_id::ulid::UlidGenerator;
use nexus_id::uuid::{UuidV4, UuidV7};
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
        // Fallback for non-x86
        std::time::Instant::now().elapsed().as_nanos() as u64
    }
}

fn print_stats(name: &str, hist: &Histogram<u64>) {
    println!(
        "  {:<30} p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}",
        name,
        hist.value_at_quantile(0.50),
        hist.value_at_quantile(0.99),
        hist.value_at_quantile(0.999),
        hist.max(),
    );
}

fn bench_uuid_v4_raw() -> Histogram<u64> {
    let mut generator = UuidV4::new(12345);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup
    for _ in 0..WARMUP {
        let _ = black_box(generator.next_raw());
    }

    // Benchmark
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = generator.next_raw();
        let end = rdtscp();

        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_uuid_v4_formatted() -> Histogram<u64> {
    let mut generator = UuidV4::new(12345);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup
    for _ in 0..WARMUP {
        let _ = black_box(generator.next());
    }

    // Benchmark
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = generator.next();
        let end = rdtscp();

        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_uuid_v4_compact() -> Histogram<u64> {
    let mut generator = UuidV4::new(12345);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup
    for _ in 0..WARMUP {
        let _ = black_box(generator.next_compact());
    }

    // Benchmark
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = generator.next_compact();
        let end = rdtscp();

        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_uuid_v7_raw() -> Histogram<u64> {
    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;

    let mut generator = UuidV7::new(epoch, unix_base, 12345);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup - use varying timestamps to exercise both paths
    for i in 0..WARMUP {
        let now = epoch + Duration::from_micros((i / 100) as u64 * 1000);
        let _ = black_box(generator.next_raw(now));
    }

    // Reset generator
    generator = UuidV7::new(epoch, unix_base, 12345);

    // Benchmark same-timestamp path (sequence increment)
    let now = epoch + Duration::from_millis(1000);
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = generator.next_raw(now);
        let end = rdtscp();

        let _ = black_box(id);
        if id.is_ok() {
            let _ = hist.record(end.wrapping_sub(start));
        }
    }

    hist
}

fn bench_uuid_v7_formatted() -> Histogram<u64> {
    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;

    let mut generator = UuidV7::new(epoch, unix_base, 12345);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup
    for i in 0..WARMUP {
        let now = epoch + Duration::from_micros((i / 100) as u64 * 1000);
        let _ = black_box(generator.next(now));
    }

    // Reset
    generator = UuidV7::new(epoch, unix_base, 12345);

    // Benchmark
    let now = epoch + Duration::from_millis(1000);
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = generator.next(now);
        let end = rdtscp();

        let _ = black_box(id);
        if id.is_ok() {
            let _ = hist.record(end.wrapping_sub(start));
        }
    }

    hist
}

fn bench_uuid_v7_new_timestamp() -> Histogram<u64> {
    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;

    let mut generator = UuidV7::new(epoch, unix_base, 12345);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup
    for i in 0..WARMUP {
        let now = epoch + Duration::from_millis(i as u64);
        let _ = black_box(generator.next(now));
    }

    // Reset
    generator = UuidV7::new(epoch, unix_base, 12345);

    // Benchmark new-timestamp path (each call advances 1ms)
    for i in 0..OPERATIONS {
        let now = epoch + Duration::from_millis(WARMUP as u64 + i as u64);

        let start = rdtscp();
        let id = generator.next(now);
        let end = rdtscp();

        let _ = black_box(id);
        if id.is_ok() {
            let _ = hist.record(end.wrapping_sub(start));
        }
    }

    hist
}

fn bench_ulid_same_ms() -> Histogram<u64> {
    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;

    let mut generator = UlidGenerator::new(epoch, unix_base, 12345);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup
    for i in 0..WARMUP {
        let now = epoch + Duration::from_micros((i / 100) as u64 * 1000);
        let _ = black_box(generator.next(now));
    }

    // Reset
    let mut generator = UlidGenerator::new(epoch, unix_base, 12345);

    // Benchmark same-timestamp path (monotonic increment)
    let now = epoch + Duration::from_millis(1000);
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let id = generator.next(now);
        let end = rdtscp();

        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_ulid_new_ms() -> Histogram<u64> {
    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;

    let mut generator = UlidGenerator::new(epoch, unix_base, 12345);
    let mut hist = Histogram::new(3).unwrap();

    // Warmup
    for i in 0..WARMUP {
        let now = epoch + Duration::from_millis(i as u64);
        let _ = black_box(generator.next(now));
    }

    // Reset
    let mut generator = UlidGenerator::new(epoch, unix_base, 12345);

    // Benchmark new-timestamp path
    for i in 0..OPERATIONS {
        let now = epoch + Duration::from_millis(WARMUP as u64 + i as u64);

        let start = rdtscp();
        let id = generator.next(now);
        let end = rdtscp();

        black_box(id);
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn main() {
    println!("UUID AND ULID BENCHMARK");
    println!("Operations: {}, Warmup: {}", OPERATIONS, WARMUP);
    println!("================================================================\n");

    println!("UUID v4 (random):");
    print_stats("next_raw() (hi, lo)", &bench_uuid_v4_raw());
    print_stats("next() dashed format", &bench_uuid_v4_formatted());
    print_stats("next_compact() no dashes", &bench_uuid_v4_compact());

    println!();
    println!("UUID v7 (timestamp + random):");
    print_stats("next_raw() same timestamp", &bench_uuid_v7_raw());
    print_stats("next() same timestamp", &bench_uuid_v7_formatted());
    print_stats("next() new timestamp each", &bench_uuid_v7_new_timestamp());

    println!();
    println!("ULID (timestamp + random, Crockford Base32):");
    print_stats("next() same timestamp", &bench_ulid_same_ms());
    print_stats("next() new timestamp each", &bench_ulid_new_ms());

    println!();
    println!("================================================================");
    println!("COMPARISON (cycles):");
    println!("----------------------------------------------------------------");

    let v4_raw = bench_uuid_v4_raw();
    let v4_fmt = bench_uuid_v4_formatted();
    let v7_raw = bench_uuid_v7_raw();
    let v7_fmt = bench_uuid_v7_formatted();
    let ulid = bench_ulid_same_ms();

    println!("              v4 raw    v4 fmt   v7 raw   v7 fmt    ULID");
    println!(
        "  p50:          {:>4}      {:>4}     {:>4}     {:>4}     {:>4}",
        v4_raw.value_at_quantile(0.50),
        v4_fmt.value_at_quantile(0.50),
        v7_raw.value_at_quantile(0.50),
        v7_fmt.value_at_quantile(0.50),
        ulid.value_at_quantile(0.50),
    );
    println!(
        "  p99:          {:>4}      {:>4}     {:>4}     {:>4}     {:>4}",
        v4_raw.value_at_quantile(0.99),
        v4_fmt.value_at_quantile(0.99),
        v7_raw.value_at_quantile(0.99),
        v7_fmt.value_at_quantile(0.99),
        ulid.value_at_quantile(0.99),
    );
    println!(
        "  p999:         {:>4}      {:>4}     {:>4}     {:>4}     {:>4}",
        v4_raw.value_at_quantile(0.999),
        v4_fmt.value_at_quantile(0.999),
        v7_raw.value_at_quantile(0.999),
        v7_fmt.value_at_quantile(0.999),
        ulid.value_at_quantile(0.999),
    );

    println!();
    println!("NOTE: 'raw' = (u64, u64) output, 'fmt' = AsciiString<36>");
    println!("      ULID outputs 26-char Crockford Base32");
    println!("      v7/ULID 'same timestamp' tests monotonic increment path");
}
