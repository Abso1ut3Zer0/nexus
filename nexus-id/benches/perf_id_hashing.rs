//! Hash performance benchmark: Snowflake IDs
//!
//! Tests hash distribution quality and HashMap performance.
//!
//! Run with:
//! ```sh
//! cargo build --release --example perf_hash
//! ./target/release/examples/perf_hash
//! ```

use hdrhistogram::Histogram;
use nexus_id::Snowflake64;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::hint::black_box;

const N_IDS: usize = 100_000;
const LOOKUP_OPS: usize = 1_000_000;
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

// ============================================================================
// Identity hasher - exposes raw distribution of the IDs themselves
// ============================================================================

#[derive(Default)]
struct IdentityHasher(u64);

impl Hasher for IdentityHasher {
    fn write(&mut self, _bytes: &[u8]) {
        panic!("IdentityHasher only supports u64");
    }

    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

// ============================================================================
// Generate IDs
// ============================================================================

fn generate_snowflake_ids(n: usize) -> Vec<u64> {
    type Id = Snowflake64<42, 6, 16>;
    let mut id_gen = Id::new(0);

    (0..n)
        .map(|i| {
            // Advance timestamp every 1000 IDs to avoid sequence exhaustion
            let ts = (i / 1000) as u64;
            id_gen.next(ts).unwrap()
        })
        .collect()
}

fn generate_sequential_ids(n: usize) -> Vec<u64> {
    (0..n as u64).collect()
}

// ============================================================================
// Bit distribution analysis
// ============================================================================

fn analyze_bits(ids: &[u64], name: &str) {
    let mut bit_counts = [0usize; 64];

    for &id in ids {
        for bit in 0..64 {
            if (id >> bit) & 1 == 1 {
                bit_counts[bit] += 1;
            }
        }
    }

    let mut min_ratio = 1.0f64;
    let mut max_ratio = 0.0f64;
    let mut worst_bit = 0;

    for (bit, &count) in bit_counts.iter().enumerate() {
        let ratio = count as f64 / ids.len() as f64;
        if ratio < min_ratio {
            min_ratio = ratio;
            worst_bit = bit;
        }
        if ratio > max_ratio {
            max_ratio = ratio;
        }
    }

    // Check low bits specifically (most important for hash tables)
    let low_8_avg: f64 = bit_counts[0..8]
        .iter()
        .map(|&c| c as f64 / ids.len() as f64)
        .sum::<f64>()
        / 8.0;

    println!(
        "  {:<12} min={:.4} max={:.4} worst_bit={:>2}  low8_avg={:.4}",
        name, min_ratio, max_ratio, worst_bit, low_8_avg
    );
}

// ============================================================================
// Bucket distribution analysis
// ============================================================================

fn analyze_buckets(ids: &[u64], name: &str, n_buckets: usize) {
    let mut buckets = vec![0usize; n_buckets];

    for &id in ids {
        let bucket = (id as usize) % n_buckets;
        buckets[bucket] += 1;
    }

    let expected = ids.len() as f64 / n_buckets as f64;
    let min = *buckets.iter().min().unwrap();
    let max = *buckets.iter().max().unwrap();

    // Chi-squared test
    let chi_squared: f64 = buckets
        .iter()
        .map(|&c| (c as f64 - expected).powi(2) / expected)
        .sum();

    println!(
        "  {:<12} expected={:>5.1}  min={:>5}  max={:>5}  χ²={:>12.2}",
        name, expected, min, max, chi_squared
    );
}

// ============================================================================
// Benchmark: HashMap lookup latency
// ============================================================================

fn bench_lookup_latency<S: std::hash::BuildHasher + Default>(
    ids: &[u64],
    hasher_name: &str,
    id_name: &str,
) {
    // Build map first
    let mut map: HashMap<u64, u64, S> = HashMap::with_hasher(S::default());
    for (i, &id) in ids.iter().enumerate() {
        map.insert(id, i as u64);
    }

    let mut hist = Histogram::<u64>::new(3).unwrap();

    // Warmup
    for &id in ids.iter().cycle().take(WARMUP) {
        black_box(map.get(&id));
    }

    // Benchmark: random-access lookups
    for &id in ids.iter().cycle().take(LOOKUP_OPS) {
        let start = rdtscp();
        let val = map.get(&id);
        let end = rdtscp();

        black_box(val);
        let _ = hist.record(end.wrapping_sub(start));
    }

    println!(
        "  {:<12} + {:<10} p50={:>4}  p99={:>4}  p999={:>5}",
        id_name,
        hasher_name,
        hist.value_at_quantile(0.50),
        hist.value_at_quantile(0.99),
        hist.value_at_quantile(0.999),
    );
}

// ============================================================================
// Benchmark: HashMap insert throughput
// ============================================================================

fn bench_insert_throughput<S: std::hash::BuildHasher + Default + Clone>(
    ids: &[u64],
    hasher_name: &str,
    id_name: &str,
) {
    let hasher = S::default();

    // Warmup
    for _ in 0..10 {
        let mut map: HashMap<u64, u64, S> = HashMap::with_hasher(hasher.clone());
        for (i, &id) in ids.iter().enumerate() {
            map.insert(id, i as u64);
        }
        black_box(&map);
    }

    // Benchmark: time to insert all IDs
    let mut times = Vec::with_capacity(100);
    for _ in 0..100 {
        let mut map: HashMap<u64, u64, S> = HashMap::with_hasher(hasher.clone());
        map.reserve(ids.len());

        let start = rdtscp();
        for (i, &id) in ids.iter().enumerate() {
            map.insert(id, i as u64);
        }
        let end = rdtscp();

        black_box(&map);
        times.push(end.wrapping_sub(start));
    }

    times.sort_unstable();
    let p50 = times[50];
    let cycles_per_insert = p50 / ids.len() as u64;

    println!(
        "  {:<12} + {:<10} total_cycles={:>12}  cycles/insert={:>4}",
        id_name, hasher_name, p50, cycles_per_insert
    );
}

fn main() {
    println!("HASH PERFORMANCE BENCHMARK");
    println!("IDs: {}, Lookups: {}", N_IDS, LOOKUP_OPS);
    println!("================================================================\n");

    // Generate IDs
    println!("Generating IDs...");
    let snowflake_ids = generate_snowflake_ids(N_IDS);
    let sequential_ids = generate_sequential_ids(N_IDS);
    println!("Done.\n");

    // ========================================================================
    println!("BIT DISTRIBUTION (ideal = 0.5000 for all bits):");
    println!("----------------------------------------------------------------");
    analyze_bits(&snowflake_ids, "Snowflake");
    analyze_bits(&sequential_ids, "Sequential");

    // ========================================================================
    println!("\nBUCKET DISTRIBUTION (lower χ² = more uniform):");
    println!("----------------------------------------------------------------");

    println!("\n  1024 buckets:");
    analyze_buckets(&snowflake_ids, "Snowflake", 1024);
    analyze_buckets(&sequential_ids, "Sequential", 1024);

    println!("\n  65536 buckets:");
    analyze_buckets(&snowflake_ids, "Snowflake", 65536);
    analyze_buckets(&sequential_ids, "Sequential", 65536);

    // ========================================================================
    println!("\n================================================================");
    println!("HASHMAP LOOKUP LATENCY (cycles per lookup):");
    println!("----------------------------------------------------------------");

    println!("\n  Identity hasher (raw ID distribution):");
    bench_lookup_latency::<BuildHasherDefault<IdentityHasher>>(
        &snowflake_ids,
        "Identity",
        "Snowflake",
    );
    bench_lookup_latency::<BuildHasherDefault<IdentityHasher>>(
        &sequential_ids,
        "Identity",
        "Sequential",
    );

    println!("\n  FxHash (rustc's hasher):");
    bench_lookup_latency::<rustc_hash::FxBuildHasher>(&snowflake_ids, "FxHash", "Snowflake");
    bench_lookup_latency::<rustc_hash::FxBuildHasher>(&sequential_ids, "FxHash", "Sequential");

    println!("\n  AHash (fast, DoS-resistant):");
    bench_lookup_latency::<ahash::RandomState>(&snowflake_ids, "AHash", "Snowflake");
    bench_lookup_latency::<ahash::RandomState>(&sequential_ids, "AHash", "Sequential");

    // ========================================================================
    println!("\n================================================================");
    println!("HASHMAP INSERT THROUGHPUT:");
    println!("----------------------------------------------------------------");

    println!("\n  Identity hasher:");
    bench_insert_throughput::<BuildHasherDefault<IdentityHasher>>(
        &snowflake_ids,
        "Identity",
        "Snowflake",
    );
    bench_insert_throughput::<BuildHasherDefault<IdentityHasher>>(
        &sequential_ids,
        "Identity",
        "Sequential",
    );

    println!("\n  FxHash:");
    bench_insert_throughput::<rustc_hash::FxBuildHasher>(&snowflake_ids, "FxHash", "Snowflake");
    bench_insert_throughput::<rustc_hash::FxBuildHasher>(&sequential_ids, "FxHash", "Sequential");

    println!("\n================================================================");
    println!("INTERPRETATION:");
    println!("- Identity hasher exposes raw ID distribution quality");
    println!("- FxHash/AHash should equalize performance across ID types");
    println!("- Sequential IDs: worst case for identity, fine with real hashers");
}
