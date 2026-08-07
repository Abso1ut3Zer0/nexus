//! Hash function performance benchmark.
//!
//! Benchmarks the unified `hash<CAP>` function which automatically selects
//! the best XXH3 implementation based on compile-time target features.
//!
//! Run with:
//! ```bash
//! # Disable turbo boost for consistent results
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//!
//! # Build and run (default: SSE2 on x86_64, scalar elsewhere)
//! cargo build --release --example perf_hash
//! sudo taskset -c 2 ./target/release/examples/perf_hash
//!
//! # Build with AVX2
//! RUSTFLAGS="-C target-feature=+avx2" cargo build --release --example perf_hash
//!
//! # Build with AVX-512
//! RUSTFLAGS="-C target-feature=+avx512f" cargo build --release --example perf_hash
//!
//! # Build with native CPU features
//! RUSTFLAGS="-C target-cpu=native" cargo build --release --example perf_hash
//!
//! # Re-enable turbo
//! echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! ```

use std::hint::black_box;

use nexus_ascii::hash::{hash, hash_with_seed};

const WARMUP: usize = 10_000;
const ITERATIONS: usize = 100_000;

#[inline(always)]
fn rdtscp() -> u64 {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: x86_64 intrinsic; this file only runs on x86_64.
    unsafe {
        let mut aux: u32 = 0;
        std::arch::x86_64::__rdtscp(&raw mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        std::time::Instant::now().elapsed().as_nanos() as u64
    }
}

struct Stats {
    samples: Vec<u64>,
}

impl Stats {
    fn new() -> Self {
        Self {
            samples: Vec::with_capacity(ITERATIONS),
        }
    }

    fn record(&mut self, cycles: u64) {
        self.samples.push(cycles);
    }

    fn percentile(&self, p: f64) -> u64 {
        let mut sorted = self.samples.clone();
        sorted.sort_unstable();
        let idx = ((p / 100.0) * (sorted.len() - 1) as f64) as usize;
        sorted[idx]
    }

    fn p50(&self) -> u64 {
        self.percentile(50.0)
    }

    fn p99(&self) -> u64 {
        self.percentile(99.0)
    }

    fn p999(&self) -> u64 {
        self.percentile(99.9)
    }
}

/// Benchmark a hash function with compile-time capacity.
fn bench<const CAP: usize>(data: &[u8]) -> Stats {
    // Warmup
    for _ in 0..WARMUP {
        black_box(hash::<CAP>(data));
    }

    // Benchmark
    let mut stats = Stats::new();
    for _ in 0..ITERATIONS {
        let start = rdtscp();
        let h = hash::<CAP>(data);
        let end = rdtscp();
        black_box(h);
        stats.record(end.wrapping_sub(start));
    }

    stats
}

fn print_implementation_info() {
    println!("HASH FUNCTION PERFORMANCE BENCHMARK");
    println!("====================================\n");

    print!("Implementation: XXH3 with ");

    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    println!("AVX-512");

    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(target_feature = "avx512f")
    ))]
    println!("AVX2");

    #[cfg(all(target_arch = "x86_64", not(target_feature = "avx2")))]
    println!("SSE2");

    #[cfg(not(target_arch = "x86_64"))]
    println!("scalar");

    println!("Iterations: {}, Warmup: {}", ITERATIONS, WARMUP);
    println!("All times in CPU cycles\n");
}

fn main() {
    print_implementation_info();

    // Test sizes that match real use cases:
    // - 8B: tiny IDs
    // - 16B: short symbols
    // - 32B: order IDs (common)
    // - 64B: medium fields
    // - 128B: larger bounded strings
    // - 256B+: approaching SIMD threshold (240B)
    // - 512B+: SIMD path (for large inputs)

    println!("=== SMALL INPUTS (compile-time branch elimination) ===\n");
    println!("{:<10} {:>8} {:>8} {:>8}", "Size", "p50", "p99", "p999");
    println!("{}", "-".repeat(40));

    // 8 bytes - CAP=8 eliminates all but smallest path
    let data_8: Vec<u8> = (0..8).map(|i| i as u8).collect();
    let stats = bench::<8>(&data_8);
    println!(
        "{:<10} {:>8} {:>8} {:>8}",
        "8B",
        stats.p50(),
        stats.p99(),
        stats.p999()
    );

    // 16 bytes - CAP=16
    let data_16: Vec<u8> = (0..16).map(|i| i as u8).collect();
    let stats = bench::<16>(&data_16);
    println!(
        "{:<10} {:>8} {:>8} {:>8}",
        "16B",
        stats.p50(),
        stats.p99(),
        stats.p999()
    );

    // 32 bytes - CAP=32 (order IDs)
    let data_32: Vec<u8> = (0..32).map(|i| i as u8).collect();
    let stats = bench::<32>(&data_32);
    println!(
        "{:<10} {:>8} {:>8} {:>8}",
        "32B",
        stats.p50(),
        stats.p99(),
        stats.p999()
    );

    // 64 bytes - CAP=64
    let data_64: Vec<u8> = (0..64).map(|i| i as u8).collect();
    let stats = bench::<64>(&data_64);
    println!(
        "{:<10} {:>8} {:>8} {:>8}",
        "64B",
        stats.p50(),
        stats.p99(),
        stats.p999()
    );

    // 128 bytes - CAP=128
    let data_128: Vec<u8> = (0..128).map(|i| i as u8).collect();
    let stats = bench::<128>(&data_128);
    println!(
        "{:<10} {:>8} {:>8} {:>8}",
        "128B",
        stats.p50(),
        stats.p99(),
        stats.p999()
    );

    println!("\n=== MEDIUM/LARGE INPUTS (SIMD paths for >240B) ===\n");
    println!(
        "{:<10} {:>8} {:>8} {:>8} {:>12}",
        "Size", "p50", "p99", "p999", "cycles/byte"
    );
    println!("{}", "-".repeat(55));

    // 256 bytes - just past SIMD threshold
    let data_256: Vec<u8> = (0..256).map(|i| (i % 256) as u8).collect();
    let stats = bench::<256>(&data_256);
    println!(
        "{:<10} {:>8} {:>8} {:>8} {:>12.3}",
        "256B",
        stats.p50(),
        stats.p99(),
        stats.p999(),
        stats.p50() as f64 / 256.0
    );

    // 512 bytes
    let data_512: Vec<u8> = (0..512).map(|i| (i % 256) as u8).collect();
    let stats = bench::<512>(&data_512);
    println!(
        "{:<10} {:>8} {:>8} {:>8} {:>12.3}",
        "512B",
        stats.p50(),
        stats.p99(),
        stats.p999(),
        stats.p50() as f64 / 512.0
    );

    // 1KB
    let data_1k: Vec<u8> = (0..1024).map(|i| (i % 256) as u8).collect();
    let stats = bench::<1024>(&data_1k);
    println!(
        "{:<10} {:>8} {:>8} {:>8} {:>12.3}",
        "1KB",
        stats.p50(),
        stats.p99(),
        stats.p999(),
        stats.p50() as f64 / 1024.0
    );

    // 2KB
    let data_2k: Vec<u8> = (0..2048).map(|i| (i % 256) as u8).collect();
    let stats = bench::<2048>(&data_2k);
    println!(
        "{:<10} {:>8} {:>8} {:>8} {:>12.3}",
        "2KB",
        stats.p50(),
        stats.p99(),
        stats.p999(),
        stats.p50() as f64 / 2048.0
    );

    // 4KB
    let data_4k: Vec<u8> = (0..4096).map(|i| (i % 256) as u8).collect();
    let stats = bench::<4096>(&data_4k);
    println!(
        "{:<10} {:>8} {:>8} {:>8} {:>12.3}",
        "4KB",
        stats.p50(),
        stats.p99(),
        stats.p999(),
        stats.p50() as f64 / 4096.0
    );

    // Verify hash_with_seed works
    println!("\n=== SEED VERIFICATION ===\n");
    let h1 = hash::<32>(&data_32);
    let h2 = hash_with_seed::<32>(&data_32, 12345);
    println!("hash(32B, seed=0):     0x{:016x}", h1);
    println!("hash(32B, seed=12345): 0x{:016x}", h2);
    println!("Different: {}", h1 != h2);

    println!();
}
