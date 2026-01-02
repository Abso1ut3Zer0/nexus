//! Cycle-accurate get latency comparison using rdtscp.
//!
//! Compares nexus-slab vs slab crate with per-operation cycle counts.
//! Uses random access pattern with fixed seed for reproducibility.
//!
//! Working set: 100K entries (1.6MB) fits in L2/L3 cache for stable results.
//! For large-scale THP testing, use perf_get_large_cycles.
//!
//! Run with:
//!   cargo build --release --example perf_get_cycles
//!   taskset -c 0 ./target/release/examples/perf_get_cycles

use hdrhistogram::Histogram;
use std::hint::black_box;

// 100K entries × 16 bytes = 1.6MB - fits in L2/L3 cache
const CAPACITY: usize = 100_000;
const OPS: usize = 1_000_000;
const SEED: u64 = 0xDEADBEEF;

#[inline(always)]
fn rdtscp() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        let mut aux: u32 = 0;
        std::arch::x86_64::__rdtscp(&mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        panic!("rdtscp only supported on x86_64");
    }
}

/// Simple deterministic PRNG for reproducible random access pattern
struct Xorshift {
    state: u64,
}

impl Xorshift {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state
    }
}

fn print_stats(name: &str, hist: &Histogram<u64>) {
    println!("{}", name);
    println!("  min:  {:>6} cycles", hist.min());
    println!("  p50:  {:>6} cycles", hist.value_at_quantile(0.50));
    println!("  p99:  {:>6} cycles", hist.value_at_quantile(0.99));
    println!("  p999: {:>6} cycles", hist.value_at_quantile(0.999));
    println!("  max:  {:>6} cycles", hist.max());
    println!("  avg:  {:>6.0} cycles", hist.mean());
}

fn generate_random_indices(count: usize, max: usize, seed: u64) -> Vec<usize> {
    let mut rng = Xorshift::new(seed);
    (0..count).map(|_| (rng.next() as usize) % max).collect()
}

fn bench_nexus_slab(indices: &[usize]) -> Histogram<u64> {
    let mut slab = nexus_slab::Slab::<u64>::with_capacity(CAPACITY).unwrap();
    let mut hist = Histogram::<u64>::new(3).unwrap();

    // Fill the slab - keys are indices 0..CAPACITY
    for i in 0..CAPACITY as u64 {
        slab.insert(i).unwrap();
    }

    // Warmup - random access
    for &idx in indices.iter().take(10_000) {
        let key = unsafe { nexus_slab::Key::from_raw(idx as u32) };
        black_box(slab.get(key));
    }

    // Measured random gets
    for &idx in indices {
        let key = unsafe { nexus_slab::Key::from_raw(idx as u32) };
        let start = rdtscp();
        black_box(slab.get(key));
        let end = rdtscp();
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_slab_crate(indices: &[usize]) -> Histogram<u64> {
    let mut slab = slab::Slab::<u64>::with_capacity(CAPACITY);
    let mut hist = Histogram::<u64>::new(3).unwrap();

    // Fill the slab - keys are indices 0..CAPACITY
    for i in 0..CAPACITY as u64 {
        slab.insert(i);
    }

    // Warmup - random access
    for &idx in indices.iter().take(10_000) {
        black_box(slab.get(idx));
    }

    // Measured random gets
    for &idx in indices {
        let start = rdtscp();
        black_box(slab.get(idx));
        let end = rdtscp();
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn main() {
    // Pre-generate random indices (same for both benchmarks)
    let indices = generate_random_indices(OPS, CAPACITY, SEED);

    println!(
        "GET latency comparison ({} random ops, seed=0x{:X})",
        OPS, SEED
    );
    println!("========================================");
    println!();

    let nexus_hist = bench_nexus_slab(&indices);
    let slab_hist = bench_slab_crate(&indices);

    print_stats("nexus-slab:", &nexus_hist);
    println!();
    print_stats("slab:", &slab_hist);
    println!();

    let nexus_p50 = nexus_hist.value_at_quantile(0.50);
    let slab_p50 = slab_hist.value_at_quantile(0.50);

    println!("----------------------------------------");
    if nexus_p50 < slab_p50 {
        println!(
            "nexus-slab p50 is {:.1}% FASTER",
            (1.0 - nexus_p50 as f64 / slab_p50 as f64) * 100.0
        );
    } else if nexus_p50 > slab_p50 {
        println!(
            "nexus-slab p50 is {:.1}% SLOWER",
            (nexus_p50 as f64 / slab_p50 as f64 - 1.0) * 100.0
        );
    } else {
        println!("nexus-slab p50 is EQUAL");
    }
}
