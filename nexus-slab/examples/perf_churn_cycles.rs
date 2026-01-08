//! Cycle-accurate churn (insert+remove) latency comparison using rdtscp.
//!
//! Compares nexus-slab vs slab crate with per-operation cycle counts.
//! This measures the common pattern of inserting then removing.
//!
//! Run with:
//!   cargo build --release --example perf_churn_cycles
//!   taskset -c 0 ./target/release/examples/perf_churn_cycles

use hdrhistogram::Histogram;
use std::hint::black_box;

const CAPACITY: usize = 100_000;
const OPS: usize = 1_000_000;

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

fn print_stats(name: &str, hist: &Histogram<u64>) {
    println!("{}", name);
    println!("  min:  {:>6} cycles", hist.min());
    println!("  p50:  {:>6} cycles", hist.value_at_quantile(0.50));
    println!("  p99:  {:>6} cycles", hist.value_at_quantile(0.99));
    println!("  p999: {:>6} cycles", hist.value_at_quantile(0.999));
    println!("  max:  {:>6} cycles", hist.max());
    println!("  avg:  {:>6.0} cycles", hist.mean());
}

fn bench_nexus_slab() -> Histogram<u64> {
    let mut slab = nexus_slab::SlabBuilder::default()
        .capacity(CAPACITY)
        .build()
        .unwrap();
    let mut hist = Histogram::<u64>::new(3).unwrap();

    // Warmup
    for i in 0..10_000u64 {
        let key = slab.insert(i).unwrap();
        black_box(slab.remove(key));
    }

    // Measured churn: insert then immediately remove
    for i in 0..OPS as u64 {
        let start = rdtscp();
        let key = slab.insert(i).unwrap();
        black_box(slab.remove(key));
        let end = rdtscp();
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn bench_slab_crate() -> Histogram<u64> {
    let mut slab = slab::Slab::<u64>::with_capacity(CAPACITY);
    let mut hist = Histogram::<u64>::new(3).unwrap();

    // Warmup
    for i in 0..10_000u64 {
        let key = slab.insert(i);
        black_box(slab.remove(key));
    }

    // Measured churn: insert then immediately remove
    for i in 0..OPS as u64 {
        let start = rdtscp();
        let key = slab.insert(i);
        black_box(slab.remove(key));
        let end = rdtscp();
        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

fn main() {
    println!("CHURN latency comparison ({} insert+remove pairs)", OPS);
    println!("========================================");
    println!();

    let nexus_hist = bench_nexus_slab();
    let slab_hist = bench_slab_crate();

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
