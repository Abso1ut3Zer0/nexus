//! Pool benchmark: acquire/return latency measurement
//!
//! Measures cycle-accurate latency for pool operations using rdtscp.
//! Tests both BoundedPool and Pool variants.

use hdrhistogram::Histogram;
use std::hint::black_box;

const CAPACITY: usize = 10_000;
const OPERATIONS: usize = 1_000_000;

#[inline(always)]
fn rdtscp() -> u64 {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe {
        let mut aux: u32 = 0;
        std::arch::x86_64::__rdtscp(&raw mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    panic!("rdtscp only supported on x86_64");
}

struct Stats {
    acquire: Histogram<u64>,
    release: Histogram<u64>,
}

impl Stats {
    fn new() -> Self {
        Self {
            acquire: Histogram::new(3).unwrap(),
            release: Histogram::new(3).unwrap(),
        }
    }

    fn print(&self, name: &str) {
        println!("{}:", name);
        println!(
            "  ACQUIRE: p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}  (n={})",
            self.acquire.value_at_quantile(0.50),
            self.acquire.value_at_quantile(0.99),
            self.acquire.value_at_quantile(0.999),
            self.acquire.max(),
            self.acquire.len()
        );
        println!(
            "  RELEASE: p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}  (n={})",
            self.release.value_at_quantile(0.50),
            self.release.value_at_quantile(0.99),
            self.release.value_at_quantile(0.999),
            self.release.max(),
            self.release.len()
        );
    }
}

fn bench_bounded_pool() -> Stats {
    use nexus_pool::local::BoundedPool;

    let pool: BoundedPool<Vec<u8>> =
        BoundedPool::new(CAPACITY, || Vec::with_capacity(1024), Vec::clear);

    let mut stats = Stats::new();

    // Acquire/release cycle
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let guard = pool.try_acquire().unwrap();
        let mid = rdtscp();

        // Do minimal work to prevent optimizing away
        black_box(guard.capacity());

        drop(guard);
        let end = rdtscp();

        let _ = stats.acquire.record(mid.wrapping_sub(start));
        let _ = stats.release.record(end.wrapping_sub(mid));
    }

    stats
}

fn bench_bounded_pool_held() -> Stats {
    use nexus_pool::local::BoundedPool;

    // Test with multiple items held - more realistic scenario
    let pool: BoundedPool<Vec<u8>> =
        BoundedPool::new(CAPACITY, || Vec::with_capacity(1024), Vec::clear);

    let mut stats = Stats::new();
    let mut held = Vec::with_capacity(CAPACITY / 2);

    // Pre-acquire half capacity
    for _ in 0..(CAPACITY / 2) {
        held.push(pool.try_acquire().unwrap());
    }

    // Acquire/release cycle while holding others
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let guard = pool.try_acquire().unwrap();
        let mid = rdtscp();

        black_box(guard.capacity());

        drop(guard);
        let end = rdtscp();

        let _ = stats.acquire.record(mid.wrapping_sub(start));
        let _ = stats.release.record(end.wrapping_sub(mid));
    }

    // Clean up
    drop(held);

    stats
}

fn bench_pool_fast_path() -> Stats {
    use nexus_pool::local::Pool;

    // Pre-populate so we only hit fast path (no factory calls)
    let pool: Pool<Vec<u8>> =
        Pool::with_capacity(CAPACITY, || Vec::with_capacity(1024), Vec::clear);

    let mut stats = Stats::new();

    // Acquire/release cycle - should always hit pool, never factory
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let guard = pool.try_acquire().unwrap();
        let mid = rdtscp();

        black_box(guard.capacity());

        drop(guard);
        let end = rdtscp();

        let _ = stats.acquire.record(mid.wrapping_sub(start));
        let _ = stats.release.record(end.wrapping_sub(mid));
    }

    stats
}

fn bench_pool_slow_path() -> Stats {
    use nexus_pool::local::Pool;

    // Empty pool - every acquire hits factory
    let pool: Pool<Vec<u8>> = Pool::new(|| Vec::with_capacity(1024), Vec::clear);

    let mut stats = Stats::new();

    // Acquire creates, release returns, acquire reuses, release returns...
    // So half hit factory, half reuse
    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let guard = pool.acquire();
        let mid = rdtscp();

        black_box(guard.capacity());

        drop(guard);
        let end = rdtscp();

        let _ = stats.acquire.record(mid.wrapping_sub(start));
        let _ = stats.release.record(end.wrapping_sub(mid));
    }

    stats
}

fn main() {
    println!("POOL BENCHMARK");
    println!("Capacity: {}, Operations: {}", CAPACITY, OPERATIONS);
    println!("================================================================\n");

    let bounded = bench_bounded_pool();
    let bounded_held = bench_bounded_pool_held();
    let pool_fast = bench_pool_fast_path();
    let pool_slow = bench_pool_slow_path();

    bounded.print("BoundedPool (empty pool)");
    println!();
    bounded_held.print("BoundedPool (50% held)");
    println!();
    pool_fast.print("Pool (fast path - try_acquire)");
    println!();
    pool_slow.print("Pool (slow path - acquire, first hits factory)");
    println!();

    println!("================================================================");
    println!("COMPARISON (cycles):");
    println!("----------------------------------------------------------------");
    println!("                Bounded   Bounded+Held   Pool-Fast   Pool-Slow");
    println!(
        "  ACQUIRE p50:    {:>4}         {:>4}        {:>4}        {:>4}",
        bounded.acquire.value_at_quantile(0.50),
        bounded_held.acquire.value_at_quantile(0.50),
        pool_fast.acquire.value_at_quantile(0.50),
        pool_slow.acquire.value_at_quantile(0.50),
    );
    println!(
        "  ACQUIRE p99:    {:>4}         {:>4}        {:>4}        {:>4}",
        bounded.acquire.value_at_quantile(0.99),
        bounded_held.acquire.value_at_quantile(0.99),
        pool_fast.acquire.value_at_quantile(0.99),
        pool_slow.acquire.value_at_quantile(0.99),
    );
    println!(
        "  RELEASE p50:    {:>4}         {:>4}        {:>4}        {:>4}",
        bounded.release.value_at_quantile(0.50),
        bounded_held.release.value_at_quantile(0.50),
        pool_fast.release.value_at_quantile(0.50),
        pool_slow.release.value_at_quantile(0.50),
    );
    println!(
        "  RELEASE p99:    {:>4}         {:>4}        {:>4}        {:>4}",
        bounded.release.value_at_quantile(0.99),
        bounded_held.release.value_at_quantile(0.99),
        pool_fast.release.value_at_quantile(0.99),
        pool_slow.release.value_at_quantile(0.99),
    );

    println!();
    println!("NOTE: Release includes reset fn call (Vec::clear in this test)");
    println!("      Pool-Slow alternates: factory call -> reuse -> factory -> ...");
}
