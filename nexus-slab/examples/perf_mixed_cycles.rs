//! Mixed workload benchmark: INSERT + GET + REMOVE across large slab.
//!
//! Simulates realistic order lifecycle with rolling window:
//! - Maintains ~50% slab occupancy
//! - Each order: insert -> several lookups -> remove
//! - Orders spread randomly across slab for realistic access pattern
//!
//! Tests THP behavior and whether try_collapse() helps tail latencies.
//!
//! Run with:
//!   cargo build --release --example perf_mixed_cycles
//!   taskset -c 0 ./target/release/examples/perf_mixed_cycles

use hdrhistogram::Histogram;
use std::hint::black_box;

// 1M slots = 16MB working set - triggers THP behavior
const CAPACITY: usize = 1_000_000;

// Total order lifecycles to simulate (can exceed capacity)
const TOTAL_ORDERS: usize = 1_000_000;

// How many orders active at once (~50% of capacity)
const ACTIVE_ORDERS: usize = CAPACITY / 2;

// Lookups per order before removal
const LOOKUPS_PER_ORDER: usize = 3;

const SEED: u64 = 0xCAFEBABE;

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

    fn next_usize(&mut self, max: usize) -> usize {
        (self.next() as usize) % max
    }
}

struct Stats {
    insert: Histogram<u64>,
    get: Histogram<u64>,
    remove: Histogram<u64>,
}

impl Stats {
    fn new() -> Self {
        Self {
            insert: Histogram::new(3).unwrap(),
            get: Histogram::new(3).unwrap(),
            remove: Histogram::new(3).unwrap(),
        }
    }

    fn print(&self, name: &str) {
        println!("{}", name);
        println!(
            "  INSERT:  p50={:>4}  p99={:>4}  p999={:>5}  max={:>7}  (n={})",
            self.insert.value_at_quantile(0.50),
            self.insert.value_at_quantile(0.99),
            self.insert.value_at_quantile(0.999),
            self.insert.max(),
            self.insert.len()
        );
        println!(
            "  GET:     p50={:>4}  p99={:>4}  p999={:>5}  max={:>7}  (n={})",
            self.get.value_at_quantile(0.50),
            self.get.value_at_quantile(0.99),
            self.get.value_at_quantile(0.999),
            self.get.max(),
            self.get.len()
        );
        println!(
            "  REMOVE:  p50={:>4}  p99={:>4}  p999={:>5}  max={:>7}  (n={})",
            self.remove.value_at_quantile(0.50),
            self.remove.value_at_quantile(0.99),
            self.remove.value_at_quantile(0.999),
            self.remove.max(),
            self.remove.len()
        );
    }
}

/// Order with remaining lookups before removal
struct Order {
    key: nexus_slab::Key,
    lookups_remaining: usize,
}

/// Rolling window benchmark for nexus-slab
fn bench_nexus(use_collapse: bool) -> Stats {
    let mut slab = nexus_slab::Slab::<u64>::with_capacity(CAPACITY).unwrap();

    if use_collapse {
        match slab.try_collapse() {
            Ok(()) => {}
            Err(e) => eprintln!("  try_collapse failed: {}", e),
        }
    }

    let mut stats = Stats::new();
    let mut rng = Xorshift::new(SEED);
    let mut active: Vec<Order> = Vec::with_capacity(ACTIVE_ORDERS + 1);
    let mut orders_created = 0usize;

    // Warmup: fill to 25% and drain
    let warmup = CAPACITY / 4;
    for i in 0..warmup as u64 {
        let _ = slab.insert(i);
    }
    slab.clear();

    // Main loop: maintain rolling window of active orders
    while orders_created < TOTAL_ORDERS || !active.is_empty() {
        // If we have room and orders left to create, insert
        if active.len() < ACTIVE_ORDERS && orders_created < TOTAL_ORDERS {
            let start = rdtscp();
            let key = slab.insert(orders_created as u64).unwrap();
            let end = rdtscp();
            let _ = stats.insert.record(end.wrapping_sub(start));

            active.push(Order {
                key,
                lookups_remaining: LOOKUPS_PER_ORDER,
            });
            orders_created += 1;
        }

        // Pick a random active order
        if active.is_empty() {
            continue;
        }
        let idx = rng.next_usize(active.len());

        if active[idx].lookups_remaining > 0 {
            // Do a lookup
            let start = rdtscp();
            black_box(slab.get(active[idx].key));
            let end = rdtscp();
            let _ = stats.get.record(end.wrapping_sub(start));
            active[idx].lookups_remaining -= 1;
        } else {
            // Remove this order
            let order = active.swap_remove(idx);
            let start = rdtscp();
            black_box(slab.remove(order.key));
            let end = rdtscp();
            let _ = stats.remove.record(end.wrapping_sub(start));
        }
    }

    stats
}

/// Order for slab crate
struct SlabOrder {
    key: usize,
    lookups_remaining: usize,
}

/// Rolling window benchmark for slab crate
fn bench_slab_crate() -> Stats {
    let mut slab = slab::Slab::<u64>::with_capacity(CAPACITY);
    let mut stats = Stats::new();
    let mut rng = Xorshift::new(SEED);
    let mut active: Vec<SlabOrder> = Vec::with_capacity(ACTIVE_ORDERS + 1);
    let mut orders_created = 0usize;

    // Warmup
    let warmup = CAPACITY / 4;
    for i in 0..warmup as u64 {
        slab.insert(i);
    }
    slab.clear();

    // Main loop
    while orders_created < TOTAL_ORDERS || !active.is_empty() {
        if active.len() < ACTIVE_ORDERS && orders_created < TOTAL_ORDERS {
            let start = rdtscp();
            let key = slab.insert(orders_created as u64);
            let end = rdtscp();
            let _ = stats.insert.record(end.wrapping_sub(start));

            active.push(SlabOrder {
                key,
                lookups_remaining: LOOKUPS_PER_ORDER,
            });
            orders_created += 1;
        }

        if active.is_empty() {
            continue;
        }
        let idx = rng.next_usize(active.len());

        if active[idx].lookups_remaining > 0 {
            let start = rdtscp();
            black_box(slab.get(active[idx].key));
            let end = rdtscp();
            let _ = stats.get.record(end.wrapping_sub(start));
            active[idx].lookups_remaining -= 1;
        } else {
            let order = active.swap_remove(idx);
            let start = rdtscp();
            black_box(slab.remove(order.key));
            let end = rdtscp();
            let _ = stats.remove.record(end.wrapping_sub(start));
        }
    }

    stats
}

fn main() {
    println!(
        "MIXED WORKLOAD: {} total orders, {} capacity, {} active",
        TOTAL_ORDERS, CAPACITY, ACTIVE_ORDERS
    );
    println!(
        "Each order: 1 insert + {} gets + 1 remove",
        LOOKUPS_PER_ORDER
    );
    println!(
        "Working set: {}MB (exceeds cache, tests THP)",
        CAPACITY * 16 / 1024 / 1024
    );
    println!("================================================================");
    println!();

    println!("nexus-slab (no collapse):");
    let nexus_no_collapse = bench_nexus(false);
    nexus_no_collapse.print("");
    println!();

    println!("nexus-slab (with try_collapse):");
    let nexus_with_collapse = bench_nexus(true);
    nexus_with_collapse.print("");
    println!();

    println!("slab crate:");
    let slab_stats = bench_slab_crate();
    slab_stats.print("");
    println!();

    // Summary comparison focused on tails
    println!("================================================================");
    println!("TAIL LATENCY COMPARISON (p999 cycles):");
    println!("----------------------------------------------------------------");
    println!("              nexus       nexus+collapse    slab");
    println!(
        "  INSERT:     {:>5}          {:>5}          {:>5}",
        nexus_no_collapse.insert.value_at_quantile(0.999),
        nexus_with_collapse.insert.value_at_quantile(0.999),
        slab_stats.insert.value_at_quantile(0.999)
    );
    println!(
        "  GET:        {:>5}          {:>5}          {:>5}",
        nexus_no_collapse.get.value_at_quantile(0.999),
        nexus_with_collapse.get.value_at_quantile(0.999),
        slab_stats.get.value_at_quantile(0.999)
    );
    println!(
        "  REMOVE:     {:>5}          {:>5}          {:>5}",
        nexus_no_collapse.remove.value_at_quantile(0.999),
        nexus_with_collapse.remove.value_at_quantile(0.999),
        slab_stats.remove.value_at_quantile(0.999)
    );
}
