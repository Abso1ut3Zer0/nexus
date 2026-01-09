//! Growth benchmark: compare allocation strategies when exceeding initial capacity
//!
//! Tests:
//! 1. Pre-allocated phase (within initial capacity)
//! 2. Growth phase (exceeding capacity, triggers realloc/mmap)
//! 3. Post-growth phase (steady state after growth)

use hdrhistogram::Histogram;
use std::hint::black_box;

const INITIAL_CAPACITY: usize = 100_000;
const FINAL_SIZE: usize = 500_000;
const OPERATIONS_PER_PHASE: usize = 500_000;
const SEED: u64 = 0xDEADBEEF;

#[inline(always)]
fn rdtscp() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        let mut aux: u32 = 0;
        std::arch::x86_64::__rdtscp(&mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    panic!("rdtscp only supported on x86_64");
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

struct PhaseStats {
    insert: Histogram<u64>,
    get: Histogram<u64>,
    remove: Histogram<u64>,
}

impl PhaseStats {
    fn new() -> Self {
        Self {
            insert: Histogram::new(3).unwrap(),
            get: Histogram::new(3).unwrap(),
            remove: Histogram::new(3).unwrap(),
        }
    }

    fn print(&self, phase: &str) {
        println!("  {}:", phase);
        println!(
            "    INSERT:  p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}  (n={})",
            self.insert.value_at_quantile(0.50),
            self.insert.value_at_quantile(0.99),
            self.insert.value_at_quantile(0.999),
            self.insert.max(),
            self.insert.len()
        );
        println!(
            "    GET:     p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}  (n={})",
            self.get.value_at_quantile(0.50),
            self.get.value_at_quantile(0.99),
            self.get.value_at_quantile(0.999),
            self.get.max(),
            self.get.len()
        );
        println!(
            "    REMOVE:  p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}  (n={})",
            self.remove.value_at_quantile(0.50),
            self.remove.value_at_quantile(0.99),
            self.remove.value_at_quantile(0.999),
            self.remove.max(),
            self.remove.len()
        );
    }
}

struct GrowthStats {
    pre_growth: PhaseStats,
    during_growth: PhaseStats,
    post_growth: PhaseStats,
}

impl GrowthStats {
    fn new() -> Self {
        Self {
            pre_growth: PhaseStats::new(),
            during_growth: PhaseStats::new(),
            post_growth: PhaseStats::new(),
        }
    }
}

fn bench_nexus() -> GrowthStats {
    // Start with initial capacity, let it grow
    let mut slab: nexus_slab::DynamicSlab<u64> = nexus_slab::SlabBuilder::new()
        .capacity(INITIAL_CAPACITY) // 100K - will need to grow
        .slab_bytes(2 * 1024 * 1024)
        .build()
        .unwrap();

    let mut stats = GrowthStats::new();
    let mut rng = Xorshift::new(SEED);
    let mut keys: Vec<nexus_slab::Key> = Vec::with_capacity(FINAL_SIZE);

    // Phase 1: Pre-growth (fill to ~80% of initial capacity)
    let pre_growth_target = INITIAL_CAPACITY * 8 / 10;
    for i in 0..pre_growth_target {
        let start = rdtscp();
        let key = slab.insert(i as u64);
        let end = rdtscp();
        let _ = stats.pre_growth.insert.record(end.wrapping_sub(start));
        keys.push(key);
    }

    // Mixed ops within pre-allocated space
    for _ in 0..OPERATIONS_PER_PHASE {
        let op = rng.next() % 10;
        if op < 2 && slab.len() < pre_growth_target {
            // Insert
            let start = rdtscp();
            let key = slab.insert(rng.next());
            let end = rdtscp();
            let _ = stats.pre_growth.insert.record(end.wrapping_sub(start));
            keys.push(key);
        } else if op < 8 && !keys.is_empty() {
            // Get
            let idx = rng.next_usize(keys.len());
            let start = rdtscp();
            black_box(slab.get(keys[idx]));
            let end = rdtscp();
            let _ = stats.pre_growth.get.record(end.wrapping_sub(start));
        } else if !keys.is_empty() {
            // Remove
            let idx = rng.next_usize(keys.len());
            let key = keys.swap_remove(idx);
            let start = rdtscp();
            black_box(slab.remove(key));
            let end = rdtscp();
            let _ = stats.pre_growth.remove.record(end.wrapping_sub(start));
        }
    }

    // Phase 2: Growth (push beyond initial capacity)
    while slab.capacity() < FINAL_SIZE {
        let start = rdtscp();
        let key = slab.insert(rng.next());
        let end = rdtscp();
        let _ = stats.during_growth.insert.record(end.wrapping_sub(start));
        keys.push(key);

        // Some gets during growth
        if !keys.is_empty() && rng.next() % 4 == 0 {
            let idx = rng.next_usize(keys.len());
            let start = rdtscp();
            black_box(slab.get(keys[idx]));
            let end = rdtscp();
            let _ = stats.during_growth.get.record(end.wrapping_sub(start));
        }
    }

    // Phase 3: Post-growth steady state
    for _ in 0..OPERATIONS_PER_PHASE {
        let op = rng.next() % 10;
        if op < 2 {
            let start = rdtscp();
            let key = slab.insert(rng.next());
            let end = rdtscp();
            let _ = stats.post_growth.insert.record(end.wrapping_sub(start));
            keys.push(key);
        } else if op < 8 && !keys.is_empty() {
            let idx = rng.next_usize(keys.len());
            let start = rdtscp();
            black_box(slab.get(keys[idx]));
            let end = rdtscp();
            let _ = stats.post_growth.get.record(end.wrapping_sub(start));
        } else if !keys.is_empty() {
            let idx = rng.next_usize(keys.len());
            let key = keys.swap_remove(idx);
            let start = rdtscp();
            black_box(slab.remove(key));
            let end = rdtscp();
            let _ = stats.post_growth.remove.record(end.wrapping_sub(start));
        }
    }

    stats
}

fn bench_slab_crate() -> GrowthStats {
    let mut slab = slab::Slab::<u64>::with_capacity(INITIAL_CAPACITY);

    let mut stats = GrowthStats::new();
    let mut rng = Xorshift::new(SEED);
    let mut keys: Vec<usize> = Vec::with_capacity(FINAL_SIZE);

    // Phase 1: Pre-growth
    let pre_growth_target = INITIAL_CAPACITY * 8 / 10;
    for i in 0..pre_growth_target {
        let start = rdtscp();
        let key = slab.insert(i as u64);
        let end = rdtscp();
        let _ = stats.pre_growth.insert.record(end.wrapping_sub(start));
        keys.push(key);
    }

    for _ in 0..OPERATIONS_PER_PHASE {
        let op = rng.next() % 10;
        if op < 2 && slab.len() < pre_growth_target {
            let start = rdtscp();
            let key = slab.insert(rng.next());
            let end = rdtscp();
            let _ = stats.pre_growth.insert.record(end.wrapping_sub(start));
            keys.push(key);
        } else if op < 8 && !keys.is_empty() {
            let idx = rng.next_usize(keys.len());
            let start = rdtscp();
            black_box(slab.get(keys[idx]));
            let end = rdtscp();
            let _ = stats.pre_growth.get.record(end.wrapping_sub(start));
        } else if !keys.is_empty() {
            let idx = rng.next_usize(keys.len());
            let key = keys.swap_remove(idx);
            let start = rdtscp();
            black_box(slab.remove(key));
            let end = rdtscp();
            let _ = stats.pre_growth.remove.record(end.wrapping_sub(start));
        }
    }

    // Phase 2: Growth
    while slab.capacity() < FINAL_SIZE {
        let start = rdtscp();
        let key = slab.insert(rng.next());
        let end = rdtscp();
        let _ = stats.during_growth.insert.record(end.wrapping_sub(start));
        keys.push(key);

        if !keys.is_empty() && rng.next() % 4 == 0 {
            let idx = rng.next_usize(keys.len());
            let start = rdtscp();
            black_box(slab.get(keys[idx]));
            let end = rdtscp();
            let _ = stats.during_growth.get.record(end.wrapping_sub(start));
        }
    }

    // Phase 3: Post-growth
    for _ in 0..OPERATIONS_PER_PHASE {
        let op = rng.next() % 10;
        if op < 2 {
            let start = rdtscp();
            let key = slab.insert(rng.next());
            let end = rdtscp();
            let _ = stats.post_growth.insert.record(end.wrapping_sub(start));
            keys.push(key);
        } else if op < 8 && !keys.is_empty() {
            let idx = rng.next_usize(keys.len());
            let start = rdtscp();
            black_box(slab.get(keys[idx]));
            let end = rdtscp();
            let _ = stats.post_growth.get.record(end.wrapping_sub(start));
        } else if !keys.is_empty() {
            let idx = rng.next_usize(keys.len());
            let key = keys.swap_remove(idx);
            let start = rdtscp();
            black_box(slab.remove(key));
            let end = rdtscp();
            let _ = stats.post_growth.remove.record(end.wrapping_sub(start));
        }
    }

    stats
}

fn main() {
    println!("GROWTH BENCHMARK");
    println!(
        "Initial capacity: {}, Final size: {}",
        INITIAL_CAPACITY, FINAL_SIZE
    );
    println!("================================================================\n");

    let nexus = bench_nexus();
    let slab = bench_slab_crate();

    println!("nexus-slab:");
    nexus.pre_growth.print("PRE-GROWTH (within capacity)");
    nexus
        .during_growth
        .print("DURING GROWTH (exceeding capacity)");
    nexus.post_growth.print("POST-GROWTH (steady state)");
    println!();

    println!("slab crate:");
    slab.pre_growth.print("PRE-GROWTH (within capacity)");
    slab.during_growth
        .print("DURING GROWTH (exceeding capacity)");
    slab.post_growth.print("POST-GROWTH (steady state)");
    println!();

    println!("================================================================");
    println!("GROWTH PHASE INSERT COMPARISON (where realloc/mmap happens):");
    println!("----------------------------------------------------------------");
    println!("              nexus          slab");
    println!(
        "  p50:        {:>5}          {:>5}",
        nexus.during_growth.insert.value_at_quantile(0.50),
        slab.during_growth.insert.value_at_quantile(0.50)
    );
    println!(
        "  p99:        {:>5}          {:>5}",
        nexus.during_growth.insert.value_at_quantile(0.99),
        slab.during_growth.insert.value_at_quantile(0.99)
    );
    println!(
        "  p999:       {:>5}          {:>5}",
        nexus.during_growth.insert.value_at_quantile(0.999),
        slab.during_growth.insert.value_at_quantile(0.999)
    );
    println!(
        "  max:        {:>5}          {:>5}",
        nexus.during_growth.insert.max(),
        slab.during_growth.insert.max()
    );
}
