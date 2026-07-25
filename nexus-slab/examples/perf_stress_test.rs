//! Stress test: nexus-slab vs Box under realistic pressure
//!
//! Tests that reveal real-world differences:
//! 1. Long-running churn - does malloc degrade over time?
//! 2. Burst allocation - who hits the OS?
//! 3. Mixed lifetimes - fragmentation effects
//! 4. Tail latency under pressure
//!
//! Run with: `taskset -c 0 ./target/release/examples/perf_stress_test`

#![allow(clippy::items_after_statements, clippy::large_stack_arrays)]

use nexus_slab::bounded::Slab as BoundedSlab;
use std::collections::VecDeque;
use std::hint::black_box;

// ============================================================================
// Timing Infrastructure
// ============================================================================

#[inline(always)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsics; benchmark is x86_64-only.
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsics; benchmark is x86_64-only.
    unsafe {
        let tsc = core::arch::x86_64::__rdtscp(&mut 0u32 as *mut _);
        core::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    if sorted.is_empty() {
        return 0;
    }
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_histogram(name: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    let p25 = percentile(samples, 25.0);
    let p50 = percentile(samples, 50.0);
    let p75 = percentile(samples, 75.0);
    let p90 = percentile(samples, 90.0);
    let p99 = percentile(samples, 99.0);
    let p999 = percentile(samples, 99.9);
    let p9999 = percentile(samples, 99.99);
    let max = samples.last().copied().unwrap_or(0);

    println!(
        "  {:<18} p25={:>4}  p50={:>4}  p75={:>4}  p90={:>4}  p99={:>5}  p99.9={:>5}  p99.99={:>6}  max={:>7}",
        name, p25, p50, p75, p90, p99, p999, p9999, max
    );
}

// ============================================================================
// Test Types
// ============================================================================

#[derive(Clone)]
#[allow(dead_code)]
pub struct TestValue {
    id: u64,
    data: [u64; 7], // 64 bytes total - realistic order/message size
}

impl TestValue {
    fn new(id: u64) -> Self {
        Self { id, data: [id; 7] }
    }
}

// ============================================================================
// Test 1: Long-running churn - does performance degrade over time?
// ============================================================================

fn test_long_running_churn() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 1: LONG-RUNNING CHURN");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Pattern: 10M operations with 50% fill, random insert/remove");
    println!("  Looking for: degradation over time (fragmentation effects)\n");

    const CAPACITY: usize = 10_000;
    const OPS_PER_PHASE: usize = 1_000_000;
    const PHASES: usize = 10;

    // --- Box test ---
    println!("  Box<TestValue>:");
    {
        let mut items: Vec<Option<Box<TestValue>>> = vec![None; CAPACITY];
        let mut _occupied = 0usize;
        let mut rng = 12345u64;
        let mut next_id = 0u64;

        // Pre-fill to 50%
        for i in 0..CAPACITY / 2 {
            items[i] = Some(Box::new(TestValue::new(next_id)));
            next_id += 1;
            _occupied += 1;
        }

        for phase in 0..PHASES {
            let mut samples = Vec::with_capacity(OPS_PER_PHASE / 10);

            for op in 0..OPS_PER_PHASE {
                rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let idx = (rng as usize) % CAPACITY;

                // Sample every 10th operation
                let should_sample = op % 10 == 0;

                let start = if should_sample { rdtsc_start() } else { 0 };

                if items[idx].is_some() {
                    // Remove
                    black_box(items[idx].take());
                    _occupied -= 1;
                } else {
                    // Insert
                    items[idx] = Some(Box::new(TestValue::new(next_id)));
                    next_id += 1;
                    _occupied += 1;
                }

                if should_sample {
                    samples.push(rdtsc_end() - start);
                }
            }

            samples.sort_unstable();
            println!(
                "    Phase {:>2}: p25={:>3} p50={:>3} p75={:>3} p90={:>4} p99={:>4} p99.9={:>5} p99.99={:>6} max={:>7}",
                phase + 1,
                percentile(&samples, 25.0),
                percentile(&samples, 50.0),
                percentile(&samples, 75.0),
                percentile(&samples, 90.0),
                percentile(&samples, 99.0),
                percentile(&samples, 99.9),
                percentile(&samples, 99.99),
                samples.last().copied().unwrap_or(0),
            );
        }
    }

    // --- Slab test ---
    println!("\n  Slab<TestValue>:");
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<TestValue> = unsafe { BoundedSlab::with_capacity(CAPACITY) };

        let mut items: Vec<Option<_>> = (0..CAPACITY).map(|_| None).collect();
        let mut _occupied = 0usize;
        let mut rng = 12345u64; // Same seed for fair comparison
        let mut next_id = 0u64;

        // Pre-fill to 50%
        for i in 0..CAPACITY / 2 {
            items[i] = Some(alloc.alloc(TestValue::new(next_id)));
            next_id += 1;
            _occupied += 1;
        }

        for phase in 0..PHASES {
            let mut samples = Vec::with_capacity(OPS_PER_PHASE / 10);

            for op in 0..OPS_PER_PHASE {
                rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let idx = (rng as usize) % CAPACITY;

                let should_sample = op % 10 == 0;
                let start = if should_sample { rdtsc_start() } else { 0 };

                if let Some(slot) = items[idx].take() {
                    // SAFETY: slot was allocated from this slab
                    alloc.free(slot);
                    _occupied -= 1;
                } else {
                    items[idx] = Some(alloc.alloc(TestValue::new(next_id)));
                    next_id += 1;
                    _occupied += 1;
                }

                if should_sample {
                    samples.push(rdtsc_end() - start);
                }
            }

            samples.sort_unstable();
            println!(
                "    Phase {:>2}: p25={:>3} p50={:>3} p75={:>3} p90={:>4} p99={:>4} p99.9={:>5} p99.99={:>6} max={:>7}",
                phase + 1,
                percentile(&samples, 25.0),
                percentile(&samples, 50.0),
                percentile(&samples, 75.0),
                percentile(&samples, 90.0),
                percentile(&samples, 99.0),
                percentile(&samples, 99.9),
                percentile(&samples, 99.99),
                samples.last().copied().unwrap_or(0),
            );
        }
    }
}

// ============================================================================
// Test 2: Burst allocation - who hits the OS?
// ============================================================================

fn test_burst_allocation() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 2: BURST ALLOCATION");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Pattern: Rapidly allocate 5000 items, then free all. Repeat 100x.");
    println!("  Looking for: OS interaction spikes (mmap/brk syscalls)\n");

    const BURST_SIZE: usize = 5000;
    const BURSTS: usize = 100;

    // --- Box bursts ---
    {
        let mut alloc_samples = Vec::with_capacity(BURSTS);
        let mut free_samples = Vec::with_capacity(BURSTS);

        for _ in 0..BURSTS {
            // Allocate burst
            let start = rdtsc_start();
            let items: Vec<_> = (0..BURST_SIZE)
                .map(|i| Box::new(TestValue::new(i as u64)))
                .collect();
            let alloc_time = rdtsc_end() - start;
            alloc_samples.push(alloc_time / BURST_SIZE as u64);

            black_box(&items);

            // Free burst
            let start = rdtsc_start();
            drop(items);
            let free_time = rdtsc_end() - start;
            free_samples.push(free_time / BURST_SIZE as u64);
        }

        print_histogram("Box alloc burst", &mut alloc_samples);
        print_histogram("Box free burst", &mut free_samples);
    }

    println!();

    // --- Slab bursts ---
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<TestValue> = unsafe { BoundedSlab::with_capacity(BURST_SIZE) };

        let mut alloc_samples = Vec::with_capacity(BURSTS);
        let mut free_samples = Vec::with_capacity(BURSTS);

        for _ in 0..BURSTS {
            // Allocate burst
            let start = rdtsc_start();
            let items: Vec<_> = (0..BURST_SIZE)
                .map(|i| alloc.alloc(TestValue::new(i as u64)))
                .collect();
            let alloc_time = rdtsc_end() - start;
            alloc_samples.push(alloc_time / BURST_SIZE as u64);

            black_box(&items);

            // Free burst
            let start = rdtsc_start();
            for slot in items {
                // SAFETY: slot was allocated from this slab
                alloc.free(slot);
            }
            let free_time = rdtsc_end() - start;
            free_samples.push(free_time / BURST_SIZE as u64);
        }

        print_histogram("Slab alloc burst", &mut alloc_samples);
        print_histogram("Slab free burst", &mut free_samples);
    }
}

// ============================================================================
// Test 3: Mixed lifetimes - fragmentation stress
// ============================================================================

fn test_mixed_lifetimes() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 3: MIXED LIFETIMES (Fragmentation Stress)");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Pattern: Some items live long (90%), some die quickly (10%)");
    println!("  Looking for: Heap fragmentation slowing down allocation\n");

    const LONG_LIVED: usize = 5000;
    const SHORT_CYCLES: usize = 100_000;

    // --- Box mixed lifetimes ---
    {
        // Create long-lived items
        let _long_lived: Vec<_> = (0..LONG_LIVED)
            .map(|i| Box::new(TestValue::new(i as u64)))
            .collect();

        let mut samples = Vec::with_capacity(SHORT_CYCLES);

        for i in 0..SHORT_CYCLES {
            let start = rdtsc_start();
            let short = Box::new(TestValue::new((LONG_LIVED + i) as u64));
            black_box(&*short);
            drop(short);
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Box (fragmented)", &mut samples);
    }

    // --- Slab mixed lifetimes ---
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<TestValue> = unsafe { BoundedSlab::with_capacity(LONG_LIVED + 100) };

        // Create long-lived items
        let _long_lived: Vec<_> = (0..LONG_LIVED)
            .map(|i| alloc.alloc(TestValue::new(i as u64)))
            .collect();

        let mut samples = Vec::with_capacity(SHORT_CYCLES);

        for i in 0..SHORT_CYCLES {
            let start = rdtsc_start();
            let short = alloc.alloc(TestValue::new((LONG_LIVED + i) as u64));
            black_box(&*short);
            // SAFETY: slot was allocated from this slab
            alloc.free(short);
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Slab (no frag)", &mut samples);
    }
}

// ============================================================================
// Test 4: FIFO queue simulation - realistic workload
// ============================================================================

fn test_fifo_queue() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 4: FIFO QUEUE SIMULATION");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Pattern: Push to back, pop from front (message queue simulation)");
    println!("  Looking for: Consistent latency under steady-state load\n");

    const QUEUE_SIZE: usize = 1000;
    const OPERATIONS: usize = 500_000;

    // --- Box queue ---
    {
        let mut queue: VecDeque<Box<TestValue>> = VecDeque::with_capacity(QUEUE_SIZE);

        // Pre-fill
        for i in 0..QUEUE_SIZE {
            queue.push_back(Box::new(TestValue::new(i as u64)));
        }

        let mut push_samples = Vec::with_capacity(OPERATIONS);
        let mut pop_samples = Vec::with_capacity(OPERATIONS);

        for i in 0..OPERATIONS {
            // Pop
            let start = rdtsc_start();
            let item = queue.pop_front();
            pop_samples.push(rdtsc_end() - start);
            black_box(item);

            // Push
            let start = rdtsc_start();
            queue.push_back(Box::new(TestValue::new((QUEUE_SIZE + i) as u64)));
            push_samples.push(rdtsc_end() - start);
        }

        print_histogram("Box push", &mut push_samples);
        print_histogram("Box pop", &mut pop_samples);
    }

    println!();

    // --- Slab queue ---
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<TestValue> = unsafe { BoundedSlab::with_capacity(QUEUE_SIZE + 100) };

        let mut queue: VecDeque<_> = VecDeque::with_capacity(QUEUE_SIZE);

        // Pre-fill
        for i in 0..QUEUE_SIZE {
            queue.push_back(alloc.alloc(TestValue::new(i as u64)));
        }

        let mut push_samples = Vec::with_capacity(OPERATIONS);
        let mut pop_samples = Vec::with_capacity(OPERATIONS);

        for i in 0..OPERATIONS {
            // Pop
            let start = rdtsc_start();
            let item = queue.pop_front();
            pop_samples.push(rdtsc_end() - start);
            if let Some(slot) = item {
                // SAFETY: slot was allocated from this slab
                alloc.free(slot);
            }

            // Push
            let start = rdtsc_start();
            queue.push_back(alloc.alloc(TestValue::new((QUEUE_SIZE + i) as u64)));
            push_samples.push(rdtsc_end() - start);
        }

        // Clean up remaining queue
        while let Some(slot) = queue.pop_front() {
            alloc.free(slot);
        }

        print_histogram("Slab push", &mut push_samples);
        print_histogram("Slab pop", &mut pop_samples);
    }
}

// ============================================================================
// Test 5: Worst-case tail latency
// ============================================================================

fn test_tail_latency() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 5: WORST-CASE TAIL LATENCY");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Collecting 1M samples to find true tail behavior\n");

    const SAMPLES: usize = 1_000_000;

    // --- Box tail latency ---
    {
        let mut samples = Vec::with_capacity(SAMPLES);

        for i in 0..SAMPLES {
            let start = rdtsc_start();
            let item = Box::new(TestValue::new(i as u64));
            black_box(&*item);
            drop(item);
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Box alloc+free", &mut samples);
    }

    // --- Slab tail latency ---
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<TestValue> = unsafe { BoundedSlab::with_capacity(100) };

        let mut samples = Vec::with_capacity(SAMPLES);

        for i in 0..SAMPLES {
            let start = rdtsc_start();
            let item = alloc.alloc(TestValue::new(i as u64));
            black_box(&*item);
            // SAFETY: slot was allocated from this slab
            alloc.free(item);
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Slab alloc+free", &mut samples);
    }
}

// ============================================================================
// Test 6: Brutal fragmentation - mixed sizes, swiss cheese pattern
// ============================================================================

/// Different sized allocations to scatter across allocator size classes
#[derive(Clone)]
#[allow(dead_code)]
pub struct Small {
    data: [u8; 32],
}

#[derive(Clone)]
#[allow(dead_code)]
pub struct Medium {
    data: [u8; 128],
}

#[derive(Clone)]
#[allow(dead_code)]
pub struct Large {
    data: [u8; 512],
}

#[derive(Clone)]
#[allow(dead_code)]
pub struct XLarge {
    data: [u8; 2048],
}

fn test_brutal_fragmentation() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 6: BRUTAL FRAGMENTATION");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Phase 1: Allocate mixed sizes (32B, 128B, 512B, 2KB) to fragment heap");
    println!("  Phase 2: Free every 3rd allocation (swiss cheese pattern)");
    println!("  Phase 3: Measure 64-byte allocations in fragmented heap");
    println!("  Looking for: Allocation latency increase due to fragmentation\n");

    const FRAGMENT_COUNT: usize = 50_000;
    const MEASURE_COUNT: usize = 100_000;

    // --- Box with fragmented heap ---
    println!("  Box<TestValue> in fragmented heap:");
    {
        // Phase 1: Create fragmentation with mixed sizes
        let mut smalls: Vec<Box<Small>> = Vec::new();
        let mut mediums: Vec<Box<Medium>> = Vec::new();
        let mut larges: Vec<Box<Large>> = Vec::new();
        let mut xlarges: Vec<Box<XLarge>> = Vec::new();

        for i in 0..FRAGMENT_COUNT {
            match i % 4 {
                0 => smalls.push(Box::new(Small {
                    data: [i as u8; 32],
                })),
                1 => mediums.push(Box::new(Medium {
                    data: [i as u8; 128],
                })),
                2 => larges.push(Box::new(Large {
                    data: [i as u8; 512],
                })),
                _ => xlarges.push(Box::new(XLarge {
                    data: [i as u8; 2048],
                })),
            }
        }

        println!(
            "    Allocated {} mixed-size objects to fragment heap",
            FRAGMENT_COUNT
        );

        // Phase 2: Create swiss cheese by freeing every 3rd
        let smalls: Vec<_> = smalls
            .into_iter()
            .enumerate()
            .filter(|(i, _)| i % 3 != 0)
            .map(|(_, v)| v)
            .collect();
        let mediums: Vec<_> = mediums
            .into_iter()
            .enumerate()
            .filter(|(i, _)| i % 3 != 1)
            .map(|(_, v)| v)
            .collect();
        let larges: Vec<_> = larges
            .into_iter()
            .enumerate()
            .filter(|(i, _)| i % 3 != 2)
            .map(|(_, v)| v)
            .collect();
        // Keep all xlarges to block coalescing

        println!("    Created swiss cheese pattern (freed ~33% of small/medium/large)");
        println!(
            "    Remaining: {} small, {} medium, {} large, {} xlarge",
            smalls.len(),
            mediums.len(),
            larges.len(),
            xlarges.len()
        );

        // Phase 3: Measure 64-byte allocations in fragmented heap
        let mut samples = Vec::with_capacity(MEASURE_COUNT);

        for i in 0..MEASURE_COUNT {
            let start = rdtsc_start();
            let item = Box::new(TestValue::new(i as u64));
            black_box(&*item);
            drop(item);
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Box (fragmented)", &mut samples);

        // Keep references alive
        black_box(&smalls);
        black_box(&mediums);
        black_box(&larges);
        black_box(&xlarges);
    }

    // --- Box with clean heap (baseline) ---
    println!();
    {
        // Force a fresh state by doing nothing before measurement
        let mut samples = Vec::with_capacity(MEASURE_COUNT);

        for i in 0..MEASURE_COUNT {
            let start = rdtsc_start();
            let item = Box::new(TestValue::new(i as u64));
            black_box(&*item);
            drop(item);
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Box (clean heap)", &mut samples);
    }

    // --- Slab (immune to fragmentation) ---
    println!();
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<TestValue> = unsafe { BoundedSlab::with_capacity(1000) };

        let mut samples = Vec::with_capacity(MEASURE_COUNT);

        for i in 0..MEASURE_COUNT {
            let start = rdtsc_start();
            let item = alloc.alloc(TestValue::new(i as u64));
            black_box(&*item);
            // SAFETY: slot was allocated from this slab
            alloc.free(item);
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Slab (no frag)", &mut samples);
    }
}

// ============================================================================
// Test 7: Sustained pressure with memory churn
// ============================================================================

fn test_sustained_pressure() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 7: SUSTAINED MEMORY PRESSURE");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Allocate until we hit ~100MB, then churn while maintaining pressure");
    println!("  Looking for: Allocator degradation under sustained load\n");

    const TARGET_MB: usize = 100;
    const VALUE_SIZE: usize = std::mem::size_of::<TestValue>(); // 64 bytes
    const TARGET_COUNT: usize = (TARGET_MB * 1024 * 1024) / VALUE_SIZE;
    const CHURN_OPS: usize = 500_000;

    // --- Box under pressure ---
    println!(
        "  Box under {}MB pressure ({} allocations):",
        TARGET_MB, TARGET_COUNT
    );
    {
        // Build up pressure
        let mut items: Vec<Option<Box<TestValue>>> = Vec::with_capacity(TARGET_COUNT);
        for i in 0..TARGET_COUNT {
            items.push(Some(Box::new(TestValue::new(i as u64))));
        }
        println!("    Allocated {}MB of 64-byte objects", TARGET_MB);

        // Now churn while maintaining pressure
        let mut samples = Vec::with_capacity(CHURN_OPS);
        let mut rng = 12345u64;

        for _ in 0..CHURN_OPS {
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let idx = (rng as usize) % TARGET_COUNT;

            let start = rdtsc_start();
            if items[idx].is_some() {
                items[idx] = None;
            } else {
                items[idx] = Some(Box::new(TestValue::new(rng)));
            }
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Box (100MB)", &mut samples);
        drop(items);
    }

    // --- Slab under pressure ---
    println!();
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<TestValue> = unsafe { BoundedSlab::with_capacity(TARGET_COUNT) };

        // Build up pressure
        let mut items: Vec<Option<_>> = (0..TARGET_COUNT).map(|_| None).collect();

        for i in 0..TARGET_COUNT {
            items[i] = Some(alloc.alloc(TestValue::new(i as u64)));
        }
        println!("    Allocated {}MB in slab", TARGET_MB);

        // Now churn while maintaining pressure
        let mut samples = Vec::with_capacity(CHURN_OPS);
        let mut rng = 12345u64;

        for _ in 0..CHURN_OPS {
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let idx = (rng as usize) % TARGET_COUNT;

            let start = rdtsc_start();
            if let Some(slot) = items[idx].take() {
                // SAFETY: slot was allocated from this slab
                alloc.free(slot);
            } else {
                items[idx] = Some(alloc.alloc(TestValue::new(rng)));
            }
            samples.push(rdtsc_end() - start);
        }

        print_histogram("Slab (100MB)", &mut samples);
        // Clean up remaining items
        for item in items.into_iter().flatten() {
            alloc.free(item);
        }
    }
}

// ============================================================================
// Test 8: Size class comparison with pre-fragmented allocators
// ============================================================================

// POD types of various sizes
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod64 {
    data: [u8; 64],
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod128 {
    data: [u8; 128],
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod256 {
    data: [u8; 256],
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod512 {
    data: [u8; 512],
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod1024 {
    data: [u8; 1024],
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod2048 {
    data: [u8; 2048],
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod4096 {
    data: [u8; 4096],
}

// Manual Default impls (array Default only works up to 32 elements)
impl Default for Pod64 {
    fn default() -> Self {
        Self { data: [0; 64] }
    }
}
impl Default for Pod128 {
    fn default() -> Self {
        Self { data: [0; 128] }
    }
}
impl Default for Pod256 {
    fn default() -> Self {
        Self { data: [0; 256] }
    }
}
impl Default for Pod512 {
    fn default() -> Self {
        Self { data: [0; 512] }
    }
}
impl Default for Pod1024 {
    fn default() -> Self {
        Self { data: [0; 1024] }
    }
}
impl Default for Pod2048 {
    fn default() -> Self {
        Self { data: [0; 2048] }
    }
}
impl Default for Pod4096 {
    fn default() -> Self {
        Self { data: [0; 4096] }
    }
}

/// Fragment the global allocator with mixed-size allocations
fn fragment_global_allocator() -> Vec<Box<[u8]>> {
    let mut fragments = Vec::new();

    // Allocate mixed sizes to create fragmentation
    for i in 0..10_000 {
        let size = match i % 7 {
            0 => 64,
            1 => 128,
            2 => 256,
            3 => 512,
            4 => 1024,
            5 => 2048,
            _ => 4096,
        };
        fragments.push(vec![0u8; size].into_boxed_slice());
    }

    // Free every 3rd to create holes (swiss cheese)
    let fragments: Vec<_> = fragments
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % 3 != 0)
        .map(|(_, v)| v)
        .collect();

    fragments
}

#[allow(dead_code)]
fn print_full_histogram(name: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "    {:<14} p25={:>4} p50={:>4} p75={:>4} p90={:>4} p99={:>5} p99.9={:>5} p99.99={:>6} max={:>7}",
        name,
        percentile(samples, 25.0),
        percentile(samples, 50.0),
        percentile(samples, 75.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        percentile(samples, 99.99),
        samples.last().copied().unwrap_or(0),
    );
}

fn test_size_classes() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 8: SIZE CLASS COMPARISON (Realistic Conditions)");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Pre-conditions:");
    println!("    - Global allocator fragmented with mixed-size allocations");
    println!("    - Slab pre-filled to 10%, 25%, 50% capacity");
    println!("  Measuring churn (alloc+free) within remaining capacity\n");

    // Fragment the global allocator first
    let _fragments = fragment_global_allocator();
    println!("  Global allocator fragmented with ~6,666 mixed-size allocations\n");

    // Run all tests
    test_size_64();
    test_size_128();
    test_size_256();
    test_size_512();
    test_size_1024();
    test_size_2048();
    test_size_4096();
}

fn print_full_histogram_inline(samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        " p25={:>4} p50={:>4} p75={:>4} p90={:>4} p99={:>5} p99.9={:>5} p99.99={:>6} max={:>7}",
        percentile(samples, 25.0),
        percentile(samples, 50.0),
        percentile(samples, 75.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        percentile(samples, 99.99),
        samples.last().copied().unwrap_or(0),
    );
}

const SLAB_CAPACITY: usize = 10_000;
const SIZE_CHURN_OPS: usize = 50_000;

fn size_test<T: Default + Clone + 'static>(name: &str) {
    println!("  ── {} ──", name);

    // 10% fill
    {
        let fill = SLAB_CAPACITY / 10;
        let _box_long: Vec<Box<T>> = (0..fill).map(|_| Box::new(T::default())).collect();
        let mut box_samples = Vec::with_capacity(SIZE_CHURN_OPS);
        for _ in 0..SIZE_CHURN_OPS {
            let start = rdtsc_start();
            let item = Box::new(T::default());
            black_box(&*item);
            drop(item);
            box_samples.push(rdtsc_end() - start);
        }
        print!("  Box  10% fill");
        print_full_histogram_inline(&mut box_samples);

        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<T> = unsafe { BoundedSlab::with_capacity(SLAB_CAPACITY) };
        let _slab_long: Vec<_> = (0..fill).map(|_| alloc.alloc(T::default())).collect();
        let mut slab_samples = Vec::with_capacity(SIZE_CHURN_OPS);
        for _ in 0..SIZE_CHURN_OPS {
            let start = rdtsc_start();
            let item = alloc.alloc(T::default());
            black_box(&*item);
            // SAFETY: slot was allocated from this slab
            alloc.free(item);
            slab_samples.push(rdtsc_end() - start);
        }
        print!("  Slab 10% fill");
        print_full_histogram_inline(&mut slab_samples);
    }

    // 25% fill
    {
        let fill = SLAB_CAPACITY / 4;
        let _box_long: Vec<Box<T>> = (0..fill).map(|_| Box::new(T::default())).collect();
        let mut box_samples = Vec::with_capacity(SIZE_CHURN_OPS);
        for _ in 0..SIZE_CHURN_OPS {
            let start = rdtsc_start();
            let item = Box::new(T::default());
            black_box(&*item);
            drop(item);
            box_samples.push(rdtsc_end() - start);
        }
        print!("  Box  25% fill");
        print_full_histogram_inline(&mut box_samples);

        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<T> = unsafe { BoundedSlab::with_capacity(SLAB_CAPACITY) };
        let _slab_long: Vec<_> = (0..fill).map(|_| alloc.alloc(T::default())).collect();
        let mut slab_samples = Vec::with_capacity(SIZE_CHURN_OPS);
        for _ in 0..SIZE_CHURN_OPS {
            let start = rdtsc_start();
            let item = alloc.alloc(T::default());
            black_box(&*item);
            // SAFETY: slot was allocated from this slab
            alloc.free(item);
            slab_samples.push(rdtsc_end() - start);
        }
        print!("  Slab 25% fill");
        print_full_histogram_inline(&mut slab_samples);
    }

    // 50% fill
    {
        let fill = SLAB_CAPACITY / 2;
        let _box_long: Vec<Box<T>> = (0..fill).map(|_| Box::new(T::default())).collect();
        let mut box_samples = Vec::with_capacity(SIZE_CHURN_OPS);
        for _ in 0..SIZE_CHURN_OPS {
            let start = rdtsc_start();
            let item = Box::new(T::default());
            black_box(&*item);
            drop(item);
            box_samples.push(rdtsc_end() - start);
        }
        print!("  Box  50% fill");
        print_full_histogram_inline(&mut box_samples);

        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<T> = unsafe { BoundedSlab::with_capacity(SLAB_CAPACITY) };
        let _slab_long: Vec<_> = (0..fill).map(|_| alloc.alloc(T::default())).collect();
        let mut slab_samples = Vec::with_capacity(SIZE_CHURN_OPS);
        for _ in 0..SIZE_CHURN_OPS {
            let start = rdtsc_start();
            let item = alloc.alloc(T::default());
            black_box(&*item);
            // SAFETY: slot was allocated from this slab
            alloc.free(item);
            slab_samples.push(rdtsc_end() - start);
        }
        print!("  Slab 50% fill");
        print_full_histogram_inline(&mut slab_samples);
    }

    println!();
}

fn test_size_64() {
    size_test::<Pod64>("64B");
}
fn test_size_128() {
    size_test::<Pod128>("128B");
}
fn test_size_256() {
    size_test::<Pod256>("256B");
}
fn test_size_512() {
    size_test::<Pod512>("512B");
}
fn test_size_1024() {
    size_test::<Pod1024>("1024B");
}
fn test_size_2048() {
    size_test::<Pod2048>("2048B");
}
fn test_size_4096() {
    size_test::<Pod4096>("4096B");
}

// ============================================================================
// Test 9: Active contention - Box shares allocator, Slab is isolated
// ============================================================================

fn test_active_contention() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 9: ACTIVE CONTENTION (Isolation Advantage)");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Both: Same noise pattern hits global allocator BETWEEN batches");
    println!("  Box: Allocations GO THROUGH the (equally warm) global allocator");
    println!("  Slab: Allocations BYPASS global allocator entirely");
    println!("  This isolates the benefit of not sharing the allocator\n");

    test_contention_64();
    test_contention_256();
    test_contention_1024();
    test_contention_4096();
}

const CONTENTION_SAMPLES: usize = 5000;
const CONTENTION_BATCH: usize = 100;

fn contention_test<T: Default + Clone + 'static>(name: &str) {
    println!("  ── {} ──", name);

    // Box with randomized active contention
    {
        let mut samples = Vec::with_capacity(CONTENTION_SAMPLES);
        let mut rng = 12345u64;

        for _ in 0..CONTENTION_SAMPLES {
            // Randomized background noise (NOT timed)
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let noise_count = 20 + (rng % 60) as usize; // 20-80 allocations

            let mut noise: Vec<Box<[u8]>> = Vec::with_capacity(noise_count);
            for _ in 0..noise_count {
                rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let size = match rng % 7 {
                    0 => 32,
                    1 => 64,
                    2 => 128,
                    3 => 256,
                    4 => 512,
                    5 => 1024,
                    _ => 2048,
                };
                noise.push(vec![0u8; size as usize].into_boxed_slice());
            }

            // Free random subset (swiss cheese within noise)
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let keep_mod = (rng % 3) + 2; // keep all except every 2nd, 3rd, or 4th
            let noise: Vec<_> = noise
                .into_iter()
                .enumerate()
                .filter(|(i, _)| i % keep_mod as usize != 0)
                .map(|(_, v)| v)
                .collect();

            // Time a BATCH of allocations
            let start = rdtsc_start();
            for _ in 0..CONTENTION_BATCH {
                let item = Box::new(T::default());
                black_box(&*item);
                drop(item);
            }
            let elapsed = rdtsc_end() - start;
            samples.push(elapsed / CONTENTION_BATCH as u64);

            drop(noise); // Free remaining after measurement
        }

        print!("  Box  (contended)");
        print_full_histogram_inline(&mut samples);
    }

    // Slab - with same noise pattern (global allocator equally warm)
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<T> = unsafe { BoundedSlab::with_capacity(CONTENTION_BATCH + 100) };

        let mut samples = Vec::with_capacity(CONTENTION_SAMPLES);
        let mut rng = 12345u64; // Same seed for fair comparison

        for _ in 0..CONTENTION_SAMPLES {
            // SAME background noise as Box - keeps global allocator equally warm
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let noise_count = 20 + (rng % 60) as usize;

            let mut noise: Vec<Box<[u8]>> = Vec::with_capacity(noise_count);
            for _ in 0..noise_count {
                rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let size = match rng % 7 {
                    0 => 32,
                    1 => 64,
                    2 => 128,
                    3 => 256,
                    4 => 512,
                    5 => 1024,
                    _ => 2048,
                };
                noise.push(vec![0u8; size as usize].into_boxed_slice());
            }

            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let keep_mod = (rng % 3) + 2;
            let noise: Vec<_> = noise
                .into_iter()
                .enumerate()
                .filter(|(i, _)| i % keep_mod as usize != 0)
                .map(|(_, v)| v)
                .collect();

            // Time a BATCH of slab allocations
            // (slab doesn't use global allocator, but global allocator is equally warm)
            let start = rdtsc_start();
            for _ in 0..CONTENTION_BATCH {
                let item = alloc.alloc(T::default());
                black_box(&*item);
                // SAFETY: slot was allocated from this slab
                alloc.free(item);
            }
            let elapsed = rdtsc_end() - start;
            samples.push(elapsed / CONTENTION_BATCH as u64);

            drop(noise);
        }

        print!("  Slab (same noise)");
        print_full_histogram_inline(&mut samples);
    }

    println!();
}

fn test_contention_64() {
    contention_test::<Pod64>("64B");
}
fn test_contention_256() {
    contention_test::<Pod256>("256B");
}
fn test_contention_1024() {
    contention_test::<Pod1024>("1024B");
}
fn test_contention_4096() {
    contention_test::<Pod4096>("4096B");
}

// ============================================================================
// Test 10: First allocation latency (cold start)
// ============================================================================

fn test_first_allocation_latency() {
    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("TEST 10: FIRST ALLOCATION LATENCY (Cold Start)");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Measure the very first allocation after process start simulation");
    println!("  Box must potentially mmap memory; Slab is pre-allocated\n");

    // We can't truly restart the process, but we can simulate by:
    // 1. Allocating large chunks to exhaust thread cache
    // 2. Freeing them (but not returning to OS)
    // 3. Allocating a different size to force new arena activity

    const TRIALS: usize = 50;

    println!("  Measuring first allocation of each burst (after cache flush):\n");

    // Box - measure first allocation of each fresh burst
    {
        let mut first_alloc_times = Vec::with_capacity(TRIALS);

        for _ in 0..TRIALS {
            // Allocate a bunch of large objects to push out any cached memory
            let _flush: Vec<Box<[u8; 65536]>> = (0..100).map(|_| Box::new([0u8; 65536])).collect();

            // Now time the first 64-byte allocation
            let start = rdtsc_start();
            let item = Box::new(TestValue::new(0));
            let elapsed = rdtsc_end() - start;
            black_box(item);

            first_alloc_times.push(elapsed);
        }

        print_histogram("Box first alloc", &mut first_alloc_times);
    }

    // Slab - first allocation from pre-allocated pool
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let alloc: BoundedSlab<TestValue> = unsafe { BoundedSlab::with_capacity(1000) };

        let mut first_alloc_times = Vec::with_capacity(TRIALS);

        for _ in 0..TRIALS {
            // Drain and refill to simulate "first" allocation
            let items: Vec<_> = (0..1000)
                .map(|i| alloc.alloc(TestValue::new(i as u64)))
                .collect();
            // Free all items
            for item in items {
                // SAFETY: slot was allocated from this slab
                alloc.free(item);
            }

            // Now time the first allocation
            let start = rdtsc_start();
            let item = alloc.alloc(TestValue::new(0));
            let elapsed = rdtsc_end() - start;
            black_box(&*item);
            // SAFETY: slot was allocated from this slab
            alloc.free(item);

            first_alloc_times.push(elapsed);
        }

        print_histogram("Slab first alloc", &mut first_alloc_times);
    }

    println!("\n  Note: Box 'first alloc' includes potential heap management overhead.");
    println!("  Slab 'first alloc' is just a freelist pop - O(1) always.");
}

fn main() {
    println!("╔═══════════════════════════════════════════════════════════════════╗");
    println!("║           NEXUS-SLAB vs BOX - STRESS TEST SUITE                   ║");
    println!("╠═══════════════════════════════════════════════════════════════════╣");
    println!(
        "║  Value size: {} bytes                                              ║",
        std::mem::size_of::<TestValue>()
    );
    println!("║  Tests: Churn, Bursts, Fragmentation, Contention, Tail latency    ║");
    println!("╚═══════════════════════════════════════════════════════════════════╝");

    // NOTE: For accurate contention test results, run it first or in isolation.
    // Memory-intensive tests can pollute cache/TLB and skew results.
    // See BENCHMARKS.md "Benchmark Isolation Warning" for details.
    test_active_contention();

    test_long_running_churn();
    test_burst_allocation();
    test_mixed_lifetimes();
    test_fifo_queue();
    test_tail_latency();
    test_brutal_fragmentation();
    test_sustained_pressure();
    test_size_classes();
    test_first_allocation_latency();

    println!("\n═══════════════════════════════════════════════════════════════════");
    println!("SUMMARY");
    println!("═══════════════════════════════════════════════════════════════════");
    println!("  Box advantages:");
    println!("    - No setup cost (no init() required)");
    println!("    - Works with any type without macro");
    println!("    - Familiar API");
    println!();
    println!("  Slab advantages:");
    println!("    - Isolated from global allocator contention");
    println!("    - Consistent tail latency (no OS interaction after init)");
    println!("    - No fragmentation (fixed-size slots)");
    println!("    - Better cache locality (contiguous memory)");
    println!("    - Faster deallocation (~2x)");
    println!("    - 8-byte handles vs 8-byte Box (same, but Slot has key access)");
}
