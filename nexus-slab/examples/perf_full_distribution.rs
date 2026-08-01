//! Latency distribution benchmarks for nexus-slab vs slab crate.
//!
//! Uses unrolled loops (100 ops) to eliminate loop overhead and measure
//! actual CPU cycles per operation.
//!
//! Run with:
//!   cargo build --release --example perf_full_distribution
//!   taskset -c 0 ./target/release/examples/perf_full_distribution

#![allow(clippy::iter_with_drain)]

use hdrhistogram::Histogram;
use nexus_slab::Slot;
use nexus_slab::bounded::Slab as BoundedSlab;
use seq_macro::seq;
use std::hint::black_box;

const NUM_SLOTS: usize = 10_000;
const OPS: usize = 500_000;
const BATCH_SIZE: u64 = 100;

/// Unroll N iterations of an expression - no loop overhead, just straight-line code.
macro_rules! unroll {
    ($n:literal, $op:expr) => {
        seq!(_ in 0..$n { $op; })
    };
}

#[inline(always)]
fn rdtsc_start() -> u64 {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: x86_64 intrinsics; benchmark is x86_64-only.
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
    #[cfg(not(target_arch = "x86_64"))]
    panic!("rdtsc only supported on x86_64")
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: x86_64 intrinsics; benchmark is x86_64-only.
    unsafe {
        let tsc = std::arch::x86_64::__rdtscp(&mut 0u32 as *mut _);
        std::arch::x86_64::_mm_lfence();
        tsc
    }
    #[cfg(not(target_arch = "x86_64"))]
    panic!("rdtsc only supported on x86_64")
}

fn print_hist(name: &str, hist: &Histogram<u64>) {
    println!(
        "  {:28} p50={:>3}  p90={:>3}  p99={:>3}  p99.9={:>4}  max={:>6}",
        name,
        hist.value_at_quantile(0.50),
        hist.value_at_quantile(0.90),
        hist.value_at_quantile(0.99),
        hist.value_at_quantile(0.999),
        hist.max()
    );
}

// =============================================================================
// GET Benchmarks
// =============================================================================

fn bench_get() {
    println!("GET (cycles per operation)");
    println!("--------------------------");

    let mut entry_hist: Histogram<u64> = Histogram::new(3).unwrap();
    let mut entry_hot_hist: Histogram<u64> = Histogram::new(3).unwrap();
    let mut slab_hist: Histogram<u64> = Histogram::new(3).unwrap();
    let mut slab_hot_hist: Histogram<u64> = Histogram::new(3).unwrap();

    // Setup slab
    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(NUM_SLOTS) };
    let entries: Vec<Slot<u64>> = (0..NUM_SLOTS as u64).map(|i| slab.alloc(i)).collect();

    // Setup slab crate
    let mut ext_slab = slab::Slab::<u64>::with_capacity(NUM_SLOTS);
    let keys: Vec<_> = (0..NUM_SLOTS as u64).map(|i| ext_slab.insert(i)).collect();

    // slot deref - random access
    let mut idx = 0usize;
    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let entry = black_box(&entries[idx % NUM_SLOTS]);
            black_box(&**entry);
            idx = idx.wrapping_add(1);
        });
        let end = rdtsc_end();
        let _ = entry_hist.record((end - start) / BATCH_SIZE);
    }

    // slot deref - hot (same slot)
    let hot_entry = &entries[0];
    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let entry = black_box(hot_entry);
            black_box(&**entry);
        });
        let end = rdtsc_end();
        let _ = entry_hot_hist.record((end - start) / BATCH_SIZE);
    }

    // slab.get() - random access
    idx = 0;
    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let slab_ref = black_box(&ext_slab);
            let key = black_box(keys[idx % NUM_SLOTS]);
            black_box(slab_ref.get(key));
            idx = idx.wrapping_add(1);
        });
        let end = rdtsc_end();
        let _ = slab_hist.record((end - start) / BATCH_SIZE);
    }

    // slab.get() - hot (same key)
    let hot_key = keys[0];
    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let slab_ref = black_box(&ext_slab);
            let key = black_box(hot_key);
            black_box(slab_ref.get(key));
        });
        let end = rdtsc_end();
        let _ = slab_hot_hist.record((end - start) / BATCH_SIZE);
    }

    print_hist("slot deref random", &entry_hist);
    print_hist("slot deref hot", &entry_hot_hist);
    print_hist("slab.get() random", &slab_hist);
    print_hist("slab.get() hot", &slab_hot_hist);
    println!();

    // Cleanup - free all slots
    for slot in entries {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

// =============================================================================
// GET_MUT Benchmarks
// =============================================================================

fn bench_get_mut() {
    println!("GET_MUT (cycles per operation)");
    println!("------------------------------");

    let mut entry_hist: Histogram<u64> = Histogram::new(3).unwrap();
    let mut slab_hist: Histogram<u64> = Histogram::new(3).unwrap();

    // Setup slab
    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(NUM_SLOTS) };
    let mut entries: Vec<Slot<u64>> = (0..NUM_SLOTS as u64).map(|i| slab.alloc(i)).collect();

    // Setup slab crate
    let mut ext_slab = slab::Slab::<u64>::with_capacity(NUM_SLOTS);
    let keys: Vec<_> = (0..NUM_SLOTS as u64).map(|i| ext_slab.insert(i)).collect();

    // slot deref_mut - random access
    let mut idx = 0usize;
    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let entry = black_box(&mut entries[idx % NUM_SLOTS]);
            black_box(&mut **entry);
            idx = idx.wrapping_add(1);
        });
        let end = rdtsc_end();
        let _ = entry_hist.record((end - start) / BATCH_SIZE);
    }

    // slab.get_mut() - random access
    idx = 0;
    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let slab_ref = black_box(&mut ext_slab);
            let key = black_box(keys[idx % NUM_SLOTS]);
            black_box(slab_ref.get_mut(key));
            idx = idx.wrapping_add(1);
        });
        let end = rdtsc_end();
        let _ = slab_hist.record((end - start) / BATCH_SIZE);
    }

    print_hist("slot deref_mut()", &entry_hist);
    print_hist("slab.get_mut()", &slab_hist);
    println!();

    // Cleanup
    for slot in entries {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

// =============================================================================
// INSERT Benchmarks
// =============================================================================

fn bench_insert() {
    println!("INSERT (cycles per operation)");
    println!("-----------------------------");

    let mut entry_hist: Histogram<u64> = Histogram::new(3).unwrap();
    let mut slab_hist: Histogram<u64> = Histogram::new(3).unwrap();

    // slab insert - need to remove after each batch to make room
    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(NUM_SLOTS) };
    let mut temp_entries: Vec<Slot<u64>> = Vec::with_capacity(BATCH_SIZE as usize);

    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let entry = slab.try_alloc(black_box(42u64)).unwrap();
            temp_entries.push(entry);
        });
        let end = rdtsc_end();
        let _ = entry_hist.record((end - start) / BATCH_SIZE);

        // Cleanup batch
        for entry in temp_entries.drain(..) {
            // SAFETY: slot was allocated from this slab
            slab.free(entry);
        }
    }

    // slab crate insert
    let mut ext_slab = slab::Slab::<u64>::with_capacity(NUM_SLOTS);
    let mut temp_keys: Vec<usize> = Vec::with_capacity(BATCH_SIZE as usize);

    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let slab_ref = black_box(&mut ext_slab);
            let key = slab_ref.insert(black_box(42u64));
            temp_keys.push(key);
        });
        let end = rdtsc_end();
        let _ = slab_hist.record((end - start) / BATCH_SIZE);

        // Cleanup batch
        for key in temp_keys.drain(..) {
            ext_slab.remove(key);
        }
    }

    print_hist("slab insert", &entry_hist);
    print_hist("slab crate insert", &slab_hist);
    println!();
}

// =============================================================================
// REMOVE Benchmarks
// =============================================================================

#[allow(unused_assignments)]
fn bench_remove() {
    println!("REMOVE (cycles per operation)");
    println!("-----------------------------");

    let mut entry_hist: Histogram<u64> = Histogram::new(3).unwrap();
    let mut slab_hist: Histogram<u64> = Histogram::new(3).unwrap();

    // slot free_take - insert batch, then remove batch
    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(NUM_SLOTS) };

    for _ in 0..OPS / BATCH_SIZE as usize {
        // Insert batch
        let mut temp_entries: Vec<Slot<u64>> = Vec::with_capacity(BATCH_SIZE as usize);
        for _ in 0..BATCH_SIZE {
            temp_entries.push(slab.alloc(42u64));
        }

        // Time the removes
        let start = rdtsc_start();
        unroll!(100, {
            let entry = temp_entries.pop().unwrap();
            // SAFETY: slot was allocated from this slab
            black_box(slab.take(entry));
        });
        let end = rdtsc_end();
        let _ = entry_hist.record((end - start) / BATCH_SIZE);
    }

    // slab.remove()
    let mut ext_slab = slab::Slab::<u64>::with_capacity(NUM_SLOTS);

    for _ in 0..OPS / BATCH_SIZE as usize {
        // Insert batch
        let temp_keys: Vec<_> = (0..BATCH_SIZE).map(|_| ext_slab.insert(42u64)).collect();

        let mut idx = 0usize;
        let start = rdtsc_start();
        unroll!(100, {
            let slab_ref = black_box(&mut ext_slab);
            let key = black_box(temp_keys[idx]);
            black_box(slab_ref.remove(key));
            idx += 1;
        });
        let end = rdtsc_end();
        let _ = slab_hist.record((end - start) / BATCH_SIZE);
    }

    print_hist("slab.take()", &entry_hist);
    print_hist("slab.remove()", &slab_hist);
    println!();
}

// =============================================================================
// REPLACE Benchmarks
// =============================================================================

fn bench_replace() {
    println!("REPLACE (cycles per operation)");
    println!("------------------------------");

    let mut entry_hist: Histogram<u64> = Histogram::new(3).unwrap();
    let mut slab_hist: Histogram<u64> = Histogram::new(3).unwrap();

    // Setup slab
    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(NUM_SLOTS) };
    let mut entries: Vec<Slot<u64>> = (0..NUM_SLOTS as u64).map(|i| slab.alloc(i)).collect();

    // Setup slab crate
    let mut ext_slab = slab::Slab::<u64>::with_capacity(NUM_SLOTS);
    let keys: Vec<_> = (0..NUM_SLOTS as u64).map(|i| ext_slab.insert(i)).collect();

    // slot replace via deref_mut
    let mut idx = 0usize;
    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let entry = black_box(&mut entries[idx % NUM_SLOTS]);
            black_box(std::mem::replace(&mut **entry, black_box(999u64)));
            idx = idx.wrapping_add(1);
        });
        let end = rdtsc_end();
        let _ = entry_hist.record((end - start) / BATCH_SIZE);
    }

    // slab get_mut + replace
    idx = 0;
    for _ in 0..OPS / BATCH_SIZE as usize {
        let start = rdtsc_start();
        unroll!(100, {
            let slab_ref = black_box(&mut ext_slab);
            let key = black_box(keys[idx % NUM_SLOTS]);
            if let Some(v) = slab_ref.get_mut(key) {
                black_box(std::mem::replace(v, black_box(999u64)));
            }
            idx = idx.wrapping_add(1);
        });
        let end = rdtsc_end();
        let _ = slab_hist.record((end - start) / BATCH_SIZE);
    }

    print_hist("slot replace via *slot", &entry_hist);
    print_hist("slab get_mut+replace", &slab_hist);
    println!();

    // Cleanup
    for slot in entries {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

// =============================================================================
// Main
// =============================================================================

fn main() {
    println!("RAW SLAB API vs SLAB CRATE - CYCLE COUNTS");
    println!("=========================================");
    println!("Compare these results against BENCHMARKS.md");
    println!(
        "Unrolled {} ops per sample, {} total ops per benchmark",
        BATCH_SIZE, OPS
    );
    println!("All times in CPU cycles (lfence+rdtsc, loop overhead eliminated)");
    println!();
    println!(
        "Slot<T> size: {} bytes (pointer wrapper, no RAII)",
        std::mem::size_of::<Slot<u64>>()
    );
    println!();

    // Warmup: exercise slab and slab-crate paths to trigger page faults,
    // TLS init, and cache priming before timed measurements.
    {
        // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
        let warmup_slab = unsafe { BoundedSlab::<u64>::with_capacity(NUM_SLOTS) };
        let warmup_entries: Vec<Slot<u64>> = (0..NUM_SLOTS as u64)
            .map(|i| warmup_slab.alloc(i))
            .collect();
        for slot in &warmup_entries {
            black_box(&**slot);
        }
        for slot in warmup_entries {
            warmup_slab.free(slot);
        }
        let mut warmup_ext = slab::Slab::<u64>::with_capacity(NUM_SLOTS);
        let warmup_keys: Vec<_> = (0..NUM_SLOTS as u64)
            .map(|i| warmup_ext.insert(i))
            .collect();
        for &k in &warmup_keys {
            black_box(warmup_ext.get(k));
        }
        for k in warmup_keys {
            warmup_ext.remove(k);
        }
    }

    bench_get();
    bench_get_mut();
    bench_insert();
    bench_remove();
    bench_replace();

    println!("=========================================");
    println!("Legend:");
    println!("  slot.*()              Slot<T> API (8-byte ptr, explicit free)");
    println!("  slab.*()              slab crate (baseline comparison)");
}
