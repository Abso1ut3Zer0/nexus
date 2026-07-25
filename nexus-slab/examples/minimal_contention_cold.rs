//! Cold cache contention test - evicts allocator state between measurements
//!
//! Methodology:
//! - Uses 24MB eviction buffer (2x L3 cache size)
//! - Strided access pattern to defeat hardware prefetchers
//! - Interleaved Box/Slab measurements to avoid ordering bias
//! - BATCH=10 amortizes rdtsc overhead while measuring cold-start behavior

use nexus_slab::Slot;
use nexus_slab::bounded::Slab as BoundedSlab;
use std::hint::black_box;

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod64 {
    data: [u8; 64],
}
impl Default for Pod64 {
    fn default() -> Self {
        Self { data: [0; 64] }
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod256 {
    data: [u8; 256],
}
impl Default for Pod256 {
    fn default() -> Self {
        Self { data: [0; 256] }
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod4096 {
    data: [u8; 4096],
}
impl Default for Pod4096 {
    fn default() -> Self {
        Self { data: [0; 4096] }
    }
}

const SAMPLES: usize = 5000;
const BATCH: usize = 10;

// 24MB eviction buffer - 2x L3 cache to ensure full eviction
// Using 2x cache size ensures even with set-associativity we evict everything
use std::cell::UnsafeCell;
struct EvictBuffer(UnsafeCell<[u8; 24 * 1024 * 1024]>);
// SAFETY: `EvictBuffer` wraps `UnsafeCell`; `evict_cache` is the only
// accessor and is called single-threaded from main.
unsafe impl Sync for EvictBuffer {}
static EVICT_BUFFER: EvictBuffer = EvictBuffer(UnsafeCell::new([0u8; 24 * 1024 * 1024]));

#[inline(never)]
fn evict_cache() {
    // Strided access pattern to defeat prefetchers
    // Stride of 4097 bytes (not power of 2, crosses cache lines unpredictably)
    // This forces actual memory fetches rather than prefetcher hits
    // SAFETY: single-threaded; no other reference to `EVICT_BUFFER` exists
    // during this call.
    unsafe {
        let buf = &mut *EVICT_BUFFER.0.get();
        let len = buf.len();
        let stride = 4097;
        let mut i = 0;
        while i < len {
            // Read-modify-write to ensure the line is fetched and dirtied
            buf[i] = buf[i].wrapping_add(1);
            i += stride;
        }
        // Second pass with different offset to hit remaining cache sets
        i = 64;
        while i < len {
            buf[i] = buf[i].wrapping_add(1);
            i += stride;
        }
        black_box(buf);
    }
}

#[inline(never)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsics; benchmark is x86_64-only.
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(never)]
fn rdtsc_end() -> u64 {
    let mut aux: u32 = 0;
    // SAFETY: x86_64 intrinsics; benchmark is x86_64-only.
    unsafe {
        let t = core::arch::x86_64::__rdtscp(&raw mut aux);
        core::arch::x86_64::_mm_lfence();
        t
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_stats(name: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {} p25={:3} p50={:3} p75={:3} p90={:3} p99={:4} p99.9={:5}",
        name,
        percentile(samples, 25.0),
        percentile(samples, 50.0),
        percentile(samples, 75.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9)
    );
}

fn cold_test<T: Default + Clone>(name: &str, slab: &BoundedSlab<T>) {
    println!("\n  -- {} (COLD) --", name);

    let mut box_samples = Vec::with_capacity(SAMPLES);
    let mut slab_samples = Vec::with_capacity(SAMPLES);

    // Interleaved measurement - alternating Box/Slab to avoid ordering bias
    for i in 0..SAMPLES {
        #[allow(clippy::branches_sharing_code)]
        if i % 2 == 0 {
            // Box first this iteration
            evict_cache();
            let start = rdtsc_start();
            for _ in 0..BATCH {
                let item = Box::new(T::default());
                black_box(&*item);
                drop(item);
            }
            let elapsed = rdtsc_end() - start;
            box_samples.push(elapsed / BATCH as u64);

            evict_cache();
            let start = rdtsc_start();
            for _ in 0..BATCH {
                let slot: Slot<T> = slab.alloc(T::default());
                black_box(&*slot);
                // SAFETY: slot was allocated from this slab
                slab.free(slot);
            }
            let elapsed = rdtsc_end() - start;
            slab_samples.push(elapsed / BATCH as u64);
        } else {
            // Slab first this iteration
            evict_cache();
            let start = rdtsc_start();
            for _ in 0..BATCH {
                let slot: Slot<T> = slab.alloc(T::default());
                black_box(&*slot);
                // SAFETY: slot was allocated from this slab
                slab.free(slot);
            }
            let elapsed = rdtsc_end() - start;
            slab_samples.push(elapsed / BATCH as u64);

            evict_cache();
            let start = rdtsc_start();
            for _ in 0..BATCH {
                let item = Box::new(T::default());
                black_box(&*item);
                drop(item);
            }
            let elapsed = rdtsc_end() - start;
            box_samples.push(elapsed / BATCH as u64);
        }
    }

    print_stats(&format!("Box  ({})", name), &mut box_samples);
    print_stats(&format!("Slab ({})", name), &mut slab_samples);
}

fn main() {
    println!("COLD CACHE CONTENTION TEST");
    println!("==========================");
    println!("  24MB eviction buffer (2x L3), strided access, interleaved measurement");

    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab64 = unsafe { BoundedSlab::<Pod64>::with_capacity(SAMPLES * 2) };
    cold_test("64B", &slab64);

    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab256 = unsafe { BoundedSlab::<Pod256>::with_capacity(SAMPLES * 2) };
    cold_test("256B", &slab256);

    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab4096 = unsafe { BoundedSlab::<Pod4096>::with_capacity(SAMPLES * 2) };
    cold_test("4096B", &slab4096);
}
