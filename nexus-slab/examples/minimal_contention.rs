//! Minimal isolated contention test - run this ALONE for accurate numbers

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
pub struct Pod1024 {
    data: [u8; 1024],
}
impl Default for Pod1024 {
    fn default() -> Self {
        Self { data: [0; 1024] }
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
const BATCH: usize = 100;

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
        "  {} p25={:3} p50={:3} p75={:3} p90={:3} p99={:4} p99.9={:5} p99.99={:6} max={:6}",
        name,
        percentile(samples, 25.0),
        percentile(samples, 50.0),
        percentile(samples, 75.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        percentile(samples, 99.99),
        samples.last().unwrap()
    );
}

fn contention_test<T: Default + Clone>(name: &str, slab: &BoundedSlab<T>) {
    println!("\n  -- {} --", name);

    let mut rng = 12345u64;
    let mut box_samples = Vec::with_capacity(SAMPLES);
    let mut slab_samples = Vec::with_capacity(SAMPLES);

    // Box with contention
    for _ in 0..SAMPLES {
        // Random noise to global allocator (NOT timed)
        rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let noise_count = 20 + (rng % 60) as usize;
        let mut noise: Vec<Box<[u8]>> = Vec::with_capacity(noise_count);
        for _ in 0..noise_count {
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let size = 32 << (rng % 6);
            noise.push(vec![0u8; size as usize].into_boxed_slice());
        }
        // Swiss cheese
        rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let keep = 50 + (rng % 25) as usize;
        while noise.len() > keep {
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let idx = (rng as usize) % noise.len();
            noise.swap_remove(idx);
        }

        // Time batch
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let item = Box::new(T::default());
            black_box(&*item);
            drop(item);
        }
        let elapsed = rdtsc_end() - start;
        box_samples.push(elapsed / BATCH as u64);
        drop(noise);
    }

    // Reset RNG for same noise pattern
    rng = 12345u64;

    // Slab with same noise
    for _ in 0..SAMPLES {
        rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let noise_count = 20 + (rng % 60) as usize;
        let mut noise: Vec<Box<[u8]>> = Vec::with_capacity(noise_count);
        for _ in 0..noise_count {
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let size = 32 << (rng % 6);
            noise.push(vec![0u8; size as usize].into_boxed_slice());
        }
        rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let keep = 50 + (rng % 25) as usize;
        while noise.len() > keep {
            rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            let idx = (rng as usize) % noise.len();
            noise.swap_remove(idx);
        }

        let start = rdtsc_start();
        for _ in 0..BATCH {
            let slot = slab.alloc(T::default());
            black_box(&*slot);
            // SAFETY: slot was allocated from this slab
            slab.free(slot);
        }
        let elapsed = rdtsc_end() - start;
        slab_samples.push(elapsed / BATCH as u64);
        drop(noise);
    }

    print_stats(&format!("Box  ({})", name), &mut box_samples);
    print_stats(&format!("Slab ({})", name), &mut slab_samples);
}

fn main() {
    println!("ISOLATED CONTENTION TEST");
    println!("========================");

    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab64 = unsafe { BoundedSlab::<Pod64>::with_capacity(SAMPLES * 2) };
    contention_test("64B", &slab64);

    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab256 = unsafe { BoundedSlab::<Pod256>::with_capacity(SAMPLES * 2) };
    contention_test("256B", &slab256);

    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab1024 = unsafe { BoundedSlab::<Pod1024>::with_capacity(SAMPLES * 2) };
    contention_test("1024B", &slab1024);

    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
    let slab4096 = unsafe { BoundedSlab::<Pod4096>::with_capacity(SAMPLES * 2) };
    contention_test("4096B", &slab4096);
}
