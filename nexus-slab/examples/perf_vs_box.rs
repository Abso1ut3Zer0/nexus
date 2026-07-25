#![allow(clippy::large_stack_frames)]
//! Benchmark: nexus-slab vs Box across value sizes.
//!
//! Uses batched unrolled timing (64 ops per rdtsc pair) to amortize
//! the ~20 cycle rdtsc overhead.
//!
//! Run with: `taskset -c 0 ./target/release/examples/perf_vs_box`

use nexus_slab::bounded::Slab as BoundedSlab;
use std::hint::black_box;

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
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_row(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {:<40} {:>6} {:>6} {:>6} {:>7} {:>7}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

const SAMPLES: usize = 10_000;
const BATCH: u64 = 64;

macro_rules! unroll_8 {
    ($op:expr) => {
        $op;
        $op;
        $op;
        $op;
        $op;
        $op;
        $op;
        $op;
    };
}

macro_rules! unroll_64 {
    ($op:expr) => {
        unroll_8!($op);
        unroll_8!($op);
        unroll_8!($op);
        unroll_8!($op);
        unroll_8!($op);
        unroll_8!($op);
        unroll_8!($op);
        unroll_8!($op);
    };
}

macro_rules! bench_size {
    ($name:ident, $size:expr) => {
        fn $name() {
            #[derive(Clone)]
            #[repr(C)]
            struct Value {
                data: [u8; $size],
            }

            impl Value {
                fn new(seed: u64) -> Self {
                    let mut data = [0u8; $size];
                    let bytes = seed.to_le_bytes();
                    let len = bytes.len().min($size);
                    data[..len].copy_from_slice(&bytes[..len]);
                    Self { data }
                }
            }

            let label = format!("{}B", $size);

            // --- ALLOC (batched) ---
            {
                let slab: BoundedSlab<Value> =
                    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
                    unsafe { BoundedSlab::with_capacity(BATCH as usize * 2) };
                let mut slab_samples = Vec::with_capacity(SAMPLES);
                let mut box_samples = Vec::with_capacity(SAMPLES);

                for i in 0..SAMPLES {
                    let val = Value::new(i as u64);

                    let start = rdtsc_start();
                    unroll_64!({
                        let s = slab.alloc(val.clone());
                        slab.free(s);
                    });
                    let end = rdtsc_end();
                    slab_samples.push((end - start) / BATCH);

                    let start = rdtsc_start();
                    unroll_64!({
                        let b = Box::new(val.clone());
                        black_box(b);
                    });
                    let end = rdtsc_end();
                    box_samples.push((end - start) / BATCH);
                }
                print_row(&format!("slab alloc+free {label}"), &mut slab_samples);
                print_row(&format!("Box  new+drop   {label}"), &mut box_samples);
            }

            // --- FREE only (pre-alloc, then batch free) ---
            {
                let slab: BoundedSlab<Value> =
                    // SAFETY: single-threaded benchmark; slab outlives all allocated slots.
                    unsafe { BoundedSlab::with_capacity(BATCH as usize * SAMPLES) };
                let mut slab_samples = Vec::with_capacity(SAMPLES);
                let mut box_samples = Vec::with_capacity(SAMPLES);

                for i in 0..SAMPLES {
                    // Pre-alloc batch for slab
                    let mut slots = Vec::with_capacity(BATCH as usize);
                    for j in 0..BATCH {
                        slots.push(slab.alloc(Value::new(i as u64 * BATCH + j)));
                    }
                    let mut iter = slots.into_iter();

                    let start = rdtsc_start();
                    unroll_64!({
                        slab.free(iter.next().unwrap());
                    });
                    let end = rdtsc_end();
                    slab_samples.push((end - start) / BATCH);

                    // Pre-alloc batch for box
                    let boxes: Vec<_> = (0..BATCH)
                        .map(|j| Box::new(Value::new(i as u64 * BATCH + j)))
                        .collect();
                    let mut iter = boxes.into_iter();

                    let start = rdtsc_start();
                    unroll_64!({
                        drop(black_box(iter.next()));
                    });
                    let end = rdtsc_end();
                    box_samples.push((end - start) / BATCH);
                }
                print_row(&format!("slab free       {label}"), &mut slab_samples);
                print_row(&format!("drop(Box)       {label}"), &mut box_samples);
            }

            println!();
        }
    };
}

bench_size!(bench_32, 32);
bench_size!(bench_64, 64);
bench_size!(bench_128, 128);
bench_size!(bench_256, 256);
bench_size!(bench_512, 512);
bench_size!(bench_1024, 1024);
bench_size!(bench_4096, 4096);

fn main() {
    println!("NEXUS-SLAB vs BOX — MULTI-SIZE BENCHMARK");
    println!("=========================================");
    println!(
        "Batched timing (64 ops per rdtsc), pinned core, {} samples\n",
        SAMPLES
    );
    println!(
        "  {:<40} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );
    println!();

    bench_32();
    bench_64();
    bench_128();
    bench_256();
    bench_512();
    bench_1024();
    bench_4096();
}
