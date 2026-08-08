//! Shared benchmark utilities for cycle-accurate performance examples.
//!
//! Provides rdtsc helpers and percentile reporting. Included via
//! `#[path = "_bench_utils.rs"]` in benchmark examples.

#![allow(dead_code)]

use std::hint::black_box;

pub const ITERATIONS: usize = 100_000;
pub const WARMUP: usize = 10_000;
pub const BATCH: u64 = 100;

#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub fn rdtsc() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe { core::arch::x86_64::_rdtsc() }
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
pub fn rdtsc() -> u64 {
    std::time::Instant::now().elapsed().as_nanos() as u64
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub fn rdtsc_fenced_start() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
pub fn rdtsc_fenced_start() -> u64 {
    std::time::Instant::now().elapsed().as_nanos() as u64
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub fn rdtsc_fenced_end() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe {
        let mut aux = 0u32;
        let tsc = core::arch::x86_64::__rdtscp(&raw mut aux);
        core::arch::x86_64::_mm_lfence();
        tsc
    }
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
pub fn rdtsc_fenced_end() -> u64 {
    std::time::Instant::now().elapsed().as_nanos() as u64
}

#[inline]
pub fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

pub fn bench<T, F: FnMut() -> T>(name: &str, mut f: F) -> (u64, u64, u64) {
    for _ in 0..WARMUP {
        black_box(f());
    }

    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = rdtsc();
        black_box(f());
        let end = rdtsc();
        samples.push(end.wrapping_sub(start));
    }

    samples.sort_unstable();
    let p50 = percentile(&samples, 50.0);
    let p99 = percentile(&samples, 99.0);
    let p999 = percentile(&samples, 99.9);

    println!("{:<40} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

pub fn print_header(title: &str) {
    println!("=== {} ===\n", title);
    println!(
        "{:<40} {:>8} {:>8} {:>8}",
        "Operation", "p50", "p99", "p999"
    );
    println!("{}", "-".repeat(68));
}

pub fn print_intro(title: &str) {
    println!("{}", title);
    println!("{}\n", "=".repeat(title.len()));
    println!("Iterations: {}, Warmup: {}", ITERATIONS, WARMUP);
    println!("All times in CPU cycles\n");
}

fn main() {
    eprintln!("This is a utility module. Run one of the perf_* examples instead.");
}
