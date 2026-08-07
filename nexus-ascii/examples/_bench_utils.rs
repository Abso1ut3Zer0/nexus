//! Shared benchmark utilities for performance examples.
//!
//! This module provides common functions for cycle-accurate benchmarking
//! using rdtsc and percentile-based statistics.

#![allow(dead_code)]

use std::hint::black_box;

/// Number of iterations for benchmark measurements.
pub const ITERATIONS: usize = 100_000;

/// Number of warmup iterations before measurement.
pub const WARMUP: usize = 10_000;

/// Read the CPU timestamp counter (cycles).
///
/// On x86_64, uses the `rdtsc` instruction directly.
/// On other architectures, falls back to `Instant::now()`.
#[inline]
#[cfg(target_arch = "x86_64")]
pub fn rdtsc() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe { core::arch::x86_64::_rdtsc() }
}

#[inline]
#[cfg(not(target_arch = "x86_64"))]
pub fn rdtsc() -> u64 {
    std::time::Instant::now().elapsed().as_nanos() as u64
}

/// Calculate the percentile value from a sorted slice.
///
/// # Arguments
/// * `sorted` - A sorted slice of samples
/// * `p` - Percentile to calculate (0.0 to 100.0)
#[inline]
pub fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

/// Run a benchmark and print results.
///
/// Performs warmup iterations, then collects samples and reports
/// p50, p99, and p999 latencies in CPU cycles.
///
/// # Arguments
/// * `name` - Name of the benchmark (left-aligned, 40 chars)
/// * `f` - Closure to benchmark, returns a value to prevent optimization
///
/// # Returns
/// Tuple of (p50, p99, p999) cycle counts
pub fn bench<F: FnMut() -> u64>(name: &str, mut f: F) -> (u64, u64, u64) {
    // Warmup
    for _ in 0..WARMUP {
        black_box(f());
    }

    // Collect samples
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

/// Run a benchmark with a wider name column (45 chars).
///
/// Same as `bench()` but with more space for longer operation names.
pub fn bench_wide<F: FnMut() -> u64>(name: &str, mut f: F) -> (u64, u64, u64) {
    // Warmup
    for _ in 0..WARMUP {
        black_box(f());
    }

    // Collect samples
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

    println!("{:<45} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

/// Print a section header for benchmark output.
pub fn print_header(title: &str) {
    println!("=== {} ===\n", title);
    println!(
        "{:<40} {:>8} {:>8} {:>8}",
        "Operation", "p50", "p99", "p999"
    );
    println!("{}", "-".repeat(68));
}

/// Print a section header with wide name column.
pub fn print_header_wide(title: &str) {
    println!("=== {} ===\n", title);
    println!(
        "{:<45} {:>8} {:>8} {:>8}",
        "Operation", "p50", "p99", "p999"
    );
    println!("{}", "-".repeat(73));
}

/// Print benchmark intro with iterations and warmup counts.
pub fn print_intro(title: &str) {
    println!("{}", title);
    println!("{}\n", "=".repeat(title.len()));
    println!("Iterations: {}, Warmup: {}", ITERATIONS, WARMUP);
    println!("All times in CPU cycles\n");
}

/// Run a benchmark where the closure handles its own timing.
///
/// The closure is responsible for calling `rdtsc()` around the operation
/// under test and returning the elapsed cycle count. This allows
/// setup/teardown code to live outside the timing window.
pub fn bench_raw<F: FnMut() -> u64>(name: &str, mut f: F) -> (u64, u64, u64) {
    // Warmup
    for _ in 0..WARMUP {
        f();
    }

    // Collect samples
    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        samples.push(f());
    }

    samples.sort_unstable();
    let p50 = percentile(&samples, 50.0);
    let p99 = percentile(&samples, 99.0);
    let p999 = percentile(&samples, 99.9);

    println!("{:<40} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

/// Run a benchmark where the closure handles its own timing (wide name column).
///
/// The closure is responsible for calling `rdtsc()` around the operation
/// under test and returning the elapsed cycle count. This allows
/// setup/teardown code to live outside the timing window.
pub fn bench_raw_wide<F: FnMut() -> u64>(name: &str, mut f: F) -> (u64, u64, u64) {
    // Warmup
    for _ in 0..WARMUP {
        f();
    }

    // Collect samples
    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        samples.push(f());
    }

    samples.sort_unstable();
    let p50 = percentile(&samples, 50.0);
    let p99 = percentile(&samples, 99.0);
    let p999 = percentile(&samples, 99.9);

    println!("{:<45} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

/// Batch size for batched benchmarks. 100 ops per measurement amortizes
/// the ~20 cycle rdtsc overhead down to ~0.2 cycles per operation.
pub const BATCH: u64 = 100;

/// Serializing rdtsc for measurement start.
///
/// `lfence` ensures all prior instructions retire before reading TSC,
/// preventing out-of-order execution from skewing the measurement.
#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub fn rdtsc_fenced_start() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
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

/// Serializing rdtsc for measurement end.
///
/// `rdtscp` waits for prior instructions to complete before reading TSC.
/// The trailing `lfence` prevents later instructions from reordering
/// before the TSC read.
#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub fn rdtsc_fenced_end() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
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

/// Run a batched benchmark: 100 ops per rdtsc measurement.
///
/// Amortizes the ~20 cycle rdtsc overhead across [`BATCH`] operations,
/// giving ~0.2 cycle measurement resolution. Uses serializing fences
/// for accurate timing. Reports per-operation cycles.
pub fn bench_batched<F: FnMut() -> u64>(name: &str, mut f: F) -> (u64, u64, u64) {
    // Warmup
    for _ in 0..WARMUP {
        black_box(f());
    }

    // Collect samples
    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = rdtsc_fenced_start();
        for _ in 0..BATCH {
            black_box(f());
        }
        let end = rdtsc_fenced_end();
        samples.push(end.wrapping_sub(start) / BATCH);
    }

    samples.sort_unstable();
    let p50 = percentile(&samples, 50.0);
    let p99 = percentile(&samples, 99.0);
    let p999 = percentile(&samples, 99.9);

    println!("{:<40} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

/// Run a batched benchmark with a wider name column (45 chars).
///
/// Same as [`bench_batched`] but with more space for longer operation names.
pub fn bench_batched_wide<F: FnMut() -> u64>(name: &str, mut f: F) -> (u64, u64, u64) {
    // Warmup
    for _ in 0..WARMUP {
        black_box(f());
    }

    // Collect samples
    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = rdtsc_fenced_start();
        for _ in 0..BATCH {
            black_box(f());
        }
        let end = rdtsc_fenced_end();
        samples.push(end.wrapping_sub(start) / BATCH);
    }

    samples.sort_unstable();
    let p50 = percentile(&samples, 50.0);
    let p99 = percentile(&samples, 99.0);
    let p999 = percentile(&samples, 99.9);

    println!("{:<45} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

// Cargo requires a main function for files in the examples directory.
// This module is included via #[path] in the actual benchmark examples.
#[allow(dead_code)]
fn main() {
    eprintln!("This is a utility module. Run one of the perf_* examples instead.");
}
