//! Benchmarks comparing nexus-slab against the slab crate.
//!
//! Run with: cargo bench
//!
//! Both slabs are pre-allocated for fair comparison.

use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};

const CAPACITY: usize = 100_000;

// ============================================================================
// Helper: Create nexus-slab with optional mlock
// ============================================================================

fn create_nexus_slab<T>(capacity: usize, _mlock: bool) -> nexus_slab::DynamicSlab<T> {
    let slab = nexus_slab::DynamicSlab::<T>::with_capacity(capacity).unwrap();
    slab
}

// ============================================================================
// Insert Benchmarks
// ============================================================================

fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    group.throughput(Throughput::Elements(CAPACITY as u64));

    // Pre-allocate slabs ONCE, reuse via clear()
    let mut nexus = create_nexus_slab::<u64>(CAPACITY, false);
    let mut nexus_mlock = create_nexus_slab::<u64>(CAPACITY, true);
    let mut slab_crate = slab::Slab::<u64>::with_capacity(CAPACITY);

    group.bench_function("nexus-slab", |b| {
        b.iter(|| {
            for i in 0..CAPACITY as u64 {
                black_box(nexus.insert(i));
            }
            nexus.clear();
        });
    });

    group.bench_function("nexus-slab/mlock", |b| {
        b.iter(|| {
            for i in 0..CAPACITY as u64 {
                black_box(nexus_mlock.insert(i));
            }
            nexus_mlock.clear();
        });
    });

    group.bench_function("slab", |b| {
        b.iter(|| {
            for i in 0..CAPACITY as u64 {
                black_box(slab_crate.insert(i));
            }
            slab_crate.clear();
        });
    });

    group.finish();
}

// ============================================================================
// Get Benchmarks (Sequential Access - Cache Friendly)
// ============================================================================

fn bench_get_sequential(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_sequential");
    group.throughput(Throughput::Elements(CAPACITY as u64));

    // Setup nexus-slab (no mlock)
    let mut nexus = create_nexus_slab::<u64>(CAPACITY, false);
    let nexus_keys: Vec<_> = (0..CAPACITY as u64).map(|i| nexus.insert(i)).collect();

    // Setup nexus-slab (with mlock)
    let mut nexus_locked = create_nexus_slab::<u64>(CAPACITY, true);
    let nexus_locked_keys: Vec<_> = (0..CAPACITY as u64)
        .map(|i| nexus_locked.insert(i))
        .collect();

    // Setup slab
    let mut slab_crate = slab::Slab::<u64>::with_capacity(CAPACITY);
    let slab_keys: Vec<_> = (0..CAPACITY as u64).map(|i| slab_crate.insert(i)).collect();

    group.bench_function("nexus-slab", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for key in &nexus_keys {
                sum += black_box(*nexus.get(*key));
            }
            sum
        });
    });

    group.bench_function("nexus-slab/mlock", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for key in &nexus_locked_keys {
                sum += black_box(*nexus_locked.get(*key));
            }
            sum
        });
    });

    group.bench_function("slab", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for key in &slab_keys {
                sum += black_box(*slab_crate.get(*key).unwrap());
            }
            sum
        });
    });

    group.finish();
}

// ============================================================================
// Get Benchmarks (Random Access - Cache Hostile)
// ============================================================================

fn bench_get_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_random");

    const LOOKUPS: usize = 10_000;
    group.throughput(Throughput::Elements(LOOKUPS as u64));

    // Setup nexus-slab (no mlock)
    let mut nexus = create_nexus_slab::<u64>(CAPACITY, false);
    let nexus_keys: Vec<_> = (0..CAPACITY as u64).map(|i| nexus.insert(i)).collect();

    // Setup nexus-slab (with mlock)
    let mut nexus_locked = create_nexus_slab::<u64>(CAPACITY, true);
    let nexus_locked_keys: Vec<_> = (0..CAPACITY as u64)
        .map(|i| nexus_locked.insert(i))
        .collect();

    // Setup slab
    let mut slab_crate = slab::Slab::<u64>::with_capacity(CAPACITY);
    let slab_keys: Vec<_> = (0..CAPACITY as u64).map(|i| slab_crate.insert(i)).collect();

    // Pseudo-random indices (deterministic for reproducibility)
    let random_indices: Vec<usize> = (0..LOOKUPS)
        .map(|i| (i * 7919) % CAPACITY) // Prime multiplier for pseudo-random spread
        .collect();

    group.bench_function("nexus-slab", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &idx in &random_indices {
                sum += black_box(*nexus.get(nexus_keys[idx]));
            }
            sum
        });
    });

    group.bench_function("nexus-slab/mlock", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &idx in &random_indices {
                sum += black_box(*nexus_locked.get(nexus_locked_keys[idx]));
            }
            sum
        });
    });

    group.bench_function("slab", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for &idx in &random_indices {
                sum += black_box(*slab_crate.get(slab_keys[idx]).unwrap());
            }
            sum
        });
    });

    group.finish();
}

// ============================================================================
// Remove Benchmarks
// ============================================================================

fn bench_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("remove");
    group.throughput(Throughput::Elements(CAPACITY as u64));

    // Pre-allocate slabs ONCE
    let mut nexus = create_nexus_slab::<u64>(CAPACITY, false);
    let mut nexus_mlock = create_nexus_slab::<u64>(CAPACITY, true);
    let mut slab_crate = slab::Slab::<u64>::with_capacity(CAPACITY);

    group.bench_function("nexus-slab", |b| {
        b.iter(|| {
            // Fill
            let keys: Vec<_> = (0..CAPACITY as u64).map(|i| nexus.insert(i)).collect();
            // Time remove
            for key in keys {
                black_box(nexus.remove(key));
            }
        });
    });

    group.bench_function("nexus-slab/mlock", |b| {
        b.iter(|| {
            let keys: Vec<_> = (0..CAPACITY as u64)
                .map(|i| nexus_mlock.insert(i))
                .collect();
            for key in keys {
                black_box(nexus_mlock.remove(key));
            }
        });
    });

    group.bench_function("slab", |b| {
        b.iter(|| {
            let keys: Vec<_> = (0..CAPACITY as u64).map(|i| slab_crate.insert(i)).collect();
            for key in keys {
                black_box(slab_crate.remove(key));
            }
        });
    });

    group.finish();
}

// ============================================================================
// Insert/Remove Cycle (Churn Pattern)
// ============================================================================

fn bench_churn(c: &mut Criterion) {
    let mut group = c.benchmark_group("churn");

    const CYCLES: usize = 100_000;
    group.throughput(Throughput::Elements(CYCLES as u64 * 2)); // insert + remove

    // Pre-allocate slabs ONCE
    let mut nexus = create_nexus_slab::<u64>(1024, false);
    let mut nexus_mlock = create_nexus_slab::<u64>(1024, true);
    let mut slab_crate = slab::Slab::<u64>::with_capacity(1024);

    group.bench_function("nexus-slab", |b| {
        b.iter(|| {
            for i in 0..CYCLES as u64 {
                let key = nexus.insert(i);
                black_box(nexus.remove(key));
            }
        });
    });

    group.bench_function("nexus-slab/mlock", |b| {
        b.iter(|| {
            for i in 0..CYCLES as u64 {
                let key = nexus_mlock.insert(i);
                black_box(nexus_mlock.remove(key));
            }
        });
    });

    group.bench_function("slab", |b| {
        b.iter(|| {
            for i in 0..CYCLES as u64 {
                let key = slab_crate.insert(i);
                black_box(slab_crate.remove(key));
            }
        });
    });

    group.finish();
}

// ============================================================================
// Mixed Operations (Realistic Workload)
// ============================================================================

fn bench_mixed(c: &mut Criterion) {
    let mut group = c.benchmark_group("mixed");

    const OPS: usize = 50_000;
    group.throughput(Throughput::Elements(OPS as u64));

    group.bench_function("nexus-slab", |b| {
        b.iter_with_setup(
            || {
                let mut slab = create_nexus_slab::<u64>(10_000, false);
                // Pre-fill half
                let keys: Vec<_> = (0..5000u64).map(|i| slab.insert(i)).collect();
                (slab, keys)
            },
            |(mut slab, mut keys)| {
                for i in 0..OPS {
                    match i % 3 {
                        0 => {
                            // Insert
                            let key = slab.insert(i as u64);
                            keys.push(key);
                        }
                        1 => {
                            // Get
                            if let Some(key) = keys.last() {
                                black_box(slab.get(*key));
                            }
                        }
                        _ => {
                            // Remove
                            if let Some(key) = keys.pop() {
                                black_box(slab.remove(key));
                            }
                        }
                    }
                }
            },
        );
    });

    group.bench_function("nexus-slab/mlock", |b| {
        b.iter_with_setup(
            || {
                let mut slab = create_nexus_slab::<u64>(10_000, true);
                // Pre-fill half
                let keys: Vec<_> = (0..5000u64).map(|i| slab.insert(i)).collect();
                (slab, keys)
            },
            |(mut slab, mut keys)| {
                for i in 0..OPS {
                    match i % 3 {
                        0 => {
                            // Insert
                            let key = slab.insert(i as u64);
                            keys.push(key);
                        }
                        1 => {
                            // Get
                            if let Some(key) = keys.last() {
                                black_box(slab.get(*key));
                            }
                        }
                        _ => {
                            // Remove
                            if let Some(key) = keys.pop() {
                                black_box(slab.remove(key));
                            }
                        }
                    }
                }
            },
        );
    });

    group.bench_function("slab", |b| {
        b.iter_with_setup(
            || {
                let mut slab = slab::Slab::<u64>::with_capacity(10_000);
                let keys: Vec<_> = (0..5000u64).map(|i| slab.insert(i)).collect();
                (slab, keys)
            },
            |(mut slab, mut keys)| {
                for i in 0..OPS {
                    match i % 3 {
                        0 => {
                            // Insert
                            let key = slab.insert(i as u64);
                            keys.push(key);
                        }
                        1 => {
                            // Get
                            if let Some(key) = keys.last() {
                                black_box(slab.get(*key));
                            }
                        }
                        _ => {
                            // Remove
                            if let Some(key) = keys.pop() {
                                black_box(slab.remove(key));
                            }
                        }
                    }
                }
            },
        );
    });

    group.finish();
}

// ============================================================================
// Vacant Entry (nexus-slab only)
// ============================================================================

fn bench_vacant_entry(c: &mut Criterion) {
    let mut group = c.benchmark_group("vacant_entry");

    const COUNT: usize = 100_000;
    group.throughput(Throughput::Elements(COUNT as u64));

    group.bench_function("nexus-slab/vacant_entry", |b| {
        b.iter_with_setup(
            || create_nexus_slab::<u64>(COUNT, false),
            |mut slab| {
                for i in 0..COUNT as u64 {
                    let entry = slab.vacant_entry();
                    let _key = entry.insert(i);
                }
            },
        );
    });

    group.bench_function("nexus-slab/insert", |b| {
        b.iter_with_setup(
            || create_nexus_slab::<u64>(COUNT, false),
            |mut slab| {
                for i in 0..COUNT as u64 {
                    let _key = slab.insert(i);
                }
            },
        );
    });

    group.finish();
}

// ============================================================================
// Large Struct (Cache Line Effects)
// ============================================================================

fn bench_large_struct(c: &mut Criterion) {
    #[derive(Debug, Clone)]
    struct LargeStruct {
        #[allow(unused)]
        data: [u64; 32], // 256 bytes
    }

    let mut group = c.benchmark_group("large_struct");

    const COUNT: usize = 10_000;
    group.throughput(Throughput::Elements(COUNT as u64));

    group.bench_function("nexus-slab", |b| {
        b.iter_with_setup(
            || create_nexus_slab::<LargeStruct>(COUNT, false),
            |mut slab| {
                for i in 0..COUNT {
                    let val = LargeStruct {
                        data: [i as u64; 32],
                    };
                    black_box(slab.insert(val));
                }
            },
        );
    });

    group.bench_function("nexus-slab/mlock", |b| {
        b.iter_with_setup(
            || create_nexus_slab::<LargeStruct>(COUNT, true),
            |mut slab| {
                for i in 0..COUNT {
                    let val = LargeStruct {
                        data: [i as u64; 32],
                    };
                    black_box(slab.insert(val));
                }
            },
        );
    });

    group.bench_function("slab", |b| {
        b.iter_with_setup(
            || slab::Slab::<LargeStruct>::with_capacity(COUNT),
            |mut slab| {
                for i in 0..COUNT {
                    let val = LargeStruct {
                        data: [i as u64; 32],
                    };
                    black_box(slab.insert(val));
                }
            },
        );
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_insert,
    bench_get_sequential,
    bench_get_random,
    bench_remove,
    bench_churn,
    bench_mixed,
    bench_vacant_entry,
    bench_large_struct,
);

criterion_main!(benches);
