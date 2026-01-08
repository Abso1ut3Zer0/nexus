//! Performance comparison: nexus-slab vs slab crate
//!
//! Run with:
//! ```bash
//! cargo bench --bench perf_slab_compare
//! ```
//!
//! For best results, disable turbo boost and pin to physical cores:
//! ```bash
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! taskset -c 0 cargo bench --bench perf_slab_compare
//! ```

use criterion::{BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main};

const COUNT: usize = 10_000;

// ============================================================================
// INSERT benchmarks (steady-state with clear())
// ============================================================================

fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("INSERT");
    group.throughput(Throughput::Elements(COUNT as u64));

    // nexus-slab
    group.bench_function("nexus-slab", |b| {
        let mut slab = nexus_slab::SlabBuilder::default()
            .capacity(COUNT)
            .build()
            .unwrap();

        b.iter(|| {
            slab.clear();
            for i in 0..COUNT {
                black_box(slab.insert(i as u64).unwrap());
            }
        });
    });

    // slab crate
    group.bench_function("slab", |b| {
        let mut slab = slab::Slab::<u64>::with_capacity(COUNT);

        b.iter(|| {
            slab.clear();
            for i in 0..COUNT {
                black_box(slab.insert(i as u64));
            }
        });
    });

    group.finish();
}

// ============================================================================
// GET benchmarks (sequential access)
// ============================================================================

fn bench_get_sequential(c: &mut Criterion) {
    let mut group = c.benchmark_group("GET_sequential");
    group.throughput(Throughput::Elements(COUNT as u64));

    // nexus-slab
    group.bench_function("nexus-slab", |b| {
        let mut slab = nexus_slab::SlabBuilder::default()
            .capacity(COUNT)
            .build()
            .unwrap();
        let keys: Vec<_> = (0..COUNT).map(|i| slab.insert(i as u64).unwrap()).collect();

        b.iter(|| {
            for key in &keys {
                black_box(slab.get(*key));
            }
        });
    });

    // slab crate
    group.bench_function("slab", |b| {
        let mut slab = slab::Slab::<u64>::with_capacity(COUNT);
        let keys: Vec<_> = (0..COUNT).map(|i| slab.insert(i as u64)).collect();

        b.iter(|| {
            for key in &keys {
                black_box(slab.get(*key));
            }
        });
    });

    group.finish();
}

// ============================================================================
// GET benchmarks (random access)
// ============================================================================

fn bench_get_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("GET_random");
    group.throughput(Throughput::Elements(COUNT as u64));

    // Pre-generate random indices (same for both)
    let indices: Vec<usize> = {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        (0..COUNT)
            .map(|i| {
                let mut h = DefaultHasher::new();
                i.hash(&mut h);
                (h.finish() as usize) % COUNT
            })
            .collect()
    };

    // nexus-slab
    group.bench_function("nexus-slab", |b| {
        let mut slab = nexus_slab::SlabBuilder::default()
            .capacity(COUNT)
            .build()
            .unwrap();
        let keys: Vec<_> = (0..COUNT).map(|i| slab.insert(i as u64).unwrap()).collect();

        b.iter(|| {
            for &idx in &indices {
                black_box(slab.get(keys[idx]));
            }
        });
    });

    // slab crate
    group.bench_function("slab", |b| {
        let mut slab = slab::Slab::<u64>::with_capacity(COUNT);
        let keys: Vec<_> = (0..COUNT).map(|i| slab.insert(i as u64)).collect();

        b.iter(|| {
            for &idx in &indices {
                black_box(slab.get(keys[idx]));
            }
        });
    });

    group.finish();
}

// ============================================================================
// REMOVE benchmarks
// ============================================================================

fn bench_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("REMOVE");
    group.throughput(Throughput::Elements(COUNT as u64));

    // nexus-slab
    group.bench_function("nexus-slab", |b| {
        b.iter_batched(
            || {
                let mut slab = nexus_slab::SlabBuilder::default()
                    .capacity(COUNT)
                    .build()
                    .unwrap();
                let keys: Vec<_> = (0..COUNT).map(|i| slab.insert(i as u64).unwrap()).collect();
                (slab, keys)
            },
            |(mut slab, keys)| {
                for key in keys {
                    black_box(slab.remove(key));
                }
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // slab crate
    group.bench_function("slab", |b| {
        b.iter_batched(
            || {
                let mut slab = slab::Slab::<u64>::with_capacity(COUNT);
                let keys: Vec<_> = (0..COUNT).map(|i| slab.insert(i as u64)).collect();
                (slab, keys)
            },
            |(mut slab, keys)| {
                for key in keys {
                    black_box(slab.remove(key));
                }
            },
            criterion::BatchSize::SmallInput,
        );
    });

    group.finish();
}

// ============================================================================
// CHURN benchmarks (insert/remove interleaved)
// ============================================================================

fn bench_churn(c: &mut Criterion) {
    let mut group = c.benchmark_group("CHURN");
    group.throughput(Throughput::Elements(COUNT as u64));

    // nexus-slab
    group.bench_function("nexus-slab", |b| {
        let mut slab = nexus_slab::SlabBuilder::default()
            .capacity(COUNT)
            .build()
            .unwrap();

        b.iter(|| {
            slab.clear();
            // Fill half
            let keys: Vec<_> = (0..COUNT / 2)
                .map(|i| slab.insert(i as u64).unwrap())
                .collect();

            // Churn: remove even, insert new
            for (i, key) in keys.iter().enumerate() {
                if i % 2 == 0 {
                    slab.remove(*key);
                    slab.insert((COUNT + i) as u64).unwrap();
                }
            }
        });
    });

    // slab crate
    group.bench_function("slab", |b| {
        let mut slab = slab::Slab::<u64>::with_capacity(COUNT);

        b.iter(|| {
            slab.clear();
            // Fill half
            let keys: Vec<_> = (0..COUNT / 2).map(|i| slab.insert(i as u64)).collect();

            // Churn: remove even, insert new
            for (i, key) in keys.iter().enumerate() {
                if i % 2 == 0 {
                    slab.remove(*key);
                    slab.insert((COUNT + i) as u64);
                }
            }
        });
    });

    group.finish();
}

// ============================================================================
// Size scaling benchmarks
// ============================================================================

fn bench_insert_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("INSERT_scaling");

    for size in [100, 1_000, 10_000, 100_000] {
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(BenchmarkId::new("nexus-slab", size), &size, |b, &size| {
            let mut slab = nexus_slab::SlabBuilder::default()
                .capacity(COUNT)
                .build()
                .unwrap();

            b.iter(|| {
                slab.clear();
                for i in 0..size {
                    black_box(slab.insert(i as u64).unwrap());
                }
            });
        });

        group.bench_with_input(BenchmarkId::new("slab", size), &size, |b, &size| {
            let mut slab = slab::Slab::<u64>::with_capacity(size);

            b.iter(|| {
                slab.clear();
                for i in 0..size {
                    black_box(slab.insert(i as u64));
                }
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_insert,
    bench_get_sequential,
    bench_get_random,
    bench_remove,
    bench_churn,
    bench_insert_scaling,
);

criterion_main!(benches);
