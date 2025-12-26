//! Benchmarks for SPSC queue performance.
//!
//! Compares nexus-queue against crossbeam-queue's ArrayQueue.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use crossbeam_queue::ArrayQueue;
use nexus_queue::spsc;
use std::sync::Arc;
use std::thread;

/// Message sizes to benchmark
#[allow(unused)]
#[derive(Debug, Clone, Copy)]
struct Small(u64);

#[allow(unused)]
#[derive(Debug, Clone, Copy)]
struct Medium([u64; 16]); // 128 bytes

#[allow(unused)]
#[derive(Debug, Clone, Copy)]
struct Large([u64; 32]); // 256 bytes

// ============================================================================
// Single-threaded latency benchmarks
// ============================================================================

fn bench_single_thread_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("single_thread_latency");

    // --- Small message (8 bytes) ---
    group.bench_function("nexus_spsc/u64", |b| {
        let (tx, rx) = spsc::channel::<u64>(1024);
        b.iter(|| {
            tx.try_send(black_box(42)).unwrap();
            black_box(rx.try_recv().unwrap())
        });
    });

    group.bench_function("crossbeam_array/u64", |b| {
        let q = ArrayQueue::<u64>::new(1024);
        b.iter(|| {
            q.push(black_box(42)).unwrap();
            black_box(q.pop().unwrap())
        });
    });

    // --- Medium message (128 bytes) ---
    group.bench_function("nexus_spsc/128b", |b| {
        let (tx, rx) = spsc::channel::<Medium>(1024);
        let msg = Medium([0; 16]);
        b.iter(|| {
            tx.try_send(black_box(msg)).unwrap();
            black_box(rx.try_recv().unwrap())
        });
    });

    group.bench_function("crossbeam_array/128b", |b| {
        let q = ArrayQueue::<Medium>::new(1024);
        let msg = Medium([0; 16]);
        b.iter(|| {
            q.push(black_box(msg)).unwrap();
            black_box(q.pop().unwrap())
        });
    });

    // --- Large message (256 bytes) ---
    group.bench_function("nexus_spsc/256b", |b| {
        let (tx, rx) = spsc::channel::<Large>(1024);
        let msg = Large([0; 32]);
        b.iter(|| {
            tx.try_send(black_box(msg)).unwrap();
            black_box(rx.try_recv().unwrap())
        });
    });

    group.bench_function("crossbeam_array/256b", |b| {
        let q = ArrayQueue::<Large>::new(1024);
        let msg = Large([0; 32]);
        b.iter(|| {
            q.push(black_box(msg)).unwrap();
            black_box(q.pop().unwrap())
        });
    });

    group.finish();
}

// ============================================================================
// Throughput benchmarks (burst send then receive)
// ============================================================================

fn bench_burst_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("burst_throughput");

    for batch_size in [100, 1000] {
        group.throughput(Throughput::Elements(batch_size as u64));

        group.bench_with_input(
            BenchmarkId::new("nexus_spsc", batch_size),
            &batch_size,
            |b, &n| {
                let (tx, rx) = spsc::channel::<u64>(n * 2);
                b.iter(|| {
                    for i in 0..n {
                        tx.try_send(black_box(i as u64)).unwrap();
                    }
                    for _ in 0..n {
                        black_box(rx.try_recv().unwrap());
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("crossbeam_array", batch_size),
            &batch_size,
            |b, &n| {
                let q = ArrayQueue::<u64>::new(n * 2);
                b.iter(|| {
                    for i in 0..n {
                        q.push(black_box(i as u64)).unwrap();
                    }
                    for _ in 0..n {
                        black_box(q.pop().unwrap());
                    }
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Cross-thread ping-pong latency
// ============================================================================

fn bench_cross_thread_pingpong(c: &mut Criterion) {
    let mut group = c.benchmark_group("cross_thread_pingpong");

    const ITERATIONS: usize = 10_000;
    group.throughput(Throughput::Elements(ITERATIONS as u64));

    group.bench_function("nexus_spsc", |b| {
        b.iter(|| {
            let (tx1, rx1) = spsc::channel::<u64>(64);
            let (tx2, rx2) = spsc::channel::<u64>(64);

            let handle = thread::spawn(move || {
                for _ in 0..ITERATIONS {
                    let val = loop {
                        match rx1.try_recv() {
                            Ok(v) => break v,
                            Err(_) => std::hint::spin_loop(),
                        }
                    };
                    while tx2.try_send(val + 1).is_err() {
                        std::hint::spin_loop();
                    }
                }
            });

            for i in 0..ITERATIONS {
                while tx1.try_send(i as u64).is_err() {
                    std::hint::spin_loop();
                }
                let result = loop {
                    match rx2.try_recv() {
                        Ok(v) => break v,
                        Err(_) => std::hint::spin_loop(),
                    }
                };
                black_box(result);
            }

            handle.join().unwrap();
        });
    });

    group.bench_function("crossbeam_array", |b| {
        b.iter(|| {
            let q1 = Arc::new(ArrayQueue::<u64>::new(64));
            let q2 = Arc::new(ArrayQueue::<u64>::new(64));

            let q1_clone = q1.clone();
            let q2_clone = q2.clone();

            let handle = thread::spawn(move || {
                for _ in 0..ITERATIONS {
                    let val = loop {
                        match q1_clone.pop() {
                            Some(v) => break v,
                            None => std::hint::spin_loop(),
                        }
                    };
                    while q2_clone.push(val + 1).is_err() {
                        std::hint::spin_loop();
                    }
                }
            });

            for i in 0..ITERATIONS {
                while q1.push(i as u64).is_err() {
                    std::hint::spin_loop();
                }
                let result = loop {
                    match q2.pop() {
                        Some(v) => break v,
                        None => std::hint::spin_loop(),
                    }
                };
                black_box(result);
            }

            handle.join().unwrap();
        });
    });

    group.finish();
}

// ============================================================================
// Unidirectional producer-consumer throughput
// ============================================================================

fn bench_cross_thread_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("cross_thread_throughput");

    const MESSAGE_COUNT: usize = 100_000;
    group.throughput(Throughput::Elements(MESSAGE_COUNT as u64));

    group.bench_function("nexus_spsc/u64", |b| {
        b.iter(|| {
            let (tx, rx) = spsc::channel::<u64>(1024);

            let producer = thread::spawn(move || {
                for i in 0..MESSAGE_COUNT {
                    while tx.try_send(i as u64).is_err() {
                        std::hint::spin_loop();
                    }
                }
            });

            let consumer = thread::spawn(move || {
                for _ in 0..MESSAGE_COUNT {
                    loop {
                        match rx.try_recv() {
                            Ok(v) => {
                                black_box(v);
                                break;
                            }
                            Err(_) => std::hint::spin_loop(),
                        }
                    }
                }
            });

            producer.join().unwrap();
            consumer.join().unwrap();
        });
    });

    group.bench_function("crossbeam_array/u64", |b| {
        b.iter(|| {
            let q = Arc::new(ArrayQueue::<u64>::new(1024));

            let q1 = q.clone();
            let producer = thread::spawn(move || {
                for i in 0..MESSAGE_COUNT {
                    while q1.push(i as u64).is_err() {
                        std::hint::spin_loop();
                    }
                }
            });

            let q2 = q.clone();
            let consumer = thread::spawn(move || {
                for _ in 0..MESSAGE_COUNT {
                    loop {
                        match q2.pop() {
                            Some(v) => {
                                black_box(v);
                                break;
                            }
                            None => std::hint::spin_loop(),
                        }
                    }
                }
            });

            producer.join().unwrap();
            consumer.join().unwrap();
        });
    });

    // Large messages
    group.bench_function("nexus_spsc/256b", |b| {
        b.iter(|| {
            let (tx, rx) = spsc::channel::<Large>(1024);
            let msg = Large([42; 32]);

            let producer = thread::spawn(move || {
                for _ in 0..MESSAGE_COUNT {
                    while tx.try_send(msg).is_err() {
                        std::hint::spin_loop();
                    }
                }
            });

            let consumer = thread::spawn(move || {
                for _ in 0..MESSAGE_COUNT {
                    loop {
                        match rx.try_recv() {
                            Ok(v) => {
                                black_box(v);
                                break;
                            }
                            Err(_) => std::hint::spin_loop(),
                        }
                    }
                }
            });

            producer.join().unwrap();
            consumer.join().unwrap();
        });
    });

    group.bench_function("crossbeam_array/256b", |b| {
        b.iter(|| {
            let q = Arc::new(ArrayQueue::<Large>::new(1024));
            let msg = Large([42; 32]);

            let q1 = q.clone();
            let producer = thread::spawn(move || {
                for _ in 0..MESSAGE_COUNT {
                    while q1.push(msg).is_err() {
                        std::hint::spin_loop();
                    }
                }
            });

            let q2 = q.clone();
            let consumer = thread::spawn(move || {
                for _ in 0..MESSAGE_COUNT {
                    loop {
                        match q2.pop() {
                            Some(v) => {
                                black_box(v);
                                break;
                            }
                            None => std::hint::spin_loop(),
                        }
                    }
                }
            });

            producer.join().unwrap();
            consumer.join().unwrap();
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_single_thread_latency,
    bench_burst_throughput,
    bench_cross_thread_pingpong,
    bench_cross_thread_throughput,
);

criterion_main!(benches);
