//! Benchmarks for MPSC queue performance.
//!
//! Compares nexus-queue against crossbeam-queue's ArrayQueue.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use crossbeam_queue::ArrayQueue;
use nexus_queue::mpsc;
use std::sync::Arc;
use std::thread;

// ============================================================================
// Multi-producer throughput benchmarks
// ============================================================================

fn bench_mpsc_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpsc_throughput");

    const MESSAGES_PER_PRODUCER: usize = 25_000;

    for num_producers in [1, 2, 4, 8] {
        let total_messages = MESSAGES_PER_PRODUCER * num_producers;
        group.throughput(Throughput::Elements(total_messages as u64));

        group.bench_with_input(
            BenchmarkId::new("nexus_mpsc", num_producers),
            &num_producers,
            |b, &n| {
                b.iter(|| {
                    let (tx, mut rx) = mpsc::channel::<u64>(1024);

                    let _handles: Vec<_> = (0..n)
                        .map(|_| {
                            let tx = tx.clone();
                            thread::spawn(move || {
                                for i in 0..MESSAGES_PER_PRODUCER {
                                    while tx.try_send(i as u64).is_err() {
                                        std::hint::spin_loop();
                                    }
                                }
                            })
                        })
                        .collect();

                    drop(tx);

                    let mut count = 0;
                    loop {
                        match rx.try_recv() {
                            Ok(v) => {
                                black_box(v);
                                count += 1;
                            }
                            Err(mpsc::TryRecvError::Empty) => std::hint::spin_loop(),
                            Err(mpsc::TryRecvError::Disconnected) => break,
                        }
                    }
                    assert_eq!(count, MESSAGES_PER_PRODUCER * n);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("crossbeam_array", num_producers),
            &num_producers,
            |b, &n| {
                b.iter(|| {
                    let q = Arc::new(ArrayQueue::<u64>::new(1024));
                    let done = Arc::new(std::sync::atomic::AtomicUsize::new(0));

                    let handles: Vec<_> = (0..n)
                        .map(|_| {
                            let q = q.clone();
                            let done = done.clone();
                            thread::spawn(move || {
                                for i in 0..MESSAGES_PER_PRODUCER {
                                    while q.push(i as u64).is_err() {
                                        std::hint::spin_loop();
                                    }
                                }
                                done.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
                            })
                        })
                        .collect();

                    let mut count = 0;
                    let total = MESSAGES_PER_PRODUCER * n;
                    while count < total {
                        match q.pop() {
                            Some(v) => {
                                black_box(v);
                                count += 1;
                            }
                            None => std::hint::spin_loop(),
                        }
                    }

                    for handle in handles {
                        handle.join().unwrap();
                    }
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Contention benchmark (many producers, small queue)
// ============================================================================

fn bench_mpsc_contention(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpsc_contention");

    const MESSAGES_PER_PRODUCER: usize = 10_000;
    const NUM_PRODUCERS: usize = 8;
    const TOTAL: usize = MESSAGES_PER_PRODUCER * NUM_PRODUCERS;

    group.throughput(Throughput::Elements(TOTAL as u64));

    // Small queue = high contention
    group.bench_function("nexus_mpsc/small_queue", |b| {
        b.iter(|| {
            let (tx, mut rx) = mpsc::channel::<u64>(64); // Small!

            let handles: Vec<_> = (0..NUM_PRODUCERS)
                .map(|_| {
                    let tx = tx.clone();
                    thread::spawn(move || {
                        for i in 0..MESSAGES_PER_PRODUCER {
                            while tx.try_send(i as u64).is_err() {
                                std::hint::spin_loop();
                            }
                        }
                    })
                })
                .collect();

            drop(tx);

            let mut count = 0;
            loop {
                match rx.try_recv() {
                    Ok(v) => {
                        black_box(v);
                        count += 1;
                    }
                    Err(mpsc::TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(mpsc::TryRecvError::Disconnected) => break,
                }
            }

            for handle in handles {
                handle.join().unwrap();
            }

            assert_eq!(count, TOTAL);
        });
    });

    group.bench_function("crossbeam_array/small_queue", |b| {
        b.iter(|| {
            let q = Arc::new(ArrayQueue::<u64>::new(64)); // Small!

            let handles: Vec<_> = (0..NUM_PRODUCERS)
                .map(|_| {
                    let q = q.clone();
                    thread::spawn(move || {
                        for i in 0..MESSAGES_PER_PRODUCER {
                            while q.push(i as u64).is_err() {
                                std::hint::spin_loop();
                            }
                        }
                    })
                })
                .collect();

            let mut count = 0;
            while count < TOTAL {
                match q.pop() {
                    Some(v) => {
                        black_box(v);
                        count += 1;
                    }
                    None => std::hint::spin_loop(),
                }
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    group.finish();
}

// ============================================================================
// Large message benchmark
// ============================================================================

fn bench_mpsc_large_messages(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpsc_large_messages");

    #[derive(Clone, Copy)]
    #[allow(unused)]
    struct LargeMessage([u64; 32]); // 256 bytes

    const MESSAGES_PER_PRODUCER: usize = 10_000;
    const NUM_PRODUCERS: usize = 4;
    const TOTAL: usize = MESSAGES_PER_PRODUCER * NUM_PRODUCERS;

    group.throughput(Throughput::Elements(TOTAL as u64));

    group.bench_function("nexus_mpsc/256b", |b| {
        b.iter(|| {
            let (tx, mut rx) = mpsc::channel::<LargeMessage>(1024);
            let msg = LargeMessage([42; 32]);

            let handles: Vec<_> = (0..NUM_PRODUCERS)
                .map(|_| {
                    let tx = tx.clone();
                    thread::spawn(move || {
                        for _ in 0..MESSAGES_PER_PRODUCER {
                            while tx.try_send(msg).is_err() {
                                std::hint::spin_loop();
                            }
                        }
                    })
                })
                .collect();

            drop(tx);

            let mut count = 0;
            loop {
                match rx.try_recv() {
                    Ok(v) => {
                        black_box(v);
                        count += 1;
                    }
                    Err(mpsc::TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(mpsc::TryRecvError::Disconnected) => break,
                }
            }

            for handle in handles {
                handle.join().unwrap();
            }

            assert_eq!(count, TOTAL);
        });
    });

    group.bench_function("crossbeam_array/256b", |b| {
        b.iter(|| {
            let q = Arc::new(ArrayQueue::<LargeMessage>::new(1024));
            let msg = LargeMessage([42; 32]);

            let handles: Vec<_> = (0..NUM_PRODUCERS)
                .map(|_| {
                    let q = q.clone();
                    thread::spawn(move || {
                        for _ in 0..MESSAGES_PER_PRODUCER {
                            while q.push(msg).is_err() {
                                std::hint::spin_loop();
                            }
                        }
                    })
                })
                .collect();

            let mut count = 0;
            while count < TOTAL {
                match q.pop() {
                    Some(v) => {
                        black_box(v);
                        count += 1;
                    }
                    None => std::hint::spin_loop(),
                }
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_mpsc_throughput,
    bench_mpsc_contention,
    bench_mpsc_large_messages,
);

criterion_main!(benches);
