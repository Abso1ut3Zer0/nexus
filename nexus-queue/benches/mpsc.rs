//! Benchmarks for MPSC queue performance.
//!
//! Compares nexus-queue against crossbeam-queue's ArrayQueue.

use criterion::{BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main};
use crossbeam_queue::ArrayQueue;
use nexus_queue::mpsc;
use std::sync::Arc;
use std::thread;

// ============================================================================
// Single-operation latency benchmarks
// ============================================================================

fn bench_mpsc_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpsc_latency");

    // Measure single send+recv round-trip latency (no contention)
    group.bench_function("nexus_mpsc/u64", |b| {
        let (tx, mut rx) = mpsc::bounded::channel::<u64>(1024);
        b.iter(|| {
            tx.try_send(black_box(42u64)).unwrap();
            black_box(rx.try_recv().unwrap())
        });
    });

    group.bench_function("crossbeam_array/u64", |b| {
        let q = ArrayQueue::<u64>::new(1024);
        b.iter(|| {
            q.push(black_box(42u64)).unwrap();
            black_box(q.pop().unwrap())
        });
    });

    // 128-byte message
    #[allow(unused)]
    #[derive(Debug, Clone, Copy)]
    struct Message128([u64; 16]);

    group.bench_function("nexus_mpsc/128b", |b| {
        let (tx, mut rx) = mpsc::bounded::channel::<Message128>(1024);
        let msg = Message128([42; 16]);
        b.iter(|| {
            tx.try_send(black_box(msg)).unwrap();
            black_box(rx.try_recv().unwrap())
        });
    });

    group.bench_function("crossbeam_array/128b", |b| {
        let q = ArrayQueue::<Message128>::new(1024);
        let msg = Message128([42; 16]);
        b.iter(|| {
            q.push(black_box(msg)).unwrap();
            black_box(q.pop().unwrap())
        });
    });

    // 256-byte message
    #[allow(unused)]
    #[derive(Debug, Clone, Copy)]
    struct Message256([u64; 32]);

    group.bench_function("nexus_mpsc/256b", |b| {
        let (tx, mut rx) = mpsc::bounded::channel::<Message256>(1024);
        let msg = Message256([42; 32]);
        b.iter(|| {
            tx.try_send(black_box(msg)).unwrap();
            black_box(rx.try_recv().unwrap())
        });
    });

    group.bench_function("crossbeam_array/256b", |b| {
        let q = ArrayQueue::<Message256>::new(1024);
        let msg = Message256([42; 32]);
        b.iter(|| {
            q.push(black_box(msg)).unwrap();
            black_box(q.pop().unwrap())
        });
    });

    group.finish();
}

// ============================================================================
// Send-only and recv-only latency (to isolate each operation)
// ============================================================================

fn bench_mpsc_send_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpsc_send_latency");

    group.bench_function("nexus_mpsc/u64", |b| {
        let (tx, mut rx) = mpsc::bounded::channel::<u64>(1024);
        let mut i = 0u64;
        b.iter(|| {
            tx.try_send(black_box(i)).unwrap();
            i += 1;
            // Drain periodically to avoid full queue
            if i % 512 == 0 {
                while rx.try_recv().is_ok() {}
            }
        });
    });

    group.bench_function("crossbeam_array/u64", |b| {
        let q = ArrayQueue::<u64>::new(1024);
        let mut i = 0u64;
        b.iter(|| {
            q.push(black_box(i)).unwrap();
            i += 1;
            if i % 512 == 0 {
                while q.pop().is_some() {}
            }
        });
    });

    group.finish();
}

fn bench_mpsc_recv_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpsc_recv_latency");

    group.bench_function("nexus_mpsc/u64", |b| {
        let (tx, mut rx) = mpsc::bounded::channel::<u64>(1024);
        // Pre-fill
        for i in 0..512 {
            tx.try_send(i).unwrap();
        }
        let mut refill_counter = 0usize;
        b.iter(|| {
            let val = rx.try_recv().unwrap();
            black_box(val);
            refill_counter += 1;
            // Refill periodically
            if refill_counter % 256 == 0 {
                for i in 0..256 {
                    tx.try_send(i).unwrap();
                }
            }
        });
    });

    group.bench_function("crossbeam_array/u64", |b| {
        let q = ArrayQueue::<u64>::new(1024);
        // Pre-fill
        for i in 0..512 {
            q.push(i).unwrap();
        }
        let mut refill_counter = 0usize;
        b.iter(|| {
            let val = q.pop().unwrap();
            black_box(val);
            refill_counter += 1;
            if refill_counter % 256 == 0 {
                for i in 0..256 {
                    q.push(i).unwrap();
                }
            }
        });
    });

    group.finish();
}

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
                    let (tx, mut rx) = mpsc::bounded::channel::<u64>(1024);

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
                            Err(mpsc::bounded::TryRecvError::Empty) => std::hint::spin_loop(),
                            Err(mpsc::bounded::TryRecvError::Disconnected) => break,
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
            let (tx, mut rx) = mpsc::bounded::channel::<u64>(64); // Small!

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
                    Err(mpsc::bounded::TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(mpsc::bounded::TryRecvError::Disconnected) => break,
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
            let (tx, mut rx) = mpsc::bounded::channel::<LargeMessage>(1024);
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
                    Err(mpsc::bounded::TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(mpsc::bounded::TryRecvError::Disconnected) => break,
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

fn bench_mpsc_cross_thread_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpsc_cross_thread_latency");

    group.bench_function("nexus_mpsc/u64", |b| {
        let (tx, mut rx) = mpsc::bounded::channel::<u64>(1024);
        let done = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let done2 = done.clone();

        let handle = thread::spawn(move || {
            while !done2.load(std::sync::atomic::Ordering::Relaxed) {
                match rx.try_recv() {
                    Ok(_) => {}
                    Err(_) => std::hint::spin_loop(),
                }
            }
            // Drain remaining
            while rx.try_recv().is_ok() {}
        });

        b.iter(|| {
            while tx.try_send(black_box(1u64)).is_err() {
                std::hint::spin_loop();
            }
        });

        done.store(true, std::sync::atomic::Ordering::Relaxed);
        handle.join().unwrap();
    });

    group.bench_function("crossbeam_array/u64", |b| {
        let q = Arc::new(ArrayQueue::<u64>::new(1024));
        let q2 = q.clone();
        let done = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let done2 = done.clone();

        let handle = thread::spawn(move || {
            while !done2.load(std::sync::atomic::Ordering::Relaxed) {
                match q2.pop() {
                    Some(_) => {}
                    None => std::hint::spin_loop(),
                }
            }
            // Drain remaining
            while q2.pop().is_some() {}
        });

        b.iter(|| {
            while q.push(black_box(1u64)).is_err() {
                std::hint::spin_loop();
            }
        });

        done.store(true, std::sync::atomic::Ordering::Relaxed);
        handle.join().unwrap();
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_mpsc_latency,
    bench_mpsc_send_latency,
    bench_mpsc_recv_latency,
    bench_mpsc_throughput,
    bench_mpsc_contention,
    bench_mpsc_large_messages,
    bench_mpsc_cross_thread_latency,
);

criterion_main!(benches);
