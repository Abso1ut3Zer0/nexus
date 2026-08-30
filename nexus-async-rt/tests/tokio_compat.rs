#![allow(
    unused_must_use,
    unused_imports,
    dead_code,
    unknown_lints,
    clippy::float_cmp,
    clippy::ref_option,
    clippy::used_underscore_binding,
    clippy::redundant_locals,
    clippy::semicolon_if_nothing_returned,
    clippy::let_underscore_future,
    clippy::while_let_loop,
    clippy::needless_continue,
    clippy::match_wild_err_arm,
    clippy::collection_is_never_read,
    clippy::async_yields_async,
    clippy::match_same_arms
)]
//! Integration tests for the tokio compatibility layer.
//!
//! Requires `tokio-compat` feature:
//! `cargo test -p nexus-async-rt --test tokio_compat --features tokio-compat`

#![cfg(feature = "tokio-compat")]

use std::cell::Cell;
use std::rc::Rc;
use std::time::Instant;

use nexus_async_rt::tokio_compat::{spawn_on_tokio, with_tokio};
use nexus_async_rt::{Runtime, spawn_boxed};
use nexus_rt::WorldBuilder;

// hdrhistogram for latency tests
#[cfg(feature = "tokio-compat")]
use hdrhistogram::Histogram;

// =============================================================================
// Basic: tokio::time::sleep works from our executor
// =============================================================================

#[test]
fn tokio_sleep() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();

    rt.block_on(async move {
        // tokio::time::sleep driven by tokio's timer, waker bridges back.
        with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(10))).await;
        flag.set(true);
    });

    assert!(done.get());
}

// =============================================================================
// TCP: tokio TcpStream from our executor
// =============================================================================

#[test]
fn tokio_tcp_echo() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();

    rt.block_on(async move {
        // Start a tokio TCP listener on a background thread.
        // (We use std::thread because tokio::spawn needs tokio's scheduler,
        // which we're only using for the reactor, not task scheduling.)
        let listener = with_tokio(|| tokio::net::TcpListener::bind("127.0.0.1:0"))
            .await
            .unwrap();
        let addr = listener.local_addr().unwrap();

        // Spawn a task that accepts and echoes.
        spawn_boxed(async move {
            let (mut stream, _) = with_tokio(|| listener.accept()).await.unwrap();
            let mut buf = [0u8; 64];
            let n = with_tokio(|| tokio::io::AsyncReadExt::read(&mut stream, &mut buf))
                .await
                .unwrap();
            with_tokio(|| tokio::io::AsyncWriteExt::write_all(&mut stream, &buf[..n]))
                .await
                .unwrap();
        });

        // Connect and send from another spawned task.
        let mut client = with_tokio(|| tokio::net::TcpStream::connect(addr))
            .await
            .unwrap();
        with_tokio(|| tokio::io::AsyncWriteExt::write_all(&mut client, b"hello"))
            .await
            .unwrap();

        let mut buf = [0u8; 64];
        let n = with_tokio(|| tokio::io::AsyncReadExt::read(&mut client, &mut buf))
            .await
            .unwrap();
        assert_eq!(&buf[..n], b"hello");

        flag.set(true);
    });

    assert!(done.get());
}

// =============================================================================
// Timeout: tokio::time::timeout wrapping a tokio future
// =============================================================================

#[test]
fn tokio_timeout_success() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();

    rt.block_on(async move {
        let result = with_tokio(|| {
            tokio::time::timeout(
                std::time::Duration::from_secs(1),
                tokio::time::sleep(std::time::Duration::from_millis(10)),
            )
        })
        .await;
        assert!(result.is_ok()); // Completed before timeout.
        flag.set(true);
    });

    assert!(done.get());
}

#[test]
fn tokio_timeout_expires() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();

    rt.block_on(async move {
        let result = with_tokio(|| {
            tokio::time::timeout(
                std::time::Duration::from_millis(10),
                tokio::time::sleep(std::time::Duration::from_secs(10)),
            )
        })
        .await;
        assert!(result.is_err()); // Timed out.
        flag.set(true);
    });

    assert!(done.get());
}

// =============================================================================
// Multiple await points in a single with_tokio block
// =============================================================================

#[test]
fn tokio_multi_await_block() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();

    rt.block_on(async move {
        let listener = with_tokio(|| tokio::net::TcpListener::bind("127.0.0.1:0"))
            .await
            .unwrap();
        let addr = listener.local_addr().unwrap();

        // Server: single with_tokio block, multiple awaits inside.
        spawn_boxed(async move {
            with_tokio(|| async {
                let (mut stream, _) = listener.accept().await.unwrap();
                let mut buf = [0u8; 64];
                let n = tokio::io::AsyncReadExt::read(&mut stream, &mut buf)
                    .await
                    .unwrap();
                tokio::io::AsyncWriteExt::write_all(&mut stream, &buf[..n])
                    .await
                    .unwrap();
            })
            .await;
        });

        // Client: single block with multiple awaits.
        let result = with_tokio(|| async {
            let mut client = tokio::net::TcpStream::connect(addr).await.unwrap();
            tokio::io::AsyncWriteExt::write_all(&mut client, b"multi-await")
                .await
                .unwrap();
            let mut buf = [0u8; 64];
            let n = tokio::io::AsyncReadExt::read(&mut client, &mut buf)
                .await
                .unwrap();
            String::from_utf8(buf[..n].to_vec()).unwrap()
        })
        .await;

        assert_eq!(result, "multi-await");
        flag.set(true);
    });

    assert!(done.get());
}

// =============================================================================
// Spawned task uses with_tokio
// =============================================================================

#[test]
fn spawned_task_with_tokio() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();
    let check = done.clone();

    rt.block_on(async move {
        spawn_boxed(async move {
            with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(10))).await;
            flag.set(true);
        });

        // Wait for the spawned task.
        for _ in 0..100 {
            nexus_async_rt::yield_now().await;
            if check.get() {
                return;
            }
            with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(1))).await;
        }
        panic!("spawned task did not complete");
    });

    assert!(done.get());
}

// =============================================================================
// Latency: tokio TCP loopback through our executor
// =============================================================================

fn print_histogram(name: &str, hist: &Histogram<u64>) {
    println!("\n=== {name} ({} samples) ===", hist.len());
    println!("  p50:    {:>8} ns", hist.value_at_quantile(0.50));
    println!("  p90:    {:>8} ns", hist.value_at_quantile(0.90));
    println!("  p99:    {:>8} ns", hist.value_at_quantile(0.99));
    println!("  p99.9:  {:>8} ns", hist.value_at_quantile(0.999));
    println!("  max:    {:>8} ns", hist.max());
    println!("  mean:   {:>8.1} ns", hist.mean());
}

#[test]
#[ignore]
fn tokio_compat_tcp_latency() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    const WARMUP: usize = 1_000;
    const ITERS: usize = 10_000;

    let hist_cell = Rc::new(Cell::new(None::<Histogram<u64>>));
    let hist_ref = hist_cell.clone();

    rt.block_on(async move {
        let listener = with_tokio(|| tokio::net::TcpListener::bind("127.0.0.1:0"))
            .await
            .unwrap();
        let addr = listener.local_addr().unwrap();

        // Echo server in a spawned task.
        spawn_boxed(async move {
            with_tokio(|| async {
                let (mut stream, _) = listener.accept().await.unwrap();
                let mut buf = [0u8; 64];
                loop {
                    match tokio::io::AsyncReadExt::read(&mut stream, &mut buf).await {
                        Ok(0) => break,
                        Ok(n) => {
                            tokio::io::AsyncWriteExt::write_all(&mut stream, &buf[..n])
                                .await
                                .unwrap();
                        }
                        Err(_) => break,
                    }
                }
            })
            .await;
        });

        let mut client = with_tokio(|| tokio::net::TcpStream::connect(addr))
            .await
            .unwrap();
        client.set_nodelay(true).unwrap();

        let msg = b"ping1234"; // 8 bytes
        let mut buf = [0u8; 8];

        // Warmup
        for _ in 0..WARMUP {
            with_tokio(|| tokio::io::AsyncWriteExt::write_all(&mut client, msg))
                .await
                .unwrap();
            with_tokio(|| tokio::io::AsyncReadExt::read_exact(&mut client, &mut buf))
                .await
                .unwrap();
        }

        // Measure
        let mut hist = Histogram::<u64>::new(3).unwrap();
        for _ in 0..ITERS {
            let start = Instant::now();
            with_tokio(|| tokio::io::AsyncWriteExt::write_all(&mut client, msg))
                .await
                .unwrap();
            with_tokio(|| tokio::io::AsyncReadExt::read_exact(&mut client, &mut buf))
                .await
                .unwrap();
            let elapsed = start.elapsed().as_nanos() as u64;
            hist.record(elapsed).unwrap();
        }

        print_histogram("tokio-compat TCP echo RTT", &hist);
        hist_ref.set(Some(hist));
    });

    assert!(hist_cell.take().is_some());
}

// =============================================================================
// Stress: many concurrent with_tokio tasks
// =============================================================================

#[test]
#[ignore]
fn tokio_compat_stress_concurrent_sleeps() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let count = Rc::new(Cell::new(0u32));
    let count_ref = count.clone();

    rt.block_on(async move {
        for _ in 0..100 {
            let c = count_ref.clone();
            spawn_boxed(async move {
                with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(1))).await;
                c.set(c.get() + 1);
            });
        }

        for _ in 0..500 {
            nexus_async_rt::yield_now().await;
            if count.get() >= 100 {
                return;
            }
            with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(1))).await;
        }
        panic!("only {}/100 tasks completed", count.get());
    });
}

#[test]
#[ignore]
fn tokio_compat_stress_rapid_tcp() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let listener = with_tokio(|| tokio::net::TcpListener::bind("127.0.0.1:0"))
            .await
            .unwrap();
        let addr = listener.local_addr().unwrap();

        spawn_boxed(async move {
            with_tokio(|| async {
                loop {
                    match listener.accept().await {
                        Ok((mut stream, _)) => {
                            let mut buf = [0u8; 64];
                            match tokio::io::AsyncReadExt::read(&mut stream, &mut buf).await {
                                Ok(n) if n > 0 => {
                                    let _ =
                                        tokio::io::AsyncWriteExt::write_all(&mut stream, &buf[..n])
                                            .await;
                                }
                                _ => {}
                            }
                        }
                        Err(_) => break,
                    }
                }
            })
            .await;
        });

        for i in 0u32..100 {
            with_tokio(|| async {
                let mut client = tokio::net::TcpStream::connect(addr).await.unwrap();
                let msg = i.to_le_bytes();
                tokio::io::AsyncWriteExt::write_all(&mut client, &msg)
                    .await
                    .unwrap();
                let mut buf = [0u8; 4];
                tokio::io::AsyncReadExt::read_exact(&mut client, &mut buf)
                    .await
                    .unwrap();
                assert_eq!(buf, msg);
            })
            .await;
        }
    });
}

// =============================================================================
// Latency: pure waker bridge (no IO, no TCP)
// =============================================================================

/// Measures the pure waker bridge cost.
///
/// A background thread sends on a tokio oneshot channel, which fires
/// the waker immediately (no timer, no IO). The waker goes through
/// our cross-thread inbox → eventfd → our executor re-polls.
///
/// The background thread uses a sync barrier to coordinate — it sends
/// right after we start awaiting, so we measure the full round-trip:
/// register waker → Pending → sender fires waker → inbox push →
/// eventfd poke → our poll loop → re-poll → Ready.
#[test]
#[ignore]
fn tokio_compat_waker_bridge_latency() {
    use std::sync::{Arc, Barrier};

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    const WARMUP: usize = 1_000;
    const ITERS: usize = 50_000;

    let hist_cell = Rc::new(Cell::new(None::<Histogram<u64>>));
    let hist_ref = hist_cell.clone();

    // Long-lived sender thread with per-iteration barrier.
    // Barrier ensures background thread has the oneshot sender
    // and is about to send BEFORE we start timing.
    let (coord_tx, coord_rx) =
        std::sync::mpsc::channel::<(tokio::sync::oneshot::Sender<()>, Arc<Barrier>)>();

    std::thread::spawn(move || {
        while let Ok((tx, barrier)) = coord_rx.recv() {
            barrier.wait(); // sync with receiver
            let _ = tx.send(()); // fire immediately
        }
    });

    // Use block_on_busy — never parks in epoll, drains inbox every iteration.
    rt.block_on_busy(async move {
        let mut hist_park = Histogram::<u64>::new(3).unwrap();

        for i in 0..(WARMUP + ITERS) {
            let (tx, rx) = tokio::sync::oneshot::channel::<()>();
            let barrier = Arc::new(Barrier::new(2));

            coord_tx.send((tx, barrier.clone())).unwrap();
            barrier.wait();

            let start = Instant::now();
            let _ = with_tokio(|| rx).await;
            let elapsed = start.elapsed().as_nanos() as u64;

            if i >= WARMUP {
                hist_park.record(elapsed).unwrap();
            }
        }

        print_histogram(
            "tokio-compat waker bridge (busy spin, no epoll)",
            &hist_park,
        );
        hist_ref.set(Some(hist_park));
    });

    assert!(hist_cell.take().is_some());
}

// =============================================================================
// Integration: bidirectional TCP conversation
// =============================================================================

#[test]
fn tokio_tcp_bidirectional_conversation() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();

    rt.block_on(async move {
        let listener = with_tokio(|| tokio::net::TcpListener::bind("127.0.0.1:0"))
            .await
            .unwrap();
        let addr = listener.local_addr().unwrap();

        // Server: multi-round conversation.
        spawn_boxed(async move {
            with_tokio(|| async {
                let (mut stream, _) = listener.accept().await.unwrap();
                let mut buf = [0u8; 256];

                for round in 0u32..10 {
                    let n = tokio::io::AsyncReadExt::read(&mut stream, &mut buf)
                        .await
                        .unwrap();
                    let msg = std::str::from_utf8(&buf[..n]).unwrap();
                    assert_eq!(msg, format!("ping-{round}"));

                    let reply = format!("pong-{round}");
                    tokio::io::AsyncWriteExt::write_all(&mut stream, reply.as_bytes())
                        .await
                        .unwrap();
                }
            })
            .await;
        });

        // Client: send ping, receive pong, 10 rounds.
        with_tokio(|| async {
            let mut client = tokio::net::TcpStream::connect(addr).await.unwrap();

            for round in 0u32..10 {
                let msg = format!("ping-{round}");
                tokio::io::AsyncWriteExt::write_all(&mut client, msg.as_bytes())
                    .await
                    .unwrap();

                let mut buf = [0u8; 256];
                let n = tokio::io::AsyncReadExt::read(&mut client, &mut buf)
                    .await
                    .unwrap();
                let reply = std::str::from_utf8(&buf[..n]).unwrap();
                assert_eq!(reply, format!("pong-{round}"));
            }
        })
        .await;

        flag.set(true);
    });

    assert!(done.get());
}

// =============================================================================
// Integration: concurrent TCP clients
// =============================================================================

#[test]
fn tokio_tcp_concurrent_clients() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let count = Rc::new(Cell::new(0u32));
    let count_ref = count.clone();

    rt.block_on(async move {
        let listener = with_tokio(|| tokio::net::TcpListener::bind("127.0.0.1:0"))
            .await
            .unwrap();
        let addr = listener.local_addr().unwrap();

        // Server: accept multiple connections, echo each.
        spawn_boxed(async move {
            with_tokio(|| async {
                for _ in 0..5 {
                    let (mut stream, _) = listener.accept().await.unwrap();
                    let mut buf = [0u8; 64];
                    let n = tokio::io::AsyncReadExt::read(&mut stream, &mut buf)
                        .await
                        .unwrap();
                    tokio::io::AsyncWriteExt::write_all(&mut stream, &buf[..n])
                        .await
                        .unwrap();
                }
            })
            .await;
        });

        // 5 concurrent client tasks.
        for i in 0u32..5 {
            let c = count_ref.clone();
            spawn_boxed(async move {
                with_tokio(|| async {
                    let mut client = tokio::net::TcpStream::connect(addr).await.unwrap();
                    let msg = i.to_le_bytes();
                    tokio::io::AsyncWriteExt::write_all(&mut client, &msg)
                        .await
                        .unwrap();
                    let mut buf = [0u8; 4];
                    tokio::io::AsyncReadExt::read_exact(&mut client, &mut buf)
                        .await
                        .unwrap();
                    assert_eq!(buf, msg);
                })
                .await;
                c.set(c.get() + 1);
            });
        }

        // Wait for all clients.
        //
        // We use `tokio::sleep` rather than `yield_now` here because the
        // wait is for cross-thread state — the clients' completion
        // depends on tokio's IO driver thread firing wakes. `yield_now`
        // is a cooperative yield within nexus's executor; it doesn't
        // give other OS threads CPU time. A tight `yield_now` loop
        // on a single-threaded executor can starve tokio's worker
        // thread, causing the cross-thread wakes to arrive after the
        // budget runs out. `sleep` parks the executor for a bounded
        // duration, letting the OS schedule tokio's worker.
        for _ in 0..200 {
            if count.get() >= 5 {
                return;
            }
            with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(1))).await;
        }
        panic!("only {}/5 clients completed", count.get());
    });
}

// =============================================================================
// Integration: tokio timeout on slow server
// =============================================================================

#[test]
fn tokio_timeout_on_slow_server() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();

    rt.block_on(async move {
        let listener = with_tokio(|| tokio::net::TcpListener::bind("127.0.0.1:0"))
            .await
            .unwrap();
        let addr = listener.local_addr().unwrap();

        // Server: accept but never respond (simulate slow/dead server).
        spawn_boxed(async move {
            with_tokio(|| async {
                let (_stream, _) = listener.accept().await.unwrap();
                // Hold connection open, never write.
                tokio::time::sleep(std::time::Duration::from_secs(60)).await;
            })
            .await;
        });

        // Client: connect with timeout. Should timeout, not hang.
        let result = with_tokio(|| async {
            let mut client = tokio::net::TcpStream::connect(addr).await.unwrap();
            let mut buf = [0u8; 64];
            tokio::time::timeout(
                std::time::Duration::from_millis(50),
                tokio::io::AsyncReadExt::read(&mut client, &mut buf),
            )
            .await
        })
        .await;

        assert!(result.is_err()); // Elapsed — timeout fired.
        flag.set(true);
    });

    assert!(done.get());
}

// =============================================================================
// Integration: mixed nexus IO + tokio futures
// =============================================================================

#[test]
fn mixed_nexus_and_tokio() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let done = Rc::new(Cell::new(false));
    let flag = done.clone();

    rt.block_on(async move {
        // Use our local channel (nexus primitive) alongside tokio sleep.
        let (tx, rx) = nexus_async_rt::channel::local::channel::<u32>(16);

        spawn_boxed(async move {
            for i in 0..5 {
                // Tokio timer between sends.
                with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(5))).await;
                tx.send(i).await.unwrap();
            }
        });

        let mut received = Vec::new();
        for _ in 0..5 {
            let val = rx.recv().await.unwrap();
            received.push(val);
        }
        assert_eq!(received, vec![0, 1, 2, 3, 4]);
        flag.set(true);
    });

    assert!(done.get());
}

// =============================================================================
// Fuzz: rapid with_tokio creation/drop
// =============================================================================

#[test]
#[ignore]
fn fuzz_rapid_with_tokio() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        // Rapidly create and await with_tokio futures.
        // Tests that the leaked EnterGuard + cross-thread waker
        // creation/drop don't leak or corrupt state.
        for _ in 0..10_000 {
            with_tokio(|| tokio::time::sleep(std::time::Duration::ZERO)).await;
        }
    });
}

#[test]
#[ignore]
fn fuzz_concurrent_tasks_with_tokio() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let count = Rc::new(Cell::new(0u32));
    let count_ref = count.clone();

    rt.block_on(async move {
        // Spawn 50 tasks, each doing 100 tokio sleeps.
        for _ in 0..50 {
            let c = count_ref.clone();
            spawn_boxed(async move {
                for _ in 0..100 {
                    with_tokio(|| tokio::time::sleep(std::time::Duration::ZERO)).await;
                }
                c.set(c.get() + 1);
            });
        }

        // Wait for all.
        loop {
            if count.get() >= 50 {
                return;
            }
            with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(1))).await;
        }
    });
}

#[test]
#[ignore]
fn fuzz_tcp_connect_storm() {
    // Many rapid TCP connections through the bridge.
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let listener = with_tokio(|| tokio::net::TcpListener::bind("127.0.0.1:0"))
            .await
            .unwrap();
        let addr = listener.local_addr().unwrap();

        // Server: accept everything, echo, close.
        spawn_boxed(async move {
            with_tokio(|| async {
                loop {
                    match listener.accept().await {
                        Ok((mut stream, _)) => {
                            let mut buf = [0u8; 8];
                            match tokio::io::AsyncReadExt::read(&mut stream, &mut buf).await {
                                Ok(n) if n > 0 => {
                                    let _ =
                                        tokio::io::AsyncWriteExt::write_all(&mut stream, &buf[..n])
                                            .await;
                                }
                                _ => {}
                            }
                        }
                        Err(_) => break,
                    }
                }
            })
            .await;
        });

        // Rapid connect/send/recv/close — 200 connections.
        for i in 0u32..200 {
            with_tokio(|| async {
                let mut client = tokio::net::TcpStream::connect(addr).await.unwrap();
                let msg = i.to_le_bytes();
                tokio::io::AsyncWriteExt::write_all(&mut client, &msg)
                    .await
                    .unwrap();
                let mut buf = [0u8; 4];
                tokio::io::AsyncReadExt::read_exact(&mut client, &mut buf)
                    .await
                    .unwrap();
                assert_eq!(buf, msg);
            })
            .await;
        }
    });
}

// =============================================================================
// spawn_on_tokio tests
// =============================================================================

#[test]
fn spawn_on_tokio_basic() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let result = spawn_on_tokio(async { 42u64 }).await.unwrap();
        assert_eq!(result, 42);
    });
}

#[test]
fn spawn_on_tokio_string() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let result = spawn_on_tokio(async { String::from("from tokio pool") })
            .await
            .unwrap();
        assert_eq!(result, "from tokio pool");
    });
}

#[test]
fn spawn_on_tokio_with_sleep() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let result = spawn_on_tokio(async {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            "after sleep"
        })
        .await
        .unwrap();
        assert_eq!(result, "after sleep");
    });
}

#[test]
fn spawn_on_tokio_abort() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let handle = spawn_on_tokio(async {
            tokio::time::sleep(std::time::Duration::from_secs(60)).await;
            42u64
        });
        handle.abort();
        let result = handle.await;
        assert!(result.is_err());
        assert!(result.unwrap_err().is_cancelled());
    });
}

#[test]
fn spawn_on_tokio_drop_aborts() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let completed = Arc::new(AtomicBool::new(false));
    let flag = completed.clone();

    rt.block_on(async move {
        {
            let _handle = spawn_on_tokio(async move {
                tokio::time::sleep(std::time::Duration::from_secs(60)).await;
                flag.store(true, Ordering::Relaxed);
            });
            // _handle drops here → task aborted
        }
        // Give tokio a moment to process the abort.
        with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(50))).await;
    });

    assert!(
        !completed.load(Ordering::Relaxed),
        "task should have been aborted"
    );
}

#[test]
fn spawn_on_tokio_is_finished() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let handle = spawn_on_tokio(async { 42 });
        // Bounded retry — avoid fixed sleep that's flaky on slow CI.
        let deadline = Instant::now() + std::time::Duration::from_secs(2);
        while !handle.is_finished() && Instant::now() < deadline {
            with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(5))).await;
        }
        assert!(
            handle.is_finished(),
            "tokio task did not complete before timeout"
        );
        let val = handle.await.unwrap();
        assert_eq!(val, 42);
    });
}

#[test]
fn spawn_on_tokio_panic_in_task() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let result = spawn_on_tokio(async {
            panic!("intentional test panic");
            #[allow(unreachable_code)]
            42u64
        })
        .await;
        assert!(result.is_err());
        assert!(result.unwrap_err().is_panic());
    });
}

#[test]
fn spawn_on_tokio_multiple_concurrent() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        let h1 = spawn_on_tokio(async { 10u64 });
        let h2 = spawn_on_tokio(async { 20u64 });
        let h3 = spawn_on_tokio(async { 30u64 });

        let r1 = h1.await.unwrap();
        let r2 = h2.await.unwrap();
        let r3 = h3.await.unwrap();

        assert_eq!(r1 + r2 + r3, 60);
    });
}

#[test]
fn spawn_on_tokio_tcp_io() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async {
        // Start a listener on tokio's thread pool.
        let listener =
            spawn_on_tokio(async { tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap() })
                .await
                .unwrap();
        let addr = listener.local_addr().unwrap();

        // Server on tokio's pool.
        let server = spawn_on_tokio(async move {
            let (mut stream, _) = listener.accept().await.unwrap();
            let mut buf = [0u8; 64];
            let n = tokio::io::AsyncReadExt::read(&mut stream, &mut buf)
                .await
                .unwrap();
            tokio::io::AsyncWriteExt::write_all(&mut stream, &buf[..n])
                .await
                .unwrap();
        });

        // Client on tokio's pool.
        let echo = spawn_on_tokio(async move {
            let mut client = tokio::net::TcpStream::connect(addr).await.unwrap();
            tokio::io::AsyncWriteExt::write_all(&mut client, b"hello")
                .await
                .unwrap();
            let mut buf = [0u8; 64];
            let n = tokio::io::AsyncReadExt::read(&mut client, &mut buf)
                .await
                .unwrap();
            String::from_utf8(buf[..n].to_vec()).unwrap()
        })
        .await
        .unwrap();

        assert_eq!(echo, "hello");
        server.await.unwrap();
    });
}

// =============================================================================
// Regression: Executor::drop must not double-panic during unwinding
// =============================================================================

/// Helper: spawn a task that registers a tokio waker, signals readiness,
/// then sleeps forever. Returns when the spawned task is at its await
/// point (waker registered) or the wait deadline expires.
///
/// `spawner` lets us use this for both Box and slab variants.
async fn setup_pending_tokio_task<F>(spawner: F)
where
    F: FnOnce(std::pin::Pin<Box<dyn std::future::Future<Output = ()> + 'static>>),
{
    let started = Rc::new(Cell::new(false));
    let s = started.clone();
    spawner(Box::pin(async move {
        s.set(true);
        with_tokio(|| async {
            tokio::time::sleep(std::time::Duration::from_secs(60)).await;
        })
        .await;
    }));

    // Wait for the spawned task to start AND for tokio to register the
    // waker. The flag confirms the spawned task ran past `s.set(true)`,
    // i.e., it's now in the with_tokio body. The additional sleeps give
    // tokio's worker thread CPU to process the IO source registration.
    while !started.get() {
        with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(1))).await;
    }
    for _ in 0..50 {
        with_tokio(|| tokio::time::sleep(std::time::Duration::from_millis(1))).await;
    }
}

/// When `block_on` panics from user code, the Runtime drops mid-unwind.
/// `Executor::drop` then iterates `all_tasks` — for any task with
/// outstanding cross-thread waker refs (e.g., tokio holds a stored
/// waker), the executor previously debug-panicked with "outstanding
/// references". A panic during unwinding is a double-panic → SIGABRT.
///
/// This is the **box-allocated** variant. Box leak is safe: the Box just
/// sits in process memory; subsequent `cross_task_drop` from tokio's
/// thread sees valid memory.
///
/// Verifies via `catch_unwind` that the original panic propagates rather
/// than the process aborting. Resources held by the spawned task are
/// still cleaned up by `drop_task_future`.
#[test]
fn executor_drop_during_unwind_does_not_abort_box() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            setup_pending_tokio_task(|fut| {
                spawn_boxed(fut);
            })
            .await;

            // Panic with a cross-thread waker still held by tokio.
            panic!("intentional test panic");
        });
    }));

    // Reaching here at all means the original panic propagated cleanly.
    // If Executor::drop double-panicked, the process would have aborted.
    assert!(
        result.is_err(),
        "block_on panic should propagate, not abort"
    );
    let panic_msg = result
        .unwrap_err()
        .downcast::<&'static str>()
        .map(|s| *s)
        .unwrap_or("<not-a-static-str>");
    assert!(
        panic_msg.contains("intentional test panic"),
        "expected our panic to propagate, got: {panic_msg}"
    );
}

/// **Slab-allocated** variant of the unwind regression test.
///
/// Slab tasks have stricter lifetime constraints than box tasks: the
/// `_slab_guard` field on `Runtime` releases the slab's backing storage
/// immediately after `Executor::drop` returns. If we leaked an
/// outstanding-ref slab task (as we do for box tasks), the slab memory
/// would be freed while a cross-thread waker still holds the task ptr —
/// `cross_task_drop` would later UAF on freed slab memory.
///
/// `Executor::drop` handles this by waiting (bounded) for cross-thread
/// refs to settle before allowing the slab guard to drop. If the wait
/// times out, it aborts (UAF would be worse). For this test the wait
/// should succeed — tokio's worker thread will drop its waker when
/// `drop_task_future` releases the IO source, well within 100ms.
#[test]
fn executor_drop_during_unwind_does_not_uaf_slab() {
    use nexus_async_rt::spawn_slab;

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        // SAFETY: single-threaded test; slab outlives all slots allocated within this closure.
        let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(8) };
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

        rt.block_on(async {
            setup_pending_tokio_task(|fut| {
                spawn_slab(fut);
            })
            .await;

            // Panic with a slab task holding a cross-thread waker.
            panic!("intentional slab test panic");
        });
    }));

    // Same as the box variant: reaching here means we didn't abort.
    // Additionally verifies the slab branch (wait + free) didn't UAF.
    assert!(
        result.is_err(),
        "block_on panic should propagate, not abort"
    );
    let panic_msg = result
        .unwrap_err()
        .downcast::<&'static str>()
        .map(|s| *s)
        .unwrap_or("<not-a-static-str>");
    assert!(
        panic_msg.contains("intentional slab test panic"),
        "expected our panic to propagate, got: {panic_msg}"
    );
}
