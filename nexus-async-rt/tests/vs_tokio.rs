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
#![cfg(target_arch = "x86_64")]
//! Head-to-head comparison: nexus-async-rt vs tokio LocalSet.
//!
//! Both runtimes run single-threaded on the same machine. Measures
//! TCP echo latency distribution and UDP send/recv latency.
//!
//! Run with:
//!   cargo test -p nexus-async-rt --release --test vs_tokio -- --ignored --nocapture --test-threads=1

use std::cell::Cell;
use std::rc::Rc;
use std::time::Duration;

const WARMUP: usize = 1_000;
const SAMPLES: usize = 50_000;
const MSG_SIZE: usize = 64;

#[inline(always)]
fn rdtsc() -> u64 {
    // SAFETY: x86_64 intrinsic; the file-level cfg(target_arch = "x86_64") guarantees the target.
    unsafe { core::arch::x86_64::_rdtsc() }
}

#[inline(always)]
fn rdtscp() -> u64 {
    // SAFETY: x86_64 intrinsic; the file-level cfg(target_arch = "x86_64") guarantees the target.
    unsafe {
        let mut aux: u32 = 0;
        let tsc = core::arch::x86_64::__rdtscp(&raw mut aux);
        core::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn print_distribution(name: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    let len = samples.len();
    let p50 = samples[len / 2];
    let p90 = samples[len * 90 / 100];
    let p99 = samples[len * 99 / 100];
    let p999 = samples[len * 999 / 1000];
    let p9999 = samples[len * 9999 / 10000];
    let min = samples[0];
    let max = samples[len - 1];
    println!(
        "{name:<45} min:{min:>7}  p50:{p50:>7}  p90:{p90:>7}  p99:{p99:>7}  p999:{p999:>7}  p9999:{p9999:>7}  max:{max:>8}"
    );
}

// =============================================================================
// nexus-async-rt TCP echo
// =============================================================================

fn nexus_tcp_echo_samples() -> Vec<u64> {
    use nexus_async_rt::{Runtime, TcpListener, TcpStream, spawn_boxed};
    use nexus_rt::WorldBuilder;

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let samples_rc: Rc<Cell<Vec<u64>>> = Rc::new(Cell::new(Vec::new()));
    let writer = samples_rc.clone();

    rt.block_on(async move {
        let listener = TcpListener::bind("127.0.0.1:0".parse().unwrap()).unwrap();
        let addr = listener.local_addr().unwrap();

        // Server
        spawn_boxed(async move {
            let mut listener = listener;
            let (mut s, _) = listener.accept().await.unwrap();
            s.set_nodelay(true).unwrap();
            let mut buf = [0u8; MSG_SIZE];
            loop {
                let n = s.read(&mut buf).await.unwrap();
                if n == 0 {
                    break;
                }
                s.write_all(&buf[..n]).await.unwrap();
            }
        });

        // Client
        spawn_boxed(async move {
            nexus_async_rt::sleep(Duration::from_millis(10)).await;
            let mut c = TcpStream::connect(addr).unwrap();
            c.set_nodelay(true).unwrap();

            let msg = [0xABu8; MSG_SIZE];
            let mut buf = [0u8; MSG_SIZE];

            for _ in 0..WARMUP {
                c.write_all(&msg).await.unwrap();
                read_exact(&mut c, &mut buf).await;
            }

            let mut samples = Vec::with_capacity(SAMPLES);
            for _ in 0..SAMPLES {
                let start = rdtsc();
                c.write_all(&msg).await.unwrap();
                read_exact(&mut c, &mut buf).await;
                let end = rdtscp();
                samples.push(end.wrapping_sub(start));
            }
            writer.set(samples);
        });

        nexus_async_rt::sleep(Duration::from_millis(60_000)).await;
    });

    samples_rc.take()
}

async fn read_exact(stream: &mut nexus_async_rt::TcpStream, buf: &mut [u8]) {
    let mut filled = 0;
    while filled < buf.len() {
        let n = stream.read(&mut buf[filled..]).await.unwrap();
        assert!(n > 0, "unexpected EOF");
        filled += n;
    }
}

// =============================================================================
// tokio LocalSet TCP echo
// =============================================================================

fn tokio_tcp_echo_samples() -> Vec<u64> {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    let local = tokio::task::LocalSet::new();

    let samples_rc: Rc<Cell<Vec<u64>>> = Rc::new(Cell::new(Vec::new()));
    let writer = samples_rc.clone();

    local.block_on(&rt, async move {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();

        // Server
        tokio::task::spawn_local(async move {
            let (mut s, _) = listener.accept().await.unwrap();
            s.set_nodelay(true).unwrap();
            let mut buf = [0u8; MSG_SIZE];
            loop {
                let n = tokio::io::AsyncReadExt::read(&mut s, &mut buf)
                    .await
                    .unwrap();
                if n == 0 {
                    break;
                }
                s.write_all(&buf[..n]).await.unwrap();
            }
        });

        // Client
        tokio::task::spawn_local(async move {
            tokio::time::sleep(Duration::from_millis(10)).await;
            let mut c = tokio::net::TcpStream::connect(addr).await.unwrap();
            c.set_nodelay(true).unwrap();

            let msg = [0xABu8; MSG_SIZE];
            let mut buf = [0u8; MSG_SIZE];

            for _ in 0..WARMUP {
                c.write_all(&msg).await.unwrap();
                tokio::io::AsyncReadExt::read_exact(&mut c, &mut buf)
                    .await
                    .unwrap();
            }

            let mut samples = Vec::with_capacity(SAMPLES);
            for _ in 0..SAMPLES {
                let start = rdtsc();
                c.write_all(&msg).await.unwrap();
                tokio::io::AsyncReadExt::read_exact(&mut c, &mut buf)
                    .await
                    .unwrap();
                let end = rdtscp();
                samples.push(end.wrapping_sub(start));
            }
            writer.set(samples);
        });

        tokio::time::sleep(Duration::from_millis(60_000)).await;
    });

    samples_rc.take()
}

// =============================================================================
// nexus-async-rt UDP
// =============================================================================

fn nexus_udp_samples() -> Vec<u64> {
    use nexus_async_rt::{Runtime, UdpSocket, spawn_boxed};
    use nexus_rt::WorldBuilder;

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    let samples_rc: Rc<Cell<Vec<u64>>> = Rc::new(Cell::new(Vec::new()));
    let writer = samples_rc.clone();

    rt.block_on(async move {
        let a = UdpSocket::bind("127.0.0.1:0".parse().unwrap()).unwrap();
        let b = UdpSocket::bind("127.0.0.1:0".parse().unwrap()).unwrap();
        let a_addr = a.local_addr().unwrap();
        let b_addr = b.local_addr().unwrap();

        // Echo server on b
        spawn_boxed(async move {
            let mut b = b;
            b.connect(a_addr).unwrap();
            let mut buf = [0u8; MSG_SIZE];
            loop {
                let n = b.recv(&mut buf).await.unwrap();
                if n == 0 {
                    break;
                }
                b.send(&buf[..n]).await.unwrap();
            }
        });

        // Client on a
        spawn_boxed(async move {
            nexus_async_rt::sleep(Duration::from_millis(10)).await;
            let mut a = a;
            a.connect(b_addr).unwrap();

            let msg = [0xCDu8; MSG_SIZE];
            let mut buf = [0u8; MSG_SIZE];

            for _ in 0..WARMUP {
                a.send(&msg).await.unwrap();
                a.recv(&mut buf).await.unwrap();
            }

            let mut samples = Vec::with_capacity(SAMPLES);
            for _ in 0..SAMPLES {
                let start = rdtsc();
                a.send(&msg).await.unwrap();
                a.recv(&mut buf).await.unwrap();
                let end = rdtscp();
                samples.push(end.wrapping_sub(start));
            }
            writer.set(samples);
        });

        nexus_async_rt::sleep(Duration::from_millis(60_000)).await;
    });

    samples_rc.take()
}

// =============================================================================
// tokio LocalSet UDP
// =============================================================================

fn tokio_udp_samples() -> Vec<u64> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    let local = tokio::task::LocalSet::new();

    let samples_rc: Rc<Cell<Vec<u64>>> = Rc::new(Cell::new(Vec::new()));
    let writer = samples_rc.clone();

    local.block_on(&rt, async move {
        let a = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let b = tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let a_addr = a.local_addr().unwrap();
        let b_addr = b.local_addr().unwrap();

        // Echo server on b
        tokio::task::spawn_local(async move {
            b.connect(a_addr).await.unwrap();
            let mut buf = [0u8; MSG_SIZE];
            loop {
                let n = b.recv(&mut buf).await.unwrap();
                if n == 0 {
                    break;
                }
                b.send(&buf[..n]).await.unwrap();
            }
        });

        // Client on a
        tokio::task::spawn_local(async move {
            tokio::time::sleep(Duration::from_millis(10)).await;
            a.connect(b_addr).await.unwrap();

            let msg = [0xCDu8; MSG_SIZE];
            let mut buf = [0u8; MSG_SIZE];

            for _ in 0..WARMUP {
                a.send(&msg).await.unwrap();
                a.recv(&mut buf).await.unwrap();
            }

            let mut samples = Vec::with_capacity(SAMPLES);
            for _ in 0..SAMPLES {
                let start = rdtsc();
                a.send(&msg).await.unwrap();
                a.recv(&mut buf).await.unwrap();
                let end = rdtscp();
                samples.push(end.wrapping_sub(start));
            }
            writer.set(samples);
        });

        tokio::time::sleep(Duration::from_millis(60_000)).await;
    });

    samples_rc.take()
}

// =============================================================================
// Tests
// =============================================================================

#[test]
#[ignore]
fn tcp_echo_vs_tokio() {
    println!(
        "\n=== TCP Echo Latency: nexus-async-rt vs tokio LocalSet ({MSG_SIZE}B msg, {SAMPLES} samples) ===\n"
    );
    println!("All values in cycles (rdtsc)\n");

    let mut nexus = nexus_tcp_echo_samples();
    assert!(!nexus.is_empty(), "nexus samples empty");
    print_distribution("nexus-async-rt TCP echo", &mut nexus);

    let mut tokio = tokio_tcp_echo_samples();
    assert!(!tokio.is_empty(), "tokio samples empty");
    print_distribution("tokio LocalSet TCP echo", &mut tokio);

    let nexus_p50 = nexus[nexus.len() / 2];
    let tokio_p50 = tokio[tokio.len() / 2];
    let ratio = tokio_p50 as f64 / nexus_p50 as f64;
    println!(
        "\n  nexus p50: {nexus_p50} cy  ({:.0} ns)",
        nexus_p50 as f64 / 3.5
    );
    println!(
        "  tokio p50: {tokio_p50} cy  ({:.0} ns)",
        tokio_p50 as f64 / 3.5
    );
    println!("  ratio:     {ratio:.2}x (>1 = nexus faster)");
}

#[test]
#[ignore]
fn udp_echo_vs_tokio() {
    println!(
        "\n=== UDP Echo Latency: nexus-async-rt vs tokio LocalSet ({MSG_SIZE}B msg, {SAMPLES} samples) ===\n"
    );
    println!("All values in cycles (rdtsc)\n");

    let mut nexus = nexus_udp_samples();
    assert!(!nexus.is_empty(), "nexus samples empty");
    print_distribution("nexus-async-rt UDP echo", &mut nexus);

    let mut tokio = tokio_udp_samples();
    assert!(!tokio.is_empty(), "tokio samples empty");
    print_distribution("tokio LocalSet UDP echo", &mut tokio);

    let nexus_p50 = nexus[nexus.len() / 2];
    let tokio_p50 = tokio[tokio.len() / 2];
    let ratio = tokio_p50 as f64 / nexus_p50 as f64;
    println!(
        "\n  nexus p50: {nexus_p50} cy  ({:.0} ns)",
        nexus_p50 as f64 / 3.5
    );
    println!(
        "  tokio p50: {tokio_p50} cy  ({:.0} ns)",
        tokio_p50 as f64 / 3.5
    );
    println!("  ratio:     {ratio:.2}x (>1 = nexus faster)");
}
