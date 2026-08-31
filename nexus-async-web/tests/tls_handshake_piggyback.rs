//! TLS 1.3 handshake-piggyback regression test with allocation
//! counting.
//!
//! TLS 1.3 lets the server piggyback application-data records onto
//! the same burst that carries `ServerFinished`. Pre-0.7.0, the
//! handshake driver fed bursts via `read_and_process_tls`, which
//! kept consuming past the `is_handshaking() → false` transition
//! and queued the post-handshake plaintext in rustls's internal
//! buffer (capped at ~16 KiB). The 0.7.0 driver
//! (`TlsInner::drive_handshake`) reads directly into
//! `pending_read.spare()` and stops stepping at the handshake
//! transition — the post-handshake remainder stays in
//! `pending_read` for the streaming reader to pick up on the first
//! `poll_read`.
//!
//! This test:
//! 1. Stands up a sync rustls server that emits handshake records
//!    plus an app-data record in a single burst.
//! 2. Drives `TlsInner::connect` from a `nexus_async_rt::Runtime`.
//! 3. Asserts:
//!    - `connect` succeeds (no `received plaintext buffer full`).
//!    - First `poll_read` after connect returns the piggybacked
//!      app-data bytes.
//!    - Heap allocations during the `drive_handshake` block are
//!      bounded — the buffer constructions inside `connect` are the
//!      only expected allocations.
//!
//! **Lives in its own test binary** because `#[global_allocator]` is
//! process-wide.

#![cfg(all(feature = "nexus", feature = "tls"))]

use std::alloc::{GlobalAlloc, Layout, System};
use std::future::poll_fn;
use std::io::{Read, Write};
use std::net::TcpListener;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::thread;
use std::time::Duration;

use nexus_async_rt::{AsyncRead, Runtime, TcpStream as AsyncTcpStream};
use nexus_async_web::maybe_tls::{MaybeTls, TlsInner};
use nexus_net::tls::{TlsBufferCapacities, TlsCodec, TlsConfig};
use nexus_rt::WorldBuilder;

// =============================================================================
// Counting global allocator
// =============================================================================

struct CountingAllocator {
    counting_active: AtomicBool,
    allocs: AtomicUsize,
}

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if self.counting_active.load(Ordering::Relaxed) {
            self.allocs.fetch_add(1, Ordering::Relaxed);
        }
        // SAFETY: delegates to System; layout is valid per GlobalAlloc safety contract.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: delegates to System; ptr and layout are valid per GlobalAlloc safety contract.
        unsafe { System.dealloc(ptr, layout) };
    }
}

#[global_allocator]
static ALLOC: CountingAllocator = CountingAllocator {
    counting_active: AtomicBool::new(false),
    allocs: AtomicUsize::new(0),
};

fn start_counting() {
    ALLOC.allocs.store(0, Ordering::Relaxed);
    ALLOC.counting_active.store(true, Ordering::Relaxed);
}

fn stop_counting() -> usize {
    ALLOC.counting_active.store(false, Ordering::Relaxed);
    ALLOC.allocs.load(Ordering::Relaxed)
}

// =============================================================================
// Sync rustls server that emits handshake + app-data piggyback
// =============================================================================

const PIGGYBACK_PAYLOAD: &[u8] = b"piggybacked-server-greeting";

fn make_server_config() -> Arc<rustls::ServerConfig> {
    let cert_kp =
        rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).expect("cert generation");
    let chain = vec![rustls::pki_types::CertificateDer::from(
        cert_kp.cert.der().to_vec(),
    )];
    let key = rustls::pki_types::PrivateKeyDer::try_from(cert_kp.key_pair.serialize_der())
        .expect("server key");
    Arc::new(
        rustls::ServerConfig::builder()
            .with_no_client_auth()
            .with_single_cert(chain, key)
            .expect("server config"),
    )
}

/// Drive the server's view of the handshake just far enough to have
/// queued ServerHello + EncryptedExtensions + Certificate +
/// CertVerify + Finished, then queue piggyback plaintext on top of
/// those records and flush everything in a single `write_tls` cycle.
/// The result on the wire is one TCP burst containing handshake
/// records and app-data records back-to-back.
#[allow(clippy::needless_pass_by_value)]
fn run_piggyback_server(listener: TcpListener, server_config: Arc<rustls::ServerConfig>) {
    let (mut tcp, _) = listener.accept().expect("server accept");
    tcp.set_nodelay(true).ok();
    tcp.set_read_timeout(Some(Duration::from_secs(15))).ok();
    tcp.set_write_timeout(Some(Duration::from_secs(15))).ok();

    let mut server = rustls::ServerConnection::new(server_config).expect("server conn");

    // Read ClientHello (a single read_tls call usually suffices for
    // a small CH).
    server.read_tls(&mut tcp).expect("server read CH");
    server.process_new_packets().expect("server process CH");

    // Server is now post-CH and has queued ServerHello+...+Finished
    // in its outbound. Queue piggyback plaintext on top BEFORE
    // flushing, so the next write_tls flushes everything in one
    // cycle — TLS 1.3 lets the server send app-data after Finished.
    server
        .writer()
        .write_all(PIGGYBACK_PAYLOAD)
        .expect("server queue piggyback");

    while server.wants_write() {
        server.write_tls(&mut tcp).expect("server flush burst");
    }

    // Drive the rest of the handshake (read client Finished).
    while server.is_handshaking() {
        if server.wants_read() {
            server.read_tls(&mut tcp).expect("server read finished");
            server.process_new_packets().expect("server process");
        }
        if server.wants_write() {
            server.write_tls(&mut tcp).expect("server flush");
        }
    }

    // Hold the connection open until the client closes.
    let mut sink = [0u8; 64];
    while let Ok(n) = tcp.read(&mut sink) {
        if n == 0 {
            break;
        }
    }
}

// =============================================================================
// Test
// =============================================================================

#[test]
fn drive_handshake_handles_piggyback_with_bounded_allocations() {
    let server_config = make_server_config();

    let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
    let port = listener.local_addr().expect("local_addr").port();
    let server_handle = thread::spawn(move || run_piggyback_server(listener, server_config));

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    rt.block_on(async move {
        let tls_config = TlsConfig::builder()
            .danger_no_verify()
            .build()
            .expect("client tls config");

        let addr = format!("127.0.0.1:{port}").parse().unwrap();
        let tcp = AsyncTcpStream::connect(addr).expect("client tcp connect");

        let codec = TlsCodec::new(&tls_config, "localhost").expect("client codec");
        let capacities = TlsBufferCapacities::default();

        // Count allocations across connect+handshake.
        //
        // The handshake itself allocates non-trivially inside rustls:
        // certificate chain decoding, signature verification, key
        // derivation, etc. — that's outside our control and happens
        // regardless of the piggyback shape. What we DO control is
        // our adapter code: the 0.7.0 `drive_handshake` reads directly
        // into `pending_read.spare()` and stashes the piggyback
        // remainder in-place — no `Vec<u8>` for the post-handshake
        // bytes, no temporary scratch buffer.
        //
        // Bound = 250: comfortably above rustls's typical handshake
        // count (~140 for a simple self-signed cert) and well below
        // any regression that adds a per-iteration allocation in our
        // adapter. If this trips legitimately because of a rustls
        // upgrade, raise it; if it trips on an adapter change, that's
        // the regression this test exists to catch.
        start_counting();
        let inner = TlsInner::connect(tcp, codec, capacities)
            .await
            .expect("connect succeeds despite piggyback");
        let allocs = stop_counting();
        assert!(
            allocs < 250,
            "handshake allocations exceeded 250 (got {allocs}) — \
             likely an adapter regression introducing per-step \
             allocations on the handshake path"
        );

        // First poll_read after connect returns the piggybacked app
        // data — it was stashed in pending_read by drive_handshake's
        // mid-burst transition exit.
        let mut tls = MaybeTls::Tls(Box::new(inner));
        let mut buf = vec![0u8; PIGGYBACK_PAYLOAD.len()];
        let n = poll_fn(|cx| Pin::new(&mut tls).poll_read(cx, &mut buf))
            .await
            .expect("poll_read after handshake");
        assert!(n > 0, "first poll_read must return piggybacked bytes");
        assert_eq!(&buf[..n], &PIGGYBACK_PAYLOAD[..n]);
    });

    server_handle.join().expect("server thread");
}
