//! TLS inbound path benchmark: nexus-web vs tungstenite
//!
//! Measures ONLY the decrypt + WS parse path. No socket, no kernel.
//! Pre-encrypts WS frames into TLS records, then benchmarks processing
//! them through each library's pipeline.
//!
//! Usage:
//!   cargo run --release -p nexus-web --features tls --example perf_tls

use std::hint::black_box;
use std::io::{self, Cursor, Read, Write};
use std::sync::Arc;

// ============================================================================
// Timing
// ============================================================================

#[inline(always)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsic; this example targets x86_64 only.
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsic; this example targets x86_64 only.
    unsafe {
        let mut aux = 0u32;
        let tsc = std::arch::x86_64::__rdtscp(&raw mut aux);
        std::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_row(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {:<55} {:>6} {:>6} {:>6} {:>7} {:>7}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

fn print_header() {
    println!(
        "  {:<55} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles)", "p50", "p90", "p99", "p99.9", "max"
    );
}

const SAMPLES: usize = 10_000;
const BATCH: u64 = 8;

// ============================================================================
// Setup: create a paired TLS client/server, do handshake, then use the
// server side to encrypt WS frames into TLS records that we can feed
// to the client side for benchmarking.
// ============================================================================

fn generate_self_signed() -> (Vec<u8>, Vec<u8>) {
    let cert =
        rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).expect("cert generation");
    (cert.cert.der().to_vec(), cert.key_pair.serialize_der())
}

/// In-memory pipe for TLS handshake.
struct MemPipe {
    /// Data written by one side, read by the other.
    buf: Vec<u8>,
}

impl MemPipe {
    fn new() -> Self {
        Self { buf: Vec::new() }
    }

    fn write_to(&mut self, data: &[u8]) {
        self.buf.extend_from_slice(data);
    }

    fn read_from(&mut self, dst: &mut [u8]) -> usize {
        let n = dst.len().min(self.buf.len());
        dst[..n].copy_from_slice(&self.buf[..n]);
        self.buf.drain(..n);
        n
    }

    fn len(&self) -> usize {
        self.buf.len()
    }
}

/// Do the TLS handshake over in-memory pipes.
/// Returns (client_conn, server_conn) ready for data transfer.
fn handshake_in_memory(
    cert_der: &[u8],
    key_der: &[u8],
) -> (rustls::ClientConnection, rustls::ServerConnection) {
    // Client config (no verify for self-signed)
    let client_config = Arc::new(
        rustls::ClientConfig::builder()
            .dangerous()
            .with_custom_certificate_verifier(Arc::new(NoVerify))
            .with_no_client_auth(),
    );

    // Server config
    let cert = rustls::pki_types::CertificateDer::from(cert_der.to_vec());
    let key = rustls::pki_types::PrivateKeyDer::try_from(key_der.to_vec()).unwrap();
    let server_config = Arc::new(
        rustls::ServerConfig::builder()
            .with_no_client_auth()
            .with_single_cert(vec![cert], key)
            .unwrap(),
    );

    let server_name = rustls::pki_types::ServerName::try_from("localhost".to_string()).unwrap();
    let mut client = rustls::ClientConnection::new(client_config, server_name).unwrap();
    let mut server = rustls::ServerConnection::new(server_config).unwrap();

    // Drive handshake via in-memory pipes
    let mut c2s = MemPipe::new();
    let mut s2c = MemPipe::new();

    for _ in 0..20 {
        // Client → Server
        let mut buf = vec![0u8; 16384];
        if client.wants_write() {
            let mut cursor = Cursor::new(Vec::new());
            client.write_tls(&mut cursor).unwrap();
            c2s.write_to(cursor.get_ref());
        }
        if c2s.len() > 0 {
            let n = c2s.read_from(&mut buf);
            server.read_tls(&mut Cursor::new(&buf[..n])).unwrap();
            server.process_new_packets().unwrap();
        }

        // Server → Client
        if server.wants_write() {
            let mut cursor = Cursor::new(Vec::new());
            server.write_tls(&mut cursor).unwrap();
            s2c.write_to(cursor.get_ref());
        }
        if s2c.len() > 0 {
            let n = s2c.read_from(&mut buf);
            client.read_tls(&mut Cursor::new(&buf[..n])).unwrap();
            client.process_new_packets().unwrap();
        }

        if !client.is_handshaking() && !server.is_handshaking() {
            break;
        }
    }

    assert!(!client.is_handshaking(), "client handshake incomplete");
    assert!(!server.is_handshaking(), "server handshake incomplete");

    (client, server)
}

/// Use the server connection to encrypt a WS frame into a TLS record.
#[allow(dead_code)]
fn encrypt_ws_frame(server: &mut rustls::ServerConnection, ws_frame: &[u8]) -> Vec<u8> {
    server.writer().write_all(ws_frame).unwrap();
    let mut out = Vec::new();
    server.write_tls(&mut out).unwrap();
    out
}

fn make_ws_frame(fin: bool, opcode: u8, payload: &[u8]) -> Vec<u8> {
    let mut frame = Vec::new();
    let byte0 = if fin { 0x80 } else { 0x00 } | opcode;
    frame.push(byte0);
    if payload.len() <= 125 {
        frame.push(payload.len() as u8);
    } else if payload.len() <= 65535 {
        frame.push(126);
        frame.extend_from_slice(&(payload.len() as u16).to_be_bytes());
    } else {
        frame.push(127);
        frame.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    }
    frame.extend_from_slice(payload);
    frame
}

// ============================================================================
// nexus-web: TLS decrypt + WS parse
// ============================================================================

fn bench_nexus(
    label: &str,
    ws_frame: &[u8],
    client: &mut rustls::ClientConnection,
    server: &mut rustls::ServerConnection,
) {
    use nexus_web::ws::FrameReader;
    use nexus_web::ws::Role;

    let mut reader = FrameReader::builder()
        .role(Role::Client)
        .buffer_capacity(256 * 1024)
        .build();

    let mut samples = vec![0u64; SAMPLES];

    for s in &mut samples {
        // Generate records for this batch
        let mut records = Vec::with_capacity(BATCH as usize);
        for _ in 0..BATCH {
            server.writer().write_all(ws_frame).unwrap();
            let mut out = Vec::new();
            server.write_tls(&mut out).unwrap();
            records.push(out);
        }

        let t0 = rdtsc_start();
        for record in &records {
            client
                .read_tls(&mut Cursor::new(record.as_slice()))
                .unwrap();
            client.process_new_packets().unwrap();
            let mut rd = client.reader();
            let _ = reader.read_from(&mut rd);
            let msg = reader.next().unwrap();
            black_box(&msg);
        }
        let t1 = rdtsc_end();
        *s = (t1 - t0) / BATCH;
    }

    print_row(&format!("nexus-web  {label}"), &mut samples);
}

// ============================================================================
// tungstenite: TLS decrypt + WS parse
// ============================================================================

/// Feeds pre-encrypted TLS records through a rustls ClientConnection.
/// tungstenite reads plaintext from this via the Read trait.
struct TlsRecordFeeder<'a> {
    client: &'a mut rustls::ClientConnection,
    records: &'a [Vec<u8>],
    idx: std::cell::Cell<usize>,
}

impl Read for TlsRecordFeeder<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // Try reading plaintext first
        match self.client.reader().read(buf) {
            Ok(n) if n > 0 => return Ok(n),
            _ => {}
        }
        // Feed next TLS record
        let idx = self.idx.get();
        if idx >= self.records.len() {
            return Err(io::Error::new(io::ErrorKind::WouldBlock, "no more records"));
        }
        let record = &self.records[idx];
        self.idx.set(idx + 1);
        self.client
            .read_tls(&mut Cursor::new(record.as_slice()))
            .unwrap();
        self.client.process_new_packets().unwrap();
        self.client.reader().read(buf)
    }
}

impl Write for TlsRecordFeeder<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn bench_tungstenite(
    label: &str,
    ws_frame: &[u8],
    client: &mut rustls::ClientConnection,
    server: &mut rustls::ServerConnection,
) {
    // Pre-generate all records upfront (tungstenite needs them in
    // a single Vec for the feeder adapter)
    let total = SAMPLES * BATCH as usize;
    let mut records: Vec<Vec<u8>> = Vec::with_capacity(total);
    for _ in 0..total {
        server.writer().write_all(ws_frame).unwrap();
        let mut out = Vec::new();
        server.write_tls(&mut out).unwrap();
        records.push(out);
    }

    let adapter = TlsRecordFeeder {
        client,
        records: &records,
        idx: std::cell::Cell::new(0),
    };
    let mut ws = tungstenite::protocol::WebSocket::from_raw_socket(
        adapter,
        tungstenite::protocol::Role::Client,
        None,
    );

    let mut samples = vec![0u64; SAMPLES];
    let mut rec_idx = 0;

    for s in &mut samples {
        ws.get_mut().idx.set(rec_idx);
        let t0 = rdtsc_start();
        for _ in 0..BATCH {
            match ws.read() {
                Ok(msg) => {
                    black_box(&msg);
                }
                Err(_) => break,
            }
        }
        let t1 = rdtsc_end();
        rec_idx += BATCH as usize;
        *s = (t1 - t0) / BATCH;
    }

    print_row(&format!("tungstenite {label}"), &mut samples);
}

// NoVerify
#[derive(Debug)]
struct NoVerify;
impl rustls::client::danger::ServerCertVerifier for NoVerify {
    fn verify_server_cert(
        &self,
        _: &rustls::pki_types::CertificateDer<'_>,
        _: &[rustls::pki_types::CertificateDer<'_>],
        _: &rustls::pki_types::ServerName<'_>,
        _: &[u8],
        _: rustls::pki_types::UnixTime,
    ) -> Result<rustls::client::danger::ServerCertVerified, rustls::Error> {
        Ok(rustls::client::danger::ServerCertVerified::assertion())
    }
    fn verify_tls12_signature(
        &self,
        _: &[u8],
        _: &rustls::pki_types::CertificateDer<'_>,
        _: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        Ok(rustls::client::danger::HandshakeSignatureValid::assertion())
    }
    fn verify_tls13_signature(
        &self,
        _: &[u8],
        _: &rustls::pki_types::CertificateDer<'_>,
        _: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        Ok(rustls::client::danger::HandshakeSignatureValid::assertion())
    }
    fn supported_verify_schemes(&self) -> Vec<rustls::SignatureScheme> {
        rustls::crypto::aws_lc_rs::default_provider()
            .signature_verification_algorithms
            .supported_schemes()
    }
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    let (cert_der, key_der) = generate_self_signed();

    println!("\n  TLS + WS inbound path: decrypt → parse → Message");
    println!("  No socket, no kernel. Pure processing cost.");
    println!("  Batch={BATCH}, {SAMPLES} samples\n");
    print_header();

    for &(size, label) in &[
        (32, "text 32B"),
        (128, "text 128B"),
        (512, "text 512B"),
        (2048, "text 2048B"),
    ] {
        println!("\n  --- {label} ---");

        let payload = vec![b'x'; size];
        let ws_frame = make_ws_frame(true, 0x1, &payload);

        let (mut client_n, mut server_n) = handshake_in_memory(&cert_der, &key_der);
        let (mut client_t, mut server_t) = handshake_in_memory(&cert_der, &key_der);

        bench_nexus(label, &ws_frame, &mut client_n, &mut server_n);
        bench_tungstenite(label, &ws_frame, &mut client_t, &mut server_t);
    }

    println!("\n  --- binary 128B ---");
    {
        let payload = vec![0x42u8; 128];
        let ws_frame = make_ws_frame(true, 0x2, &payload);

        let (mut client_n, mut server_n) = handshake_in_memory(&cert_der, &key_der);
        let (mut client_t, mut server_t) = handshake_in_memory(&cert_der, &key_der);

        bench_nexus("binary 128B", &ws_frame, &mut client_n, &mut server_n);
        bench_tungstenite("binary 128B", &ws_frame, &mut client_t, &mut server_t);
    }

    println!();
}
