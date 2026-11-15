# TLS

TLS support is feature-gated behind `tls` and implemented as a thin
wrapper over [rustls](https://github.com/rustls/rustls). The
cryptographic backend is `aws-lc-rs`.

## Enabling

```toml
[dependencies]
nexus-net = { version = "...", features = ["tls"] }
```

## `TlsConfig`

`TlsConfig` wraps an `Arc<rustls::ClientConfig>` so it's cheap to
share across many connections.

```rust
use nexus_net::tls::TlsConfig;

// Default: system trust store (via rustls-native-certs), TLS 1.2 + 1.3
let tls = TlsConfig::new()?;
```

For custom configuration use the builder:

```rust
use nexus_net::tls::TlsConfig;

let tls = TlsConfig::builder()
    .tls13_only()                     // drop TLS 1.2
    .add_root_cert(exchange_ca_der)   // add a private CA
    .build()?;
```

Builder methods:

| Method | Effect |
|--------|--------|
| `add_root_cert(der)` | Trust an additional CA certificate |
| `skip_system_certs()` | Don't load the OS trust store; only use `add_root_cert` |
| `tls13_only()` | Disable TLS 1.2 |
| `danger_no_verify()` | Disable certificate verification (testing only!) |

## Using TLS with WebSocket

```rust
use nexus_web::ws::Client;
use nexus_net::tls::TlsConfig;

let tls = TlsConfig::new()?;
let mut ws = Client::builder()
    .tls(&tls)
    .connect("wss://stream.binance.com:9443/ws")?;
```

When the `tls` feature is enabled, `connect()` returns
`Client<MaybeTls<TcpStream>>` regardless of scheme:

- `ws://` → `MaybeTls::Plain(TcpStream)`
- `wss://` → `MaybeTls::Tls(Box<TlsStream<TcpStream>>)`

You get the same `Client` API either way.

## Using TLS with REST

```rust
use nexus_web::rest::Client;
use nexus_net::tls::TlsConfig;

let tls = TlsConfig::new()?;
let mut conn = Client::builder()
    .tls(&tls)
    .connect("https://api.binance.com")?;
```

## Sans-IO TLS: `TlsCodec`

If you own the transport (mio, io_uring), use `TlsCodec` directly. It
is the rustls state machine with the IO stripped out:

```rust
use nexus_net::tls::{TlsConfig, TlsCodec};

let tls = TlsConfig::new()?;
let mut codec = TlsCodec::new(&tls, "api.example.com")?;

// Drive handshake:
//   codec.wants_write()   → call codec.write_tls(&mut out_buf)  → send out_buf
//   codec.wants_read()    → read raw bytes                      → codec.read_tls(in_bytes)
//   codec.process_new_packets()
// until codec.is_handshaking() == false.
//
// After handshake, read app data with codec.reader() and write app data
// with codec.writer(), then drain/ingest raw bytes as above.
```

`TlsStream<S>` is the blocking `Read + Write` adapter built on
`TlsCodec` — use it when you have an owned stream. `MaybeTls<S>` is a
two-variant enum (`Plain(S)` or `Tls(Box<TlsStream<S>>)`) so upstream
code can be generic over whether TLS is in the pipeline.

## ALPN

rustls supports ALPN. The default `TlsConfig` does not advertise any
ALPN protocols. For HTTP/1.1 over TLS, most servers accept the
absence of ALPN. If you need to advertise `http/1.1` explicitly, build
a `rustls::ClientConfig` manually and wrap it. The public
`TlsConfigBuilder` does not currently surface ALPN configuration — if
you need it, file an issue.

## Certificate chains

By default rustls uses the system trust store via `rustls-native-certs`.
This means:

- **Linux:** `/etc/ssl/certs`
- **macOS:** System keychain
- **Windows:** Windows cert store

Add private CAs with `.add_root_cert(der)`. The format is DER bytes
(not PEM). For PEM files, decode with the `rustls-pemfile` crate
before passing to the builder.

## Performance notes

- A `TlsConfig` is cheap to clone (it's an `Arc<ClientConfig>`).
  Build it once at startup and share it across every connection.
- TLS handshake cost is dominated by cryptography, not nexus-net.
  aws-lc-rs provides hardware-accelerated AES-GCM and ChaCha20-Poly1305.
- Steady-state read/write latency: the codec overhead is a few
  hundred cycles on top of the raw IO. See
  [nexus-web/docs/performance.md](../../nexus-web/docs/performance.md#tls).

## Errors

`TlsError` covers handshake and runtime failures:

- `TlsError::Io(io::Error)` — underlying transport error
- `TlsError::InvalidDnsName(String)` — hostname not valid per RFC 5890
- `TlsError::NoRootCerts` — couldn't load the system trust store
- `TlsError::Rustls(rustls::Error)` — certificate, handshake, or
  record-layer error

All variants flow through `ws::Error::Tls` and `rest::RestError::Tls`
in the higher layers.
