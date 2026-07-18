# Changelog

All notable changes to nexus-async-web are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Internal

- `AsyncReadAdapter` and the async `MaybeTls` moved to the new `nexus-net-tokio`
  crate and are re-exported here; public paths
  (`nexus_async_web::AsyncReadAdapter`, `nexus_async_web::maybe_tls::MaybeTls`)
  are unchanged. The `wire` module is now gated behind the experimental `nexus`
  feature (it holds only the nexus-async-rt adapter).

## [0.10.0] — 2026-06-02

Renamed from `nexus-async-net` to `nexus-async-web`. Protocol types
now imported from `nexus-web` (extracted from `nexus-net` in the same
restructure). Primitives (`buf`, `tls`, `wire`) remain in `nexus-net`.
([#413](https://github.com/Abso1ut3Zer0/nexus/issues/413))

### Breaking

- **Crate renamed** from `nexus-async-net` to `nexus-async-web`.
  Update `Cargo.toml` dependency name and all `use nexus_async_net`
  paths to `use nexus_async_web`.
- **Protocol re-exports** now source from `nexus-web` instead of
  `nexus-net`. No path change for users importing from
  `nexus_async_web` — the re-exports are the same types.

### Migration

| 0.9.x (nexus-async-net) | 0.10.0 (nexus-async-web) |
|---|---|
| `nexus-async-net = "0.9"` | `nexus-async-web = "0.10"` |
| `use nexus_async_net::*` | `use nexus_async_web::*` |

## [0.9.1] — 2026-06-01

### Deprecated

- **This crate is deprecated.** It is being renamed to `nexus-async-web`
  (starting at 0.10.0) as part of the networking crate restructure
  ([#413](https://github.com/Abso1ut3Zer0/nexus/issues/413)). WebSocket
  and HTTP protocol code is moving from `nexus-net` to `nexus-web`, and
  this async adapter follows under the new name. No further updates will
  be published to `nexus-async-net` after this release.

## [0.9.0] — 2026-05-30

### Changed

- **Breaking**: `WsStreamBuilder::connect()`, `connect_with()`, and
  `accept()` now return `(WsReader, WsWriter, S)` tuples instead of
  `WsStream`. The decomposed sans-IO API is the primary interface —
  reader and writer are independent borrows, enabling zero-copy recv
  while sending concurrently.
- **Breaking**: Removed blanket `pub use nexus_net` re-export. Downstream
  code that used `nexus_async_net::nexus_net::…` paths must import from
  `nexus_net` directly or use the new targeted re-exports
  (`CloseCode`, `FrameReader`, `FrameWriter`, `Message`, `Role`,
  `WireStream`, `WriteBuf`, etc.).
- `WsStream` (tokio only) demoted to Stream/Sink ecosystem adapter.
  Construct via `WsStream::from_parts(reader, writer, conn)`. Uses
  `OwnedMessage` (allocating) — prefer `WsReader`/`WsWriter` for
  performance-sensitive paths.

### Added

- `WsReader` / `WsWriter` as the primary decomposed WebSocket API,
  shared across tokio and nexus backends.
- `WsReader::from_raw_parts()` and `WsWriter::from_raw_parts()` for
  custom handshakes, testing, and benchmarks.

## [0.8.0] — 2026-05-11

### Changed

- Dependency declaration: `nexus-pool` `1.0.0` → `1.1.0`. Pulls in
  the strong-Rc/Arc guard contract change from nexus-pool 1.1.0.
  No behavior change for HTTP client pool usage — the new contract
  (in-pool values retained until last guard drops) doesn't bite
  app-lifetime client pools, and the API surface is unchanged.
- **Adopted `nexus-async-rt` 0.7.0's API simplification.** The
  upstream constructor signatures dropped their explicit `IoHandle`
  parameter (now fetched internally via `IoHandle::current()`), so
  call sites in REST and WebSocket nexus connection paths plus the
  `tls_handshake_piggyback` and `ws_nexus_integration` test suites
  simplify from `TcpStream::connect(addr, IoHandle::current())` to
  `TcpStream::connect(addr)`. No behavior change — same TLS read,
  same registration, just hidden inside the constructor.
- Dependency declaration: `nexus-async-rt` `0.6.0` → `0.7.0` to pick
  up the `Type::current()` API and constructor cleanup.
- **`nexus` feature now flagged as experimental** (transitively, since
  the underlying nexus-async-rt crate is now experimental). README
  updated with a Backends section + feature matrix; tokio remains
  the supported path for production use.

### Added

- **Per-backend composite features** for symmetry and discoverability:
  - `tokio-full` = `tokio-tls` + `socket-opts` + `bytes` (recommended bundle)
  - `nexus-tls` = `nexus` + `tls`
  - `nexus-full` = `nexus-tls` + `socket-opts` + `bytes`
  - `full` aliased to `tokio-full` (was previously runtime-less, which
    compiled to almost nothing without explicit runtime selection).

## [0.7.1] — 2026-05-10

Doc + internal cleanup release. No public API change.

### Changed

- Dependency declaration: `nexus-net` `0.7.0` → `0.7.1`. Pulls in
  the new `HTTP_HANDSHAKE_BUFFER` constant (see nexus-net 0.7.1).

### Internal

- 18 inline `4096` literals across `ws::{tokio, nexus}::stream` and
  `rest::{tokio, nexus}::connection` replaced with
  `nexus_net::http::HTTP_HANDSHAKE_BUFFER`. Same numeric value, no
  behavior change. 25 test-side literals also replaced (cfg-gated
  import; lib build stays warning-free).
- Missing-doc additions on `rest::tokio::pool`,
  `rest::tokio::atomic_pool`, `rest::nexus::pool`.
- New `BENCHMARKS.md` with backend-split build instructions
  (tokio-rt vs nexus features) and per-bench table layout for
  Phase 4 measurement reference.

## [0.7.0] — 2026-05-08

The "TLS adapter architectural refactor" release. Companion to
[nexus-net 0.7.0](../nexus-net/CHANGELOG.md). The `MaybeTls` /
`TlsInner` adapter for the nexus-async-rt backend is rebuilt: atomic
construction + handshake, single ciphertext FIFO instead of two,
no separate scratch tmp, allocation-free past initial buffer
construction, structurally correct TLS 1.3 handshake-piggyback
handling. Phase 2 introduces a `WireStream` composition seam so the
nexus-async-rt TLS path delivers plaintext directly into the parser's
buffer (one fewer memcpy per recv).

### Added

- **`AsyncReadAdapter<S>`** (under `feature = "tokio-rt"`) — wraps a
  `tokio::io::AsyncRead + AsyncWrite` source as a `WireStream`.
- **`NexusAsyncReadAdapter<S>`** (under `feature = "nexus"`) — same
  for `nexus_async_rt::AsyncRead + AsyncWrite` sources.
  Use either at the `WsStream::connect_with` / `accept` /
  `HttpConnection::new` call site to plug a custom transport into the
  WireStream-based API.

### Breaking

- **`WsStream<S>` / `HttpConnection<S>`**: trait bound changed from
  `S: AsyncRead + AsyncWrite + Unpin` to `S: WireStream + Unpin` (in
  both backends). Callers passing `MaybeTls` are unaffected. Custom
  transports must wrap in `AsyncReadAdapter` / `NexusAsyncReadAdapter`.
- **`TlsInner::new` / `TlsInner::with_capacities`** removed. Replaced
  by `TlsInner::connect(stream, codec, capacities)` — async,
  constructs the adapter and drives the TLS handshake atomically.
  A `TlsInner` value is always post-handshake.
- **`TlsInner::TMP_SIZE` / `TlsInner::DEFAULT_PENDING_WRITE_CAPACITY`
  consts** removed. Capacities are configured via
  `nexus_net::tls::TlsBufferCapacities`.
- **`WsStreamBuilder::tls_buffer_capacities` /
  `HttpConnectionBuilder::tls_buffer_capacities`**: signature
  changed. Now takes a single `TlsBufferCapacities` value (was
  positional `(usize, usize)`):
  ```rust
  // 0.6.2
  builder.tls_buffer_capacities(8192, 65_536)
  // 0.7.0
  builder.tls_buffer_capacities(TlsBufferCapacities::default())
  builder.tls_buffer_capacities(
      TlsBufferCapacities::builder().pending_write(16 * 1024).build()
  )
  ```
- **The free-function `handshake_tls`** in
  `nexus_async_net::ws::nexus` and `nexus_async_net::rest::nexus` is
  gone. Handshake driving is folded into `TlsInner::connect`.
- **The `tmp: Box<[u8; 8192]>` field on `TlsInner`** is gone. The
  poll_read path reads directly into `pending_read.spare()` —
  ~8 KiB less per TLS connection.

### Fixed

- **TLS 1.3 handshake-piggyback: structurally correct.** When the
  server sends app-data records in the same TCP burst as
  `ServerFinished` (TLS 1.3 allows this), `drive_handshake` stops
  stepping at the handshake transition and the post-handshake
  remainder stays in `pending_read` for the streaming reader. The
  0.6.2 `const_assert!(TMP_SIZE <= 16 KiB)` guard is gone — the
  fix is structural, not a workaround.

### Migration

| 0.6.2 | 0.7.0 |
|---|---|
| `TlsInner::with_capacities(stream, codec, r, w)` | `TlsInner::connect(stream, codec, capacities).await?` |
| `TlsInner::TMP_SIZE` const | `TlsBufferCapacities::default().read_chunk()` |
| `TlsInner::DEFAULT_PENDING_WRITE_CAPACITY` const | `TlsBufferCapacities::default().pending_write()` |
| `.tls_buffer_capacities(8192, 65_536)` | `.tls_buffer_capacities(TlsBufferCapacities::default())` |
| `WsStream::connect_with(my_tokio_tcp, url)` | `WsStream::connect_with(AsyncReadAdapter::new(my_tokio_tcp), url)` |
| `WsStream::accept(my_tokio_tcp)` | `WsStream::accept(AsyncReadAdapter::new(my_tokio_tcp))` |
| `WsStream::connect_with(my_nexus_tcp, url)` (nexus backend) | `WsStream::connect_with(NexusAsyncReadAdapter::new(my_nexus_tcp), url)` |
| `HttpConnection::new(my_tokio_tcp)` | `HttpConnection::new(AsyncReadAdapter::new(my_tokio_tcp))` |

## [0.6.2] — 2026-05-07

The "TLS plaintext-backpressure + steady-state hardening" release.
Picks up [nexus-net 0.6.2](../nexus-net/CHANGELOG.md) and applies the
matching fix to the nexus-async-rt backend (`MaybeTls`). Closes
[#205](https://github.com/Abso1ut3Zer0/nexus/pull/205).

### Added

- `WsStreamBuilder::tls_buffer_capacities(read_cap, write_cap)` —
  tune the TLS adapter's `pending_read` (default 8 KiB) and
  `pending_write` (default 64 KiB) buffer sizes per connection.
  Trading workloads with small frequent messages can reduce
  `pending_write` to 8–16 KiB to lower per-connection memory
  footprint (~81 KiB → ~33 KiB at 16 KiB write cap).
- `HttpConnectionBuilder::tls_buffer_capacities(read_cap, write_cap)`
  — same plumbing for the REST connection builder.
- `MaybeTls::TlsInner::TMP_SIZE` (8 KiB) and
  `DEFAULT_PENDING_WRITE_CAPACITY` (64 KiB) crate-internal constants
  documenting the default sizing. `pending_read_cap` must be at least
  `TMP_SIZE` (constructor panics otherwise).

### Changed

- Dependency declaration: `nexus-net` 0.6.1 → 0.6.2. Pulls in the new
  `read_tls_step`, `try_encrypt`, `set_buffer_limit`, and
  `send_close_notify` primitives + the cursor-FIFO `WriteBuf` API.

### Fixed

- `MaybeTls::poll_read` (`maybe_tls/nexus.rs:85` for the
  `feature = "nexus"` backend) — same plaintext-buffer-full bug as
  nexus-net's `TlsStream::poll_read`. Steady-state app-data bursts
  ≥16 KiB no longer error with `received plaintext buffer full`.
  Adapter now uses `read_tls_step` + `pending_read: ReadBuf`
  spillover.
- `MaybeTls::poll_write` correctly chunks plaintexts larger than
  rustls's outbound plaintext queue cap (default 64 KiB) via
  `try_encrypt`, returning `Ok(N)` where N may be less than the
  input length per the `AsyncWrite` retry contract.
- `MaybeTls::poll_shutdown` queues a TLS `close_notify` alert before
  closing the transport — peers no longer see EOF-without-close_notify
  truncation alerts on graceful disconnect.

### Internal

- `pending_read` and `pending_write` migrated from `Vec<u8>` to
  cursor-FIFO `ReadBuf` / `WriteBuf` (no per-write memmove; auto-reset
  on full drain).
- Per-poll `tmp: Box<[u8; 8192]>` hoisted into `TlsInner` from
  per-poll stack alloca + memset (matches the nexus-net change).
- New integration test
  `tests/maybe_tls_nexus_backpressure.rs` — 3 tests mirroring the
  tokio-side suite (oversize app-data burst, large write chunking,
  oversize write with tiny `pending_write_cap`). Driven through
  `nexus_async_rt::Runtime` + sync server thread; activated under
  `--features nexus,tls`.

### Migration notes

`cargo update -p nexus-async-net` is the only change required for
most users. Public API of `WsClient` / `HttpClient` and their
builders is backwards-compatible; the new
`tls_buffer_capacities(...)` setters are optional.

## [0.6.1] — 2026-05-05

The "TLS handshake byte-loss" release. Picks up the
[nexus-net 0.6.1](../nexus-net/CHANGELOG.md) fix at all three async
TLS call sites and bumps the `nexus-async-rt` dependency declaration
to 0.5.0 (the hardening-series release that landed earlier today).

### Fixed

- `ws::nexus::stream::handshake_tls` (line 71),
  `rest::nexus::connection` (line 71), and
  `maybe_tls::nexus::TlsInner::poll_read` (line 83) now use
  `TlsCodec::read_and_process_tls` instead of the bare
  `read_tls` + `process_new_packets` pair. Closes the production
  bug birch reported in
  [#200](https://github.com/Abso1ut3Zer0/nexus/issues/200) — the
  async client could silently drop unconsumed handshake bytes when
  the server sent a multi-record burst exceeding rustls's per-call
  read cap (long cert chains, large certs, OCSP stapling). The
  observed symptom was
  `Io(UnexpectedEof, "closed during TLS handshake")` after the
  server's timeout (~15-30s).

### Changed

- Dependency declaration: `nexus-async-rt` 0.4.0 → 0.5.0. The 0.5.0
  release was the production-hardening version of nexus-async-rt
  (see its own CHANGELOG for details). nexus-async-net's `nexus`
  backend benefits from those fixes transitively (TaskRef-based
  refcount discipline, `dispose_terminal` routing, intrusive
  cancellation list, `shutdown_quiesce` API).

### Internal

- New end-to-end regression test:
  `tests/ws_nexus_tls_loopback.rs::nexus_async_wss_echo_with_oversize_handshake_burst`
  drives a real wss:// connect through the async client against a
  localhost TLS+WS echo server, with a 10-cert ECDSA-P256 chain
  forcing the handshake burst past rustls's 4096-byte per-call
  deframer cap. Pre-fix this test reproduces birch's exact symptom
  (`Io(UnexpectedEof, "closed during TLS handshake")`); post-fix it
  passes. Hermetic, no network access required.

### Migration notes

`cargo update -p nexus-async-net` is the only change required.
Public API is unchanged.

## [0.6.0] — 2026-04-15

Earlier 0.6.x and prior versions are not documented in this
CHANGELOG. See git history and GitHub release notes for details.
