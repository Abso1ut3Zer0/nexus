# Overview

nexus-async-web is a thin async wrapper around
[nexus-net](../../nexus-net/docs/overview.md). Every protocol
decision — frame parsing, masking, HTTP writing, TLS — lives in
nexus-net. This crate adds `.await` at the I/O boundary and nothing
else.

## What's in the box

- **`ws::WsStream<S>`** — async WebSocket over any
  `AsyncRead + AsyncWrite + Unpin` stream. Wraps a nexus-net
  `FrameReader` + `FrameWriter`.
- **`ws::WsStreamBuilder`** — configure buffer sizes, TLS, socket
  options, connect timeout, and connect to a URL.
- **`rest::HttpConnection<S>`** — async HTTP/1.1 keep-alive
  connection. Wraps a nexus-net `RequestWriter` output and
  `ResponseReader` input.
- **`rest::ClientPool`** — single-threaded pool of HTTP
  connections with **inline self-healing reconnect**. This is the
  hard part and the main reason to use this crate for trading
  systems.
- **`rest::AtomicClientPool`** — the same pool semantics over
  `nexus_pool::sync::Pool`. Single acquirer, any-thread returner.

## Runtime backends

Exactly one of `tokio-rt` or `nexus` must be enabled at a time:

- **`tokio-rt`** (default): uses `tokio::net::TcpStream`,
  `AsyncRead`/`AsyncWrite`, `tokio::spawn_local`, `tokio::time::sleep`.
  The WebSocket stream additionally implements `futures_core::Stream`
  and `futures_sink::Sink` for compatibility with the tokio
  ecosystem (`tokio_util`, `futures::StreamExt`, etc.).
- **`nexus`**: uses nexus-async-rt primitives (single-threaded,
  pre-allocated tasks, mio-backed). No `Stream`/`Sink` traits —
  direct `recv()`/`send_*()` calls are preferred for latency.

This document uses the `tokio-rt` surface in examples because it's
the default. The `nexus` backend has an identical `recv`/`send_*`
method surface.

## Relationship to nexus-net

You can think of the stack as:

```text
 nexus-async-web  WsStream<S>       ──►  async recv/send
                  HttpConnection    ──►  async send
                  ClientPool        ──►  pool + reconnect
       ▲
       │  (thin .await wrapper)
       ▼
   nexus-net      FrameReader/Writer      (sans-IO)
                  RequestWriter            (sans-IO)
                  ResponseReader           (sans-IO)
                  TlsCodec                 (sans-IO)
```

Every protocol byte is produced and consumed by nexus-net. This crate
calls `AsyncReadExt::read` into the `FrameReader::spare()` slice, then
`reader.filled(n)`, then drains frames — the async version of the
sans-IO loop in [nexus-web/docs/websocket.md](../../nexus-web/docs/websocket.md).

Because the codec is shared, numbers for parsing, masking, UTF-8
validation, and encoding are **identical** to nexus-net. The async
wrapper adds the cost of `poll_*`/`Waker` bookkeeping, which is small
— see [performance.md](./performance.md).

## When to use which

| Situation | Use |
|-----------|-----|
| Trading hot thread (blocking, pinned, single-threaded) | **nexus-net** |
| mio / io_uring / DPDK event loop | **nexus-net** (sans-IO) |
| You're already on tokio | **nexus-async-web** |
| Single-threaded tokio (`current_thread` + `LocalSet`) | **nexus-async-web** with `tokio-rt` |
| Runtime-free, single-threaded, nexus-async-rt | **nexus-async-web** with `nexus` |
| Multi-threaded tokio with shared REST pool | **nexus-async-web** `AtomicClientPool` |

nexus-async-web is designed to **not fight tokio**. If you're using
axum, reqwest, or anything else that assumes tokio, nexus-async-web
drops in alongside without bridging.

## Design notes

- **Pool reconnect is inline.** When a slot's connection dies, the
  pool ejects it and spawns a reconnect task. `try_acquire()` returns
  `None` while the task is running; `acquire().await` waits for the
  slot to come back. See [reconnect.md](./reconnect.md).
- **`!Send` by design (single-threaded pool).** `ClientPool` is
  intentionally `!Send` so it can skip synchronization. Use
  `AtomicClientPool` if you need `Send`.
- **Zero allocation on hot path.** `WsStream::recv()` returns
  `Message<'_>` that borrows from the internal `ReadBuf`. No copies,
  no `Arc`.
