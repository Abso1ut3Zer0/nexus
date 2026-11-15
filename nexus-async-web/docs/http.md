# Async HTTP / REST

The async REST surface is `rest::HttpConnection<S>` — an async
HTTP/1.1 keep-alive connection that wraps a nexus-net
`ResponseReader` on the inbound side and accepts nexus-net
`Request<'_>` bytes on the outbound side.

For production, you almost always want a **pool** of these
connections with self-healing reconnect. See
[client-pool.md](./client-pool.md) and
[atomic-client-pool.md](./atomic-client-pool.md).

## `HttpConnection` basics

```rust
use nexus_async_web::rest::HttpConnectionBuilder;
use nexus_web::rest::RequestWriter;
use nexus_web::http::ResponseReader;
use nexus_net::tls::TlsConfig;
use std::time::Duration;

#[tokio::main(flavor = "current_thread")]
async fn main() -> anyhow::Result<()> {
    let tls = TlsConfig::new()?;

    let mut conn = HttpConnectionBuilder::new()
        .tls(&tls)
        .disable_nagle()
        .connect_timeout(Duration::from_secs(3))
        .connect("https://api.binance.com")
        .await?;

    // RequestWriter owns the outbound WriteBuf.
    let mut writer = RequestWriter::new("api.binance.com")?;
    writer.default_header("X-MBX-APIKEY", api_key)?;
    writer.set_base_path("/api/v3")?;

    let mut reader = ResponseReader::new(32 * 1024);

    let req = writer.get("/ticker/price")
        .query("symbol", "BTCUSDT")
        .finish()?;

    let resp = conn.send(req, &mut reader).await?;
    println!("{}: {} bytes", resp.status(), resp.body().len());

    // Reuse conn for the next request (keep-alive).
    let req = writer.get("/depth")
        .query("symbol", "BTCUSDT")
        .query("limit", "100")
        .finish()?;
    let resp = conn.send(req, &mut reader).await?;

    Ok(())
}
```

Note that `RequestWriter`, `Request<'_>`, `ResponseReader`, and
`RestResponse<'_>` all come from nexus-net. The async layer only
adds the wire-level `send(...).await`.

See [nexus-web/docs/http.md](../../nexus-web/docs/http.md) for
`RequestWriter` typestate mechanics, body variants, and chunked
transfer.

## Builder options

```rust
HttpConnectionBuilder::new()
    .tls(&tls)                                   // feature "tls"
    .disable_nagle()
    .connect_timeout(Duration::from_secs(3))
    .tcp_keepalive(Duration::from_secs(60))      // feature "socket-opts"
    .recv_buffer_size(1 << 20)                   // feature "socket-opts"
    .send_buffer_size(1 << 20);                  // feature "socket-opts"
```

## Single connection vs pool

A single `HttpConnection` is **not concurrent-safe** — `send()` takes
`&mut self` because the underlying `WriteBuf` and
`ResponseReader` are owned. If you have concurrent tasks that need
to issue REST calls, you need either:

- **One `HttpConnection` per task** (fine for a few connections),
- **`ClientPool`** for single-threaded tokio (`current_thread`
  runtime + `LocalSet`), or
- **`AtomicClientPool`** for multi-threaded tokio.

The pool also handles reconnect — see [reconnect.md](./reconnect.md).

## Poisoning

On a transport error mid-request, `HttpConnection` is marked
poisoned (`is_poisoned() == true`) and subsequent `send()` calls
return `RestError::ConnectionPoisoned`. The caller must create a
new connection. When using a pool, this is automatic — see the
pool docs.

## Patterns

- Single-task keep-alive client: use `HttpConnection` directly.
- Trading system (single thread): use `ClientPool`.
- Web server / multi-thread: use `AtomicClientPool`.
- REST+WebSocket side-by-side on the same exchange: independent
  connections — they're separate protocols.

See [patterns.md](./patterns.md) for full recipes.
