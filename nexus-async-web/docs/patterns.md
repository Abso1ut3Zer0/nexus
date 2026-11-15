# Patterns and Recipes

Production patterns for nexus-async-web. Each recipe is written
against the public API with imports included.

## Exchange client with reconnect

Full-duplex market-data feed: connect, subscribe, stream, reply to
pings, reconnect on any failure with exponential backoff.

```rust
use nexus_async_web::ws::{WsStreamBuilder, WsError};
use nexus_web::ws::{Message, CloseCode};
use nexus_net::tls::TlsConfig;
use std::time::Duration;

pub async fn run_feed(tls: TlsConfig) {
    let mut backoff = Duration::from_millis(100);
    let max_backoff = Duration::from_secs(30);

    loop {
        match one_session(&tls).await {
            Ok(()) => {
                tracing::info!("feed closed cleanly, reconnecting");
                backoff = Duration::from_millis(100);
            }
            Err(e) => {
                tracing::warn!(?e, "feed disconnected");
                tokio::time::sleep(backoff).await;
                backoff = (backoff * 2).min(max_backoff);
            }
        }
    }
}

async fn one_session(tls: &TlsConfig) -> Result<(), WsError> {
    let mut ws = WsStreamBuilder::new()
        .tls(tls)
        .disable_nagle()
        .buffer_capacity(1 << 20)
        .max_message_size(16 << 20)
        .connect_timeout(Duration::from_secs(3))
        .connect("wss://stream.binance.com:9443/ws")
        .await?;

    // Re-send subscription state on every reconnect.
    ws.send_text(r#"{
        "method":"SUBSCRIBE",
        "params":["btcusdt@trade","btcusdt@depth20@100ms"],
        "id":1
    }"#).await?;

    loop {
        match ws.recv().await? {
            Some(Message::Text(json))    => on_json(json),
            Some(Message::Binary(bytes)) => on_binary(bytes),
            Some(Message::Ping(data))    => ws.send_pong(data).await?,
            Some(Message::Pong(_))       => {}
            Some(Message::Close(_))      => {
                let _ = ws.close(CloseCode::Normal, "").await;
                return Ok(());
            }
            None => return Ok(()),  // EOF
        }
    }
}

fn on_json(_: &str) {}
fn on_binary(_: &[u8]) {}
```

Key points:

- **Subscription state is re-sent every connect.** WebSocket
  doesn't persist subscriptions across sessions.
- **`Message::Text(s)` borrows from the `ws`.** If you need to
  process it later, copy via `.to_owned()` before the next `recv`.
- **Disable Nagle.** Required for every trading workload.

## REST with pooled connections

Trading REST client with pooled keep-alive connections, idempotent
retry, and self-healing reconnect.

```rust
use nexus_async_web::rest::ClientPool;
use nexus_web::rest::RestError;
use nexus_net::tls::TlsConfig;
use std::time::Duration;

pub async fn build_pool(api_key: String, tls: TlsConfig) -> anyhow::Result<ClientPool> {
    let pool = ClientPool::builder()
        .url("https://api.binance.com")
        .base_path("/api/v3")
        .default_header("X-MBX-APIKEY", &api_key)?
        .connections(4)
        .tls(&tls)
        .disable_nagle()
        .tcp_keepalive(Duration::from_secs(60))
        .write_buffer_capacity(32 * 1024)
        .response_buffer_capacity(64 * 1024)
        .max_body_size(1 << 20)
        .build()
        .await?;
    Ok(pool)
}

/// GET a resource. Retries on transport errors only — safe for GETs.
pub async fn get_idempotent(pool: &ClientPool, path: &str) -> Result<Vec<u8>, RestError> {
    for attempt in 0..3 {
        let mut slot = pool.acquire().await?;
        let s = &mut *slot;
        let req = s.writer.get(path).finish()?;
        let (conn, reader) = s.conn_and_reader()?;

        match conn.send(req, reader).await {
            Ok(resp) => {
                if resp.status() < 500 {
                    return Ok(resp.body().to_vec());
                }
                tracing::warn!(status = resp.status(), attempt, "5xx, retrying");
            }
            Err(RestError::Io(_))
            | Err(RestError::ConnectionPoisoned)
            | Err(RestError::ConnectionClosed(_))
            | Err(RestError::ConnectionStale)
            | Err(RestError::ReadTimeout) => {
                // Drop the slot. Next acquire will eject the dead slot and
                // spawn a reconnect task. No manual heal needed.
                drop(slot);
                tracing::warn!(attempt, "transport error, healing pool");
            }
            Err(e) => return Err(e),
        }
        tokio::time::sleep(Duration::from_millis(50 << attempt)).await;
    }
    Err(RestError::ReadTimeout)
}

/// POST that MUST NOT be retried blindly. Use exchange-side idempotency.
pub async fn place_order(pool: &ClientPool, body: &[u8]) -> Result<Vec<u8>, RestError> {
    let Some(mut slot) = pool.try_acquire() else {
        return Err(RestError::ConnectionClosed("no healthy slot"));
    };
    let s = &mut *slot;
    let req = s.writer.post("/order")
        .header("Content-Type", "application/json")
        .body(body)
        .finish()?;
    let (conn, reader) = s.conn_and_reader()?;
    let resp = conn.send(req, reader).await?;
    Ok(resp.body().to_vec())
}
```

Notice:

- `get_idempotent` uses `acquire().await` — background retry is
  acceptable.
- `place_order` uses `try_acquire()` — on the trading hot path we
  **fail fast** if the pool is exhausted. Waiting on reconnect
  while the book moves is worse than a clean rejection.
- `place_order` does **not** retry on error. A half-sent POST may
  have reached the exchange; blind retry risks duplicate orders.
  Use exchange-provided idempotency (`clientOrderId`) for safety.

## Gateway accepting many connections

Server side: accept many WebSocket clients concurrently.

```rust
use nexus_async_web::ws::WsStreamBuilder;
use nexus_web::ws::Message;
use tokio::net::TcpListener;

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let listener = TcpListener::bind("0.0.0.0:9001").await?;
    loop {
        let (sock, addr) = listener.accept().await?;
        sock.set_nodelay(true)?;
        tokio::spawn(async move {
            let mut ws = match WsStreamBuilder::new().accept(sock).await {
                Ok(ws) => ws,
                Err(e) => {
                    tracing::warn!(?addr, ?e, "handshake failed");
                    return;
                }
            };
            while let Ok(Some(msg)) = ws.recv().await {
                match msg {
                    Message::Text(s) => {
                        if ws.send_text(s).await.is_err() { break; }
                    }
                    Message::Binary(b) => {
                        if ws.send_binary(b).await.is_err() { break; }
                    }
                    Message::Ping(data) => {
                        let _ = ws.send_pong(data).await;
                    }
                    Message::Close(_) => break,
                    _ => {}
                }
            }
        });
    }
}
```

For a serious gateway:

- Pin `WsStreamBuilder::buffer_capacity` smaller if clients are
  low-rate (default 1 MiB is per-connection — 10K clients = 10 GiB).
- Enforce `max_message_size` to reject abuse.
- Use a `LocalSet` + `current_thread` runtime sharded across cores
  (SO_REUSEPORT on the listener) for hot-path workloads.

## Combined REST + WebSocket client

Typical exchange integration: REST for account / orders,
WebSocket for market data. They're separate connections.

```rust
use nexus_async_web::{rest::ClientPool, ws::WsStreamBuilder};
use nexus_net::tls::TlsConfig;

struct Exchange {
    rest: ClientPool,
    // ws is typically run in its own task that owns it,
    // so the struct holds a handle for sending (channel, actor, etc.)
}

impl Exchange {
    async fn new(api_key: String, tls: TlsConfig) -> anyhow::Result<Self> {
        let rest = ClientPool::builder()
            .url("https://api.exchange.com")
            .default_header("X-API-KEY", &api_key)?
            .connections(4)
            .tls(&tls)
            .build()
            .await?;

        // Spawn the feed task separately so it can reconnect independently.
        let tls2 = tls.clone();
        tokio::task::spawn_local(async move {
            super::run_feed(tls2).await;
        });

        Ok(Self { rest })
    }
}
```

## See also

- Sync (blocking-thread) equivalents in
  [nexus-web/docs/patterns.md](../../nexus-web/docs/patterns.md).
- [client-pool.md](./client-pool.md) for pool semantics.
- [reconnect.md](./reconnect.md) for self-healing details.
