# Async WebSocket

The async WebSocket type is `ws::WsStream<S>`. It's structurally
identical to nexus-net's `Client<S>` but with `async fn` on every
I/O method.

## Connect and stream

```rust
use nexus_async_web::ws::WsStreamBuilder;
use nexus_web::ws::{Message, CloseCode};
use nexus_net::tls::TlsConfig;
use std::time::Duration;

#[tokio::main(flavor = "current_thread")]
async fn main() -> anyhow::Result<()> {
    let tls = TlsConfig::new()?;

    let mut ws = WsStreamBuilder::new()
        .tls(&tls)
        .disable_nagle()
        .buffer_capacity(1 << 20)
        .max_message_size(16 << 20)
        .connect_timeout(Duration::from_secs(3))
        .connect("wss://stream.binance.com:9443/ws")
        .await?;

    ws.send_text(r#"{"method":"SUBSCRIBE","params":["btcusdt@trade"],"id":1}"#)
        .await?;

    loop {
        match ws.recv().await? {
            Some(Message::Text(json))    => handle(json),
            Some(Message::Binary(bytes)) => handle_binary(bytes),
            Some(Message::Ping(data))    => ws.send_pong(data).await?,
            Some(Message::Pong(_))       => {}
            Some(Message::Close(_))      => {
                ws.close(CloseCode::Normal, "bye").await?;
                break;
            }
            None => break,  // EOF
        }
    }
    Ok(())
}

fn handle(_: &str) {}
fn handle_binary(_: &[u8]) {}
```

`WsStream::recv()` returns `Result<Option<Message<'_>>, WsError>`:

- `Ok(Some(msg))` — a full message (all continuation frames
  reassembled, UTF-8 validated if text)
- `Ok(None)` — EOF or the peer cleanly closed
- `Err(e)` — protocol violation, IO error, or TLS error

The returned `Message<'_>` borrows from the internal `ReadBuf` inside
`ws` — you cannot hold it across another `.await` on `ws`. Copy
(`.into_owned()` or `.to_string()`) if you need to.

## Builder options

```rust
WsStreamBuilder::new()
    .tls(&tls)                       // TLS config (feature "tls")
    .disable_nagle()                  // TCP_NODELAY
    .buffer_capacity(1 << 20)         // ReadBuf size
    .max_read_size(64 << 10)          // max bytes per AsyncRead::read
    .compact_at(0.5)                  // compaction trigger
    .max_frame_size(16 << 20)
    .max_message_size(16 << 20)
    .write_buffer_capacity(64 << 10)
    .connect_timeout(Duration::from_secs(3))
    .tcp_keepalive(Duration::from_secs(60))     // feature "socket-opts"
    .recv_buffer_size(1 << 20)                   // feature "socket-opts"
    .send_buffer_size(1 << 20);                  // feature "socket-opts"
```

See [tuning.md](./tuning.md) for the recv-path knobs (`buffer_capacity`,
`max_read_size`, `compact_at`) in detail.

## Server side: `accept`

```rust
use tokio::net::TcpListener;
use nexus_async_web::ws::WsStreamBuilder;
use nexus_web::ws::Message;

let listener = TcpListener::bind("0.0.0.0:9001").await?;
loop {
    let (sock, _) = listener.accept().await?;
    sock.set_nodelay(true)?;
    tokio::task::spawn(async move {
        let mut ws = match WsStreamBuilder::new().accept(sock).await {
            Ok(ws) => ws,
            Err(e) => { eprintln!("handshake: {e}"); return; }
        };
        while let Ok(Some(msg)) = ws.recv().await {
            if let Message::Text(s) = msg {
                let _ = ws.send_text(s).await;
            }
        }
    });
}
```

## `Stream` and `Sink` (tokio backend only)

When the `tokio-rt` feature is enabled, `WsStream<S>` implements
`futures_core::Stream<Item = Result<OwnedMessage, WsError>>` and
`futures_sink::Sink<OwnedMessage>`. This lets you compose with
`futures::StreamExt`, `tokio_util::codec`, and other ecosystem
crates.

```rust
use futures::{SinkExt, StreamExt};
use nexus_web::ws::OwnedMessage;

while let Some(item) = ws.next().await {
    match item? {
        OwnedMessage::Text(s) => { /* ... */ }
        OwnedMessage::Binary(b) => { /* ... */ }
        _ => {}
    }
}

ws.send(OwnedMessage::Text("hi".into())).await?;
```

**Cost note.** The `Stream`/`Sink` path goes through `OwnedMessage`,
which allocates (`bytes::Bytes`). The direct `recv()`/`send_text()`
path is zero-copy. For trading hot paths, prefer the direct methods.

The `nexus` backend intentionally **does not** implement
`Stream`/`Sink` — the owned-message conversion would defeat the
zero-alloc guarantees that backend exists to provide.

## Errors and poisoning

`WsError` has the same structure as nexus-net's `ws::Error` — see
[nexus-web/docs/errors.md](../../nexus-web/docs/errors.md). An IO
error during a send poisons the `WsStream`; you must reconnect.
Unlike the REST pool, there is no automatic WebSocket reconnect
at the library layer — WebSocket connections are session-stateful
(subscriptions, auth), so the application must re-establish state.

See [patterns.md — Exchange client with reconnect](./patterns.md#exchange-client-with-reconnect)
for a production reconnect loop.
