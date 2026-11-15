# WebSocket

nexus-web implements RFC 6455 WebSocket with three composable layers:

1. **`Message` / `OwnedMessage`** — user-facing message enum
2. **`FrameReader` / `FrameWriter`** — sans-IO codec
3. **`Client<S>`** — blocking convenience wrapper around a socket

Use the top layer when you have a socket and want WebSocket to work.
Drop down to the codec layer when you own the transport.

## Messages

```rust
use nexus_web::ws::{Message, CloseCode, CloseFrame};

match msg {
    Message::Text(s)          => { /* s: &str, zero-copy into ReadBuf */ }
    Message::Binary(bytes)    => { /* bytes: &[u8] */ }
    Message::Ping(bytes)      => { /* auto-handled by Client; reader yields it */ }
    Message::Pong(bytes)      => { /* ... */ }
    Message::Close(Some(CloseFrame { code, reason })) => { /* ... */ }
    Message::Close(None)      => { /* empty close */ }
}
```

`Message<'_>` borrows from the underlying `ReadBuf`. It is valid until
the next call that advances the reader. Call `.into_owned()` to get an
`OwnedMessage` (uses `bytes::Bytes`) if you need to retain it.

## The `Client` convenience path

`Client<S>` owns a stream + a `FrameReader` + a `FrameWriter` +
a `WriteBuf`. Construct via `ClientBuilder`:

```rust
use nexus_web::ws::Client;
use nexus_net::tls::TlsConfig;
use std::time::Duration;

let tls = TlsConfig::new()?;
let mut ws = Client::builder()
    .tls(&tls)
    .disable_nagle()                  // TCP_NODELAY
    .buffer_capacity(1 << 20)         // 1 MiB ReadBuf
    .max_message_size(16 << 20)       // 16 MiB assembled
    .write_buffer_capacity(64 << 10)  // 64 KiB WriteBuf
    .connect_timeout(Duration::from_secs(3))
    .read_timeout(Duration::from_secs(30))
    .connect("wss://stream.binance.com:9443/ws")?;

ws.send_text(r#"{"method":"SUBSCRIBE","params":["btcusdt@trade"],"id":1}"#)?;

loop {
    match ws.recv()? {
        Some(Message::Text(json))     => handle_json(json),
        Some(Message::Binary(bytes))  => handle_binary(bytes),
        Some(Message::Ping(data))     => ws.send_pong(data)?,
        Some(Message::Pong(_))        => {}
        Some(Message::Close(frame))   => {
            ws.close(CloseCode::Normal, "bye")?;
            break;
        }
        None => {
            // EOF, WouldBlock, or buffer full. See buffers.md.
            break;
        }
    }
}
```

### Role

The builder uses the **client role** by default when you call
`connect()`: outgoing frames are masked (per RFC 6455) and inbound
frames are rejected if they are masked. Use `Client::builder().accept(stream)`
for the **server role** — outbound frames are unmasked, inbound frames
must be masked.

### Control frames

Ping/pong/close are exposed as regular `Message` variants. `Client` does
**not** auto-reply to pings — you see them and decide. This is
intentional: auto-pong hides liveness and complicates tests. If you
want auto-reply, call `ws.send_pong(data)` when you see a `Ping`.

`CloseCode` enumerates the RFC 6455 status codes; use
`CloseCode::Normal`, `CloseCode::GoingAway`, `CloseCode::Policy`, etc.

## Sans-IO parse loop

If you own the transport (mio, io_uring, DPDK, replay), use
`FrameReader` directly:

```rust
use nexus_web::ws::{FrameReader, Role, Message};

let mut reader = FrameReader::builder()
    .role(Role::Client)
    .buffer_capacity(1 << 20)
    .max_message_size(16 << 20)
    .build();

// Event loop: hand the reader some bytes, then drain frames.
loop {
    // 1. Get spare space in the ReadBuf.
    let dst = reader.spare();
    if dst.is_empty() {
        reader.compact();       // reclaim consumed bytes
        continue;
    }
    let n = your_transport.read(dst)?;
    if n == 0 { break; }        // EOF
    reader.filled(n);           // tell reader how much you wrote

    // 2. Drain all complete frames from the buffer.
    while reader.poll()? {
        match reader.next()? {
            Some(Message::Text(s))     => handle_text(s),
            Some(Message::Binary(b))   => handle_binary(b),
            Some(Message::Ping(b))     => enqueue_pong(b),
            Some(Message::Close(_))    => return Ok(()),
            Some(_) | None             => {}
        }
    }
}
```

`poll()` returns `true` when a complete frame is parsed and `false`
when more bytes are needed. `next()` yields the parsed message (or
`None` if the reader just finished an internal control frame). The
returned `Message<'_>` borrows from `reader`; consume it before the
next `poll()`.

### Fragmentation

`FrameReader` reassembles fragmented messages (CONT frames) internally,
up to `max_message_size`. You only see assembled messages. If the
peer sends a 20 MiB message and your limit is 16 MiB, `next()` returns
`Err(ProtocolError::MessageTooLarge)` — the connection is done.

## Sans-IO encode

`FrameWriter` encodes one frame at a time into a buffer:

```rust
use nexus_web::ws::{FrameWriter, Role};
use nexus_net::buf::WriteBuf;

let mut writer = FrameWriter::new(Role::Client);
let mut buf = WriteBuf::new(64 * 1024, 14);  // 14 bytes of header headroom

writer.encode_text_into(b"hello", &mut buf);
your_transport.write_all(buf.data())?;
buf.clear();
```

### Why `WriteBuf` with headroom?

A WebSocket frame header is 2 to 14 bytes and depends on payload length
and masking. nexus-web writes the **payload** first using the headroom
at the front of the buffer, then **prepends** the finalized header.
This avoids a second pass over the payload for masking (mask is
XORed into place while the payload is being written) and eliminates
double-buffering.

See [nexus-net/docs/buffers.md](../../nexus-net/docs/buffers.md) for the full model.

### Masking (client role)

Per RFC 6455, client-to-server frames must be masked with a random
32-bit key. nexus-web uses a ChaCha8 PRNG seeded once per `FrameWriter`
for fast, predictable mask generation. Masking is applied via SIMD
(SSE2/AVX2) XOR; at 128B the cost is ~12 cycles.

Server role frames are never masked. The reader enforces both
directions: a client-role reader rejects masked inbound frames; a
server-role reader rejects unmasked inbound frames.

## Handshake

`Client::builder().connect(url)` performs the full HTTP Upgrade
handshake internally. If you need to run the handshake manually (e.g.
custom headers, HTTP proxy tunneling), use the `handshake` module:

```rust
use nexus_web::ws::handshake;

let key = handshake::generate_key();
let req = handshake::build_upgrade_request("api.example.com", "/ws", &key);
// Send `req` on your transport, read response, call:
handshake::validate_response(&response_bytes, &key)?;
```

## Errors

`ws::Error` is the top-level error:

- `Error::Io(io::Error)` — transport failure
- `Error::Protocol(ProtocolError)` — malformed frames, oversized
  messages, masking violations, bad opcode, bad UTF-8
- `Error::Encode(EncodeError)` — outbound encoding failure (buffer
  too small, oversized control frame)
- `Error::Handshake(HandshakeError)` — HTTP upgrade failure
- `Error::Tls(TlsError)` — TLS negotiation / read / write failure

On IO error during a send, the `Client` is marked **poisoned** (a
partial frame may have been written). `is_poisoned()` is `true`, and
subsequent sends return `Err(ConnectionPoisoned)`. See
[errors.md](./errors.md).

## Autobahn conformance

The codec passes all **517/517** cases in the Autobahn Testsuite
(`fuzzingclient` + `fuzzingserver`), including strict UTF-8
validation, fragmentation edge cases, and close-code handling.
