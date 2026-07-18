# nexus-net-tokio

Tokio async wire transport for [`nexus-net`](../nexus-net): the runtime binding
that implements `WireStream` over tokio streams.

`nexus-net` stays runtime-agnostic — its `WireStream`/`ParserSink` traits and
the sync `MaybeTls<S>` (`std::io::Read + Write`) carry no runtime dependency.
This crate is the tokio layer above it, so `nexus-async-web` and
`nexus-async-fix-engine` share one async transport instead of each rolling
their own.

## What's Here

- **`AsyncReadAdapter<S>`** — wraps any `tokio::io::AsyncRead + AsyncWrite`
  source as a `nexus_net::WireStream`. Use it to run a codec over a raw
  `tokio::net::TcpStream`, a mock stream, or any custom tokio transport.
- **`MaybeTls`** — the async counterpart of `nexus_net::MaybeTls<S>`:
  transparent plaintext (`Plain`) or TLS (`Tls`, via `tokio-rustls`), both
  implementing `WireStream`. The `Tls` variant fills the parser buffer directly
  from rustls's plaintext queue, skipping the `AsyncRead` `&mut [u8]`
  intermediate.

## Features

- `tls` — enables the `MaybeTls::Tls` variant (pulls `tokio-rustls` and
  `nexus-net/tls`).

Tokio itself is always on: this crate *is* the tokio binding.

## When to Use

You usually don't depend on this directly — `nexus-async-web` and
`nexus-async-fix-engine` re-export what you need. Reach for it when composing a
codec over a custom tokio transport via `AsyncReadAdapter`.

```
nexus-async-web ────────► nexus-net-tokio ──► nexus-net
nexus-async-fix-engine ─► nexus-net-tokio ──► nexus-net
```

## License

Licensed under either of [Apache-2.0](./LICENSE-APACHE) or [MIT](./LICENSE-MIT)
at your option.
