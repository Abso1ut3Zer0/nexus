# Changelog

All notable changes to nexus-net-tokio are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- Initial release. The tokio async wire transport for `nexus-net`, extracted
  from `nexus-async-web` so `nexus-async-fix-engine` can share it without
  depending on a web crate:
  - `AsyncReadAdapter<S>` — wraps `tokio::io::AsyncRead + AsyncWrite` as a
    `nexus_net::WireStream`.
  - `MaybeTls` — async transparent plaintext/TLS transport implementing
    `WireStream`; the `Tls` variant (feature `tls`, via `tokio-rustls`) fills
    the parser buffer directly from rustls's plaintext queue.

  Keeping this out of `nexus-net` preserves that crate as a runtime-agnostic
  base — its only optional deps stay `rustls`/`bytes`, with no tokio in its
  graph.
