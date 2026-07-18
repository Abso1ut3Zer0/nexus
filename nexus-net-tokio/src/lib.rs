//! Tokio async wire transport for [`nexus-net`](nexus_net).
//!
//! This crate is the tokio binding for nexus-net's runtime-agnostic
//! [`WireStream`] seam, kept separate so
//! `nexus-net` itself stays 100% runtime-free.
//!
//! - [`AsyncReadAdapter`] wraps any `tokio::io::AsyncRead + AsyncWrite`
//!   source as a [`WireStream`] — use it to drive
//!   a `WireStream` consumer over a raw `TcpStream`, a mock, or any other
//!   tokio transport.
//! - [`MaybeTls`] is the plain-or-TLS async transport used by tokio-based
//!   protocol clients (WebSocket, HTTP, FIX). Its TLS variant is gated on
//!   the `tls` feature.

#![warn(missing_docs)]

use std::io;
use std::pin::Pin;
use std::task::{Context, Poll};

use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};
use tokio::net::TcpStream;

use nexus_net::{ParserSink, WireStream};

// =============================================================================
// AsyncReadAdapter
// =============================================================================

/// Wraps a `tokio::io::AsyncRead + AsyncWrite` source as a [`WireStream`].
///
/// Use this when constructing a `WireStream` consumer (`WsStream`,
/// `HttpConnection`, the async FIX client, …) over a custom tokio
/// transport (raw `TcpStream`, mock streams, etc.). The canonical
/// [`MaybeTls`] transport implements `WireStream` directly.
///
/// ```ignore
/// use nexus_net_tokio::AsyncReadAdapter;
///
/// // Wrap a raw tokio stream so a WireStream consumer can drive it.
/// let tcp = tokio::net::TcpStream::connect(addr).await?;
/// let adapter = AsyncReadAdapter::new(tcp);
/// ```
pub struct AsyncReadAdapter<S> {
    inner: S,
}

impl<S> AsyncReadAdapter<S> {
    /// Wrap an inner `AsyncRead+AsyncWrite` stream.
    pub fn new(inner: S) -> Self {
        Self { inner }
    }

    /// Access the inner stream.
    pub fn get_ref(&self) -> &S {
        &self.inner
    }

    /// Mutable access to the inner stream.
    pub fn get_mut(&mut self) -> &mut S {
        &mut self.inner
    }

    /// Decompose into the inner stream.
    pub fn into_inner(self) -> S {
        self.inner
    }
}

// `S: Unpin` makes `AsyncReadAdapter<S>: Unpin`, so `get_mut()` and
// `Pin::new(&mut inner)` below are safe pin operations — no unsafe
// projection is involved.
impl<S: AsyncRead + AsyncWrite + Unpin> WireStream for AsyncReadAdapter<S> {
    fn poll_fill_into<P: ParserSink>(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        sink: &mut P,
        max: usize,
    ) -> Poll<io::Result<usize>> {
        if max == 0 || sink.spare().is_empty() {
            return Poll::Ready(Err(no_space_err()));
        }
        let this = self.get_mut();
        fill_via_async_read(Pin::new(&mut this.inner), cx, sink, max)
    }

    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        let this = self.get_mut();
        Pin::new(&mut this.inner).poll_write(cx, buf)
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        let this = self.get_mut();
        Pin::new(&mut this.inner).poll_flush(cx)
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        let this = self.get_mut();
        Pin::new(&mut this.inner).poll_shutdown(cx)
    }
}

// =============================================================================
// MaybeTls
// =============================================================================

/// Async stream that may or may not be TLS-wrapped.
///
/// Constructed by the tokio protocol clients in `nexus-async-web`
/// (and the async FIX client) based on the URL scheme: plaintext for
/// `ws://`/`http://`, TLS for `wss://`/`https://`. Implements both
/// tokio's `AsyncRead + AsyncWrite` and nexus-net's [`WireStream`].
pub enum MaybeTls {
    /// Plain TCP (ws://, http://).
    Plain(TcpStream),
    /// TLS over TCP (wss://, https://).
    #[cfg(feature = "tls")]
    Tls(Box<tokio_rustls::client::TlsStream<TcpStream>>),
}

impl AsyncRead for MaybeTls {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        match self.get_mut() {
            Self::Plain(s) => Pin::new(s).poll_read(cx, buf),
            #[cfg(feature = "tls")]
            Self::Tls(s) => Pin::new(s).poll_read(cx, buf),
        }
    }
}

impl AsyncWrite for MaybeTls {
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        match self.get_mut() {
            Self::Plain(s) => Pin::new(s).poll_write(cx, buf),
            #[cfg(feature = "tls")]
            Self::Tls(s) => Pin::new(s).poll_write(cx, buf),
        }
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        match self.get_mut() {
            Self::Plain(s) => Pin::new(s).poll_flush(cx),
            #[cfg(feature = "tls")]
            Self::Tls(s) => Pin::new(s).poll_flush(cx),
        }
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        match self.get_mut() {
            Self::Plain(s) => Pin::new(s).poll_shutdown(cx),
            #[cfg(feature = "tls")]
            Self::Tls(s) => Pin::new(s).poll_shutdown(cx),
        }
    }
}

// =============================================================================
// WireStream
// =============================================================================
//
// On the tokio backend the TLS variant goes through `tokio_rustls`,
// which buffers plaintext internally and exposes only the
// `AsyncRead` interface — there's no direct way to drain that
// buffer into a `ParserSink` without a slice intermediate. So both
// variants here delegate to the slow path (poll_read into
// `sink.spare()`); the type-system seam is consistent across
// backends, but the zero-copy win is nexus-async-rt-only.

impl WireStream for MaybeTls {
    fn poll_fill_into<P: ParserSink>(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        sink: &mut P,
        max: usize,
    ) -> Poll<io::Result<usize>> {
        if max == 0 || sink.spare().is_empty() {
            return Poll::Ready(Err(no_space_err()));
        }
        match self.get_mut() {
            Self::Plain(s) => fill_via_async_read(Pin::new(s), cx, sink, max),
            #[cfg(feature = "tls")]
            Self::Tls(s) => fill_via_async_read(Pin::new(s), cx, sink, max),
        }
    }

    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        <Self as AsyncWrite>::poll_write(self, cx, buf)
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        <Self as AsyncWrite>::poll_flush(self, cx)
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        <Self as AsyncWrite>::poll_shutdown(self, cx)
    }
}

/// The `InvalidInput` error both `poll_fill_into` impls return when the caller
/// violates the `WireStream` precondition (`max > 0` and a non-empty
/// `sink.spare()`).
fn no_space_err() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        "poll_fill_into called with no buffer space \
         (max == 0 or sink.spare() is empty)",
    )
}

/// Slow-path helper: poll_read from a tokio AsyncRead source
/// directly into `sink.spare()`, capped at `max`.
///
/// Caller (the `WireStream::poll_fill_into` impl above) already
/// validated `max > 0` and `sink.spare()` non-empty per the trait
/// contract — no need to re-check.
fn fill_via_async_read<S, P>(
    stream: Pin<&mut S>,
    cx: &mut Context<'_>,
    sink: &mut P,
    max: usize,
) -> Poll<io::Result<usize>>
where
    S: AsyncRead + ?Sized,
    P: ParserSink,
{
    let spare = sink.spare();
    let cap = spare.len().min(max);
    let mut tmp_buf = ReadBuf::new(&mut spare[..cap]);
    match stream.poll_read(cx, &mut tmp_buf) {
        Poll::Ready(Ok(())) => {
            let n = tmp_buf.filled().len();
            if n > 0 {
                sink.filled(n);
            }
            Poll::Ready(Ok(n))
        }
        Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
        Poll::Pending => Poll::Pending,
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::future::poll_fn;

    /// `ParserSink` whose spare is configurable for the precondition tests.
    struct StubSink {
        buf: Vec<u8>,
        committed: usize,
    }

    impl StubSink {
        fn with_capacity(cap: usize) -> Self {
            Self {
                buf: vec![0u8; cap],
                committed: 0,
            }
        }
    }

    impl ParserSink for StubSink {
        fn spare(&mut self) -> &mut [u8] {
            &mut self.buf[self.committed..]
        }
        fn filled(&mut self, n: usize) {
            self.committed += n;
        }
    }

    /// Stream stub that panics if polled — proves the precondition
    /// error fires before any I/O is attempted.
    struct UnpolledStream;

    impl AsyncRead for UnpolledStream {
        fn poll_read(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            _buf: &mut ReadBuf<'_>,
        ) -> Poll<io::Result<()>> {
            panic!("UnpolledStream::poll_read should not be reached")
        }
    }

    impl AsyncWrite for UnpolledStream {
        fn poll_write(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            _buf: &[u8],
        ) -> Poll<io::Result<usize>> {
            panic!("unreached")
        }
        fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            panic!("unreached")
        }
        fn poll_shutdown(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            panic!("unreached")
        }
    }

    /// Drive a future to completion via a noop waker — the precondition
    /// error is synchronous so no real runtime is needed.
    fn block_on<F: std::future::Future>(f: F) -> F::Output {
        use std::task::{RawWaker, RawWakerVTable, Waker};
        fn noop(_: *const ()) {}
        fn noop_clone(p: *const ()) -> RawWaker {
            RawWaker::new(p, &VTABLE)
        }
        const VTABLE: RawWakerVTable = RawWakerVTable::new(noop_clone, noop, noop, noop);
        // SAFETY: The vtable functions (clone/wake/wake_by_ref/drop) are all no-ops
        // that never dereference the data pointer, so the null data pointer is sound.
        // The vtable is 'static (const) and correctly returns a valid RawWaker on clone.
        let waker = unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) };
        let mut cx = Context::from_waker(&waker);
        let mut f = std::pin::pin!(f);
        match f.as_mut().poll(&mut cx) {
            Poll::Ready(v) => v,
            Poll::Pending => panic!("precondition error must be synchronous"),
        }
    }

    /// Empty-spare precondition fires before the stream is polled.
    #[test]
    fn tokio_adapter_empty_spare_returns_invalid_input() {
        let mut adapter = AsyncReadAdapter::new(UnpolledStream);
        let mut sink = StubSink::with_capacity(0);
        let err = block_on(poll_fn(|cx| {
            Pin::new(&mut adapter).poll_fill_into(cx, &mut sink, 8192)
        }))
        .expect_err("must error on empty sink");
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    }

    /// `max == 0` precondition fires before the stream is polled.
    #[test]
    fn tokio_adapter_max_zero_returns_invalid_input() {
        let mut adapter = AsyncReadAdapter::new(UnpolledStream);
        let mut sink = StubSink::with_capacity(64);
        let err = block_on(poll_fn(|cx| {
            Pin::new(&mut adapter).poll_fill_into(cx, &mut sink, 0)
        }))
        .expect_err("must error on max == 0");
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    }
}
