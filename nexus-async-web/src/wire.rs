//! nexus-async-rt [`WireStream`](nexus_net::WireStream) adapter.
//!
//! `WireStream`/`ParserSink` are defined in `nexus-net`. The tokio
//! adapter (`AsyncReadAdapter`) now lives in [`nexus_net::tokio`] and is
//! re-exported at this crate's root. What remains here is the
//! experimental nexus-async-rt adapter, which wraps that runtime's own
//! `AsyncRead+AsyncWrite` trait shape.
//!
//! - [`NexusAsyncReadAdapter`] wraps `nexus_async_rt::AsyncRead+AsyncWrite`
//!   (under `feature = "nexus"`).

use std::io;
use std::pin::Pin;
use std::task::{Context, Poll};

use nexus_net::{ParserSink, WireStream};

// =============================================================================
// Nexus runtime adapter
// =============================================================================

/// Wraps a `nexus_async_rt::AsyncRead + AsyncWrite` source as a
/// [`WireStream`].
///
/// Use this when constructing `WsStream`/`HttpConnection` over a
/// custom transport on the nexus-async-rt backend. The canonical
/// `MaybeTls` path implements `WireStream` directly with a faster
/// zero-copy plaintext path; this adapter is the slow-path equivalent
/// for arbitrary transports.
///
/// ```ignore
/// use nexus_async_web::NexusAsyncReadAdapter;
///
/// let adapter = NexusAsyncReadAdapter::new(my_custom_stream);
/// let ws = WsStreamBuilder::new().connect_with(adapter, url).await?;
/// ```
pub struct NexusAsyncReadAdapter<S> {
    inner: S,
}

impl<S> NexusAsyncReadAdapter<S> {
    /// Wrap an inner stream.
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

// SAFETY note: structural pinning of `inner`. We only project
// `Pin<&mut Self> -> Pin<&mut S>` and never move out; `Self` has no
// `Drop` impl that could observe pinned state.
impl<S: nexus_async_rt::AsyncRead + nexus_async_rt::AsyncWrite + Unpin> WireStream
    for NexusAsyncReadAdapter<S>
{
    fn poll_fill_into<P: ParserSink>(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        sink: &mut P,
        max: usize,
    ) -> Poll<io::Result<usize>> {
        let this = self.get_mut();
        let spare = sink.spare();
        if max == 0 || spare.is_empty() {
            return Poll::Ready(Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "poll_fill_into called with no buffer space \
                 (max == 0 or sink.spare() is empty)",
            )));
        }
        let cap = spare.len().min(max);
        match Pin::new(&mut this.inner).poll_read(cx, &mut spare[..cap]) {
            Poll::Ready(Ok(n)) => {
                if n > 0 {
                    sink.filled(n);
                }
                Poll::Ready(Ok(n))
            }
            Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
            Poll::Pending => Poll::Pending,
        }
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

    impl nexus_async_rt::AsyncRead for UnpolledStream {
        fn poll_read(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            _buf: &mut [u8],
        ) -> Poll<io::Result<usize>> {
            panic!("UnpolledStream::poll_read should not be reached")
        }
    }

    impl nexus_async_rt::AsyncWrite for UnpolledStream {
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
    fn nexus_adapter_empty_spare_returns_invalid_input() {
        let mut adapter = NexusAsyncReadAdapter::new(UnpolledStream);
        let mut sink = StubSink::with_capacity(0);
        let err = block_on(poll_fn(|cx| {
            Pin::new(&mut adapter).poll_fill_into(cx, &mut sink, 8192)
        }))
        .expect_err("must error on empty sink");
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    }

    /// `max == 0` precondition fires before the stream is polled.
    #[test]
    fn nexus_adapter_max_zero_returns_invalid_input() {
        let mut adapter = NexusAsyncReadAdapter::new(UnpolledStream);
        let mut sink = StubSink::with_capacity(64);
        let err = block_on(poll_fn(|cx| {
            Pin::new(&mut adapter).poll_fill_into(cx, &mut sink, 0)
        }))
        .expect_err("must error on max == 0");
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    }
}
