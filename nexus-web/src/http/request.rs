#![allow(dead_code)] // Internal module — some methods kept for completeness.

use super::error::HttpError;
use nexus_net::buf::ReadBuf;

/// A parsed HTTP/1.x request. Borrows from the reader's buffer.
pub struct Request<'a> {
    /// HTTP method (GET, POST, etc.).
    pub method: &'a str,
    /// Request path.
    pub path: &'a str,
    /// HTTP version (0 = HTTP/1.0, 1 = HTTP/1.1).
    pub version: u8,
    data: &'a [u8],
    header_offsets: &'a [(usize, usize, usize, usize)], // (name_start, name_len, val_start, val_len)
}

impl<'a> Request<'a> {
    /// Look up a header value by name (case-insensitive).
    ///
    /// Returns `None` if the header is not found or if the value is not valid UTF-8.
    /// Use [`header_bytes`](Self::header_bytes) for raw access to non-UTF-8 values.
    pub fn header(&self, name: &str) -> Option<&'a str> {
        for &(ns, nl, vs, vl) in self.header_offsets {
            let hname = &self.data[ns..ns + nl];
            if hname.eq_ignore_ascii_case(name.as_bytes()) {
                return std::str::from_utf8(&self.data[vs..vs + vl]).ok();
            }
        }
        None
    }

    /// Look up a raw header value by name (case-insensitive).
    ///
    /// Returns the value as raw bytes without UTF-8 validation.
    pub fn header_bytes(&self, name: &str) -> Option<&'a [u8]> {
        for &(ns, nl, vs, vl) in self.header_offsets {
            let hname = &self.data[ns..ns + nl];
            if hname.eq_ignore_ascii_case(name.as_bytes()) {
                return Some(&self.data[vs..vs + vl]);
            }
        }
        None
    }

    /// Iterate over headers as (name, value) pairs.
    ///
    /// Skips headers with non-UTF-8 names or values.
    /// Use [`header_count`](Self::header_count) for the total count including non-UTF-8.
    pub fn headers(&self) -> impl Iterator<Item = (&'a str, &'a str)> {
        self.header_offsets.iter().filter_map(|&(ns, nl, vs, vl)| {
            let name = std::str::from_utf8(&self.data[ns..ns + nl]).ok()?;
            let value = std::str::from_utf8(&self.data[vs..vs + vl]).ok()?;
            Some((name, value))
        })
    }

    /// Number of parsed headers (including non-UTF-8).
    pub fn header_count(&self) -> usize {
        self.header_offsets.len()
    }
}

impl std::fmt::Debug for Request<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Request")
            .field("method", &self.method)
            .field("path", &self.path)
            .field("version", &self.version)
            .field("headers", &self.header_count())
            .finish()
    }
}

/// Sans-IO HTTP/1.x request parser.
///
/// # Usage
///
/// ```
/// use nexus_web::http::RequestReader;
///
/// let mut reader = RequestReader::new(4096);
/// reader.read(b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n").unwrap();
/// let req = reader.next().unwrap().unwrap();
/// assert_eq!(req.method, "GET");
/// assert_eq!(req.path, "/");
/// assert_eq!(req.header("Host"), Some("example.com"));
/// ```
pub struct RequestReader {
    buf: ReadBuf,
    max_headers: usize,
    max_head_size: usize,
    head_len: Option<usize>,
    // Stored after parsing: (name_start, name_len, val_start, val_len) relative to buf.data()
    header_offsets: Vec<(usize, usize, usize, usize)>,
    method_end: usize,
    path_start: usize,
    path_end: usize,
    version: u8,
}

impl RequestReader {
    /// Create with the given buffer capacity.
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        Self {
            buf: ReadBuf::with_capacity(capacity),
            max_headers: 64,
            max_head_size: 8192,
            head_len: None,
            header_offsets: Vec::new(),
            method_end: 0,
            path_start: 0,
            path_end: 0,
            version: 1,
        }
    }

    /// Set maximum number of headers. Default: 64.
    #[must_use]
    pub fn max_headers(mut self, n: usize) -> Self {
        self.max_headers = n;
        self
    }

    /// Set maximum head size. Default: 8KB.
    ///
    /// Once the head terminator is seen, the head must fit in `n` bytes.
    /// Until then, every buffered byte counts against `n`, bounding a peer
    /// that never sends one.
    #[must_use]
    pub fn max_head_size(mut self, n: usize) -> Self {
        self.max_head_size = n;
        self
    }

    /// Writable region for direct in-buffer writes. Pair with
    /// [`filled()`](Self::filled) to commit bytes after the write.
    /// Used by [`crate::WireStream`] to deliver bytes from a transport
    /// without a slice intermediate.
    #[inline]
    pub fn spare(&mut self) -> &mut [u8] {
        self.buf.spare()
    }

    /// Commit `n` bytes written into [`spare()`](Self::spare).
    #[inline]
    pub fn filled(&mut self, n: usize) {
        self.buf.filled(n);
    }

    /// Buffer wire bytes.
    pub fn read(&mut self, src: &[u8]) -> Result<(), HttpError> {
        let spare = self.buf.spare();
        if src.len() > spare.len() {
            return Err(HttpError::BufferFull {
                needed: src.len(),
                available: spare.len(),
            });
        }
        spare[..src.len()].copy_from_slice(src);
        self.buf.filled(src.len());
        Ok(())
    }

    /// Parse the next request.
    ///
    /// Returns `Ok(Some(request))` when the head is complete.
    /// Returns `Ok(None)` if more bytes are needed.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Option<Request<'_>>, HttpError> {
        if self.head_len.is_none() {
            self.try_parse()?;
        }

        if self.head_len.is_none() {
            return Ok(None);
        }

        let data = self.buf.data();
        let method = std::str::from_utf8(&data[..self.method_end])
            .map_err(|_| HttpError::Malformed("invalid UTF-8 in method"))?;
        let path = std::str::from_utf8(&data[self.path_start..self.path_end])
            .map_err(|_| HttpError::Malformed("invalid UTF-8 in path"))?;

        Ok(Some(Request {
            method,
            path,
            version: self.version,
            data,
            header_offsets: &self.header_offsets,
        }))
    }

    /// Bytes after the parsed head.
    pub fn remainder(&self) -> &[u8] {
        match self.head_len {
            Some(n) => &self.buf.data()[n..],
            None => &[],
        }
    }

    /// Reset for a new request.
    pub fn reset(&mut self) {
        self.buf.clear();
        self.head_len = None;
        self.header_offsets.clear();
    }

    fn try_parse(&mut self) -> Result<(), HttpError> {
        let data = self.buf.data();
        if data.is_empty() {
            return Ok(());
        }

        // Stack-allocate for the common case (≤ 64 headers).
        // Fall back to heap for larger max_headers configurations.
        let mut stack_headers = [httparse::EMPTY_HEADER; 64];
        let mut heap_headers;
        let headers: &mut [httparse::Header<'_>] = if self.max_headers <= 64 {
            &mut stack_headers[..self.max_headers]
        } else {
            heap_headers = vec![httparse::EMPTY_HEADER; self.max_headers];
            &mut heap_headers
        };
        let mut req = httparse::Request::new(headers);

        match req.parse(data) {
            Ok(httparse::Status::Complete(head_len)) => {
                if head_len > self.max_head_size {
                    return Err(HttpError::HeadTooLarge {
                        max: self.max_head_size,
                    });
                }
                let method = req
                    .method
                    .ok_or(HttpError::Malformed("missing request method"))?;
                let path = req
                    .path
                    .ok_or(HttpError::Malformed("missing request path"))?;
                let version = req
                    .version
                    .ok_or(HttpError::Malformed("missing HTTP version"))?;

                let data_ptr = data.as_ptr();
                self.method_end = method.len();
                // SAFETY: path and data_ptr point within the same allocation
                // (self.buf's backing Vec). offset_from is valid and non-negative.
                self.path_start = unsafe { path.as_ptr().offset_from(data_ptr) } as usize;
                self.path_end = self.path_start + path.len();
                self.version = version;

                self.header_offsets.clear();
                for h in req.headers.iter() {
                    // SAFETY: header name/value pointers are within data (same allocation).
                    let ns = unsafe { h.name.as_ptr().offset_from(data_ptr) } as usize;
                    let nl = h.name.len();
                    // SAFETY: header value pointer is within data (same allocation as data_ptr).
                    let vs = unsafe { h.value.as_ptr().offset_from(data_ptr) } as usize;
                    let vl = h.value.len();
                    self.header_offsets.push((ns, nl, vs, vl));
                }

                self.head_len = Some(head_len);
                Ok(())
            }
            Ok(httparse::Status::Partial) => {
                if data.len() > self.max_head_size {
                    return Err(HttpError::HeadTooLarge {
                        max: self.max_head_size,
                    });
                }
                Ok(())
            }
            Err(httparse::Error::TooManyHeaders) => Err(HttpError::TooManyHeaders),
            Err(_) => Err(HttpError::Malformed("httparse rejected request")),
        }
    }
}

/// Lets a [`WireStream`](crate::WireStream) feed bytes directly into
/// the RequestReader's spare region — one fewer copy than going
/// through a slice intermediary.
impl crate::ParserSink for RequestReader {
    #[inline]
    fn spare(&mut self) -> &mut [u8] {
        RequestReader::spare(self)
    }

    #[inline]
    fn filled(&mut self, n: usize) {
        RequestReader::filled(self, n);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_get() {
        let mut r = RequestReader::new(4096);
        r.read(b"GET /path HTTP/1.1\r\nHost: example.com\r\n\r\n")
            .unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.method, "GET");
        assert_eq!(req.path, "/path");
        assert_eq!(req.version, 1);
        assert_eq!(req.header("Host"), Some("example.com"));
    }

    #[test]
    fn multiple_headers() {
        let mut r = RequestReader::new(4096);
        r.read(b"POST /api HTTP/1.1\r\nHost: a.com\r\nContent-Type: application/json\r\nX-Custom: value\r\n\r\n").unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.method, "POST");
        assert_eq!(req.header("Content-Type"), Some("application/json"));
        assert_eq!(req.header("x-custom"), Some("value")); // case-insensitive
        assert_eq!(req.header_count(), 3);
    }

    #[test]
    fn partial_then_complete() {
        let mut r = RequestReader::new(4096);
        r.read(b"GET / HTTP/1.1\r\nHost: ex").unwrap();
        assert!(r.next().unwrap().is_none());
        r.read(b"ample.com\r\n\r\n").unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.header("Host"), Some("example.com"));
    }

    #[test]
    fn remainder_after_head() {
        let mut r = RequestReader::new(4096);
        r.read(b"GET / HTTP/1.1\r\nHost: a.com\r\n\r\nextra bytes")
            .unwrap();
        let _req = r.next().unwrap().unwrap();
        assert_eq!(r.remainder(), b"extra bytes");
    }

    #[test]
    fn head_too_large() {
        let mut r = RequestReader::new(4096).max_head_size(32);
        r.read(b"GET / HTTP/1.1\r\nHost: a-very-long-hostname.example.com\r\n\r\n")
            .unwrap();
        assert!(matches!(r.next(), Err(HttpError::HeadTooLarge { .. })));
    }

    // 27-byte head, max_head_size=80.  head(27) fits; head+body(127) previously did not.
    const REQ_HEAD: &[u8] = b"GET / HTTP/1.1\r\nHost: a\r\n\r\n";

    #[test]
    fn split_read_one_chunk() {
        let body = vec![b'x'; 100];
        let mut buf = REQ_HEAD.to_vec();
        buf.extend_from_slice(&body);
        let mut r = RequestReader::new(4096).max_head_size(80);
        r.read(&buf).unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.method, "GET");
        assert_eq!(r.remainder(), body.as_slice());
    }

    #[test]
    fn split_read_two_chunks() {
        let body = vec![b'x'; 100];
        let mut r = RequestReader::new(4096).max_head_size(80);
        r.read(REQ_HEAD).unwrap();
        r.read(&body).unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.method, "GET");
        assert_eq!(r.remainder(), body.as_slice());
    }

    #[test]
    fn split_read_byte_by_byte() {
        let body = vec![b'x'; 100];
        let mut r = RequestReader::new(4096).max_head_size(80);
        for &b in REQ_HEAD.iter().chain(body.iter()) {
            r.read(&[b]).unwrap();
        }
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.method, "GET");
        assert_eq!(r.remainder(), body.as_slice());
    }

    #[test]
    fn complete_head_over_limit() {
        let mut r = RequestReader::new(4096).max_head_size(40);
        r.read(b"GET / HTTP/1.1\r\nHost: a-very-long-hostname.example.com\r\n\r\n")
            .unwrap();
        assert!(matches!(r.next(), Err(HttpError::HeadTooLarge { .. })));
    }

    #[test]
    fn partial_head_over_limit() {
        const MAX: usize = 40;
        let mut partial = b"GET / HTTP/1.1\r\nHost: ".to_vec();
        let fill = MAX + 1 - partial.len();
        partial.extend_from_slice(&vec![b'a'; fill]);
        assert_eq!(partial.len(), MAX + 1);
        let mut r = RequestReader::new(4096).max_head_size(MAX);
        r.read(&partial).unwrap();
        assert!(matches!(r.next(), Err(HttpError::HeadTooLarge { .. })));
    }

    #[test]
    fn exact_head_size_boundary() {
        // "GET / HTTP/1.1\r\nHost: " = 22 bytes, "\r\n\r\n" = 4 bytes -> pad = MAX - 26
        const MAX: usize = 50;
        let pad = MAX - 26;
        let mut exact = b"GET / HTTP/1.1\r\nHost: ".to_vec();
        exact.extend_from_slice(&vec![b'a'; pad]);
        exact.extend_from_slice(b"\r\n\r\n");
        assert_eq!(exact.len(), MAX);
        let mut r = RequestReader::new(4096).max_head_size(MAX);
        r.read(&exact).unwrap();
        assert!(r.next().unwrap().is_some());

        let mut over = b"GET / HTTP/1.1\r\nHost: ".to_vec();
        over.extend_from_slice(&vec![b'a'; pad + 1]);
        over.extend_from_slice(b"\r\n\r\n");
        assert_eq!(over.len(), MAX + 1);
        let mut r2 = RequestReader::new(4096).max_head_size(MAX);
        r2.read(&over).unwrap();
        assert!(matches!(r2.next(), Err(HttpError::HeadTooLarge { .. })));
    }

    #[test]
    fn malformed_request() {
        let mut r = RequestReader::new(4096);
        r.read(b"NOT_HTTP\r\n\r\n").unwrap();
        assert!(matches!(r.next(), Err(HttpError::Malformed(_))));
    }

    #[test]
    fn buffer_full() {
        let mut r = RequestReader::new(16);
        let err = r
            .read(b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n")
            .unwrap_err();
        assert!(matches!(err, HttpError::BufferFull { .. }));
    }

    #[test]
    fn ws_upgrade_request() {
        let mut r = RequestReader::new(4096);
        r.read(
            b"GET /ws HTTP/1.1\r\n\
                  Host: localhost:8080\r\n\
                  Upgrade: websocket\r\n\
                  Connection: Upgrade\r\n\
                  Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\
                  Sec-WebSocket-Version: 13\r\n\
                  \r\n",
        )
        .unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.method, "GET");
        assert_eq!(req.path, "/ws");
        assert_eq!(req.header("Upgrade"), Some("websocket"));
        assert_eq!(req.header("Connection"), Some("Upgrade"));
        assert_eq!(
            req.header("Sec-WebSocket-Key"),
            Some("dGhlIHNhbXBsZSBub25jZQ==")
        );
        assert_eq!(req.header("Sec-WebSocket-Version"), Some("13"));
    }

    #[test]
    fn reset_then_reuse() {
        let mut r = RequestReader::new(4096);
        r.read(b"GET /a HTTP/1.1\r\nHost: a\r\n\r\n").unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.path, "/a");
        // Ensure req is consumed before reset
        let _ = req;

        r.reset();
        r.read(b"GET /b HTTP/1.1\r\nHost: b\r\n\r\n").unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.path, "/b");
    }

    #[test]
    fn header_iter() {
        let mut r = RequestReader::new(4096);
        r.read(b"GET / HTTP/1.1\r\nA: 1\r\nB: 2\r\n\r\n").unwrap();
        let req = r.next().unwrap().unwrap();
        let hdrs: Vec<_> = req.headers().collect();
        assert_eq!(hdrs.len(), 2);
        assert_eq!(hdrs[0], ("A", "1"));
        assert_eq!(hdrs[1], ("B", "2"));
    }
}
