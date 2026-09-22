use super::error::HttpError;
use nexus_net::buf::ReadBuf;

/// A parsed HTTP/1.x response. Borrows from the reader's buffer.
pub struct Response<'a> {
    /// HTTP status code (e.g., 101, 200, 404).
    pub status: u16,
    /// Reason phrase (e.g., "Switching Protocols", "OK").
    pub reason: &'a str,
    /// HTTP version (0 = HTTP/1.0, 1 = HTTP/1.1).
    pub version: u8,
    data: &'a [u8],
    header_offsets: &'a [(usize, usize, usize, usize)],
}

impl<'a> Response<'a> {
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

impl std::fmt::Debug for Response<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Response")
            .field("status", &self.status)
            .field("reason", &self.reason)
            .field("version", &self.version)
            .field("headers", &self.header_count())
            .finish()
    }
}

/// Sans-IO HTTP/1.x response parser.
///
/// # Usage
///
/// ```
/// use nexus_web::http::ResponseReader;
///
/// let mut reader = ResponseReader::new(4096);
/// reader.read(b"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\n\r\n").unwrap();
/// let resp = reader.next().unwrap().unwrap();
/// assert_eq!(resp.status, 101);
/// assert_eq!(resp.header("Upgrade"), Some("websocket"));
/// ```
pub struct ResponseReader {
    buf: ReadBuf,
    max_headers: usize,
    max_head_size: usize,
    max_body_size: usize,
    head_len: Option<usize>,
    header_offsets: Vec<(usize, usize, usize, usize)>,
    status: u16,
    reason_start: usize,
    reason_end: usize,
    version: u8,
    // Cached during try_parse to avoid post-parse header scans.
    cached_content_length: Option<Result<usize, ()>>,
    cached_is_chunked: bool,
    /// Raw wire bytes consumed for the last response body.
    /// Used by `consume_response` to advance past the correct number of bytes.
    last_raw_body_bytes: usize,
}

impl ResponseReader {
    /// Create with the given buffer capacity.
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        Self {
            buf: ReadBuf::with_capacity(capacity),
            max_headers: 64,
            max_head_size: 8192,
            max_body_size: 0,
            head_len: None,
            header_offsets: Vec::with_capacity(16),
            status: 0,
            reason_start: 0,
            reason_end: 0,
            version: 1,
            cached_content_length: None,
            cached_is_chunked: false,
            last_raw_body_bytes: 0,
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

    /// Set maximum response body size. Default: 0 (no limit).
    ///
    /// When set, responses with Content-Length exceeding this value
    /// will be rejected during validation.
    #[must_use]
    pub fn max_body_size(mut self, n: usize) -> Self {
        self.max_body_size = n;
        self
    }

    /// Configured maximum body size (0 = no limit).
    pub fn max_body_size_limit(&self) -> usize {
        self.max_body_size
    }

    /// Buffer wire bytes.
    pub fn read(&mut self, src: &[u8]) -> Result<(), HttpError> {
        let spare = self.buf.spare();
        if src.len() > spare.len() {
            self.buf.compact();
            let spare = self.buf.spare();
            if src.len() > spare.len() {
                return Err(HttpError::BufferFull {
                    needed: src.len(),
                    available: spare.len(),
                });
            }
        }
        let spare = self.buf.spare();
        spare[..src.len()].copy_from_slice(src);
        self.buf.filled(src.len());
        Ok(())
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

    /// Read bytes from a source directly into the internal buffer.
    ///
    /// Returns bytes read, or 0 on EOF.
    pub fn read_from<R: std::io::Read>(&mut self, src: &mut R) -> std::io::Result<usize> {
        let spare = self.buf.spare();
        if spare.is_empty() {
            self.buf.compact();
        }
        let spare = self.buf.spare();
        if spare.is_empty() {
            return Err(std::io::Error::other("response buffer full"));
        }
        let n = src.read(spare)?;
        self.buf.filled(n);
        Ok(n)
    }

    /// Bytes of data buffered beyond the parsed headers (body bytes).
    /// Available after `next()` returns `Some`.
    pub fn body_remaining(&self) -> usize {
        self.head_len
            .map_or(0, |n| self.buf.data().len().saturating_sub(n))
    }

    /// Look up a parsed response header by name (case-insensitive).
    ///
    /// Returns `None` if headers haven't been parsed yet or the header
    /// is not found. Only valid after `next()` returns `Some`.
    pub fn header(&self, name: &str) -> Option<&str> {
        self.head_len?;
        let data = self.buf.data();
        for &(ns, nl, vs, vl) in &self.header_offsets {
            if data[ns..ns + nl].eq_ignore_ascii_case(name.as_bytes()) {
                return std::str::from_utf8(&data[vs..vs + vl]).ok();
            }
        }
        None
    }

    /// Parse the next response.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Option<Response<'_>>, HttpError> {
        if self.head_len.is_none() {
            self.try_parse()?;
        }

        if self.head_len.is_none() {
            return Ok(None);
        }

        let data = self.buf.data();
        if self.reason_end > data.len() || self.reason_start > self.reason_end {
            return Err(HttpError::Malformed("reason phrase out of bounds"));
        }
        let reason = std::str::from_utf8(&data[self.reason_start..self.reason_end])
            .map_err(|_| HttpError::Malformed("invalid UTF-8 in reason phrase"))?;

        Ok(Some(Response {
            status: self.status,
            reason,
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

    /// HTTP status code from parsed headers.
    pub fn status(&self) -> u16 {
        self.status
    }

    /// Number of parsed headers.
    pub fn header_count(&self) -> usize {
        self.header_offsets.len()
    }

    /// Cached Content-Length from parsed headers.
    /// `None` = header absent, `Some(Ok(n))` = valid, `Some(Err(()))` = present but malformed.
    pub fn content_length(&self) -> Option<Result<usize, ()>> {
        self.cached_content_length
    }

    /// Whether Transfer-Encoding includes "chunked" (cached from parse).
    pub fn is_chunked(&self) -> bool {
        self.cached_is_chunked
    }

    /// Set the raw wire bytes consumed for the response body.
    ///
    /// For Content-Length responses: equals Content-Length.
    /// For chunked responses: includes chunk framing overhead.
    /// For bodyless (1xx/204/304): 0.
    ///
    /// Must be called before `consume_response()`.
    pub fn set_body_consumed(&mut self, raw_bytes: usize) {
        self.last_raw_body_bytes = raw_bytes;
    }

    /// Advance past a consumed response, preserving any pipelined bytes.
    ///
    /// Uses `last_raw_body_bytes` (set via [`set_body_consumed`](Self::set_body_consumed)) to
    /// determine how many wire bytes to skip. Call before parsing the
    /// next response on a keep-alive connection.
    pub fn consume_response(&mut self) {
        if let Some(head_len) = self.head_len {
            let consumed = head_len + self.last_raw_body_bytes;
            if consumed <= self.buf.data().len() {
                self.buf.advance(consumed);
            } else {
                self.buf.clear();
            }
        }
        self.head_len = None;
        self.header_offsets.clear();
        self.cached_content_length = None;
        self.cached_is_chunked = false;
        self.last_raw_body_bytes = 0;
    }

    /// Reset for a new response. Discards all buffered data.
    pub fn reset(&mut self) {
        self.buf.clear();
        self.head_len = None;
        self.header_offsets.clear();
        self.cached_content_length = None;
        self.cached_is_chunked = false;
        self.last_raw_body_bytes = 0;
    }

    fn try_parse(&mut self) -> Result<(), HttpError> {
        let data = self.buf.data();
        if data.is_empty() {
            return Ok(());
        }

        let mut stack_headers = [httparse::EMPTY_HEADER; 64];
        let mut heap_headers;
        let headers: &mut [httparse::Header<'_>] = if self.max_headers <= 64 {
            &mut stack_headers[..self.max_headers]
        } else {
            heap_headers = vec![httparse::EMPTY_HEADER; self.max_headers];
            &mut heap_headers
        };
        let mut resp = httparse::Response::new(headers);

        match resp.parse(data) {
            Ok(httparse::Status::Complete(head_len)) => {
                if head_len > self.max_head_size {
                    return Err(HttpError::HeadTooLarge {
                        max: self.max_head_size,
                    });
                }
                let status = resp
                    .code
                    .ok_or(HttpError::Malformed("missing status code"))?;
                let reason = resp
                    .reason
                    .ok_or(HttpError::Malformed("missing reason phrase"))?;
                let version = resp
                    .version
                    .ok_or(HttpError::Malformed("missing HTTP version"))?;

                let data_ptr = data.as_ptr();
                self.status = status;
                // SAFETY: reason ptr is within data (same allocation).
                self.reason_start = unsafe { reason.as_ptr().offset_from(data_ptr) } as usize;
                self.reason_end = self.reason_start + reason.len();
                self.version = version;

                self.header_offsets.clear();
                self.cached_content_length = None;
                self.cached_is_chunked = false;

                for h in resp.headers.iter() {
                    // SAFETY: header name/value pointers are within data (same allocation).
                    let ns = unsafe { h.name.as_ptr().offset_from(data_ptr) } as usize;
                    let nl = h.name.len();
                    // SAFETY: header value pointer is within data (same allocation as data_ptr).
                    let vs = unsafe { h.value.as_ptr().offset_from(data_ptr) } as usize;
                    let vl = h.value.len();
                    debug_assert!(ns + nl <= data.len(), "header name offset out of bounds");
                    debug_assert!(vs + vl <= data.len(), "header value offset out of bounds");
                    self.header_offsets.push((ns, nl, vs, vl));

                    // Cache Content-Length and Transfer-Encoding during parse
                    // to avoid post-parse linear scans.
                    if h.name.eq_ignore_ascii_case("Content-Length") {
                        self.cached_content_length = Some(
                            std::str::from_utf8(h.value)
                                .ok()
                                .and_then(|v| v.trim().parse::<usize>().ok())
                                .ok_or(()),
                        );
                    } else if h.name.eq_ignore_ascii_case("Transfer-Encoding")
                        && let Ok(te) = std::str::from_utf8(h.value)
                    {
                        self.cached_is_chunked = te
                            .split(',')
                            .any(|t| t.trim().eq_ignore_ascii_case("chunked"));
                    }
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
            Err(_) => Err(HttpError::Malformed("httparse rejected response")),
        }
    }
}

/// Lets a [`WireStream`](crate::WireStream) feed bytes directly into
/// the ResponseReader's spare region — one fewer copy than going
/// through a slice intermediary.
impl crate::ParserSink for ResponseReader {
    #[inline]
    fn spare(&mut self) -> &mut [u8] {
        ResponseReader::spare(self)
    }

    #[inline]
    fn filled(&mut self, n: usize) {
        ResponseReader::filled(self, n);
    }
}

/// Validate that a header name or value contains no CRLF characters.
fn validate_header_value(s: &str) -> Result<(), super::error::HttpError> {
    if s.bytes().any(|b| b == b'\r' || b == b'\n') {
        return Err(super::error::HttpError::InvalidHeaderValue);
    }
    Ok(())
}

fn copy_to(dst: &mut [u8], offset: usize, src: &[u8]) -> Result<usize, super::error::HttpError> {
    let end = offset + src.len();
    if end > dst.len() {
        return Err(super::error::HttpError::BufferTooSmall {
            needed: end,
            available: dst.len(),
        });
    }
    dst[offset..end].copy_from_slice(src);
    Ok(src.len())
}

fn write_u16(dst: &mut [u8], offset: usize, val: u16) -> Result<usize, super::error::HttpError> {
    debug_assert!(
        val >= 100 && val <= 999,
        "HTTP status must be 3 digits: {val}"
    );
    if offset + 3 > dst.len() {
        return Err(super::error::HttpError::BufferTooSmall {
            needed: offset + 3,
            available: dst.len(),
        });
    }
    dst[offset] = (val / 100) as u8 + b'0';
    dst[offset + 1] = ((val / 10) % 10) as u8 + b'0';
    dst[offset + 2] = (val % 10) as u8 + b'0';
    Ok(3)
}

/// Compute the exact size needed for a request.
#[must_use]
pub fn request_size(method: &str, path: &str, headers: &[(&str, &str)]) -> usize {
    let mut size = method.len() + 1 + path.len() + 11; // " HTTP/1.1\r\n"
    for &(name, value) in headers {
        size += name.len() + 2 + value.len() + 2; // ": " + "\r\n"
    }
    size + 2 // final "\r\n"
}

/// Compute the exact size needed for a response.
#[must_use]
pub fn response_size(reason: &str, headers: &[(&str, &str)]) -> usize {
    let mut size = 9 + 3 + 1 + reason.len() + 2; // "HTTP/1.1 " + status + " " + reason + "\r\n"
    for &(name, value) in headers {
        size += name.len() + 2 + value.len() + 2;
    }
    size + 2
}

/// Write an HTTP/1.1 request into a byte buffer. Returns bytes written.
///
/// Returns `HttpError::BufferTooSmall` if `dst` is undersized.
/// Use [`request_size`] to compute the exact size needed.
pub fn write_request(
    method: &str,
    path: &str,
    headers: &[(&str, &str)],
    dst: &mut [u8],
) -> Result<usize, super::error::HttpError> {
    let mut offset = 0;
    offset += copy_to(dst, offset, method.as_bytes())?;
    offset += copy_to(dst, offset, b" ")?;
    offset += copy_to(dst, offset, path.as_bytes())?;
    offset += copy_to(dst, offset, b" HTTP/1.1\r\n")?;
    for &(name, value) in headers {
        validate_header_value(name)?;
        validate_header_value(value)?;
        offset += copy_to(dst, offset, name.as_bytes())?;
        offset += copy_to(dst, offset, b": ")?;
        offset += copy_to(dst, offset, value.as_bytes())?;
        offset += copy_to(dst, offset, b"\r\n")?;
    }
    offset += copy_to(dst, offset, b"\r\n")?;
    Ok(offset)
}

/// Write an HTTP/1.1 response into a byte buffer. Returns bytes written.
///
/// Returns `HttpError::BufferTooSmall` if `dst` is undersized.
/// Use [`response_size`] to compute the exact size needed.
pub fn write_response(
    status: u16,
    reason: &str,
    headers: &[(&str, &str)],
    dst: &mut [u8],
) -> Result<usize, super::error::HttpError> {
    let mut offset = 0;
    offset += copy_to(dst, offset, b"HTTP/1.1 ")?;
    offset += write_u16(dst, offset, status)?;
    offset += copy_to(dst, offset, b" ")?;
    offset += copy_to(dst, offset, reason.as_bytes())?;
    offset += copy_to(dst, offset, b"\r\n")?;
    for &(name, value) in headers {
        validate_header_value(name)?;
        validate_header_value(value)?;
        offset += copy_to(dst, offset, name.as_bytes())?;
        offset += copy_to(dst, offset, b": ")?;
        offset += copy_to(dst, offset, value.as_bytes())?;
        offset += copy_to(dst, offset, b"\r\n")?;
    }
    offset += copy_to(dst, offset, b"\r\n")?;
    Ok(offset)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_101_response() {
        let mut r = ResponseReader::new(4096);
        r.read(b"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n").unwrap();
        let resp = r.next().unwrap().unwrap();
        assert_eq!(resp.status, 101);
        assert_eq!(resp.reason, "Switching Protocols");
        assert_eq!(resp.version, 1);
        assert_eq!(resp.header("Upgrade"), Some("websocket"));
        assert_eq!(resp.header("Connection"), Some("Upgrade"));
    }

    #[test]
    fn basic_200_response() {
        let mut r = ResponseReader::new(4096);
        r.read(b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nHello")
            .unwrap();
        let resp = r.next().unwrap().unwrap();
        assert_eq!(resp.status, 200);
        assert_eq!(resp.reason, "OK");
        assert_eq!(resp.header("Content-Length"), Some("5"));
    }

    #[test]
    fn response_remainder() {
        let mut r = ResponseReader::new(4096);
        r.read(b"HTTP/1.1 200 OK\r\n\r\nbody data").unwrap();
        let _resp = r.next().unwrap().unwrap();
        assert_eq!(r.remainder(), b"body data");
    }

    #[test]
    fn partial_response() {
        let mut r = ResponseReader::new(4096);
        r.read(b"HTTP/1.1 200 OK\r\nHost: ").unwrap();
        assert!(r.next().unwrap().is_none());
        r.read(b"example.com\r\n\r\n").unwrap();
        let resp = r.next().unwrap().unwrap();
        assert_eq!(resp.status, 200);
        assert_eq!(resp.header("Host"), Some("example.com"));
    }

    #[test]
    fn write_request_round_trip() {
        use crate::http::RequestReader;
        let mut dst = [0u8; 256];
        let n = write_request(
            "GET",
            "/ws",
            &[("Host", "localhost:8080"), ("Upgrade", "websocket")],
            &mut dst,
        )
        .unwrap();

        let mut r = RequestReader::new(4096);
        r.read(&dst[..n]).unwrap();
        let req = r.next().unwrap().unwrap();
        assert_eq!(req.method, "GET");
        assert_eq!(req.path, "/ws");
        assert_eq!(req.header("Upgrade"), Some("websocket"));
    }

    #[test]
    fn write_response_round_trip() {
        let mut dst = [0u8; 256];
        let n = write_response(
            101,
            "Switching Protocols",
            &[("Upgrade", "websocket"), ("Connection", "Upgrade")],
            &mut dst,
        )
        .unwrap();

        let mut r = ResponseReader::new(4096);
        r.read(&dst[..n]).unwrap();
        let resp = r.next().unwrap().unwrap();
        assert_eq!(resp.status, 101);
        assert_eq!(resp.header("Connection"), Some("Upgrade"));
    }

    #[test]
    fn reset_then_reuse() {
        let mut r = ResponseReader::new(4096);
        r.read(b"HTTP/1.1 200 OK\r\n\r\n").unwrap();
        let _ = r.next().unwrap().unwrap();
        r.reset();
        r.read(b"HTTP/1.1 404 Not Found\r\n\r\n").unwrap();
        let resp = r.next().unwrap().unwrap();
        assert_eq!(resp.status, 404);
    }

    // 38-byte head, max_head_size=80.  head(38) fits; head+body(138) previously did not.
    const RESP_HEAD: &[u8] = b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n";

    #[test]
    fn split_read_one_chunk() {
        let body = vec![b'x'; 100];
        let mut buf = RESP_HEAD.to_vec();
        buf.extend_from_slice(&body);
        let mut r = ResponseReader::new(4096).max_head_size(80);
        r.read(&buf).unwrap();
        let resp = r.next().unwrap().unwrap();
        assert_eq!(resp.status, 200);
        assert_eq!(r.remainder(), body.as_slice());
    }

    #[test]
    fn split_read_two_chunks() {
        let body = vec![b'x'; 100];
        let mut r = ResponseReader::new(4096).max_head_size(80);
        r.read(RESP_HEAD).unwrap();
        r.read(&body).unwrap();
        let resp = r.next().unwrap().unwrap();
        assert_eq!(resp.status, 200);
        assert_eq!(r.remainder(), body.as_slice());
    }

    #[test]
    fn split_read_byte_by_byte() {
        let body = vec![b'x'; 100];
        let mut r = ResponseReader::new(4096).max_head_size(80);
        for &b in RESP_HEAD.iter().chain(body.iter()) {
            r.read(&[b]).unwrap();
        }
        let resp = r.next().unwrap().unwrap();
        assert_eq!(resp.status, 200);
        assert_eq!(r.remainder(), body.as_slice());
    }

    #[test]
    fn complete_head_over_limit() {
        let mut r = ResponseReader::new(4096).max_head_size(40);
        r.read(b"HTTP/1.1 200 OK\r\nServer: a-very-long-server-name.example.com\r\n\r\n")
            .unwrap();
        assert!(matches!(r.next(), Err(HttpError::HeadTooLarge { .. })));
    }

    #[test]
    fn partial_head_over_limit() {
        const MAX: usize = 40;
        let mut partial = b"HTTP/1.1 200 OK\r\nServer: ".to_vec();
        let fill = MAX + 1 - partial.len();
        partial.extend_from_slice(&vec![b'a'; fill]);
        assert_eq!(partial.len(), MAX + 1);
        let mut r = ResponseReader::new(4096).max_head_size(MAX);
        r.read(&partial).unwrap();
        assert!(matches!(r.next(), Err(HttpError::HeadTooLarge { .. })));
    }

    #[test]
    fn exact_head_size_boundary() {
        // "HTTP/1.1 200 OK\r\nA: " = 20 bytes, "\r\n\r\n" = 4 bytes -> pad = MAX - 24
        const MAX: usize = 50;
        let pad = MAX - 24;
        let mut exact = b"HTTP/1.1 200 OK\r\nA: ".to_vec();
        exact.extend_from_slice(&vec![b'a'; pad]);
        exact.extend_from_slice(b"\r\n\r\n");
        assert_eq!(exact.len(), MAX);
        let mut r = ResponseReader::new(4096).max_head_size(MAX);
        r.read(&exact).unwrap();
        assert!(r.next().unwrap().is_some());

        let mut over = b"HTTP/1.1 200 OK\r\nA: ".to_vec();
        over.extend_from_slice(&vec![b'a'; pad + 1]);
        over.extend_from_slice(b"\r\n\r\n");
        assert_eq!(over.len(), MAX + 1);
        let mut r2 = ResponseReader::new(4096).max_head_size(MAX);
        r2.read(&over).unwrap();
        assert!(matches!(r2.next(), Err(HttpError::HeadTooLarge { .. })));
    }
}
