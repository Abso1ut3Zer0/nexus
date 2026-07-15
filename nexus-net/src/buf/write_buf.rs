/// Flat byte slab for outbound protocol frames.
///
/// sk_buff headroom model: payload is appended at the tail, protocol
/// headers are prepended into reserved headroom. The result is one
/// contiguous [`data()`](WriteBuf::data) slice for the write syscall.
///
/// Fixed capacity. No growth.
///
/// # Layout
///
/// ```text
/// [ headroom          | payload data         | tailroom    ]
/// ^                   ^                      ^             ^
/// 0                   head                   tail          buf.len()
/// ```
///
/// After [`clear()`](WriteBuf::clear): `head = headroom`, `tail = headroom`.
///
/// # Modes
///
/// **One-shot message** (sk_buff style):
/// [`prepend()`](WriteBuf::prepend) / [`append()`](WriteBuf::append) to
/// build a single frame, [`data()`](WriteBuf::data) to send,
/// [`clear()`](WriteBuf::clear) between frames. This is what most
/// protocol-frame builders want.
///
/// **Cursor FIFO**: [`spare()`](WriteBuf::spare) /
/// [`filled()`](WriteBuf::filled) to stage bytes (e.g. from a sans-IO
/// codec writing into the tail region), [`data()`](WriteBuf::data) to
/// send, [`advance(n)`](WriteBuf::advance) after partial writes.
/// Auto-reset on full drain means the buffer is reusable across cycles
/// without an explicit `clear()`. This is what TLS adapters use for
/// ciphertext staging.
///
/// # Examples
///
/// ```
/// use nexus_net::buf::WriteBuf;
///
/// let mut wbuf = WriteBuf::new(128, 14);
///
/// // Build message: payload first, then header
/// wbuf.append(b"Hello, world!");
/// wbuf.prepend(&[0x81, 0x0D]); // WS text frame header
///
/// // data() = contiguous [header | payload]
/// assert_eq!(&wbuf.data()[..2], &[0x81, 0x0D]);
/// assert_eq!(&wbuf.data()[2..], b"Hello, world!");
///
/// // For partial writes:
/// // let n = socket.write(wbuf.data())?;
/// // wbuf.advance(n);
/// ```
pub struct WriteBuf {
    buf: Box<[u8]>,
    head: usize,
    tail: usize,
    reset_offset: usize,
}

impl WriteBuf {
    /// Create with total capacity and reserved headroom.
    ///
    /// Usable tailroom = capacity - headroom.
    ///
    /// # Panics
    /// Panics if `headroom >= capacity`.
    #[must_use]
    pub fn new(capacity: usize, headroom: usize) -> Self {
        assert!(
            headroom < capacity,
            "headroom ({headroom}) must be less than capacity ({capacity})"
        );
        Self {
            buf: vec![0u8; capacity].into_boxed_slice(),
            head: headroom,
            tail: headroom,
            reset_offset: headroom,
        }
    }

    // =========================================================================
    // Build outbound data
    // =========================================================================

    /// Prepend bytes into headroom (protocol headers).
    /// Moves head backward.
    ///
    /// # Panics
    /// Panics if `src.len() > self.headroom()`.
    #[inline]
    pub fn prepend(&mut self, src: &[u8]) {
        if src.len() > self.headroom() {
            Self::panic_headroom(src.len(), self.headroom());
        }
        let new_head = self.head - src.len();
        self.buf[new_head..self.head].copy_from_slice(src);
        self.head = new_head;
    }

    /// Append bytes at tail (payload data).
    ///
    /// # Panics
    /// Panics if `src.len() > self.tailroom()`.
    #[inline]
    pub fn append(&mut self, src: &[u8]) {
        if src.len() > self.tailroom() {
            Self::panic_tailroom(src.len(), self.tailroom());
        }
        self.buf[self.tail..self.tail + src.len()].copy_from_slice(src);
        self.tail += src.len();
    }

    /// Extend the buffer with `n` zeroed bytes at the tail.
    /// No heap allocation — zeroes directly in the existing buffer.
    ///
    /// # Panics
    /// Panics if `n > self.tailroom()`.
    #[inline]
    pub fn extend_zeroed(&mut self, n: usize) {
        if n > self.tailroom() {
            Self::panic_tailroom(n, self.tailroom());
        }
        self.buf[self.tail..self.tail + n].fill(0);
        self.tail += n;
    }

    // =========================================================================
    // Send side
    // =========================================================================

    /// Complete outbound data (contiguous: headers + payload).
    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.buf[self.head..self.tail]
    }

    /// Mutable access to outbound data.
    /// For in-place operations like XOR masking.
    #[inline]
    pub fn data_mut(&mut self) -> &mut [u8] {
        &mut self.buf[self.head..self.tail]
    }

    /// Writable tail region for direct in-place writes.
    ///
    /// Pair with [`filled()`](Self::filled) to commit bytes after a
    /// successful write. Used by sans-IO codecs that produce bytes
    /// directly (e.g. `TlsCodec::write_tls_to(&mut buf.spare())`).
    ///
    /// Returns `buf[tail .. buf.len()]`. May be empty if tail has
    /// reached the buffer boundary.
    #[inline]
    pub fn spare(&mut self) -> &mut [u8] {
        &mut self.buf[self.tail..]
    }

    /// Commit `n` bytes written into [`spare()`](Self::spare).
    ///
    /// # Panics
    /// Panics if `n` would push tail past the buffer boundary.
    #[inline]
    pub fn filled(&mut self, n: usize) {
        let new_tail = self.tail + n;
        if new_tail > self.buf.len() {
            Self::panic_filled(n, self.tail, self.buf.len());
        }
        self.tail = new_tail;
    }

    /// Consume `n` bytes from front after a partial write.
    ///
    /// If the buffer becomes empty after advance, resets head and tail
    /// to `reset_offset` (free — no memmove, just cursor reset). This
    /// makes WriteBuf usable as a cursor FIFO: encrypt → drain partial →
    /// encrypt more → drain more, with auto-reclaim when fully drained.
    /// Calling [`clear()`](Self::clear) after a fully-drained
    /// `advance()` is now redundant.
    ///
    /// # Panics
    /// Panics if `n > self.len()`.
    #[inline]
    pub fn advance(&mut self, n: usize) {
        if n > self.len() {
            Self::panic_advance(n, self.len());
        }
        self.head += n;
        if self.head == self.tail {
            self.head = self.reset_offset;
            self.tail = self.reset_offset;
        }
    }

    // =========================================================================
    // Capacity queries
    // =========================================================================

    /// Bytes available for prepend.
    #[inline]
    pub fn headroom(&self) -> usize {
        self.head
    }

    /// Total backing-buffer capacity in bytes (fixed at construction).
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    /// Bytes available for append.
    #[inline]
    pub fn tailroom(&self) -> usize {
        self.buf.len() - self.tail
    }

    /// Bytes of outbound data.
    #[inline]
    pub fn len(&self) -> usize {
        self.tail - self.head
    }

    /// Whether the buffer has no outbound data.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head == self.tail
    }

    /// Remove `n` bytes from the end. For Content-Length backfill
    /// after shifting body bytes left.
    ///
    /// # Panics
    /// Panics if `n > self.len()`.
    pub fn shrink_tail(&mut self, n: usize) {
        if n > self.len() {
            Self::panic_shrink(n, self.len());
        }
        self.tail -= n;
    }

    /// Reset for next message. Cursors return to headroom offset.
    pub fn clear(&mut self) {
        self.head = self.reset_offset;
        self.tail = self.reset_offset;
    }

    #[cold]
    #[inline(never)]
    fn panic_headroom(needed: usize, available: usize) -> ! {
        panic!("prepend: {needed} bytes exceeds headroom ({available})")
    }

    #[cold]
    #[inline(never)]
    fn panic_tailroom(needed: usize, available: usize) -> ! {
        panic!("append: {needed} bytes exceeds tailroom ({available})")
    }

    #[cold]
    #[inline(never)]
    fn panic_advance(n: usize, len: usize) -> ! {
        panic!("advance({n}) exceeds data length ({len})")
    }

    #[cold]
    #[inline(never)]
    fn panic_shrink(n: usize, len: usize) -> ! {
        panic!("shrink_tail({n}) exceeds data length ({len})")
    }

    #[cold]
    #[inline(never)]
    fn panic_filled(n: usize, tail: usize, end: usize) -> ! {
        panic!("filled({n}) would exceed buffer (tail={tail}, end={end})")
    }
}

/// Write adapter over WriteBuf's spare region.
///
/// Implements `std::io::Write` for direct serialization into a
/// pre-allocated buffer. Used by REST `body_writer` and WS
/// `encode_text_writer` / `encode_binary_writer`.
pub struct WriteBufWriter<'a> {
    buf: &'a mut WriteBuf,
    written: usize,
}

impl<'a> WriteBufWriter<'a> {
    /// Create a writer over the WriteBuf's spare region.
    pub fn new(buf: &'a mut WriteBuf) -> Self {
        Self { buf, written: 0 }
    }

    /// Bytes written so far.
    pub fn written(&self) -> usize {
        self.written
    }
}

impl std::io::Write for WriteBufWriter<'_> {
    fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
        let available = self.buf.tailroom();
        if data.len() > available {
            return Err(std::io::Error::new(
                std::io::ErrorKind::WriteZero,
                "write exceeds buffer capacity",
            ));
        }
        self.buf.append(data);
        self.written += data.len();
        Ok(data.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_layout() {
        let buf = WriteBuf::new(128, 14);
        assert_eq!(buf.buf.len(), 128);
        assert_eq!(buf.headroom(), 14);
        assert_eq!(buf.tailroom(), 114);
        assert!(buf.is_empty());
    }

    #[test]
    fn append_data() {
        let mut buf = WriteBuf::new(128, 14);
        buf.append(b"Hello");
        assert_eq!(buf.data(), b"Hello");
        assert_eq!(buf.len(), 5);
    }

    #[test]
    fn prepend_data() {
        let mut buf = WriteBuf::new(128, 14);
        buf.append(b"World");
        buf.prepend(b"Hello");
        assert_eq!(buf.data(), b"HelloWorld");
        assert_eq!(buf.len(), 10);
    }

    #[test]
    fn prepend_then_append() {
        let mut buf = WriteBuf::new(128, 14);
        buf.append(b"payload");
        buf.prepend(&[0x81, 0x07]); // WS-like header
        let d = buf.data();
        assert_eq!(&d[..2], &[0x81, 0x07]);
        assert_eq!(&d[2..], b"payload");
    }

    #[test]
    fn advance_partial_write() {
        let mut buf = WriteBuf::new(128, 14);
        buf.append(b"Hello, world!");
        buf.advance(7);
        assert_eq!(buf.data(), b"world!");
        assert_eq!(buf.len(), 6);
    }

    #[test]
    fn headroom_tailroom_tracking() {
        let mut buf = WriteBuf::new(128, 14);
        assert_eq!(buf.headroom(), 14);
        assert_eq!(buf.tailroom(), 114);

        buf.append(b"12345");
        assert_eq!(buf.headroom(), 14);
        assert_eq!(buf.tailroom(), 109);

        buf.prepend(b"AB");
        assert_eq!(buf.headroom(), 12);
        assert_eq!(buf.tailroom(), 109);
    }

    #[test]
    fn clear_resets() {
        let mut buf = WriteBuf::new(128, 14);
        buf.append(b"data");
        buf.prepend(b"hdr");
        buf.clear();
        assert!(buf.is_empty());
        assert_eq!(buf.headroom(), 14);
        assert_eq!(buf.tailroom(), 114);
    }

    #[test]
    fn multiple_cycles() {
        let mut buf = WriteBuf::new(64, 10);
        for i in 0u8..5 {
            buf.clear();
            buf.append(&[i; 4]);
            buf.prepend(&[0xFF, i]);
            assert_eq!(buf.len(), 6);
            assert_eq!(buf.data()[0], 0xFF);
            assert_eq!(buf.data()[1], i);
            assert_eq!(&buf.data()[2..], &[i; 4]);
        }
    }

    #[test]
    #[should_panic(expected = "headroom")]
    fn prepend_exceeds_headroom() {
        let mut buf = WriteBuf::new(64, 4);
        buf.prepend(&[0; 8]); // 8 > 4 headroom
    }

    #[test]
    #[should_panic(expected = "tailroom")]
    fn append_exceeds_tailroom() {
        let mut buf = WriteBuf::new(16, 4);
        buf.append(&[0; 16]); // only 12 tailroom
    }

    #[test]
    #[should_panic(expected = "headroom")]
    fn headroom_ge_capacity_panics() {
        let _ = WriteBuf::new(10, 10);
    }

    #[test]
    #[should_panic(expected = "advance")]
    fn advance_exceeds_data() {
        let mut buf = WriteBuf::new(64, 10);
        buf.append(b"Hi");
        buf.advance(5);
    }

    #[test]
    fn zero_length_operations() {
        let mut buf = WriteBuf::new(32, 8);
        buf.append(b"");
        buf.prepend(b"");
        assert!(buf.is_empty());
        buf.advance(0);
        assert!(buf.is_empty());
    }

    #[test]
    fn advance_auto_resets_on_empty() {
        let mut buf = WriteBuf::new(64, 10);
        buf.append(b"Hello");
        buf.advance(5);
        assert!(buf.is_empty());
        // Auto-reset: headroom returns to its initial value, no clear() needed.
        assert_eq!(buf.headroom(), 10);
        assert_eq!(buf.tailroom(), 54);
    }

    #[test]
    fn advance_partial_does_not_reset() {
        let mut buf = WriteBuf::new(64, 10);
        buf.append(b"Hello");
        buf.advance(2);
        // Still has data — no reset.
        assert_eq!(buf.data(), b"llo");
        assert_eq!(buf.headroom(), 12);
    }

    #[test]
    fn cursor_fifo_cycle() {
        // Demonstrates the cursor-FIFO use case: write into spare,
        // commit with filled, partially drain via advance, repeat.
        // Ciphertext-style cycling without per-step memmove.
        let mut buf = WriteBuf::new(32, 0);

        buf.spare()[..10].copy_from_slice(b"0123456789");
        buf.filled(10);
        assert_eq!(buf.data(), b"0123456789");

        buf.advance(4);
        assert_eq!(buf.data(), b"456789");

        // Spare reflects the post-tail region — head is mid-buffer.
        assert_eq!(buf.spare().len(), 22);
        buf.spare()[..3].copy_from_slice(b"ABC");
        buf.filled(3);
        assert_eq!(buf.data(), b"456789ABC");

        buf.advance(9);
        assert!(buf.is_empty());
        // Auto-reset gave us full tailroom back.
        assert_eq!(buf.tailroom(), 32);
    }

    #[test]
    fn spare_is_post_tail_region() {
        let mut buf = WriteBuf::new(32, 8);
        // tail starts at headroom offset → spare is buf[8..32]
        assert_eq!(buf.spare().len(), 24);
        buf.append(b"hi");
        // tail advanced by 2 → spare shrinks by 2
        assert_eq!(buf.spare().len(), 22);
    }

    #[test]
    #[should_panic(expected = "filled")]
    fn filled_exceeds_buffer() {
        let mut buf = WriteBuf::new(16, 0);
        buf.filled(32);
    }
}
