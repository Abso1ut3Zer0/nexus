# Buffers: ReadBuf and WriteBuf

nexus-net ships two byte buffers tuned for protocol codecs:

- **`ReadBuf`** — inbound parse surface with optional pre/post padding.
  Used by `FrameReader` and `ResponseReader`.
- **`WriteBuf`** — outbound buffer with **prepend headroom** so frame
  or request headers can be written after the payload.

Both live in `nexus_net::buf`.

## `ReadBuf`

```rust
use nexus_net::buf::ReadBuf;

let mut buf = ReadBuf::new(capacity, pre_padding, post_padding);
// or:
let mut buf = ReadBuf::with_capacity(1 << 20);
```

The layout is a single contiguous allocation:

```text
┌─────────────┬──────────────────────────┬──────────────┐
│ pre_padding │  [consumed][filled][spare] │ post_padding │
└─────────────┴──────────────────────────┴──────────────┘
                ▲          ▲         ▲
                cursor     cursor+len capacity
```

- `spare()` — mutable slice of unfilled bytes you can read into
- `filled(n)` — mark `n` bytes as filled (after reading from transport)
- `data()` — slice of unconsumed parsed bytes
- `advance(n)` — mark `n` bytes as consumed
- `compact()` — move unconsumed data back to the front, reclaiming
  space for more `spare()`

Pre-padding is useful when a protocol parser wants to write a few
bytes **before** the data it reads (e.g. a length prefix). Post-padding
is useful for SIMD over-reads: simdutf8 can read up to 32 bytes past
the end of a slice, so post-padding of 32 is used internally so the
validation code can run lock-step without extra branch.

### Usage from `FrameReader`

```rust
let mut reader = FrameReader::builder().build();

let dst = reader.spare();           // mutable &[u8]
let n = tcp.read(dst)?;
reader.filled(n);

while reader.poll()? {
    match reader.next()? {
        Some(msg) => handle(msg),
        None => break,
    }
}
```

The reader re-exposes `spare()`, `filled()`, and `compact()` on its
own surface — they proxy into the underlying `ReadBuf`.

### Compaction

The reader tracks a `should_compact()` hint based on how much of the
buffer is consumed. `ClientBuilder::compact_at(fraction)` tunes when
compaction fires (default 0.5 — compact once half the buffer is
consumed). Compaction is an O(n) `memmove` of the unconsumed tail to
the front, so you want it to run when that tail is small (which is
almost always — most message boundaries land on the frame boundary).

If `spare()` returns an empty slice, you **must** call `compact()`
before the next read. The convenience `Client::recv()` does this for
you.

## `WriteBuf`

```rust
use nexus_net::buf::WriteBuf;

let mut buf = WriteBuf::new(capacity, headroom);
```

The distinguishing feature is **prepend headroom**: you reserve some
bytes at the front so headers can be written after you know the
payload.

```text
┌─────────────────────────┬────────────────────────┐
│ [headroom→ prepend()]   │ [append() → payload]   │
└─────────────────────────┴────────────────────────┘
 ▲                         ▲                        ▲
 start                     cursor                    capacity
```

- `append(&[u8])` — write bytes at the tail (ordinary append)
- `prepend(&[u8])` — write bytes into the headroom **to the left** of
  the current start. Each prepend moves the start pointer left.
- `data()` — slice from start to tail (the framed, ready-to-send bytes)
- `clear()` — reset both cursors back to the initial headroom split

### Why prepend?

A WebSocket frame header is 2–14 bytes depending on payload length.
Computing payload length after the payload is written is trivial —
but traditional "buffer-then-patch" schemes require either a
two-pass copy (serialize payload to scratch, then prepend header into
main buffer) or reserving a *maximum-size* header slot and leaving
padding when the real header is shorter.

`WriteBuf` solves this with a left-growing prepend region:

1. `FrameWriter` writes the **masked payload** via `append()` (or
   direct writer). This also updates the mask in-place as bytes are
   produced — single pass.
2. After the payload is complete, `FrameWriter` computes the header
   (length encoding determined by payload size) and `prepend()`s it
   into the headroom.
3. `buf.data()` now points at `[header | payload]` — one
   contiguous slice ready for `write_all()`.

This is a few percent faster than patch-then-memmove, and avoids the
"max header + actual header" gap entirely. For 128B text frames it
cuts encode to ~20 cycles.

### Sizing

- **`capacity`** — the total buffer size. Must be large enough for
  the biggest single frame/request you emit plus the headroom.
- **`headroom`** — at least 14 for WebSocket frames (2-byte header +
  8-byte extended length + 4-byte mask). 64 or 128 is safe for HTTP
  where you prepend a start line plus a few short headers.

The `ws::ClientBuilder` defaults to 64 KiB capacity and 14-byte
headroom. `rest::ClientBuilder` uses a 32 KiB `WriteBuf` owned by the
`RequestWriter`.

## `WriteBufWriter`

A thin `std::io::Write` adapter over `WriteBuf`:

```rust
use nexus_net::buf::{WriteBuf, WriteBufWriter};
use std::io::Write;

let mut buf = WriteBuf::new(4096, 64);
let mut w = WriteBufWriter::new(&mut buf);
write!(w, "hello {}", 42)?;
let n = w.written();
```

Used internally by `RequestWriter::body_writer` so callers can
serialize with `write!`/`serde_json::to_writer` without an extra
allocation.

## Capacity tuning

- `buffer_capacity` (read): size for several seconds of peak throughput
  so you don't hammer `compact()`. 256 KiB handles ~10K msg/sec at
  128B; 1 MiB is the default.
- `write_buffer_capacity`: size for the largest single frame or
  request. WebSocket control frames are capped at 125B; data frames
  can be up to `max_frame_size`. Oversized sends return
  `EncodeError::Overflow`.
- `max_message_size`: independently bounded — a small WriteBuf doesn't
  protect you from inbound floods.

See [nexus-web/docs/performance.md](../../nexus-web/docs/performance.md) for concrete numbers.
