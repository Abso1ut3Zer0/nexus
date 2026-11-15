# Performance

Numbers are median cycles on an AMD desktop CPU, no turbo
throttling, warm cache, batch=64, 100K samples. See `BENCHMARKS.md`
at the crate root for the raw tables.

Take these as **relative** — absolute cycle counts depend on CPU,
frequency, and the work around the codec. The ratios against
`tungstenite` and `reqwest` are stable across machines we've tested.

## WebSocket inbound — `FrameReader`

### Single-frame unmasked text (client role, server→client)

The market-data path. Most messages on the wire.

| Payload | p50 | p99 | p99.9 |
|---------|-----|-----|-------|
| 32 B | 43 | 64 | 87 |
| 128 B | 38 | 66 | 157 |
| 512 B | 42 | 51 | 190 |
| 2048 B | 81 | 128 | 381 |

That's **~39 cycles** to parse a 128B text frame including UTF-8
validation. Comparable tungstenite numbers are ~390 cycles — **~10x**
at the cycle level.

### Single-frame unmasked binary (client role)

No UTF-8 validation. Shows the validation cost by comparison:

| Payload | p50 |
|---------|-----|
| 128 B | 34 |
| 1024 B | 33 |

UTF-8 adds ~5 cycles at 128B and ~9 cycles at 1024B. simdutf8 is
aggressively vectorized.

### Single-frame masked text (server role, client→server)

Adds XOR unmasking:

| Payload | p50 |
|---------|-----|
| 128 B | 51 |
| 512 B | 65 |
| 2048 B | 145 |

## Component costs

### `apply_mask` (SIMD XOR)

SSE2 at 16B/step, AVX2 at 32B/step.

| Size | p50 |
|------|-----|
| 64 B | 11 |
| 128 B | 12 |
| 512 B | 30 |
| 1024 B | 31 |

### `simdutf8::basic::from_utf8`

| Size | p50 |
|------|-----|
| 64 B | 5 |
| 128 B | 7 |
| 512 B | 15 |
| 1024 B | 26 |

## Throughput

- **WebSocket in-memory round-trip:** ~107 M msg/sec (128B text)
- **TCP loopback:** ~33 M msg/sec (128B text)
- **REST loopback:** ~114 K req/sec (short GET + 200 OK, mock
  server)

## vs tungstenite

Head-to-head on identical workloads:

| Workload | tungstenite p50 | nexus-web p50 | Ratio |
|----------|-----------------|---------------|-------|
| 128B text parse | ~390 | 38 | **10.3x** |
| 128B text encode | ~90 | ~20 | **4.5x** |

Why the gap:

- **Zero-copy parse.** tungstenite allocates a `Vec<u8>` per frame;
  nexus-web returns `Message::Text(&str)` borrowing into the ReadBuf.
  No allocator, no `memcpy`, no Arc counting.
- **SIMD everywhere.** Masking is AVX2/SSE2. UTF-8 validation is
  simdutf8. tungstenite uses scalar code in both paths.
- **Inline control flow.** The parser is a single state machine;
  tungstenite bounces between `Frame`, `Message`, and `Utf8Validator`
  objects, each with its own branch/callback layer.
- **Prepend WriteBuf.** Encode is one pass — masking and header emit
  interleave with the payload write. See [nexus-net/docs/buffers.md](../../nexus-net/docs/buffers.md).

## vs reqwest (REST)

| Workload | reqwest p50 | nexus-web p50 | Ratio |
|----------|-------------|---------------|-------|
| Mock GET (loopback) | ~1540 | ~494 | **3.1x** |

reqwest targets usability and covers HTTP/2 + connection pooling +
cookies + redirect following. nexus-web does HTTP/1.1 keep-alive
only and leaves pooling / retry to the caller. Different scope,
different numbers.

## TLS

TLS (rustls + aws-lc-rs) adds record-layer encryption but not much
parser overhead. Steady-state read/write cost for a 128B payload is
~300 cycles on top of the base codec — dominated by AES-GCM.

Handshake cost is almost entirely cryptographic (~1–3ms) and
identical to bare rustls. nexus-web doesn't add observable latency
on top of rustls at handshake time.

## What nexus-web does *not* optimize

- **Multi-connection routing.** There is no thread pool, no
  scheduler, no epoll abstraction. You bring the IO.
- **HTTP/2, HTTP/3, QUIC.** Only HTTP/1.1 keep-alive is supported.
- **Compression (permessage-deflate).** Not implemented. On trading
  feeds, compression adds 50–200 µs of latency and is off by default
  on every exchange we care about.
- **Per-message allocation.** The whole point is to avoid it.

## Measuring in your own workload

Use rdtsc timing:

```rust
let start = unsafe { core::arch::x86_64::_rdtsc() };
let msg = ws.recv()?;
let cycles = unsafe { core::arch::x86_64::_rdtsc() } - start;
```

Collect into an HDR histogram (e.g. `hdrhistogram` crate) and
report p50 / p99 / p99.9 / max. Don't use `Instant::now()` inside a
tight loop — the syscall is ~30ns and drowns the signal.

Disable turbo and pin to a physical core (avoid hyperthread
siblings) when benchmarking:

```bash
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
sudo taskset -c 0,2 ./target/release/your_bench
```
