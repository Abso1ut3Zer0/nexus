# nexus-slot

A high-performance SPSC conflation slot for "latest value wins" scenarios.

## Overview

`nexus-slot` provides a single-value slot optimized for the common pattern where only the most recent value matters: market data snapshots, sensor readings, configuration updates, position state, etc.

- **Writer** overwrites with newest data (never blocks)
- **Reader** gets each new value exactly once
- **Old values** are silently discarded (conflated)

## Performance

Benchmarked on Intel Core Ultra 7 155H, pinned to physical cores with turbo disabled:

| Implementation | p50 Latency | Notes |
|----------------|-------------|-------|
| **nexus-slot** | 159 cycles (59 ns) | SPSC only |
| `seqlock` crate | 355 cycles (132 ns) | Supports multiple writers |
| `ArrayQueue(1)` | 540 cycles (201 ns) | General-purpose bounded queue |

The **2.2x speedup** over `seqlock` comes from specializing for single-producer:

- No writer contention → no CAS loops
- Cached sequence number → writer avoids atomic load
- No queue machinery → just a sequence counter

## Usage

```rust
use nexus_slot::{slot, Pod};

#[derive(Copy, Clone, Default)]
struct Quote {
    bid: f64,
    ask: f64,
    sequence: u64,
}

let (mut writer, mut reader) = slot::<Quote>();

// Writer side (e.g., market data thread)
writer.write(Quote { bid: 100.0, ask: 100.05, sequence: 1 });
writer.write(Quote { bid: 100.1, ask: 100.15, sequence: 2 });  // Overwrites previous

// Reader side (e.g., trading logic thread)
let quote = reader.read();  // Gets sequence 2, skipped 1
assert_eq!(quote.unwrap().sequence, 2);

// Already consumed - returns None until next write
assert!(reader.read().is_none());
```

## Semantics

### Conflation

Multiple writes before a read result in only the latest value being observed:

```rust
writer.write(value_1);
writer.write(value_2);
writer.write(value_3);

// Reader only sees value_3
assert_eq!(reader.read(), Some(value_3));
assert!(reader.read().is_none());
```

### Exactly-Once Delivery

Each written value can be read at most once:

```rust
writer.write(value);

assert!(reader.read().is_some());  // Consumes it
assert!(reader.read().is_none());  // Already consumed

writer.write(another_value);
assert!(reader.read().is_some());  // New value available
```

### Check Without Consuming

```rust
if reader.has_update() {
    // New data available, but not consumed yet
    let value = reader.read();  // Now consumed
}
```

## The `Pod` Trait

Types must implement `Pod` (Plain Old Data) — no heap allocations or drop glue.

Any `Copy` type automatically implements `Pod`:

```rust
// These work automatically
let (w, r) = slot::<u64>();
let (w, r) = slot::<[f64; 4]>();
let (w, r) = slot::<(i32, i32)>();
```

For non-`Copy` types that are still just bytes:

```rust
use nexus_slot::Pod;

#[repr(C)]
struct OrderBook {
    bids: [f64; 20],
    asks: [f64; 20],
    sequence: u64,
}

// SAFETY: OrderBook is just bytes, no heap allocations
unsafe impl Pod for OrderBook {}

let (mut writer, mut reader) = slot::<OrderBook>();
```

**Pod requirements:**
- No `Vec`, `String`, `Box`, `Arc`, or other heap types
- No `File`, `TcpStream`, `Mutex`, or other resources
- `std::mem::needs_drop::<T>()` must be `false`

## API

### Writer

| Method | Description |
|--------|-------------|
| `write(value)` | Overwrite with new value (never blocks) |
| `is_disconnected()` | Returns true if reader was dropped |

### Reader

| Method | Description |
|--------|-------------|
| `read() -> Option<T>` | Get latest value if new, consuming it |
| `has_update() -> bool` | Check for new data without consuming |
| `is_disconnected()` | Returns true if writer was dropped |

## Use Cases

**Good fit:**
- Market data distribution (quotes, trades, order book snapshots)
- Sensor data (temperature, position, velocity)
- Configuration/state broadcasting
- Any "latest value wins" SPSC scenario

**Not ideal for:**
- Multiple writers → use `seqlock` or mutex
- Multiple readers → use `arc-swap` or `RwLock`
- Queue semantics (all values must be delivered) → use `nexus-queue`
- Async/await → use `tokio::sync::watch`

## Implementation

Uses a sequence lock (seqlock) internally:

1. Writer increments sequence to odd (write in progress)
2. Writer copies data
3. Writer increments sequence to even (write complete)
4. Reader loads sequence, copies data, checks sequence unchanged
5. If sequence changed during read, retry

The SPSC constraint allows caching the sequence on the writer side, eliminating an atomic load per write.

## Thread Safety

- `Writer<T>` is `Send` (can move to another thread)
- `Reader<T>` is `Send` (can move to another thread)
- Neither is `Sync` — each handle is for one thread only

## License

MIT OR Apache-2.0
