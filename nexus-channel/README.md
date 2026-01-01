# nexus-channel

A high-performance bounded SPSC (Single-Producer Single-Consumer) channel for Rust.

Built on [`nexus-queue`](../nexus-queue)'s lock-free ring buffer with an optimized parking strategy that minimizes syscall overhead.

## Performance

Benchmarked against `crossbeam-channel` (bounded) on Intel Core Ultra 7 155H @ 2.7GHz base, pinned to physical cores 0,2 with turbo disabled:

| Metric | nexus-channel | crossbeam-channel | Improvement |
|--------|---------------|-------------------|-------------|
| **p50 latency** | 665 cycles (247 ns) | 1344 cycles (499 ns) | **2.0x faster** |
| **p99 latency** | 1360 cycles (505 ns) | 1708 cycles (634 ns) | **1.3x faster** |
| **p999 latency** | 2501 cycles (928 ns) | 37023 cycles (13.7 µs) | **14.8x faster** |
| **Throughput** | 64 M msgs/sec | 34 M msgs/sec | **1.9x faster** |

The **14.8x improvement at p999** comes from avoiding syscalls in the common case.

## Usage
```rust
use nexus_channel::channel;

// Create a bounded channel with capacity 1024
let (mut tx, mut rx) = channel::<u64>(1024);

// Blocking send - waits if buffer is full
tx.send(42).unwrap();

// Blocking recv - waits if buffer is empty  
assert_eq!(rx.recv().unwrap(), 42);
```

### Non-blocking Operations
```rust
use nexus_channel::{channel, TrySendError, TryRecvError};

let (mut tx, mut rx) = channel::<u64>(2);

// try_send returns immediately
tx.try_send(1).unwrap();
tx.try_send(2).unwrap();
assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));

// try_recv returns immediately
assert_eq!(rx.try_recv().unwrap(), 1);
assert_eq!(rx.try_recv().unwrap(), 2);
assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
```

### Cross-Thread Communication
```rust
use nexus_channel::channel;
use std::thread;

let (mut tx, mut rx) = channel::<String>(100);

let producer = thread::spawn(move || {
    for i in 0..1000 {
        tx.send(format!("message {}", i)).unwrap();
    }
});

let consumer = thread::spawn(move || {
    for _ in 0..1000 {
        let msg = rx.recv().unwrap();
        // process msg
    }
});

producer.join().unwrap();
consumer.join().unwrap();
```

### Disconnection Handling
```rust
use nexus_channel::channel;

let (mut tx, mut rx) = channel::<u64>(4);

tx.send(1).unwrap();
tx.send(2).unwrap();
drop(tx); // Disconnect

// Can still receive buffered messages
assert_eq!(rx.recv().unwrap(), 1);
assert_eq!(rx.recv().unwrap(), 2);

// Then get disconnection error
assert!(rx.recv().is_err());
```

## Why It's Fast

### 1. Conditional Parking

Traditional channels call `unpark()` on every send, even when the receiver is actively spinning:
```
Traditional channel:
┌─────────────────────────────────────────────────────────┐
│ send() -> push -> unpark() -> SYSCALL (every time!)    │
│ recv() -> pop empty -> park() -> SYSCALL               │
└─────────────────────────────────────────────────────────┘

nexus-channel:
┌─────────────────────────────────────────────────────────┐
│ send() -> push -> if (receiver_parked) unpark()        │
│ recv() -> pop empty -> spin -> snooze -> park()        │
└─────────────────────────────────────────────────────────┘
   Only syscall when receiver is ACTUALLY sleeping
```

The `receiver_parked` check is just an atomic load (~1 cycle). The syscall is ~1000+ cycles. In high-throughput scenarios where data flows continuously, we almost never hit the syscall path.

### 2. Three-Phase Backoff

Before committing to an expensive park syscall:
```
Phase 1: Fast path
├── Try operation immediately
├── Cost: ~10-50 cycles
└── Succeeds when data is already available

Phase 2: Backoff (spin + yield)
├── Use crossbeam's Backoff::snooze()
├── Cost: ~100-1000 cycles per iteration  
├── Configurable iterations (default: 8)
└── Catches data arriving "soon"

Phase 3: Park (syscall)
├── Actually sleep via futex/os primitive
├── Cost: ~1000-10000+ cycles
└── Only when data is truly not coming
```

### 3. Cache-Padded Parking Flags
```
┌─────────────────────────────────────────────────────────┐
│ Cache Line 0: sender_parked (AtomicBool + 63 bytes pad) │
├─────────────────────────────────────────────────────────┤
│ Cache Line 1: receiver_parked (AtomicBool + 63 bytes)   │
└─────────────────────────────────────────────────────────┘
   No false sharing between sender and receiver
```

### 4. Lock-Free Underlying Queue

The actual data transfer uses `nexus_queue`'s per-slot lap counter design, which achieves ~430 cycle one-way latency. See the [nexus-queue README](../nexus-queue/README.md) for details.

## The p999 Win Explained

Why 14.8x faster at p999 (928 ns vs 13.7 µs)?
```
crossbeam: Every send() calls unpark() -> futex syscall
           Even if receiver is spinning and will see data immediately
           Occasional syscall latency spikes to 10+ µs

nexus:     send() checks receiver_parked flag (just a load)
           If receiver is spinning, no syscall needed
           Only syscall when receiver actually went to sleep
```

In ping-pong workloads, the receiver is rarely actually asleep—data arrives quickly. So we skip almost all syscalls, eliminating the tail latency spikes.

## Tuning

The default backoff uses 8 snooze iterations. Tune for your workload:
```rust
use nexus_channel::channel_with_config;

// More spinning for ultra-low-latency (burns more CPU)
let (tx, rx) = channel_with_config::<u64>(1024, 32);

// Less spinning for power efficiency  
let (tx, rx) = channel_with_config::<u64>(1024, 2);
```

## API Reference

### Channel Creation

| Function | Description |
|----------|-------------|
| `channel::<T>(capacity)` | Create channel with default backoff (8 iterations) |
| `channel_with_config::<T>(capacity, snooze_iters)` | Create channel with custom backoff |

### Sender Methods

| Method | Description |
|--------|-------------|
| `send(value)` | Blocking send, returns `Err` on disconnect |
| `try_send(value)` | Non-blocking send, returns `Full` or `Disconnected` |
| `is_disconnected()` | Check if receiver was dropped |
| `capacity()` | Get channel capacity |

### Receiver Methods

| Method | Description |
|--------|-------------|
| `recv()` | Blocking receive, returns `Err` on disconnect |
| `try_recv()` | Non-blocking receive, returns `Empty` or `Disconnected` |
| `is_disconnected()` | Check if sender was dropped |
| `capacity()` | Get channel capacity |

## Benchmarking

For accurate benchmarks, disable turbo boost and pin to physical cores:
```bash
# Disable turbo boost
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo

# Run latency benchmark (ping-pong)
sudo taskset -c 0,2 ./target/release/deps/perf_channel_latency-*

# Run throughput benchmark
sudo taskset -c 0,2 ./target/release/deps/perf_channel_throughput-*

# Re-enable turbo boost
echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

### Why Pinning Matters

Without pinning, threads can migrate between cores, causing:
- Cache invalidation storms
- Variable cross-core latency (same CCX vs different CCX)
- Up to 2x throughput variance

### Why Disable Turbo

Turbo boost changes CPU frequency dynamically, making cycle counts inconsistent. The actual memory/cache latency is fixed in nanoseconds, but cycle counts vary with frequency.

## When to Use This

**Use nexus-channel when:**
- You have exactly one sender and one receiver
- You need blocking semantics (send waits when full, recv waits when empty)
- Tail latency matters (p999, p9999)
- You want maximum throughput for SPSC

**Consider alternatives when:**
- Multiple senders → `crossbeam-channel`, `flume`
- Multiple receivers → `crossbeam-channel`, `flume`  
- Need `select!` macro → `crossbeam-channel`
- Don't need blocking → use `nexus_queue` directly
- Need async/await → `tokio::sync::mpsc`

## License

MIT OR Apache-2.0
