# nexus-queue

A high-performance SPSC (Single-Producer Single-Consumer) ring buffer for Rust, optimized for ultra-low-latency messaging.

## Performance

Benchmarked against [`rtrb`](https://crates.io/crates/rtrb) on dual-socket Intel Xeon 8124M @ 3.00GHz, pinned to physical cores with turbo boost disabled:

### Latency (ping-pong, 25 runs)

| Metric | nexus-queue | rtrb | Δ |
|--------|-------------|------|---|
| **p50 best** | 346 cycles | 375 cycles | -8% |
| **p50 median** | ~370 cycles | ~430 cycles | -14% |
| **p99 typical** | ~600 cycles | ~700 cycles | -14% |

**25/25 wins on p50 latency.**

### Throughput

| Metric | nexus-queue | rtrb |
|--------|-------------|------|
| **Throughput** | 294 M msgs/sec | 127 M msgs/sec |

**2.3x throughput advantage.**

## Usage
```rust
use nexus_queue::spsc;

let (mut tx, mut rx) = spsc::ring_buffer::<u64>(1024);

// Producer thread
tx.push(42).unwrap();

// Consumer thread  
assert_eq!(rx.pop(), Some(42));
```

### Handling backpressure
```rust
use nexus_queue::Full;

// Spin until space is available
while tx.push(msg).is_err() {
    std::hint::spin_loop();
}

// Or handle the full case
match tx.push(msg) {
    Ok(()) => { /* sent */ }
    Err(Full(returned_msg)) => { /* queue full, msg returned */ }
}
```

### Disconnection detection
```rust
// Check if the other end has been dropped
if rx.is_disconnected() {
    // Producer was dropped, drain remaining messages
}

if tx.is_disconnected() {
    // Consumer was dropped, stop producing
}
```

## Design

Two implementations are available with different cache line ownership patterns:

### Index-based (default)
```
┌─────────────────────────────────────────────────────────────┐
│ Shared:                                                     │
│   tail: CachePadded<AtomicUsize>   ← Producer writes        │
│   head: CachePadded<AtomicUsize>   ← Consumer writes        │
│   buffer: *mut T                                            │
└─────────────────────────────────────────────────────────────┘
```

Producer and consumer write to **separate cache lines**. Each endpoint caches the other's index, only refreshing when the cache indicates full/empty.

### Slot-based
```
┌──────────────────────────────────────────────────────────────┐
│ buffer[0]: { lap: AtomicUsize, data: T }                     │
│ buffer[1]: { lap: AtomicUsize, data: T }                     │
│ ...                                                          │
└──────────────────────────────────────────────────────────────┘
```

Producer and consumer write to the **same cache line** (the slot's lap counter). The synchronization word and data share a cache line for locality.

### Trade-offs

| | index (default) | slot |
|-------------------|-----------------|------|
| Cache line writes | Unidirectional | Bidirectional |
| Multi-socket/NUMA | ✓ Better | Worse |
| Shared L3 (single socket) | Good | ✓ Better |

Which performs better depends on your hardware topology. **Benchmark both on your target hardware.**
```toml
# Use slot-based implementation
nexus-queue = { version = "0.3", features = ["slot-based"] }
```

Both implementations are always available as submodules for benchmarking:
```rust
use nexus_queue::spsc::{index, slot};

let (mut tx_index, mut rx_index) = index::ring_buffer::<u64>(1024);
let (mut tx_slot, mut rx_slot) = slot::ring_buffer::<u64>(1024);
```

## Benchmarking

For accurate results, disable turbo boost and pin to physical cores:
```bash
# Disable turbo boost (Intel)
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo

# Run benchmark pinned to cores 0 and 2
sudo taskset -c 0,2 ./target/release/deps/your_benchmark-*

# Re-enable turbo boost
echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

Verify your core topology with `lscpu -e` — you want cores with different CORE numbers to avoid hyperthreading siblings.

## Memory Ordering

Both implementations use manual fencing for clarity and portability:

- **Producer**: `fence(Release)` before publishing
- **Consumer**: `fence(Acquire)` after reading, `fence(Release)` before advancing

On x86 these compile to no instructions (strong memory model), but they're required for correctness on ARM and other weakly-ordered architectures.

## When to Use This

**Use nexus-queue when:**
- You have exactly one producer and one consumer
- You need the lowest possible latency
- You're building trading systems, audio pipelines, or real-time applications

**Consider alternatives when:**
- Multiple producers → use MPSC queues
- Multiple consumers → use MPMC queues
- You need async/await → use `tokio::sync::mpsc`

## License

MIT OR Apache-2.0
