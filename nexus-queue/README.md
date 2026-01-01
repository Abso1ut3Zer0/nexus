# nexus-queue

A high-performance SPSC (Single-Producer Single-Consumer) ring buffer for Rust, optimized for ultra-low-latency messaging.

## Performance

Benchmarked against [`rtrb`](https://crates.io/crates/rtrb) and [`crossbeam`](https://crates.io/crates/crossbeam) on Intel Core Ultra 7 155H, pinned to physical cores 0,2 with turbo boost disabled:

| Metric | nexus-queue | rtrb | crossbeam ArrayQueue |
|--------|-------------|------|----------------------|
| **p50 latency** | 425 cycles (158 ns) | 560 cycles (208 ns) | 1073 cycles (398 ns) |
| **p99 latency** | 681 cycles (253 ns) | 894 cycles (332 ns) | 1598 cycles (593 ns) |
| **Throughput** | 117 M msgs/sec | 50 M msgs/sec | 32 M msgs/sec |

**~25% lower latency and ~2.3x higher throughput than rtrb.**

## Usage

```rust
use nexus_queue;

let (mut producer, mut consumer) = nexus_queue::ring_buffer::<u64>(1024);

// Producer thread
producer.push(42).unwrap();

// Consumer thread  
assert_eq!(consumer.pop(), Some(42));
```

### Handling backpressure

```rust
// Spin until space is available
while producer.push(msg).is_err() {
    std::hint::spin_loop();
}

// Or handle the full case
match producer.push(msg) {
    Ok(()) => { /* sent */ }
    Err(Full(returned_msg)) => { /* queue full, msg returned */ }
}
```

### Disconnection detection

```rust
// Check if the other end has been dropped
if consumer.is_disconnected() {
    // Producer was dropped, drain remaining messages
}

if producer.is_disconnected() {
    // Consumer was dropped, stop producing
}
```

## Design

### Per-Slot Sequencing

Traditional SPSC queues use separate atomic head/tail indices:

```
Traditional (rtrb-style):
┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐
│ head (atomic)   │  │ tail (atomic)   │  │ buffer[N]       │
│ cached_tail     │  │ cached_head     │  │ (just data)     │
└─────────────────┘  └─────────────────┘  └─────────────────┘
   Cache line 1         Cache line 2         Cache line 3+
```

nexus-queue uses per-slot lap counters instead:

```
Per-slot sequencing (nexus):
┌──────────────────────────────────────────────────────────┐
│ buffer[0]: { lap: AtomicUsize, data: T }                 │
│ buffer[1]: { lap: AtomicUsize, data: T }                 │
│ ...                                                      │
└──────────────────────────────────────────────────────────┘
   Lap counter + data on SAME cache line
```

### Why This Wins

1. **Cache Locality**: The lap counter and data share a cache line. One fetch gets both the synchronization state and the payload.

2. **No Stale Cache Problem**: Traditional designs cache the remote index to avoid atomic loads, but in ping-pong scenarios the cache is *always* stale. Per-slot sequencing checks the slot directly.

3. **Simpler Control Flow**: Fewer branches means better branch prediction.

### Optimization Journey

Starting from an rtrb clone (p50 ≈ 560 cycles):

| Change | Impact | Notes |
|--------|--------|-------|
| Per-slot lap counters | **+25%** | Biggest win - eliminates stale cache |
| Division → bit shift | **+15%** | `tail/cap` → `tail>>shift` |
| `repr(C)` field ordering | +5% | Hot fields first for prefetching |
| Manual fencing | ~0% | Required for ARM correctness |

What didn't work:
- **Const generics**: -20% regression (monomorphization bloat)
- **CachePadded slots**: No improvement (true sharing dominates)
- **Cached indices**: Slower in latency-sensitive workloads

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

The implementation uses manual fencing for clarity and portability:

- **Producer**: `fence(Release)` before storing lap counter
- **Consumer**: `fence(Acquire)` after loading lap counter, `fence(Release)` before clearing

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
