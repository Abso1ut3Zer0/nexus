# nexus-slab

Manual memory management with SLUB-style slab allocation. 1 cycle churn
(alloc+free) at 32B, sub-cycle free. 15x faster than Box. Placement new
confirmed in assembly.

## Why

When you churn same-type objects (orders, connections, timers, nodes), the
global allocator is your bottleneck. `malloc`/`free` contend with every other
allocation in the process. A slab gives you:

- **LIFO cache locality** — free a slot, allocate again, get the same
  cache-hot memory back
- **Zero fragmentation** — every slot is the same size
- **Allocator isolation** — your hot path doesn't compete with logging
  or serialization
- **Placement new** — values written directly into slot memory, no copy

## Quick Start

```rust
use nexus_slab::bounded::Slab;

// SAFETY: caller accepts manual memory management contract
let slab = unsafe { Slab::with_capacity(1024) };

let mut ptr = slab.alloc(Order { id: 1, price: 100.5 });
ptr.price = 105.0;         // safe Deref/DerefMut
slab.free(ptr);             // consumes handle, can't use after
```

Construction is `unsafe` — you're opting into:
- **Free everything you allocate.** Unfree'd slots leak.
- **Free from the same slab.** Cross-slab free corrupts the freelist.
- **Don't share across threads.** The slab is `!Send`/`!Sync`.

Everything after construction is safe. `Slot<T>` is move-only
(`!Copy`, `!Clone`) — the compiler prevents double-free.

## API

### Typed Slabs

```rust
use nexus_slab::bounded::Slab;   // fixed capacity
use nexus_slab::unbounded::Slab; // grows via chunks

// Bounded
let slab = unsafe { Slab::with_capacity(1024) };
let ptr = slab.alloc(42u64);           // panics if full
let ptr = slab.try_alloc(42u64)?;      // returns Err(Full(42)) if full
let value = slab.take(ptr);            // extract without drop, free slot
slab.free(ptr);                        // drop value, free slot

// Unbounded
let slab = unsafe { Slab::with_chunk_capacity(256) };
let ptr = slab.alloc(42u64);           // never fails, grows if needed

// Placement new (two-phase)
if let Some(claim) = slab.claim() {
    let ptr = claim.write(Order { id: 1, price: 100.5 });
    // value constructed directly in slot memory
    slab.free(ptr);
}
```

### Byte Slabs (Type-Erased)

Store heterogeneous types in one slab. Any `T` fitting in `N` bytes works.

```rust
use nexus_slab::byte::bounded::Slab;

let slab: Slab<128> = unsafe { Slab::with_capacity(64) };

let p1 = slab.alloc(42u64);                    // 8 bytes
let p2 = slab.alloc([1.0f64; 8]);              // 64 bytes
let p3 = slab.alloc(String::from("hello"));    // different types, same slab

slab.free(p3);
slab.free(p2);
slab.free(p1);
```

### Slot<T>

8-byte move-only handle. Safe `Deref`/`DerefMut` access.

```rust
let mut ptr = slab.alloc(Order { id: 1, price: 100.5 });

// Safe access
ptr.price = 105.0;

// Raw pointer escape hatch
let raw = ptr.into_raw();               // disarms debug leak detector
let ptr = unsafe { Slot::from_raw(raw) };  // reconstruct
slab.free(ptr);
```

**Debug mode:** dropping a `Slot` without calling `free()` or `take()`
panics (leak detection). Release mode: silent leak.

**Pinning:** `pin()` / `pin_mut()` are deprecated in 2.3.5 and removed in
2.4.0. They were unsound for `!Unpin` types: the address is stable, but
`take()` and `DerefMut` can still move the value out from under the `Pin`.
For `T: Unpin`, `Pin::new(&mut *ptr)` is correct and needs no helper. A
sound pinned handle that consumes the `Slot` ships in 2.4.0.

### Rc Slabs (Shared Ownership)

When multiple owners need access to the same slot — e.g., a collection
holds a node and the user holds a handle for cancellation.

```rust
use nexus_slab::rc::bounded::Slab;

// SAFETY: caller accepts manual memory management contract
let slab = unsafe { Slab::<Order>::with_capacity(1024) };

// Alloc returns RcSlot<Order> with refcount 1
let h1 = slab.alloc(Order { id: 1, price: 100.0 });

// Clone is safe — increments refcount
let h2 = h1.clone();  // refcount 2

// Access through borrow guards — one borrow at a time
{
    let mut order = h1.borrow_mut();  // exclusive guard
    order.price = 105.0;
}
{
    let order = h2.borrow();          // shared guard (still exclusive — see below)
    assert_eq!(order.price, 105.0);   // mutation visible across clones
}

// Every handle must be freed — slot deallocated on last free
slab.free(h2);  // refcount 2 → 1, slot stays alive
slab.free(h1);  // refcount 1 → 0, value dropped, slot freed
```

**Borrow rules:** More conservative than `RefCell`. Only one borrow
(shared OR exclusive) is allowed at a time. Any attempt to borrow while
another borrow is active panics. This is intentional — shared mutable
state in a low-latency system should be tightly controlled.

```rust
let h1 = slab.alloc(42u64);
let h2 = h1.clone();

let _g1 = h1.borrow();
let _g2 = h2.borrow();  // PANICS — already borrowed (even though both are shared)
```

**Pinning:** `pin()` / `pin_mut()` on `RcSlot` are deprecated in 2.3.5 and
removed in 2.4.0 for the same reason as on `Slot`: once the guard drops,
`borrow_mut()` plus `mem::replace` can move the value out from under the
`Pin`. For `T: Unpin`, `Pin::new(handle.borrow_mut())` is correct.

## Performance

See [BENCHMARKS.md](./BENCHMARKS.md) for full methodology and numbers.

Pinned to core 0. Batched timing (64 ops per rdtsc pair), 10K samples.

### Churn — alloc + deref + free (cycles p50)

| Size | Slab | Box | Speedup |
|------|------|-----|---------|
| 32B | **1** | 15 | **15x** |
| 64B | **2** | 17 | **8.5x** |
| 128B | **4** | 23 | **5.8x** |
| 256B | **7** | 29 | **4.1x** |
| 512B | **14** | 44 | **3.1x** |
| 1024B | **25** | 103 | **4.1x** |
| 4096B | **78** | 249 | **3.2x** |

### Free (cycles p50)

| Size | Slab | Box |
|------|------|-----|
| 32B-4096B | **0-1** | 23-26 |

Slab free is sub-cycle regardless of size — a single freelist pointer
write. Box free is constant at ~24 cycles (allocator bookkeeping).

Assembly-verified placement new: `alloc()` compiles to freelist pop +
SIMD store directly into slot memory. No intermediate copy.

## Bounded vs Unbounded

| | Bounded | Unbounded |
|---|---------|-----------|
| Capacity | Fixed at init | Grows via chunks |
| Full behavior | `Err(Full)` | Always succeeds |
| Alloc latency | ~2 cycles | ~2 cycles (LIFO from current chunk) |
| Growth | Never | New chunk (~40 cycle p999) |

Use bounded when you know your capacity. Use unbounded when you need
overflow headroom without crashing.

## Architecture

### Pointer Provenance

Freelist pointers are derived from `UnsafeCell` for correct write provenance under stacked borrows. This ensures that miri accepts the freelist manipulation as valid -- pointers written into vacant slots carry the correct provenance tag from the `UnsafeCell` wrapping the union, not from a stale read-only reference.

### SlotCell (SLUB-style union)

```rust
#[repr(C)]
union SlotCell<T> {
    next_free: *mut SlotCell<T>,  // vacant: freelist link
    value: ManuallyDrop<MaybeUninit<T>>,  // occupied: user data
}
```

No tag, no metadata. Writing a value overwrites the freelist pointer.
The `Slot` handle is the proof of occupancy.

### Unbounded Builder

```rust
use nexus_slab::unbounded::Builder;

// SAFETY: caller guarantees slab contract
let slab = unsafe {
    Builder::new()
        .chunk_capacity(4096)
        .initial_chunks(4)
        .build::<Order>()
};
```

## Features

| Feature | Default | Description |
|---------|---------|-------------|
| `std` | yes | Enables `alloc` + `thread::panicking()` for debug leak detection |
| `alloc` | with `std` | `Vec`-backed storage. Required for slab operation. |
| `rc` | no | Reference-counted handles (`rc::bounded::Slab`, `rc::unbounded::Slab`) with borrow guards |

`no_std` with `alloc` is supported for embedded systems.

## License

MIT OR Apache-2.0
