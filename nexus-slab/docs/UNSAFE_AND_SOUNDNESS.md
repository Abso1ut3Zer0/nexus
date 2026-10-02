# Unsafe Code & Soundness Guarantees

This document describes the unsafe code in nexus-slab, the invariants
that make each pattern sound, and how miri testing verifies them. The
slab is the foundational allocator for nexus — most other crates
(collections, async-rt, timer) build on it.

---

## Guiding Principles

1. **The `unsafe` constructor is the opt-in gate.** `Slab::with_capacity`
   is `unsafe` — by creating a slab, you accept manual memory management.
   After construction, all operations are safe (Slot is move-only, no
   Clone/Copy, consumed on free).
2. **43 miri tests** cover every unsafe path including provenance.
3. **One known Rust limitation** (stacked borrows on `Cell<*mut>`) is
   documented and passes tree borrows.

---

## Architecture: SlotCell Union

The core data structure is `SlotCell<T>`, a `repr(C)` union:

```rust
#[repr(C)]
pub(crate) union SlotCell<T> {
    next_free: *mut SlotCell<T>,  // when vacant: freelist pointer
    value: ManuallyDrop<MaybeUninit<T>>,  // when occupied: the value
}
```

**No occupied/vacant tracking.** The `Slot<T>` RAII handle IS the proof
of occupancy. If you hold a `Slot<T>`, the value is live. When you call
`free(slot)`, the slot is consumed (moved), the value is dropped in place,
and the freelist pointer is written — transitioning from occupied to vacant.

This design eliminates a branch on every access (no "check if occupied"
before deref). The type system prevents misuse: `Slot` is move-only, so
double-free is a compile error.

---

## Unsafe Code Categories

### 1. Freelist Pointer Manipulation — bounded.rs, unbounded.rs

Each vacant slot stores a `*mut SlotCell<T>` pointing to the next free
slot. `claim_ptr` pops the head, `free_ptr` pushes back.

**Key invariants:**
- All freelist pointers are derived from `UnsafeCell::get()` at
  construction time — they carry write provenance from the `UnsafeCell`.
- The freelist is never accessed concurrently: the slab is `!Sync`
  (`Cell<*mut SlotCell<T>>`). The slab is `Send`, but moving it moves the
  only access path to the freelist, because every handle is `!Send` and
  stays behind; a stranded handle can touch only its own occupied slot,
  which the slab never reads or writes. The full argument is the SAFETY
  comment on `bounded::Slab`'s `Send` impl.
  No concurrent modification.
- `free()` consumes the `Slot` (move semantics) — double-free is a
  compile error, not a runtime check.
- Cross-slab free is caught by `debug_assert!` (the pointer range check
  in `contains_ptr`).

**Provenance fix (2026-04-12):** `slots_ptr()` was changed from
`(&*self.slots.get()).as_ptr().cast_mut()` (read-only provenance via
`&Vec`) to `(*self.slots.get()).as_mut_ptr()` (write provenance via
`*mut Vec`). The old version derived a `*mut` with read-only provenance
— any write through it was UB. Caught by miri audit.

### 2. SlotCell Union Access — shared.rs

Reading and writing the union fields:

- `write_value(value)` — writes to the `value` field, transitioning
  from vacant to occupied. Sound because the slot was just claimed
  (vacant, freelist pointer is the active field — overwriting is fine).
- `read_value()` → `ManuallyDrop::take` — reads and moves the value
  out. Sound because `Slot<T>` is consumed (caller can't access after).
- `drop_value_in_place()` — drops the value via `ptr::drop_in_place`.
  Called by `free()`. Sound because the slot is occupied (Slot handle
  proves it) and consumed by free.
- `get_next_free()` — reads the freelist pointer. Only called on vacant
  slots (during claim/free operations).

**No runtime field discrimination.** The union field access is always
correct by construction — the API surface makes it impossible to read
`value` on a vacant slot or `next_free` on an occupied slot.

### 3. Unbounded Slab Chunk Growth — unbounded.rs

The unbounded slab grows by allocating new `Vec<SlotCell<T>>` chunks.
Each chunk is independent — no copying, no pointer invalidation.

**Key invariants:**
- Chunks are stored in a `Vec<ChunkEntry<T>>` behind `UnsafeCell`.
  The chunk Vec can reallocate (adding new chunks), but existing
  chunk addresses are stable (each chunk is its own Vec allocation).
- `claim_ptr` searches the `head_with_space` linked list of chunks
  with available slots. If no chunk has space, `grow()` adds one.
- Pointers to slots in existing chunks remain valid across growth
  because chunks are heap-allocated independently.

### 4. Byte Slab Type Punning — byte/bounded.rs, byte/unbounded.rs

The byte slab stores `AlignedBytes<N>` (a `repr(C, align(8))` byte
array) in each slot, then casts to `*mut T` for typed access:

```rust
let slot_ptr: *mut SlotCell<AlignedBytes<N>> = ...;
let data_ptr: *mut T = slot_ptr.cast::<T>();
core::ptr::write(data_ptr, value);
```

**Key invariants:**
- `validate_type::<T, N>()` checks `size_of::<T>() <= N` and
  `align_of::<T>() <= 8` at compile time. The AlignedBytes type is
  `align(8)`, so any T with alignment ≤ 8 is valid.
- The cast from `*mut SlotCell<AlignedBytes<N>>` to `*mut T` is sound
  because `SlotCell` is `repr(C)` with the value field at offset 0.
  The pointer points to the start of the value region.
- `ByteClaim` stores a polymorphic free function pointer
  (`free: unsafe fn(...)`) to handle both bounded and unbounded slab
  deallocation through the same type.

### 5. RC Slab Borrow Tracking — rc/mod.rs

The RC slab wraps each slot in reference counting with borrow tracking.
`RcSlot` is `Clone` (increments refcount), `borrow()` and `borrow_mut()`
use a single-bit borrow flag.

**Key invariants:**
- Refcount prevents use-after-free — the value is dropped only when
  count reaches 0 (via `slab.free(handle)`).
- Borrow bit prevents `&T` and `&mut T` aliasing — only one borrow
  at a time (more conservative than RefCell, which allows multiple
  shared borrows).
- `RcSlot` is `!Send` and `!Sync` (contains `*mut RcCell<T>`) —
  prevents cross-thread access.
- The `Ref<T>` and `RefMut<T>` guards release the borrow bit on Drop.

### 6. Macro-Generated TLS Allocators — via `bounded_allocator!`/`unbounded_allocator!`

The slab macros generate thread-local slab instances with typed `alloc`/
`free` functions. The `#[inline]` on trait impls is critical for
performance — without it, values get memcpy'd through each call boundary.

**Key invariant:** The TLS slab is scoped via `thread_local!` with
`const { }` constructor. Each thread gets its own slab. No cross-thread
access is possible.

---

## Known Provenance Issue: `Cell<*mut SlotCell<T>>` in `&self`

### Stacked borrows limitation

The `free_head: Cell<*mut SlotCell<T>>` field stores a raw pointer that
was derived from `UnsafeCell::get()` at construction time. When
`claim_ptr(&self)` reads this pointer via `Cell::get()`, stacked borrows
may consider the returned pointer value's provenance as "weakened" by the
`&self` retag.

This is a known stacked borrows limitation with `Cell<*mut T>` inside
shared references. **Tree borrows handles it correctly.** The code is
sound — tested and verified under tree borrows.

### Where it manifests

Only in nexus-async-rt's slab allocation path, where the slab is accessed
through a type-erased TLS pointer round-trip (`*const u8` → `*const Slab`
→ `&Slab`). Direct slab usage (as in nexus-collections, nexus-timer) does
not trigger this because the `&self` borrow has the correct provenance.

### Miri commands

```bash
# Default stacked borrows (43 tests)
MIRIFLAGS="-Zmiri-ignore-leaks" cargo +nightly miri test -p nexus-slab --test miri_tests

# Tree borrows (if testing with async-rt slab integration)
MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-ignore-leaks" cargo +nightly miri test -p nexus-slab --test miri_tests
```

---

## Miri Test Inventory

43 tests in `tests/miri_tests.rs`:

| Category | Tests | What they cover |
|----------|-------|----------------|
| Bounded basic | 8 | alloc/free roundtrip, fill capacity, reuse after free, String/Vec drop, deref/deref_mut, into_inner, replace |
| Unbounded basic | 5 | alloc/free, claim/abandon, growth across chunks, String growth |
| Claim lifecycle | 4 | claim + write, claim + abandon, abandon at full chunk, large struct |
| RC slab | 4 | alloc/borrow/free, clone + borrow_mut, rc drop tracking, free-on-last-drop |
| Byte slab | 7 | bounded alloc/write/free, different types in same slot, abandon, unbounded growth, drop tracking, alignment |
| Provenance | 6 | stored-pointer roundtrip (bounded/unbounded), alloc cycle through stored pointer, two-slot interleaved, claim+write through stored pointer, cross-chunk through stored pointer |
| ZST | 1 | zero-sized type allocation |
| Large struct | 1 | 1KB struct alloc/free |
| Drop tracking | 5 | exact drop count verification across all slab variants |

---

## Adding New Unsafe Code

1. **Prefer the existing safe API.** `alloc(value)` → `Slot<T>` → `free(slot)`
   covers 99% of use cases. Reach for `claim_ptr` / `free_ptr` only when
   the macro-generated allocator needs raw access.

2. **Never bypass the Slot handle.** The move-only `Slot<T>` is the type-level
   proof that the slot is occupied. Raw pointer access (via `leak()`,
   `from_key()`, `remove_by_key()`) is `unsafe` for this reason.

3. **Derive pointers from `UnsafeCell::get()`.** Never create `&Vec` from
   `self.slots.get()` then cast to `*mut` — this gives read-only provenance.
   Always use `(*self.slots.get()).as_mut_ptr()`.

4. **Add miri tests.** Run:
   ```bash
   MIRIFLAGS="-Zmiri-ignore-leaks" cargo +nightly miri test -p nexus-slab --test miri_tests
   ```
