# Unsafe Code & Soundness Guarantees

This document describes every category of unsafe code in nexus-rt, the
invariants that make each one sound, and how we verify those invariants
under miri. nexus-rt is the single-threaded dispatch runtime — it has
significantly less unsafe surface than nexus-async-rt because it has no
TLS-stored raw pointer patterns and no cross-thread waker lifecycle.

---

## Guiding Principles

1. **Every unsafe block has a SAFETY comment.**
2. **Every unsafe pattern has miri coverage** (11 tests in `miri_tests.rs`).
3. **No TLS raw pointer patterns** — unlike nexus-async-rt, nexus-rt
   doesn't store raw pointers in TLS that survive `&mut self` reborrows.
   No `UnsafeCell` wrapping is needed.

---

## Unsafe Code Categories

### 1. World Resource Storage (world.rs) — 35 unsafe blocks

The World stores type-erased resources as `Box<ResourceCell<T>>` behind
`ResourceId` (a `NonNull<u8>` wrapper). All resource access goes through
this pointer.

**Lifecycle:**
```
register(value: T)
  → Box::new(ResourceCell { value, changed_at })
  → Box::into_raw → NonNull::new_unchecked
  → stored in HashMap<TypeId, ResourceId>

resource::<T>()
  → id.as_ptr() as *const ResourceCell<T> → &T

resource_mut::<T>()
  → id.as_ptr() as *mut ResourceCell<T> → &mut T

World::drop
  → Box::from_raw(ptr as *mut ResourceCell<T>) → dropped
```

**Key invariants:**
- `ResourceId` is created from a `Box::into_raw` — the pointer is valid
  for the lifetime of the World (the Box is never freed until World drops).
- The `TypeId` key in the HashMap ensures the cast back to
  `*const ResourceCell<T>` uses the correct `T`. A wrong `T` would be a
  type confusion bug, but the HashMap is keyed by `TypeId::of::<T>()` so
  this can't happen through the public API.
- `resource_mut` takes `&mut World`, which is single-threaded exclusivity.
  No concurrent access to the same `ResourceCell` is possible.
- `drop_resource` reconstitutes the `Box` exactly once per resource.
  Double-free is prevented by the HashMap: each TypeId has exactly one
  entry, removed during drop iteration.

**Why this is NOT the UnsafeCell pattern:**
The `ResourceId` pointer is created at registration time and stored in
the handler's pre-resolved state. It's never stored in TLS. There's no
pattern where a raw pointer to a World field outlives an `&mut World`
reborrow — the pointer points to HEAP memory (the Box), not to a field
of the World struct.

**Miri coverage:** 9 tests in `tests/miri_tests.rs` — insert/get
roundtrip, resource_mut, multiple resources coexist, drop verification
with DropTracker, heap resource drop (String), rebuild after drop, many
resources (8 types), stress cycle (10 iterations).

### 2. Template ZST Dispatch (template.rs) — 21 unsafe blocks

Templates use `mem::zeroed::<F>()` to construct a zero-sized function
item. Named function types in Rust are ZSTs — they have exactly one
value and no bytes. `mem::zeroed()` on a ZST is sound because there are
no bytes to initialize.

**Key invariant:**
```rust
const { assert!(size_of::<F>() == 0) }
```
This compile-time assertion rejects closures (which capture state and
have non-zero size) and function pointers (which are pointer-sized).
Only named function items pass.

**Why `mem::zeroed` and not `MaybeUninit`:**
A ZST has size 0 — `mem::zeroed()` writes zero bytes (a no-op). The
function item type has exactly one valid value (the function itself),
and since there are zero bytes, any bit pattern (including all-zeros)
is that value. `MaybeUninit` would work but adds ceremony for a
zero-byte type.

**Miri coverage:** Exercised indirectly through handler/pipeline tests
that use template-based dispatch. The compile-time `size_of` assertion
is the primary safety mechanism — miri can't catch a compile error.

### 3. View Lifetime Erasure (view.rs) — 10 unsafe blocks

The `with_view` function constructs a `ViewType<'a>` (borrowing from
the source), then casts it to `&StaticViewType` (`'static` stand-in)
for trait resolution. This is a scoped lifetime transmute — the same
pattern used by `std::thread::scope`.

**Key invariants:**
- `ViewType<'a>` and `StaticViewType` are the same struct with different
  lifetime parameters. Layout equivalence is required by the `unsafe trait
  View` contract.
- The source outlives the entire `with_view` call — the borrow is valid.
- The `for<'a> FnOnce(&'a ...)` bound prevents the closure from storing
  the reference (it must work for ANY lifetime, so it can't assume `'static`).
- The view is dropped after the closure returns — no escape.

**Rust language limitation:** `repr(Rust)` types are not formally
guaranteed to have identical layout across lifetime parameters. All
current compilers maintain this property. Users of the `#[derive(View)]`
macro (or manual impls) should apply `#[repr(C)]` to view structs with
borrowed fields for guaranteed layout stability. This is documented in
the trait's safety comment.

**Miri coverage:** Exercised indirectly through pipeline view scope
tests. The view itself is safe code — the unsafe is only in the pointer
cast inside `with_view`.

### 4. Reactor Dispatch (reactor.rs) — 11 unsafe blocks

The reactor system moves handlers out of a slab for dispatch, then
returns them after firing. Raw pointers are used to work around the
borrow checker's inability to express "borrow this slab slot, move the
value out, call a method, move it back."

**Key invariants:**
- `ReactorNotify` is accessed through `get_mut()` on a pre-resolved
  `ResourceId`. Single-threaded — no concurrent access.
- Handler moved out via `ManuallyDrop::take`, fired, then put back.
  If the handler panics, the slot is left empty (the handler is consumed).
- `SourceRegistry` downcasts use `.expect("invariant: TypeId matches")`
  instead of `.unwrap()` — the invariant is documented.

**Miri coverage:** Not directly — reactor dispatch requires IO readiness
events (mio). Covered by integration tests.

### 5. Handler HRTB Dispatch (handler.rs) — 28 unsafe blocks

The `call_inner` helper bridges the HRTB double-bound pattern — it
binds a concrete lifetime at the call site so the function pointer can
be invoked with the correct types. This uses `unsafe` for the function
call through a type-erased pointer.

**Key invariants:**
- The function pointer stored in `Callback<C, F, P>` is the same `F`
  that was provided at construction. The ZST enforcement
  (`size_of::<F>() == 0`) prevents type confusion.
- Parameter state (`P::State`) is resolved at handler creation time
  and stored inline. `Param::fetch` dereferences the pre-resolved
  `ResourceId` pointers — same safety as World resource access.

**Miri coverage:** Exercised through the extensive handler/pipeline test
suite (391 inline tests). The unsafe is function dispatch, which every
handler test exercises.

### 6. Pipeline/DAG Combinators (pipeline.rs, dag.rs) — 16 unsafe blocks

Opaque step wrappers (`OpaqueStep`, `OpaqueHandler`) hold `&mut World`
closures and dispatch through function pointers. The unsafe is in the
call-through — same pattern as handler dispatch.

**Key invariant:** The `Opaque` marker type prevents overlap with the
`Param`-resolved path. The compiler proves coherence — no runtime check
needed.

**Miri coverage:** Exercised through pipeline/dag tests.

### 7. Dispatch Payload Unwrap (dispatch.rs) — 2 unsafe blocks

`#[derive(Dispatchable)]` + `.dispatch_variant` (issue #723) route an enum to a
per-variant arm through a flat dispatch table indexed by the value's dense
`ordinal()`. Each arm receives its variant's **typed payload**, extracted by the
derive-generated `VariantOf::unwrap`. That unwrap is the feature's only unsafe:

```rust
// Generated by the derive, per variant:
unsafe fn unwrap(e: Cmd) -> Self::Payload {
    match e {
        Cmd::RouteAway(f0) => f0,
        _ => {
            debug_assert!(false, "Dispatchable unwrap on wrong variant");
            unsafe { core::hint::unreachable_unchecked() }
        }
    }
}
```

It is called from exactly one hand-written unsafe block — inside the shared
`VariantArm` thunk (`dispatch.rs`), reached by both its `StepCall` impl (plain
pipeline) and its `CtxStepCall` impl (ctx pipeline, threading `&mut C`):

```rust
// SAFETY: this slot is indexed by input.ordinal(), so input is variant V.
let payload = unsafe { V::unwrap(input) };
```

**Key invariant:** the arm for ordinal *i* is stored in table slot *i*, and the
slot is reached **only** when `input.ordinal() == i`. So whenever `V::unwrap` runs,
`input` provably **is** variant `V` — the `_` arm (and its `unreachable_unchecked`)
is never taken. The dispatch key comes from the value's own discriminant, so
there is no way for a caller to route a value to the wrong arm.

- In **debug** builds the `debug_assert!` fires *before* `unreachable_unchecked`,
  turning an invariant violation into a panic rather than UB — a guard against a
  future refactor breaking the index/slot correspondence.
- `.dispatch_on` has **no** unsafe: its arms receive the whole value (a
  projection carries no variant guarantee), so there is nothing to unwrap.

**Why `unreachable_unchecked` and not a panic in release:** the branch is
provably dead given the invariant, so eliding it lets LLVM treat the `match` as
the single reachable arm — a plain move-out of the payload, no discriminant
re-check after the table already selected the arm by ordinal.

**Miri coverage:** 2 tests in `tests/miri_tests.rs` drive a value of *every*
variant shape (unit, single-field, and a heap-carrying `(u32, String)` tuple, so
the move-out is a genuine non-`Copy` ownership transfer) through a built pipeline
and assert the correct typed payload emerges — `dispatch_variant_unwraps_each_variant_shape`
(Pipeline) and `ctx_dispatch_variant_unwraps_each_variant_shape` (CtxPipeline).
Miri runs with `debug_assertions` on, so the guard stays active and the happy
path never reaches `unreachable_unchecked`; the invariant-violation path is
unreachable without breaking dispatch and is therefore not (and cannot soundly
be) tested.

---

## What nexus-rt Does NOT Have

Unlike nexus-async-rt, nexus-rt has:

- **No TLS-stored raw pointers** — no waker queue, no cross-thread wake
- **No refcount lifecycle** — resources are owned by World, handlers are
  owned by the caller
- **No union transitions** — no future/output overlapping storage
- **No intrusive linked lists** — no waiter nodes, no Treiber stacks
- **No cross-thread anything** — `!Send`, `!Sync`, single-threaded by design

This dramatically reduces the unsafe surface. The primary risk is the
`ResourceId` type-erasure pattern, which is well-established (same as
ECS systems like Bevy) and fully covered by miri.

---

## Miri Testing

```bash
# Run all miri tests (~2 seconds)
MIRIFLAGS="-Zmiri-ignore-leaks" cargo +nightly miri test -p nexus-rt --test miri_tests
```

`-Zmiri-ignore-leaks` is included for consistency with the workspace
miri convention. World uses `Box::into_raw` / `Box::from_raw` (not
`Box::leak`) — resources are properly freed in `World::drop`. The flag
is harmless but not strictly required for nexus-rt alone.

### Test inventory

| Test | What it covers |
|------|---------------|
| `world_resource_insert_get_roundtrip` | NonNull cast roundtrip: register → get |
| `world_resource_mut` | Mutable access through NonNull cast |
| `world_multiple_resources_coexist` | Multiple ResourceIds don't alias |
| `world_drop_drops_resources` | Box reconstitution in World::drop (3 types) |
| `world_drop_drops_heap_resources` | Heap-allocated resource (String) freed on drop |
| `world_rebuild_after_drop` | Full lifecycle: build → use → drop → rebuild |
| `world_change_detection` | ResourceCell tick stamping through mutable access |
| `world_many_resources` | 8 resource types — HashMap<TypeId> pressure |
| `world_stress_register_mutate_drop` | 10 cycles of register/mutate/drop with DropTracker |
| `dispatch_variant_unwraps_each_variant_shape` | `VariantOf::unwrap` over every variant shape (unit/single/heap tuple) via a Pipeline |
| `ctx_dispatch_variant_unwraps_each_variant_shape` | Same, through the shared `VariantArm`'s `CtxStepCall` impl (threads `&mut C`) |

---

## Adding New Unsafe Code

1. **Check if you actually need unsafe.** nexus-rt's design avoids most
   patterns that require it. If you're reaching for raw pointers, ask
   whether a safe abstraction (handler params, view scopes, pipeline
   combinators) already covers your use case.

2. **Write the SAFETY comment before the code.**

3. **Add a miri test** to `tests/miri_tests.rs`. Keep it simple — miri
   finds UB on the first iteration.

4. **Run miri locally:**
   ```bash
   MIRIFLAGS="-Zmiri-ignore-leaks" cargo +nightly miri test -p nexus-rt --test miri_tests
   ```

5. **Do NOT introduce TLS raw pointer patterns** without `UnsafeCell`.
   See `nexus-async-rt/docs/UNSAFE_AND_SOUNDNESS.md` for why this matters.
   nexus-rt currently avoids this entirely — keep it that way.
