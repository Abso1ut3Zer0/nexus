# Unsafe audit open items

Items that could not be fully verified during the SAFETY comment pass.
Each entry has a crate, file, approximate line, and the specific question.

---

## nexus-shm

### 1. Post-Release payload writes in `ShmSlotWriter::create` and `ShmRingWriter::create`

**File:** `nexus-shm/src/slot.rs` (`ShmSlotReader::attach`, line ~135)
**File:** `nexus-shm/src/ring.rs` (`read_capacity` / `read_elem_size`, lines ~26-31)

**Issue:** `ShmSlotWriter::create` and `ShmRingWriter::create` both write
`elem_size` (and `capacity` in the ring case) to the payload *after*
`Segment::create_file` returns. `Segment::create_file` stores `status=ALIVE`
with `Ordering::Release` inside `ControlBlock::write_header`. Because the
payload writes happen after that Release, a reader that Acquire-loads
`status=ALIVE` in `Segment::attach` is not formally guaranteed to observe
those payload writes under the C11 memory model.

**In practice:** On x86 (TSO), stores are globally visible in program order.
On ARM/POWER, the page-cache coherency mechanism and the fact that the reader
typically opens the file only after the writer process has finished `create()`
provide de-facto ordering. However, this relies on OS-level happens-before
(filesystem open/close), not the Rust/C11 memory model.

**Fix:** Move the `elem_size`/`capacity` writes to before the Release store
of `status=ALIVE`, i.e., initialize the payload header inside `Segment::create`
(or via a callback) before `write_header` is called. This would make the
Acquire/Release pair formally sufficient.

**Risk level:** Low in practice (x86 Linux), but not formally sound.

**Tracking:** #625

---

### 2. Ring slot alignment in `slot_ptr` (`ShmRingWriter`/`ShmRingReader`)

**File:** `nexus-shm/src/ring.rs` (`slot_ptr`, line ~53)

**Issue:** `slot_ptr` casts a byte pointer offset by `DATA_OFFSET + slot_idx * size_of::<T>()`
to `*mut T`. The assert in `ShmRingWriter::create` checks `align_of::<T>() <= DATA_OFFSET`
(192), but `DATA_OFFSET = 192` is not a power of two (192 = 64 * 3). A slot at offset 192
is only 64-aligned: `192 mod 128 = 64`, so any `Pod` type with `align_of == 128` passes the
assert but lands on a misaligned address. The `copy_nonoverlapping` and `read` calls at the
call sites then operate on a misaligned pointer, which is UB.

**In practice:** No in-tree `Pod` type exceeds `align_of == 16` (the maximum for `f64`/`u128`),
so this is latent. It becomes reachable via a user-defined `#[repr(align(128))]` type that
implements `Pod`.

**Fix:** Change the assert to require `align_of::<T>().is_power_of_two() && DATA_OFFSET % align_of::<T>() == 0`,
or adjust `DATA_OFFSET` to the next power-of-two boundary (256).

**Risk level:** Low in practice (no in-tree type triggers it), but unsound by construction.

**Tracking:** #624
