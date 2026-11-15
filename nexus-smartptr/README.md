# nexus-smartptr

Inline smart pointers for `?Sized` types.

- **`Flat<T, B>`** — inline only. Panics if the value doesn't fit.
- **`Flex<T, B>`** — inline with heap fallback. Never panics.

`B` is a buffer marker type (`B32`, `B64`, etc.) whose name is the total
size in bytes. `size_of::<Flat<dyn Trait, B32>>() == 32`.

See the [crate documentation](src/lib.rs) for usage.

## Acknowledgements

The fat pointer decomposition approach is inspired by
[smallbox](https://github.com/andylokandy/smallbox). Like smallbox,
we rely on the de facto stable `(data, metadata)` fat pointer layout
and validate it at build time. We diverge in storage design — smallbox
keeps metadata in a persistent `NonNull<T>`, while nexus-smartptr
decomposes into an opaque `Metadata` word stored inline alongside
the value, giving exact-size-class structs
(`size_of::<Flat<dyn Trait, B32>>() == 32`).
