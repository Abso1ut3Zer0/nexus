# Runtime vs Const-Generic Window Sizes

Some algorithms use a window or buffer: MOSUM, WindowedMedian, KAMA,
BoolWindow. These need to know the size of the buffer.

## Two Options

### Const Generic (default, no alloc)

```rust
// Window size known at compile time
let mut mosum = Mosum::<64>::builder(target)
    .threshold(50.0)
    .build().unwrap();
```

- Buffer is stack-allocated: `[f64; 64]`
- No heap allocation ever
- Size must be a compile-time constant
- Works in `no_std` with no `alloc`

### Runtime-Sized (requires `alloc` feature)

```toml
[dependencies]
nexus-stats = { version = "1.0", features = ["alloc"] }
```

```rust
// Window size from configuration / runtime
let window_size = config.mosum_window;
let mut mosum = Mosum::builder(target)
    .window_size(window_size)
    .threshold(50.0)
    .build().unwrap();
```

- Buffer is heap-allocated once in `build()` — no allocation after that
- Size can come from config files, command line, etc.
- Requires the `alloc` crate (available in most environments)

## When to Use Which

| Situation | Use |
|-----------|-----|
| Embedded / kernel / no heap | Const generic |
| Config-driven parameters | Runtime (`alloc`) |
| Need to change window size without recompiling | Runtime (`alloc`) |
| Maximum performance (compile-time optimization) | Const generic |

## Both Are Zero-Allocation After Init

Both variants allocate their buffer exactly once — at construction time.
The const-generic variant puts it on the stack, the runtime variant puts
it on the heap. After `build()`, both are allocation-free.
