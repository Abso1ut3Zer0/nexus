# nexus-stats-smoothing

Smoothers for [nexus-stats](https://crates.io/crates/nexus-stats): each takes a sample and returns the smoothed value, in fixed memory.

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` exists only where it has a job.** A type has one when some input can leave it unable to give a right reading until `reset()`. It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.

**Not yet migrated:** `Hampel`, `Kama`, `WindowedMedian`. They have not been moved to these guarantees. Most still validate in `update` and return a `Result`.

## Which smoother?

Start with **Ema**, an exponential moving average. It is usually the right answer. Move off it for a reason:

- **EwmVar**: the spread around the average too (exponentially weighted mean and variance)
- **AsymEma**: an average that rises and falls at different speeds
- **Slew**: a slew rate limiter; follows the input, but moves only so far per sample
- **Holt**: the signal has a trend, and an average lags it
- **Kama**: it swings between trending and ranging (requires `alloc`)
- **Spring**: a moving target chased without overshoot
- **HuberEma**: outliers, with each step bounded
- **Hampel**: outliers, shrunk or rejected (requires `alloc`)
- **WindowedMedian**: outliers, up to half the window ignored (requires `alloc`)

Each type's docs give its definition, how to choose its parameters, and an example.

## Example

```rust
use nexus_stats_smoothing::Ema;

let mut ema = Ema::builder().alpha(0.5).build().unwrap();
assert_eq!(ema.update(10.0), Some(10.0));
assert_eq!(ema.update(20.0), Some(15.0)); // half the way
```

## Usage

Enable the `smoothing` feature on `nexus-stats` for unified import paths:

```rust,ignore
use nexus_stats::smoothing::Holt;
```

Or depend on this crate directly:

```rust
use nexus_stats_smoothing::Holt;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
