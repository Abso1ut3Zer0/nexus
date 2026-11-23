# nexus-stats-smoothing

Smoothers for [nexus-stats](https://crates.io/crates/nexus-stats): each takes a sample and returns the smoothed value, in fixed memory.

## Which smoother?

Start with **Ema**, an exponential moving average. It is usually the right answer. Move off it for a reason:

- **EwmVar**: the spread around the average too (exponentially weighted mean and variance)
- **AsymEma**: an average that rises and falls at different speeds
- **Slew**: follows the input, but moves only so far per sample
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
