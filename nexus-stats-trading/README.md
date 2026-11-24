# nexus-stats-trading

Trading and market-microstructure statistics for [nexus-stats](https://crates.io/crates/nexus-stats).

Streaming measures of how a market is behaving, each fed one price, return or trade at a time in fixed memory. Every type follows its published definition, and is checked against a reference implementation where one exists.

This is not a technical-analysis library: there are no chart indicators here. It covers what a trading system needs to measure, market microstructure included.

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` protects the state.** A type has one when some input does damage that outlasts the sample, or when `update` drops a sample you should be told about (a NaN it ignores, a timestamp that goes back). It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reader reports what the arithmetic gives,** NaN included where the true answer is undefined. It never substitutes a number. The library protects the state. It does not promise a reading is never NaN.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.
- **A windowed type with running totals reports its own accuracy.** `update` returns `Accuracy`. A reading that is given is sound. `resync()` is never run for you.

**Not yet migrated:** `Cvar`, `KyleLambda`. They have not been moved to these guarantees. Most still validate in `update` and return a `Result`.

## Which type do I use?

**Is the price trending or reverting?**

- **VarianceRatio**: Lo and MacKinlay's ratio, with a test statistic that says whether the departure from a random walk could be chance (requires `alloc` + (`std` or `libm`))

**How volatile is it?**

- **TwoScaleRv**: realized variance from tick data, with the noise of bid-ask bounce taken out (requires `alloc` + (`std` or `libm`))
- **BipowerVariation**: realized variance split into a continuous part and a jump part (requires `std` or `libm`)

**What does it cost to trade?**

- **Amihud**: illiquidity, the price move per unit traded
- **RollSpread**: the effective spread, from trade prices alone (requires `std` or `libm`)
- **KyleLambda**: price impact per unit of signed volume (requires the `regression` feature, on by default)

**How much risk is in the tail?**

- **Lpm**: lower partial moments, such as semivariance
- **Cvar**: conditional value at risk, the expected loss beyond a quantile

Each type's docs give its definition, how to read it, and an example.

## Example

```rust
use nexus_stats_trading::{Accuracy, VarianceRatio};

// Compare 5-period with 1-period variance over the last 200 returns.
let mut vr = VarianceRatio::builder().horizon(5).window(200).build().unwrap();

let mut price = 100.0_f64;
for i in 0..500_i32 {
    price *= 1.0 + 0.001 * f64::from(i % 7 - 3);
    // `update` says when rounding in its running totals needs clearing.
    // Until `resync` is called there is no reading.
    if let Accuracy::ResyncRequired { .. } = vr.update(price) {
        vr.resync(); // costs the window: schedule it off the hot path
    }
}

if let Some(estimate) = vr.estimate() {
    // A ratio near 1 is a random walk. `|z|` above about 2 says the
    // departure is unlikely to be chance.
    println!("ratio {:.3}, z {:.2}", estimate.ratio, estimate.z_statistic);
}
```

## Features

| Feature | Default | Enables |
|---------|---------|---------|
| `std` | yes | `sqrt` and `ln` from the standard library; implies `alloc` |
| `alloc` | no (implied by `std`) | the windowed types, `VarianceRatio` and `TwoScaleRv` (with `std` or `libm`) |
| `libm` | no | pure Rust `sqrt` and `ln` for `no_std` |
| `regression` | yes | `KyleLambda`, and with it the `nexus-stats-regression` crate |

`Accuracy`, `ConfigError` and `DataError` are re-exported, so this crate can be used without depending on `nexus-stats-core` directly.

## Usage

Enable the `trading` feature on `nexus-stats` for unified import paths:

```rust,ignore
use nexus_stats::trading::VarianceRatio;
```

Or depend on this crate directly:

```rust
use nexus_stats_trading::VarianceRatio;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
