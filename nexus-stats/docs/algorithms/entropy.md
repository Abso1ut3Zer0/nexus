# Entropy — Shannon Entropy over Categorical Distributions

Online Shannon entropy estimation. "How predictable is this signal?"

| Property | Value |
|----------|-------|
| Update cost | 3 cycles |
| Memory | `8×K + 8` bytes |
| Types | `Entropy` |
| Priming | After 1 observation |
| Output | `entropy()`, `entropy_bits()`, `surprise(cat)`, `probability(cat)` — all `Option` |
| Feature | `std` or `libm` (needs `ln`) |

## What It Does

Maintains frequency counts for K categories and computes Shannon
entropy on query:

```
H(X) = -sum(p_i × ln(p_i))  where p_i = count_i / total
```

- **Low entropy** = concentrated distribution = predictable signal
- **High entropy** = uniform distribution = maximum uncertainty
- **Maximum** = ln(K) (when all categories are equally likely)

Also provides **surprise** (self-information) for individual
observations: `-ln(p_i)`. Rare events have high surprise.

## When to Use It

**Use Entropy when:**
- You want to measure signal predictability or diversity
- You want to detect regime changes via entropy shift
- You need per-observation anomaly scoring (surprise)
- Your data is naturally categorical or can be discretized

**Don't use Entropy when:**
- You need continuous distribution analysis → use [Moments](moments.md)
- You need directed information flow → use [TransferEntropy](transfer-entropy.md)
- You need correlation → use [Autocorrelation](autocorrelation.md) or [CrossCorrelation](cross-correlation.md)

## How It Works

```
State:
  counts[K]  — frequency count per category
  total      — sum of all counts

On each observation (category i):
  counts[i] += 1
  total += 1

Entropy query (O(K)):
  H = 0
  for i in 0..K:
    if counts[i] > 0:
      p = counts[i] / total
      H -= p × ln(p)
  return H
```

The update is O(1) — one integer increment. The entropy query is
O(K), but K is const and typically small (4-32).

## Configuration

```rust
use nexus_stats::signal::Entropy;

// 8 categories
let mut e = Entropy::builder().bins(8).build().unwrap();

for category in observations {
    e.update(category);
}

println!("entropy: {:.3} nats", e.entropy().unwrap());
println!("entropy: {:.3} bits", e.entropy_bits().unwrap());
```

`bins` determines the frequency table size and is set at construction
time via the builder. Categories must be in `0..bins`. Out-of-range panics.

### Surprise Scoring

```rust
// How unusual was this observation?
e.update(rare_category);
if let Some(s) = e.surprise(rare_category) {
    // High surprise = rare event
    println!("surprise: {s:.2} nats");
}
```

## Examples by Domain

### Trading — Order Flow Diversity

```rust
// Discretize order sizes into buckets
let mut e = Entropy::builder().bins(4).build().unwrap();

// 0 = small, 1 = medium, 2 = large, 3 = very large
let bucket = match order_size {
    0..=100     => 0,
    101..=1000  => 1,
    1001..=10000 => 2,
    _           => 3,
};
e.update(bucket);

// Low entropy = concentrated in one bucket → predictable behavior
// High entropy = diverse distribution → normal variation
```

### Monitoring — Signal Predictability

```rust
// Discretize latency into ranges
let mut e = Entropy::builder().bins(8).build().unwrap();

let bucket = (latency_us / 100).min(7) as usize;
e.update(bucket);

// Entropy drop = distribution concentrating = more predictable
// Entropy spike = distribution spreading = less predictable
```

### Networking — Traffic Classification

```rust
// Track distribution of packet types
let mut e = Entropy::builder().bins(16).build().unwrap();

e.update(packet_type as usize);

// High entropy = diverse traffic (normal)
// Low entropy = dominated by one type (possible attack)
```

## Entropy Units

| Method | Unit | Base | Value for fair coin |
|--------|------|------|---------------------|
| `entropy()` | nats | e | ln(2) ≈ 0.693 |
| `entropy_bits()` | bits | 2 | 1.0 |

Nats are the natural unit (base e). Bits are more common in
information theory. Conversion: bits = nats / ln(2).

## Performance

| Operation | p50 |
|-----------|-----|
| `Entropy::update` (bins=8) | 3 cycles |
| `entropy()` query (K=8) | 106 cycles |
| `surprise(cat)` query | 14 cycles |

The update is a single integer increment. Query cost scales with K
due to the sum over all categories.
