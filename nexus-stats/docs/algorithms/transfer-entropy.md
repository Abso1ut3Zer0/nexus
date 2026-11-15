# Transfer Entropy — Directed Information Flow

Directed information flow between two discretized streams. "Does
knowing X's past reduce uncertainty about Y's future?" Non-parametric
Granger causality.

| Property | Value |
|----------|-------|
| Update cost | ~14 cycles |
| Memory | `2×bins³×8 + 2×bins²×8 + 2×lag×8` bytes (heap) |
| Types | `TransferEntropy` |
| Priming | After `lag + 1` paired observations |
| Output | `te_x_to_y()`, `te_y_to_x()`, `net_flow()` — all `Option<f64>` |
| Feature | `alloc` + (`std` or `libm`) |

## What It Does

Measures the transfer entropy in both directions between two
streams simultaneously:

```
TE(X→Y) = H(Y_t | Y_{t-lag}) - H(Y_t | Y_{t-lag}, X_{t-lag})
```

Positive TE(X→Y) means knowing X's past reduces uncertainty about
Y's future — X provides predictive information about Y beyond what
Y's own history provides.

`net_flow()` = TE(X→Y) - TE(Y→X). Positive means X leads Y.
Negative means Y leads X. Near zero means symmetric coupling or
independence.

## When to Use It

**Use TransferEntropy when:**
- You need to determine WHICH signal drives the other
- Cross-correlation shows a relationship but you need directionality
- You want a non-parametric (model-free) causality measure

**Don't use TransferEntropy when:**
- You just need correlation at a lag → use [CrossCorrelation](cross-correlation.md) (much cheaper)
- Your data is continuous and you can't discretize meaningfully
- Memory is extremely constrained (tables grow cubically with bins)

## How It Works

```
State:
  joint_xy[bins³]     — P(X_{t-lag}, Y_{t-lag}, Y_t) counts
  joint_yx[bins³]     — P(Y_{t-lag}, X_{t-lag}, X_t) counts
  marginal_y[bins²]   — P(Y_{t-lag}, Y_t) counts
  marginal_x[bins²]   — P(X_{t-lag}, X_t) counts
  prev_x[lag], prev_y[lag] — circular history buffers

On each paired observation (x_bin, y_bin):
  // Retrieve lagged values from circular buffers
  x_lagged = prev_x[lag steps ago]
  y_lagged = prev_y[lag steps ago]

  // Update joint and marginal tables
  joint_xy[x_lagged][y_lagged][y_bin] += 1
  joint_yx[y_lagged][x_lagged][x_bin] += 1
  marginal_y[y_lagged][y_bin] += 1
  marginal_x[x_lagged][x_bin] += 1

  // Store current values in history
  prev_x.push(x_bin)
  prev_y.push(y_bin)

TE(X→Y) query (O(bins³)):
  For each (a, b, c) where joint_xy[a][b][c] > 0:
    TE += P(a,b,c) × ln(P(a,b,c) × P(b) / (P(b,c) × P(a,b)))
```

## Configuration

```rust
use nexus_stats::signal::TransferEntropy;

let mut te = TransferEntropy::builder()
    .bins(8)    // 8 categories per stream
    .lag(1)     // compare with 1 step ago
    .build()
    .unwrap();

for (x_bin, y_bin) in discretized_data {
    te.observe(x_bin, y_bin);
}

if let Some(flow) = te.net_flow() {
    if flow > 0.01 {
        println!("X leads Y (TE = {flow:.4})");
    } else if flow < -0.01 {
        println!("Y leads X (TE = {:.4})", -flow);
    } else {
        println!("no significant directional flow");
    }
}
```

`bins` and `lag` are runtime-configured via the builder. Both are
validated: `bins >= 2`, `lag >= 1`.

### Memory Budget

Both `bins` and `lag` are runtime parameters. The cubic growth of
the frequency tables means `bins` dominates memory:

| bins | lag | Memory |
|------|-----|--------|
| 4 | 1 | ~1.3 KB |
| 8 | 1 | ~9 KB |
| 8 | 4 | ~9 KB |
| 16 | 1 | ~131 KB |

`lag` adds only `2 × lag × 8` bytes for the history buffers —
negligible compared to the tables.

### Choosing bins

Too few bins loses resolution (can't distinguish subtle effects).
Too many bins requires exponentially more data to populate the
joint table. Rules of thumb:

- **4 bins**: quartile-based discretization, works with ~1000 samples
- **8 bins**: octile, works with ~10000 samples
- **16 bins**: fine resolution, needs ~100000+ samples

### Choosing lag

`lag` controls how far back to look. `lag=1` asks "does X one step
ago predict Y now?" `lag=3` asks "does X three steps ago predict Y
now?" Different causal mechanisms have different propagation delays.

If you don't know the lag, run [CrossCorrelation](cross-correlation.md)
first to find the peak lag, then use that as the `lag` parameter.

## Examples by Domain

### Monitoring — Causal Relationship Detection

```rust
// Which metric drives the other?
let mut te = TransferEntropy::builder()
    .bins(8)
    .lag(1)
    .build()
    .unwrap();

// Discretize metrics into 8 bins (e.g., by quantile)
te.observe(metric_a_bin, metric_b_bin);

// Positive net_flow → metric A drives metric B
```

### Monitoring — Root Cause Detection

```rust
// Is high CPU causing high latency, or vice versa?
let mut te = TransferEntropy::builder()
    .bins(4)
    .lag(2)
    .build()
    .unwrap();

// Discretize both metrics into quartiles
te.observe(cpu_quartile, latency_quartile);

// net_flow > 0 → CPU drives latency (expected)
// net_flow < 0 → latency drives CPU (unexpected — investigate)
```

## Cross-Correlation vs Transfer Entropy

See [CrossCorrelation](cross-correlation.md#cross-correlation-vs-transfer-entropy)
for a detailed comparison. In short: use cross-correlation to find
the lag, use transfer entropy to confirm which signal drives which.

## Performance

| Operation | p50 |
|-----------|-----|
| `observe` (bins=8, lag=1) | ~14 cycles |
| `te_x_to_y()` query (bins=8) | ~500 cycles |
| `net_flow()` query (bins=8) | ~1000 cycles |

The update is O(1) — table lookups and increments. The query is
O(bins³) due to iterating the joint frequency table.

## Academic Reference

Schreiber, T. "Measuring Information Transfer." *Physical Review
Letters* 85.2 (2000): 461-464.
