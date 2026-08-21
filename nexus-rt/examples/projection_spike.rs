//! Pipeline view scopes — reusable steps via projected views.
//!
//! Demonstrates `.view::<V>()` / `.end_view()` for running shared
//! step functions across different event types that project to the
//! same view.
//!
//! Run with:
//! ```bash
//! cargo run -p nexus-rt --example projection_spike
//! ```

use nexus_rt::{PipelineBuilder, Res, ResMut, Resource, View, World, WorldBuilder};

// =============================================================================
// Domain types
// =============================================================================

#[derive(Resource)]
struct RiskLimits {
    max_qty: u64,
}

#[derive(Resource)]
struct AuditLog {
    entries: Vec<String>,
}

/// Shared view — borrowed fields from the source event. Zero-cost.
struct OrderView<'a> {
    symbol: &'a str,
    qty: u64,
    price: f64,
}

struct AdminCommand {
    source: String,
    symbol: String,
    qty: u64,
    price: f64,
    admin_flags: u32,
}

struct MarketUpdate {
    venue: String,
    symbol: String,
    qty: u64,
    price: f64,
    sequence: u64,
}

// =============================================================================
// View marker + impls
// =============================================================================

/// Marker type selecting the OrderView projection.
struct AsOrderView;

// SAFETY: ViewType<'a> and StaticViewType are the same struct with different
// lifetime parameters; layout is identical. `view` borrows correctly from source.
unsafe impl View<AdminCommand> for AsOrderView {
    type ViewType<'a> = OrderView<'a>;
    type StaticViewType = OrderView<'static>;
    fn view(source: &AdminCommand) -> OrderView<'_> {
        OrderView {
            symbol: &source.symbol,
            qty: source.qty,
            price: source.price,
        }
    }
}

// SAFETY: as above; same struct, different source type.
unsafe impl View<MarketUpdate> for AsOrderView {
    type ViewType<'a> = OrderView<'a>;
    type StaticViewType = OrderView<'static>;
    fn view(source: &MarketUpdate) -> OrderView<'_> {
        OrderView {
            symbol: &source.symbol,
            qty: source.qty,
            price: source.price,
        }
    }
}

// =============================================================================
// Reusable step functions — work on &OrderView, not on any specific event.
// Params first, &View last (same convention as all pipeline ref steps).
// =============================================================================

fn log_order(mut log: ResMut<AuditLog>, v: &OrderView) {
    log.entries
        .push(format!("  [audit] {} qty={} @{}", v.symbol, v.qty, v.price));
}

fn check_risk(limits: Res<RiskLimits>, v: &OrderView) -> bool {
    v.qty <= limits.max_qty
}

// =============================================================================
// Main
// =============================================================================

fn main() {
    let mut wb = WorldBuilder::new();
    wb.register(RiskLimits { max_qty: 100 });
    wb.register(AuditLog {
        entries: Vec::new(),
    });
    let mut world = wb.build();
    let reg = world.registry();

    // Pipeline A: AdminCommand → view as OrderView → route
    //
    // Inside the view scope: log_order and check_risk operate on
    // &OrderView. After end_view_guarded: the full AdminCommand is
    // available (or None if the guard rejected).
    let mut pipeline_a = PipelineBuilder::<AdminCommand>::new()
        .view::<AsOrderView>()
        .tap(log_order, reg)
        .guard(check_risk, reg)
        .end_view_guarded()
        .then(
            |w: &mut World, cmd: Option<AdminCommand>| {
                if let Some(cmd) = cmd {
                    let log = w.resource_mut::<AuditLog>();
                    log.entries.push(format!(
                        "  [route] admin from '{}' flags=0x{:02x}",
                        cmd.source, cmd.admin_flags
                    ));
                }
            },
            reg,
        );

    // Pipeline B: MarketUpdate → SAME view steps, different event type
    let mut pipeline_b = PipelineBuilder::<MarketUpdate>::new()
        .view::<AsOrderView>()
        .tap(log_order, reg) // SAME function as pipeline A
        .guard(check_risk, reg) // SAME function as pipeline A
        .end_view_guarded()
        .then(
            |w: &mut World, update: Option<MarketUpdate>| {
                if let Some(update) = update {
                    let log = w.resource_mut::<AuditLog>();
                    log.entries.push(format!(
                        "  [route] market from '{}' seq={}",
                        update.venue, update.sequence
                    ));
                }
            },
            reg,
        );

    // =========================================================================
    // Run events
    // =========================================================================

    println!("=== AdminCommand: normal order (qty=50) ===");
    pipeline_a.run(
        &mut world,
        AdminCommand {
            source: "ops-console".into(),
            symbol: "BTC-USD".into(),
            qty: 50,
            price: 42000.0,
            admin_flags: 0x01,
        },
    );

    println!("\n=== AdminCommand: oversized order (qty=200, should REJECT) ===");
    pipeline_a.run(
        &mut world,
        AdminCommand {
            source: "risk-override".into(),
            symbol: "ETH-USD".into(),
            qty: 200,
            price: 3000.0,
            admin_flags: 0x03,
        },
    );

    println!("\n=== MarketUpdate: normal order (qty=25) ===");
    pipeline_b.run(
        &mut world,
        MarketUpdate {
            venue: "binance".into(),
            symbol: "SOL-USD".into(),
            qty: 25,
            price: 150.0,
            sequence: 1001,
        },
    );

    println!("\n=== MarketUpdate: oversized (qty=500, should REJECT) ===");
    pipeline_b.run(
        &mut world,
        MarketUpdate {
            venue: "coinbase".into(),
            symbol: "BTC-USD".into(),
            qty: 500,
            price: 41999.0,
            sequence: 1002,
        },
    );

    // =========================================================================
    // Print results
    // =========================================================================

    println!("\n=== Audit Log ===");
    let log = world.resource::<AuditLog>();
    for entry in &log.entries {
        println!("{entry}");
    }

    println!("\n=== Summary ===");
    println!("  Events:    4 (2 admin, 2 market)");
    println!("  Accepted:  2 (qty <= 100)");
    println!("  Rejected:  2 (qty > 100)");
    println!(
        "  Audit log: {} entries (tap fires before guard)",
        log.entries.len()
    );
    println!("  Reuse:     log_order + check_risk shared across both pipelines");
    println!("  Views:     zero-cost borrowed (&str, not String clone)");
}
