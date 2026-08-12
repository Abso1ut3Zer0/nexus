//! Plugin trait for composable resource registration.

use crate::world::WorldBuilder;

/// Composable unit of resource registration.
///
/// Analogous to Bevy's `Plugin`.
///
/// Plugins register resources into a [`WorldBuilder`]. The runtime is
/// assembled by installing plugins via [`WorldBuilder::install_plugin`].
///
/// When choosing how to register — [`register`](WorldBuilder::register) for a
/// resource the plugin owns, [`ensure`](WorldBuilder::ensure) /
/// [`ensure_default`](WorldBuilder::ensure_default) for one it shares with other
/// plugins — see the owned-vs-shared guidance on the
/// [`Installer`](crate::Installer) trait.
///
/// # Examples
///
/// ```ignore
/// struct TradingPlugin;
///
/// impl Plugin for TradingPlugin {
///     fn build(self, world: &mut WorldBuilder) {
///         world.register(PriceCache::new());
///         world.register(TradeState::default());
///     }
/// }
///
/// let mut wb = WorldBuilder::new();
/// wb.install_plugin(TradingPlugin);
/// ```
pub trait Plugin {
    /// Register resources into the world.
    fn build(self, world: &mut WorldBuilder);
}

impl<F: FnOnce(&mut WorldBuilder)> Plugin for F {
    fn build(self, world: &mut WorldBuilder) {
        self(world);
    }
}
