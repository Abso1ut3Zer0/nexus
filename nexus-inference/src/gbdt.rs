use crate::error::LoadError;

/// Marks a leaf in [`RawNode`] (intermediate format during loading).
pub(crate) const LEAF_SENTINEL: u16 = u16::MAX;

/// Bit 15 of `feature_idx` — set on leaf nodes in the packed [`Node`].
pub(crate) const LEAF_BIT: u16 = 0x8000;

/// Bit 14 of `feature_idx` — NaN default-left routing flag.
const DEFAULT_LEFT_BIT: u16 = 0x4000;

/// Mask for the actual feature index (bits 13:0). Up to 16384 features.
pub(crate) const FEATURE_MASK: u16 = 0x3FFF;

/// Intermediate node used during loading and tree construction.
///
/// Explicit fields for clarity: `right` and `default_left` are separate.
/// Converted to compact [`Node`] by [`reorder_and_compact`] during model
/// construction.
#[derive(Debug, Clone)]
pub(crate) struct RawNode {
    pub(crate) feature_idx: u16,
    pub(crate) left: u16,
    pub(crate) right: u16,
    pub(crate) default_left: bool,
    pub(crate) value: f64,
}

/// Compact 8-byte decision tree node.
///
/// Layout: `[f32 value | u16 feature_idx | u16 left]`
///
/// `feature_idx` packs three fields:
/// - bit 15: leaf flag (1 = leaf node, value is leaf output)
/// - bit 14: default_left (NaN routing direction)
/// - bits 13:0: feature index for the split
///
/// The `right` child is absent: false-branch-next (DFS right-first)
/// layout guarantees the right child is always at `idx + 1`. This
/// saves a stored index per node and enables sequential memory access
/// on ~50% of decisions (the false/right path).
///
/// 8-byte power-of-2 stride: pointer arithmetic is a shift, not a
/// multiply. 2x cache density vs the previous 16-byte node.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub(crate) struct Node {
    pub(crate) value: f32,
    pub(crate) feature_idx: u16,
    pub(crate) left: u16,
}

const _: () = assert!(core::mem::size_of::<Node>() == 8);

/// Reorder tree to false-branch-next layout and convert to compact [`Node`].
///
/// DFS right-first traversal: the right (false) child is always placed at
/// `idx + 1`, so `walk_tree` uses `idx + 1` instead of loading a stored
/// index. Only the left child index is stored.
fn reorder_and_compact(raw: &[RawNode]) -> Result<Vec<Node>, LoadError> {
    let n = raw.len();
    if n == 0 {
        return Ok(Vec::new());
    }
    debug_assert!(n <= u16::MAX as usize + 1);

    let mut nodes = Vec::with_capacity(n);
    let mut old_to_new = vec![0u16; n];
    let mut visited = vec![false; n];
    let mut stack = Vec::with_capacity(32);
    stack.push(0usize);

    while let Some(old_idx) = stack.pop() {
        if visited[old_idx] {
            return Err(LoadError::Validation(
                "cycle or shared child in tree structure",
            ));
        }
        visited[old_idx] = true;
        old_to_new[old_idx] = nodes.len() as u16;
        let r = &raw[old_idx];

        if r.feature_idx == LEAF_SENTINEL {
            nodes.push(Node {
                value: r.value as f32,
                feature_idx: LEAF_BIT,
                left: 0,
            });
        } else {
            let mut packed_feat = r.feature_idx;
            if r.default_left {
                packed_feat |= DEFAULT_LEFT_BIT;
            }
            nodes.push(Node {
                value: r.value as f32,
                feature_idx: packed_feat,
                left: r.left, // old index; remapped below
            });
            // Push left first so right pops first (right lands at idx+1)
            stack.push(r.left as usize);
            stack.push(r.right as usize);
        }
    }

    if visited.iter().filter(|&&v| v).count() < n {
        return Err(LoadError::Validation("unreachable node in tree structure"));
    }

    for node in &mut nodes {
        if node.feature_idx & LEAF_BIT == 0 {
            node.left = old_to_new[node.left as usize];
        }
    }

    Ok(nodes)
}

/// Gradient-boosted decision tree ensemble.
///
/// Immutable after construction. All prediction methods take `&self`.
/// Thread-safe: `Send + Sync` by construction (no interior mutability).
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "loader-lightgbm")] {
/// use nexus_inference::Gbdt;
///
/// // Load a LightGBM model from text format bytes
/// // let model = Gbdt::from_lightgbm(model_bytes).unwrap();
/// // let prediction = model.predict(&features);
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct Gbdt {
    nodes: Box<[Node]>,
    tree_offsets: Box<[u32]>,
    n_features: usize,
    base_score: f32,
}

impl Gbdt {
    /// Predict the ensemble score.
    ///
    /// Returns the raw ensemble score (base score + sum of leaf values).
    /// For classification objectives, apply the appropriate link function
    /// (e.g., sigmoid for binary classification).
    ///
    /// NaN features always route right (`NaN <= threshold` is false).
    /// Use [`predict_nan_aware`](Self::predict_nan_aware) for learned
    /// NaN routing.
    ///
    /// # Panics
    ///
    /// Panics if `features.len() != self.n_features()`.
    pub fn predict(&self, features: &[f32]) -> f32 {
        assert_eq!(features.len(), self.n_features);
        let base = self.nodes.as_ptr();
        let mut score = self.base_score;
        for &offset in &*self.tree_offsets {
            // SAFETY: every `offset` in `tree_offsets` is a valid root index
            // into `self.nodes` (the buffer `base` points into), established at
            // construction; see walk_tree's SAFETY note. `add` stays in bounds.
            score += Self::walk_tree(unsafe { base.add(offset as usize) }, features, false);
        }
        score
    }

    /// Predict with NaN routing (LightGBM-compatible).
    ///
    /// NaN features are routed via the learned default direction at each
    /// split node. Matches LightGBM's inference behavior. Use this when
    /// features may contain NaN (missing values).
    ///
    /// # Panics
    ///
    /// Panics if `features.len() != self.n_features()`.
    pub fn predict_nan_aware(&self, features: &[f32]) -> f32 {
        assert_eq!(features.len(), self.n_features);
        let base = self.nodes.as_ptr();
        let mut score = self.base_score;
        for &offset in &*self.tree_offsets {
            // SAFETY: every `offset` in `tree_offsets` is a valid root index
            // into `self.nodes` (the buffer `base` points into), established at
            // construction; see walk_tree's SAFETY note. `add` stays in bounds.
            score += Self::walk_tree(unsafe { base.add(offset as usize) }, features, true);
        }
        score
    }

    /// Evaluate only the first `n_trees` trees.
    ///
    /// Clamped to `self.n_trees()` if `n_trees` exceeds the ensemble size.
    pub fn predict_n(&self, features: &[f32], n_trees: usize) -> f32 {
        assert_eq!(features.len(), self.n_features);
        let n = n_trees.min(self.tree_offsets.len());
        let base = self.nodes.as_ptr();
        let mut score = self.base_score;
        for &offset in &self.tree_offsets[..n] {
            // SAFETY: every `offset` in `tree_offsets` is a valid root index
            // into `self.nodes` (the buffer `base` points into), established at
            // construction; see walk_tree's SAFETY note. `add` stays in bounds.
            score += Self::walk_tree(unsafe { base.add(offset as usize) }, features, false);
        }
        score
    }

    /// Evaluate only the first `n_trees` trees with NaN routing.
    ///
    /// Clamped to `self.n_trees()` if `n_trees` exceeds the ensemble size.
    pub fn predict_n_nan_aware(&self, features: &[f32], n_trees: usize) -> f32 {
        assert_eq!(features.len(), self.n_features);
        let n = n_trees.min(self.tree_offsets.len());
        let base = self.nodes.as_ptr();
        let mut score = self.base_score;
        for &offset in &self.tree_offsets[..n] {
            // SAFETY: every `offset` in `tree_offsets` is a valid root index
            // into `self.nodes` (the buffer `base` points into), established at
            // construction; see walk_tree's SAFETY note. `add` stays in bounds.
            score += Self::walk_tree(unsafe { base.add(offset as usize) }, features, true);
        }
        score
    }

    /// Number of trees in the ensemble.
    pub fn n_trees(&self) -> usize {
        self.tree_offsets.len()
    }

    /// Number of features expected by the model.
    pub fn n_features(&self) -> usize {
        self.n_features
    }

    /// Base score (initial prediction before tree contributions).
    pub fn base_score(&self) -> f32 {
        self.base_score
    }

    /// Number of outputs. Always 1 for GBDT.
    pub fn n_outputs(&self) -> usize {
        1
    }

    /// Write prediction to output buffer.
    ///
    /// # Panics
    ///
    /// Panics if `features.len() != self.n_features()` or
    /// `output.len() != 1`.
    pub fn predict_into(&self, features: &[f32], output: &mut [f32]) {
        assert_eq!(output.len(), 1);
        output[0] = self.predict(features);
    }

    /// Write prediction to output buffer with NaN routing.
    ///
    /// # Panics
    ///
    /// Panics if `features.len() != self.n_features()` or
    /// `output.len() != 1`.
    pub fn predict_into_nan_aware(&self, features: &[f32], output: &mut [f32]) {
        assert_eq!(output.len(), 1);
        output[0] = self.predict_nan_aware(features);
    }

    /// Branchless tree traversal with single cmov per level.
    ///
    /// # Safety
    ///
    /// `tree` must point to the root of a valid tree within `self.nodes`.
    /// Nodes use false-branch-next layout: right child is at `idx + 1`.
    /// Left child index validated by `remap_child` during loading.
    fn walk_tree(tree: *const Node, features: &[f32], nan_aware: bool) -> f32 {
        let mut idx = 0usize;
        loop {
            // SAFETY: idx=0 at entry. Subsequent values from node.left
            // (validated by remap_child) or idx+1 (DFS layout invariant).
            let node = unsafe { *tree.add(idx) };
            if node.feature_idx & LEAF_BIT != 0 {
                return node.value;
            }

            // SAFETY: feature_idx & FEATURE_MASK < n_features (validated in convert_tree).
            let feat =
                unsafe { *features.get_unchecked((node.feature_idx & FEATURE_MASK) as usize) };
            let go_left = if nan_aware {
                let is_nan = feat.is_nan();
                let default_left = node.feature_idx & DEFAULT_LEFT_BIT != 0;
                #[allow(clippy::needless_bitwise_bool)]
                {
                    (feat <= node.value) | (is_nan & default_left)
                }
            } else {
                feat <= node.value
            };

            let left_idx = node.left as usize;
            let right_idx = idx + 1;
            idx = core::hint::select_unpredictable(go_left, left_idx, right_idx);
        }
    }

    #[allow(dead_code)]
    pub(crate) fn from_parts(
        trees: Vec<Vec<RawNode>>,
        n_features: usize,
        base_score: f32,
    ) -> Result<Self, LoadError> {
        let total: usize = trees.iter().map(Vec::len).sum();
        let mut nodes = Vec::with_capacity(total);
        let mut tree_offsets = Vec::with_capacity(trees.len());
        for tree in &trees {
            for node in tree {
                assert!(
                    node.feature_idx == LEAF_SENTINEL || (node.feature_idx as usize) < n_features,
                    "feature_idx {} out of range for n_features {}",
                    node.feature_idx,
                    n_features,
                );
            }
        }
        for tree in trees {
            tree_offsets.push(nodes.len() as u32);
            nodes.extend_from_slice(&reorder_and_compact(&tree)?);
        }
        Ok(Self {
            nodes: nodes.into_boxed_slice(),
            tree_offsets: tree_offsets.into_boxed_slice(),
            n_features,
            base_score,
        })
    }
}

crate::impl_model!(Gbdt, stateless);

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(value: f64) -> RawNode {
        RawNode {
            feature_idx: LEAF_SENTINEL,
            left: 0,
            right: 0,
            default_left: false,
            value,
        }
    }

    fn split(feat: u16, left: u16, right: u16, threshold: f64) -> RawNode {
        RawNode {
            feature_idx: feat,
            left,
            right,
            default_left: false,
            value: threshold,
        }
    }

    fn single_stump(base_score: f32) -> Gbdt {
        let nodes = vec![split(0, 1, 2, 0.5), leaf(-1.0), leaf(1.0)];
        Gbdt::from_parts(vec![nodes], 1, base_score).unwrap()
    }

    #[test]
    fn single_stump_left() {
        let model = single_stump(0.0);
        assert_eq!(model.predict(&[0.3_f32]), -1.0_f32);
    }

    #[test]
    fn single_stump_right() {
        let model = single_stump(0.0);
        assert_eq!(model.predict(&[0.8_f32]), 1.0_f32);
    }

    #[test]
    fn single_stump_boundary() {
        let model = single_stump(0.0);
        assert_eq!(model.predict(&[0.5_f32]), -1.0_f32);
    }

    #[test]
    fn base_score_added() {
        let model = single_stump(10.0);
        assert_eq!(model.predict(&[0.3_f32]), 10.0_f32 + -1.0_f32);
        assert_eq!(model.predict(&[0.8_f32]), 10.0_f32 + 1.0_f32);
    }

    #[test]
    fn multi_tree_sums() {
        let stump = vec![split(0, 1, 2, 0.5), leaf(-1.0), leaf(1.0)];
        let model =
            Gbdt::from_parts(vec![stump.clone(), stump.clone(), stump], 1, 0.0_f32).unwrap();
        assert_eq!(model.predict(&[0.3_f32]), -3.0_f32);
        assert_eq!(model.predict(&[0.8_f32]), 3.0_f32);
    }

    #[test]
    fn predict_n_partial() {
        let stump = vec![split(0, 1, 2, 0.5), leaf(-1.0), leaf(1.0)];
        let model =
            Gbdt::from_parts(vec![stump.clone(), stump.clone(), stump], 1, 5.0_f32).unwrap();
        assert_eq!(model.predict_n(&[0.3_f32], 2), 5.0_f32 + -2.0_f32);
    }

    #[test]
    fn predict_n_exceeds_count() {
        let stump = vec![split(0, 1, 2, 0.5), leaf(-1.0), leaf(1.0)];
        let model =
            Gbdt::from_parts(vec![stump.clone(), stump.clone(), stump], 1, 0.0_f32).unwrap();
        assert_eq!(model.predict_n(&[0.3_f32], 100), model.predict(&[0.3_f32]));
    }

    #[test]
    fn deeper_tree() {
        let nodes = vec![
            split(0, 1, 2, 5.0),
            split(1, 3, 4, 2.0),
            split(1, 5, 6, 8.0),
            leaf(-4.0),
            leaf(-2.0),
            leaf(2.0),
            leaf(4.0),
        ];
        let model = Gbdt::from_parts(vec![nodes], 2, 0.0_f32).unwrap();
        assert_eq!(model.predict(&[3.0_f32, 1.0]), -4.0_f32);
        assert_eq!(model.predict(&[3.0_f32, 3.0]), -2.0_f32);
        assert_eq!(model.predict(&[7.0_f32, 5.0]), 2.0_f32);
        assert_eq!(model.predict(&[7.0_f32, 9.0]), 4.0_f32);
    }

    #[test]
    fn nan_routing_default_left() {
        let nodes = vec![
            RawNode {
                feature_idx: 0,
                left: 1,
                right: 2,
                default_left: true,
                value: 0.5,
            },
            leaf(-1.0),
            leaf(1.0),
        ];
        let model = Gbdt::from_parts(vec![nodes], 1, 0.0_f32).unwrap();
        assert_eq!(model.predict_nan_aware(&[f32::NAN]), -1.0_f32);
    }

    #[test]
    fn nan_routing_default_right() {
        let nodes = vec![split(0, 1, 2, 0.5), leaf(-1.0), leaf(1.0)];
        let model = Gbdt::from_parts(vec![nodes], 1, 0.0_f32).unwrap();
        assert_eq!(model.predict_nan_aware(&[f32::NAN]), 1.0_f32);
    }

    #[test]
    fn nan_goes_right() {
        let nodes = vec![
            RawNode {
                feature_idx: 0,
                left: 1,
                right: 2,
                default_left: true,
                value: 0.5,
            },
            leaf(-1.0),
            leaf(1.0),
        ];
        let model = Gbdt::from_parts(vec![nodes], 1, 0.0_f32).unwrap();
        assert_eq!(model.predict(&[f32::NAN]), 1.0_f32);
    }

    #[test]
    #[should_panic]
    fn wrong_feature_count_panics() {
        let model = single_stump(0.0);
        model.predict(&[1.0_f32, 2.0]);
    }

    #[test]
    fn accessors() {
        let model = single_stump(2.5);
        assert_eq!(model.n_trees(), 1);
        assert_eq!(model.n_features(), 1);
        assert_eq!(model.n_outputs(), 1);
        assert_eq!(model.base_score(), 2.5_f32);
    }

    #[test]
    fn predict_into_matches() {
        let model = single_stump(0.0);
        let mut out = [0.0_f32];
        model.predict_into(&[0.3_f32], &mut out);
        assert_eq!(out[0], model.predict(&[0.3_f32]));
        model.predict_into(&[0.8_f32], &mut out);
        assert_eq!(out[0], model.predict(&[0.8_f32]));
    }

    #[test]
    #[should_panic]
    fn predict_into_wrong_output_len() {
        let model = single_stump(0.0);
        let mut out = [0.0_f32; 2];
        model.predict_into(&[0.3_f32], &mut out);
    }
}
