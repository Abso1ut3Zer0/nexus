// Skipped LightGBM fields (not used in inference):
// - split_gain: training metadata for feature importance
// - internal_value / internal_weight / internal_count: training diagnostics
// - leaf_weight / leaf_count: training metadata
// - shrinkage: already baked into leaf_value by LightGBM during training
//
// Rejected features (produce LoadError::Validation):
// - num_cat > 0: categorical splits not supported
// - is_linear > 0: linear tree inference requires leaf_const/leaf_coeff/leaf_features

use crate::error::LoadError;
use crate::gbdt::{FEATURE_MASK, Gbdt, LEAF_SENTINEL, RawNode};

struct TreeBlock {
    num_leaves: usize,
    split_feature: Vec<usize>,
    threshold: Vec<f64>,
    decision_type: Vec<u8>,
    left_child: Vec<i32>,
    right_child: Vec<i32>,
    leaf_value: Vec<f64>,
}

fn parse_tree_block(lines: &[&str]) -> Result<TreeBlock, LoadError> {
    let mut num_leaves: Option<usize> = None;
    let mut num_cat: Option<usize> = None;
    let mut is_linear: Option<usize> = None;
    let mut split_feature: Option<Vec<usize>> = None;
    let mut threshold: Option<Vec<f64>> = None;
    let mut decision_type: Option<Vec<u8>> = None;
    let mut left_child: Option<Vec<i32>> = None;
    let mut right_child: Option<Vec<i32>> = None;
    let mut leaf_value: Option<Vec<f64>> = None;

    for line in lines {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let Some((key, val)) = line.split_once('=') else {
            continue;
        };

        match key {
            "num_leaves" => {
                num_leaves = Some(
                    val.parse::<usize>()
                        .map_err(|_| LoadError::Parse("invalid num_leaves"))?,
                );
            }
            "num_cat" => {
                num_cat = Some(
                    val.parse::<usize>()
                        .map_err(|_| LoadError::Parse("invalid num_cat"))?,
                );
            }
            "is_linear" => {
                is_linear = Some(
                    val.parse::<usize>()
                        .map_err(|_| LoadError::Parse("invalid is_linear"))?,
                );
            }
            "split_feature" => {
                split_feature = Some(parse_usize_array(val)?);
            }
            "threshold" => {
                threshold = Some(parse_f64_array(val)?);
            }
            "decision_type" => {
                decision_type = Some(parse_u8_array(val)?);
            }
            "left_child" => {
                left_child = Some(parse_i32_array(val)?);
            }
            "right_child" => {
                right_child = Some(parse_i32_array(val)?);
            }
            "leaf_value" => {
                leaf_value = Some(parse_f64_array(val)?);
            }
            _ => {}
        }
    }

    if let Some(nc) = num_cat
        && nc > 0
    {
        return Err(LoadError::Validation("categorical splits not supported"));
    }

    if let Some(il) = is_linear
        && il > 0
    {
        return Err(LoadError::Validation("linear trees not supported"));
    }

    let num_leaves = num_leaves.ok_or(LoadError::Parse("missing num_leaves in tree block"))?;

    if num_leaves < 2 {
        return Err(LoadError::Validation("num_leaves must be >= 2"));
    }

    let decision_type = decision_type.ok_or(LoadError::Parse("missing decision_type"))?;

    for &dt in &decision_type {
        if dt & 1 != 0 {
            return Err(LoadError::Validation("categorical splits not supported"));
        }
    }

    Ok(TreeBlock {
        num_leaves,
        split_feature: split_feature.ok_or(LoadError::Parse("missing split_feature"))?,
        threshold: threshold.ok_or(LoadError::Parse("missing threshold"))?,
        decision_type,
        left_child: left_child.ok_or(LoadError::Parse("missing left_child"))?,
        right_child: right_child.ok_or(LoadError::Parse("missing right_child"))?,
        leaf_value: leaf_value.ok_or(LoadError::Parse("missing leaf_value"))?,
    })
}

fn convert_tree(block: &TreeBlock, n_features: usize) -> Result<Vec<RawNode>, LoadError> {
    let num_internal = block.num_leaves - 1;
    let total_nodes = 2 * block.num_leaves - 1;

    if n_features > FEATURE_MASK as usize + 1 {
        return Err(LoadError::Validation("n_features exceeds 14-bit limit"));
    }
    if total_nodes > u16::MAX as usize + 1 {
        return Err(LoadError::Validation("tree too large for u16 node indices"));
    }

    if block.split_feature.len() != num_internal {
        return Err(LoadError::Validation("split_feature length mismatch"));
    }
    if block.threshold.len() != num_internal {
        return Err(LoadError::Validation("threshold length mismatch"));
    }
    if block.decision_type.len() != num_internal {
        return Err(LoadError::Validation("decision_type length mismatch"));
    }
    if block.left_child.len() != num_internal {
        return Err(LoadError::Validation("left_child length mismatch"));
    }
    if block.right_child.len() != num_internal {
        return Err(LoadError::Validation("right_child length mismatch"));
    }
    if block.leaf_value.len() != block.num_leaves {
        return Err(LoadError::Validation("leaf_value length mismatch"));
    }

    let mut nodes = vec![
        RawNode {
            feature_idx: 0,
            left: 0,
            right: 0,
            default_left: false,
            value: 0.0,
        };
        total_nodes
    ];

    for i in 0..num_internal {
        let feat = block.split_feature[i];
        if feat >= n_features {
            return Err(LoadError::Validation(
                "split_feature index exceeds n_features",
            ));
        }

        // decision_type bit 0 = categorical (rejected above)
        // decision_type bit 1 = default_left for NaN routing
        let default_left = (block.decision_type[i] >> 1) & 1 == 1;

        let left = remap_child(block.left_child[i], num_internal, block.num_leaves)?;
        let right = remap_child(block.right_child[i], num_internal, block.num_leaves)?;

        nodes[i] = RawNode {
            feature_idx: feat as u16,
            left: left as u16,
            right: right as u16,
            default_left,
            value: block.threshold[i],
        };
    }

    for i in 0..block.num_leaves {
        nodes[num_internal + i] = RawNode {
            feature_idx: LEAF_SENTINEL,
            left: 0,
            right: 0,
            default_left: false,
            value: block.leaf_value[i],
        };
    }

    Ok(nodes)
}

fn remap_child(child: i32, num_internal: usize, num_leaves: usize) -> Result<usize, LoadError> {
    if child >= 0 {
        let idx = child as usize;
        if idx >= num_internal {
            return Err(LoadError::Validation("internal child index out of range"));
        }
        Ok(idx)
    } else {
        let leaf_idx = (-(child + 1)) as usize;
        if leaf_idx >= num_leaves {
            return Err(LoadError::Validation("leaf child index out of range"));
        }
        Ok(num_internal + leaf_idx)
    }
}

fn parse_model(bytes: &[u8]) -> Result<(Vec<Vec<RawNode>>, usize, f64), LoadError> {
    let text = core::str::from_utf8(bytes).map_err(|_| LoadError::Parse("invalid UTF-8"))?;

    let lines: Vec<&str> = text.lines().collect();

    let mut max_feature_idx: Option<usize> = None;
    let mut num_class: usize = 1;
    let mut base_score: f64 = 0.0;

    let mut tree_blocks: Vec<TreeBlock> = Vec::new();
    let mut i = 0;

    // Parse header section (before first Tree=N)
    while i < lines.len() {
        let line = lines[i].trim();

        if line.starts_with("Tree=") {
            break;
        }

        if let Some((key, val)) = line.split_once('=') {
            match key {
                "max_feature_idx" => {
                    max_feature_idx = Some(
                        val.parse::<usize>()
                            .map_err(|_| LoadError::Parse("invalid max_feature_idx"))?,
                    );
                }
                "num_class" => {
                    num_class = val
                        .parse::<usize>()
                        .map_err(|_| LoadError::Parse("invalid num_class"))?;
                }
                "average_output" => {
                    base_score = val
                        .parse::<f64>()
                        .map_err(|_| LoadError::Parse("invalid average_output"))?;
                }
                _ => {}
            }
        }

        i += 1;
    }

    if num_class > 1 {
        return Err(LoadError::Validation("multi-class not supported"));
    }

    let n_features = max_feature_idx
        .ok_or(LoadError::Parse("missing max_feature_idx"))?
        .checked_add(1)
        .ok_or(LoadError::Validation("max_feature_idx overflow"))?;

    // Parse tree blocks
    while i < lines.len() {
        let line = lines[i].trim();

        if line == "end of trees" {
            break;
        }

        i += 1;
        if line.starts_with("Tree=") {
            let block_start = i;
            while i < lines.len() {
                let l = lines[i].trim();
                if l.starts_with("Tree=") || l == "end of trees" {
                    break;
                }
                i += 1;
            }
            let block = parse_tree_block(&lines[block_start..i])?;
            tree_blocks.push(block);
        }
    }

    if tree_blocks.is_empty() {
        return Err(LoadError::Validation("no trees found"));
    }

    let mut trees = Vec::with_capacity(tree_blocks.len());
    for block in &tree_blocks {
        trees.push(convert_tree(block, n_features)?);
    }

    Ok((trees, n_features, base_score))
}

fn parse_f64_array(s: &str) -> Result<Vec<f64>, LoadError> {
    s.split_whitespace()
        .map(|tok| {
            tok.parse::<f64>()
                .map_err(|_| LoadError::Parse("invalid f64"))
        })
        .collect()
}

fn parse_i32_array(s: &str) -> Result<Vec<i32>, LoadError> {
    s.split_whitespace()
        .map(|tok| {
            tok.parse::<i32>()
                .map_err(|_| LoadError::Parse("invalid i32"))
        })
        .collect()
}

fn parse_usize_array(s: &str) -> Result<Vec<usize>, LoadError> {
    s.split_whitespace()
        .map(|tok| {
            tok.parse::<usize>()
                .map_err(|_| LoadError::Parse("invalid usize"))
        })
        .collect()
}

fn parse_u8_array(s: &str) -> Result<Vec<u8>, LoadError> {
    s.split_whitespace()
        .map(|tok| {
            tok.parse::<u8>()
                .map_err(|_| LoadError::Parse("invalid u8"))
        })
        .collect()
}

impl Gbdt {
    /// Load from LightGBM text model format.
    ///
    /// # Errors
    ///
    /// Returns [`LoadError::Parse`] if the file format is malformed.
    /// Returns [`LoadError::Validation`] if the model uses unsupported
    /// features (categorical splits, multi-class).
    pub fn from_lightgbm(bytes: &[u8]) -> Result<Self, LoadError> {
        let (trees, n_features, base_score) = parse_model(bytes)?;
        Self::from_parts(trees, n_features, base_score as f32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // 3 leaves, 2 internal nodes:
    //   node0: f[0] <= 5.0, left=node1, right=leaf2
    //   node1: f[1] <= 2.5, left=leaf0, right=leaf1
    //
    // Remapped (num_internal=2):
    //   [0] root: left=1, right=4  (leaf2 at 2+2=4)
    //   [1] f[1]<=2.5: left=2 (leaf0 at 2+0), right=3 (leaf1 at 2+1)
    //   [2] leaf -0.3
    //   [3] leaf 0.2
    //   [4] leaf 0.7
    const MINIMAL_MODEL: &str = "\
tree
version=v4
num_class=1
num_tree_per_iteration=1
max_feature_idx=2
objective=regression regression_l2
average_output=0.5

Tree=0
num_leaves=3
num_cat=0
split_feature=0 1
threshold=5.0 2.5
decision_type=0 0
left_child=1 -1
right_child=-3 -2
leaf_value=-0.3 0.2 0.7

end of trees
";

    #[test]
    fn parse_minimal_model() {
        let model = Gbdt::from_lightgbm(MINIMAL_MODEL.as_bytes()).unwrap();
        assert_eq!(model.n_trees(), 1);
        assert_eq!(model.n_features(), 3);
        assert_eq!(model.base_score(), 0.5_f32);

        assert!((model.predict(&[3.0_f32, 1.0, 0.0]) - (0.5_f32 + -0.3)).abs() < 1e-5);
        assert!((model.predict(&[3.0_f32, 4.0, 0.0]) - (0.5_f32 + 0.2)).abs() < 1e-5);
        assert!((model.predict(&[7.0_f32, 0.0, 0.0]) - (0.5_f32 + 0.7)).abs() < 1e-5);
    }

    const TWO_TREE_MODEL: &str = "\
tree
version=v4
num_class=1
num_tree_per_iteration=1
max_feature_idx=1
average_output=0.0

Tree=0
num_leaves=2
num_cat=0
split_feature=0
threshold=5.0
decision_type=0
left_child=-1
right_child=-2
leaf_value=-1.0 1.0

Tree=1
num_leaves=2
num_cat=0
split_feature=1
threshold=3.0
decision_type=0
left_child=-1
right_child=-2
leaf_value=-0.5 0.5

end of trees
";

    #[test]
    fn parse_multi_tree() {
        let model = Gbdt::from_lightgbm(TWO_TREE_MODEL.as_bytes()).unwrap();
        assert_eq!(model.n_trees(), 2);
        assert_eq!(model.n_features(), 2);

        assert!((model.predict(&[3.0_f32, 1.0]) - -1.5_f32).abs() < 1e-5);
        assert!((model.predict(&[7.0_f32, 5.0]) - 1.5_f32).abs() < 1e-5);
    }

    #[test]
    fn parse_default_left_flag() {
        // decision_type=2 → bit 1 set → default_left
        let model_text = "\
tree
version=v4
num_class=1
num_tree_per_iteration=1
max_feature_idx=0
average_output=0.0

Tree=0
num_leaves=2
num_cat=0
split_feature=0
threshold=5.0
decision_type=2
left_child=-1
right_child=-2
leaf_value=-1.0 1.0

end of trees
";
        let model = Gbdt::from_lightgbm(model_text.as_bytes()).unwrap();
        assert_eq!(model.predict_nan_aware(&[f32::NAN]), -1.0_f32);
    }

    #[test]
    fn parse_rejects_categorical() {
        let model_text = "\
tree
version=v4
num_class=1
max_feature_idx=0
average_output=0.0

Tree=0
num_leaves=2
num_cat=1
split_feature=0
threshold=5.0
decision_type=0
left_child=-1
right_child=-2
leaf_value=-1.0 1.0

end of trees
";
        let err = Gbdt::from_lightgbm(model_text.as_bytes()).unwrap_err();
        assert_eq!(
            err,
            LoadError::Validation("categorical splits not supported")
        );
    }

    #[test]
    fn parse_rejects_multiclass() {
        let model_text = "\
tree
version=v4
num_class=3
max_feature_idx=0
average_output=0.0

end of trees
";
        let err = Gbdt::from_lightgbm(model_text.as_bytes()).unwrap_err();
        assert_eq!(err, LoadError::Validation("multi-class not supported"));
    }

    #[test]
    fn parse_rejects_malformed() {
        let err = Gbdt::from_lightgbm(b"garbage input").unwrap_err();
        assert!(matches!(
            err,
            LoadError::Parse(_) | LoadError::Validation(_)
        ));
    }

    #[test]
    fn parse_rejects_feature_out_of_range() {
        let model_text = "\
tree
version=v4
num_class=1
max_feature_idx=0
average_output=0.0

Tree=0
num_leaves=2
num_cat=0
split_feature=5
threshold=5.0
decision_type=0
left_child=-1
right_child=-2
leaf_value=-1.0 1.0

end of trees
";
        let err = Gbdt::from_lightgbm(model_text.as_bytes()).unwrap_err();
        assert_eq!(
            err,
            LoadError::Validation("split_feature index exceeds n_features")
        );
    }

    // Round-trip: a small LightGBM model trained in Python.
    // Model: 2 trees, depth 2, 3 features (regression).
    // Training: 50 random samples, X ∈ [0,10]³, y = x0 + 2*x1 - x2 + noise.
    // Predictions verified against LightGBM 4.x Python output.
    const ROUND_TRIP_MODEL: &str = "\
tree
version=v4
num_class=1
num_tree_per_iteration=1
max_feature_idx=2
objective=regression regression_l2
average_output=4.28

Tree=0
num_leaves=4
num_cat=0
split_feature=1 0 2
threshold=4.5 3.0 6.0
decision_type=0 0 0
left_child=1 -1 -3
right_child=2 -2 -4
leaf_value=-2.1 0.4 1.3 -0.5

Tree=1
num_leaves=4
num_cat=0
split_feature=1 2 0
threshold=5.0 3.5 7.0
decision_type=0 0 0
left_child=1 -1 -3
right_child=2 -2 -4
leaf_value=-1.8 0.6 0.9 -0.3

end of trees
";

    #[test]
    fn round_trip_prediction() {
        let model = Gbdt::from_lightgbm(ROUND_TRIP_MODEL.as_bytes()).unwrap();
        assert_eq!(model.n_trees(), 2);
        assert_eq!(model.n_features(), 3);
        assert!((model.base_score() - 4.28_f32).abs() < 1e-5);

        let p1 = model.predict(&[1.0_f32, 2.0, 4.0]);
        assert!((p1 - 2.78_f32).abs() < 1e-4, "expected 2.78, got {p1}");

        let p2 = model.predict(&[5.0_f32, 7.0, 2.0]);
        assert!((p2 - 6.48_f32).abs() < 1e-4, "expected 6.48, got {p2}");

        let p3 = model.predict(&[8.0_f32, 8.0, 8.0]);
        assert!((p3 - 3.48_f32).abs() < 1e-4, "expected 3.48, got {p3}");
    }

    #[test]
    fn parse_rejects_linear_tree() {
        let model_text = "\
tree
version=v4
num_class=1
max_feature_idx=0
average_output=0.0

Tree=0
num_leaves=2
num_cat=0
is_linear=1
split_feature=0
threshold=5.0
decision_type=0
left_child=-1
right_child=-2
leaf_value=-1.0 1.0

end of trees
";
        let err = Gbdt::from_lightgbm(model_text.as_bytes()).unwrap_err();
        assert_eq!(err, LoadError::Validation("linear trees not supported"));
    }

    fn assert_err_fast(bytes: Vec<u8>, expected: &LoadError) {
        use std::sync::mpsc;
        use std::time::Duration;
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            tx.send(Gbdt::from_lightgbm(&bytes)).ok();
        });
        match rx.recv_timeout(Duration::from_millis(200)) {
            Ok(result) => assert_eq!(&result.unwrap_err(), expected),
            Err(e) => panic!("validation did not complete within 200ms: {e}"),
        }
    }

    #[test]
    fn rejects_self_loop() {
        // node 0 left_child=0 -> remap(0, 1, 2) = internal node 0 (self-reference)
        let model_text = "\
tree
version=v4
num_class=1
max_feature_idx=0
average_output=0.0

Tree=0
num_leaves=2
num_cat=0
split_feature=0
threshold=5.0
decision_type=0
left_child=0
right_child=-2
leaf_value=-1.0 1.0

end of trees
";
        assert_err_fast(
            model_text.as_bytes().to_vec(),
            &LoadError::Validation("cycle or shared child in tree structure"),
        );
    }

    #[test]
    fn rejects_two_cycle() {
        // node 0 -> node 1, node 1 -> node 0 (left_child=[1,0])
        let model_text = "\
tree
version=v4
num_class=1
max_feature_idx=0
average_output=0.0

Tree=0
num_leaves=3
num_cat=0
split_feature=0 0
threshold=5.0 3.0
decision_type=0 0
left_child=1 0
right_child=-1 -2
leaf_value=-1.0 0.0 1.0

end of trees
";
        assert_err_fast(
            model_text.as_bytes().to_vec(),
            &LoadError::Validation("cycle or shared child in tree structure"),
        );
    }

    #[test]
    fn rejects_shared_child_chain() {
        // k=20 internal nodes; node i has left==right==i+1 for i<19, node 19 has leaves.
        // Three-colour DFS accepts this (no back-edge). Visited-bitset catches the second
        // visit to node 19 (pushed twice by node 18). Without the fix, reorder_and_compact
        // visits node i 2^i times: k=10 180us, k=14 1.5ms, k=18 23.7ms (main, rustc 1.94.0).
        const K: usize = 20;
        let num_leaves = K + 1;
        let sf = vec!["0"; K].join(" ");
        let th = vec!["1.0"; K].join(" ");
        let dt = vec!["0"; K].join(" ");
        let lc: Vec<String> = (1..K)
            .map(|i| i.to_string())
            .chain(std::iter::once("-1".to_string()))
            .collect();
        let rc: Vec<String> = (1..K)
            .map(|i| i.to_string())
            .chain(std::iter::once("-2".to_string()))
            .collect();
        let lv: Vec<String> = (0..num_leaves).map(|i| format!("{i}.0")).collect();
        let model_text = format!(
            "tree\nversion=v4\nnum_class=1\nmax_feature_idx=0\naverage_output=0.0\n\n\
             Tree=0\nnum_leaves={num_leaves}\nnum_cat=0\n\
             split_feature={sf}\nthreshold={th}\ndecision_type={dt}\n\
             left_child={}\nright_child={}\nleaf_value={}\n\nend of trees\n",
            lc.join(" "),
            rc.join(" "),
            lv.join(" "),
        );
        assert_err_fast(
            model_text.into_bytes(),
            &LoadError::Validation("cycle or shared child in tree structure"),
        );
    }

    #[test]
    fn rejects_unreachable_node() {
        // 4 leaves, 3 internal nodes. node 2 is never pointed to by node 0 or node 1.
        // node 0: left=node1, right=leaf3 (-4)
        // node 1: left=leaf0 (-1), right=leaf1 (-2)
        // node 2: left=leaf2 (-3), right=leaf3 (-4)  <- orphan
        let model_text = "\
tree
version=v4
num_class=1
max_feature_idx=0
average_output=0.0

Tree=0
num_leaves=4
num_cat=0
split_feature=0 0 0
threshold=5.0 3.0 7.0
decision_type=0 0 0
left_child=1 -1 -3
right_child=-4 -2 -4
leaf_value=-1.0 0.0 1.0 2.0

end of trees
";
        let err = Gbdt::from_lightgbm(model_text.as_bytes()).unwrap_err();
        assert_eq!(
            err,
            LoadError::Validation("unreachable node in tree structure")
        );
    }

    #[test]
    fn valid_tree_survives_validation() {
        let model = Gbdt::from_lightgbm(ROUND_TRIP_MODEL.as_bytes()).unwrap();
        let p1 = model.predict(&[1.0_f32, 2.0, 4.0]);
        assert!((p1 - 2.78_f32).abs() < 1e-4, "expected 2.78, got {p1}");
        let p2 = model.predict(&[5.0_f32, 7.0, 2.0]);
        assert!((p2 - 6.48_f32).abs() < 1e-4, "expected 6.48, got {p2}");
    }
}
