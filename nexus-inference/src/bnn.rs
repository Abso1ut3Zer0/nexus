use crate::LoadError;
use crate::Scratch;
#[cfg(not(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma")
    )
)))]
use crate::kernel::dot::matvec_bias_f32;

fn bias_to_int_threshold(bias: f32, hidden_size: usize) -> u32 {
    let half = (hidden_size as f32 - bias) * 0.5;
    half.ceil().clamp(0.0, (hidden_size + 1) as f32) as u32
}

#[derive(Debug, Clone)]
struct BinaryLayer {
    w_packed: Box<[u64]>,
    int_threshold: Box<[u32]>,
}

/// Binary neural network with ±1 weights and XNOR+popcount inference.
///
/// Architecture: fp32 input layer → N binary hidden layers → fp32 output.
/// Binary layers replace multiply-add with XNOR + popcount, roughly
/// an order of magnitude cheaper per hidden-layer step than fp32.
///
/// ```text
/// x → W_in @ x + b_in → sign → [XNOR+popcount layers] → unpack → W_out @ h + b_out → y
/// ```
///
/// Users train in Python (BinaryConnect, XNOR-Net, Larq, or custom
/// STE training), fold batch normalization into biases, export binary
/// weights as ±1 i8 via safetensors. With no binary layers (N=0) the
/// network is just the fp32 input and output layers with a binarization
/// between them — no XNOR+popcount layers.
///
/// Hidden size must be a multiple of 64 for clean bit packing.
/// Binary weights are packed as `u64`: bit 1 = weight +1, bit 0 = weight −1.
///
/// # Examples
///
/// ```
/// use nexus_inference::Bnn;
///
/// let h = 64;
/// let w_input = vec![0.1_f32; h * 2];
/// let b_input = vec![0.0_f32; h];
/// let w_output = vec![0.1_f32; 1 * h];
/// let b_output = vec![0.0_f32; 1];
///
/// let bnn = Bnn::from_parts(
///     &w_input, &b_input, &[], &[], &w_output, &b_output, 1,
/// ).unwrap();
///
/// let output = bnn.predict(&[1.0, 1.0]);
/// ```
#[derive(Debug, Clone)]
pub struct Bnn {
    w_input: Box<[f32]>,
    b_input: Box<[f32]>,
    binary_layers: Box<[BinaryLayer]>,
    w_output: Box<[f32]>,
    b_output: Box<[f32]>,
    w_output_row_sum: Box<[f32]>,
    bits_a: Scratch<Box<[u64]>>,
    bits_b: Scratch<Box<[u64]>>,
    #[cfg(not(all(
        target_arch = "x86_64",
        any(
            target_feature = "avx512f",
            all(target_feature = "avx2", target_feature = "fma")
        )
    )))]
    float_scratch: Scratch<Box<[f32]>>,
    input_size: u16,
    hidden_size: u16,
    output_size: u16,
}

impl Bnn {
    /// Construct from pre-packed binary weights.
    ///
    /// - `w_input`: fp32 input-to-hidden weights, `[H, I]` row-major.
    /// - `b_input`: fp32 input layer bias, `[H]`. Absorbs folded batch norm;
    ///   binarization applies `sign(W @ input + bias)`.
    /// - `binary_weights`: per-layer packed ±1 weights. Each slice is
    ///   `[H * H/64]` u64s in row-major order (bit 1 = +1, bit 0 = −1).
    /// - `binary_biases`: per-layer fp32 biases, each `[H]`. Converted to
    ///   integer thresholds internally: `ceil((H − bias) / 2)`.
    /// - `w_output`: fp32 hidden-to-output weights, `[O, H]` row-major.
    /// - `b_output`: fp32 output bias, `[O]`.
    /// - `output_size`: number of outputs.
    ///
    /// # Errors
    ///
    /// Returns [`LoadError::Validation`] if dimensions are inconsistent,
    /// hidden size is not a multiple of 64, or any fp32 weight is non-finite.
    pub fn from_parts(
        w_input: &[f32],
        b_input: &[f32],
        binary_weights: &[&[u64]],
        binary_biases: &[&[f32]],
        w_output: &[f32],
        b_output: &[f32],
        output_size: usize,
    ) -> Result<Self, LoadError> {
        let hidden_size = b_input.len();
        if hidden_size == 0 || output_size == 0 {
            return Err(LoadError::Validation("sizes must be > 0"));
        }
        if !hidden_size.is_multiple_of(64) {
            return Err(LoadError::Validation(
                "hidden_size must be a multiple of 64",
            ));
        }
        if w_input.is_empty() {
            return Err(LoadError::Validation("w_input must not be empty"));
        }
        if !w_input.len().is_multiple_of(hidden_size) {
            return Err(LoadError::Validation("w_input length must be H * I"));
        }
        let input_size = w_input.len() / hidden_size;
        if input_size == 0 {
            return Err(LoadError::Validation("sizes must be > 0"));
        }
        if input_size > u16::MAX as usize
            || hidden_size > u16::MAX as usize
            || output_size > u16::MAX as usize
        {
            return Err(LoadError::Validation("size exceeds u16::MAX"));
        }
        if binary_weights.len() != binary_biases.len() {
            return Err(LoadError::Validation(
                "binary_weights and binary_biases must have same length",
            ));
        }

        let wpr = hidden_size / 64;
        for (w, b) in binary_weights.iter().zip(binary_biases.iter()) {
            if w.len() != hidden_size * wpr {
                return Err(LoadError::Validation(
                    "binary weight length must be H * (H/64)",
                ));
            }
            if b.len() != hidden_size {
                return Err(LoadError::Validation("binary bias length must be H"));
            }
        }

        if w_output.len() != output_size * hidden_size {
            return Err(LoadError::Validation("w_output length must be O * H"));
        }
        if b_output.len() != output_size {
            return Err(LoadError::Validation("b_output length must be O"));
        }

        for &v in w_input
            .iter()
            .chain(b_input)
            .chain(w_output)
            .chain(b_output)
        {
            if !v.is_finite() {
                return Err(LoadError::Validation("non-finite weight"));
            }
        }
        for biases in binary_biases {
            for &v in *biases {
                if !v.is_finite() {
                    return Err(LoadError::Validation("non-finite weight"));
                }
            }
        }

        let binary_layers: Vec<BinaryLayer> = binary_weights
            .iter()
            .zip(binary_biases.iter())
            .map(|(w, b)| {
                let int_threshold: Vec<u32> = b
                    .iter()
                    .map(|&bias| bias_to_int_threshold(bias, hidden_size))
                    .collect();
                BinaryLayer {
                    w_packed: (*w).into(),
                    int_threshold: int_threshold.into_boxed_slice(),
                }
            })
            .collect();

        let w_output_row_sum: Vec<f32> = (0..output_size)
            .map(|j| {
                w_output[j * hidden_size..(j + 1) * hidden_size]
                    .iter()
                    .sum()
            })
            .collect();

        Ok(Self {
            w_input: w_input.into(),
            b_input: b_input.into(),
            binary_layers: binary_layers.into_boxed_slice(),
            w_output: w_output.into(),
            b_output: b_output.into(),
            w_output_row_sum: w_output_row_sum.into_boxed_slice(),
            bits_a: Scratch::new(vec![0_u64; wpr].into_boxed_slice()),
            bits_b: Scratch::new(vec![0_u64; wpr].into_boxed_slice()),
            #[cfg(not(all(
                target_arch = "x86_64",
                any(
                    target_feature = "avx512f",
                    all(target_feature = "avx2", target_feature = "fma")
                )
            )))]
            float_scratch: Scratch::new(vec![0.0_f32; hidden_size].into_boxed_slice()),
            input_size: input_size as u16,
            hidden_size: hidden_size as u16,
            output_size: output_size as u16,
        })
    }

    /// Predict a single scalar output.
    ///
    /// # Panics
    ///
    /// Panics if `output_size != 1` or `input.len() != input_size`.
    pub fn predict(&self, input: &[f32]) -> f32 {
        assert_eq!(
            self.output_size, 1,
            "predict() requires output_size == 1, use predict_into()"
        );
        let mut out = [0.0_f32];
        self.predict_into(input, &mut out);
        out[0]
    }

    /// Predict into caller's buffer.
    ///
    /// Inference pipeline:
    /// 1. fp32 matmul: `h = W_in @ input + b_in`
    /// 2. Binarize: `bits = sign(h)` (≥0 → 1, <0 → 0)
    /// 3. Binary layers: XNOR + popcount, threshold comparison
    /// 4. Unpack bits to ±1.0, fp32 output matmul
    ///
    /// # Panics
    ///
    /// Panics if `input.len() != input_size` or
    /// `output.len() != output_size`.
    pub fn predict_into(&self, input: &[f32], output: &mut [f32]) {
        let i_sz = self.input_size as usize;
        let h_sz = self.hidden_size as usize;
        let o_sz = self.output_size as usize;
        let wpr = h_sz / 64;

        assert_eq!(input.len(), i_sz, "input length must equal input_size");
        assert_eq!(output.len(), o_sz, "output length must equal output_size");

        // SAFETY: predict is not reentrant. Scratch is !Sync, preventing concurrent access.
        let bits_a = unsafe { self.bits_a.get_mut() };
        // SAFETY: same as above.
        let bits_b = unsafe { self.bits_b.get_mut() };
        #[cfg(not(all(
            target_arch = "x86_64",
            any(
                target_feature = "avx512f",
                all(target_feature = "avx2", target_feature = "fma")
            )
        )))]
        // SAFETY: same as above.
        let float_scratch = unsafe { self.float_scratch.get_mut() };

        // fused input: matmul + binarize in one pass
        #[cfg(all(
            target_arch = "x86_64",
            any(
                target_feature = "avx512f",
                all(target_feature = "avx2", target_feature = "fma")
            )
        ))]
        {
            crate::kernel::binary::matvec_bias_binarize(
                &self.w_input,
                input,
                &self.b_input,
                bits_a,
                h_sz,
                i_sz,
            );
        }
        #[cfg(not(all(
            target_arch = "x86_64",
            any(
                target_feature = "avx512f",
                all(target_feature = "avx2", target_feature = "fma")
            )
        )))]
        {
            matvec_bias_f32(
                &self.w_input,
                input,
                &self.b_input,
                float_scratch,
                h_sz,
                i_sz,
            );
            crate::kernel::binary::binarize(float_scratch, bits_a);
        }

        // binary hidden layers (alternating buffers)
        let n_layers = self.binary_layers.len();
        for i in 0..n_layers {
            if i % 2 == 0 {
                crate::kernel::binary::binary_layer_forward(
                    &self.binary_layers[i].w_packed,
                    &self.binary_layers[i].int_threshold,
                    bits_a,
                    bits_b,
                    h_sz,
                    wpr,
                );
            } else {
                crate::kernel::binary::binary_layer_forward(
                    &self.binary_layers[i].w_packed,
                    &self.binary_layers[i].int_threshold,
                    bits_b,
                    bits_a,
                    h_sz,
                    wpr,
                );
            }
        }

        // fused output: compute dot product directly from bits
        let final_bits: &[u64] = if n_layers.is_multiple_of(2) {
            bits_a
        } else {
            bits_b
        };

        for j in 0..o_sz {
            let w_row = &self.w_output[j * h_sz..(j + 1) * h_sz];
            let row_sum = self.w_output_row_sum[j];
            let bias = self.b_output[j];

            #[cfg(all(
                target_arch = "x86_64",
                any(
                    target_feature = "avx512f",
                    all(target_feature = "avx2", target_feature = "fma")
                )
            ))]
            {
                output[j] =
                    crate::kernel::binary::output_from_bits_simd(w_row, final_bits, row_sum, bias);
            }
            #[cfg(not(all(
                target_arch = "x86_64",
                any(
                    target_feature = "avx512f",
                    all(target_feature = "avx2", target_feature = "fma")
                )
            )))]
            {
                output[j] =
                    crate::kernel::binary::output_from_bits(w_row, final_bits, row_sum, bias, h_sz);
            }
        }
    }

    /// Number of input features.
    pub fn n_inputs(&self) -> usize {
        self.input_size as usize
    }

    /// Hidden layer width (all layers same size, multiple of 64).
    pub fn n_hidden(&self) -> usize {
        self.hidden_size as usize
    }

    /// Number of outputs.
    pub fn n_outputs(&self) -> usize {
        self.output_size as usize
    }

    /// Number of binary hidden layers.
    pub fn n_layers(&self) -> usize {
        self.binary_layers.len()
    }
}

crate::impl_model!(Bnn, stateless);

#[cfg(test)]
mod tests {
    use super::*;

    fn pack_i8(weights: &[i8], rows: usize, cols: usize) -> Vec<u64> {
        debug_assert_eq!(cols % 64, 0);
        debug_assert_eq!(weights.len(), rows * cols);
        let wpr = cols / 64;
        let mut packed = vec![0_u64; rows * wpr];
        for r in 0..rows {
            for c in 0..cols {
                if weights[r * cols + c] == 1 {
                    packed[r * wpr + c / 64] |= 1 << (c % 64);
                }
            }
        }
        packed
    }

    const H: usize = 64;
    const WPR: usize = H / 64;

    fn make_bnn_no_binary(
        w_input: &[f32],
        b_input: &[f32],
        w_output: &[f32],
        b_output: &[f32],
        output_size: usize,
    ) -> Bnn {
        Bnn::from_parts(w_input, b_input, &[], &[], w_output, b_output, output_size).unwrap()
    }

    #[test]
    fn no_binary_layers_all_positive() {
        // I=2, H=64, O=1
        // W_in = 0.1, b_in = 0 → matmul = 0.2 for all → all bits = 1 → all +1.0
        // W_out = 0.1 → dot = 0.1 * 64 = 6.4
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        );
        let y = bnn.predict(&[1.0, 1.0]);
        assert!((y - 6.4).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn no_binary_layers_all_negative() {
        // Same but negative input → matmul = -0.2 → all bits = 0 → all -1.0
        // dot = 0.1 * (-64) = -6.4
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        );
        let y = bnn.predict(&[-1.0, -1.0]);
        assert!((y - (-6.4)).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn no_binary_layers_mixed_signs() {
        // First 32 rows of W_in positive, last 32 negative
        let mut w_input = vec![0.0_f32; H * 2];
        for r in 0..32 {
            w_input[r * 2] = 0.1;
            w_input[r * 2 + 1] = 0.1;
        }
        for r in 32..64 {
            w_input[r * 2] = -0.1;
            w_input[r * 2 + 1] = -0.1;
        }
        // input = [1, 1]: first 32 → 0.2 → +1, last 32 → -0.2 → -1
        // W_out = 0.1: dot = 0.1*(32 - 32) = 0
        let bnn = make_bnn_no_binary(
            &w_input,
            &vec![0.0_f32; H],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        );
        let y = bnn.predict(&[1.0, 1.0]);
        assert!(y.abs() < 1e-5, "got {y}");
    }

    #[test]
    fn bias_shifts_threshold() {
        // b_input = -1.0: matmul must be >= 1.0 to activate
        // W_in @ [1, 1] = 0.2 per row, but 0.2 + (-1.0) = -0.8 < 0 → bit 0
        // All bits = 0 → all -1.0
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 2],
            &vec![-1.0_f32; H],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        );
        let y = bnn.predict(&[1.0, 1.0]);
        assert!((y - (-6.4)).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn one_binary_layer_all_match() {
        // Binary weights: all +1 (all bits set)
        // Input bits: all +1 (from positive matmul)
        // XNOR(1, 1) = 1 → popcount = 64
        // threshold = ceil((64 - 0) / 2) = 32
        // 64 >= 32 → all bits = 1 → unpack = all +1.0
        let bin_weights = vec![u64::MAX; H * WPR];
        let bin_biases = vec![0.0_f32; H];
        let bnn = Bnn::from_parts(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &[bin_weights.as_slice()],
            &[bin_biases.as_slice()],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        )
        .unwrap();
        let y = bnn.predict(&[1.0, 1.0]);
        assert!((y - 6.4).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn one_binary_layer_all_mismatch() {
        // Binary weights: all -1 (all bits clear)
        // Input bits: all +1
        // XNOR(0, 1) = 0 → popcount = 0
        // threshold = 32, 0 < 32 → all bits = 0 → all -1.0
        let bin_weights = vec![0_u64; H * WPR];
        let bin_biases = vec![0.0_f32; H];
        let bnn = Bnn::from_parts(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &[bin_weights.as_slice()],
            &[bin_biases.as_slice()],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        )
        .unwrap();
        let y = bnn.predict(&[1.0, 1.0]);
        assert!((y - (-6.4)).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn binary_layer_bias_forces_activation() {
        // Binary weights: all -1 (mismatch), popcount = 0
        // But bias = 200.0: threshold = ceil((64 - 200) / 2) = ceil(-68) = -68 → clamped to 0
        // 0 >= 0 → all activate → all +1.0
        let bin_weights = vec![0_u64; H * WPR];
        let bin_biases = vec![200.0_f32; H];
        let bnn = Bnn::from_parts(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &[bin_weights.as_slice()],
            &[bin_biases.as_slice()],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        )
        .unwrap();
        let y = bnn.predict(&[1.0, 1.0]);
        assert!((y - 6.4).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn binary_layer_bias_suppresses_activation() {
        // Binary weights: all +1 (match), popcount = 64
        // But bias = -200.0: threshold = ceil((64 + 200) / 2) = ceil(132) = 132 > 64
        // 64 < 132 → all suppressed → all -1.0
        let bin_weights = vec![u64::MAX; H * WPR];
        let bin_biases = vec![-200.0_f32; H];
        let bnn = Bnn::from_parts(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &[bin_weights.as_slice()],
            &[bin_biases.as_slice()],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        )
        .unwrap();
        let y = bnn.predict(&[1.0, 1.0]);
        assert!((y - (-6.4)).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn two_binary_layers() {
        // Layer 0: all +1 weights, bias 0 → all match → all +1 bits
        // Layer 1: all +1 weights, bias 0 → same → all +1 bits
        // Result same as no binary layers with all-positive input
        let bin_weights = vec![u64::MAX; H * WPR];
        let bin_biases = vec![0.0_f32; H];
        let bnn = Bnn::from_parts(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &[bin_weights.as_slice(), bin_weights.as_slice()],
            &[bin_biases.as_slice(), bin_biases.as_slice()],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        )
        .unwrap();
        let y = bnn.predict(&[1.0, 1.0]);
        assert!((y - 6.4).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn pack_i8_round_trip() {
        // ±1 i8 weights → pack → XNOR+popcount should match manual calc
        let mut weights_i8 = vec![1_i8; H * H];
        // Set first row to all -1
        for c in 0..H {
            weights_i8[c] = -1;
        }
        let packed = pack_i8(&weights_i8, H, H);

        // First row: all -1 → all bits 0 → packed[0] = 0
        assert_eq!(packed[0], 0);
        // Second row: all +1 → all bits 1 → packed[WPR] = u64::MAX
        assert_eq!(packed[WPR], u64::MAX);
    }

    #[test]
    fn multi_output() {
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &vec![0.1_f32; 2 * H],
            &vec![0.0_f32; 2],
            2,
        );
        let mut out = [0.0_f32; 2];
        bnn.predict_into(&[1.0, 1.0], &mut out);
        assert!((out[0] - 6.4).abs() < 1e-5);
        assert!((out[1] - 6.4).abs() < 1e-5);
    }

    #[test]
    fn output_bias() {
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &vec![0.1_f32; H],
            &vec![1.0_f32; 1],
            1,
        );
        let y = bnn.predict(&[1.0, 1.0]);
        assert!((y - 7.4).abs() < 1e-5, "got {y}");
    }

    #[test]
    fn accessors() {
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 4],
            &vec![0.0_f32; H],
            &vec![0.1_f32; 2 * H],
            &vec![0.0_f32; 2],
            2,
        );
        assert_eq!(bnn.n_inputs(), 4);
        assert_eq!(bnn.n_hidden(), 64);
        assert_eq!(bnn.n_outputs(), 2);
        assert_eq!(bnn.n_layers(), 0);
    }

    #[test]
    fn rejects_non_multiple_of_64() {
        assert!(
            Bnn::from_parts(
                &vec![0.1_f32; 32 * 2],
                &vec![0.0_f32; 32],
                &[],
                &[],
                &vec![0.1_f32; 32],
                &vec![0.0_f32; 1],
                1,
            )
            .is_err()
        );
    }

    #[test]
    fn rejects_empty() {
        assert!(Bnn::from_parts(&[], &[], &[], &[], &[], &[], 1).is_err());
    }

    #[test]
    fn rejects_mismatched_binary_layers() {
        let bin_w = vec![0_u64; H * WPR];
        assert!(
            Bnn::from_parts(
                &vec![0.1_f32; H * 2],
                &vec![0.0_f32; H],
                &[bin_w.as_slice()],
                &[], // no biases
                &vec![0.1_f32; H],
                &vec![0.0_f32; 1],
                1,
            )
            .is_err()
        );
    }

    #[test]
    fn rejects_non_finite() {
        assert!(
            Bnn::from_parts(
                &vec![f32::NAN; H * 2],
                &vec![0.0_f32; H],
                &[],
                &[],
                &vec![0.1_f32; H],
                &vec![0.0_f32; 1],
                1,
            )
            .is_err()
        );
    }

    #[test]
    #[should_panic(expected = "input length must equal input_size")]
    fn wrong_input_panics() {
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        );
        bnn.predict(&[1.0]); // expects 2
    }

    #[test]
    #[should_panic(expected = "output length must equal output_size")]
    fn wrong_output_panics() {
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &vec![0.1_f32; H],
            &vec![0.0_f32; 1],
            1,
        );
        let mut out = [0.0_f32; 3];
        bnn.predict_into(&[1.0, 1.0], &mut out);
    }

    #[test]
    #[should_panic(expected = "predict() requires output_size == 1")]
    fn predict_multi_output_panics() {
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; H * 2],
            &vec![0.0_f32; H],
            &vec![0.1_f32; 2 * H],
            &vec![0.0_f32; 2],
            2,
        );
        bnn.predict(&[1.0, 1.0]);
    }

    #[test]
    fn hidden_128_two_words() {
        // H=128 (2 u64 words per row)
        let h = 128;
        let bnn = make_bnn_no_binary(
            &vec![0.1_f32; h * 2],
            &vec![0.0_f32; h],
            &vec![0.1_f32; h],
            &vec![0.0_f32; 1],
            1,
        );
        let y = bnn.predict(&[1.0, 1.0]);
        // All positive → all bits = 1 → all +1.0
        // dot = 0.1 * 128 = 12.8
        assert!((y - 12.8).abs() < 1e-4, "got {y}");
    }
}
