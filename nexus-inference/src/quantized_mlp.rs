use crate::LoadError;
use crate::Scratch;
use crate::activation::Activation;
use crate::kernel::activate::activate_f32;

#[derive(Debug, Clone)]
struct QuantLayer {
    w_i8: Box<[i8]>,
    bias_adjusted: Box<[f32]>,
    combined_scale: f32,
    inv_input_scale: f32,
    w_zero_point: i8,
    input_zero_point: i8,
    in_size: u16,
    out_size: u16,
}

/// Int8 quantized multi-layer perceptron for fast inference.
///
/// Weights are stored as `i8` with per-layer affine quantization
/// (scale + zero_point). The forward pass quantizes f32 inputs to i8,
/// performs integer matmul with i32 accumulation, dequantizes back to
/// f32, applies activation, and repeats for each layer. The final
/// layer outputs f32 directly.
///
/// Supports both symmetric (zero_point = 0) and asymmetric
/// quantization, matching PyTorch's `torch.ao.quantization` output.
///
/// # Examples
///
/// ```
/// use nexus_inference::{Activation, QuantizedMlp};
///
/// // 2-input, 4-hidden, 1-output with symmetric quantization
/// let w0 = vec![10_i8; 4 * 2];  // layer 0: [4, 2]
/// let b0 = vec![0.0_f32; 4];
/// let w1 = vec![5_i8; 1 * 4];   // layer 1: [1, 4]
/// let b1 = vec![0.0_f32; 1];
///
/// let mut model = QuantizedMlp::from_parts(
///     &[&w0, &w1],
///     &[&b0, &b1],
///     &[0.01, 0.01],  // weight scales
///     &[0, 0],         // weight zero points (symmetric)
///     &[0.05, 0.05],   // input scales
///     &[0, 0],          // input zero points (symmetric)
///     Activation::Relu,
/// ).unwrap();
///
/// let output = model.predict(&[1.0, 2.0]);
/// ```
#[derive(Debug, Clone)]
pub struct QuantizedMlp {
    layers: Box<[QuantLayer]>,
    scratch_f32: Scratch<Box<[f32]>>,
    scratch_i8: Scratch<Box<[i8]>>,
    scratch_i32: Scratch<Box<[i32]>>,
    input_size: u16,
    output_size: u16,
    activation: Activation,
}

impl QuantizedMlp {
    /// Construct from pre-trained quantized weights.
    ///
    /// Each layer k has:
    /// - `layers_w[k]`: i8 weights, `[out_size, in_size]` row-major
    /// - `layers_b[k]`: f32 biases, `[out_size]`
    /// - `w_scales[k]`: weight quantization scale
    /// - `w_zero_points[k]`: weight zero point (0 for symmetric)
    /// - `input_scales[k]`: input/activation quantization scale
    /// - `input_zero_points[k]`: input/activation zero point
    ///
    /// Layer sizes are inferred from weight dimensions. Layer 0 input
    /// size is `layers_w[0].len() / layers_b[0].len()`.
    #[allow(clippy::too_many_arguments)]
    pub fn from_parts(
        layers_w: &[&[i8]],
        layers_b: &[&[f32]],
        w_scales: &[f32],
        w_zero_points: &[i8],
        input_scales: &[f32],
        input_zero_points: &[i8],
        activation: Activation,
    ) -> Result<Self, LoadError> {
        let num_layers = layers_w.len();
        if num_layers == 0 {
            return Err(LoadError::Validation("must have at least 1 layer"));
        }
        if layers_b.len() != num_layers
            || w_scales.len() != num_layers
            || w_zero_points.len() != num_layers
            || input_scales.len() != num_layers
            || input_zero_points.len() != num_layers
        {
            return Err(LoadError::Validation(
                "all per-layer arrays must have the same length",
            ));
        }

        let mut layers = Vec::with_capacity(num_layers);
        let mut prev_out_size: Option<usize> = None;
        let mut max_dim = 0_usize;

        for k in 0..num_layers {
            let out_size = layers_b[k].len();
            if out_size == 0 {
                return Err(LoadError::Validation("layer output size must be > 0"));
            }
            if layers_w[k].is_empty() || !layers_w[k].len().is_multiple_of(out_size) {
                return Err(LoadError::Validation(
                    "weight length not divisible by output size",
                ));
            }
            let in_size = layers_w[k].len() / out_size;
            if in_size == 0 {
                return Err(LoadError::Validation("layer input size must be > 0"));
            }

            if let Some(prev) = prev_out_size
                && in_size != prev
            {
                return Err(LoadError::Validation(
                    "layer input size must match previous layer output size",
                ));
            }

            if in_size > u16::MAX as usize || out_size > u16::MAX as usize {
                return Err(LoadError::Validation("layer size exceeds u16::MAX"));
            }

            if !w_scales[k].is_finite() || w_scales[k] <= 0.0 {
                return Err(LoadError::Validation("w_scale must be finite and positive"));
            }
            if !input_scales[k].is_finite() || input_scales[k] <= 0.0 {
                return Err(LoadError::Validation(
                    "input_scale must be finite and positive",
                ));
            }

            for &b in layers_b[k] {
                if !b.is_finite() {
                    return Err(LoadError::Validation("non-finite bias"));
                }
            }

            // Precompute row sums and adjusted bias.
            // The SIMD path uses XOR 0x80 (i8→u8), producing dot = sum((x+128)*w).
            // Corrections folded into bias at construction:
            //   bias_adj = bias - correction_factor * row_sum * combined_scale
            // where correction_factor = 128 + input_zp (SIMD) or input_zp (scalar).
            let combined_scale = w_scales[k] * input_scales[k];
            let inv_input_scale = 1.0 / input_scales[k];
            let input_zp_i32 = input_zero_points[k] as i32;

            #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
            let correction_factor = 128 + input_zp_i32;
            #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
            let correction_factor = input_zp_i32;

            let mut row_sum = vec![0_i32; out_size];
            let mut bias_adjusted = vec![0.0_f32; out_size];
            for j in 0..out_size {
                let mut s = 0_i32;
                for i in 0..in_size {
                    s += layers_w[k][j * in_size + i] as i32;
                }
                row_sum[j] = s;
                bias_adjusted[j] =
                    ((correction_factor * s) as f32).mul_add(-combined_scale, layers_b[k][j]);
            }

            if in_size > max_dim {
                max_dim = in_size;
            }
            if out_size > max_dim {
                max_dim = out_size;
            }

            layers.push(QuantLayer {
                w_i8: layers_w[k].into(),
                bias_adjusted: bias_adjusted.into_boxed_slice(),
                combined_scale,
                inv_input_scale,
                w_zero_point: w_zero_points[k],
                input_zero_point: input_zero_points[k],
                in_size: in_size as u16,
                out_size: out_size as u16,
            });

            prev_out_size = Some(out_size);
        }

        let input_size = layers[0].in_size;
        let output_size = layers[num_layers - 1].out_size;

        Ok(Self {
            layers: layers.into_boxed_slice(),
            scratch_f32: Scratch::new(vec![0.0_f32; max_dim].into_boxed_slice()),
            scratch_i8: Scratch::new(vec![0_i8; max_dim].into_boxed_slice()),
            scratch_i32: Scratch::new(vec![0_i32; max_dim].into_boxed_slice()),
            input_size,
            output_size,
            activation,
        })
    }

    /// Single-output prediction.
    ///
    /// Panics if `output_size != 1`.
    pub fn predict(&self, input: &[f32]) -> f32 {
        assert_eq!(
            self.output_size, 1,
            "predict() requires output_size == 1, use predict_into()"
        );
        let mut out = [0.0_f32];
        self.predict_into(input, &mut out);
        out[0]
    }

    /// General prediction (multi-output).
    ///
    /// # Panics
    ///
    /// Panics if `input.len() != n_inputs()` or
    /// `output.len() != n_outputs()`.
    pub fn predict_into(&self, input: &[f32], output: &mut [f32]) {
        assert_eq!(input.len(), self.input_size as usize);
        assert_eq!(output.len(), self.output_size as usize);

        // SAFETY: predict is not reentrant. Scratch is !Sync, preventing concurrent access.
        let scratch_f32 = unsafe { self.scratch_f32.get_mut() };
        // SAFETY: same as above.
        let scratch_i8 = unsafe { self.scratch_i8.get_mut() };
        // SAFETY: same as above.
        let scratch_i32 = unsafe { self.scratch_i32.get_mut() };

        let n_layers = self.layers.len();

        // First layer reads from caller's input
        scratch_f32[..input.len()].copy_from_slice(input);

        for layer_idx in 0..n_layers {
            let in_size = self.layers[layer_idx].in_size as usize;
            let out_size = self.layers[layer_idx].out_size as usize;
            let is_last = layer_idx == n_layers - 1;

            let inv_input_scale = self.layers[layer_idx].inv_input_scale;
            let input_zp = self.layers[layer_idx].input_zero_point;
            let w_zp = self.layers[layer_idx].w_zero_point as i32;
            let combined_scale = self.layers[layer_idx].combined_scale;

            // Step 1: Quantize f32 → i8
            crate::kernel::quantized::quantize_f32_to_i8(
                &scratch_f32[..in_size],
                &mut scratch_i8[..in_size],
                inv_input_scale,
                input_zp,
            );

            // Step 2: Integer matmul → i32 accumulation
            #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
            {
                crate::kernel::quantized::matvec_i8_i32(
                    &self.layers[layer_idx].w_i8,
                    &scratch_i8[..in_size],
                    &mut scratch_i32[..out_size],
                    out_size,
                    in_size,
                );
            }
            #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
            {
                let out_4 = out_size & !3;
                let mut j = 0;
                while j < out_4 {
                    let rows = &self.layers[layer_idx].w_i8[j * in_size..(j + 4) * in_size];
                    let dots = crate::kernel::quantized::dot4_i8_i32(rows, &scratch_i8[..in_size]);
                    scratch_i32[j] = dots[0];
                    scratch_i32[j + 1] = dots[1];
                    scratch_i32[j + 2] = dots[2];
                    scratch_i32[j + 3] = dots[3];
                    j += 4;
                }
                while j < out_size {
                    let row = &self.layers[layer_idx].w_i8[j * in_size..(j + 1) * in_size];
                    scratch_i32[j] =
                        crate::kernel::quantized::dot_i8_i32(row, &scratch_i8[..in_size]);
                    j += 1;
                }
            }

            // Step 3: Dequantize + bias (128 and input_zp corrections precomputed
            // into bias_adjusted at construction) + weight zp correction + activation
            let dst = if is_last {
                &mut *output
            } else {
                &mut scratch_f32[..out_size]
            };

            // Weight zero-point correction requires input_sum (input-dependent).
            // Hoisted out of the output loop — constant across all output neurons.
            let w_zp_correction = if w_zp != 0 {
                let mut input_sum = 0_i32;
                for i in 0..in_size {
                    input_sum += scratch_i8[i] as i32;
                }
                w_zp * input_sum - (in_size as i32) * w_zp * (input_zp as i32)
            } else {
                0
            };

            for j in 0..out_size {
                let acc = scratch_i32[j] - w_zp_correction;

                // Dequantize: y = acc * combined_scale + bias_adjusted
                // (bias_adjusted already includes 128*row_sum and input_zp*row_sum corrections)
                let mut y =
                    (acc as f32).mul_add(combined_scale, self.layers[layer_idx].bias_adjusted[j]);

                // Activation (not on last layer)
                if !is_last {
                    y = activate_f32(y, self.activation);
                }

                dst[j] = y;
            }
        }
    }

    /// Number of input features.
    pub fn n_inputs(&self) -> usize {
        self.input_size as usize
    }

    /// Number of output values.
    pub fn n_outputs(&self) -> usize {
        self.output_size as usize
    }

    /// Number of layers (weight matrices).
    pub fn n_layers(&self) -> usize {
        self.layers.len()
    }

    /// Activation function applied to hidden layers.
    pub fn activation(&self) -> Activation {
        self.activation
    }
}

crate::impl_model!(QuantizedMlp, stateless);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symmetric_identity_passthrough() {
        // 1 layer, 2→1, identity, scale=1.0, zp=0
        // weights=[1, 1], bias=0
        // input=[3.0, 4.0] → quantized=[3, 4] → dot=7 → dequant=7*1*1+0=7.0
        let w = [1_i8, 1];
        let b = [0.0_f32];
        let m = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[1.0],
            &[0],
            &[1.0],
            &[0],
            Activation::Identity,
        )
        .unwrap();
        let out = m.predict(&[3.0, 4.0]);
        assert!((out - 7.0).abs() < 1e-6, "got {out}");
    }

    #[test]
    fn symmetric_with_scale() {
        // 1 layer, 2→1, identity
        // w=[10, 20], w_scale=0.1 (real weights: 1.0, 2.0)
        // input_scale=0.5 → input [2.0, 3.0] quantizes to [4, 6]
        // dot = 10*4 + 20*6 = 160
        // dequant = 160 * 0.1 * 0.5 = 8.0
        // real: 1.0*2.0 + 2.0*3.0 = 8.0
        let w = [10_i8, 20];
        let b = [0.0_f32];
        let m = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[0.1],
            &[0],
            &[0.5],
            &[0],
            Activation::Identity,
        )
        .unwrap();
        let out = m.predict(&[2.0, 3.0]);
        assert!((out - 8.0).abs() < 0.5, "got {out}");
    }

    #[test]
    fn bias_applied() {
        let w = [1_i8, 1];
        let b = [5.0_f32];
        let m = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[1.0],
            &[0],
            &[1.0],
            &[0],
            Activation::Identity,
        )
        .unwrap();
        let out = m.predict(&[3.0, 4.0]);
        assert!((out - 12.0).abs() < 1e-6, "got {out}");
    }

    #[test]
    fn relu_activation() {
        // 2 layers: 2→2→1, relu
        // Layer 0: w=[1,0, -1,0], b=[0, 0] → [x0, -x0]
        // After relu: [max(0,x0), 0]
        // Layer 1: w=[1, 1], b=[0] → max(0,x0)
        let w0 = [1_i8, 0, -1, 0];
        let b0 = [0.0_f32, 0.0];
        let w1 = [1_i8, 1];
        let b1 = [0.0_f32];
        let m = QuantizedMlp::from_parts(
            &[&w0, &w1],
            &[&b0, &b1],
            &[1.0, 1.0],
            &[0, 0],
            &[1.0, 1.0],
            &[0, 0],
            Activation::Relu,
        )
        .unwrap();
        // input=[5, 0] → layer0=[5, -5] → relu=[5, 0] → layer1=5
        let out = m.predict(&[5.0, 0.0]);
        assert!((out - 5.0).abs() < 1e-4, "positive: got {out}");

        // input=[-3, 0] → layer0=[-3, 3] → relu=[0, 3] → layer1=3
        let out2 = m.predict(&[-3.0, 0.0]);
        assert!((out2 - 3.0).abs() < 1e-4, "negative: got {out2}");
    }

    #[test]
    fn asymmetric_weight_zero_point() {
        // w_zp=10 means real weight = (w_i8 - 10) * w_scale
        // w_i8=[20, 30], w_scale=0.1, w_zp=10
        // real weights: (20-10)*0.1=1.0, (30-10)*0.1=2.0
        // input=[2.0, 3.0], input_scale=1.0, input_zp=0
        // expected: 1.0*2.0 + 2.0*3.0 = 8.0
        let w = [20_i8, 30];
        let b = [0.0_f32];
        let m = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[0.1],
            &[10],
            &[1.0],
            &[0],
            Activation::Identity,
        )
        .unwrap();
        let out = m.predict(&[2.0, 3.0]);
        assert!((out - 8.0).abs() < 0.5, "got {out}");
    }

    #[test]
    fn asymmetric_input_zero_point() {
        // input_zp=5 means real input = (x_i8 - 5) * input_scale
        // input_scale=1.0, so input [7.0] → quantized i8=12 → real=(12-5)*1=7.0
        // w=[1], w_scale=1.0, w_zp=0
        // dot=1*12=12, correction: -5*sum(w)=-5*1=-5 → acc=12-5=7
        // dequant=7*1.0*1.0=7.0
        let w = [1_i8];
        let b = [0.0_f32];
        let m = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[1.0],
            &[0],
            &[1.0],
            &[5],
            Activation::Identity,
        )
        .unwrap();
        let out = m.predict(&[7.0]);
        assert!((out - 7.0).abs() < 1e-4, "got {out}");
    }

    #[test]
    fn multi_output() {
        let w = [1_i8, 0, 0, 1];
        let b = [10.0_f32, 20.0];
        let m = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[1.0],
            &[0],
            &[1.0],
            &[0],
            Activation::Identity,
        )
        .unwrap();
        let mut out = [0.0_f32; 2];
        m.predict_into(&[3.0, 7.0], &mut out);
        assert!((out[0] - 13.0).abs() < 1e-4, "out[0]={}", out[0]);
        assert!((out[1] - 27.0).abs() < 1e-4, "out[1]={}", out[1]);
    }

    #[test]
    fn two_layer_with_scale() {
        // Layer 0: 2→2, w_scale=0.1, i_scale=0.5
        // Layer 1: 2→1, w_scale=0.2, i_scale=0.1
        let w0 = [10_i8, 0, 0, 10]; // identity (real: 1.0, 1.0 diagonal)
        let b0 = [0.0_f32, 0.0];
        let w1 = [5_i8, 5]; // real: 1.0, 1.0
        let b1 = [0.0_f32];
        let m = QuantizedMlp::from_parts(
            &[&w0, &w1],
            &[&b0, &b1],
            &[0.1, 0.2],
            &[0, 0],
            &[0.5, 0.1],
            &[0, 0],
            Activation::Identity,
        )
        .unwrap();
        // input=[2.0, 3.0]
        // L0: quantize(2.0/0.5)=4, (3.0/0.5)=6
        //     dot0=10*4=40, dot1=10*6=60
        //     dequant: 40*0.1*0.5=2.0, 60*0.1*0.5=3.0 → [2.0, 3.0]
        // L1: quantize(2.0/0.1)=20, (3.0/0.1)=30
        //     dot=5*20+5*30=250
        //     dequant: 250*0.2*0.1=5.0
        let out = m.predict(&[2.0, 3.0]);
        assert!((out - 5.0).abs() < 0.5, "got {out}");
    }

    #[test]
    fn accessors() {
        let w0 = [0_i8; 3 * 2];
        let b0 = [0.0_f32; 3];
        let w1 = [0_i8; 1 * 3];
        let b1 = [0.0_f32; 1];
        let m = QuantizedMlp::from_parts(
            &[&w0, &w1],
            &[&b0, &b1],
            &[1.0, 1.0],
            &[0, 0],
            &[1.0, 1.0],
            &[0, 0],
            Activation::Relu,
        )
        .unwrap();
        assert_eq!(m.n_inputs(), 2);
        assert_eq!(m.n_outputs(), 1);
        assert_eq!(m.n_layers(), 2);
        assert!(matches!(m.activation(), Activation::Relu));
    }

    #[test]
    fn validation_rejects_empty() {
        let r: Result<QuantizedMlp, _> =
            QuantizedMlp::from_parts(&[], &[], &[], &[], &[], &[], Activation::Relu);
        assert!(r.is_err());
    }

    #[test]
    fn validation_rejects_mismatched_arrays() {
        let w = [0_i8; 4];
        let b = [0.0_f32; 2];
        let r = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[1.0, 1.0], // 2 scales but only 1 layer
            &[0],
            &[1.0],
            &[0],
            Activation::Relu,
        );
        assert!(r.is_err());
    }

    #[test]
    fn validation_rejects_bad_scale() {
        let w = [0_i8; 4];
        let b = [0.0_f32; 2];
        let r = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[-1.0], // negative scale
            &[0],
            &[1.0],
            &[0],
            Activation::Relu,
        );
        assert!(r.is_err());
    }

    #[test]
    fn validation_rejects_non_finite_bias() {
        let w = [0_i8; 4];
        let b = [f32::NAN, 0.0];
        let r =
            QuantizedMlp::from_parts(&[&w], &[&b], &[1.0], &[0], &[1.0], &[0], Activation::Relu);
        assert!(r.is_err());
    }

    #[test]
    fn validation_rejects_layer_size_mismatch() {
        // Layer 0: 2→3, Layer 1: 4→1 (should be 3→1)
        let w0 = [0_i8; 3 * 2];
        let b0 = [0.0_f32; 3];
        let w1 = [0_i8; 1 * 4]; // wrong: in_size=4 != prev out_size=3
        let b1 = [0.0_f32; 1];
        let r = QuantizedMlp::from_parts(
            &[&w0, &w1],
            &[&b0, &b1],
            &[1.0, 1.0],
            &[0, 0],
            &[1.0, 1.0],
            &[0, 0],
            Activation::Relu,
        );
        assert!(r.is_err());
    }

    #[test]
    #[should_panic(expected = "output_size == 1")]
    fn predict_panics_multi_output() {
        let w = [0_i8; 4];
        let b = [0.0_f32; 2];
        let m =
            QuantizedMlp::from_parts(&[&w], &[&b], &[1.0], &[0], &[1.0], &[0], Activation::Relu)
                .unwrap();
        m.predict(&[1.0, 2.0]);
    }

    #[test]
    #[should_panic]
    fn predict_panics_wrong_input_len() {
        let w = [0_i8; 4];
        let b = [0.0_f32; 2];
        let m =
            QuantizedMlp::from_parts(&[&w], &[&b], &[1.0], &[0], &[1.0], &[0], Activation::Relu)
                .unwrap();
        m.predict(&[1.0]); // expects 2 inputs
    }

    #[test]
    fn clamps_to_i8_range() {
        // Large input that would overflow i8 range after quantization
        let w = [1_i8];
        let b = [0.0_f32];
        let m = QuantizedMlp::from_parts(
            &[&w],
            &[&b],
            &[1.0],
            &[0],
            &[1.0],
            &[0],
            Activation::Identity,
        )
        .unwrap();
        // 200.0 / 1.0 = 200 → clamped to 127
        let out = m.predict(&[200.0]);
        assert!((out - 127.0).abs() < 1e-4, "got {out}");

        // -200.0 → clamped to -128
        let out2 = m.predict(&[-200.0]);
        assert!((out2 - (-128.0)).abs() < 1e-4, "got {out2}");
    }
}
