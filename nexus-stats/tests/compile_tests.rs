#![allow(
    clippy::float_cmp,
    clippy::approx_constant,
    clippy::clone_on_copy,
    clippy::suboptimal_flops
)]
//! Compile tests for feature_vector! macro and optimizer integration.
//!
//! These tests verify that various macro invocations and usage patterns
//! actually compile. If any of these fail to compile, the macro has a
//! bug in its expansion.

use nexus_stats::feature_vector;

// === feature_vector! macro: struct generation ===

// Basic: no defaults
feature_vector! {
    pub struct BasicVec {
        a,
        b,
        c,
    }
}

// With defaults on some fields
feature_vector! {
    pub struct MixedDefaults {
        alpha,
        beta = 0.9,
        gamma,
        delta = 1e-8,
    }
}

// All defaults
feature_vector! {
    pub struct AllDefaults {
        x = 1.0,
        y = 2.0,
        z = 3.0,
    }
}

// Single field
feature_vector! {
    pub struct SingleField {
        value,
    }
}

// Single field with default
feature_vector! {
    pub struct SingleDefault {
        value = 42.0,
    }
}

// Private (no pub)
feature_vector! {
    struct PrivateVec {
        a,
        b,
    }
}

// pub(crate)
feature_vector! {
    pub(crate) struct CrateVec {
        a,
        b,
    }
}

// Trailing comma
feature_vector! {
    pub struct TrailingComma {
        a,
        b,
        c,
    }
}

// No trailing comma
feature_vector! {
    pub struct NoTrailingComma {
        a,
        b,
        c
    }
}

// Many fields (stress test)
feature_vector! {
    pub struct WideVec {
        f0, f1, f2, f3, f4, f5, f6, f7,
        f8, f9, f10, f11, f12, f13, f14, f15,
    }
}

// Negative default
feature_vector! {
    pub struct NegativeDefault {
        a = -1.0,
        b = -100.5,
    }
}

// Expression default
feature_vector! {
    pub struct ExprDefault {
        a = 1.0 / 3.0,
        b = 2.0 * 3.14159,
    }
}

// Attributes that keep f64 alignment stay accepted
feature_vector! {
    #[repr(align(16))]
    pub struct Aligned16 {
        a,
        b,
    }
}

feature_vector! {
    #[repr(packed(8))]
    pub struct Packed8 {
        a,
        b,
        c,
    }
}

// === Compile-time property verification ===

#[test]
fn dimensions_are_correct() {
    assert_eq!(BasicVec::DIMENSIONS, 3);
    assert_eq!(MixedDefaults::DIMENSIONS, 4);
    assert_eq!(AllDefaults::DIMENSIONS, 3);
    assert_eq!(SingleField::DIMENSIONS, 1);
    assert_eq!(SingleDefault::DIMENSIONS, 1);
    assert_eq!(PrivateVec::DIMENSIONS, 2);
    assert_eq!(CrateVec::DIMENSIONS, 2);
    assert_eq!(WideVec::DIMENSIONS, 16);
    assert_eq!(NegativeDefault::DIMENSIONS, 2);
    assert_eq!(ExprDefault::DIMENSIONS, 2);
}

#[test]
fn field_names_are_correct() {
    assert_eq!(BasicVec::FIELD_NAMES, &["a", "b", "c"]);
    assert_eq!(
        MixedDefaults::FIELD_NAMES,
        &["alpha", "beta", "gamma", "delta"]
    );
    assert_eq!(SingleField::FIELD_NAMES, &["value"]);
    assert_eq!(
        WideVec::FIELD_NAMES,
        &[
            "f0", "f1", "f2", "f3", "f4", "f5", "f6", "f7", "f8", "f9", "f10", "f11", "f12", "f13",
            "f14", "f15"
        ]
    );
}

// === Size/layout verification ===

#[test]
fn sizes_match_arrays() {
    assert_eq!(
        core::mem::size_of::<BasicVec>(),
        core::mem::size_of::<[f64; 3]>()
    );
    assert_eq!(
        core::mem::size_of::<MixedDefaults>(),
        core::mem::size_of::<[f64; 4]>()
    );
    assert_eq!(
        core::mem::size_of::<SingleField>(),
        core::mem::size_of::<[f64; 1]>()
    );
    assert_eq!(
        core::mem::size_of::<WideVec>(),
        core::mem::size_of::<[f64; 16]>()
    );
}

#[test]
fn alignment_is_f64() {
    assert_eq!(
        core::mem::align_of::<BasicVec>(),
        core::mem::align_of::<f64>()
    );
    assert_eq!(
        core::mem::align_of::<WideVec>(),
        core::mem::align_of::<f64>()
    );
}

#[test]
fn repr_attributes_that_keep_alignment() {
    assert_eq!(core::mem::align_of::<Aligned16>(), 16);
    assert_eq!(
        core::mem::align_of::<Packed8>(),
        core::mem::align_of::<f64>()
    );
    let a = Aligned16 { a: 1.0, b: 2.0 };
    assert_eq!(a.as_slice(), &[1.0, 2.0]);
    let p = Packed8 {
        a: 1.0,
        b: 2.0,
        c: 3.0,
    };
    assert_eq!(p.as_slice(), &[1.0, 2.0, 3.0]);
}

// === as_slice / as_mut_slice correctness ===

#[test]
fn as_slice_preserves_field_order() {
    let v = BasicVec {
        a: 1.0,
        b: 2.0,
        c: 3.0,
    };
    assert_eq!(v.as_slice(), &[1.0, 2.0, 3.0]);
}

#[test]
fn as_slice_with_defaults() {
    let v = MixedDefaults::new();
    assert_eq!(v.as_slice(), &[0.0, 0.9, 0.0, 1e-8]);
}

#[test]
fn as_slice_single_field() {
    let v = SingleField { value: 7.5 };
    assert_eq!(v.as_slice(), &[7.5]);
}

#[test]
fn as_slice_wide_vec() {
    let mut v = WideVec::new();
    v.f0 = 100.0;
    v.f15 = 200.0;
    let s = v.as_slice();
    assert_eq!(s[0], 100.0);
    assert_eq!(s[15], 200.0);
    assert_eq!(s.len(), 16);
}

#[test]
fn as_mut_slice_modifies_fields() {
    let mut v = BasicVec::new();
    let s = v.as_mut_slice();
    s[0] = 10.0;
    s[1] = 20.0;
    s[2] = 30.0;
    assert_eq!(v.a, 10.0);
    assert_eq!(v.b, 20.0);
    assert_eq!(v.c, 30.0);
}

#[test]
fn field_mutation_visible_in_slice() {
    let mut v = BasicVec::new();
    v.b = 99.0;
    assert_eq!(v.as_slice()[1], 99.0);
}

// === Default / new() ===

#[test]
fn new_applies_defaults() {
    let v = AllDefaults::new();
    assert_eq!(v.x, 1.0);
    assert_eq!(v.y, 2.0);
    assert_eq!(v.z, 3.0);
}

#[test]
fn new_zeros_without_default() {
    let v = BasicVec::new();
    assert_eq!(v.a, 0.0);
    assert_eq!(v.b, 0.0);
    assert_eq!(v.c, 0.0);
}

#[test]
fn default_trait_matches_new() {
    let v1 = MixedDefaults::new();
    let v2 = MixedDefaults::default();
    assert_eq!(v1, v2);
}

#[test]
fn negative_defaults_work() {
    let v = NegativeDefault::new();
    assert_eq!(v.a, -1.0);
    assert_eq!(v.b, -100.5);
}

#[test]
fn expression_defaults_work() {
    let v = ExprDefault::new();
    assert!((v.a - 1.0 / 3.0).abs() < f64::EPSILON);
    assert!((v.b - 2.0 * 3.14159).abs() < f64::EPSILON);
}

// === Trait impls ===

#[test]
fn as_ref_works() {
    let v = BasicVec {
        a: 1.0,
        b: 2.0,
        c: 3.0,
    };
    let r: &[f64] = v.as_ref();
    assert_eq!(r, &[1.0, 2.0, 3.0]);
}

#[test]
fn as_mut_works() {
    let mut v = BasicVec::new();
    let r: &mut [f64] = v.as_mut();
    r[0] = 5.0;
    assert_eq!(v.a, 5.0);
}

#[test]
fn copy_semantics() {
    let v1 = BasicVec {
        a: 1.0,
        b: 2.0,
        c: 3.0,
    };
    let v2 = v1; // Copy
    assert_eq!(v1.as_slice(), v2.as_slice()); // v1 still usable
}

#[test]
fn clone_semantics() {
    let v1 = BasicVec {
        a: 1.0,
        b: 2.0,
        c: 3.0,
    };
    let v2 = v1.clone();
    assert_eq!(v1, v2);
}

#[test]
fn debug_format() {
    let v = BasicVec {
        a: 1.0,
        b: 2.0,
        c: 3.0,
    };
    let s = format!("{:?}", v);
    assert!(s.contains("BasicVec"));
    assert!(s.contains("1.0"));
}

// === Integration with filters and optimizers ===
// These require the `regression` feature (and alloc, some std|libm) for the filter/optimizer types.

#[cfg(all(feature = "regression", feature = "alloc"))]
#[test]
fn works_with_lms_filter() {
    use nexus_stats::learning::LmsFilter;

    feature_vector! {
        struct LmsFeatures {
            signal,
            noise,
            trend,
        }
    }

    let mut filter = LmsFilter::builder()
        .dimensions(LmsFeatures::DIMENSIONS)
        .learning_rate(0.01)
        .build()
        .unwrap();

    let f = LmsFeatures {
        signal: 0.5,
        noise: 0.1,
        trend: 0.8,
    };
    filter.update(f.as_slice(), 1.0).unwrap();
    assert_eq!(filter.count(), 1);
}

#[cfg(all(feature = "regression", feature = "alloc"))]
#[test]
fn works_with_nlms_filter() {
    use nexus_stats::learning::NlmsFilter;

    feature_vector! {
        struct NlmsFeatures {
            x,
            y,
        }
    }

    let mut filter = NlmsFilter::builder()
        .dimensions(NlmsFeatures::DIMENSIONS)
        .learning_rate(0.5)
        .build()
        .unwrap();

    let f = NlmsFeatures { x: 1.0, y: 2.0 };
    filter.update(f.as_slice(), 5.0).unwrap();
    assert_eq!(filter.count(), 1);
}

#[cfg(all(feature = "regression", feature = "alloc"))]
#[test]
fn works_with_rls_filter() {
    use nexus_stats::learning::RlsFilter;

    feature_vector! {
        struct RlsFeatures {
            a,
            b,
        }
    }

    let mut filter = RlsFilter::builder()
        .dimensions(RlsFeatures::DIMENSIONS)
        .forgetting_factor(0.99)
        .build()
        .unwrap();

    let f = RlsFeatures { a: 1.0, b: 0.5 };
    filter.update(f.as_slice(), 2.0).unwrap();
    assert_eq!(filter.count(), 1);
}

#[cfg(all(feature = "regression", feature = "alloc"))]
#[test]
fn works_with_online_gd() {
    use nexus_stats::learning::OnlineGd;

    feature_vector! {
        struct GdGradient {
            dx,
            dy,
        }
    }

    let mut opt = OnlineGd::builder()
        .dimensions(GdGradient::DIMENSIONS)
        .learning_rate(0.01)
        .build()
        .unwrap();

    let g = GdGradient { dx: 1.0, dy: -0.5 };
    opt.step(g.as_slice()).unwrap();
    assert_eq!(opt.count(), 1);
}

#[cfg(all(
    feature = "regression",
    feature = "alloc",
    any(feature = "std", feature = "libm")
))]
#[test]
fn works_with_adagrad() {
    use nexus_stats::learning::AdaGrad;

    feature_vector! {
        struct AgGradient {
            dx,
            dy,
            dz,
        }
    }

    let mut opt = AdaGrad::builder()
        .dimensions(AgGradient::DIMENSIONS)
        .learning_rate(0.1)
        .build()
        .unwrap();

    let g = AgGradient {
        dx: 1.0,
        dy: -0.5,
        dz: 0.2,
    };
    opt.step(g.as_slice()).unwrap();
    assert_eq!(opt.count(), 1);
}

#[cfg(all(
    feature = "regression",
    feature = "alloc",
    any(feature = "std", feature = "libm")
))]
#[test]
fn works_with_adam() {
    use nexus_stats::learning::Adam;

    feature_vector! {
        struct AdamGradient {
            dx,
            dy,
        }
    }

    let mut opt = Adam::builder()
        .dimensions(AdamGradient::DIMENSIONS)
        .learning_rate(0.001)
        .build()
        .unwrap();

    let g = AdamGradient { dx: 1.0, dy: -0.5 };
    opt.step(g.as_slice()).unwrap();
    assert_eq!(opt.count(), 1);
}

#[cfg(all(
    feature = "regression",
    feature = "alloc",
    any(feature = "std", feature = "libm")
))]
#[test]
fn works_with_adam_weight_decay() {
    use nexus_stats::learning::Adam;

    feature_vector! {
        struct WdGradient {
            dx,
            dy,
        }
    }

    let mut opt = Adam::builder()
        .dimensions(WdGradient::DIMENSIONS)
        .learning_rate(0.001)
        .weight_decay(0.01)
        .build()
        .unwrap();

    let g = WdGradient { dx: 1.0, dy: -0.5 };
    opt.step(g.as_slice()).unwrap();
    assert_eq!(opt.count(), 1);
}

#[cfg(all(
    feature = "regression",
    feature = "alloc",
    any(feature = "std", feature = "libm")
))]
#[test]
fn works_with_logistic_regression() {
    use nexus_stats::regression::LogisticRegression;

    feature_vector! {
        struct LrFeatures {
            x1,
            x2,
        }
    }

    let mut lr = LogisticRegression::builder()
        .dimensions(LrFeatures::DIMENSIONS)
        .learning_rate(0.1)
        .build()
        .unwrap();

    let f = LrFeatures { x1: 0.5, x2: -0.3 };
    lr.update(f.as_slice(), true);
    assert_eq!(lr.count(), 1);
}

#[cfg(all(feature = "regression", feature = "alloc"))]
#[test]
fn works_with_online_kmeans() {
    use nexus_stats::learning::OnlineKMeans;

    feature_vector! {
        struct KmFeatures {
            x,
            y,
        }
    }

    let mut km = OnlineKMeans::builder()
        .dimensions(KmFeatures::DIMENSIONS)
        .clusters(3)
        .learning_rate(0.1)
        .build()
        .unwrap();

    let f = KmFeatures { x: 1.0, y: 2.0 };
    km.update(f.as_slice());
    assert_eq!(km.count(), 1);
}

// === Realistic usage pattern ===

#[cfg(all(
    feature = "regression",
    feature = "alloc",
    any(feature = "std", feature = "libm")
))]
#[test]
fn realistic_training_loop() {
    use nexus_stats::learning::Adam;

    feature_vector! {
        struct ModelParams {
            weight,
            bias = 0.1,
        }
    }

    let mut opt = Adam::builder()
        .dimensions(ModelParams::DIMENSIONS)
        .learning_rate(0.01)
        .build()
        .unwrap();

    // Simulated training: minimize (weight - 3)² + (bias - 1)²
    opt.set_parameters(&[0.0, 0.1]);
    for _ in 0..2000 {
        let p = opt.parameters();
        let mut grad = ModelParams::new();
        grad.weight = 2.0 * (p[0] - 3.0);
        grad.bias = 2.0 * (p[1] - 1.0);
        opt.step(grad.as_slice()).unwrap();
    }

    let p = opt.parameters();
    assert!((p[0] - 3.0).abs() < 0.1, "weight = {}, expected ~3.0", p[0]);
    assert!((p[1] - 1.0).abs() < 0.1, "bias = {}, expected ~1.0", p[1]);
}

// === AsRef<[f64]> generic usage ===

#[test]
fn generic_function_accepts_feature_vector() {
    fn sum_features(features: &impl AsRef<[f64]>) -> f64 {
        features.as_ref().iter().sum()
    }

    let v = BasicVec {
        a: 1.0,
        b: 2.0,
        c: 3.0,
    };
    assert_eq!(sum_features(&v), 6.0);
}

#[test]
fn generic_mut_function_accepts_feature_vector() {
    fn zero_features(features: &mut impl AsMut<[f64]>) {
        features.as_mut().fill(0.0);
    }

    let mut v = AllDefaults::new();
    zero_features(&mut v);
    assert_eq!(v.as_slice(), &[0.0, 0.0, 0.0]);
}
