/// Generates a named feature vector struct where every field is `f64`.
///
/// The struct converts to `&[f64]` at zero cost via `repr(C)` pointer
/// cast, for passing to adaptive filters (`LmsFilter`, `RlsFilter`),
/// classifiers (`LogisticRegression`, `OnlineKMeans`),
/// and optimizers (`Adam`, `AdaGrad`) from the `nexus-stats-regression` crate.
///
/// All fields are `pub` and `f64`. Construct via struct literal or
/// `new()` (which applies defaults). Mutate fields directly.
///
/// # Example
///
/// ```
/// use nexus_stats_core::feature_vector;
///
/// feature_vector! {
///     pub struct MarketFeatures {
///         autocorrelation,
///         spread = 1.0,
///         imbalance,
///     }
/// }
///
/// let f = MarketFeatures { autocorrelation: 0.3, spread: 1.5, imbalance: -0.2 };
/// assert_eq!(f.as_slice(), &[0.3, 1.5, -0.2]);
/// assert_eq!(MarketFeatures::DIMENSIONS, 3);
/// ```
///
/// The struct must keep `f64` alignment, so `#[repr(packed)]` is rejected at
/// compile time (it would make `as_slice` hand out a misaligned `&[f64]`):
///
/// ```compile_fail,E0080
/// use nexus_stats_core::feature_vector;
///
/// feature_vector! {
///     #[repr(packed)]
///     pub struct Packed { a, b }
/// }
/// ```
///
/// Partial packing that lowers the alignment below 8 is rejected the same way:
///
/// ```compile_fail,E0080
/// use nexus_stats_core::feature_vector;
///
/// feature_vector! {
///     #[repr(packed(4))]
///     pub struct Packed4 { a, b }
/// }
/// ```
#[macro_export]
macro_rules! feature_vector {
    // Internal: default value or 0.0
    (@default $default:expr) => { $default };
    (@default) => { 0.0 };

    (
        $(#[$meta:meta])*
        $vis:vis struct $name:ident {
            $( $field:ident $( = $default:expr )? ),+ $(,)?
        }
    ) => {
        $(#[$meta])*
        #[derive(Debug, Clone, Copy, PartialEq)]
        #[repr(C)]
        $vis struct $name {
            $(
                /// Feature field.
                pub $field: f64,
            )*
        }

        impl $name {
            /// Number of features (compile-time constant).
            pub const DIMENSIONS: usize = [$(stringify!($field)),*].len();

            /// Field names in declaration order (for logging/debug).
            #[allow(dead_code)]
            pub const FIELD_NAMES: &[&str] = &[$(stringify!($field)),*];

            /// Creates a feature vector with default values.
            /// Fields without `= value` default to 0.0.
            #[inline]
            #[must_use]
            pub fn new() -> Self {
                Self {
                    $( $field: $crate::feature_vector!(@default $($default)? ), )*
                }
            }

            /// Returns the feature values as a slice.
            ///
            /// Zero-cost: pointer cast on `repr(C)` struct of all `f64` fields.
            #[inline]
            #[must_use]
            pub fn as_slice(&self) -> &[f64] {
                // SAFETY: a repr(C) struct of DIMENSIONS `f64` fields has the
                // layout of `[f64; DIMENSIONS]`. The two compile-time
                // assertions below the impl are what guarantee it: the size
                // one rules out padding, the alignment one rules out a
                // `repr(packed)` among the caller's attributes.
                unsafe {
                    core::slice::from_raw_parts(
                        self as *const Self as *const f64,
                        Self::DIMENSIONS,
                    )
                }
            }

            /// Returns a mutable slice over the feature values.
            #[inline]
            #[must_use]
            pub fn as_mut_slice(&mut self) -> &mut [f64] {
                // SAFETY: same layout justification as as_slice.
                unsafe {
                    core::slice::from_raw_parts_mut(
                        self as *mut Self as *mut f64,
                        Self::DIMENSIONS,
                    )
                }
            }
        }

        impl Default for $name {
            #[inline]
            fn default() -> Self {
                Self::new()
            }
        }

        impl AsRef<[f64]> for $name {
            #[inline]
            fn as_ref(&self) -> &[f64] {
                self.as_slice()
            }
        }

        impl AsMut<[f64]> for $name {
            #[inline]
            fn as_mut(&mut self) -> &mut [f64] {
                self.as_mut_slice()
            }
        }

        // Compile-time assertion: no padding in the struct.
        const _: () = assert!(
            core::mem::size_of::<$name>() == core::mem::size_of::<f64>() * $name::DIMENSIONS,
            "feature_vector struct has unexpected padding"
        );
        // `as_slice` reinterprets the struct as `[f64; N]`, so it must also
        // keep f64 alignment: a `#[repr(packed)]` among the caller's
        // attributes adds no padding but lowers the alignment.
        const _: () = assert!(
            core::mem::align_of::<$name>() >= core::mem::align_of::<f64>(),
            "feature_vector struct must keep f64 alignment; #[repr(packed)] is not supported"
        );
    };
}

#[cfg(test)]
mod tests {
    feature_vector! {
        struct TestVec {
            a,
            b = 5.0,
            c,
        }
    }

    feature_vector! {
        pub struct PubVec {
            x = 1.0,
            y = 2.0,
        }
    }

    feature_vector! {
        struct SingleField {
            only,
        }
    }

    #[test]
    fn defaults() {
        let v = TestVec::new();
        assert_eq!(v.a, 0.0);
        assert_eq!(v.b, 5.0);
        assert_eq!(v.c, 0.0);
    }

    #[test]
    fn as_slice_matches_fields() {
        let v = TestVec {
            a: 1.0,
            b: 2.0,
            c: 3.0,
        };
        assert_eq!(v.as_slice(), &[1.0, 2.0, 3.0]);
    }

    #[test]
    fn dimensions() {
        assert_eq!(TestVec::DIMENSIONS, 3);
        assert_eq!(PubVec::DIMENSIONS, 2);
        assert_eq!(SingleField::DIMENSIONS, 1);
    }

    #[test]
    fn field_names() {
        assert_eq!(TestVec::FIELD_NAMES, &["a", "b", "c"]);
        assert_eq!(PubVec::FIELD_NAMES, &["x", "y"]);
    }

    #[test]
    fn direct_field_mutation() {
        let mut v = TestVec::new();
        v.a = 10.0;
        assert_eq!(v.a, 10.0);
        assert_eq!(v.as_slice()[0], 10.0);
    }

    #[test]
    fn as_mut_slice_round_trip() {
        let mut v = TestVec::new();
        v.as_mut_slice()[1] = 42.0;
        assert_eq!(v.b, 42.0);
    }

    #[test]
    fn size_equals_array() {
        assert_eq!(
            core::mem::size_of::<TestVec>(),
            core::mem::size_of::<[f64; 3]>()
        );
        assert_eq!(
            core::mem::size_of::<PubVec>(),
            core::mem::size_of::<[f64; 2]>()
        );
        assert_eq!(
            core::mem::size_of::<SingleField>(),
            core::mem::size_of::<[f64; 1]>()
        );
    }

    #[test]
    fn default_trait() {
        let v = TestVec::default();
        assert_eq!(v.a, 0.0);
        assert_eq!(v.b, 5.0);
        assert_eq!(v.c, 0.0);
    }

    #[test]
    fn as_ref_trait() {
        let v = TestVec {
            a: 1.0,
            b: 2.0,
            c: 3.0,
        };
        let slice: &[f64] = v.as_ref();
        assert_eq!(slice, &[1.0, 2.0, 3.0]);
    }

    #[test]
    fn as_mut_trait() {
        let mut v = TestVec::new();
        let slice: &mut [f64] = v.as_mut();
        slice[0] = 7.0;
        slice[2] = 9.0;
        assert_eq!(v.a, 7.0);
        assert_eq!(v.c, 9.0);
    }

    #[test]
    fn copy_semantics() {
        let v = TestVec {
            a: 1.0,
            b: 2.0,
            c: 3.0,
        };
        let v2 = v;
        assert_eq!(v.as_slice(), v2.as_slice());
    }

    #[test]
    fn pub_defaults() {
        let v = PubVec::new();
        assert_eq!(v.x, 1.0);
        assert_eq!(v.y, 2.0);
    }
}
