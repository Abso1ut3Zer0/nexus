#[test]
fn pod_compile_fail() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile_fail/padded_struct_rejected.rs");
    t.compile_fail("tests/compile_fail/nonzero_rejected.rs");
    t.compile_fail("tests/compile_fail/char_rejected.rs");
    t.pass("tests/compile_fail/primitives_accepted.rs");
    t.pass("tests/compile_fail/array_accepted.rs");
}
