use shinri_core::Context;

#[test]
fn identical_numerals_share_one_node_and_one_rat() {
    let mut ctx = Context::new();
    let int = ctx.int_sort();
    let v = shinri_num::Rational::from_int(42i128.into());
    let a = ctx.mk_numeral(v.clone(), int);
    let _b = ctx.mk_numeral(v.clone(), int);
    let c = ctx.mk_numeral(v, int);
    // Maximal sharing: rebuilding the same numeral never yields a new id.
    assert_eq!(a, c);
}

#[test]
fn distinct_bools_are_distinct_ids() {
    let mut ctx = Context::new();
    assert_ne!(ctx.mk_const_bool(true), ctx.mk_const_bool(false));
}
