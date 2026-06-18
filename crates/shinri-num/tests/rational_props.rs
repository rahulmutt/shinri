use num_rational::BigRational;
use proptest::prelude::*;
use shinri_num::Rational;

/// Build identical shinri / oracle integers, scaled by 2^62 `times` times so
/// values exceed i128 and exercise the Big path.
fn scaled(base: i64, times: u32) -> (shinri_num::Integer, num_bigint::BigInt) {
    let pow = 1i128 << 62;
    let mut s = shinri_num::Integer::from(base);
    let mut b = num_bigint::BigInt::from(base);
    for _ in 0..times {
        s = s.clone() * shinri_num::Integer::from(pow);
        b = b * num_bigint::BigInt::from(pow);
    }
    (s, b)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn rational_ops_match_bigrational(
        an in any::<i64>(), ad in 1i64..=i64::MAX,
        bn in any::<i64>(), bd in 1i64..=i64::MAX,
        san in 0u32..3, sad in 0u32..3, sbn in 0u32..3, sbd in 0u32..3,
    ) {
        let (an_s, an_b) = scaled(an, san);
        let (ad_s, ad_b) = scaled(ad, sad);
        let (bn_s, bn_b) = scaled(bn, sbn);
        let (bd_s, bd_b) = scaled(bd, sbd);
        let sa = Rational::new(an_s, ad_s);
        let sb = Rational::new(bn_s, bd_s);
        let ba = BigRational::new(an_b, ad_b);
        let bb = BigRational::new(bn_b, bd_b);

        prop_assert_eq!(
            rat_str(sa.clone() + sb.clone()),
            bb_str(ba.clone() + bb.clone()),
            "add mismatch: ({}/{}) + ({}/{})", an, ad, bn, bd
        );
        prop_assert_eq!(
            rat_str(sa.clone() - sb.clone()),
            bb_str(ba.clone() - bb.clone()),
            "sub mismatch: ({}/{}) - ({}/{})", an, ad, bn, bd
        );
        prop_assert_eq!(
            rat_str(sa.clone() * sb.clone()),
            bb_str(ba.clone() * bb.clone()),
            "mul mismatch: ({}/{}) * ({}/{})", an, ad, bn, bd
        );
        if !sb.is_zero() {
            prop_assert_eq!(
                rat_str(sa.clone() / sb.clone()),
                bb_str(ba.clone() / bb.clone()),
                "div mismatch: ({}/{}) / ({}/{})", an, ad, bn, bd
            );
        }
        prop_assert_eq!(
            sa.cmp(&sb),
            ba.cmp(&bb),
            "cmp mismatch: ({}/{}) vs ({}/{})", an, ad, bn, bd
        );
    }
}

fn rat_str(r: Rational) -> String {
    format!("{}/{}", r.numer(), r.denom())
}
fn bb_str(r: BigRational) -> String {
    format!("{}/{}", r.numer(), r.denom())
}
