use num_bigint::BigInt;
use num_rational::BigRational;
use proptest::prelude::*;
use shinri_num::{Integer, Rational};

fn sr(n: i64, d: i64) -> Rational {
    Rational::new(Integer::from(n), Integer::from(d))
}
fn br(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn rational_ops_match_bigrational(
        an in any::<i64>(), ad in 1i64..=i64::MAX,
        bn in any::<i64>(), bd in 1i64..=i64::MAX,
    ) {
        let sa = sr(an, ad);
        let sb = sr(bn, bd);
        let ba = br(an, ad);
        let bb = br(bn, bd);

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
