use num_bigint::BigInt;
use proptest::prelude::*;
use shinri_num::Integer;

fn to_big(i: i128) -> BigInt {
    BigInt::from(i)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn add_matches_bigint(a in any::<i128>(), b in any::<i128>(), scale_a in 0u32..4, scale_b in 0u32..4) {
        // Multiply operands by 2^(62*scale) to push past the i128 boundary.
        let mut si = Integer::from(a);
        let mut bi = to_big(a);
        for _ in 0..scale_a {
            si = si.clone() * Integer::from(1i128 << 62);
            bi *= BigInt::from(1i128 << 62);
        }
        let mut sj = Integer::from(b);
        let mut bj = to_big(b);
        for _ in 0..scale_b {
            sj = sj.clone() * Integer::from(1i128 << 62);
            bj *= BigInt::from(1i128 << 62);
        }

        let sum = si.clone() + sj.clone();
        prop_assert_eq!(sum.to_string(), (bi.clone() + bj.clone()).to_string());

        let diff = si.clone() - sj.clone();
        prop_assert_eq!(diff.to_string(), (bi.clone() - bj.clone()).to_string());

        let prod = si.clone() * sj.clone();
        prop_assert_eq!(prod.to_string(), (bi.clone() * bj.clone()).to_string());

        if !sj.is_zero() {
            let (q, r) = si.div_rem(&sj);
            let (bq, br) = (bi.clone() / bj.clone(), bi.clone() % bj.clone());
            prop_assert_eq!(q.to_string(), bq.to_string(), "quotient mismatch: {} / {}", si, sj);
            prop_assert_eq!(r.to_string(), br.to_string(), "remainder mismatch: {} % {}", si, sj);
            // reconstruction identity: q*sj + r == si
            prop_assert_eq!(q * sj.clone() + r, si.clone(), "reconstruction failed for si={}", si);
        }

        let g = si.gcd(&sj);
        let bg = num_integer_gcd(bi.clone(), bj.clone());
        prop_assert_eq!(g.to_string(), bg.to_string(), "gcd mismatch: gcd({}, {})", si, sj);

        prop_assert_eq!(si.cmp(&sj), bi.cmp(&bj), "cmp mismatch: {} vs {}", si, sj);
    }
}

fn num_integer_gcd(a: BigInt, b: BigInt) -> BigInt {
    // Euclidean on BigInt for an independent reference.
    let (mut a, mut b) = (magnitude_abs(a), magnitude_abs(b));
    while b != BigInt::from(0) {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

fn magnitude_abs(x: BigInt) -> BigInt {
    if x < BigInt::from(0) {
        -x
    } else {
        x
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn from_str_radix_matches_bigint(digits in "[0-9]{1,40}") {
        let ours = shinri_num::Integer::from_str_radix(&digits, 10).unwrap();
        let theirs: BigInt = digits.parse().unwrap();
        prop_assert_eq!(ours.to_string(), theirs.to_string());
    }
}
