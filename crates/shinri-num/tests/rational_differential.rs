use num_bigint::BigInt;
use num_rational::BigRational;
use proptest::prelude::*;
use shinri_num::{Integer, Rational};

fn shinri(n: i128, d: i128) -> Rational {
    Rational::new(Integer::from(n), Integer::from(d))
}

fn oracle(n: i128, d: i128) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

// Both types canonicalize (reduced, positive denominator), so equal values have
// equal numerator/denominator decimal strings.
fn agree(s: &Rational, o: &BigRational) -> bool {
    s.numer().to_string() == o.numer().to_string() && s.denom().to_string() == o.denom().to_string()
}

proptest! {
    // The folded Rational must match the oracle on every op, including when
    // operands overflow i128 and spill to Big (and demote back). Spec §7 / §10.
    #[test]
    fn rational_matches_oracle(
        an in -1_000_000i128..1_000_000,
        ad in 1i128..1_000_000,
        bn in -1_000_000i128..1_000_000,
        bd in 1i128..1_000_000,
        scale in prop::sample::select(vec![1i128, 1_000_000_000_000_000_000]),
    ) {
        let (an, ad) = (an.saturating_mul(scale), ad);
        let (bn, bd) = (bn, bd.saturating_mul(scale));

        let (sa, sb) = (shinri(an, ad), shinri(bn, bd));
        let (oa, ob) = (oracle(an, ad), oracle(bn, bd));

        prop_assert!(agree(&(sa.clone() + sb.clone()), &(oa.clone() + ob.clone())));
        prop_assert!(agree(&(sa.clone() - sb.clone()), &(oa.clone() - ob.clone())));
        prop_assert!(agree(&(sa.clone() * sb.clone()), &(oa.clone() * ob.clone())));
        if bn != 0 {
            prop_assert!(agree(&(sa.clone() / sb.clone()), &(oa.clone() / ob.clone())));
        }
        prop_assert_eq!(sa.cmp(&sb), oa.cmp(&ob));
    }
}
