#![no_main]
use libfuzzer_sys::fuzz_target;
use num_bigint::BigInt;
use shinri_num::Integer;

// Cross-check add/sub/mul/div against BigInt on fuzzed limb sequences.
fuzz_target!(|data: (Vec<u64>, bool, Vec<u64>, bool)| {
    let (al, asign, bl, bsign) = data;
    if al.len() > 64 || bl.len() > 64 {
        return; // keep inputs bounded
    }
    let a = limbs_to_integer(&al, asign);
    let b = limbs_to_integer(&bl, bsign);
    let ba = integer_to_bigint(&a);
    let bb = integer_to_bigint(&b);

    assert_eq!((a.clone() + b.clone()).to_string(), (&ba + &bb).to_string());
    assert_eq!((a.clone() - b.clone()).to_string(), (&ba - &bb).to_string());
    assert_eq!((a.clone() * b.clone()).to_string(), (&ba * &bb).to_string());
    if !b.is_zero() {
        let (q, r) = a.div_rem(&b);
        assert_eq!(q.to_string(), (&ba / &bb).to_string());
        assert_eq!(r.to_string(), (&ba % &bb).to_string());
    }
});

fn limbs_to_integer(limbs: &[u64], negative: bool) -> Integer {
    // Build sum(limb_i * 2^(64*i)) with sign.
    let mut acc = Integer::from(0i128);
    let shift = Integer::from(1i128 << 32) * Integer::from(1i128 << 32); // 2^64
    let mut pow = Integer::from(1i128);
    for &l in limbs {
        acc = acc + Integer::from(l) * pow.clone();
        pow = pow * shift.clone();
    }
    if negative {
        -acc
    } else {
        acc
    }
}

fn integer_to_bigint(i: &Integer) -> BigInt {
    i.to_string().parse().unwrap()
}
