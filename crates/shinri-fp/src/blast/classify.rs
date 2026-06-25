//! Bit-blasted FP classification predicates over an Unpacked operand.

use shinri_bv::{BitLit, Blaster};
use crate::unpack::Unpacked;

pub fn is_nan(_b: &mut Blaster, u: &Unpacked) -> BitLit { u.is_nan }
pub fn is_inf(_b: &mut Blaster, u: &Unpacked) -> BitLit { u.is_inf }
pub fn is_zero(_b: &mut Blaster, u: &Unpacked) -> BitLit { u.is_zero }

/// exp is neither all-zero nor all-ones ⇒ normal. Equivalent to
/// NOT(is_nan OR is_inf OR is_zero OR is_subnormal); compute directly from flags.
pub fn is_normal(b: &mut Blaster, u: &Unpacked) -> BitLit {
    // normal = NOT exp_all_zero AND NOT exp_all_ones.
    // Reconstruct exp_all_ones / exp_all_zero from u.exp.
    let mut all_ones = b.one();
    for &e in &u.exp { all_ones = b.and2(all_ones, e); }
    let mut all_zero = b.one();
    for &e in &u.exp { let ne = b.not1(e); all_zero = b.and2(all_zero, ne); }
    let not_ones = b.not1(all_ones);
    let not_zero = b.not1(all_zero);
    b.and2(not_ones, not_zero)
}

/// subnormal = exp_all_zero AND sig != 0.
pub fn is_subnormal(b: &mut Blaster, u: &Unpacked) -> BitLit {
    let mut all_zero = b.one();
    for &e in &u.exp { let ne = b.not1(e); all_zero = b.and2(all_zero, ne); }
    let mut sig_all_zero = b.one();
    for &s in &u.sig { let ns = b.not1(s); sig_all_zero = b.and2(sig_all_zero, ns); }
    let sig_nonzero = b.not1(sig_all_zero);
    b.and2(all_zero, sig_nonzero)
}

/// isNegative: sign set AND NOT NaN. Signed zeros carry their sign (isNegative(-0)=true);
/// only NaN is excluded. Matches the Task-1 reference oracle and z3.
pub fn is_negative(b: &mut Blaster, u: &Unpacked) -> BitLit {
    let not_nan = b.not1(u.is_nan);
    b.and2(u.sign, not_nan)
}

/// isPositive: sign clear AND NOT NaN. isPositive(+0)=true; only NaN is excluded.
pub fn is_positive(b: &mut Blaster, u: &Unpacked) -> BitLit {
    let not_sign = b.not1(u.sign);
    let not_nan = b.not1(u.is_nan);
    b.and2(not_sign, not_nan)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{decode, ref_is_nan, ref_is_inf, ref_is_zero, ref_is_normal,
                           ref_is_subnormal, ref_is_negative, ref_is_positive};
    use crate::unpack::unpack;
    use shinri_num::Integer;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    /// Build constant bits (LSB→MSB) for `value` of width W=eb+sb in a Blaster.
    fn const_bits(b: &Blaster, eb: u32, sb: u32, value: u64) -> Vec<BitLit> {
        let w = eb + sb;
        (0..w).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    }

    /// Solve the Blaster's CNF and return the boolean value of `lit`.
    fn eval(b: Blaster, lit: BitLit) -> bool {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars { s.new_var(); }
        for clause in &cnf.clauses {
            let lits: Vec<Lit> = clause.iter().map(|bl| Lit::new(Var::new(bl.var), bl.pos)).collect();
            s.add_clause(&lits);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let raw = s.value_of(Var::new(lit.var)).unwrap();
        if lit.pos { raw } else { !raw }
    }

    fn check_all(eb: u32, sb: u32, value: u64) {
        let cls = decode(eb, sb, &Integer::from(value));
        // each predicate gets its own fresh Blaster (independent solve)
        macro_rules! one {
            ($gadget:path, $reference:expr) => {{
                let mut b = Blaster::new();
                let bits = const_bits(&b, eb, sb, value);
                let u = unpack(&mut b, &bits, eb, sb);
                let lit = $gadget(&mut b, &u);
                assert_eq!(eval(b, lit), $reference, "value={:#x} gadget={}", value, stringify!($gadget));
            }};
        }
        one!(is_nan, ref_is_nan(&cls));
        one!(is_inf, ref_is_inf(&cls));
        one!(is_zero, ref_is_zero(&cls));
        one!(is_normal, ref_is_normal(&cls));
        one!(is_subnormal, ref_is_subnormal(&cls));
        one!(is_negative, ref_is_negative(&cls));
        one!(is_positive, ref_is_positive(&cls));
    }

    #[test]
    fn classify_float32_representatives() {
        let (eb, sb) = (8, 24);
        for v in [0x0000_0000u64, 0x8000_0000, 0x7F80_0000, 0xFF80_0000, 0x7FC0_0000,
                  0x3F80_0000, 0xBF80_0000, 0x0000_0001, 0x8000_0001] {
            check_all(eb, sb, v);
        }
    }

    #[test]
    fn classify_tiny_format_exhaustive() {
        // (3,5): W=8 bits, all 256 patterns, against the reference.
        let (eb, sb) = (3, 5);
        for v in 0u64..256 { check_all(eb, sb, v); }
    }
}
