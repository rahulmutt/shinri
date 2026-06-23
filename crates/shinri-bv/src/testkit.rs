//! Test helpers shared across all blast/* test modules.
//! Only compiled under `#[cfg(test)]`.

use crate::blast::{BitLit, Blaster, Cnf};
use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

/// Allocate `width` fresh bits in `b` and add unit clauses pinning each bit i
/// to bit i of `val` (LSB→MSB order).
pub(crate) fn pin_const(b: &mut Blaster, val: u64, width: u32) -> Vec<BitLit> {
    (0..width)
        .map(|i| {
            let bit = b.fresh();
            let bit_is_one = ((val >> i) & 1) == 1;
            let lit = if bit_is_one { bit } else { bit.negate() };
            b.add_clause(&[lit]);
            bit
        })
        .collect()
}

fn build_solver(cnf: &Cnf) -> Solver<NoTheory, NoProof, Vmtf> {
    let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
    for _ in 0..cnf.num_vars {
        s.new_var();
    }
    for clause in &cnf.clauses {
        let sat_lits: Vec<Lit> = clause
            .iter()
            .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
            .collect();
        s.add_clause(&sat_lits);
    }
    s
}

fn pack_bits(s: &Solver<NoTheory, NoProof, Vmtf>, bits: &[BitLit]) -> u64 {
    let mut out: u64 = 0;
    for (i, bl) in bits.iter().enumerate() {
        let raw = s
            .value_of(Var::new(bl.var))
            .expect("output var unassigned in model");
        let bit_val = if bl.pos { raw } else { !raw };
        if bit_val {
            out |= 1u64 << i;
        }
    }
    out
}

/// Finish the blaster into a CNF, build a `shinri_sat::Solver`, solve (expect SAT),
/// and pack the output bits LSB→MSB into a u64.
///
/// Polarity: `bit.pos == true` means "the output value equals the model value of `bit.var`".
/// `bit.pos == false` means the output value is the complement.
pub(crate) fn solve_value(b: Blaster, bits: &[BitLit]) -> u64 {
    let cnf = b.finish();
    let mut s = build_solver(&cnf);
    let result = s.solve();
    assert_eq!(result, SolveResult::Sat, "expected SAT but got UNSAT");
    pack_bits(&s, bits)
}

/// Like `solve_value` but reads TWO output slices from a single solve call.
/// Returns `(value_of_a, value_of_c)`.
pub(crate) fn solve_value_pair(b: Blaster, a: &[BitLit], c: &[BitLit]) -> (u64, u64) {
    let cnf = b.finish();
    let mut s = build_solver(&cnf);
    let result = s.solve();
    assert_eq!(result, SolveResult::Sat, "expected SAT but got UNSAT");
    (pack_bits(&s, a), pack_bits(&s, c))
}
