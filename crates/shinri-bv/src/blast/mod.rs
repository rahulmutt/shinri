use rustc_hash::FxHashMap;
use shinri_core::TermId;

pub mod structural;
pub mod bitwise;
pub mod arith;
pub mod div;
pub mod shift;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BitLit {
    pub var: u32,
    pub pos: bool,
}

impl BitLit {
    pub fn negate(self) -> BitLit {
        BitLit { var: self.var, pos: !self.pos }
    }
}

#[derive(Default)]
pub struct Cnf {
    pub num_vars: u32,
    pub clauses: Vec<Vec<BitLit>>,
}

pub struct Blaster {
    next_var: u32,
    clauses: Vec<Vec<BitLit>>,
    /// Memoized blasted words: TermId -> LSB..MSB bit literals.
    pub(crate) cache: FxHashMap<TermId, Vec<BitLit>>,
}

impl Blaster {
    pub fn new() -> Blaster {
        // var 0 is the pinned-true constant.
        let mut b = Blaster {
            next_var: 1,
            clauses: Vec::new(),
            cache: FxHashMap::default(),
        };
        let t = BitLit { var: 0, pos: true };
        b.add_clause(&[t]); // force var0 = true
        b
    }

    pub fn one(&self) -> BitLit {
        BitLit { var: 0, pos: true }
    }

    pub fn zero(&self) -> BitLit {
        BitLit { var: 0, pos: false }
    }

    pub fn fresh(&mut self) -> BitLit {
        let v = self.next_var;
        self.next_var += 1;
        BitLit { var: v, pos: true }
    }

    pub fn add_clause(&mut self, lits: &[BitLit]) {
        self.clauses.push(lits.to_vec());
    }

    pub fn finish(self) -> Cnf {
        Cnf { num_vars: self.next_var, clauses: self.clauses }
    }

    pub fn not1(&self, a: BitLit) -> BitLit {
        a.negate()
    }

    pub fn and2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // o <-> (a AND b):
        //   o -> a          : (NOT o OR a)
        //   o -> b          : (NOT o OR b)
        //   (a AND b) -> o  : (NOT a OR NOT b OR o)
        self.add_clause(&[o.negate(), a]);
        self.add_clause(&[o.negate(), b]);
        self.add_clause(&[o, a.negate(), b.negate()]);
        o
    }

    pub fn or2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // o <-> (a OR b):
        //   (NOT a) -> NOT o  : (o OR NOT a)
        //   (NOT b) -> NOT o  : (o OR NOT b)
        //   NOT o -> (NOT a AND NOT b) : (NOT o OR a OR b)
        self.add_clause(&[o, a.negate()]);
        self.add_clause(&[o, b.negate()]);
        self.add_clause(&[o.negate(), a, b]);
        o
    }

    pub fn xor2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // o <-> (a XOR b):
        //   o -> (a OR b)           : (NOT o OR a OR b)
        //   o -> NOT(a AND b)       : (NOT o OR NOT a OR NOT b)
        //   NOT o -> (a <-> b):
        //     (NOT a AND NOT b) -> NOT o : (o OR NOT a OR b) — wait, check carefully
        //   NOT o -> (a XNOR b):
        //     NOT o AND a -> b      : (o OR NOT a OR b)
        //     NOT o AND NOT a -> NOT b : (o OR a OR NOT b)
        self.add_clause(&[o.negate(), a, b]);
        self.add_clause(&[o.negate(), a.negate(), b.negate()]);
        self.add_clause(&[o, a.negate(), b]);
        self.add_clause(&[o, a, b.negate()]);
        o
    }

    /// sel ? a : b
    pub fn mux2(&mut self, sel: BitLit, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // sel -> (o <-> a):
        //   NOT sel OR NOT o OR a
        //   NOT sel OR o OR NOT a
        // NOT sel -> (o <-> b):
        //   sel OR NOT o OR b
        //   sel OR o OR NOT b
        self.add_clause(&[sel.negate(), o.negate(), a]);
        self.add_clause(&[sel.negate(), o, a.negate()]);
        self.add_clause(&[sel, o.negate(), b]);
        self.add_clause(&[sel, o, b.negate()]);
        o
    }

    pub fn full_adder(&mut self, a: BitLit, b: BitLit, cin: BitLit) -> (BitLit, BitLit) {
        let axb = self.xor2(a, b);
        let sum = self.xor2(axb, cin);
        let t1 = self.and2(a, b);
        let t2 = self.and2(axb, cin);
        let cout = self.or2(t1, t2);
        (sum, cout)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_sat::{Lit, NoProof, NoTheory, Solver, SolveResult, SolverConfig, Var, Vmtf};

    /// Build a shinri_sat::Solver from a finished Cnf, with `num_vars` pre-allocated.
    fn cnf_to_solver(cnf: &Cnf) -> Solver<NoTheory, NoProof, Vmtf> {
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

    /// Pin a BitLit to a concrete Boolean value by adding a unit assumption clause,
    /// then read the model value of another BitLit after solving.
    fn solve_with_inputs_and_read(
        blaster: Blaster,
        inputs: &[(BitLit, bool)],
        outputs: &[BitLit],
    ) -> Vec<bool> {
        let mut cnf = blaster.finish();
        // Force each input to its assigned value via unit clauses.
        for &(bl, val) in inputs {
            let lit = if val { bl } else { bl.negate() };
            cnf.clauses.push(vec![lit]);
        }
        let mut s = cnf_to_solver(&cnf);
        let result = s.solve();
        assert_eq!(result, SolveResult::Sat, "expected SAT for gate truth-table input");
        outputs
            .iter()
            .map(|bl| s.value_of(Var::new(bl.var)).expect("output var unassigned"))
            // BitLit stores the var index; the actual model value accounts for polarity:
            // a positive BitLit means "the output is this var"; if the var is true, output is true.
            // But `value_of` returns the raw var truth — if pos=true, value IS the bit.
            // If pos=false (negate), the bit is the opposite.
            .zip(outputs.iter())
            .map(|(v, bl)| if bl.pos { v } else { !v })
            .collect()
    }

    #[test]
    fn const_bits_and_fresh_allocate_distinct_vars() {
        let mut b = Blaster::new();
        assert_eq!(b.one().var, 0);
        assert!(b.one().pos);
        assert_eq!(b.zero().var, 0);
        assert!(!b.zero().pos);
        let x = b.fresh();
        let y = b.fresh();
        assert_ne!(x.var, y.var);
        assert!(x.var >= 1 && y.var >= 1);
    }

    #[test]
    fn full_adder_truth_table_structural() {
        // Structural check: full_adder returns two distinct signal lits.
        let mut b = Blaster::new();
        let a = b.fresh();
        let bb = b.fresh();
        let c = b.fresh();
        let (s, co) = b.full_adder(a, bb, c);
        assert_ne!(s.var, co.var);
    }

    /// Helper: build a fresh Blaster, pin 3 input vars, call full_adder,
    /// solve and return (sum_bit, cout_bit).
    fn check_full_adder(av: bool, bv: bool, cinv: bool) -> (bool, bool) {
        let mut bl = Blaster::new();
        let a = bl.fresh();
        let b = bl.fresh();
        let cin = bl.fresh();
        let (sum, cout) = bl.full_adder(a, b, cin);
        let results = solve_with_inputs_and_read(bl, &[(a, av), (b, bv), (cin, cinv)], &[sum, cout]);
        (results[0], results[1])
    }

    #[test]
    fn full_adder_solve_all_8_combinations() {
        for av in [false, true] {
            for bv in [false, true] {
                for cinv in [false, true] {
                    let total = (av as u32) + (bv as u32) + (cinv as u32);
                    let expected_sum = (total & 1) == 1;
                    let expected_cout = total >= 2;
                    let (got_sum, got_cout) = check_full_adder(av, bv, cinv);
                    assert_eq!(
                        got_sum, expected_sum,
                        "full_adder sum wrong for a={av} b={bv} cin={cinv}: expected {expected_sum} got {got_sum}"
                    );
                    assert_eq!(
                        got_cout, expected_cout,
                        "full_adder cout wrong for a={av} b={bv} cin={cinv}: expected {expected_cout} got {got_cout}"
                    );
                }
            }
        }
    }

    #[test]
    fn and2_solve_verify() {
        for (av, bv) in [(false, false), (false, true), (true, false), (true, true)] {
            let mut bl = Blaster::new();
            let a = bl.fresh();
            let b = bl.fresh();
            let o = bl.and2(a, b);
            let results = solve_with_inputs_and_read(bl, &[(a, av), (b, bv)], &[o]);
            let expected = av && bv;
            assert_eq!(
                results[0], expected,
                "and2 wrong for a={av} b={bv}: expected {expected} got {}",
                results[0]
            );
        }
    }

    #[test]
    fn or2_solve_verify() {
        for (av, bv) in [(false, false), (false, true), (true, false), (true, true)] {
            let mut bl = Blaster::new();
            let a = bl.fresh();
            let b = bl.fresh();
            let o = bl.or2(a, b);
            let results = solve_with_inputs_and_read(bl, &[(a, av), (b, bv)], &[o]);
            let expected = av || bv;
            assert_eq!(
                results[0], expected,
                "or2 wrong for a={av} b={bv}: expected {expected} got {}",
                results[0]
            );
        }
    }

    #[test]
    fn xor2_solve_verify() {
        for (av, bv) in [(false, false), (false, true), (true, false), (true, true)] {
            let mut bl = Blaster::new();
            let a = bl.fresh();
            let b = bl.fresh();
            let o = bl.xor2(a, b);
            let results = solve_with_inputs_and_read(bl, &[(a, av), (b, bv)], &[o]);
            let expected = av ^ bv;
            assert_eq!(
                results[0], expected,
                "xor2 wrong for a={av} b={bv}: expected {expected} got {}",
                results[0]
            );
        }
    }

    #[test]
    fn mux2_solve_verify() {
        // Check sel=false picks b, sel=true picks a for a few combos.
        for (selv, av, bv) in [
            (false, false, false),
            (false, false, true),
            (false, true, false),
            (false, true, true),
            (true, false, false),
            (true, false, true),
            (true, true, false),
            (true, true, true),
        ] {
            let mut bl = Blaster::new();
            let sel = bl.fresh();
            let a = bl.fresh();
            let b = bl.fresh();
            let o = bl.mux2(sel, a, b);
            let results = solve_with_inputs_and_read(bl, &[(sel, selv), (a, av), (b, bv)], &[o]);
            // mux2(sel, a, b) = sel ? a : b
            let expected = if selv { av } else { bv };
            assert_eq!(
                results[0], expected,
                "mux2 wrong for sel={selv} a={av} b={bv}: expected {expected} got {}",
                results[0]
            );
        }
    }
}
