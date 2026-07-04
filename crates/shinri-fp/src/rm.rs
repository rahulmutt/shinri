//! RoundingMode operand → 5-bit one-hot selector [Rne, Rna, Rtp, Rtn, Rtz].

use shinri_bv::{BitLit, Blaster};
use shinri_core::RoundingMode;

/// One-hot rounding-mode selector, order [Rne, Rna, Rtp, Rtn, Rtz].
pub struct RmSel {
    pub sel: [BitLit; 5],
}

/// Constant one-hot for a literal mode.
pub fn literal(b: &Blaster, rm: RoundingMode) -> RmSel {
    let o = b.one();
    let z = b.zero();
    let idx = match rm {
        RoundingMode::Rne => 0,
        RoundingMode::Rna => 1,
        RoundingMode::Rtp => 2,
        RoundingMode::Rtn => 3,
        RoundingMode::Rtz => 4,
    };
    let mut sel = [z; 5];
    sel[idx] = o;
    RmSel { sel }
}

/// Symbolic mode: 3 fresh bits (e2 e1 e0), codes 000..100 only.
/// Decode to one-hot; exclude illegal codes 101/110/111 with two clauses.
pub fn symbolic(b: &mut Blaster) -> RmSel {
    symbolic_bits(b).0
}

/// Like [`symbolic`] but also returns the three raw input bits `[e0, e1, e2]`
/// (LSB→MSB) so tests can pin the encoded code and exercise the exclusion
/// clauses directly. The public one-hot contract is identical to [`symbolic`].
fn symbolic_bits(b: &mut Blaster) -> (RmSel, [BitLit; 3]) {
    let e0 = b.fresh();
    let e1 = b.fresh();
    let e2 = b.fresh();
    let n0 = b.not1(e0);
    let n1 = b.not1(e1);
    let n2 = b.not1(e2);
    // exclude codes >= 5: NOT(e2 AND e0) AND NOT(e2 AND e1)
    b.add_clause(&[n2, n0]); // (¬e2 ∨ ¬e0)
    b.add_clause(&[n2, n1]); // (¬e2 ∨ ¬e1)
                             // one-hot decode of the 5 legal codes.
    let rne = {
        let t = b.and2(n2, n1);
        b.and2(t, n0)
    }; // 000
    let rna = {
        let t = b.and2(n2, n1);
        b.and2(t, e0)
    }; // 001
    let rtp = {
        let t = b.and2(n2, e1);
        b.and2(t, n0)
    }; // 010
    let rtn = {
        let t = b.and2(n2, e1);
        b.and2(t, e0)
    }; // 011
    let rtz = {
        let t = b.and2(e2, n1);
        b.and2(t, n0)
    }; // 100
    (
        RmSel {
            sel: [rne, rna, rtp, rtn, rtz],
        },
        [e0, e1, e2],
    )
}

/// Equality of two RoundingMode selectors. ONE-HOT PRECONDITION: both inputs
/// must come from `literal`/`symbolic` (exactly one bit set); under that
/// invariant the selected indices match iff some position has both bits set.
/// Wrong for general (non-one-hot) words — do not reuse outside RM.
pub fn eq(b: &mut Blaster, x: &RmSel, y: &RmSel) -> BitLit {
    let mut acc = b.zero();
    for i in 0..5 {
        let both = b.and2(x.sel[i], y.sel[i]);
        acc = b.or2(acc, both);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn eval_sel(b: Blaster, sel: &[BitLit; 5]) -> [bool; 5] {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars {
            s.new_var();
        }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c
                .iter()
                .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                .collect();
            s.add_clause(&ls);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let mut out = [false; 5];
        for (i, bl) in sel.iter().enumerate() {
            let raw = s.value_of(Var::new(bl.var)).unwrap();
            out[i] = if bl.pos { raw } else { !raw };
        }
        out
    }

    #[test]
    fn literal_is_one_hot() {
        for (rm, idx) in [
            (RoundingMode::Rne, 0),
            (RoundingMode::Rna, 1),
            (RoundingMode::Rtp, 2),
            (RoundingMode::Rtn, 3),
            (RoundingMode::Rtz, 4),
        ] {
            let b = Blaster::new();
            let s = literal(&b, rm);
            let got = eval_sel(b, &s.sel);
            for (i, &g) in got.iter().enumerate() {
                assert_eq!(g, i == idx, "rm={rm:?} bit {i}");
            }
        }
    }

    /// Build a solver from `b`'s CNF plus `extra` pinning clauses, then solve.
    fn solve_with(b: Blaster, extra: &[Vec<BitLit>]) -> SolveResult {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars {
            s.new_var();
        }
        for c in cnf.clauses.iter().chain(extra.iter()) {
            let ls: Vec<Lit> = c
                .iter()
                .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                .collect();
            s.add_clause(&ls);
        }
        s.solve()
    }

    /// Unit clause pinning bit `bl` to `val`.
    fn pin(bl: BitLit, val: bool) -> Vec<BitLit> {
        // `bl` is a fresh literal (pos == true), so pinning its var to `val`
        // is simply the unit literal with polarity `val`.
        vec![BitLit {
            var: bl.var,
            pos: val,
        }]
    }

    /// SAT-check `b`'s accumulated clauses with no extra pinning.
    fn solve_ok(b: Blaster) -> bool {
        matches!(solve_with(b, &[]), SolveResult::Sat)
    }

    #[test]
    fn symbolic_is_exactly_one_hot_and_excludes_illegal() {
        // 1) The default (unpinned) symbolic RM yields a one-hot assignment.
        let mut b = Blaster::new();
        let s = symbolic(&mut b);
        let got = eval_sel(b, &s.sel);
        assert_eq!(
            got.iter().filter(|x| **x).count(),
            1,
            "symbolic RM must be one-hot"
        );

        // 2) Each legal code 0..=4 is SAT and decodes to *exactly* its own
        //    selector. We pin (e2,e1,e0) to the code, then require sel[code]=true
        //    and every other sel[j]=false; SAT proves the decode is correct.
        for code in 0u8..=4 {
            let mut b = Blaster::new();
            let (s, bits) = symbolic_bits(&mut b);
            let mut extra: Vec<Vec<BitLit>> = Vec::new();
            for (k, &bit) in bits.iter().take(3).enumerate() {
                extra.push(pin(bit, (code >> k) & 1 == 1));
            }
            for j in 0..5 {
                extra.push(pin(s.sel[j], j == code as usize));
            }
            assert_eq!(
                solve_with(b, &extra),
                SolveResult::Sat,
                "legal code {code} must decode to selector {code}"
            );
        }

        // 3) The exclusion clauses must make every illegal code 5/6/7 UNSAT.
        //    This is the falsifiable coverage of the two `add_clause` lines:
        //    removing either exclusion clause makes one of these SAT.
        for code in [5u8, 6, 7] {
            let mut b = Blaster::new();
            let (_s, bits) = symbolic_bits(&mut b);
            let extra: Vec<Vec<BitLit>> =
                (0..3).map(|k| pin(bits[k], (code >> k) & 1 == 1)).collect();
            assert!(
                matches!(solve_with(b, &extra), SolveResult::Unsat { .. }),
                "illegal code {code} must be excluded (UNSAT)"
            );
        }

        // 4) Genuine mutual exclusivity: forcing two selectors true is UNSAT.
        let mut b = Blaster::new();
        let s = symbolic(&mut b);
        let extra = vec![pin(s.sel[0], true), pin(s.sel[1], true)];
        assert!(
            matches!(solve_with(b, &extra), SolveResult::Unsat { .. }),
            "two selectors cannot be simultaneously true"
        );
    }

    #[test]
    fn rm_eq_literal_pairs_exhaustive() {
        use shinri_core::RoundingMode::*;
        // 5×5 literal pairs: the reified eq bit must be constant-true iff modes match.
        for &m1 in &[Rne, Rna, Rtp, Rtn, Rtz] {
            for &m2 in &[Rne, Rna, Rtp, Rtn, Rtz] {
                let mut b = Blaster::new();
                let x = literal(&b, m1);
                let y = literal(&b, m2);
                let e = eq(&mut b, &x, &y);
                // Force e true and solve: SAT iff m1 == m2.
                b.add_clause(&[e]);
                let expect_sat = m1 == m2;
                assert_eq!(solve_ok(b), expect_sat, "rm_eq({m1:?},{m2:?})");
            }
        }
    }

    #[test]
    fn rm_eq_symbolic_vs_literal_forces_mode() {
        use shinri_core::RoundingMode::*;
        // (= r RTZ) with symbolic r: SAT, and asserting also (= r RNE) is UNSAT.
        let mut b = Blaster::new();
        let r = symbolic(&mut b);
        let rtz = literal(&b, Rtz);
        let rne = literal(&b, Rne);
        let e1 = eq(&mut b, &r, &rtz);
        let e2 = eq(&mut b, &r, &rne);
        b.add_clause(&[e1]);
        b.add_clause(&[e2]);
        assert!(!solve_ok(b), "r cannot equal two distinct modes");
    }
}
