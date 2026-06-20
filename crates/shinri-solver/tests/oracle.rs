//! Differential oracle: shinri-solver vs z3 on random QF_UF.
//! Run with: `cargo test -p shinri-solver --features oracle -- --nocapture`
//! Requires a `z3` binary on PATH.
#![cfg(feature = "oracle")]

use shinri_core::{BuiltinOp, Op};
use shinri_solver::{SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0 >> 16
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

#[test]
fn differential_qf_uf_small() {
    let mut rng = Lcg(0x5eed);
    for _ in 0..200 {
        // Build a random conjunction of (in)equalities over 4 constants and f/1.
        let mut s = Solver::new();
        let u = s.declare_sort("U");
        let consts: Vec<_> = (0..4)
            .map(|i| {
                let sym = s.declare_fun(&format!("c{i}"), &[], u);
                s.app(Op::Uninterpreted(sym), &[])
            })
            .collect();
        let f = s.declare_fun("f", &[u], u);

        // SMT-LIB mirror via easy-smt (requires z3 on PATH at runtime).
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        let su = ctx.declare_sort("U", 0).unwrap();
        let mut z_consts = Vec::new();
        for i in 0..4 {
            z_consts.push(ctx.declare_const(format!("c{i}"), su).unwrap());
        }
        // declare_fun takes Vec<SExpr> for args in easy-smt 0.2
        let _zf = ctx.declare_fun("f", vec![su], su).unwrap();

        let n_lits = 2 + rng.below(4) as usize;
        let mut z_lits = Vec::new();
        for _ in 0..n_lits {
            let i = rng.below(4) as usize;
            let j = rng.below(4) as usize;
            let use_f = rng.below(2) == 1;
            let neg = rng.below(2) == 1;

            let (lhs, rhs, z_lhs, z_rhs) = if use_f {
                let fl = s.app(Op::Uninterpreted(f), &[consts[i]]);
                let fr = s.app(Op::Uninterpreted(f), &[consts[j]]);
                // build (f ci) and (f cj) as s-expressions
                let zf_atom = ctx.atom("f");
                let zl = ctx.list(vec![zf_atom, z_consts[i]]);
                let zr = ctx.list(vec![zf_atom, z_consts[j]]);
                (fl, fr, zl, zr)
            } else {
                (consts[i], consts[j], z_consts[i], z_consts[j])
            };

            let eqt = s.eq(lhs, rhs);
            let lit = if neg {
                s.app(Op::Builtin(BuiltinOp::Not), &[eqt])
            } else {
                eqt
            };
            s.assert(lit);

            let zeq = ctx.eq(z_lhs, z_rhs);
            z_lits.push(if neg { ctx.not(zeq) } else { zeq });
        }

        for zl in z_lits {
            ctx.assert(zl).unwrap();
        }

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();

        match (ours, theirs) {
            (SolveOutcome::Unknown, _) => {} // never a failure
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {}
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {}
            (o, t) => panic!("DISAGREEMENT: shinri={o:?} z3={t:?}"),
        }
    }
}
