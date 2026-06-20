//! Differential oracle: shinri-solver vs z3 on random QF_UF and QF_LRA.
//! Run with: `cargo test -p shinri-solver --features oracle -- --nocapture`
//! Requires a `z3` binary on PATH.
#![cfg(feature = "oracle")]

use shinri_core::{BuiltinOp, Op};
use shinri_num::Rational;
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

/// Build a z3 (easy-smt) s-expression for an integer coefficient * variable.
/// Handles zero (returns None), positive and negative coefficients.
fn z_coeff_times_var(
    ctx: &easy_smt::Context,
    coeff: i32,
    var: easy_smt::SExpr,
) -> Option<easy_smt::SExpr> {
    if coeff == 0 {
        return None;
    }
    if coeff == 1 {
        return Some(var);
    }
    if coeff == -1 {
        return Some(ctx.negate(var));
    }
    let abs_val = coeff.unsigned_abs() as i32;
    let z_coeff = ctx.numeral(abs_val);
    let product = ctx.times(z_coeff, var);
    if coeff < 0 {
        Some(ctx.negate(product))
    } else {
        Some(product)
    }
}

/// Build a z3 integer numeral, supporting negative values.
fn z_int(ctx: &easy_smt::Context, n: i32) -> easy_smt::SExpr {
    if n >= 0 {
        ctx.numeral(n)
    } else {
        ctx.negate(ctx.numeral(-n))
    }
}

/// Relation kind for the random LRA generator.
#[derive(Debug, Clone, Copy)]
enum Rel {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
    Ne,
}

#[test]
fn differential_qf_lra_small() {
    // Reuse the same Lcg (different seed to keep corpora independent).
    let mut rng = Lcg(0x1_4a4b);

    const N_VARS: usize = 3;
    const N_ITERS: usize = 300;
    let mut unknowns = 0usize;

    for iter in 0..N_ITERS {
        // ── shinri setup ────────────────────────────────────────────────────
        let mut s = Solver::new();
        let real = s.real_sort();
        let vars: Vec<shinri_core::TermId> = (0..N_VARS)
            .map(|i| s.declare_const(&format!("x{i}"), real))
            .collect();

        // ── z3 setup (easy-smt) ─────────────────────────────────────────────
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        ctx.set_logic("QF_LRA").unwrap();
        let z_real = ctx.atom("Real");
        let z_vars: Vec<easy_smt::SExpr> = (0..N_VARS)
            .map(|i| ctx.declare_const(format!("x{i}"), z_real).unwrap())
            .collect();

        // Number of constraints for this iteration.
        let n_constraints = 4 + rng.below(4) as usize; // 4..=7

        let mut dump = format!("iter={iter} seed after setup: ");

        for c in 0..n_constraints {
            // Pick relation.
            let rel = match rng.below(6) {
                0 => Rel::Le,
                1 => Rel::Lt,
                2 => Rel::Ge,
                3 => Rel::Gt,
                4 => Rel::Eq,
                _ => Rel::Ne,
            };

            // Generate coefficients for each variable in -2..=2.
            // If all are zero, force x0 to have coeff=1.
            let mut coeffs: Vec<i32> = (0..N_VARS).map(|_| (rng.below(5) as i32) - 2).collect();
            if coeffs.iter().all(|&c| c == 0) {
                coeffs[0] = 1;
            }

            // RHS in -3..=3.
            let rhs_val: i32 = (rng.below(7) as i32) - 3;

            // ── shinri: build lhs = Σ coeff_i * x_i ────────────────────────
            let mut shinri_terms: Vec<shinri_core::TermId> = Vec::new();
            for (i, &coeff) in coeffs.iter().enumerate() {
                if coeff == 0 {
                    continue;
                }
                let c_term = s.numeral(Rational::from_int((coeff as i128).into()), real);
                let product = s.app(Op::Builtin(BuiltinOp::Mul), &[c_term, vars[i]]);
                shinri_terms.push(product);
            }
            let s_lhs = if shinri_terms.len() == 1 {
                shinri_terms[0]
            } else {
                // fold left: Add(Add(...), term)
                shinri_terms
                    .into_iter()
                    .reduce(|acc, t| s.app(Op::Builtin(BuiltinOp::Add), &[acc, t]))
                    .unwrap()
            };
            let s_rhs = s.numeral(Rational::from_int((rhs_val as i128).into()), real);

            // ── z3: build lhs = Σ coeff_i * x_i ────────────────────────────
            let z_terms: Vec<easy_smt::SExpr> = coeffs
                .iter()
                .enumerate()
                .filter_map(|(i, &coeff)| z_coeff_times_var(&ctx, coeff, z_vars[i]))
                .collect();
            let z_lhs = if z_terms.len() == 1 {
                z_terms[0]
            } else {
                z_terms
                    .into_iter()
                    .reduce(|acc, t| ctx.plus(acc, t))
                    .unwrap()
            };
            let z_rhs = z_int(&ctx, rhs_val);

            // Dump for debugging disagreements.
            let coeff_str: Vec<String> = coeffs.iter().map(|c| c.to_string()).collect();
            dump.push_str(&format!("\n  [{c}] {coeff_str:?}·x {rel:?} {rhs_val}"));

            // ── shinri: assert constraint ────────────────────────────────────
            let s_atom = match rel {
                Rel::Le => s.app(Op::Builtin(BuiltinOp::Le), &[s_lhs, s_rhs]),
                Rel::Lt => s.app(Op::Builtin(BuiltinOp::Lt), &[s_lhs, s_rhs]),
                Rel::Ge => s.app(Op::Builtin(BuiltinOp::Ge), &[s_lhs, s_rhs]),
                Rel::Gt => s.app(Op::Builtin(BuiltinOp::Gt), &[s_lhs, s_rhs]),
                Rel::Eq => s.eq(s_lhs, s_rhs),
                Rel::Ne => {
                    let eq = s.eq(s_lhs, s_rhs);
                    s.app(Op::Builtin(BuiltinOp::Not), &[eq])
                }
            };
            s.assert(s_atom);

            // ── z3: assert constraint ────────────────────────────────────────
            let z_atom = match rel {
                Rel::Le => ctx.lte(z_lhs, z_rhs),
                Rel::Lt => ctx.lt(z_lhs, z_rhs),
                Rel::Ge => ctx.gte(z_lhs, z_rhs),
                Rel::Gt => ctx.gt(z_lhs, z_rhs),
                Rel::Eq => ctx.eq(z_lhs, z_rhs),
                Rel::Ne => {
                    let eq = ctx.eq(z_lhs, z_rhs);
                    ctx.not(eq)
                }
            };
            ctx.assert(z_atom).unwrap();
        }

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();

        match (ours, theirs) {
            (SolveOutcome::Unknown, _) => {
                unknowns += 1;
            }
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {}
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {}
            (o, t) => {
                panic!("SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{dump}");
            }
        }
    }

    println!(
        "differential_qf_lra_small: {N_ITERS} systems checked, {unknowns} Unknowns (should be 0)"
    );
    assert_eq!(
        unknowns, 0,
        "Got {unknowns} Unknown results in pure QF_LRA — \
         this indicates a bug (mixed-theory fence firing spuriously)"
    );
}
