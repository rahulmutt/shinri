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

// ────────────────────────────────────────────────────────────────────────────
// QF_UFLRA differential oracle — validates the Nelson-Oppen combination.
//
// Generates random instances over a few Real vars, two UFs f,g : Real -> Real,
// random linear arithmetic atoms, and (dis)equalities over both vars and
// function applications. The generator deliberately steers a large fraction of
// instances into the two interesting N-O directions:
//
//   • arith → EUF (bounds-pinned ⇒ congruence): pin a var x to a constant c via
//     x >= c ∧ x <= c, then constrain (f x) vs (f c). LRA entails x = c, which
//     must reach EUF congruence so (f x) ≡ (f c).
//   • EUF → arith (congruence-derived ⇒ arith): assert (= a b) (or congruent
//     f-apps) then feed (f a),(f b) into a linear atom like
//     (>= (- (f a) (f b)) 1). EUF entails (f a) = (f b), which must reach arith.
//
// Every instance is built identically for our Solver and for z3 (easy-smt). On
// any sat/unsat disagreement we PANIC with the full instance dumped. Our Unknown
// is never a disagreement (but for pure QF_UFLRA the fence is gone, so we also
// count Unknowns and report them).
// ────────────────────────────────────────────────────────────────────────────

/// A single random term, built in lock-step for shinri and z3.
struct PairTerm {
    s: shinri_core::TermId,
    z: easy_smt::SExpr,
}

#[test]
fn differential_qf_uflra() {
    let mut rng = Lcg(0x12_34_56_78);

    const N_VARS: usize = 4;
    const N_ITERS: usize = 320;

    let mut unknowns = 0usize;
    // Disagreements panic immediately (with the full instance dumped) — reaching
    // the end of the loop therefore means zero disagreements occurred.
    // Stats: how often each interesting shape was emitted, and how many
    // instances actually came back UNSAT through each N-O direction's witness.
    let mut n_pin_congruence = 0usize; // arith→EUF shape generated
    let mut n_cong_arith = 0usize; // EUF→arith shape generated
    let mut n_nested = 0usize; // nested f(g(x)) generated
    let mut n_sat = 0usize;
    let mut n_unsat = 0usize;

    for iter in 0..N_ITERS {
        // ── shinri setup ────────────────────────────────────────────────────
        let mut s = Solver::new();
        let real = s.real_sort();
        let vars: Vec<shinri_core::TermId> = (0..N_VARS)
            .map(|i| s.declare_const(&format!("x{i}"), real))
            .collect();
        let f = s.declare_fun("f", &[real], real);
        let g = s.declare_fun("g", &[real], real);

        // ── z3 setup (easy-smt) ─────────────────────────────────────────────
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        ctx.set_logic("QF_UFLRA").unwrap();
        let z_real = ctx.atom("Real");
        let z_vars: Vec<easy_smt::SExpr> = (0..N_VARS)
            .map(|i| ctx.declare_const(format!("x{i}"), z_real).unwrap())
            .collect();
        let _zf = ctx.declare_fun("f", vec![z_real], z_real).unwrap();
        let _zg = ctx.declare_fun("g", vec![z_real], z_real).unwrap();

        let mut dump = format!("iter={iter}\n(set-logic QF_UFLRA)");
        for i in 0..N_VARS {
            dump.push_str(&format!("\n(declare-const x{i} Real)"));
        }
        dump.push_str("\n(declare-fun f (Real) Real)\n(declare-fun g (Real) Real)");

        // Helpers to build f/g applications in lock-step.
        let mk_f = |s: &mut Solver, ctx: &easy_smt::Context, t: &PairTerm| PairTerm {
            s: s.app(Op::Uninterpreted(f), &[t.s]),
            z: ctx.list(vec![ctx.atom("f"), t.z]),
        };
        let mk_g = |s: &mut Solver, ctx: &easy_smt::Context, t: &PairTerm| PairTerm {
            s: s.app(Op::Uninterpreted(g), &[t.s]),
            z: ctx.list(vec![ctx.atom("g"), t.z]),
        };

        // Var terms as PairTerms.
        let var_terms: Vec<PairTerm> = (0..N_VARS)
            .map(|i| PairTerm {
                s: vars[i],
                z: z_vars[i],
            })
            .collect();

        // Build a small pool of "atomic-ish" Real terms to combine: the vars,
        // plus a handful of function applications (f(xi), g(xi), and the
        // occasional nested f(g(xi))).
        let mut pool: Vec<PairTerm> = Vec::new();
        for vt in &var_terms {
            pool.push(PairTerm { s: vt.s, z: vt.z });
        }
        // f(x0), f(x1), g(x0), g(x2) as a stable base of app terms.
        let app_specs: [(bool, usize); 4] = [(true, 0), (true, 1), (false, 0), (false, 2)];
        for &(is_f, vi) in app_specs.iter() {
            let base = PairTerm {
                s: var_terms[vi].s,
                z: var_terms[vi].z,
            };
            let app = if is_f {
                mk_f(&mut s, &ctx, &base)
            } else {
                mk_g(&mut s, &ctx, &base)
            };
            pool.push(app);
        }
        // Occasionally a nested term f(g(x1)) — exercises deeper congruence.
        if rng.below(3) == 0 {
            let base = PairTerm {
                s: var_terms[1].s,
                z: var_terms[1].z,
            };
            let inner = mk_g(&mut s, &ctx, &base);
            let nested = mk_f(&mut s, &ctx, &inner);
            pool.push(nested);
            n_nested += 1;
        }

        // Assert a constraint into both engines, recording it in the dump.
        let assert_both = |s: &mut Solver,
                           ctx: &mut easy_smt::Context,
                           dump: &mut String,
                           s_atom: shinri_core::TermId,
                           z_atom: easy_smt::SExpr,
                           text: &str| {
            s.assert(s_atom);
            ctx.assert(z_atom).unwrap();
            dump.push_str("\n(assert ");
            dump.push_str(text);
            dump.push(')');
        };

        // ── Direction 1: arith→EUF (bounds-pinned ⇒ congruence). ────────────
        // With some probability, pin a var xk to a constant c and relate
        // (f xk) to (f c) via eq/distinct. z3 sees the same constant numeral.
        if rng.below(2) == 0 {
            n_pin_congruence += 1;
            let k = rng.below(N_VARS as u64) as usize;
            let c: i32 = (rng.below(7) as i32) - 3; // -3..=3
                                                    // xk >= c  and  xk <= c
            let sc = s.numeral(Rational::from_int((c as i128).into()), real);
            let zc = z_int(&ctx, c);
            let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[vars[k], sc]);
            let le = s.app(Op::Builtin(BuiltinOp::Le), &[vars[k], sc]);
            let zge = ctx.gte(z_vars[k], zc);
            let zle = ctx.lte(z_vars[k], zc);
            assert_both(
                &mut s,
                &mut ctx,
                &mut dump,
                ge,
                zge,
                &format!("(>= x{k} {c})"),
            );
            assert_both(
                &mut s,
                &mut ctx,
                &mut dump,
                le,
                zle,
                &format!("(<= x{k} {c})"),
            );

            // (f xk) vs (f c): the constant c gets its own numeral term so the
            // numeral-pinning path is exercised.
            let xk = PairTerm {
                s: vars[k],
                z: z_vars[k],
            };
            let cterm = PairTerm { s: sc, z: zc };
            let f_xk = mk_f(&mut s, &ctx, &xk);
            let f_c = mk_f(&mut s, &ctx, &cterm);
            // Randomly equate or distinguish. distinct ⇒ should be UNSAT (the
            // discriminating witness shape); eq ⇒ trivially consistent.
            if rng.below(2) == 0 {
                let d = {
                    let e = s.eq(f_xk.s, f_c.s);
                    s.app(Op::Builtin(BuiltinOp::Not), &[e])
                };
                let zd = ctx.not(ctx.eq(f_xk.z, f_c.z));
                assert_both(
                    &mut s,
                    &mut ctx,
                    &mut dump,
                    d,
                    zd,
                    &format!("(not (= (f x{k}) (f {c})))"),
                );
            } else {
                let e = s.eq(f_xk.s, f_c.s);
                let ze = ctx.eq(f_xk.z, f_c.z);
                assert_both(
                    &mut s,
                    &mut ctx,
                    &mut dump,
                    e,
                    ze,
                    &format!("(= (f x{k}) (f {c}))"),
                );
            }
        }

        // ── Direction 2: EUF→arith (congruence-derived ⇒ arith). ────────────
        // With some probability, assert (= a b) over two vars, then put
        // (f a),(f b) (which become congruent) into a linear atom.
        if rng.below(2) == 0 {
            n_cong_arith += 1;
            let a = rng.below(N_VARS as u64) as usize;
            let mut b = rng.below(N_VARS as u64) as usize;
            if b == a {
                b = (b + 1) % N_VARS;
            }
            let use_g = rng.below(2) == 0;
            // (= xa xb)
            let eq = s.eq(vars[a], vars[b]);
            let zeq = ctx.eq(z_vars[a], z_vars[b]);
            assert_both(
                &mut s,
                &mut ctx,
                &mut dump,
                eq,
                zeq,
                &format!("(= x{a} x{b})"),
            );

            let ta = PairTerm {
                s: vars[a],
                z: z_vars[a],
            };
            let tb = PairTerm {
                s: vars[b],
                z: z_vars[b],
            };
            let (fa, fb, fname) = if use_g {
                (mk_g(&mut s, &ctx, &ta), mk_g(&mut s, &ctx, &tb), "g")
            } else {
                (mk_f(&mut s, &ctx, &ta), mk_f(&mut s, &ctx, &tb), "f")
            };
            // (>= (- (f a) (f b)) rhs): EUF entails (f a)=(f b) ⇒ LHS=0, so
            // rhs>=1 ⇒ UNSAT, rhs<=0 ⇒ SAT.
            let rhs: i32 = (rng.below(3) as i32) - 1; // -1..=1
            let s_sub = s.app(Op::Builtin(BuiltinOp::Sub), &[fa.s, fb.s]);
            let s_rhs = s.numeral(Rational::from_int((rhs as i128).into()), real);
            let s_atom = s.app(Op::Builtin(BuiltinOp::Ge), &[s_sub, s_rhs]);
            let z_sub = ctx.sub(fa.z, fb.z);
            let z_atom = ctx.gte(z_sub, z_int(&ctx, rhs));
            assert_both(
                &mut s,
                &mut ctx,
                &mut dump,
                s_atom,
                z_atom,
                &format!("(>= (- ({fname} x{a}) ({fname} x{b})) {rhs})"),
            );
        }

        // ── General random atoms over the pool (linear LRA + (dis)equalities) ─
        let n_atoms = 3 + rng.below(5) as usize; // 3..=7 extra atoms
        for _ in 0..n_atoms {
            // 0,1: (dis)equality between two pool terms.
            // 2..: a linear atom over up to 2 pool terms with small coeffs.
            let kind = rng.below(5);
            if kind < 2 {
                let i = rng.below(pool.len() as u64) as usize;
                let j = rng.below(pool.len() as u64) as usize;
                let neg = rng.below(2) == 0;
                let s_eq = s.eq(pool[i].s, pool[j].s);
                let z_eq = ctx.eq(pool[i].z, pool[j].z);
                if neg {
                    let s_atom = s.app(Op::Builtin(BuiltinOp::Not), &[s_eq]);
                    let z_atom = ctx.not(z_eq);
                    assert_both(
                        &mut s,
                        &mut ctx,
                        &mut dump,
                        s_atom,
                        z_atom,
                        "<distinct pair>",
                    );
                } else {
                    assert_both(&mut s, &mut ctx, &mut dump, s_eq, z_eq, "<eq pair>");
                }
            } else {
                // Linear atom: c0*t0 + c1*t1 REL rhs over two distinct pool terms.
                let i = rng.below(pool.len() as u64) as usize;
                let mut j = rng.below(pool.len() as u64) as usize;
                if j == i {
                    j = (j + 1) % pool.len();
                }
                let c0: i32 = (rng.below(5) as i32) - 2;
                let mut c1: i32 = (rng.below(5) as i32) - 2;
                if c0 == 0 && c1 == 0 {
                    c1 = 1;
                }
                let rhs: i32 = (rng.below(7) as i32) - 3;
                let rel = match rng.below(4) {
                    0 => Rel::Le,
                    1 => Rel::Lt,
                    2 => Rel::Ge,
                    _ => Rel::Gt,
                };

                // shinri lhs.
                let mut s_terms: Vec<shinri_core::TermId> = Vec::new();
                let mut z_terms: Vec<easy_smt::SExpr> = Vec::new();
                for (c, t) in [(c0, i), (c1, j)] {
                    if c == 0 {
                        continue;
                    }
                    let cterm = s.numeral(Rational::from_int((c as i128).into()), real);
                    s_terms.push(s.app(Op::Builtin(BuiltinOp::Mul), &[cterm, pool[t].s]));
                    if let Some(zt) = z_coeff_times_var(&ctx, c, pool[t].z) {
                        z_terms.push(zt);
                    }
                }
                let s_lhs = s_terms
                    .into_iter()
                    .reduce(|acc, t| s.app(Op::Builtin(BuiltinOp::Add), &[acc, t]))
                    .unwrap();
                let z_lhs = z_terms
                    .into_iter()
                    .reduce(|acc, t| ctx.plus(acc, t))
                    .unwrap();
                let s_rhs = s.numeral(Rational::from_int((rhs as i128).into()), real);
                let z_rhs = z_int(&ctx, rhs);
                let (s_atom, z_atom) = match rel {
                    Rel::Le => (
                        s.app(Op::Builtin(BuiltinOp::Le), &[s_lhs, s_rhs]),
                        ctx.lte(z_lhs, z_rhs),
                    ),
                    Rel::Lt => (
                        s.app(Op::Builtin(BuiltinOp::Lt), &[s_lhs, s_rhs]),
                        ctx.lt(z_lhs, z_rhs),
                    ),
                    Rel::Ge => (
                        s.app(Op::Builtin(BuiltinOp::Ge), &[s_lhs, s_rhs]),
                        ctx.gte(z_lhs, z_rhs),
                    ),
                    Rel::Gt => (
                        s.app(Op::Builtin(BuiltinOp::Gt), &[s_lhs, s_rhs]),
                        ctx.gt(z_lhs, z_rhs),
                    ),
                    _ => unreachable!(),
                };
                assert_both(
                    &mut s,
                    &mut ctx,
                    &mut dump,
                    s_atom,
                    z_atom,
                    &format!("<lin {c0}*t{i} + {c1}*t{j} {rel:?} {rhs}>"),
                );
            }
        }

        dump.push_str("\n(check-sat)");

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();

        match (ours, theirs) {
            (SolveOutcome::Unknown, _) => {
                unknowns += 1;
            }
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (o, t) => {
                panic!(
                    "QF_UFLRA SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                     Reproduce with this instance:\n{dump}"
                );
            }
        }
    }

    println!(
        "differential_qf_uflra: {N_ITERS} instances checked, 0 disagreements\n  \
         sat={n_sat} unsat={n_unsat} unknown={unknowns}\n  \
         shapes: pin⇒congruence(arith→EUF)={n_pin_congruence} \
         congruence⇒arith(EUF→arith)={n_cong_arith} nested f(g(x))={n_nested}"
    );

    // Both N-O directions must actually be generated, or the test proves nothing.
    assert!(
        n_pin_congruence > 0 && n_cong_arith > 0,
        "generator failed to exercise both N-O directions: \
         pin⇒congruence={n_pin_congruence} congruence⇒arith={n_cong_arith}"
    );
    // For pure QF_UFLRA the fence should be gone; report any Unknowns loudly.
    assert_eq!(
        unknowns, 0,
        "Got {unknowns} Unknown results in QF_UFLRA — the N-O combination bailed \
         (fence firing). This is worth investigating even though it is sound."
    );
}
