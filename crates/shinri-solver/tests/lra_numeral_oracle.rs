//! Differential oracle: shinri vs z3 on QF_LRA scripts whose constants are
//! integer literals — bare, `(- k)`, and let-bound — in Real contexts
//! (slice 64). Requires z3 on PATH.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(lra_numeral_oracle)'
//!
//! Negative coefficients are written `(- (* k v))`, `(* (- k) v)` or
//! `(* v (- k))`. The last two are the cross-slice case (final review,
//! slice 64): `(- k)` is an integer-literal negation that slice 64 mints as
//! a Real in Reals logics, and slice 63 is what accepts a constant-coefficient
//! product of that shape as linear. `+` also takes bare integer-literal
//! operands (`(+ (* 2 a) 3)`).
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG (same convention as tests/nary_arith_oracle.rs).
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

const N_ITERS: usize = 200;
const VARS: &[&str] = &["a", "b", "c"];

fn shinri_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.unwrap_or_else(|e| panic!("parse error {e:?} in:\n{src}"));
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

fn z3_outcome_lra(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_LRA").expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-const ") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

/// An integer literal; negatives as `(- k)`.
fn int_lit(k: i64) -> String {
    if k < 0 {
        format!("(- {})", -k)
    } else {
        format!("{k}")
    }
}

/// Which cross-slice shapes a generated script contains.
#[derive(Default)]
struct Shapes {
    /// A `(* (- k) v)` or `(* v (- k))` product.
    neg_coeff: bool,
    /// A `+` with an integer-literal operand.
    lit_summand: bool,
}

/// `k·v` with k in -3..=3 \ {0}: `(* k v)` / `(* v k)`, or for negative k
/// one of `(- (* |k| v))`, `(* (- |k|) v)`, `(* v (- |k|))`.
fn gen_product(rng: &mut Lcg, shapes: &mut Shapes) -> String {
    let v = VARS[rng.below(VARS.len() as u64) as usize];
    let mut k = rng.below(6) as i64 - 3;
    if k >= 0 {
        k += 1;
    }
    if k < 0 {
        match rng.below(3) {
            0 => format!("(- (* {} {v}))", -k),
            1 => {
                shapes.neg_coeff = true;
                format!("(* {} {v})", int_lit(k))
            }
            _ => {
                shapes.neg_coeff = true;
                format!("(* {v} {})", int_lit(k))
            }
        }
    } else if rng.below(2) == 0 {
        format!("(* {k} {v})")
    } else {
        format!("(* {v} {k})")
    }
}

/// A sum of 1–3 products, plus (one time in three) an integer-literal
/// operand `(+ … k)`.
fn gen_lhs(rng: &mut Lcg, shapes: &mut Shapes) -> String {
    let n = 1 + rng.below(3) as usize;
    let mut ps: Vec<String> = (0..n).map(|_| gen_product(rng, shapes)).collect();
    if rng.below(3) == 0 {
        shapes.lit_summand = true;
        ps.push(int_lit(rng.below(7) as i64 - 3));
    }
    if ps.len() == 1 {
        ps[0].clone()
    } else {
        format!("(+ {})", ps.join(" "))
    }
}

/// An atom whose constant is a bare literal, `(- k)`, or let-bound.
fn gen_atom(rng: &mut Lcg, shapes: &mut Shapes) -> String {
    let op = ["<=", ">=", "=", "<"][rng.below(4) as usize];
    let lhs = gen_lhs(rng, shapes);
    let k = int_lit(rng.below(11) as i64 - 5);
    if rng.below(3) == 0 {
        format!("(let ((?k {k})) ({op} {lhs} ?k))")
    } else {
        format!("({op} {lhs} {k})")
    }
}

fn gen_script(rng: &mut Lcg, shapes: &mut Shapes) -> String {
    let mut s = String::from("(set-logic QF_LRA)\n");
    for v in VARS {
        s.push_str(&format!("(declare-const {v} Real)\n"));
    }
    for v in VARS {
        s.push_str(&format!("(assert (and (<= (- 3) {v}) (<= {v} 3)))\n"));
    }
    for _ in 0..2 + rng.below(4) {
        let a = match rng.below(4) {
            0 => format!("(not {})", gen_atom(rng, shapes)),
            1 => format!("(or {} {})", gen_atom(rng, shapes), gen_atom(rng, shapes)),
            _ => gen_atom(rng, shapes),
        };
        s.push_str(&format!("(assert {a})\n"));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_lra_integer_literals() {
    let mut rng = Lcg(0x51CE_0064);
    let (mut n_sat, mut n_unsat, mut n_z3_checked) = (0usize, 0usize, 0usize);
    // Scripts exercising the cross-slice shapes (vacuity floors below).
    let (mut n_neg_coeff, mut n_lit_summand) = (0usize, 0usize);
    for iter in 0..N_ITERS {
        let mut shapes = Shapes::default();
        let src = gen_script(&mut rng, &mut shapes);
        n_neg_coeff += usize::from(shapes.neg_coeff);
        n_lit_summand += usize::from(shapes.lit_summand);
        let ours = shinri_outcome(&src);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {
                panic!("unknown on a bounded QF_LRA script (iter {iter}):\n{src}")
            }
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        match (ours, z3_outcome_lra(&mut ctx, &src)) {
            (SolveOutcome::Sat, easy_smt::Response::Sat)
            | (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (o, t) => panic!(
                "QF_LRA integer-literal DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_lra_integer_literals: sat={n_sat} unsat={n_unsat} \
         z3_checked={n_z3_checked} neg_coeff_scripts={n_neg_coeff} \
         literal_summand_scripts={n_lit_summand}"
    );
    assert!(
        n_neg_coeff >= N_ITERS / 4 && n_lit_summand >= N_ITERS / 4,
        "cross-slice shapes under-sampled ({n_neg_coeff} (* (- k) v) scripts, \
         {n_lit_summand} literal-summand scripts)"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat)"
    );
    assert_eq!(
        n_z3_checked, N_ITERS,
        "every iteration must be z3-confirmed"
    );
}
