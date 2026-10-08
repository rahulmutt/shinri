//! Differential oracle: shinri vs z3 on QF_LIA scripts whose products carry a
//! unary-minus constant coefficient, `(* (- k) v)` / `(* v (- k))` /
//! `(* (- (- k)) v)` (slice 63). Requires z3 on PATH.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(neg_coeff_oracle)'
//!
//! Variables are bounded to [-3, 3], so every script is small and decidable:
//! shinri's own `Unknown` is not tolerated (it fails the test). A z3 `unknown`
//! is skipped, and bounded by the 90% z3-confirmation floor.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand
/// (same convention as tests/nary_arith_oracle.rs).
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
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

fn z3_outcome_lia(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_LIA").expect("z3 set-logic failed");
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

/// SMT-LIB integer literal; negatives use the `(- k)` form.
fn int_lit(k: i64) -> String {
    if k < 0 {
        format!("(- {})", -k)
    } else {
        format!("{k}")
    }
}

/// `k·v` for k in -4..=4 \ {0}, in a slice-63 shape: the coefficient on
/// either side; one time in four the literal is `(- <literal of -k>)`,
/// which gives a double negation `(- (- k))` for positive k.
fn gen_product(rng: &mut Lcg) -> String {
    let v = VARS[rng.below(VARS.len() as u64) as usize];
    let mut k = rng.below(8) as i64 - 4;
    if k >= 0 {
        k += 1;
    }
    let lit = if rng.below(4) == 0 {
        format!("(- {})", int_lit(-k))
    } else {
        int_lit(k)
    };
    if rng.below(2) == 0 {
        format!("(* {lit} {v})")
    } else {
        format!("(* {v} {lit})")
    }
}

/// A linear sum of 1..=3 products, sometimes as a binary `-`.
fn gen_lhs(rng: &mut Lcg) -> String {
    match rng.below(4) {
        0 => format!("(- {} {})", gen_product(rng), gen_product(rng)),
        _ => {
            let n = 1 + rng.below(3) as usize;
            let ps: Vec<String> = (0..n).map(|_| gen_product(rng)).collect();
            if n == 1 {
                ps[0].clone()
            } else {
                format!("(+ {})", ps.join(" "))
            }
        }
    }
}

fn gen_atom(rng: &mut Lcg) -> String {
    let op = ["<=", ">=", "=", "<"][rng.below(4) as usize];
    let rhs = int_lit(rng.below(11) as i64 - 5);
    format!("({op} {} {rhs})", gen_lhs(rng))
}

fn gen_script(rng: &mut Lcg) -> String {
    let mut s = String::from("(set-logic QF_LIA)\n");
    for v in VARS {
        s.push_str(&format!("(declare-const {v} Int)\n"));
    }
    for v in VARS {
        s.push_str(&format!("(assert (and (<= (- 3) {v}) (<= {v} 3)))\n"));
    }
    for _ in 0..2 + rng.below(4) {
        let a = match rng.below(4) {
            0 => format!("(not {})", gen_atom(rng)),
            1 => format!("(or {} {})", gen_atom(rng), gen_atom(rng)),
            _ => gen_atom(rng),
        };
        s.push_str(&format!("(assert {a})\n"));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_lia_neg_coeff() {
    let mut rng = Lcg(0x51CE_0063);
    let (mut n_sat, mut n_unsat, mut n_z3_checked) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng);
        let ours = shinri_outcome(&src);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {
                panic!("unknown on a bounded QF_LIA script (iter {iter}):\n{src}")
            }
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        match (ours, z3_outcome_lia(&mut ctx, &src)) {
            (SolveOutcome::Sat, easy_smt::Response::Sat)
            | (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (_, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_LIA (- k) coefficient DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_lia_neg_coeff: sat={n_sat} unsat={n_unsat} z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat)"
    );
    assert!(
        n_z3_checked >= N_ITERS * 9 / 10,
        "z3 must confirm at least 90% of iterations ({n_z3_checked}/{N_ITERS})"
    );
}
