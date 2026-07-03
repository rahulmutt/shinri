//! Differential oracle: shinri vs z3 on negated/positive n-ary arith `=` over
//! Int with bound constraints (slice 7 — C2's family; no prior oracle covered
//! arith n-ary =). Requires z3 on PATH.
//!
//! Run with:
//!   cargo test -p shinri-solver --features oracle --test nary_arith_oracle -- --nocapture
//!
//! ## What it checks
//! C2 was a wrong-SAT bug: negated n-ary `=` over Int (e.g. `(not (= a b c))`)
//! was unsound-lowered such that shinri could say Sat on scripts that are
//! actually Unsat once combined with bound constraints that force pairwise
//! equality (`(<= a b)` + `(>= a b)` squeezes `a = b`, which combined with
//! `(not (= a b c))` should force Unsat whenever the third variable is also
//! squeezed equal). This oracle generates random Int-sorted scripts mixing
//! negated/positive n-ary `=` atoms (arity 2..=4) with such bound pairs and
//! checks shinri's verdict against z3 with zero disagreements. QF_LIA is a
//! decidable/total logic, so Unknown is NOT tolerated here (unlike the QF_S
//! family in nary_oracle.rs).
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand.
/// Copied verbatim from tests/nary_oracle.rs to match the existing convention.
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

const INT_VARS: &[&str] = &["a", "b", "c", "d"];

/// One n-ary (arity 2..=4) `=` atom over Int variables. Duplicate operands
/// are allowed on purpose (they fold `=` to true-ish constraints and are a
/// good self-check probe, mirroring gen_atom in nary_oracle.rs).
fn gen_eq_atom(rng: &mut Lcg) -> String {
    let n = 2 + rng.below(3) as usize;
    let ops: Vec<&str> = (0..n)
        .map(|_| INT_VARS[rng.below(INT_VARS.len() as u64) as usize])
        .collect();
    format!("(= {})", ops.join(" "))
}

/// Render an SMT-LIB2 integer literal, using the `(- k)` unary-minus form
/// for negative values (bare `-k` is not a valid SMT-LIB2 numeral token).
fn int_lit(k: i64) -> String {
    if k < 0 {
        format!("(- {})", -k)
    } else {
        format!("{k}")
    }
}

/// A bound constraint: either between two (possibly equal) Int vars, or
/// between a var and a small integer literal in -5..=5. Generating both
/// `(<= a b)` and `(>= a b)` for the same pair (across different assertions
/// in the same script) squeezes `a = b` — the exact C2 shape when combined
/// with a negated n-ary `=` over a superset of vars.
fn gen_bound(rng: &mut Lcg) -> String {
    let op = if rng.below(2) == 0 { "<=" } else { ">=" };
    let lhs = INT_VARS[rng.below(INT_VARS.len() as u64) as usize];
    if rng.below(2) == 0 {
        let rhs = INT_VARS[rng.below(INT_VARS.len() as u64) as usize];
        format!("({op} {lhs} {rhs})")
    } else {
        let k = rng.below(11) as i64 - 5; // -5..=5
        format!("({op} {lhs} {})", int_lit(k))
    }
}

/// One assertion: a negated n-ary `=` (C2's exact shape), a positive n-ary
/// `=`, a single bound constraint, or a conjunction/disjunction of two
/// bounds. The conjunction case is what commonly forces pairwise equality
/// between two variables (`(<= a b)` AND `(>= a b)` ⇒ `a = b`).
fn gen_assertion(rng: &mut Lcg) -> String {
    match rng.below(5) {
        0 => format!("(not {})", gen_eq_atom(rng)),
        1 => gen_eq_atom(rng),
        2 => gen_bound(rng),
        3 => format!("(and {} {})", gen_bound(rng), gen_bound(rng)),
        _ => format!("(or {} {})", gen_bound(rng), gen_bound(rng)),
    }
}

fn gen_script(rng: &mut Lcg) -> String {
    let mut s = String::new();
    for v in INT_VARS {
        s.push_str(&format!("(declare-const {v} Int)\n"));
    }
    let n = 2 + rng.below(3);
    for _ in 0..n {
        s.push_str(&format!("(assert {})\n", gen_assertion(rng)));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_lia_nary() {
    let mut rng = Lcg(0x51CE7_0001);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_lia(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_LIA n-ary DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_lia_nary: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(n_unknown == 0, "unknown must be 0 — QF_LIA is total ({n_unknown} unknown)");
    assert!(
        n_z3_checked == N_ITERS,
        "expected every iteration z3-checked with zero disagreements \
         ({n_z3_checked}/{N_ITERS} checked)"
    );
}
