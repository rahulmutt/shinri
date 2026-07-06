//! Differential oracle: shinri vs z3 on ite over Int/Real/uninterpreted sorts
//! (slice 10 — the EUF-opaque ite wrong-SAT family; no prior oracle fuzzed
//! term-level ite over these sorts). Requires z3 on PATH.
//!
//! Run with:
//!   cargo test -p shinri-solver --features oracle --test ite_oracle -- --nocapture
//!
//! All three fragments (QF_LRA / QF_LIA / QF_UF with ite) are decidable and
//! admitted post-slice-10, so Unknown is NOT tolerated and both SAT and UNSAT
//! witnesses must arise.
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

/// Forward declare-sort/declare-fun/assert lines to z3 under `logic`.
fn z3_outcome(ctx: &mut easy_smt::Context, logic: &str, src: &str) -> easy_smt::Response {
    ctx.set_logic(logic).expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-sort ")
            || t.starts_with("(declare-fun ")
            || t.starts_with("(assert ")
        {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

fn z3_ctx() -> easy_smt::Context {
    easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()
        .expect("failed to launch z3 — ensure z3 is on PATH")
}

fn assert_no_disagreement(
    ours: SolveOutcome,
    theirs: easy_smt::Response,
    family: &str,
    iter: usize,
    s: &str,
) {
    assert!(
        !matches!(
            (ours, theirs),
            (SolveOutcome::Sat, easy_smt::Response::Unsat)
                | (SolveOutcome::Unsat, easy_smt::Response::Sat)
        ),
        "{family} ite DISAGREEMENT (iter {iter}): shinri={ours:?} z3={theirs:?}\n{s}"
    );
}

/// Real-sorted ite: (ite b c1 c2) compared against a bound, with the
/// condition sometimes pinned so both branches get exercised.
fn gen_lra_ite_script(rng: &mut Lcg) -> String {
    let consts = ["0.25", "1.0", "2.5", "4.0"];
    let c1 = consts[rng.below(consts.len() as u64) as usize];
    let c2 = consts[rng.below(consts.len() as u64) as usize];
    let bound = consts[rng.below(consts.len() as u64) as usize];
    let ops = ["<=", "<", ">=", ">", "="];
    let op = ops[rng.below(ops.len() as u64) as usize];
    let mut s = String::from("(declare-fun b () Bool)\n");
    s.push_str(&format!("(assert ({op} (ite b {c1} {c2}) {bound}))\n"));
    match rng.below(3) {
        0 => s.push_str("(assert b)\n"),
        1 => s.push_str("(assert (not b))\n"),
        _ => {}
    }
    s.push_str("(check-sat)\n");
    s
}

/// Int-sorted ite nested under +, compared against a bound.
fn gen_lia_ite_script(rng: &mut Lcg) -> String {
    let c1 = rng.below(5) as i64;
    let c2 = rng.below(5) as i64;
    let add = rng.below(3) as i64;
    let bound = rng.below(8) as i64;
    let ops = ["<=", "<", ">=", ">", "="];
    let op = ops[rng.below(ops.len() as u64) as usize];
    let mut s = String::from("(declare-fun b () Bool)\n");
    s.push_str(&format!(
        "(assert ({op} (+ (ite b {c1} {c2}) {add}) {bound}))\n"
    ));
    match rng.below(3) {
        0 => s.push_str("(assert b)\n"),
        1 => s.push_str("(assert (not b))\n"),
        _ => {}
    }
    s.push_str("(check-sat)\n");
    s
}

/// Uninterpreted-sort ite among 3 constants with random (dis)equalities.
fn gen_uf_ite_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(declare-sort U 0)\n\
         (declare-fun b () Bool)\n\
         (declare-fun u1 () U)\n\
         (declare-fun u2 () U)\n\
         (declare-fun u3 () U)\n",
    );
    let rhs = ["u1", "u2", "u3"][rng.below(3) as usize];
    s.push_str(&format!("(assert (= (ite b u1 u2) {rhs}))\n"));
    match rng.below(4) {
        0 => s.push_str("(assert (distinct u1 u2 u3))\n"),
        1 => s.push_str("(assert (distinct u1 u2))\n"),
        2 => s.push_str("(assert (= u1 u2))\n"),
        _ => {}
    }
    match rng.below(3) {
        0 => s.push_str("(assert b)\n"),
        1 => s.push_str("(assert (not b))\n"),
        _ => {}
    }
    s.push_str("(check-sat)\n");
    s
}

fn run_family(family: &str, logic: &str, seed: u64, gen: fn(&mut Lcg) -> String) {
    let mut rng = Lcg(seed);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let s = gen(&mut rng);
        let ours = shinri_outcome(&s);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => n_unknown += 1,
        }
        let mut ctx = z3_ctx();
        let theirs = z3_outcome(&mut ctx, logic, &s);
        assert_no_disagreement(ours, theirs, family, iter, &s);
    }
    println!("{family}: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(
        n_sat > 0 && n_unsat > 0,
        "{family} produced no SAT/UNSAT coverage (sat={n_sat} unsat={n_unsat})"
    );
    assert_eq!(
        n_unknown, 0,
        "{family}: decidable ite fragment must never fence ({n_unknown})"
    );
}

#[test]
fn differential_qf_lra_ite() {
    run_family(
        "differential_qf_lra_ite",
        "QF_LRA",
        0x517E_0A11_D00D,
        gen_lra_ite_script,
    );
}

#[test]
fn differential_qf_lia_ite() {
    run_family(
        "differential_qf_lia_ite",
        "QF_LIA",
        0x517E_0B22_FEED,
        gen_lia_ite_script,
    );
}

#[test]
fn differential_qf_uf_ite() {
    run_family(
        "differential_qf_uf_ite",
        "QF_UF",
        0x517E_0C33_CAFE,
        gen_uf_ite_script,
    );
}
