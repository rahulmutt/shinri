//! Differential oracle: shinri-solver vs z3 on random n-ary =/distinct over
//! Bool and an uninterpreted sort (slice 6 — the sorts word_norm previously
//! skipped, where tseitin/EUF silently dropped operands 3+).
//!
//! Run with:
//!   cargo test -p shinri-solver --features oracle --test nary_oracle -- --nocapture
//!
//! Requires `z3` on PATH at runtime. Mirrors tests/fp_oracle.rs.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand.
/// Copied verbatim from tests/fp_oracle.rs to match the existing convention.
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

fn z3_outcome_uf(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_UF").expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-sort ")
            || t.starts_with("(declare-const ")
            || t.starts_with("(assert ")
        {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

const BOOLS: &[&str] = &["p", "q", "r", "s"];
const ELEMS: &[&str] = &["a", "b", "c", "d"];

/// One n-ary (arity 2..=4) =/distinct atom over a single sort family.
/// Duplicate operands are allowed on purpose (they fold = to true-ish
/// constraints and make distinct trivially unsat — both good probes).
fn gen_atom(rng: &mut Lcg) -> String {
    let pool: &[&str] = if rng.below(2) == 0 { BOOLS } else { ELEMS };
    let n = 2 + rng.below(3) as usize;
    let ops: Vec<&str> = (0..n)
        .map(|_| pool[rng.below(pool.len() as u64) as usize])
        .collect();
    let op = if rng.below(2) == 0 { "=" } else { "distinct" };
    format!("({} {})", op, ops.join(" "))
}

fn gen_assertion(rng: &mut Lcg) -> String {
    match rng.below(4) {
        0 => gen_atom(rng),
        1 => format!("(not {})", gen_atom(rng)),
        2 => format!("(and {} {})", gen_atom(rng), gen_atom(rng)),
        _ => format!("(or {} {})", gen_atom(rng), gen_atom(rng)),
    }
}

fn gen_script(rng: &mut Lcg) -> String {
    let mut s = String::new();
    s.push_str("(declare-sort U 0)\n");
    for b in BOOLS {
        s.push_str(&format!("(declare-const {b} Bool)\n"));
    }
    for e in ELEMS {
        s.push_str(&format!("(declare-const {e} U)\n"));
    }
    let n = 2 + rng.below(3);
    for _ in 0..n {
        s.push_str(&format!("(assert {})\n", gen_assertion(rng)));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_uf_nary() {
    let mut rng = Lcg(0x51CE6_ABCD);
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
        let theirs = z3_outcome_uf(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_UF n-ary DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_uf_nary: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(
        n_unknown == 0,
        "unknown must be 0 — QF_UF is total ({n_unknown} unknown)"
    );
    assert!(
        n_z3_checked == N_ITERS,
        "expected every iteration z3-checked with zero disagreements \
         ({n_z3_checked}/{N_ITERS} checked)"
    );
}

// ---------------------------------------------------------------------------
// String family (QF_S): n-ary =/distinct over a pool that mixes String vars,
// compound `(str.++ si "…")` terms, and "". Strings may SOUNDLY fence (return
// unknown), so this family uses RELAXED asserts (unlike the total UF family):
// we only require SAT and UNSAT coverage, at least one z3-checked decision, and
// ZERO disagreements. Exercises the C1 self-check descent into `(and …)`
// wrappers that word_norm emits for expanded compound n-ary equalities.
// ---------------------------------------------------------------------------

const STR_VARS: &[&str] = &["s1", "s2", "s3"];

/// The operand pool: {s1,s2,s3, (str.++ si "a"), (str.++ si "b"), ""}.
fn str_pool() -> Vec<String> {
    let mut pool: Vec<String> = STR_VARS.iter().map(|v| v.to_string()).collect();
    for v in STR_VARS {
        pool.push(format!("(str.++ {v} \"a\")"));
    }
    for v in STR_VARS {
        pool.push(format!("(str.++ {v} \"b\")"));
    }
    pool.push("\"\"".to_string());
    pool
}

fn gen_atom_s(rng: &mut Lcg, pool: &[String]) -> String {
    let n = 2 + rng.below(3) as usize;
    let ops: Vec<String> = (0..n)
        .map(|_| pool[rng.below(pool.len() as u64) as usize].clone())
        .collect();
    let op = if rng.below(2) == 0 { "=" } else { "distinct" };
    format!("({} {})", op, ops.join(" "))
}

fn gen_assertion_s(rng: &mut Lcg, pool: &[String]) -> String {
    match rng.below(4) {
        0 => gen_atom_s(rng, pool),
        1 => format!("(not {})", gen_atom_s(rng, pool)),
        _ => format!("(and {} {})", gen_atom_s(rng, pool), gen_atom_s(rng, pool)),
    }
}

fn gen_script_s(rng: &mut Lcg) -> String {
    let pool = str_pool();
    let mut s = String::new();
    for v in STR_VARS {
        s.push_str(&format!("(declare-const {v} String)\n"));
    }
    let n = 2 + rng.below(3);
    for _ in 0..n {
        s.push_str(&format!("(assert {})\n", gen_assertion_s(rng, &pool)));
    }
    s.push_str("(check-sat)\n");
    s
}

fn z3_outcome_s(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_S").expect("z3 set-logic failed");
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

#[test]
fn differential_qf_s_nary() {
    // Seed for string oracle differential. Prior seed 0xB000_9E37 avoided
    // panics now fixed: I2 VMTF premature-SAT (slice 7), eq_engine
    // InsertOverwrite/residual-diseq and EUF stale-pending-congruence (cluster
    // C, slice 8), analyze/backtrack robustness (cluster B, slice 8), and
    // distinct-over-concat empty-length hardening (cluster A, slice 8).
    // C1 self-check descent is exercised by `(and …)` wrappers in gen_assertion_s.
    let mut rng = Lcg(0xB000_9E38);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_script_s(&mut rng);
        let ours = shinri_outcome(&src);
        // Strings may soundly fence: unknown is allowed here, just skip z3.
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
        let theirs = z3_outcome_s(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_S n-ary DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_s_nary: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    // RELAXED asserts (strings may fence): require coverage + at least one
    // z3-checked decision; disagreements already panic above.
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(
        n_z3_checked > 0,
        "expected at least one z3-checked decision ({n_z3_checked} checked)"
    );
}
