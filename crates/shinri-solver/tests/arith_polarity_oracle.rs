//! Differential oracle (slice 53, spec §6.3): Int/Real `=`/`distinct`/`<=`
//! atoms nested under random `not`/`or`/`and`/`=>`/`xor`/`ite`/Bool-`=` shapes,
//! conjoined with bound pins, checked against z3. The pre-existing arithmetic
//! oracles generate conjunctions, so they never put an arithmetic `=` under
//! non-positive polarity, which is how the slice-53 wrong `sat` survived.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(arith_polarity_oracle)'
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Copied from tests/nary_arith_oracle.rs (the per-binary convention).
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
const VARS: &[&str] = &["x", "y", "z"];

#[derive(Clone, Copy)]
enum Sort {
    Int,
    Real,
}

impl Sort {
    fn name(self) -> &'static str {
        match self {
            Sort::Int => "Int",
            Sort::Real => "Real",
        }
    }
    fn logic(self) -> &'static str {
        match self {
            Sort::Int => "QF_LIA",
            Sort::Real => "QF_LRA",
        }
    }
    /// A literal in -2..=2: `(- 1)` / `(- 1.0)` for negatives.
    fn lit(self, k: i64) -> String {
        let mag = match self {
            Sort::Int => format!("{}", k.abs()),
            Sort::Real => format!("{}.0", k.abs()),
        };
        if k < 0 {
            format!("(- {mag})")
        } else {
            mag
        }
    }
}

fn var(rng: &mut Lcg) -> &'static str {
    VARS[rng.below(VARS.len() as u64) as usize]
}

/// Small constants (-2..=2) so atoms collide with the pinned values often.
fn small(rng: &mut Lcg) -> i64 {
    rng.below(5) as i64 - 2
}

/// An arithmetic term: a variable, `(+ v k)`, `(- v w)` or `(* c v)`.
fn term(rng: &mut Lcg, s: Sort) -> String {
    match rng.below(4) {
        0 => var(rng).to_string(),
        1 => format!("(+ {} {})", var(rng), s.lit(small(rng))),
        2 => format!("(- {} {})", var(rng), var(rng)),
        _ => format!("(* {} {})", s.lit(1 + rng.below(2) as i64), var(rng)),
    }
}

fn atom(rng: &mut Lcg, s: Sort) -> String {
    let rhs = if rng.below(2) == 0 {
        var(rng).to_string()
    } else {
        s.lit(small(rng))
    };
    let op = match rng.below(6) {
        0..=3 => "=", // bias towards the atom under test
        4 => "distinct",
        _ => "<=",
    };
    format!("({op} {} {rhs})", term(rng, s))
}

fn formula(rng: &mut Lcg, s: Sort, depth: u32) -> String {
    if depth == 0 || rng.below(4) == 0 {
        return if rng.below(6) == 0 {
            "p".to_string()
        } else {
            atom(rng, s)
        };
    }
    let k = rng.below(7);
    let mut f = || formula(rng, s, depth - 1);
    match k {
        0 => format!("(not {})", f()),
        1 => format!("(or {} {})", f(), f()),
        2 => format!("(and {} {})", f(), f()),
        3 => format!("(=> {} {})", f(), f()),
        4 => format!("(xor {} {})", f(), f()),
        5 => format!("(ite {} {} {})", f(), f(), f()),
        _ => format!("(= {} {})", f(), f()),
    }
}

fn gen_script(rng: &mut Lcg, s: Sort) -> String {
    let mut src = String::from("(declare-const p Bool)\n");
    for v in VARS {
        src.push_str(&format!("(declare-const {v} {})\n", s.name()));
    }
    // A negated root makes non-positive polarity the common case.
    let root = formula(rng, s, 3);
    let root = if rng.below(2) == 0 {
        format!("(not {root})")
    } else {
        root
    };
    src.push_str(&format!("(assert {root})\n"));
    // 0..=2 pins, each squeezing a variable to a small value via <= and >=.
    for _ in 0..rng.below(3) {
        let (v, k) = (var(rng), s.lit(small(rng)));
        src.push_str(&format!("(assert (<= {v} {k}))\n(assert (>= {v} {k}))\n"));
    }
    src.push_str("(check-sat)\n");
    src
}

fn shinri_outcome(logic: &str, src: &str) -> SolveOutcome {
    let full = format!("(set-logic {logic})\n{src}");
    let mut solver = Solver::new();
    let mut parser = Parser::new(&full);
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

fn z3_outcome(logic: &str, src: &str) -> easy_smt::Response {
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()
        .expect("failed to launch z3 — run `mise install`");
    ctx.set_logic(logic).expect("z3 set-logic failed");
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

fn run_family(s: Sort, seed: u64) {
    let mut rng = Lcg(seed);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut disagreements: Vec<String> = Vec::new();
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng, s);
        let ours = shinri_outcome(s.logic(), &src);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {
                n_unknown += 1;
                continue;
            }
        }
        match (ours, z3_outcome(s.logic(), &src)) {
            (SolveOutcome::Sat, easy_smt::Response::Sat)
            | (SolveOutcome::Unsat, easy_smt::Response::Unsat)
            | (_, easy_smt::Response::Unknown) => {}
            (o, t) => disagreements.push(format!("iter {iter}: shinri={o:?} z3={t:?}\n{src}")),
        }
    }
    println!(
        "{}: sat={n_sat} unsat={n_unsat} unknown={n_unknown} disagreements={}",
        s.logic(),
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "{} disagreements; first three:\n{}",
        disagreements.len(),
        disagreements
            .iter()
            .take(3)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "need both sat ({n_sat}) and unsat ({n_unsat})"
    );
    assert_eq!(n_unknown, 0, "QF_LIA/QF_LRA are total in shinri");
}

#[test]
fn differential_qf_lia_lra_polarity() {
    run_family(Sort::Int, 0x51CE_0053_0001);
    run_family(Sort::Real, 0x51CE_0053_0002);
}
