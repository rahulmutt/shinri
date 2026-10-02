//! Differential oracle (slice 54, spec §6.3): uninterpreted functions and a
//! datatype constructor applied to compound Bool arguments, checked against
//! z3. Arguments are drawn from a small shared atom pool so that two
//! applications often receive equivalent arguments — congruence then has to
//! see through the argument's truth value, which is exactly what the slice-54
//! wrong `sat` broke (a compound Bool argument was an opaque e-graph node).
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)'
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

#[derive(Clone, Copy, PartialEq)]
enum Family {
    UfLia,
    UfLra,
    Dt,
}

impl Family {
    fn logic(self) -> &'static str {
        match self {
            Family::UfLia => "QF_UFLIA",
            Family::UfLra => "QF_UFLRA",
            Family::Dt => "QF_DT",
        }
    }
    fn decls(self) -> &'static str {
        match self {
            Family::UfLia => {
                "(declare-const p Bool)\n(declare-const q Bool)\n\
                 (declare-const x Int)\n(declare-const y Int)\n\
                 (declare-fun P (Bool) Bool)\n(declare-fun f (Bool Int) Int)\n"
            }
            Family::UfLra => {
                "(declare-const p Bool)\n(declare-const q Bool)\n\
                 (declare-const x Real)\n(declare-const y Real)\n\
                 (declare-fun P (Bool) Bool)\n(declare-fun f (Bool Real) Real)\n"
            }
            Family::Dt => {
                "(declare-datatypes ((B 0)) (((mk (fa Bool) (fb Bool)) (nil))))\n\
                 (declare-const p Bool)\n(declare-const q Bool)\n\
                 (declare-const u B)\n(declare-const v B)\n"
            }
        }
    }
    /// The shared atom pool: Bool variables plus theory atoms.
    fn leaves(self) -> &'static [&'static str] {
        match self {
            Family::UfLia => &["p", "q", "(= x 1)", "(<= y 0)", "(= x y)"],
            Family::UfLra => &["p", "q", "(= x 1.0)", "(<= y 0.0)", "(= x y)"],
            Family::Dt => &["p", "q", "(fa u)", "((_ is mk) v)", "(= u v)"],
        }
    }
    fn lit(self, k: u64) -> String {
        match self {
            Family::UfLra => format!("{k}.0"),
            _ => format!("{k}"),
        }
    }
}

fn leaf(rng: &mut Lcg, fam: Family) -> String {
    let ls = fam.leaves();
    ls[rng.below(ls.len() as u64) as usize].to_string()
}

fn formula(rng: &mut Lcg, fam: Family, depth: u32) -> String {
    if depth == 0 || rng.below(3) == 0 {
        return leaf(rng, fam);
    }
    let k = rng.below(5);
    let mut f = || formula(rng, fam, depth - 1);
    match k {
        0 => format!("(not {})", f()),
        1 => format!("(and {} {})", f(), f()),
        2 => format!("(or {} {})", f(), f()),
        3 => format!("(=> {} {})", f(), f()),
        _ => format!("(xor {} {})", f(), f()),
    }
}

/// A Bool argument: `true`/`false` (so congruence with a constant matters)
/// or a depth-≤1 formula (a leaf or one connective over leaves).
fn arg(rng: &mut Lcg, fam: Family) -> String {
    match rng.below(5) {
        0 => "true".to_string(),
        1 => "false".to_string(),
        _ => formula(rng, fam, 1),
    }
}

fn assertion(rng: &mut Lcg, fam: Family) -> String {
    let k = rng.below(6);
    if k >= 4 {
        // Pins on the atom pool, so the arguments' truth values are forced.
        return if k == 4 {
            formula(rng, fam, 2)
        } else {
            format!("(not {})", formula(rng, fam, 1))
        };
    }
    match fam {
        Family::Dt => match k {
            0 => format!("(= u (mk {} {}))", arg(rng, fam), arg(rng, fam)),
            1 => format!("(= v (mk {} {}))", arg(rng, fam), arg(rng, fam)),
            2 => format!(
                "(distinct (mk {} {}) (mk {} {}))",
                arg(rng, fam),
                arg(rng, fam),
                arg(rng, fam),
                arg(rng, fam)
            ),
            _ => {
                if rng.below(2) == 0 {
                    "(= u v)".to_string()
                } else {
                    "(not (= u v))".to_string()
                }
            }
        },
        _ => match k {
            0 => format!("(P {})", arg(rng, fam)),
            1 => format!("(not (P {}))", arg(rng, fam)),
            2 => format!("(= (f {} x) {})", arg(rng, fam), fam.lit(rng.below(3))),
            _ => format!("(distinct (f {} y) (f {} y))", arg(rng, fam), arg(rng, fam)),
        },
    }
}

fn gen_script(rng: &mut Lcg, fam: Family) -> String {
    let mut src = String::from(fam.decls());
    for _ in 0..3 + rng.below(3) {
        src.push_str(&format!("(assert {})\n", assertion(rng, fam)));
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
        if t.starts_with("(declare-") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            let ack = ctx.raw_recv().expect("z3 ack failed");
            let ack = ctx.display(ack).to_string();
            assert!(
                !ack.contains("error"),
                "z3 rejected a generated line (assertion dropped): {ack}\n{t}"
            );
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

fn run_family(fam: Family, seed: u64) {
    let mut rng = Lcg(seed);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut disagreements: Vec<String> = Vec::new();
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng, fam);
        let ours = shinri_outcome(fam.logic(), &src);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {
                n_unknown += 1;
                continue;
            }
        }
        match (ours, z3_outcome(fam.logic(), &src)) {
            (SolveOutcome::Sat, easy_smt::Response::Sat)
            | (SolveOutcome::Unsat, easy_smt::Response::Unsat)
            | (_, easy_smt::Response::Unknown) => {}
            (o, t) => disagreements.push(format!("iter {iter}: shinri={o:?} z3={t:?}\n{src}")),
        }
    }
    println!(
        "{}: sat={n_sat} unsat={n_unsat} unknown={n_unknown} disagreements={}",
        fam.logic(),
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
}

#[test]
fn differential_bool_arg_uflia() {
    run_family(Family::UfLia, 0x51CE_0054_0001);
}

#[test]
fn differential_bool_arg_uflra() {
    run_family(Family::UfLra, 0x51CE_0054_0002);
}

#[test]
fn differential_bool_arg_dt() {
    run_family(Family::Dt, 0x51CE_0054_0003);
}
