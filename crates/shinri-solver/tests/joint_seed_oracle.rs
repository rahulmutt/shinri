//! Differential oracle (slice 61, spec §7.3): concat-subject memberships
//! over 1–3 free leaves with constants between them, mixed polarity,
//! optional bare memberships and an optional length pin. Every decided
//! shinri answer must match z3, and every shinri `sat` witness, re-asserted
//! into z3, must be `sat`.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(joint_seed_oracle)'
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

/// Copied verbatim from tests/slice61_probes.rs (minus `set-logic`).
const NORN_531: &str = r#"(declare-fun var_8 () String)
(declare-fun var_9 () String)
(assert (str.in_re (str.++ var_8 "z" var_9 ) (re.++ (re.* (re.++ (str.to_re "a") (re.++ (re.* (re.union (str.to_re "b") (str.to_re "a"))) (str.to_re "z")))) (re.++ (str.to_re "a") (re.* (re.union (str.to_re "b") (str.to_re "a")))))))
(assert (str.in_re (str.++ var_8 "z" var_9 ) (re.++ (re.* (re.union (str.to_re "z") (re.++ (str.to_re "a") (re.++ (re.* (str.to_re "a")) (str.to_re "z"))))) (re.++ (str.to_re "a") (re.* (str.to_re "a"))))))
(assert (str.in_re var_9 (re.* (re.range "a" "u"))))
(assert (str.in_re var_8 (re.* (re.range "a" "u"))))
(assert (not (str.in_re (str.++ "b" var_8 "z" "b" var_9 ) (re.++ (re.* (re.union (re.union (str.to_re "z") (str.to_re "b")) (re.++ (str.to_re "a") (re.union (str.to_re "z") (str.to_re "a"))))) (str.to_re "a")))))
"#;
const REGEX_035: &str = r#"(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ y x) (re.* (str.to_re "b"))))
"#;
const JOINT_EMPTY: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))
(assert (str.in_re x (re.+ (str.to_re "b"))))
"#;
const JOINT_EMPTY_SAT: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))
(assert (str.in_re x (re.+ (str.to_re "a"))))
"#;
const LEN_SUM: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "ab"))))
(assert (= (+ (str.len x) (str.len y)) 3))
"#;
const LEN_PIN: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "ab"))))
(assert (= (str.len x) 3))
"#;

/// shinri's verdict on `body` and, on `sat`, the quoted values of `vars` in
/// order (the text between each pair of quotes; the alphabets here have no
/// `"`).
fn shinri_run(body: &str, vars: &[&str]) -> (SolveOutcome, Vec<String>) {
    let full = format!(
        "(set-logic QF_SLIA)\n{body}(check-sat)\n(get-value ({}))\n",
        vars.join(" ")
    );
    let mut solver = Solver::new();
    let mut parser = Parser::new(&full);
    let mut outcome = SolveOutcome::Unknown;
    let mut values = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            CommandResponse::Values(s) => {
                values = s
                    .split('"')
                    .skip(1)
                    .step_by(2)
                    .map(str::to_string)
                    .collect();
            }
            _ => {}
        }
    }
    (outcome, values)
}

/// `timeout_s` is z3's wall-clock limit; a timeout comes back as `Unknown`.
fn z3_outcome(body: &str, timeout_s: u32) -> easy_smt::Response {
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver(
            "z3",
            [
                "-smt2".to_string(),
                "-in".to_string(),
                format!("-T:{timeout_s}"),
            ],
        )
        .build()
        .expect("failed to launch z3 — run `mise install`");
    ctx.set_logic("QF_SLIA").expect("z3 set-logic failed");
    for line in body.lines() {
        let t = line.trim();
        if t.starts_with("(declare-") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            let ack = ctx.raw_recv().expect("z3 ack failed");
            let ack = ctx.display(ack).to_string();
            assert!(
                !ack.contains("error"),
                "z3 rejected a line (assertion dropped): {ack}\n{t}"
            );
        }
    }
    match ctx.check() {
        Ok(r) => r,
        Err(e) if e.to_string().contains("timeout") => easy_smt::Response::Unknown,
        Err(e) => panic!("z3 check-sat failed: {e}\n{body}"),
    }
}

/// Checks one script against z3. Returns shinri's verdict; a z3 timeout
/// bumps `z3_timeouts`. A shinri `unsat` that z3 cannot confirm fails.
fn check(body: &str, vars: &[&str], timeout_s: u32, z3_timeouts: &mut usize) -> SolveOutcome {
    let (ours, values) = shinri_run(body, vars);
    let theirs = z3_outcome(body, timeout_s);
    if matches!(theirs, easy_smt::Response::Unknown) {
        *z3_timeouts += 1;
    }
    match (ours, theirs) {
        (SolveOutcome::Sat, easy_smt::Response::Unsat) => panic!("shinri sat, z3 unsat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Sat) => panic!("shinri unsat, z3 sat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Unknown) => {
            panic!("shinri unsat, z3 timed out (-T:{timeout_s}), unconfirmed:\n{body}")
        }
        _ => {}
    }
    if ours == SolveOutcome::Sat {
        assert_eq!(values.len(), vars.len(), "get-value shape:\n{body}");
        let mut pinned = body.to_string();
        for (v, val) in vars.iter().zip(&values) {
            pinned.push_str(&format!("(assert (= {v} \"{val}\"))\n"));
        }
        assert!(
            matches!(z3_outcome(&pinned, 20), easy_smt::Response::Sat),
            "z3 rejects shinri's witness {values:?}:\n{body}"
        );
    }
    ours
}

const REGEXES: [&str; 6] = [
    "(re.* (str.to_re \"a\"))",
    "(re.* (re.union (str.to_re \"a\") (str.to_re \"b\")))",
    "(re.++ (re.* (str.to_re \"a\")) (str.to_re \"z\") (re.* (str.to_re \"b\")))",
    "(re.+ (str.to_re \"ab\"))",
    "(re.++ (str.to_re \"a\") (re.* (re.range \"a\" \"z\")))",
    "(re.* (re.union (str.to_re \"z\") (re.++ (str.to_re \"a\") (str.to_re \"b\"))))",
];
const LITS: [&str; 3] = ["a", "b", "z"];
const NAMES: [&str; 3] = ["x", "y", "z"];

/// One generated script over leaves x, y, z (only the first 1–3 are used
/// in subjects; all three are declared, and the test queries only those some
/// assertion mentions).
fn gen(rng: &mut Lcg) -> String {
    let mut body = String::from(
        "(declare-fun x () String)\n(declare-fun y () String)\n(declare-fun z () String)\n",
    );
    let leaves = 1 + rng.below(3) as usize;
    for _ in 0..1 + rng.below(3) {
        let mut ops: Vec<String> = (0..2 + rng.below(3))
            .map(|_| {
                if rng.below(3) == 0 {
                    format!("\"{}\"", LITS[rng.below(3) as usize])
                } else {
                    NAMES[rng.below(leaves as u64) as usize].to_string()
                }
            })
            .collect();
        if ops.iter().all(|o| o.starts_with('"')) {
            ops[0] = "x".to_string();
        }
        let re = REGEXES[rng.below(REGEXES.len() as u64) as usize];
        let a = format!("(str.in_re (str.++ {}) {re})", ops.join(" "));
        if rng.below(4) == 0 {
            body.push_str(&format!("(assert (not {a}))\n"));
        } else {
            body.push_str(&format!("(assert {a})\n"));
        }
    }
    for n in &NAMES[..leaves] {
        if rng.below(2) == 0 {
            body.push_str(&format!(
                "(assert (str.in_re {n} (re.* (re.range \"a\" \"u\"))))\n"
            ));
        }
    }
    if rng.below(4) == 0 {
        let k = rng.below(5);
        if rng.below(2) == 0 {
            body.push_str(&format!("(assert (= (str.len x) {k}))\n"));
        } else {
            body.push_str(&format!("(assert (= (+ (str.len x) (str.len y)) {k}))\n"));
        }
    }
    body
}

#[test]
fn joint_seed_probes_agree_with_z3() {
    let mut t = 0;
    assert_eq!(
        check(NORN_531, &["var_8", "var_9"], 20, &mut t),
        SolveOutcome::Sat
    );
    assert_eq!(check(REGEX_035, &["x", "y"], 20, &mut t), SolveOutcome::Sat);
    assert_ne!(
        check(JOINT_EMPTY, &["x", "y"], 20, &mut t),
        SolveOutcome::Sat
    );
    assert_eq!(
        check(JOINT_EMPTY_SAT, &["x", "y"], 20, &mut t),
        SolveOutcome::Sat
    );
    check(LEN_PIN, &["x", "y"], 20, &mut t);
    assert_ne!(check(LEN_SUM, &["x", "y"], 20, &mut t), SolveOutcome::Sat);
}

#[test]
fn joint_seed_generated_agree_with_z3() {
    let mut rng = Lcg(61);
    let (mut sat, mut unsat, mut z3_timeouts) = (0usize, 0usize, 0usize);
    for _ in 0..N_ITERS {
        let body = gen(&mut rng);
        // shinri prints a never-constrained String as `?`, which has no
        // quoted value; query only the leaves some assertion mentions.
        // (Separately: z3's -T is wall-clock, so under heavy load a
        // shinri-unsat / z3-timeout failure is a possible flake; it fails
        // closed.)
        let used: Vec<&str> = NAMES
            .iter()
            .copied()
            .filter(|n| {
                body.lines()
                    .filter(|l| l.starts_with("(assert"))
                    .any(|l| l.split([' ', '(', ')']).any(|t| t == *n))
            })
            .collect();
        match check(&body, &used, 3, &mut z3_timeouts) {
            SolveOutcome::Sat => sat += 1,
            SolveOutcome::Unsat => unsat += 1,
            _ => {}
        }
    }
    eprintln!(
        "joint_seed_oracle: {sat} sat, {unsat} unsat, {} unknown, {z3_timeouts} z3 unknown/timeouts",
        N_ITERS - sat - unsat
    );
    assert!(
        sat > 0,
        "generator must reach sat: {sat} sat, {unsat} unsat"
    );
}
