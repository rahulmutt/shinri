//! Differential oracle (slice 60, spec §7.3): `re.+` memberships over long
//! literals of pairwise non-adjacent chars, which overflowed
//! `CLASS_SPLIT_CAP` under the old all-ranges `next_classes`. Every decided
//! shinri answer must match z3, and every shinri `sat` witness, re-asserted
//! into z3, must be `sat`. Subjects are a bare variable (witness search,
//! emptiness conflict) or `(str.++ x y)` (Rule-E unfolding).
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(head_classes_oracle)'
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

/// Copied verbatim from tests/slice60_probes.rs.
const L40: &str = "!#%')+-/13579;=?ACEGIKMOQSUWY[]_acegikmo";
const REGEX_010: &str = r#"(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.+ (str.to_re "bba"))))
(assert (str.in_re x (re.+ (str.to_re "aaps]0e4_b{a"))))
(assert (str.in_re x (re.+ (str.to_re "j.3F&AXI'\x0c';7lLbg8[c_P1ou^uNIM-(' '%+}q'\x0c''\r''\t''\n'(CW/"))))
"#;

fn shared_member_body() -> String {
    format!(
        "(declare-fun x () String)\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}\"))))\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}{L40}\"))))\n\
         (assert (str.in_re x (re.* (re.range \"!\" \"~\"))))\n"
    )
}

fn len_pin_body() -> String {
    format!(
        "(declare-fun x () String)\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}\"))))\n\
         (assert (= (str.len x) 80))\n"
    )
}

/// shinri's verdict on `body` (declarations + assertions, one per line) and,
/// on `sat`, the quoted values of `vars` in order. The pool has no `"` or
/// `\`, so a value is the text between a pair of quotes.
fn shinri_run(body: &str, vars: &[&str]) -> (SolveOutcome, Vec<String>) {
    let full = format!(
        "(set-logic QF_S)\n{body}(check-sat)\n(get-value ({}))\n",
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

fn z3_outcome(body: &str) -> easy_smt::Response {
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in", "-T:3"])
        .build()
        .expect("failed to launch z3 — run `mise install`");
    ctx.set_logic("QF_S").expect("z3 set-logic failed");
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
    // z3 can time out (-T:3) on long unrelated words; that is inconclusive,
    // not a disagreement.
    match ctx.check() {
        Ok(r) => r,
        Err(e) if e.to_string().contains("timeout") => easy_smt::Response::Unknown,
        Err(e) => panic!("z3 check-sat failed: {e}\n{body}"),
    }
}

/// Checks one script. Returns shinri's verdict for the caller's tally.
fn check(body: &str, vars: &[&str]) -> SolveOutcome {
    let (ours, values) = shinri_run(body, vars);
    let theirs = z3_outcome(body);
    match (ours, theirs) {
        (SolveOutcome::Sat, easy_smt::Response::Unsat) => panic!("shinri sat, z3 unsat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Sat) => panic!("shinri unsat, z3 sat:\n{body}"),
        _ => {}
    }
    if ours == SolveOutcome::Sat {
        assert_eq!(values.len(), vars.len(), "get-value shape:\n{body}");
        let mut pinned = body.to_string();
        for (v, val) in vars.iter().zip(&values) {
            pinned.push_str(&format!("(assert (= {v} \"{val}\"))\n"));
        }
        assert!(
            matches!(z3_outcome(&pinned), easy_smt::Response::Sat),
            "z3 rejects shinri's witness {values:?}:\n{body}"
        );
    }
    ours
}

/// One generated script: k ∈ {2, 3} `re.+` memberships on `x` or on
/// `(str.++ x y)`. Half the scripts take every word as a power of one base
/// word (common member base⁶ — sat-leaning); the rest draw words
/// independently (distinct heads — unsat-leaning). A quarter of the bases
/// are the 40-char head-wide word. Optional length pin.
fn gen(rng: &mut Lcg) -> (String, Vec<&'static str>) {
    let pool: Vec<char> = L40.chars().collect();
    let word = |rng: &mut Lcg, len: u64| -> String {
        (0..len)
            .map(|_| pool[rng.below(pool.len() as u64) as usize])
            .collect()
    };
    let concat_subject = rng.below(3) == 0;
    let (subject, vars, decls) = if concat_subject {
        (
            "(str.++ x y)",
            vec!["x", "y"],
            "(declare-fun x () String)\n(declare-fun y () String)\n",
        )
    } else {
        ("x", vec!["x"], "(declare-fun x () String)\n")
    };
    let base = if rng.below(4) == 0 {
        L40.to_string()
    } else {
        let len = 1 + rng.below(12);
        word(rng, len)
    };
    let k = 2 + rng.below(2);
    let shared = rng.below(2) == 0;
    let words: Vec<String> = (0..k)
        .map(|i| {
            if shared {
                base.repeat(1 + rng.below(3) as usize)
            } else if i == 0 {
                base.clone()
            } else {
                let len = 1 + rng.below(40);
                word(rng, len)
            }
        })
        .collect();
    let mut body = decls.to_string();
    for w in &words {
        body.push_str(&format!(
            "(assert (str.in_re {subject} (re.+ (str.to_re \"{w}\"))))\n"
        ));
    }
    if rng.below(2) == 0 {
        let n = if shared {
            6 * base.chars().count() as u64
        } else {
            1 + rng.below(80)
        };
        body.push_str(&format!("(assert (= (str.len {subject}) {n}))\n"));
    }
    (body, vars)
}

#[test]
fn head_classes_probes_agree_with_z3() {
    assert_eq!(check(REGEX_010, &["x"]), SolveOutcome::Unsat);
    assert_eq!(check(&shared_member_body(), &["x"]), SolveOutcome::Sat);
    assert_eq!(check(&len_pin_body(), &["x"]), SolveOutcome::Sat);
}

#[test]
fn head_classes_generated_agree_with_z3() {
    let mut rng = Lcg(60);
    let (mut sat, mut unsat) = (0usize, 0usize);
    for _ in 0..N_ITERS {
        let (body, vars) = gen(&mut rng);
        match check(&body, &vars) {
            SolveOutcome::Sat => sat += 1,
            SolveOutcome::Unsat => unsat += 1,
            _ => {}
        }
    }
    eprintln!(
        "head_classes_oracle: {sat} sat, {unsat} unsat, {} unknown",
        N_ITERS - sat - unsat
    );
    assert!(
        sat > 0 && unsat > 0,
        "generator must exercise both verdicts: {sat} sat, {unsat} unsat"
    );
}
