//! Differential oracle (slice 62, spec §7.3): bare String leaves with 2–4
//! memberships each (mixed polarity), a compound length constraint (`+`,
//! scalar `*`) and optionally an Int `v`. Every decided shinri answer must
//! match z3; every shinri `sat` witness (strings and `v`), re-asserted into
//! z3, must be `sat`; a shinri `unsat` z3 cannot confirm fails.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(len_bounds_oracle)'
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

/// Copied verbatim from tests/slice62_probes.rs (minus `set-logic`).
const R11A_VARIANT: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (and (<= (+ (str.len x) (str.len y)) 3) (>= (+ (str.len x) (str.len y)) 3)))
"#;
const NORN_135: &str = r#"(declare-fun var_0 () String)
(declare-const v Int)
(assert (str.in_re var_0 (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(assert (str.in_re var_0 (re.++ (re.* (str.to_re "a")) (re.++ (str.to_re "b") (re.* (str.to_re "b"))))))
(assert (str.in_re var_0 (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
(assert (str.in_re var_0 (re.* (re.range "a" "u"))))
(assert (and (<= 0  (str.len var_0)) (= (* v 2 ) (+ (str.len var_0) 2 ))))
"#;

/// shinri's verdict on `body` and, on `sat`, the values of `strs` (quoted
/// words, in order) and of `v` when `with_v`.
fn shinri_run(body: &str, strs: &[&str], with_v: bool) -> (SolveOutcome, Vec<String>, Option<i64>) {
    let mut full = format!("(set-logic ALL)\n{body}(check-sat)\n");
    if !strs.is_empty() {
        full.push_str(&format!("(get-value ({}))\n", strs.join(" ")));
    }
    if with_v {
        full.push_str("(get-value (v))\n");
    }
    let mut solver = Solver::new();
    let mut parser = Parser::new(&full);
    let mut outcome = SolveOutcome::Unknown;
    let mut values: Vec<Vec<String>> = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            CommandResponse::Values(s) => values.push(vec![s]),
            _ => {}
        }
    }
    let mut words = Vec::new();
    let mut v = None;
    let mut it = values.into_iter().map(|mut x| x.remove(0));
    if outcome == SolveOutcome::Sat && !strs.is_empty() {
        let s = it.next().expect("string get-value");
        words = s
            .split('"')
            .skip(1)
            .step_by(2)
            .map(str::to_string)
            .collect();
    }
    if outcome == SolveOutcome::Sat && with_v {
        let s = it.next().expect("v get-value");
        let t = s.replace(['(', ')'], " ");
        let toks: Vec<&str> = t.split_whitespace().collect();
        // ((v k)) or ((v (- k)))
        v = Some(match toks.as_slice() {
            ["v", "-", k] => -k.parse::<i64>().expect("int"),
            ["v", k] => k.parse::<i64>().expect("int"),
            other => panic!("unexpected v value {other:?}"),
        });
    }
    (outcome, words, v)
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

/// A shinri `unsat` that z3 times out on is not failed outright: z3 4.16 and
/// cvc5 1.3.4 cannot decide e.g. `z in (ab)* and z not in [a-u]*`. Instead the
/// script is re-asked with every string length (and `v`) bounded by 12. The
/// bounded query is a falsification check, not a proof: bounded `unsat`
/// counts as confirmed (in `bounded_confirmed`), bounded `sat` is a failure.
fn check(
    body: &str,
    strs: &[&str],
    with_v: bool,
    timeout_s: u32,
    z3_timeouts: &mut usize,
    bounded_confirmed: &mut usize,
) -> SolveOutcome {
    let (ours, words, v) = shinri_run(body, strs, with_v);
    let theirs = z3_outcome(body, timeout_s);
    if matches!(theirs, easy_smt::Response::Unknown) {
        *z3_timeouts += 1;
    }
    match (ours, theirs) {
        (SolveOutcome::Sat, easy_smt::Response::Unsat) => panic!("shinri sat, z3 unsat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Sat) => panic!("shinri unsat, z3 sat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Unknown) => {
            let mut bounded = body.to_string();
            for s in strs {
                bounded.push_str(&format!("(assert (<= (str.len {s}) 12))\n"));
            }
            if with_v {
                bounded.push_str("(assert (<= v 12))\n");
            }
            match z3_outcome(&bounded, 20) {
                easy_smt::Response::Unsat => *bounded_confirmed += 1,
                easy_smt::Response::Sat => {
                    panic!("shinri unsat, z3 finds a bounded model:\n{body}")
                }
                _ => panic!(
                    "shinri unsat, z3 timed out (-T:{timeout_s}) and on the length<=12 bounded query, unconfirmed:\n{body}"
                ),
            }
        }
        _ => {}
    }
    if ours == SolveOutcome::Sat {
        assert_eq!(words.len(), strs.len(), "get-value shape:\n{body}");
        let mut pinned = body.to_string();
        for (s, w) in strs.iter().zip(&words) {
            pinned.push_str(&format!("(assert (= {s} \"{w}\"))\n"));
        }
        if let Some(k) = v {
            pinned.push_str(&format!("(assert (= v {k}))\n"));
        }
        assert!(
            matches!(z3_outcome(&pinned, 20), easy_smt::Response::Sat),
            "z3 rejects shinri's witness {words:?} v={v:?}:\n{body}"
        );
    }
    ours
}

const REGEXES: [&str; 8] = [
    "(re.* (str.to_re \"ab\"))",
    "(re.++ (re.* (str.to_re \"a\")) (str.to_re \"b\"))",
    "(re.++ (str.to_re \"a\") (re.* (str.to_re \"b\")))",
    "(re.* (re.range \"a\" \"u\"))",
    "(re.++ (re.* (str.to_re \"a\")) (str.to_re \"b\") (re.* (str.to_re \"b\")))",
    "(re.union (str.to_re \"a\") (str.to_re \"bb\") (str.to_re \"abc\"))",
    "((_ re.loop 1 3) (re.union (str.to_re \"a\") (str.to_re \"b\")))",
    "(re.+ (re.union (str.to_re \"a\") (str.to_re \"ba\")))",
];
const NAMES: [&str; 3] = ["x", "y", "z"];

/// One generated script; returns (body, string leaves used, uses v).
fn gen(rng: &mut Lcg) -> (String, Vec<&'static str>, bool) {
    let leaves = 1 + rng.below(3) as usize;
    let mut body = String::new();
    for n in &NAMES[..leaves] {
        body.push_str(&format!("(declare-fun {n} () String)\n"));
    }
    let with_v = rng.below(2) == 0;
    if with_v {
        body.push_str("(declare-const v Int)\n(assert (>= v 0))\n");
    }
    for n in &NAMES[..leaves] {
        for _ in 0..2 + rng.below(3) {
            let re = REGEXES[rng.below(REGEXES.len() as u64) as usize];
            let a = format!("(str.in_re {n} {re})");
            if rng.below(4) == 0 {
                body.push_str(&format!("(assert (not {a}))\n"));
            } else {
                body.push_str(&format!("(assert {a})\n"));
            }
        }
    }
    let lens: Vec<String> = NAMES[..leaves]
        .iter()
        .map(|n| format!("(str.len {n})"))
        .collect();
    let lhs = if lens.len() == 1 {
        lens[0].clone()
    } else {
        format!("(+ {})", lens.join(" "))
    };
    let k = rng.below(7);
    let rhs = if with_v {
        format!("(+ (* 2 v) {k})")
    } else {
        k.to_string()
    };
    match rng.below(3) {
        0 => body.push_str(&format!("(assert (= {lhs} {rhs}))\n")),
        1 => body.push_str(&format!(
            "(assert (and (<= {lhs} {rhs}) (>= {lhs} {rhs})))\n"
        )),
        _ => body.push_str(&format!("(assert (= (* 2 {lhs}) {rhs}))\n")),
    }
    (body, NAMES[..leaves].to_vec(), with_v)
}

#[test]
fn len_bounds_probes_agree_with_z3() {
    let (mut t, mut b) = (0, 0);
    assert_ne!(
        check(R11A_VARIANT, &["x", "y"], false, 20, &mut t, &mut b),
        SolveOutcome::Sat
    );
    assert_eq!(
        check(NORN_135, &["var_0"], true, 20, &mut t, &mut b),
        SolveOutcome::Sat
    );
}

#[test]
fn len_bounds_generated_agree_with_z3() {
    let mut rng = Lcg(62);
    let (mut sat, mut unsat, mut z3_timeouts, mut bounded) = (0usize, 0usize, 0usize, 0usize);
    for _ in 0..N_ITERS {
        let (body, strs, with_v) = gen(&mut rng);
        match check(&body, &strs, with_v, 3, &mut z3_timeouts, &mut bounded) {
            SolveOutcome::Sat => sat += 1,
            SolveOutcome::Unsat => unsat += 1,
            _ => {}
        }
    }
    eprintln!(
        "len_bounds_oracle: {sat} sat, {unsat} unsat, {} unknown, {z3_timeouts} z3 unknown/timeouts, {bounded} bounded-confirmed unsat",
        N_ITERS - sat - unsat
    );
    assert!(
        sat > 0,
        "generator must reach sat: {sat} sat, {unsat} unsat"
    );
}

/// Final review (Important 1): constraints over the group lemma's own bound
/// atoms. Appended to a `gen` script: per leaf, a negated bound atom
/// (`(not (<= (str.len n) k))` / `(not (>= (str.len n) k))`) — an INPUT atom
/// equal to a bound atom, false at final check — or a disjunction over bound
/// atoms / memberships, so the search branches and the same bound is
/// re-emitted under a second guard set while it is false.
fn gen_bound_atoms(rng: &mut Lcg, body: &mut String, strs: &[&str]) {
    body.push_str("(declare-fun p () Bool)\n");
    for n in strs {
        let len = format!("(str.len {n})");
        let (k1, k2) = (rng.below(5), rng.below(5));
        let re = REGEXES[rng.below(REGEXES.len() as u64) as usize];
        match rng.below(6) {
            0 => body.push_str(&format!("(assert (not (<= {len} {k1})))\n")),
            1 => body.push_str(&format!("(assert (not (>= {len} {k1})))\n")),
            2 => body.push_str(&format!(
                "(assert (or (not (<= {len} {k1})) (not (>= {len} {k2}))))\n"
            )),
            3 => body.push_str(&format!(
                "(assert (or (str.in_re {n} {re}) (not (<= {len} {k1}))))\n"
            )),
            4 => body.push_str(&format!(
                "(assert (or p (not (>= {len} {k1}))))\n(assert (or (not p) (not (<= {len} {k2}))))\n"
            )),
            _ => {}
        }
    }
}

#[test]
fn len_bounds_bound_atoms_agree_with_z3() {
    let mut rng = Lcg(6262);
    let (mut sat, mut unsat, mut z3_timeouts, mut bounded) = (0usize, 0usize, 0usize, 0usize);
    for _ in 0..N_ITERS {
        let (mut body, strs, with_v) = gen(&mut rng);
        gen_bound_atoms(&mut rng, &mut body, &strs);
        match check(&body, &strs, with_v, 3, &mut z3_timeouts, &mut bounded) {
            SolveOutcome::Sat => sat += 1,
            SolveOutcome::Unsat => unsat += 1,
            _ => {}
        }
    }
    eprintln!(
        "len_bounds_oracle (bound atoms): {sat} sat, {unsat} unsat, {} unknown, {z3_timeouts} z3 unknown/timeouts, {bounded} bounded-confirmed unsat",
        N_ITERS - sat - unsat
    );
    assert!(
        sat > 0 && unsat > 0,
        "generator must reach both verdicts: {sat} sat, {unsat} unsat"
    );
}
