//! Slice 57 probes (spec §7.3). When the word-equation search leaves a
//! string class holding several concats (an input equation's side and a
//! minted char-peel/F-split side) or a cycle through a minted concat, the
//! default model builder picked the wrong concat and the gate rejected the
//! model (`unknown fence=str-model-rejected`). At `46d5fd9` the `len =`
//! cases below answered `unknown`; the slice-53 base binary answered the `len`
//! cases `sat`. A model produced by the reconciliation rebuild must pass the
//! strict gate: `strict_gate_confirms_lowered_str_lt` is confirmed (lowering
//! makes `str.<` against a constant gate-evaluable), while
//! `strict_gate_keeps_unevaluable_unknown` (compound arithmetic the gate
//! cannot evaluate) stays `unknown`.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn run_script(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

const H: &str = "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)";

/// The `check-sat` verdict of `body` and the solver's fence tag after it.
fn verdict_and_fence(body: &str) -> (String, Option<&'static str>) {
    let mut solver = Solver::new();
    let src = format!("{H}{body}(check-sat)");
    let mut parser = Parser::new(&src);
    let mut verdict = String::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match solver.execute(result.expect("probe parses")) {
            CommandResponse::Sat => verdict = "sat".into(),
            CommandResponse::Unsat => verdict = "unsat".into(),
            CommandResponse::Unknown => verdict = "unknown".into(),
            _ => {}
        }
    }
    (verdict, solver.last_fence())
}

fn verdict(body: &str) -> String {
    run_script(&format!("{H}{body}(check-sat)"))
        .first()
        .cloned()
        .unwrap_or_default()
}

/// Decode the first SMT-LIB 2.6 string literal in `resp` (`""` and `\u{..}`).
fn decode(resp: &str) -> String {
    let start = resp.find('"').expect("a string literal");
    let cs: Vec<char> = resp[start + 1..].chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < cs.len() {
        match cs[i] {
            '"' if cs.get(i + 1) == Some(&'"') => {
                out.push('"');
                i += 2;
            }
            '"' => break,
            '\\' if cs.get(i + 1) == Some(&'u') && cs.get(i + 2) == Some(&'{') => {
                let close = i + cs[i..]
                    .iter()
                    .position(|&c| c == '}')
                    .expect("closing brace");
                let hex: String = cs[i + 3..close].iter().collect();
                let code = u32::from_str_radix(&hex, 16).expect("hex escape");
                out.push(char::from_u32(code).expect("valid code point"));
                i = close + 1;
            }
            c => {
                out.push(c);
                i += 1;
            }
        }
    }
    out
}

/// `body` must be `sat`; returns the model value of `x`.
fn sat_x(body: &str) -> String {
    let out = run_script(&format!("{H}{body}(check-sat)(get-value (x))"));
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{H}{body}");
    decode(&out[1])
}

// ── spec §1.1: the slice-53 regressions ─────────────────────────────────────

#[test]
fn p1_len_eq_prefix_cd() {
    let x = sat_x("(assert (= (str.len x) 3))(assert (str.prefixof \"cd\" x))");
    assert!(x.starts_with("cd") && x.chars().count() == 3, "x = {x:?}");
}

#[test]
fn p1_len_bounds_prefix_cd() {
    let x = sat_x(
        "(assert (>= (str.len x) 3))(assert (<= (str.len x) 3))(assert (str.prefixof \"cd\" x))",
    );
    assert!(x.starts_with("cd") && x.chars().count() == 3, "x = {x:?}");
}

/// `"\\"` is two backslashes in SMT-LIB 2.6 (Review Focus 3).
#[test]
fn p2_len_eq_prefix_backslashes() {
    let x = sat_x("(assert (= (str.len x) 3))(assert (str.prefixof \"\\\\\" x))");
    assert!(x.starts_with("\\\\") && x.chars().count() == 3, "x = {x:?}");
}

#[test]
fn p2_len_bounds_prefix_backslashes() {
    let x = sat_x(
        "(assert (>= (str.len x) 3))(assert (<= (str.len x) 3))(assert (str.prefixof \"\\\\\" x))",
    );
    assert!(x.starts_with("\\\\") && x.chars().count() == 3, "x = {x:?}");
}

#[test]
fn p3_len_eq_suffix_c() {
    let x = sat_x("(assert (= (str.len x) 3))(assert (str.suffixof \"c\" x))");
    assert!(x.ends_with('c') && x.chars().count() == 3, "x = {x:?}");
}

#[test]
fn p3_len_bounds_suffix_c() {
    let x = sat_x(
        "(assert (>= (str.len x) 3))(assert (<= (str.len x) 3))(assert (str.suffixof \"c\" x))",
    );
    assert!(x.ends_with('c') && x.chars().count() == 3, "x = {x:?}");
}

/// `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-multiply-reverse-fuzz.smt2`,
/// assertions inlined. z3: sat.
#[test]
fn p4_stringfuzz_multiply_reverse() {
    let x = sat_x(
        "(assert (= (str.len x) 5))(assert (= x y))\
         (assert (str.in_re y (re.* (re.range \"!\" \"`\"))))(assert (str.prefixof \"1\" x))",
    );
    assert!(x.starts_with('1') && x.chars().count() == 5, "x = {x:?}");
    assert!(x.chars().all(|c| ('!'..='`').contains(&c)), "x = {x:?}");
}

// ── unsat siblings: the rebuild must not over-accept ────────────────────────

#[test]
fn u1_prefix_longer_than_len_unsat() {
    assert_eq!(
        verdict("(assert (= (str.len x) 1))(assert (str.prefixof \"cd\" x))"),
        "unsat"
    );
}

#[test]
fn u2_suffix_with_zero_len_unsat() {
    assert_eq!(
        verdict("(assert (= (str.len x) 0))(assert (str.suffixof \"c\" x))"),
        "unsat"
    );
}

// ── known-unknown pins (queued engine-side reconciliation, spec §9 item 1) ──

/// `regex-050-translate-rotate-fuzz.smt2`; z3: unsat. Needs the engine to
/// derive the conflict between `x`'s constant prefix and the membership
/// (spec §9 item 1); the model-side rebuild cannot produce `unsat`.
#[test]
fn k1_stringfuzz_translate_rotate_stays_unknown() {
    assert_eq!(
        verdict(
            "(assert (= (str.len x) 3))(assert (= x y))\
             (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))(assert (str.prefixof \"\\\\\" x))"
        ),
        "unknown",
        "queued: engine-side reconciliation (slice-57 spec §9 item 1)"
    );
}

/// `regex-050-translate-graft-translate.smt2`; z3: unsat. Same queue item.
#[test]
fn k2_stringfuzz_translate_graft_stays_unknown() {
    assert_eq!(
        verdict(
            "(assert (= 2 (str.len x)))(assert (= x y))\
             (assert (str.in_re y (re.* (re.range \"a\" \"b\"))))(assert (str.prefixof \"1\" x))"
        ),
        "unknown",
        "queued: engine-side reconciliation (slice-57 spec §9 item 1)"
    );
}

// ── strict gate (spec §4.3, Review Focus 5) ─────────────────────────────────

/// The default build is rejected, so the rebuild runs and the strict gate
/// applies. Lowering turns `str.<` against a constant into atoms the gate can
/// evaluate, so the strict gate confirms the rebuilt model (z3: sat).
#[test]
fn strict_gate_confirms_lowered_str_lt() {
    let x = sat_x(
        "(assert (= (str.len x) 3))(assert (str.prefixof \"cd\" x))(assert (str.< x \"zzz\"))",
    );
    assert!(x.starts_with("cd") && x.chars().count() == 3, "x = {x:?}");
    assert!(x.as_str() < "zzz", "x = {x:?}");
}

/// The rebuild runs (as above), but the gate cannot evaluate the compound
/// arithmetic `(- (str.len x) (str.len y))`. Under the strict gate the
/// rebuilt model is not confirmed, so the answer stays `unknown` (z3: sat).
/// With the gate forced non-strict this script answers `sat`, so the strict
/// gate is what keeps it `unknown`.
#[test]
fn strict_gate_keeps_unevaluable_unknown() {
    let (v, fence) = verdict_and_fence(
        "(assert (= (str.len x) 3))(assert (str.prefixof \"cd\" x))\
         (assert (<= (- (str.len x) (str.len y)) 1))",
    );
    assert_eq!(v, "unknown");
    assert_eq!(fence, Some("str-model-rejected"));
}

// ── Review Focus ────────────────────────────────────────────────────────────

/// Review Focus 1: a decided input disjunct; `sat` today, must stay `sat`.
#[test]
fn rf1_input_disjunction_stays_sat() {
    let x = sat_x(
        "(assert (or (= x \"ab\") (= x \"cd\")))(assert (= (str.len x) 2))\
         (assert (str.prefixof \"c\" x))",
    );
    assert_eq!(x, "cd");
}

/// Review Focus 2: the strict flag belongs to one model build only.
#[test]
fn rf2_strict_flag_does_not_leak_across_checks() {
    // The second query's compound arithmetic is gate-unevaluable, and its
    // default model passes the 3-valued gate: a leaked strict flag would
    // reject it (`unknown`).
    let out = run_script(&format!(
        "{H}(push 1)(assert (= (str.len x) 3))(assert (str.prefixof \"cd\" x))(check-sat)(pop 1)\
         (push 1)(assert (= (str.len x) 1))(assert (<= (- (str.len x) (str.len y)) 1))\
         (check-sat)(pop 1)"
    ));
    assert_eq!(out, vec!["sat".to_string(), "sat".to_string()]);
}

/// Review Focus 4: zero-length class; `sat` today, must stay `sat`.
#[test]
fn rf4_zero_length_class_stays_sat() {
    let x = sat_x("(assert (= x (str.++ y \"\")))(assert (= (str.len x) 0))");
    assert_eq!(x, "");
}
