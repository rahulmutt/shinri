//! Slice 58 probes (spec §7.3). A membership `t ∈ R` whose EUF class holds
//! a constant-headed concat that is not the class's normal-form
//! representative: `normal_form` never picks a concat as rep, so Rule G saw
//! `nf = [t]` and never consumed the constant. At `f515c00` the `m*` targets
//! answered `unknown fence=str-model-rejected` (`m1`/`m2` measured; see the
//! slice-58 report for `m3`/`m4`). The `g*` and `rf*` cases must stay `sat`;
//! their witnesses are checked against every assertion.
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

fn all_in(s: &str, ok: impl Fn(char) -> bool) -> bool {
    s.chars().all(ok)
}

// ── targets (spec §7.3): unsat via a class member's constant prefix ─────────

/// `regex-050-translate-rotate-fuzz.smt2`; z3: unsat. Was
/// `slice57_probes::k1_stringfuzz_translate_rotate_stays_unknown`.
#[test]
fn m1_translate_rotate() {
    assert_eq!(
        verdict(
            "(assert (= (str.len x) 3))(assert (= x y))\
             (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))(assert (str.prefixof \"\\\\\" x))"
        ),
        "unsat"
    );
}

/// `regex-050-translate-graft-translate.smt2`; z3: unsat. Was
/// `slice57_probes::k2_stringfuzz_translate_graft_stays_unknown`.
#[test]
fn m2_translate_graft() {
    assert_eq!(
        verdict(
            "(assert (= 2 (str.len x)))(assert (= x y))\
             (assert (str.in_re y (re.* (re.range \"a\" \"b\"))))(assert (str.prefixof \"1\" x))"
        ),
        "unsat"
    );
}

/// The member's prefix is only visible through its DEEP normal form
/// (`"a" ++ z`, `z = "b" ++ w` ⟹ `"ab" ++ w`).
#[test]
fn m3_deep_nf_prefix() {
    assert_eq!(
        verdict(
            "(declare-fun z () String)(declare-fun w () String)\
             (assert (= x (str.++ \"a\" z)))(assert (= z (str.++ \"b\" w)))(assert (= y x))\
             (assert (str.in_re y (re.++ (str.to_re \"ac\") re.all)))"
        ),
        "unsat"
    );
}

/// Negative polarity: `∂_a comp("a"·Σ*) = comp(Σ*) = ∅`.
#[test]
fn m4_negative_polarity() {
    assert_eq!(
        verdict(
            "(assert (= x y))(assert (str.prefixof \"a\" x))\
             (assert (not (str.in_re y (re.++ (str.to_re \"a\") re.all))))"
        ),
        "unsat"
    );
}

// ── sound-direction guards (spec §7.3) ───────────────────────────────────────

/// Non-empty derivative ⟹ no conflict.
#[test]
fn g1_compatible_prefix() {
    let x = sat_x(
        "(assert (str.prefixof \"a\" x))(assert (= x y))\
         (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))",
    );
    assert!(
        x.starts_with('a') && all_in(&x, |c| c == 'a' || c == 'b'),
        "x = {x:?}"
    );
}

/// The `"1"` branch's conflict must cite its disjunct, so the `"ab"` branch
/// survives (the E1 ce2 shape).
#[test]
fn g2_conditional_member() {
    let x = sat_x(
        "(assert (or (= x (str.++ \"1\" y)) (= x \"ab\")))\
         (assert (str.in_re x (re.* (re.range \"a\" \"b\"))))",
    );
    assert_eq!(x, "ab");
}

/// A consistent minted `"1" ++ !strk` member ⟹ no conflict.
#[test]
fn g3_minted_member_other_branch() {
    let x = sat_x(
        "(assert (= 2 (str.len x)))(assert (= x y))\
         (assert (str.in_re y (re.* (re.union (re.range \"a\" \"b\") (str.to_re \"1\")))))\
         (assert (str.prefixof \"1\" x))",
    );
    assert!(
        x.starts_with('1')
            && x.chars().count() == 2
            && all_in(&x, |c| matches!(c, 'a' | 'b' | '1')),
        "x = {x:?}"
    );
}

// ── Review Focus (plan) ──────────────────────────────────────────────────────

/// RF1: a member asserted inside a scope must not conflict after `pop`.
#[test]
fn rf1_member_popped_with_scope() {
    let out = run_script(&format!(
        "{H}(assert (= x y))(assert (str.in_re y (re.* (re.range \"a\" \"b\"))))\
         (push 1)(assert (str.prefixof \"1\" x))(check-sat)(pop 1)(check-sat)"
    ));
    assert_eq!(out, vec!["unsat".to_string(), "sat".to_string()]);
}

/// RF2: `prefixof ""` mints a concat whose NF drops `""` — nothing to consume.
#[test]
fn rf2_empty_prefix_no_conflict() {
    let x = sat_x(
        "(assert (str.prefixof \"\" x))(assert (= x y))\
         (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))",
    );
    assert!(
        !x.is_empty() && all_in(&x, |c| c == 'a' || c == 'b'),
        "x = {x:?}"
    );
}

/// RF3: code points above ASCII, inside the range ⟹ no conflict.
#[test]
fn rf3_non_ascii_prefix_in_range() {
    let x = sat_x(
        "(assert (str.prefixof \"\\u{e9}\" x))(assert (= x y))\
         (assert (str.in_re y (re.* (re.range \"\\u{e0}\" \"\\u{ff}\"))))",
    );
    assert!(
        x.starts_with('\u{e9}') && all_in(&x, |c| ('\u{e0}'..='\u{ff}').contains(&c)),
        "x = {x:?}"
    );
}

/// RF4: the membership's string side is itself a concat.
#[test]
fn rf4_concat_membership_side() {
    let x = sat_x(
        "(assert (str.prefixof \"a\" x))\
         (assert (str.in_re (str.++ x \"b\") (re.* (re.range \"a\" \"b\"))))",
    );
    assert!(
        x.starts_with('a') && all_in(&x, |c| c == 'a' || c == 'b'),
        "x = {x:?}"
    );
}
