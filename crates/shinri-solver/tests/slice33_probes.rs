//! Slice 33 probes (spec §7). These pin the resolver-propagation frontier.
//!
//! Written BEFORE the implementation as a measured baseline; now (Task 6) each
//! probe records what the engine does with the propagation mechanism landed,
//! after the new verdict was oracle-confirmed. Measured flips: probes E, G, AND
//! C all moved `unknown → unsat`; the control probe F held `unsat`. Spec §7
//! predicted E and G would flip and predicted C would STAY `unknown`; the
//! probe-C prediction was FALSIFIED (see `probe_c_len_zero_var` below). Every
//! pin here is confirmed by BOTH z3 and cvc5.
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

/// Probe E — PIN (slice 33). The residual `[y] = ["ab"]` now propagates
/// `y ≈ "ab"`, which contradicts the asserted `distinct`. z3 + cvc5: unsat.
#[test]
fn probe_e_empty_literal_concat() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun y () String)
           (assert (= (str.++ "" y) "ab"))(assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

/// Probe G — PIN (slice 33). The `x = ""` merge rewrites the normal form to
/// `[y]`; same propagation path as probe E. z3 + cvc5: unsat.
#[test]
fn probe_g_asserted_empty_var() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= x ""))(assert (= (str.++ x y) "ab"))
           (assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

/// Probe C — PIN (slice 33). Spec §7 PREDICTED this would STAY `unknown` (it
/// was listed as a stated non-goal needing the retracted wall-3 `len(x) = 0 →
/// x ≈ ""` grounding seam). That prediction was FALSIFIED by measurement: C
/// flips to `unsat`, and NOT via the retracted seam. Mechanism: the word
/// equation `x·y = "ab"` F-splits; the asserted `len(x) = 0` closes every
/// non-empty branch through the arith length seam; on the surviving branch the
/// residual reduces to the pure assignment `y = "ab"`, where the new
/// propagation (spec §3) fires and collides with `distinct y "ab"`. The
/// propagation itself only ever fired on the designed constant-word residual
/// shape — the §2 scope fence held — so the REACH here is wider than §7's model
/// only because the mechanism COMPOSES with existing F-split/length branching,
/// not because it widened. The flip is a sound completeness gain: z3 + cvc5
/// both confirm `unsat`. Controller-adjudicated ACCEPTED.
#[test]
fn probe_c_len_zero_var() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.len x) 0))(assert (= (str.++ x y) "ab"))
           (assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

/// Probe F — control. The contradiction machinery is intact once the equality
/// exists. This must stay `unsat` throughout the slice.
#[test]
fn probe_f_control_direct_contradiction() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun y () String)
           (assert (= y "ab"))(assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"], "control: must never regress");
}

/// Probe H — PIN (slice 33, final review). Same-check composition of a mid-check
/// propagation merge with a LATER gated conflict channel. The first equation
/// F-splits; in the branch deciding minted `x=""` (dl 1), eq-a's residual
/// `[y]=["ab"]` propagates `y ≈ "ab"` (a merge into `cx.eq` MID-invocation — the
/// first mechanism to do so). eq-b then normalizes through that merged class to a
/// constant-head-mismatch. The merged class root is created AFTER the
/// `cond_roots` sets are built at check() entry, so without eager insertion its
/// root is in NEITHER set for the rest of the invocation, and the later gated
/// word-eq conflict path could pass a stale `side_clean` gate and learn an
/// under-cited global conflict → wrong UNSAT. z3 + cvc5: sat (x="a", y="b", w="").
#[test]
fn probe_h_same_check_composition() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (declare-fun w () String)
           (assert (= (str.++ x y) "ab"))(assert (= (str.++ y w) "b"))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
}
