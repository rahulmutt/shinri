//! End-to-end: SMT-LIB text -> parser -> solver, command-incremental streaming.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

/// The driver loop (the seam a future shinri-cli will own). Streams: parse one
/// command, execute it, collect any output line.
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

#[test]
fn qf_uf_unsat() {
    let out = run_script(
        "(set-logic QF_UF)\
         (declare-sort U 0)\
         (declare-fun a () U)\
         (declare-fun b () U)\
         (declare-fun f (U) U)\
         (assert (= a b))\
         (assert (distinct (f a) (f b)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn qf_lra_sat_and_unsat() {
    let sat = run_script(
        "(set-logic QF_LRA)(declare-fun x () Real)(assert (< x 1.0))(assert (> x 0.0))(check-sat)",
    );
    assert_eq!(sat, vec!["sat"]);
    let unsat = run_script(
        "(set-logic QF_LRA)(declare-fun x () Real)(assert (< x 0.0))(assert (> x 0.0))(check-sat)",
    );
    assert_eq!(unsat, vec!["unsat"]);
}

#[test]
fn qf_uflra_combination() {
    // f : Real -> Real, x = y => f(x) = f(y), with x = y forced by arithmetic.
    let out = run_script(
        "(set-logic QF_UFLRA)\
         (declare-fun x () Real)(declare-fun y () Real)(declare-fun f (Real) Real)\
         (assert (= x y))(assert (distinct (f x) (f y)))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn streaming_incremental_push_pop() {
    // check-sat solves at each point against assertions so far.
    let out = run_script(
        "(declare-fun x () Real)\
         (assert (> x 0.0))(check-sat)\
         (push 1)(assert (< x 0.0))(check-sat)(pop 1)\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat", "unsat", "sat"]);
}

#[test]
fn error_recovers_and_continues() {
    let out = run_script(
        "(declare-fun p () Bool)\
         (assert (+ p 1))\
         (assert p)(check-sat)",
    );
    // First assert errors (Bool + Int), second assert + check-sat still run.
    assert_eq!(out.len(), 2);
    assert!(out[0].starts_with("(error"));
    assert_eq!(out[1], "sat");
}

#[test]
fn int_arithmetic_is_now_decided() {
    // Pure QF_LIA is now decided end-to-end (Task 7 flip).
    // n > 0 ∧ n < 1 has no integer solution → unsat.
    let unsat = run_script("(declare-fun n () Int)(assert (> n 0))(assert (< n 1))(check-sat)");
    assert_eq!(unsat, vec!["unsat"]);
    // n > 0 is satisfiable over Int (e.g. n=1) → sat.
    let sat = run_script("(declare-fun n () Int)(assert (> n 0))(check-sat)");
    assert_eq!(sat, vec!["sat"]);
}

// ─────────────────────────────────────────────────────────────────────────────
// Slice 5 final review — Finding 1 (soundness): a user declaration that names a
// word_norm-minted internal symbol (`ite!<n>`) must be REJECTED, not silently
// aliased. Without the guard the user's nullary app hash-conses to the internal
// ite var and inherits its definition, yielding a wrong UNSAT (shinri unsat vs
// z3 sat). The mint happens during the first check-sat; the collision only
// arises when the user declares the name AFTERWARDS.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn post_mint_declaration_of_internal_name_is_rejected() {
    // First check-sat mints ite!0 for (ite c x y). The user then declares ite!0.
    // Pre-fix: shinri answered `sat` then `unsat` (wrong — z3: sat, sat), because
    // (distinct ite!0 x) aliased the internal ite var. Post-fix: the declaration
    // is rejected, the aliased use is an undeclared-symbol error, and the second
    // check-sat is `sat` (matching z3). No wrong UNSAT anywhere.
    let out = run_script(
        "(declare-const c Bool)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert (= (ite c x y) x))\
         (check-sat)\
         (declare-const ite!0 (_ BitVec 8))\
         (assert (= x y))\
         (assert (distinct ite!0 x))\
         (check-sat)",
    );
    assert_eq!(
        out.len(),
        4,
        "sat / declare-error / aliased-use-error / sat"
    );
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("reserved for solver-internal use"),
        "declaration of the minted name must be rejected, got {:?}",
        out[1]
    );
    assert!(
        out[2].starts_with("(error"),
        "aliased use is undeclared, got {:?}",
        out[2]
    );
    assert_eq!(out[3], "sat", "must NOT be a wrong unsat");
    assert!(
        !out.contains(&"unsat".to_string()),
        "no wrong UNSAT anywhere"
    );
}

#[test]
fn user_ite_name_declared_before_any_mint_still_works() {
    // A user who declares `ite!7` BEFORE it is ever minted keeps a usable free
    // constant: word_norm's mint-time probe skips the taken name and never
    // reserves it. This must remain SAT (matches z3) — the guard must not
    // regress legitimate scripts.
    let out = run_script(
        "(declare-const ite!7 (_ BitVec 8))\
         (declare-const c Bool)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert (= (ite c x y) x))\
         (assert (distinct ite!7 x))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

// ─────────────────────────────────────────────────────────────────────────────
// Slice 5 final review — Finding 2 (test gap): ABV × word-level BV-sorted ite.
// The slice changed the ABV path for a BV-sorted `ite` from panic to a correct,
// sound verdict, previously with zero coverage. Scripts below were cross-checked
// against z3 4.16.0 on PATH.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn abv_select_over_bv_ite_decided_unsat() {
    // (select a (ite (bvult u v) x y)): the condition atom is pinned TRUE, so the
    // ite resolves to x; (select a x)=0x2a is contradicted by the distinct on the
    // ite-indexed select → UNSAT. Cross-checked: z3 → unsat.
    let out = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const u (_ BitVec 8))(declare-const v (_ BitVec 8))\
         (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert (bvult u v))\
         (assert (= (select a x) #x2a))\
         (assert (distinct (select a (ite (bvult u v) x y)) #x2a))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn abv_select_over_bv_ite_decided_sat_twin() {
    // SAT twin of the above: the condition atom is pinned FALSE, so the ite
    // resolves to y; with x != y the (select a x)=0x2a constraint no longer
    // touches the ite-indexed select → SAT. Cross-checked: z3 → sat.
    let out = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const u (_ BitVec 8))(declare-const v (_ BitVec 8))\
         (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert (not (bvult u v)))\
         (assert (distinct x y))\
         (assert (= (select a x) #x2a))\
         (assert (distinct (select a (ite (bvult u v) x y)) #x2a))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn abv_select_over_bare_bool_ite_decided_sat() {
    // Slice 6: the bare-Bool fence exemption (fp_stage/bv_stage) is now
    // ported to the ABV path too — a bare Bool ite condition decides instead
    // of fencing. Was pinned sound-Unknown from slice 5 until the port.
    // Cross-checked: z3 → sat.
    let out = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const p Bool)\
         (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert (= (select a (ite p x y)) #x2a))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn abv_select_over_bare_bool_ite_decided_unsat_twin() {
    // Condition pinned TRUE → ite resolves to x, but (select a x) is forced
    // to two different values → UNSAT. Cross-checked: z3 → unsat.
    let out = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const p Bool)\
         (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert p)\
         (assert (= (select a x) #x00))\
         (assert (= (select a (ite p x y)) #x2a))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

// ── Slice 6: n-ary `=` over the sorts word_norm previously skipped ──────────
// Wrong-SAT before slice 6: tseitin encoded Bool (= p q r) as p↔q (operands
// 3+ dropped); EUF new_var registered only kids[0],kids[1]. z3-diffed in the
// slice-5 final review and re-confirmed in the slice-6 pre-flight.

#[test]
fn bool_nary_eq_third_operand_not_dropped_unsat() {
    // (= p q r) ∧ p ∧ q ∧ ¬r — answered sat before slice 6. z3: unsat.
    let out = run_script(
        "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)\
         (assert (= p q r))(assert p)(assert q)(assert (not r))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn bool_nary_eq_sat_twin() {
    let out = run_script(
        "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)\
         (assert (= p q r))(assert p)(check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn uf_nary_eq_transitivity_unsat() {
    // (= a b d) ∧ (distinct a d) over sort U — answered sat before slice 6.
    let out = run_script(
        "(declare-sort U 0)\
         (declare-const a U)(declare-const b U)(declare-const d U)\
         (assert (= a b d))(assert (distinct a d))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn uf_nary_eq_sat_twin() {
    let out = run_script(
        "(declare-sort U 0)\
         (declare-const a U)(declare-const b U)(declare-const d U)\
         (assert (= a b d))(check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn string_nary_eq_transitivity_unsat() {
    // Post-expansion this is two binary String equalities + a binary distinct
    // — the QF_S core's native shape. z3: unsat (pre-flight, Task 1).
    // Pre-fix behavior: debug-build panic (euf/solver.rs:114 "Eq atom must be binary")
    // or release-build wrong-sat.
    let out = run_script(
        "(declare-const s1 String)(declare-const s2 String)(declare-const s3 String)\
         (assert (= s1 s2 s3))(assert (distinct s1 s3))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn array_nary_eq_transitivity_decided_unsat() {
    // Arrays over BV route to the ABV path, whose own normalize pass already
    // handled n-ary array = correctly; post-slice-6, word_norm pre-expands
    // instead. Either way the verdict stays DECIDED (z3-diffed: unsat).
    let out = run_script(
        "(declare-const a1 (Array (_ BitVec 4) (_ BitVec 4)))\
         (declare-const a2 (Array (_ BitVec 4) (_ BitVec 4)))\
         (declare-const a3 (Array (_ BitVec 4) (_ BitVec 4)))\
         (assert (= a1 a2 a3))(assert (distinct a1 a3))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn array_nary_eq_operand_three_not_dropped_unsat() {
    // (= a1 a2 a3) ∧ (distinct a2 a3): dropping operand 3 would answer sat.
    let out = run_script(
        "(declare-const a1 (Array (_ BitVec 4) (_ BitVec 4)))\
         (declare-const a2 (Array (_ BitVec 4) (_ BitVec 4)))\
         (declare-const a3 (Array (_ BitVec 4) (_ BitVec 4)))\
         (assert (= a1 a2 a3))(assert (distinct a2 a3))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn nullary_define_fun_bare_symbol_solves() {
    // Slice 6: bare `one` expands to the macro body end-to-end.
    let out = run_script(
        "(define-fun one () Int 1)(declare-const y Int)\
         (assert (= y one))(assert (= y 2))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn string_nary_eq_compound_and_wrapper_not_wrong_sat() {
    // C1 (slice 6): word_norm expands n-ary String = into (and (= a b) (= b c)),
    // which the string self-check used to skip (it only walked top-level atoms),
    // letting a spurious model slip through as SAT. z3 says UNSAT; the fixed
    // self-check now descends the positive And chain and downgrades to a SOUND
    // `unknown` (it must NOT answer sat).
    let out = run_script(
        "(declare-const s1 String)(declare-const s3 String)\
         (assert (= (str.++ s3 \"a\") (str.++ s1 \"b\") (str.++ s3 \"b\")))(check-sat)",
    );
    assert_ne!(
        out,
        vec!["sat"],
        "C1 soundness: string n-ary = must not be SAT"
    );
    assert_eq!(out, vec!["unknown"]);

    // Binary-written twin: the same constraint split into two top-level binary
    // equalities. Each is a bare top-level atom the self-check already caught;
    // it must reach the same non-SAT verdict (z3: unsat).
    let twin = run_script(
        "(declare-const s1 String)(declare-const s3 String)\
         (assert (= (str.++ s3 \"a\") (str.++ s1 \"b\")))\
         (assert (= (str.++ s1 \"b\") (str.++ s3 \"b\")))(check-sat)",
    );
    assert_ne!(
        twin,
        vec!["sat"],
        "C1 soundness: binary twin must not be SAT"
    );
    assert_eq!(twin, vec!["unknown"]);
}

#[test]
fn abv_ite_true_bool_const_not_wrong_sat() {
    // I4 (pre-existing): the ABV skeleton encoder used to map Bool CONSTANTS to
    // free proxy vars, so `(ite true …)` could pick the else branch → wrong SAT.
    // z3: unsat. Fixed encoder pins the constant, so both repros are UNSAT.
    let ite_true = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert (ite true (= (select a x) #x01) (= (select a x) #x02)))\
         (assert (= (select a x) #x02))(check-sat)",
    );
    assert_eq!(ite_true, vec!["unsat"]);

    let or_false = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const x (_ BitVec 8))\
         (assert (or false (= (select a x) #x01)))\
         (assert (= (select a x) #x02))(check-sat)",
    );
    assert_eq!(or_false, vec!["unsat"]);
}

#[test]
fn abv_bare_bool_plus_uninterpreted_predicate_fences_unknown() {
    // M1 / Task-5 over-admission pin (a): a bare Bool and an uninterpreted
    // predicate alongside an array-over-BV constraint fall outside ABV's admitted
    // fragment. Both today fence to `unknown` (z3: sat — a sound fence, never
    // wrong-SAT). Pins the fence so a future admission is a deliberate change.
    let out = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const p Bool)(declare-fun P ((_ BitVec 8)) Bool)\
         (declare-const x (_ BitVec 8))\
         (assert p)(assert (P x))(assert (= (select a x) #x2a))(check-sat)",
    );
    assert_eq!(out, vec!["unknown"]);
}

#[test]
fn abv_bare_bool_plus_arith_fences_unknown() {
    // M1 / Task-5 over-admission pin (b): a bare Bool plus integer arithmetic
    // alongside an array-over-BV constraint. Fences to `unknown` (z3: sat — sound
    // fence).
    let out = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const p Bool)(declare-const i Int)\
         (declare-const x (_ BitVec 8))\
         (assert (= (select a (ite p x x)) #x2a))(assert (< i 3))(check-sat)",
    );
    assert_eq!(out, vec!["unknown"]);
}

// ── Slice 12: string predicates ──────────────────────────────────────────────

#[test]
fn str_predicate_literal_folds_decide_any_polarity() {
    // Literal-literal predicates constant-fold at ANY polarity — including
    // under (not …) — so no fence applies and the query decides.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (not (str.contains "abc" "d")))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
    let out = run_script(r#"(set-logic QF_S)(assert (str.prefixof "b" "abc"))(check-sat)"#);
    assert_eq!(out, vec!["unsat"]);
    let out = run_script(r#"(set-logic QF_S)(assert (str.suffixof "bc" "abc"))(check-sat)"#);
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn str_input_var_concat_length_decides() {
    // Task 7.5 regression: the predicate-free root shape. An input `var = concat`
    // equality now emits the guarded length link `len(s) = len("ab"++k)`, so
    // `len(s) = 2 + len(k) >= 2` contradicts the asserted `len(s) = 1` → UNSAT
    // (z3: unsat). Before Task 7.5 this was a wrong `sat` (len(s) floated free in
    // arith and the var-headed word equation solved trivially).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)(declare-fun k () String)
           (assert (= s (str.++ "ab" k)))(assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // Concat on the LEFT side decides identically (order-independent link).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)(declare-fun k () String)
           (assert (= (str.++ "ab" k) s))(assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // No-spurious-UNSAT control: `len(s) = 3` is satisfiable (witness
    // s = "ab" ++ any 1-char k). The new length link must NOT over-constrain it
    // to UNSAT. The engine returns a SOUND `unknown` here (the var-headed word
    // equation's witness synthesis is a pre-existing incompleteness, unrelated to
    // this fix) — the load-bearing assertion is simply that it is NOT `unsat`.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)(declare-fun k () String)
           (assert (= s (str.++ "ab" k)))(assert (= (str.len s) 3))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
    assert_ne!(
        out,
        vec!["unsat"],
        "must not over-constrain to spurious UNSAT"
    );
}

#[test]
fn str_prefixof_positive_decides() {
    // LENGTH-based UNSAT pin (restored by Task 7.5): `str.prefixof "ab" s`
    // rewrites to `s = "ab" ++ !pfx{n}`, so `len(s) = 2 + len(!pfx{n}) >= 2`;
    // asserting `len(s) = 1` is UNSAT. Task 7 had to REPLACE this with a
    // direct-equality pin because the input `var = concat` equality got no
    // length link (`len(s)` floated free in arith, the var-headed word equation
    // solved trivially → wrong `sat`). Task 7.5's guarded input-concat length
    // link (`len(s) = len("ab"++!pfx{n})`) feeds the length-defining fixpoint and
    // restores the sound UNSAT. Reproduced originally with a hand-written
    // `(= s (str.++ "ab" k))` + `(= (str.len s) 1)` query (no predicates pass),
    // now also decided UNSAT — pinned as `str_input_var_concat_length_decides`.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof "ab" s))(assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // Direct-equality UNSAT pin (Task 7, KEPT as an additional case): `s` can't
    // be `"a"` if it must start with the 2-character prefix `"ab"`.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof "ab" s))(assert (= s "a"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // len(s) = 2 forces s = "ab" exactly. (Verified: this exact brief shape
    // already decides correctly — unaffected by the note-(b) gap above.)
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof "ab" s))(assert (= (str.len s) 2))
           (check-sat)(get-value (s))"#,
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"));
    assert!(
        out.get(1).is_some_and(|v| v.contains("\"ab\"")),
        "s must be \"ab\", got {out:?}"
    );
}

#[test]
fn str_suffixof_and_contains_positive_decide() {
    // LENGTH-based UNSAT pins (restored by Task 7.5, same root cause and fix as
    // `str_prefixof_positive_decides`): `str.suffixof "ab" s` rewrites to
    // `s = !sfx{n} ++ "ab"` and `str.contains s "ab"` to `s = !ctnl ++ "ab" ++
    // !ctnr` — both force `len(s) >= 2`, so `len(s) = 1` is UNSAT once the input
    // `var = concat` length link is emitted.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.suffixof "ab" s))(assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.contains s "ab"))(assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // Direct-equality UNSAT pins (Task 7, KEPT as additional cases).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.suffixof "ab" s))(assert (= s "b"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.contains s "ab"))(assert (= s "a"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // Flip-marker (Task 7 pinned `unknown`; Task 7.5 FLIPPED it to `sat`):
    // `str.contains s "b"` is the THREE-way concat `s = kl ++ "b" ++ kr`, and
    // with `len(s) = 2` the query is SAT (witness e.g. s = "bb"). Task 7 could
    // only observe `unknown` because the 3-way concat never linked its length;
    // Task 7.5's input-concat length link now lets arith find `len(kl)+1+len(kr)
    // = 2` with a concrete solution, so the engine decides the (correct) `sat`.
    // A strict improvement (unknown → sound decision), not a wrong-SAT: z3 agrees.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.contains s "b"))(assert (= (str.len s) 2))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn str_predicate_with_foldable_substr_decides() {
    // Predicate rewrite runs BEFORE the substr desugar; the constant substr
    // folds to "ab" inside the emitted equation (combined fresh-var minters).
    //
    // The fold produces `str.prefixof "ab" s`, i.e. `s = "ab" ++ !pfx{n}`.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof (str.substr "abc" 0 2) s))
           (assert (= s "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
    // LENGTH-based UNSAT pin (restored by Task 7.5): the folded 2-char prefix
    // forces `len(s) >= 2`, contradicting `len(s) = 1`. This exercises the
    // fold-then-rewrite ordering AND the input-concat length link together.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof (str.substr "abc" 0 2) s))
           (assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // Direct-equality UNSAT pin (Task 7, KEPT as an additional case).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof (str.substr "abc" 0 2) s))
           (assert (= s "a"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

// ── Fence canaries: flip-markers for a future negative-polarity slice ────────

#[test]
fn str_predicate_negative_polarity_fences_unknown() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (not (str.contains s "a")))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}

#[test]
fn str_predicate_under_ite_condition_fences_unknown() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)(declare-fun t () String)
           (assert (= t (ite (str.prefixof "a" s) "x" "y")))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}

#[test]
fn str_predicate_mixed_polarity_fences_unknown() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)(declare-fun b () Bool)
           (assert (or (str.contains s "a") b))
           (assert (or (not (str.contains s "a")) (not b)))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}

#[test]
fn str_predicate_over_uf_fences_unknown() {
    // Upstream string_stage fence condition 1 (String under non-nullary UF)
    // catches this BEFORE the predicate pass — unchanged behavior, pinned.
    let out = run_script(
        r#"(declare-fun s () String)(declare-fun g (String) String)
           (assert (str.prefixof (g s) s))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}
