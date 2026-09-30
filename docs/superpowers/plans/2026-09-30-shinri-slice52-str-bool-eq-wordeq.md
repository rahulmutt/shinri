# Slice 52 — Strings: Bool `=` in the model gate, word-equation holes H1/H3 — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the two Noetzli rows (`str-pred-small-rw_370`, `_458`, the last `wrong` rows in QF_S + QF_SLIA) answer `unsat`, and close the model-gate hole that let their bogus model through.

**Architecture:**
- **Model gate (post-solve self-check).** It learns to evaluate Bool-sorted `=`/`distinct`. This is the sound backstop.
- **Word-equation resolver, H1.** A residual of the form `[] = [v1..vn]` now propagates `vi ≈ ""`.
- **E1 gate on word-equation resolution, H3.** A new, narrowly scoped contributor map lets the gate stop blocking an equation because of its own conditional literal, or because of conditional disequalities.

H3 is the risky change. It carries an agreed fallback (drop it) if the oracle, the fuzzer or the bench shows any wrong answer.

**Tech Stack:** Rust 1.98.1 (mise), cargo-nextest 0.9.140, z3 4.16.0 (mise, oracle only).

**Spec:** `docs/superpowers/specs/2026-09-30-shinri-slice52-str-bool-eq-wordeq-design.md`

## Global Constraints

- Branch: `slice52-str-bool-eq-wordeq` off `main`; PR to `main`, merge commit when CI is green, then delete the branch (remote and local).
- Run `cargo fmt --all` before every commit; `cargo clippy --workspace --all-targets -- -D warnings` must be clean (`mise run lint` covers both).
- nextest filters use the expression form `-E 'test(<name>)'`, or `-E 'binary(<name>)'` for a whole integration-test binary. Always confirm the discovered test count is non-zero.
- Oracle tests only run with `--features oracle`; without it they run 0 tests, and that is never reported as coverage.
- Any test measured over 5 min is `#[ignore = "exhaustive: nightly tier (~N min in CI)"]`d, with a fast smoke companion.
- No change to: the SAT step budget (`2_000_000`), `STRING_PATH_BRANCH_BUDGET`, `STRING_PATH_PIVOT_BUDGET`, `all_cond_roots`, `input_cond_roots`, Tseitin, the char-peel, F-split and single-atom `Propagate` paths, or `prefix_of_constant_is_done_not_conflict`.
- Pure-Rust mandate: no new dependencies.
- **Fallback (agreed):** if Task 5 finds a wrong `unsat`, or Task 6 shows any `* → wrong` row that Task 4 caused, revert Task 4's commit, keep Tasks 1–3, and re-pin the Noetzli probes to "not `sat`". The rows then end as `unknown:str-model-rejected`, and H3 is queued with the evidence.

## Review Focus

1. **A genuine `sat` whose Bool `=` the gate can now evaluate** must stay `sat`. The gate reads more shapes now, so a model that was never checked is checked. Pinned by `ctrl_iff_true` in Task 1, re-run after Task 2.
2. **An uninterpreted Bool constant (`p`) under Bool `=`** is still unevaluable by the gate (the audit is queued). `bool_proxy` must be `unsat` after Task 4, and is expected to stay `sat` between Tasks 2 and 4. Task 2 records this, and Task 4 turns it green.
3. **A residual with a repeated variable, `[] = [x, x]`,** must propagate `x ≈ ""` once, then stop, with no loop. Unit test added in Task 3.
4. **Contributors must survive an intra-check merge.** After a propagation merge unions two classes, a second conditional equation on either one must still block. Unit test `on_merge_carries_contributors` in Task 4.
5. **A `distinct` atom asserted false** (`¬distinct ≡ =`, stored in `eq_true`) must get the same own-literal exemption as an `=` atom. Probe `not_distinct_form` in Task 1.

---

### Task 0: Branch

- [ ] **Step 1: Create the slice branch**

```bash
cd /workspace && git checkout main && git pull --ff-only && git checkout -b slice52-str-bool-eq-wordeq
```

---

### Task 1: Red pins — `slice52_probes.rs`

**Files:**
- Create: `crates/shinri-solver/tests/slice52_probes.rs`

**Interfaces:**
- Consumes: `shinri_parser::Parser`, `shinri_solver::{CommandResponse, Solver}` (same as `slice34_probes.rs`).
- Produces: the named probes from spec §8, plus `not_distinct_form` and `ctrl_repeated_var`. Later tasks re-run them with `-E 'binary(slice52_probes)'`.

- [ ] **Step 1: Write the probe file**

```rust
//! Slice 52 probes (spec §8). They pin the Noetzli wrong-`sat` pair and its
//! reduced reproducers.
//!
//! Written BEFORE the implementation. On `main` (`7bd2279`) every `unsat` pin
//! fails: `sat` for the Bool-`=`/`distinct`/proxy forms, and `unknown`
//! (`str-model-rejected`) for R1, R2 and `xor`. The SAT controls pass, and
//! each control's model is re-checked here by hand. z3 4.16.0 confirms every
//! `unsat` pin.
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

const XY: &str = "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)";

fn verdict(body: &str) -> String {
    let out = run_script(&format!("{XY}{body}(check-sat)"));
    out.first().cloned().unwrap_or_default()
}

/// The value of String variable `name` in a `(get-model)` response. The
/// controls only use `A`, `B` and the empty string, so no escape handling.
fn model_str(model: &str, name: &str) -> String {
    let key = format!("(define-fun {name} () String \"");
    let start = model.find(&key).unwrap_or_else(|| panic!("{name} missing: {model}")) + key.len();
    let end = start + model[start..].find('"').expect("closing quote");
    model[start..end].to_owned()
}

fn sat_model(body: &str) -> (String, String) {
    let out = run_script(&format!(
        "(set-option :produce-models true){XY}{body}(check-sat)(get-model)"
    ));
    assert_eq!(out[0], "sat", "control must be sat: {out:?}");
    (model_str(&out[1], "x"), model_str(&out[1], "y"))
}

/// Corpus row `str-pred-small-rw_370.smt2`. z3: unsat.
#[test]
fn noetzli_370() {
    assert_eq!(
        verdict(r#"(assert (not (= (= "A" (str.++ y x)) (= "A" (str.++ x y)))))"#),
        "unsat"
    );
}

/// Corpus row `str-pred-small-rw_458.smt2`. z3: unsat.
#[test]
fn noetzli_458() {
    assert_eq!(
        verdict(r#"(assert (not (= (= "B" (str.++ y x)) (= "B" (str.++ x y)))))"#),
        "unsat"
    );
}

/// R1 (spec §1.2): H1 shape, top-level literals only. z3: unsat.
#[test]
fn r1_unit_diseq() {
    assert_eq!(
        verdict(r#"(assert (= "A" (str.++ y x)))(assert (not (= "A" (str.++ x y))))"#),
        "unsat"
    );
}

/// R2 (spec §1.2): the char-peel leaves `[] = [!strk0, x]`. z3: unsat.
#[test]
fn r2_both_vars_diseq() {
    assert_eq!(
        verdict(r#"(assert (= "A" (str.++ y x)))(assert (not (= "A" x)))(assert (not (= "A" y)))"#),
        "unsat"
    );
}

#[test]
fn distinct_form() {
    assert_eq!(
        verdict(r#"(assert (distinct (= "A" (str.++ y x)) (= "A" (str.++ x y))))"#),
        "unsat"
    );
}

#[test]
fn xor_form() {
    assert_eq!(
        verdict(r#"(assert (xor (= "A" (str.++ y x)) (= "A" (str.++ x y))))"#),
        "unsat"
    );
}

/// Stays `sat` after Task 2: the gate cannot evaluate the Bool constant `p`
/// (spec §9 audit). It turns `unsat` at Task 4 (H3).
#[test]
fn bool_proxy() {
    assert_eq!(
        verdict(
            r#"(declare-fun p () Bool)(assert (= p (= "A" (str.++ y x))))
               (assert (not (= p (= "A" (str.++ x y)))))"#
        ),
        "unsat"
    );
}

/// Review Focus 5: a `distinct` atom asserted false (`¬distinct ≡ =`) lands in
/// `eq_true` and must get the same own-literal exemption. z3: unsat.
#[test]
fn not_distinct_form() {
    assert_eq!(
        verdict(r#"(assert (not (= (not (distinct "A" (str.++ y x))) (= "A" (str.++ x y)))))"#),
        "unsat"
    );
}

/// H2 (constant-prefix residual) is QUEUED (spec §9). Today it answers `sat`
/// with a bogus model. After Task 2 the gate turns it into a sound `unknown`.
/// If a later slice fixes H2, change this to `unsat` on purpose.
#[test]
fn ab_prefix_h2() {
    assert_ne!(
        verdict(r#"(assert (not (= (= "AB" (str.++ y x)) (= "AB" (str.++ x y)))))"#),
        "sat"
    );
}

#[test]
fn ctrl_single_eq() {
    let (x, y) = sat_model(r#"(assert (= "A" (str.++ y x)))"#);
    assert_eq!(format!("{y}{x}"), "A");
}

#[test]
fn ctrl_both_empty_ok() {
    let (x, y) = sat_model(r#"(assert (= "" (str.++ y x)))(assert (= "" (str.++ x y)))"#);
    assert_eq!((x.as_str(), y.as_str()), ("", ""));
}

/// Review Focus 1: a genuine `sat` whose Bool `=` the gate now evaluates.
#[test]
fn ctrl_iff_true() {
    let (x, y) = sat_model(r#"(assert (= (= "A" (str.++ y x)) (= "A" (str.++ x y))))"#);
    assert_eq!(format!("{y}{x}") == "A", format!("{x}{y}") == "A");
}

/// Review Focus 3 end to end: `"" = x ++ x` forces `x = ""`.
#[test]
fn ctrl_repeated_var() {
    let (x, _y) = sat_model(r#"(assert (= "" (str.++ x x y)))"#);
    assert_eq!(x, "");
}
```

- [ ] **Step 2: Run it and record the red set**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice52_probes)' --no-fail-fast`

Expected: 13 tests discovered.
- FAIL: `noetzli_370`, `noetzli_458`, `r1_unit_diseq`, `r2_both_vars_diseq`, `distinct_form`, `xor_form`, `bool_proxy`, `not_distinct_form`, `ab_prefix_h2`.
- PASS: the four `ctrl_*`.

If a control fails, stop and report it: it is a pre-existing bug outside this slice's reasoning. If `not_distinct_form` passes on `main`, keep it anyway and note that in the commit message.

- [ ] **Step 3: Confirm the `unsat` pins with z3**

```bash
S=$(mktemp -d); for b in \
 '(assert (not (= (= "A" (str.++ y x)) (= "A" (str.++ x y)))))' \
 '(assert (= "A" (str.++ y x)))(assert (not (= "A" x)))(assert (not (= "A" y)))' \
 '(assert (not (= (not (distinct "A" (str.++ y x))) (= "A" (str.++ x y)))))' \
 '(declare-fun p () Bool)(assert (= p (= "A" (str.++ y x))))(assert (not (= p (= "A" (str.++ x y)))))' \
 '(assert (not (= (= "AB" (str.++ y x)) (= "AB" (str.++ x y)))))'; do
 printf '(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)%s(check-sat)' "$b" > $S/p.smt2; z3 $S/p.smt2; done
```

Expected: `unsat` five times.

- [ ] **Step 4: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/slice52_probes.rs
git commit -m "test: slice52 T1 - red pins for the Noetzli pair and reduced reproducers"
```

---

### Task 2: Model gate evaluates Bool-sorted `=` / `distinct` (spec §3.1)

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (`eval_atom`, ~line 1667)
- Test: `crates/shinri-solver/src/lib.rs` (new `#[cfg(test)] mod slice52_gate_tests` at the end of the file)

**Interfaces:**
- Consumes: `Solver::{new, ctx_mut, declare_fun, app, eq, eval_bool, string_model_satisfies}`, `Model { values }` (`pub(crate)`), `ModelVal::String`.
- Produces: `eval_atom` returns `Some(bool)` for a Bool-sorted `=`/`distinct` whose two operands `eval_bool` can decide, and `None` otherwise.

- [ ] **Step 1: Write the failing tests**

Append to `crates/shinri-solver/src/lib.rs`:

```rust
#[cfg(test)]
mod slice52_gate_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Op, TermId};
    use shinri_theory::types::ModelVal;

    /// `(x, y, e1, e2)` with `e1 = (= "A" (str.++ y x))`, `e2 = (= "A" (str.++ x y))`.
    fn noetzli_atoms(s: &mut Solver) -> (TermId, TermId, TermId, TermId) {
        let ss = s.ctx_mut().string_sort();
        let xf = s.declare_fun("x", &[], ss);
        let x = s.app(Op::Uninterpreted(xf), &[]);
        let yf = s.declare_fun("y", &[], ss);
        let y = s.app(Op::Uninterpreted(yf), &[]);
        let a = s.ctx_mut().mk_string_const("A");
        let yx = s.app(Op::Builtin(BuiltinOp::StrConcat), &[y, x]);
        let xy = s.app(Op::Builtin(BuiltinOp::StrConcat), &[x, y]);
        let e1 = s.eq(a, yx);
        let e2 = s.eq(a, xy);
        (x, y, e1, e2)
    }

    fn model(pairs: &[(TermId, &str)]) -> Model {
        let mut m = Model::default();
        for &(t, v) in pairs {
            m.values.insert(t, ModelVal::String(v.to_owned()));
        }
        m
    }

    #[test]
    fn bool_eq_of_two_false_atoms_is_true() {
        let mut s = Solver::new();
        let (x, y, e1, e2) = noetzli_atoms(&mut s);
        let m = model(&[(x, ""), (y, "E")]);
        let iff = s.eq(e1, e2);
        assert_eq!(s.eval_bool(iff, &m), Some(true));
        let not_iff = s.app(Op::Builtin(BuiltinOp::Not), &[iff]);
        assert_eq!(s.eval_bool(not_iff, &m), Some(false));
    }

    /// The exact Noetzli `_370` escape: the bogus model must be REJECTED.
    #[test]
    fn gate_rejects_noetzli_bogus_model() {
        let mut s = Solver::new();
        let (x, y, e1, e2) = noetzli_atoms(&mut s);
        let iff = s.eq(e1, e2);
        let assertion = s.app(Op::Builtin(BuiltinOp::Not), &[iff]);
        let m = model(&[(x, ""), (y, "E")]);
        assert!(!s.string_model_satisfies(&[assertion], &m));
    }

    #[test]
    fn bool_distinct_of_two_true_atoms_is_false() {
        let mut s = Solver::new();
        let (x, y, e1, e2) = noetzli_atoms(&mut s);
        let m = model(&[(x, ""), (y, "A")]);
        let d = s.app(Op::Builtin(BuiltinOp::Distinct), &[e1, e2]);
        assert_eq!(s.eval_bool(d, &m), Some(false));
    }

    /// Three-valued: an un-valued leaf makes the Bool `=` undecided, never a
    /// fabricated verdict.
    #[test]
    fn bool_eq_with_unvalued_side_is_none() {
        let mut s = Solver::new();
        let (x, _y, e1, e2) = noetzli_atoms(&mut s);
        let m = model(&[(x, "")]); // y un-valued
        let iff = s.eq(e1, e2);
        assert_eq!(s.eval_bool(iff, &m), None);
    }
}
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo nextest run -p shinri-solver -E 'test(/slice52_gate_tests/)'`

Expected: 4 discovered. FAIL: `bool_eq_of_two_false_atoms_is_true`, `gate_rejects_noetzli_bogus_model`, `bool_distinct_of_two_true_atoms_is_false` (they get `None`/`true`). PASS: `bool_eq_with_unvalued_side_is_none`, which already gets `None`.

- [ ] **Step 3: Implement**

In `eval_atom` (`crates/shinri-solver/src/lib.rs`), insert directly after `let sort0 = self.ctx.sort_of(kids[0]);`:

```rust
        // Slice 52: a Bool-sorted `=`/`distinct` (iff/xor over two formulas —
        // the Noetzli shape `(= (= "A" y++x) (= "A" x++y))`). Before this arm it
        // fell through to `None`, which the gate reads as SATISFIED, so a bogus
        // model passed. Same three-valued rule as the `xor` arm of `eval_bool`.
        if sort0 == self.ctx.bool_sort() {
            let a = self.eval_bool(kids[0], model)?;
            let b = self.eval_bool(kids[1], model)?;
            return match op {
                Op::Builtin(BuiltinOp::Eq) => Some(a == b),
                Op::Builtin(BuiltinOp::Distinct) => Some(a != b),
                _ => None,
            };
        }
```

- [ ] **Step 4: Run the unit tests and the probes**

Run: `cargo nextest run -p shinri-solver -E 'test(/slice52_gate_tests/)'`
Expected: 4 passed.

Run: `cargo nextest run -p shinri-solver -E 'binary(slice52_probes)' --no-fail-fast`
Expected: 13 discovered.
- PASS: `ab_prefix_h2` (now `unknown`) and all four `ctrl_*`.
- Still FAIL: `noetzli_370`, `noetzli_458`, `distinct_form` and `not_distinct_form` (each now `unknown`, not `sat`); `bool_proxy` (still `sat`, Review Focus 2); `r1_unit_diseq`, `r2_both_vars_diseq`, `xor_form` (`unknown`).
- If `ctrl_iff_true` now fails, the gate rejected a genuine model. Stop and debug with superpowers:systematic-debugging before continuing.

Also check by hand: `cargo build --release -p shinri-cli` then run
`target/release/shinri --stats bench/corpus/QF_SLIA/20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_370.smt2`.
Expected: `unknown`, with `fence=str-model-rejected` on stderr.

- [ ] **Step 5: Run the solver crate's full suite**

Run: `cargo nextest run -p shinri-solver`
Expected: all pass except the still-red `slice52_probes` listed above.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/src/lib.rs
git commit -m "fix(solver): slice52 T2 - string model gate evaluates Bool-sorted =/distinct"
```

---

### Task 3: H1 — `[] = [v1..vn]` propagates `vi ≈ ""` (spec §3.2)

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs` (`resolve_inner`, the `SLICE 33/34: single-atom propagation` block, ~line 757–858)
- Test: `crates/shinri-str/src/wordeq.rs` test module, right after `mixed_var_skolem_residual_does_not_propagate` (~line 2150)

**Interfaces:**
- Consumes: `resolve_equation(terms, eq, lhs, rhs, just, eqn_lit, fresh_ctr, emitted) -> StepResult`; `same(terms, eq, a, b) -> bool`; test helpers `declare_str_var`, `dummy_eqn_lit`.
- Produces: `StepResult::Propagate { var, word, just }` with `word` the interned `""`, for a residual that is empty on one side and has two or more free atoms (skolems included) on the other.

- [ ] **Step 1: Write the failing tests**

Add to the `wordeq.rs` test module:

```rust
    // ── Slice 52 (H1): empty residual against several free atoms ─────────────
    // `[] = [v1, …, vn]` (n ≥ 2) entails every `vi ≈ ""`. Report the first atom
    // not already `≈ ""`; later rounds report the rest.

    fn run_empty_vs(
        ctx: &mut Context,
        eq: &mut EqualityEngine,
        rhs: &[shinri_core::TermId],
    ) -> StepResult {
        let lit = dummy_eqn_lit();
        let lhs: [shinri_core::TermId; 0] = [];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        resolve_equation(
            ctx,
            eq,
            &lhs,
            rhs,
            vec![EqLeaf::Asserted(lit)],
            lit,
            &mut ctr,
            &mut emitted,
        )
    }

    #[test]
    fn empty_vs_two_vars_propagates_first_to_empty() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_h1");
        let y = declare_str_var(&mut ctx, "y_h1");
        match run_empty_vs(&mut ctx, &mut eq, &[x, y]) {
            StepResult::Propagate { var, word, just } => {
                assert_eq!(var, x);
                assert_eq!(ctx.string_const_value(word), Some(""));
                assert!(just
                    .iter()
                    .any(|l| matches!(l, EqLeaf::Asserted(a) if *a == dummy_eqn_lit())));
            }
            _ => panic!("`[] = [x, y]` must Propagate `x ≈ \"\"`"),
        }
    }

    #[test]
    fn empty_vs_two_vars_skips_atom_already_empty() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_h1s");
        let y = declare_str_var(&mut ctx, "y_h1s");
        let empty = ctx.mk_string_const("");
        let (xn, en) = (eq.intern(x), eq.intern(empty));
        let _ = eq.merge(xn, en, EqJust::Asserted(Lit::new(Var::new(1), true)));
        match run_empty_vs(&mut ctx, &mut eq, &[x, y]) {
            StepResult::Propagate { var, .. } => assert_eq!(var, y),
            _ => panic!("with `x ≈ \"\"` known, `[] = [x, y]` must Propagate `y`"),
        }
    }

    /// No loop: once every atom is `≈ ""`, nothing is propagated again.
    #[test]
    fn empty_vs_vars_all_already_empty_does_not_propagate() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_h1a");
        let y = declare_str_var(&mut ctx, "y_h1a");
        let empty = ctx.mk_string_const("");
        let en = eq.intern(empty);
        for (v, k) in [(x, 1u32), (y, 2u32)] {
            let vn = eq.intern(v);
            let _ = eq.merge(vn, en, EqJust::Asserted(Lit::new(Var::new(k), true)));
        }
        let r = run_empty_vs(&mut ctx, &mut eq, &[x, y]);
        assert!(!matches!(r, StepResult::Propagate { .. } | StepResult::Conflict(_)));
    }

    /// Review Focus 3: a repeated variable propagates once.
    #[test]
    fn empty_vs_repeated_var_propagates_it() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_h1r");
        match run_empty_vs(&mut ctx, &mut eq, &[x, x]) {
            StepResult::Propagate { var, .. } => assert_eq!(var, x),
            _ => panic!("`[] = [x, x]` must Propagate `x ≈ \"\"`"),
        }
    }

    /// Spec §3.2: minted skolems are ALLOWED here (a merge into `""` is a
    /// constant fact, not the class union the slice-34 exclusion guards).
    #[test]
    fn empty_vs_skolem_and_var_propagates_skolem() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let k = declare_str_var(&mut ctx, "!strk0");
        let x = declare_str_var(&mut ctx, "x_h1k");
        match run_empty_vs(&mut ctx, &mut eq, &[k, x]) {
            StepResult::Propagate { var, .. } => assert_eq!(var, k),
            _ => panic!("`[] = [!strk0, x]` must Propagate `!strk0 ≈ \"\"`"),
        }
    }

    /// Unchanged: a non-empty constant in the residual still conflicts.
    #[test]
    fn empty_vs_var_and_nonempty_const_still_conflicts() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_h1c");
        let a = ctx.mk_string_const("A");
        assert!(matches!(
            run_empty_vs(&mut ctx, &mut eq, &[x, a]),
            StepResult::Conflict(_)
        ));
    }
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo nextest run -p shinri-str -E 'test(/empty_vs_/)'`

Expected: 7 discovered.
- FAIL: `empty_vs_two_vars_propagates_first_to_empty`, `empty_vs_two_vars_skips_atom_already_empty`, `empty_vs_repeated_var_propagates_it`, `empty_vs_skolem_and_var_propagates_skolem`.
- PASS: `empty_vs_vars_all_already_empty_does_not_propagate`, `empty_vs_var_and_nonempty_const_still_conflicts`, and the pre-existing `empty_vs_single_variable_propagates_empty_word`.

- [ ] **Step 3: Implement**

In `resolve_inner`, inside the `SLICE 33/34` block, insert immediately before `if let Some((var, const_side)) = pair {`:

```rust
        // SLICE 52 (H1): `[] = [v1, …, vn]` (n ≥ 2, every atom a free variable)
        // ENTAILS `vi ≈ ""` for every i — a concatenation is empty iff every
        // part is. Report ONE per round: the first atom not already `≈ ""`.
        // Later rounds report the rest; the `same` check makes the choice
        // advance, so this can never re-propagate the same merge (always taking
        // `vs[0]` looped in the spike). If every atom is already `≈ ""`, fall
        // through to `Done`. Minted `!strk*` skolems are ALLOWED here, unlike
        // the slice-34 alias case above: that exclusion stops a var–var CLASS
        // UNION from replacing an F-split the model builder needs, and a merge
        // into `""` is a constant fact, not a union (spec §3.2). The driver
        // cites `nf_ante` alongside `just`, as for every `Propagate`.
        let empty_vs_vars = match (l_res.is_empty(), r_res.is_empty()) {
            (true, false) => Some(r_res),
            (false, true) => Some(l_res),
            _ => None,
        };
        if let Some(vs) = empty_vs_vars {
            if vs.len() >= 2 && vs.iter().all(|&a| is_free_var(terms, a)) {
                let empty = terms.mk_string_const("");
                if let Some(&v) = vs.iter().find(|&&a| !same(terms, eq, a, empty)) {
                    return StepResult::Propagate {
                        var: v,
                        word: empty,
                        just,
                    };
                }
            }
        }

```

- [ ] **Step 4: Run the unit tests, the crate, and the probes**

Run: `cargo nextest run -p shinri-str -E 'test(/empty_vs_/)'`
Expected: 7 passed.

Run: `cargo nextest run -p shinri-str`
Expected: all pass.

Run: `cargo nextest run -p shinri-solver -E 'binary(slice52_probes)' --no-fail-fast`
Expected:
- now PASS: `r1_unit_diseq`, `r2_both_vars_diseq`, plus everything that passed after Task 2.
- still FAIL: `noetzli_370`, `noetzli_458`, `distinct_form`, `xor_form`, `bool_proxy`, `not_distinct_form` (H3 blocks them).
- If `xor_form` already passes, record that in the commit message; it is fine.

- [ ] **Step 5: Run the solver crate and the existing string oracles**

Run: `cargo nextest run -p shinri-solver`
Expected: all pass except the H3-blocked probes above.

Run: `cargo nextest run -p shinri-solver --features oracle -E 'binary(qfs_differential) + binary(slice33_probes) + binary(slice34_probes) + binary(oracle)'`
Expected: non-zero discovered, all pass.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/wordeq.rs
git commit -m "fix(str): slice52 T3 - propagate vi = \"\" for an empty residual against several free atoms (H1)"
```

- [ ] **Step 7: Record the fuzz baseline for Task 5**

With `HEAD` at this commit (before Task 4), apply Task 5 Step 1's `qfs_fuzz_corpus.rs` generator change **uncommitted**, then run:

```bash
E1_BOOLEQ=1 cargo nextest run -p shinri-solver --features oracle --run-ignored only \
  -E 'test(e1_enumerate_wrong_verdicts)' --no-capture 2>&1 | tee target/slice52-e1-before.txt | tail -40
git stash   # keep the generator change for Task 5
```

Expected: 1 test discovered. Keep the `E1 CORPUS SUMMARY` block (distinct shapes by class) as the "before" numbers. Then `git stash pop` at Task 5 Step 1.

---

### Task 4: H3 — the word-equation gate ignores its own literal and disequalities (spec §3.3)

**Files:**
- Create: `crates/shinri-str/src/wordeq_gate.rs`
- Modify: `crates/shinri-str/src/lib.rs`:
  - `mod` list, ~line 16;
  - `check()`: build the gate after the `input_cond_roots` block (~line 322);
  - the gate call at ~line 773;
  - the propagation `Ok(())` arm, ~line 940;
  - the `#[cfg(test)] impl StrSolver` helpers, ~line 1707.
- Test: `crates/shinri-str/src/wordeq_gate.rs` (unit), `crates/shinri-str/src/lib.rs` `mod tests` (theory-level).

**Interfaces:**
- Consumes: `crate::normalize::flatten(terms: &Context, t: TermId, out: &mut Vec<TermId>)`, `crate::wordeq::diseq_sides(terms, atom) -> (TermId, TermId)`, `EqualityEngine::{intern, find, merge}`, `ENodeId`.
- Produces:
  - `pub(crate) enum CondSrc { Eq(TermId), Propagation }`
  - `pub(crate) struct WordEqGate` with:
    - `add(&mut self, root: ENodeId, src: CondSrc)`
    - `on_merge(&mut self, old_a: ENodeId, old_b: ENodeId, new_root: ENodeId)`
    - `side_clean_for(&self, eq: &mut EqualityEngine, terms: &Context, t: TermId, own: TermId) -> bool`
  - test helpers `StrSolver::test_force_eq_true_at(atom, level)` and `test_force_diseq_true_at(atom, level)`.

- [ ] **Step 1: Write the module with its failing unit tests**

Create `crates/shinri-str/src/wordeq_gate.rs`:

```rust
//! Slice 52 (H3): the word-equation resolution gate's view of conditional
//! merges.
//!
//! The E1 gate refuses to resolve a word equation whose sides sit in a class
//! that a CONDITIONAL (dl>0) merge touched, because resolution reads the
//! single-level normal forms and does not cite that merge (ce1..ce8). The
//! shared `input_cond_roots` set is too coarse for this one gate, in two ways:
//!
//! - it holds every conditional DISEQUALITY, but a disequality merges nothing,
//!   so it cannot make a normal form branch-local;
//! - it holds the equation's OWN literal, but every result of resolving the
//!   equation already cites that literal (`Conflict`/`Propagate` carry
//!   `Asserted(lit)`, `Split` is guarded by `¬lit`).
//!
//! So this map records, per class root, WHICH conditional sources touched it.
//! Only non-minted conditional equalities and conditional propagation merges
//! are recorded. A side is clean for equation `e` iff no root it reads has a
//! contributor other than `e` itself. The other readers of `input_cond_roots`
//! (membership, order, same-word conflicts) are unchanged.
use rustc_hash::FxHashMap;
use shinri_core::{Context, TermId};
use shinri_theory::types::ENodeId;
use shinri_theory::EqualityEngine;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CondSrc {
    /// A conditional (dl>0), non-minted input equality atom.
    Eq(TermId),
    /// A conditional slice-33 propagation merge. Never exempt.
    Propagation,
}

#[derive(Default, Debug)]
pub(crate) struct WordEqGate {
    by_root: FxHashMap<ENodeId, Vec<CondSrc>>,
}

impl WordEqGate {
    pub(crate) fn add(&mut self, root: ENodeId, src: CondSrc) {
        let v = self.by_root.entry(root).or_default();
        if !v.contains(&src) {
            v.push(src);
        }
    }

    /// Carry both pre-merge roots' contributors onto the post-merge root, so an
    /// intra-check merge never launders a dirty class clean.
    pub(crate) fn on_merge(&mut self, old_a: ENodeId, old_b: ENodeId, new_root: ENodeId) {
        let mut moved = Vec::new();
        for r in [old_a, old_b] {
            if r != new_root {
                if let Some(v) = self.by_root.remove(&r) {
                    moved.extend(v);
                }
            }
        }
        for s in moved {
            self.add(new_root, s);
        }
    }

    /// `true` iff every flattened atom of `t` sits in a class whose only
    /// conditional contributor (if any) is the equation `own` itself.
    pub(crate) fn side_clean_for(
        &self,
        eq: &mut EqualityEngine,
        terms: &Context,
        t: TermId,
        own: TermId,
    ) -> bool {
        if self.by_root.is_empty() {
            return true;
        }
        let mut flat = Vec::new();
        crate::normalize::flatten(terms, t, &mut flat);
        flat.iter().all(|&a| {
            let n = eq.intern(a);
            self.by_root
                .get(&eq.find(n))
                .is_none_or(|v| v.iter().all(|&s| s == CondSrc::Eq(own)))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Lit, Op, Var};
    use shinri_theory::types::EqJust;

    fn var(ctx: &mut Context, name: &str) -> TermId {
        let ss = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], ss);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    /// `(ctx, eq, x, y, e_own, e_other)` with `e_own = (= x "A")`,
    /// `e_other = (= y "B")`.
    fn fixture() -> (Context, EqualityEngine, TermId, TermId, TermId, TermId) {
        let mut ctx = Context::new();
        let eq = EqualityEngine::default();
        let x = var(&mut ctx, "x_g");
        let y = var(&mut ctx, "y_g");
        let a = ctx.mk_string_const("A");
        let b = ctx.mk_string_const("B");
        let e_own = ctx.mk_eq(x, a).unwrap();
        let e_other = ctx.mk_eq(y, b).unwrap();
        (ctx, eq, x, y, e_own, e_other)
    }

    fn root(eq: &mut EqualityEngine, t: TermId) -> ENodeId {
        let n = eq.intern(t);
        eq.find(n)
    }

    #[test]
    fn empty_gate_is_clean() {
        let (ctx, mut eq, x, _y, e_own, _) = fixture();
        assert!(WordEqGate::default().side_clean_for(&mut eq, &ctx, x, e_own));
    }

    #[test]
    fn own_equation_is_clean_for_itself_only() {
        let (ctx, mut eq, x, _y, e_own, e_other) = fixture();
        let mut g = WordEqGate::default();
        let rx = root(&mut eq, x);
        g.add(rx, CondSrc::Eq(e_own));
        assert!(g.side_clean_for(&mut eq, &ctx, x, e_own));
        assert!(!g.side_clean_for(&mut eq, &ctx, x, e_other));
    }

    #[test]
    fn second_conditional_equation_blocks() {
        let (ctx, mut eq, x, _y, e_own, e_other) = fixture();
        let mut g = WordEqGate::default();
        let rx = root(&mut eq, x);
        g.add(rx, CondSrc::Eq(e_own));
        g.add(rx, CondSrc::Eq(e_other));
        assert!(!g.side_clean_for(&mut eq, &ctx, x, e_own));
    }

    #[test]
    fn propagation_contributor_blocks() {
        let (ctx, mut eq, x, _y, e_own, _) = fixture();
        let mut g = WordEqGate::default();
        let rx = root(&mut eq, x);
        g.add(rx, CondSrc::Propagation);
        assert!(!g.side_clean_for(&mut eq, &ctx, x, e_own));
    }

    #[test]
    fn untouched_class_is_clean() {
        let (ctx, mut eq, x, y, e_own, e_other) = fixture();
        let mut g = WordEqGate::default();
        let ry = root(&mut eq, y);
        g.add(ry, CondSrc::Eq(e_other));
        assert!(g.side_clean_for(&mut eq, &ctx, x, e_own));
    }

    /// Review Focus 4: after a merge unions x's and y's classes, y's other
    /// contributor must still block x's equation.
    #[test]
    fn on_merge_carries_contributors() {
        let (ctx, mut eq, x, y, e_own, e_other) = fixture();
        let mut g = WordEqGate::default();
        let (rx, ry) = (root(&mut eq, x), root(&mut eq, y));
        g.add(rx, CondSrc::Eq(e_own));
        g.add(ry, CondSrc::Eq(e_other));
        let _ = eq.merge(rx, ry, EqJust::Asserted(Lit::new(Var::new(1), true)));
        let r = eq.find(rx);
        g.on_merge(rx, ry, r);
        assert!(!g.side_clean_for(&mut eq, &ctx, x, e_own));
        assert!(!g.side_clean_for(&mut eq, &ctx, y, e_own));
    }
}
```

In `crates/shinri-str/src/lib.rs`, add `mod wordeq_gate;` after `pub mod wordeq;` (line 16).

- [ ] **Step 2: Run the module tests**

Run: `cargo nextest run -p shinri-str -E 'test(/wordeq_gate::/)'`

Expected: 6 discovered, 6 passed. The module is new and self-contained. It is not wired into the solver yet, so these tests check the data structure itself, not the fix. If any fail, fix the module before going on.

- [ ] **Step 3: Write the failing theory-level test**

Add these helpers to the `#[cfg(test)] impl StrSolver` block in `lib.rs` (after `test_force_diseq_true`):

```rust
    /// Like `test_force_eq_true`, at an explicit decision `level` (> 0 means
    /// conditional — the case the E1 gates reason about).
    pub fn test_force_eq_true_at(&mut self, atom: TermId, level: u32) {
        self.eq_true.push((atom, Lit::new(Var::new(0), true)));
        self.eq_levels.push(level);
    }

    /// Like `test_force_diseq_true`, at an explicit decision `level`.
    pub fn test_force_diseq_true_at(&mut self, atom: TermId, level: u32) {
        self.diseq_true.push((atom, Lit::new(Var::new(1), true)));
        self.diseq_levels.push(level);
    }
```

Add to `mod tests` in `lib.rs`:

```rust
    /// Slice 52 (H3): a CONDITIONAL word equation `"A" = y ++ x` must still be
    /// resolved (char-peel `y = "" ∨ y = "A" ++ k`), even with a conditional
    /// sibling disequality `"A" ≠ x ++ y` on the shared `"A"` class. Before
    /// the fix, the gate counted the equation's own literal and the
    /// disequality as conditional merges and never resolved it.
    #[test]
    fn conditional_equation_is_resolved_despite_own_literal_and_diseq() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");
        let a = ctx.mk_string_const("A");
        let empty = ctx.mk_string_const("");
        let yx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[y, x])
            .unwrap();
        let xy = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let e = ctx.mk_eq(a, yx).unwrap();
        let d = ctx.mk_eq(a, xy).unwrap();
        let peel_empty = ctx.mk_eq(y, empty).unwrap();

        let mut solver = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        solver.new_var(&mut cx, Var::new(0), e);
        solver.new_var(&mut cx, Var::new(1), d);
        solver.test_force_eq_true_at(e, 1);
        solver.test_force_diseq_true_at(d, 1);
        let mut saw_peel = false;
        for _ in 0..64 {
            match solver.check(&mut cx, Effort::Full) {
                TCheck::Split { atoms, .. } => {
                    if atoms.contains(&peel_empty) {
                        saw_peel = true;
                        break;
                    }
                }
                TCheck::Sat | TCheck::Unknown => break,
                TCheck::Conflict(_) => break,
            }
        }
        assert!(
            saw_peel,
            "a conditional `\"A\" = y ++ x` must be char-peeled on `y` (H3)"
        );
    }
```

Run: `cargo nextest run -p shinri-str -E 'test(conditional_equation_is_resolved_despite_own_literal_and_diseq)'`
Expected: 1 discovered, FAIL (`saw_peel` false; the loop ends on `Sat`). If it
fails for a different reason (a `Conflict` or `Unknown` ends the loop first),
print the `TCheck` sequence and adjust the fixture, not the assertion: the
assertion is that the char-peel on `y` is emitted.

- [ ] **Step 4: Build the gate in `check()`**

In `lib.rs`, directly after the closing `}` of the block that builds `input_cond_roots`/`all_cond_roots` (after the `prop_merge_info` loop, ~line 322), insert:

```rust
        // Slice 52 (H3): the word-equation resolution gate's own view (see
        // `wordeq_gate.rs`). Same sources as `input_cond_roots` MINUS
        // disequalities (they merge nothing), keyed by contributor so an
        // equation is not blocked by its own literal. `input_cond_roots` and
        // `all_cond_roots` are unchanged for every other reader.
        let mut wordeq_gate = crate::wordeq_gate::WordEqGate::default();
        for (i, &(atom, _)) in self.eq_true.iter().enumerate() {
            if *self.eq_levels.get(i).unwrap_or(&u32::MAX) > 0 && !self.minted_eqs.contains(&atom)
            {
                let (a, b) = crate::wordeq::diseq_sides(cx.terms, atom);
                for side in [a, b] {
                    let n = cx.eq.intern(side);
                    let r = cx.eq.find(n);
                    wordeq_gate.add(r, crate::wordeq_gate::CondSrc::Eq(atom));
                }
            }
        }
        for &(var, word, level) in &self.prop_merge_info {
            if level > 0 {
                for side in [var, word] {
                    let n = cx.eq.intern(side);
                    let r = cx.eq.find(n);
                    wordeq_gate.add(r, crate::wordeq_gate::CondSrc::Propagation);
                }
            }
        }
```

- [ ] **Step 5: Use it at the word-equation gate**

Replace the condition at ~line 773:

```rust
            if side_clean(cx.eq, cx.terms, l, &input_cond_roots)
                && side_clean(cx.eq, cx.terms, r, &input_cond_roots)
            {
```

with:

```rust
            // Slice 52 (H3): gate on `wordeq_gate`, not `input_cond_roots`: this
            // equation's OWN literal is cited by everything resolution emits,
            // and conditional disequalities merge nothing (spec §3.3).
            if wordeq_gate.side_clean_for(cx.eq, cx.terms, l, atom)
                && wordeq_gate.side_clean_for(cx.eq, cx.terms, r, atom)
            {
```

Then add one sentence to the end of the E1 (iter 3) comment just above it: `Slice 52: this gate now reads `wordeq_gate` (own literal exempt, disequalities excluded); see wordeq_gate.rs.`

- [ ] **Step 6: Keep the map right across intra-check propagation merges**

In the `StepResult::Propagate` driver arm, directly before `match cx.eq.merge(`, add:

```rust
                        let (pre_v, pre_w) = (cx.eq.find(vn), cx.eq.find(wn));
```

In its `Ok(()) => {` arm, replace:

```rust
                                if level > 0 {
                                    let r = cx.eq.find(vn);
                                    all_cond_roots.insert(r);
                                    input_cond_roots.insert(r);
                                }
```

with:

```rust
                                let r = cx.eq.find(vn);
                                // Slice 52: carry contributors across the union
                                // at ANY level, so a merge never launders a dirty
                                // class clean for the word-equation gate.
                                wordeq_gate.on_merge(pre_v, pre_w, r);
                                if level > 0 {
                                    all_cond_roots.insert(r);
                                    input_cond_roots.insert(r);
                                    wordeq_gate.add(r, crate::wordeq_gate::CondSrc::Propagation);
                                }
```

- [ ] **Step 7: Run the tests**

Run: `cargo nextest run -p shinri-str`
Expected: all pass, including `conditional_equation_is_resolved_despite_own_literal_and_diseq` and the 6 `wordeq_gate::` tests.

Run: `cargo nextest run -p shinri-solver -E 'binary(slice52_probes)'`
Expected: 13 discovered, 13 passed.
- If `bool_proxy` or `not_distinct_form` still fails, capture `--stats` output for it and debug with superpowers:systematic-debugging. Do not weaken the pin.

Run: `cargo nextest run -p shinri-solver`
Expected: all pass.

- [ ] **Step 8: Run the existing string oracles (ce1..ce8 guard)**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'binary(qfs_differential) + binary(slice33_probes) + binary(slice34_probes) + binary(oracle)'`
Expected: non-zero discovered, all pass. **A wrong `unsat` here triggers the fallback** (Global Constraints).

- [ ] **Step 9: Commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/wordeq_gate.rs crates/shinri-str/src/lib.rs
git commit -m "fix(str): slice52 T4 - word-equation gate exempts its own literal and ignores disequalities (H3)"
```

---

### Task 5: Oracle family and fuzz evidence for H3 (spec §6.3)

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_fuzz_corpus.rs` (`Gen::assertion`, ~line 250; new `Gen::bool_eq_assertion`)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (append a new family at the end)

**Interfaces:**
- Consumes: in `qfs_differential.rs`: `Lcg`, `Verdict`, `shinri_verdict`, `shinri_lines`, `z3_verdict`, `parse_string_values`, `z3_with_model`. In `qfs_fuzz_corpus.rs`: `Gen::word_term`.
- Produces: test `qfs_bool_eq_word_eqs_match_z3`; env switch `E1_BOOLEQ=1` for `e1_enumerate_wrong_verdicts`.

- [ ] **Step 1: Add the fuzz generator switch**

(If Task 3 Step 7 stashed this change, `git stash pop` instead.) In `qfs_fuzz_corpus.rs`, at the very top of `fn assertion(&mut self) -> String {`, insert:

```rust
        // Slice 52: Bool `=`/`distinct`/`xor` over two word equations (the
        // Noetzli shape), opt-in so the default sample and seed sequence are
        // unchanged.
        if std::env::var_os("E1_BOOLEQ").is_some() && self.rng.below(4) == 0 {
            return self.bool_eq_assertion();
        }
```

and add this method to `impl Gen`:

```rust
    fn bool_eq_assertion(&mut self) -> String {
        let a = format!("(= {} {})", self.word_term(), self.word_term());
        let b = format!("(= {} {})", self.word_term(), self.word_term());
        let op = ["=", "distinct", "xor"][self.rng.below(3) as usize];
        let core = format!("({op} {a} {b})");
        if self.rng.below(2) == 0 {
            format!("(not {core})")
        } else {
            core
        }
    }
```

Also add `E1_BOOLEQ=1` to the module doc's "Run:" block.

- [ ] **Step 2: Run the fuzzer after Task 4 and compare**

```bash
E1_BOOLEQ=1 cargo nextest run -p shinri-solver --features oracle --run-ignored only \
  -E 'test(e1_enumerate_wrong_verdicts)' --no-capture 2>&1 | tee target/slice52-e1-after.txt | tail -40
```

Expected: 1 discovered. Compare its `distinct-by-class` line and shape list with `target/slice52-e1-before.txt`.
- **Any `WrongUnsat` shape in "after" that is not in "before" is a stop.** Minimise it, check it against z3, and if Task 4 caused it, take the fallback.
- A new `WrongSat` shape is a stop too: triage it the same way.
- If the run takes more than 5 min, that is fine: it is already `#[ignore]`d and never in the blocking tier.

Also run the default sample (no `E1_BOOLEQ`) once and confirm no new `WrongUnsat` against the same command run on `main` (build `main` in a scratch worktree if needed).

- [ ] **Step 3: Write the new differential family**

Append to `crates/shinri-solver/tests/qfs_differential.rs`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 52: Bool `=` / `distinct` / `xor` over pairs of word equations — the
// Noetzli `(not (= (= "A" y++x) (= "A" x++y)))` shape. Sides are a constant of
// length 0..=2 and a permuted concat of 2..=3 variables. Sat AND Unsat must
// agree with z3; Sat models are replayed through z3. Fresh seed — never
// perturb existing families' seeds.
// ─────────────────────────────────────────────────────────────────────────────

const BEQ_SEED: u64 = 0x52_52_0000_0001;
const BEQ_N_ITERS: usize = 200;

struct BeqGen {
    rng: Lcg,
}

impl BeqGen {
    fn lit(&mut self) -> String {
        let n = self.rng.below(3);
        let body: String = (0..n)
            .map(|_| ["A", "B"][self.rng.below(2) as usize])
            .collect();
        format!("\"{body}\"")
    }

    /// A concat of 2..=3 distinct variables in a random order.
    fn perm_concat(&mut self) -> String {
        let mut vs = vec!["s0", "s1", "s2"];
        let n = 2 + self.rng.below(2) as usize;
        for i in (1..vs.len()).rev() {
            let j = self.rng.below(i as u64 + 1) as usize;
            vs.swap(i, j);
        }
        format!("(str.++ {})", vs[..n].join(" "))
    }

    /// Two word equations; half the time they share the constant (the
    /// Noetzli shape, where the Bool combination is decided by commutation).
    fn pair(&mut self) -> (String, String) {
        let l1 = self.lit();
        let l2 = if self.rng.below(2) == 0 { l1.clone() } else { self.lit() };
        (
            format!("(= {l1} {})", self.perm_concat()),
            format!("(= {l2} {})", self.perm_concat()),
        )
    }

    fn body(seed: u64) -> String {
        let mut g = BeqGen { rng: Lcg(seed) };
        let mut s = String::from(
            "(set-logic QF_SLIA)\n(declare-const s0 String)\n(declare-const s1 String)\n(declare-const s2 String)\n",
        );
        for _ in 0..1 + g.rng.below(2) {
            let (a, b) = g.pair();
            let op = ["=", "distinct", "xor"][g.rng.below(3) as usize];
            let core = format!("({op} {a} {b})");
            if g.rng.below(2) == 0 {
                s.push_str(&format!("(assert (not {core}))\n"));
            } else {
                s.push_str(&format!("(assert {core})\n"));
            }
        }
        s
    }
}

#[test]
fn qfs_bool_eq_word_eqs_match_z3() {
    let mut rng = Lcg(BEQ_SEED);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness) =
        (0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..BEQ_N_ITERS {
        let seed = rng.next();
        let body = BeqGen::body(seed);
        let script = format!("{body}(check-sat)\n");
        let ours = shinri_verdict(&script);
        if ours == Verdict::Unknown {
            n_unknown += 1;
            continue;
        }
        let theirs = z3_verdict(&script);
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S BOOL-EQ WORD-EQ DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{script}"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let lines = shinri_lines(&format!("{script}(get-value (s0 s1 s2))\n"));
                if let Some(resp) = lines.get(1) {
                    let model = parse_string_values(resp);
                    if !model.is_empty() {
                        assert_eq!(
                            z3_with_model(&body, &model),
                            Verdict::Sat,
                            "WITNESS FAILURE (iter {it}, seed {seed}): model {model:?}\n{body}"
                        );
                        n_witness += 1;
                    }
                }
            }
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    println!(
        "qfs_bool_eq_word_eqs_match_z3: {BEQ_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown / {n_z3skip} z3-unknown; {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "bool-eq family produced zero SAT instances");
    assert!(n_unsat > 0, "bool-eq family produced zero UNSAT instances");
    assert!(n_witness > 0, "no witnesses checked — model path not exercised");
}
```

- [ ] **Step 4: Run it**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfs_bool_eq_word_eqs_match_z3)' --no-capture`

Expected: 1 discovered, PASS. The printed line shows non-zero sat, unsat and witnesses.
- A disagreement is a stop. Reproduce the printed script, check it against z3, and if Task 4 caused a wrong `unsat`, take the fallback.
- If the zero-SAT or zero-UNSAT assert fires, the generator drifted: fix the generator, not the assert.
- Record the wall time. If it is over 5 min, `#[ignore]` it as exhaustive and add a 20-iteration smoke companion.

- [ ] **Step 5: Run the unfiltered oracle suite**

Run: `cargo nextest run -p shinri-solver --features oracle`
Expected: non-zero discovered count (about 678, which is slice 51's 677 plus this family), all passed. Record the exact counts for the report.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfs_differential.rs crates/shinri-solver/tests/qfs_fuzz_corpus.rs
git commit -m "test(oracle): slice52 T5 - Bool =/distinct/xor over word equations; E1_BOOLEQ fuzz switch"
```

---

### Task 6: Gates, bench re-run, report, spec §12

**Files:**
- Create: `docs/superpowers/research/<run date YYYY-MM-DD>-smtlib-2024-slice52-str-bool-eq-report.md` (the date the bench run finished, as in every earlier report)
- Modify: `docs/superpowers/specs/2026-09-30-shinri-slice52-str-bool-eq-wordeq-design.md` (append `## 12. Measured outcomes`)

- [ ] **Step 1: Standard gates**

```bash
mise run lint
mise run test
mise run ci
```

Expected: all green. Record the passed/skipped counts from `mise run test`.

- [ ] **Step 2: Bench re-run (QF_S + QF_SLIA), same settings as slice 51**

```bash
cargo build --release -p shinri-cli
BENCH_LOGICS=QF_S,QF_SLIA BENCH_RUN_ID=slice52 taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice52 mise run bench-report
```

Expected: `bench/results/slice52/report.md` exists. Compare it against `bench/results/slice51/`, using the method of the slice-51 report (`docs/superpowers/research/2026-09-30-smtlib-2024-slice51-escapes-report.md`: headline, per-logic matrix, transition matrices of changed cells only).

- [ ] **Step 3: Check the success criteria (spec §7)**

1. `str-pred-small-rw_370` and `_458` are `wrong → correct` (`unsat`).
2. QF_S + QF_SLIA `wrong` is 2 → 0.
3. **0 rows `* → wrong`.** Any such row is a hard stop: root-cause it; if Task 4 caused it, take the fallback and re-run from Step 1.
4. List and triage every `correct → unknown/timeout` row, and report the `unknown:sat-budget` delta.
5. The gates from Step 1 and the oracle counts from Task 5 Step 5 are green, with non-zero counts.

- [ ] **Step 4: Write the report**

Follow the slice-51 report's sections:
- Headline
- Success criteria
- Per-logic matrix
- Transition matrices (changed cells only)
- Criterion 4 triage
- Oracle and fuzz evidence: the before/after `E1 CORPUS SUMMARY` and the `qfs_bool_eq_word_eqs_match_z3` counts
- Gates
- Queued for the next slice: spec §10, plus anything new
- References

Record the fixture sha, the timeout and `solver_md5`.

- [ ] **Step 5: Append spec §12 "Measured outcomes"**

The same table shape as slice 51's §12: criterion, result, and the `correct` deltas for QF_S and QF_SLIA.

- [ ] **Step 6: Commit and open the PR**

```bash
git add docs/superpowers/research/ docs/superpowers/specs/2026-09-30-shinri-slice52-str-bool-eq-wordeq-design.md
git commit -m "docs(bench+spec): slice52 - QF_S/QF_SLIA re-run report and measured outcomes"
git push -u origin slice52-str-bool-eq-wordeq
REPORT=$(ls docs/superpowers/research/*-smtlib-2024-slice52-str-bool-eq-report.md)
gh pr create --base main --title "slice52: Bool = in the string model gate; word-equation holes H1/H3" \
  --body "Implements docs/superpowers/specs/2026-09-30-shinri-slice52-str-bool-eq-wordeq-design.md. Report: $REPORT."
```

Then use superpowers:finishing-a-development-branch (merge commit when CI is green; delete the branch remote and local).
