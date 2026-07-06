# Slice 10: Non-Word ite Soundness + Array/Str Bridge Coverage — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix the wrong-SAT hole where ite over Int/Real/uninterpreted/Array sorts is misrouted to EUF as an opaque application (condition never linked to branches), then add the slice-9 follow-up differential coverage for Array/Str-Real operands mixed with the `fp.to_real` bridge.

**Architecture:** Broaden the existing slice-5 `word_norm` ite-elimination gate (fresh reserved `ite!<n>` symbol + defining assertion `(ite c (= w x) (= w y))`) from word sorts to every sort except Bool and String; route the fresh symbols' EUF/arith model values through the same `internal` filter the blast-model loops already use. Phase 2 adds Unknown-pinned canaries and no-disagreement z3 oracles for the (fenced-today) Array/Str bridge families.

**Tech Stack:** Rust workspace (`crates/shinri-*`), z3 on PATH for `--features oracle` differential tests, `easy_smt` for driving z3.

**Spec:** `docs/superpowers/specs/2026-07-06-shinri-slice10-ite-soundness-bridge-coverage-design.md` (read it first; §1.1 records plan-time pre-flight corrections that override §1/§3/§6 where they conflict).

## Global Constraints

- Toolchain is pinned via `rust-toolchain.toml` (1.96.0); CI runs `cargo fmt --check` and `cargo clippy --workspace --all-targets -- -D warnings`. Clippy on a warm cache gives FALSE PASSES — before trusting a clippy run, `touch` every source file you changed so its crate recompiles. Never run `cargo clippy --fix` (deadlocks in this environment).
- Commit messages follow the repo convention: `type(scope): summary (slice 10)` — see `git log --oneline` for examples.
- Oracle tests need z3 on PATH and the `oracle` feature: `cargo test -p shinri-solver --features oracle --test <file> -- --nocapture`. They take minutes; run them yourself in the background, never delegate the wait to a subagent loop.
- `word_norm` invariant (load-bearing): a term with no rewritten subterm must be returned with its ORIGINAL TermId — downstream stages key on TermIds.
- Word-sorted (BitVec/Float/RoundingMode) ite elimination behavior must be byte-identical after this slice; the existing word_norm unit tests and slice-5/6/7 e2e tests are the guard.

---

### Task 1: Broaden the word_norm ite-elimination gate

The wrong-SAT reproducers (spec §1) become failing e2e tests; the gate change at `word_norm.rs:136` makes them pass. Bool/String ites must keep passing through untouched.

**Files:**
- Create: `crates/shinri-solver/tests/ite_e2e.rs`
- Modify: `crates/shinri-solver/src/word_norm.rs` (gate at line 136, predicate at line 65, module doc lines 1–21, new unit tests)

**Interfaces:**
- Produces: `word_norm` now eliminates Int/Real/uninterpreted/Array-sorted ites into fresh `ite!<n>` symbols. Task 2 relies on those symbols appearing in the EUF/arith model (`mb`) and on `WordNorm::internal` containing them. Tasks 3–5 rely on the fixed verdicts.

- [ ] **Step 1: Write the failing e2e tests**

Create `crates/shinri-solver/tests/ite_e2e.rs`:

```rust
//! End-to-end verdict pins for non-word ite elimination (slice 10).
//!
//! Before slice 10, `(ite c x y)` over Int/Real/uninterpreted/Array sorts fell
//! through word_norm untouched and reached EUF as an OPAQUE application: the
//! condition was never linked to the branches, so e.g. pure QF_LRA
//! `(= (ite b 2.5 0.25) 1.0)` answered SAT (wrong — z3: unsat; the model even
//! valued `b` as an uninterpreted-sort element `@elem0`). word_norm now
//! eliminates those ites (slice-10 design §1/§2); these tests pin the correct
//! verdicts. Word-sorted ites (slice 5) and Bool/String ites are pinned
//! unchanged.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Drive a full SMT-LIB script; return the last check-sat outcome.
fn run(src: &str) -> SolveOutcome {
    let mut s = Solver::new();
    let mut p = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = p.next_command(s.ctx_mut()) {
        let cmd = result.expect("parse");
        match s.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

/// Pure QF_LRA: the ite can only be 2.5 or 0.25, never 1.0.
#[test]
fn lra_ite_neither_branch_unsat() {
    let o = run("(declare-fun b () Bool)\
                 (assert (= (ite b 2.5 0.25) 1.0))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// SAT twin: picking the then-branch is consistent.
#[test]
fn lra_ite_then_branch_sat() {
    let o = run("(declare-fun b () Bool)\
                 (assert (= (ite b 2.5 0.25) 2.5))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

/// Pure QF_LIA twin of the LRA pin.
#[test]
fn lia_ite_neither_branch_unsat() {
    let o = run("(declare-fun b () Bool)\
                 (assert (= (ite b 2 0) 1))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// ite nested inside arithmetic: (+ (ite b 2 0) 1) ∈ {3, 1}, never 2.
#[test]
fn lia_ite_nested_in_plus_unsat() {
    let o = run("(declare-fun b () Bool)(declare-fun y () Int)\
                 (assert (= (+ (ite b 2 0) 1) y))\
                 (assert (= y 2))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// Uninterpreted sort: ite over U with pairwise-distinct u1,u2,u3.
#[test]
fn usort_ite_neither_branch_unsat() {
    let o = run("(declare-sort U 0)\
                 (declare-fun b () Bool)\
                 (declare-fun u1 () U)(declare-fun u2 () U)(declare-fun u3 () U)\
                 (assert (distinct u1 u2 u3))\
                 (assert (= (ite b u1 u2) u3))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// SAT twin over U: the then-branch is consistent.
#[test]
fn usort_ite_then_branch_sat() {
    let o = run("(declare-sort U 0)\
                 (declare-fun b () Bool)\
                 (declare-fun u1 () U)(declare-fun u2 () U)\
                 (assert (distinct u1 u2))\
                 (assert (= (ite b u1 u2) u1))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

/// Array-sorted ite on the QF_ABV path: (ite b a1 a2) selects 1 or 2 at i,
/// never 3. Pre-slice-10 this was wrong-SAT on the VALIDATED ABV path.
#[test]
fn abv_array_ite_neither_branch_unsat() {
    let o = run("(declare-fun b () Bool)\
                 (declare-fun a1 () (Array (_ BitVec 8) (_ BitVec 8)))\
                 (declare-fun a2 () (Array (_ BitVec 8) (_ BitVec 8)))\
                 (declare-fun i () (_ BitVec 8))\
                 (assert (= (select a1 i) #x01))\
                 (assert (= (select a2 i) #x02))\
                 (assert (= (select (ite b a1 a2) i) #x03))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// SAT twin on ABV.
#[test]
fn abv_array_ite_then_branch_sat() {
    let o = run("(declare-fun b () Bool)\
                 (declare-fun a1 () (Array (_ BitVec 8) (_ BitVec 8)))\
                 (declare-fun a2 () (Array (_ BitVec 8) (_ BitVec 8)))\
                 (declare-fun i () (_ BitVec 8))\
                 (assert (= (select a1 i) #x01))\
                 (assert (= (select a2 i) #x02))\
                 (assert (= (select (ite b a1 a2) i) #x01))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

/// REGRESSION PIN (correct before slice 10 too): the string path already
/// self-eliminates arith ites in shinri-str reduce_assertions (design §1.1
/// item 2). word_norm now does it first; the verdict must stay correct.
#[test]
fn string_path_arith_ite_stays_unsat() {
    let o = run("(declare-fun s () String)\
                 (assert (= (ite (= s \"a\") 2.5 0.25) 1.0))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// REGRESSION PIN: Bool-sorted ite is plain Boolean structure (Tseitin) and
/// must NOT be eliminated — b false forces the else-branch q, but q is false.
#[test]
fn bool_ite_stays_correct_unsat() {
    let o = run("(declare-fun b () Bool)(declare-fun p () Bool)(declare-fun q () Bool)\
                 (assert p)(assert (not q))\
                 (assert (ite b p q))\
                 (assert (not b))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// REGRESSION PIN: String-sorted ite (excluded from the broadened gate) keeps
/// its correct verdict via the existing path.
#[test]
fn string_sorted_ite_stays_unsat() {
    let o = run("(declare-fun b () Bool)\
                 (assert (= (ite b \"aa\" \"bb\") \"cc\"))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}
```

- [ ] **Step 2: Run the new tests to verify the right ones fail**

Run: `cargo test -p shinri-solver --test ite_e2e`
Expected: FAIL — exactly these five assert `Unsat`/`Sat` mismatches (they get wrong-SAT or wrong verdicts today): `lra_ite_neither_branch_unsat`, `lia_ite_neither_branch_unsat`, `lia_ite_nested_in_plus_unsat`, `usort_ite_neither_branch_unsat`, `abv_array_ite_neither_branch_unsat`. The regression pins (`string_path_arith_ite_stays_unsat`, `bool_ite_stays_correct_unsat`, `string_sorted_ite_stays_unsat`) and the SAT twins must PASS already. If a "must pass already" test fails, STOP — the pre-flight picture is wrong; re-verify with the shinri CLI before touching code.

- [ ] **Step 3: Write the failing word_norm unit tests**

Append inside the existing `mod tests` in `crates/shinri-solver/src/word_norm.rs` (after `nested_ite_rewrites_bottom_up`, using the existing `bool_var` helper):

```rust
    fn real_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let s = ctx.real_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    /// Slice 10: Real-sorted ite is eliminated exactly like a word ite —
    /// rewritten atom (= w z) + appended definition (ite c (= w x) (= w y)).
    #[test]
    fn real_ite_becomes_fresh_var_plus_definition() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let z = real_var(&mut ctx, "z");
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, z]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2, "rewritten atom + definition");
        assert_eq!(wn.internal.len(), 1);
        let w = *wn.internal.iter().next().unwrap();
        let expect_atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, z]).unwrap();
        assert_eq!(out[0], expect_atom);
    }

    /// Slice 10: Int-sorted ite nested under arithmetic is eliminated.
    #[test]
    fn int_ite_under_plus_is_eliminated() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let int = ctx.int_sort();
        let xf = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let yf = ctx.declare_fun("y", &[], int);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[ite, x]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[sum, y]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
    }

    /// Slice 10: uninterpreted-sort ite is eliminated.
    #[test]
    fn usort_ite_is_eliminated() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let u = ctx.uninterpreted_sort("U");
        let af = ctx.declare_fun("a", &[], u);
        let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("b2", &[], u);
        let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, a, b]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, a]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
    }

    /// Slice 10: Array-sorted ite is eliminated (fixes the ABV-path wrong-SAT).
    #[test]
    fn array_ite_is_eliminated() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let idx = ctx.bv_sort(8);
        let elem = ctx.bv_sort(8);
        let arr = ctx.array_sort(idx, elem);
        let af = ctx.declare_fun("a1", &[], arr);
        let a1 = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("a2", &[], arr);
        let a2 = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, a1, a2]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, a1]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
    }

    /// Slice 10: a Real ite shared by two atoms mints ONE symbol + ONE deduped
    /// definition (same contract as shared_ite_and_repeated_calls_reuse_one_symbol).
    #[test]
    fn shared_real_ite_reuses_one_symbol() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let a1 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, x]).unwrap();
        let a2 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, y]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[a1, a2]);
        assert_eq!(wn.internal.len(), 1, "one ite term → one fresh symbol");
        assert_eq!(out.len(), 3, "two rewritten atoms + ONE deduped definition");
    }

    /// Slice 10 exclusion: String-sorted ite passes through UNTOUCHED (the
    /// string path's own reduce handles it — design §1.1 item 2). Original
    /// TermId must be preserved (no-change ⇒ same-TermId invariant).
    #[test]
    fn string_ite_passes_through_untouched() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let strs = ctx.string_sort();
        let af = ctx.declare_fun("s1", &[], strs);
        let s1 = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("s2", &[], strs);
        let s2 = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, s1, s2]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, s1]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "String ite must not be rewritten");
        assert!(wn.internal.is_empty());
    }

    /// Slice 10 exclusion: Bool-sorted ite passes through UNTOUCHED.
    #[test]
    fn bool_ite_passes_through_untouched() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let p = bool_var(&mut ctx, "p");
        let q = bool_var(&mut ctx, "q");
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, p, q]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[ite]);
        assert_eq!(out, vec![ite], "Bool ite must not be rewritten");
        assert!(wn.internal.is_empty());
    }
```

NOTE: verify the exact `Context` constructor names against `crates/shinri-core/src/context.rs` before compiling — the ones used above are `real_sort()`, `int_sort()`, `string_sort()`, `bv_sort(w)`, `array_sort(idx, elem)`, `uninterpreted_sort(name)`, and the arith op is `BuiltinOp::Add`. If a name differs (e.g. `mk_uninterpreted_sort`, or n-ary `Add` needs exactly 2 args), adapt the test to the real API — the asserted BEHAVIOR is the contract, not these helper spellings.

- [ ] **Step 4: Run the unit tests to verify the new ones fail**

Run: `cargo test -p shinri-solver --lib word_norm`
Expected: the five new elimination tests FAIL (`real_ite_becomes_fresh_var_plus_definition`, `int_ite_under_plus_is_eliminated`, `usort_ite_is_eliminated`, `array_ite_is_eliminated`, `shared_real_ite_reuses_one_symbol` — out.len() short, internal empty: no elimination happens for these sorts yet); the two pass-through tests and all pre-existing tests PASS.

- [ ] **Step 5: Broaden the gate**

In `crates/shinri-solver/src/word_norm.rs`, replace the `is_word_sort` function (lines 65–70) with:

```rust
/// Sorts whose ites word_norm ELIMINATES (fresh symbol + defining assertion).
/// Slice 5 covered the word sorts (BitVec/Float/RoundingMode) so the blasters
/// never see term-level ite. Slice 10 broadens to Int/Real/uninterpreted/
/// Array: those ites previously fell through to EUF as OPAQUE applications,
/// silently unlinking the condition from the branches — wrong-SAT on every
/// non-string path (design §1). Exclusions: Bool ite is plain Boolean
/// structure (Tseitin handles it); String ite is handled by the string path's
/// own reduce_assertions elimination (design §1.1 item 2) and is left
/// untouched to avoid disturbing a working, semi-decidable path.
fn eliminates_ite_sort(ctx: &Context, s: SortId) -> bool {
    !matches!(ctx.sort_node(s), SortNode::Bool | SortNode::String)
}
```

and change the gate at (previously) line 136 from

```rust
            Op::Builtin(BuiltinOp::Ite) if is_word_sort(ctx, ctx.sort_of(rebuilt)) => {
```

to

```rust
            Op::Builtin(BuiltinOp::Ite) if eliminates_ite_sort(ctx, ctx.sort_of(rebuilt)) => {
```

Also update the module doc header: item 1 (lines 5–9) now reads "ite elimination: `(ite c x y)` with any non-Bool, non-String sort …", and the invariant bullet at line 18 ("Other sorts (Bool/Int/Real/Array/String) pass through untouched EXCEPT …") must be rewritten to say only Bool and String ites pass through, n-ary `=`/`distinct` still expands for every sort.

- [ ] **Step 6: Run unit + e2e tests to verify they pass**

Run: `cargo test -p shinri-solver --lib word_norm && cargo test -p shinri-solver --test ite_e2e`
Expected: ALL PASS.

- [ ] **Step 7: Full-workspace canary net**

Run: `cargo test --workspace` (multi-minute; run in background and wait).
Expected: green. If a pre-existing test fails, it is a cross-slice canary pinned to old ite behavior — read it, decide with the slice-10 design in hand whether the pinned expectation is now simply correct-instead-of-wrong (repoint it, documenting the flip in the test comment, as slice 9 §8 did), and record the repoint in the commit message. Do NOT weaken a failing soundness pin to make it pass.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-solver/src/word_norm.rs crates/shinri-solver/tests/ite_e2e.rs
git commit -m "fix(solver): eliminate ite over Int/Real/uninterpreted/Array sorts in word_norm — closes EUF-opaque wrong-SAT on all non-string paths (slice 10)"
```

---

### Task 2: Route arith/EUF ite! values through the internal-symbol filter

After Task 1, `ite!<n>` symbols for Int/Real/U-sort ites are registered with EUF/arith, so the theory model `mb` now contains them. The two `mb`-based model-surfacing loops in `check_sat` have no `internal` filter (they predate this possibility), which (a) leaks `ite!` symbols into `get-model` and (b) never feeds `internal_vals`, so `get-value` on an eliminated arith ite degrades to no value.

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs:750-775` (the `SolveResult::Sat` arm of `check_sat`: `atom_vars` loop, `mb.iter()` loop, `internal_vals` declaration)
- Test: `crates/shinri-solver/tests/ite_e2e.rs` (append)

**Interfaces:**
- Consumes: Task 1's broadened elimination (`WordNorm::internal` contains arith/EUF `ite!` symbol terms).
- Produces: `get-value` on eliminated non-word ites answers from the theory model; `get-model` never shows `ite!` names. No API change.

- [ ] **Step 1: Write the failing tests**

Append to `crates/shinri-solver/tests/ite_e2e.rs`:

```rust
/// Like `run`, but returns (outcome, get-model string, get-value responses).
fn run_full(src: &str) -> (SolveOutcome, String, Vec<String>) {
    let mut s = Solver::new();
    let mut p = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    let mut values = Vec::new();
    while let Some(result) = p.next_command(s.ctx_mut()) {
        let cmd = result.expect("parse");
        match s.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            CommandResponse::Values(v) => values.push(v),
            _ => {}
        }
    }
    let model = s.get_model_string();
    (outcome, model, values)
}

/// Slice 10 model channel: get-value on an eliminated Int-sorted ite must
/// answer from the EUF/arith model. b is forced true, so the ite is 2.
#[test]
fn get_value_on_eliminated_int_ite_returns_branch_value() {
    let (o, _model, values) = run_full(
        "(declare-fun b () Bool)(declare-fun y () Int)\
         (assert b)\
         (assert (= y (ite b 2 0)))\
         (check-sat)(get-value ((ite b 2 0)))",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert_eq!(values.len(), 1);
    assert!(!values[0].contains("ite!"), "internal name leaked: {}", values[0]);
    assert!(!values[0].contains('?'), "no value produced: {}", values[0]);
    assert!(values[0].contains('2'), "expected branch value 2: {}", values[0]);
}

/// Slice 10 model channel: get-model must NOT leak internal ite! symbols
/// even though they now live in the EUF/arith model.
#[test]
fn get_model_does_not_leak_arith_ite_symbols() {
    let (o, model, _values) = run_full(
        "(declare-fun b () Bool)(declare-fun y () Int)\
         (assert b)\
         (assert (= y (ite b 2 0)))\
         (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(
        !model.contains("ite!"),
        "internal symbol leaked into get-model: {model}"
    );
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p shinri-solver --test ite_e2e get_value_on_eliminated_int_ite_returns_branch_value get_model_does_not_leak_arith_ite_symbols`
Expected: FAIL — get-value has no value (the `?` or missing-value branch) and/or get-model contains `ite!`. If BOTH pass already, re-read `lib.rs:750-775`; do not skip the fix without confirming the loops actually filter.

- [ ] **Step 3: Apply the filter**

In `crates/shinri-solver/src/lib.rs`, in the `SolveResult::Sat` arm: move the `internal_vals` declaration (currently at ~line 772, AFTER the two `mb` loops) up to just before the `atom_vars` loop (~line 753), and add the filter to both loops. The block from ~753–775 becomes:

```rust
                // Values of word_norm-internal symbols, keyed by the internal
                // term — surfaced to users only through the eliminated-ite
                // remap below, never through get-model (slice 6; slice 10
                // extends the filter to the EUF/arith model loops, since
                // eliminated Int/Real/U-sort ites register their ite! symbols
                // with EUF/arith and therefore appear in `mb`).
                let mut internal_vals: rustc_hash::FxHashMap<
                    TermId,
                    shinri_theory::types::ModelVal,
                > = rustc_hash::FxHashMap::default();
                for (_v, term) in &atom_vars {
                    if let Some(val) = mb.get(*term) {
                        if self.word_norm.internal.contains(term) {
                            internal_vals.insert(*term, val.clone());
                        } else {
                            model.values.insert(*term, val.clone());
                        }
                    }
                }
                // Also surface values for all terms assigned by the theories.
                // Skip terms that do not exist in the solver's own context: the
                // Combiner runs over a *clone* of the context and may mint fresh
                // terms (e.g. string-theory F-split skolems) whose TermIds are out
                // of range for `self.ctx`. Surfacing them would make `get-model` /
                // `display_term` index out of bounds.
                for (term, val) in mb.iter() {
                    if self.ctx.contains_term(term) {
                        if self.word_norm.internal.contains(&term) {
                            internal_vals.insert(term, val.clone());
                        } else {
                            model.values.insert(term, val.clone());
                        }
                    }
                }
```

and DELETE the old `internal_vals` declaration that followed (keep everything after it — the BV/FP/RM loops and the `ite_vals` remap consume `internal_vals` unchanged).

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test -p shinri-solver --test ite_e2e`
Expected: ALL PASS.

- [ ] **Step 5: Guard the neighbors**

Run: `cargo test -p shinri-solver --test fp_e2e --test qfbv_witnesses --test script_e2e`
Expected: PASS (these consume get-model/get-value; the word-sorted filter path must be unchanged).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/ite_e2e.rs
git commit -m "fix(solver): filter word_norm ite! symbols in the EUF/arith model loops — get-value answers eliminated arith ites, get-model stays clean (slice 10)"
```

---

### Task 3: z3 differential oracles for ite over the fixed sorts

Validation (not TDD): fuzzed LRA/LIA/UF ite scripts pinned against z3 with zero disagreements AND zero Unknowns (all three fragments are decidable and fully in-scope post-fix).

**Files:**
- Create: `crates/shinri-solver/tests/ite_oracle.rs`

**Interfaces:**
- Consumes: Tasks 1–2 (correct verdicts).
- Produces: nothing downstream; a permanent regression oracle.

- [ ] **Step 1: Write the oracle file**

Create `crates/shinri-solver/tests/ite_oracle.rs`:

```rust
//! Differential oracle: shinri vs z3 on ite over Int/Real/uninterpreted sorts
//! (slice 10 — the EUF-opaque ite wrong-SAT family; no prior oracle fuzzed
//! term-level ite over these sorts). Requires z3 on PATH.
//!
//! Run with:
//!   cargo test -p shinri-solver --features oracle --test ite_oracle -- --nocapture
//!
//! All three fragments (QF_LRA / QF_LIA / QF_UF with ite) are decidable and
//! admitted post-slice-10, so Unknown is NOT tolerated and both SAT and UNSAT
//! witnesses must arise.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand.
/// Copied verbatim from tests/nary_oracle.rs to match the existing convention.
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

fn shinri_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
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

/// Forward declare-sort/declare-fun/assert lines to z3 under `logic`.
fn z3_outcome(ctx: &mut easy_smt::Context, logic: &str, src: &str) -> easy_smt::Response {
    ctx.set_logic(logic).expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-sort ")
            || t.starts_with("(declare-fun ")
            || t.starts_with("(assert ")
        {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

fn z3_ctx() -> easy_smt::Context {
    easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()
        .expect("failed to launch z3 — ensure z3 is on PATH")
}

fn assert_no_disagreement(
    ours: SolveOutcome,
    theirs: easy_smt::Response,
    family: &str,
    iter: usize,
    s: &str,
) {
    assert!(
        !matches!(
            (ours, theirs),
            (SolveOutcome::Sat, easy_smt::Response::Unsat)
                | (SolveOutcome::Unsat, easy_smt::Response::Sat)
        ),
        "{family} ite DISAGREEMENT (iter {iter}): shinri={ours:?} z3={theirs:?}\n{s}"
    );
}

/// Real-sorted ite: (ite b c1 c2) compared against a bound, with the
/// condition sometimes pinned so both branches get exercised.
fn gen_lra_ite_script(rng: &mut Lcg) -> String {
    let consts = ["0.25", "1.0", "2.5", "4.0"];
    let c1 = consts[rng.below(consts.len() as u64) as usize];
    let c2 = consts[rng.below(consts.len() as u64) as usize];
    let bound = consts[rng.below(consts.len() as u64) as usize];
    let ops = ["<=", "<", ">=", ">", "="];
    let op = ops[rng.below(ops.len() as u64) as usize];
    let mut s = String::from("(declare-fun b () Bool)\n");
    s.push_str(&format!("(assert ({op} (ite b {c1} {c2}) {bound}))\n"));
    match rng.below(3) {
        0 => s.push_str("(assert b)\n"),
        1 => s.push_str("(assert (not b))\n"),
        _ => {}
    }
    s.push_str("(check-sat)\n");
    s
}

/// Int-sorted ite nested under +, compared against a bound.
fn gen_lia_ite_script(rng: &mut Lcg) -> String {
    let c1 = rng.below(5) as i64;
    let c2 = rng.below(5) as i64;
    let add = rng.below(3) as i64;
    let bound = rng.below(8) as i64;
    let ops = ["<=", "<", ">=", ">", "="];
    let op = ops[rng.below(ops.len() as u64) as usize];
    let mut s = String::from("(declare-fun b () Bool)\n");
    s.push_str(&format!(
        "(assert ({op} (+ (ite b {c1} {c2}) {add}) {bound}))\n"
    ));
    match rng.below(3) {
        0 => s.push_str("(assert b)\n"),
        1 => s.push_str("(assert (not b))\n"),
        _ => {}
    }
    s.push_str("(check-sat)\n");
    s
}

/// Uninterpreted-sort ite among 3 constants with random (dis)equalities.
fn gen_uf_ite_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(declare-sort U 0)\n\
         (declare-fun b () Bool)\n\
         (declare-fun u1 () U)\n\
         (declare-fun u2 () U)\n\
         (declare-fun u3 () U)\n",
    );
    let rhs = ["u1", "u2", "u3"][rng.below(3) as usize];
    s.push_str(&format!("(assert (= (ite b u1 u2) {rhs}))\n"));
    match rng.below(4) {
        0 => s.push_str("(assert (distinct u1 u2 u3))\n"),
        1 => s.push_str("(assert (distinct u1 u2))\n"),
        2 => s.push_str("(assert (= u1 u2))\n"),
        _ => {}
    }
    match rng.below(3) {
        0 => s.push_str("(assert b)\n"),
        1 => s.push_str("(assert (not b))\n"),
        _ => {}
    }
    s.push_str("(check-sat)\n");
    s
}

fn run_family(
    family: &str,
    logic: &str,
    seed: u64,
    gen: fn(&mut Lcg) -> String,
) {
    let mut rng = Lcg(seed);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let s = gen(&mut rng);
        let ours = shinri_outcome(&s);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => n_unknown += 1,
        }
        let mut ctx = z3_ctx();
        let theirs = z3_outcome(&mut ctx, logic, &s);
        assert_no_disagreement(ours, theirs, family, iter, &s);
    }
    println!("{family}: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(
        n_sat > 0 && n_unsat > 0,
        "{family} produced no SAT/UNSAT coverage (sat={n_sat} unsat={n_unsat})"
    );
    assert_eq!(
        n_unknown, 0,
        "{family}: decidable ite fragment must never fence ({n_unknown})"
    );
}

#[test]
fn differential_qf_lra_ite() {
    run_family("differential_qf_lra_ite", "QF_LRA", 0x517E_0A11_D00D, gen_lra_ite_script);
}

#[test]
fn differential_qf_lia_ite() {
    run_family("differential_qf_lia_ite", "QF_LIA", 0x517E_0B22_FEED, gen_lia_ite_script);
}

#[test]
fn differential_qf_uf_ite() {
    run_family("differential_qf_uf_ite", "QF_UF", 0x517E_0C33_CAFE, gen_uf_ite_script);
}
```

- [ ] **Step 2: Run the oracles**

Run (background, multi-minute): `cargo test -p shinri-solver --features oracle --test ite_oracle -- --nocapture`
Expected: 3 passed; each family prints nonzero sat AND unsat, unknown=0, no disagreements. On a disagreement: STOP and debug with superpowers:systematic-debugging — the panic message embeds the full script; minimize it with the shinri CLI (`/workspace/target/release/shinri <file>` — read EVERY line of output; the CLI prints per-command `(error …)` and continues, so a dropped assert masquerades as a wrong verdict).

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/ite_oracle.rs
git commit -m "test(solver): z3 differential oracles for ite over LRA/LIA/UF — 0 disagreements, 0 unknown (slice 10)"
```

---

### Task 4: Phase-2 bridge canary pins (flip-markers)

Pin today's sound `Unknown` fences at the Array/Str × bridge seam. These are the tests a future fence-lift slice will consciously flip (per the cross-slice canary discipline).

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` (append; uses the existing `run` helper at line 7)

**Interfaces:**
- Consumes: existing `run(src) -> (SolveOutcome, String)` helper in fp_e2e.rs.
- Produces: nothing downstream; canaries.

- [ ] **Step 1: Write the canary tests**

Append to `crates/shinri-solver/tests/fp_e2e.rs`:

```rust
// ── Slice-10 §3 canary pins: Array/Str × fp.to_real bridge fences ──────────
// These pin the CURRENT sound-Unknown behavior at the bridge seam (slice-10
// design §1/§1.1). They are FLIP-MARKERS: a future slice that decides
// Array-Real or Str-Real bridge operands must consciously repoint them to
// Sat/Unsat. Companion coverage: the unknown-tolerant differential families
// in fp_oracle.rs (differential_qf_fp_to_real_array / _str).

/// Array-Real operand + bridge: bridge_admissible ACCEPTS this shape, but the
/// downstream combined solve does not decide Real-valued arrays → Unknown.
#[test]
fn array_real_bridge_operand_fences_unknown() {
    let (o, _) = run(
        "(declare-fun x () Float16)\
         (declare-fun arr () (Array Int Real))\
         (declare-fun i () Int)\
         (assert (= x (fp #b0 #b01111 #b0000000000)))\
         (assert (= (select arr i) (fp.to_real x)))\
         (assert (> (select arr i) 0.5))\
         (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}

/// Pure (Array Int Real), no FP at all: Real-valued arrays are broadly
/// undecided today (this is why the bridge case above fences, not the bridge).
#[test]
fn pure_array_real_fences_unknown() {
    let (o, _) = run(
        "(declare-fun arr () (Array Int Real))\
         (assert (= (select (store arr 0 2.5) 0) 1.0))\
         (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}

/// Str-Real EUF operand + bridge: fenced UPSTREAM by string_stage::fenced
/// (uninterpreted function with a String argument), before the bridge
/// recognizer ever runs.
#[test]
fn str_real_euf_bridge_operand_fences_unknown() {
    let (o, _) = run(
        "(declare-fun x () Float16)\
         (declare-fun g (String) Real)\
         (declare-fun s () String)\
         (assert (= x (fp #b0 #b01111 #b0000000000)))\
         (assert (= (g s) (fp.to_real x)))\
         (assert (> (g s) 0.5))\
         (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}

/// Str-eq-conditioned Real ite + bridge: after slice-10 elimination the
/// str-eq atom still fails is_lra_real_atom, so bridge_admissible rejects →
/// sound Unknown (design §1.1 item 3). x = 1.0 and the ite ∈ {2.5, 0.25}, so
/// a future deciding slice must flip this to Unsat.
#[test]
fn str_eq_ite_bridge_fences_unknown() {
    let (o, _) = run(
        "(declare-fun x () Float16)\
         (declare-fun s () String)\
         (assert (= x (fp #b0 #b01111 #b0000000000)))\
         (assert (= (ite (= s \"a\") 2.5 0.25) (fp.to_real x)))\
         (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}
```

- [ ] **Step 2: Run them**

Run: `cargo test -p shinri-solver --test fp_e2e array_real_bridge pure_array_real str_real_euf str_eq_ite_bridge`
Expected: 4 passed. If any returns Sat/Unsat instead of Unknown, the pre-flight picture changed under you (Tasks 1–2 may have widened what the seam decides) — verify the verdict against z3 with the shinri CLI before repinning: a z3-agreeing decided verdict means pin THAT (and note the flip in the test comment); a disagreement is a soundness bug — STOP and debug.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(solver): canary pins for Array/Str x fp.to_real bridge sound-Unknown fences (slice 10)"
```

---

### Task 5: Phase-2 differential oracle families (unknown-tolerant)

The slice-9 follow-up proper: fuzzed Array+bridge and Str+bridge scripts pinned against z3. Zero disagreements; Unknowns tolerated and counted (these families are fenced today — the Task-4 canaries carry the exact pins; the oracle stays valid unchanged when a future slice lifts the fences).

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (append at end; add one helper next to `z3_outcome_arith` at line ~139)

**Interfaces:**
- Consumes: existing `Lcg`, `N_ITERS`, `shinri_outcome` in fp_oracle.rs.
- Produces: nothing downstream; permanent seam guard.

- [ ] **Step 1: Add the logic-parameterized z3 helper and delegate the existing one**

In `crates/shinri-solver/tests/fp_oracle.rs`, replace the body of `z3_outcome_arith` (lines 139–150) with a delegation and add the general helper:

```rust
fn z3_outcome_arith(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    z3_outcome_logic(ctx, "QF_FP", src)
}

/// Like `z3_outcome_arith` but with an explicit logic — the slice-10 bridge
/// families declare (Array Int Real) / String symbols, which z3 rejects under
/// QF_FP; they run under ALL.
fn z3_outcome_logic(
    ctx: &mut easy_smt::Context,
    logic: &str,
    src: &str,
) -> easy_smt::Response {
    ctx.set_logic(logic).expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-fun ") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}
```

- [ ] **Step 2: Add the generators and tests**

Append to `crates/shinri-solver/tests/fp_oracle.rs`:

```rust
/// Slice-10 §3: Array-Real operand mixed with the fp.to_real bridge. The
/// recognizer admits these shapes but the combined solve does not decide
/// Real-valued arrays (design §1) — expected all-Unknown today. Contract:
/// ZERO disagreements; Unknowns tolerated and counted; NO coverage assertion
/// (the fp_e2e canaries carry the exact Unknown pins), so this oracle keeps
/// guarding the seam unchanged when a later slice lifts the fence.
#[cfg(feature = "oracle")]
fn gen_to_real_array_script(rng: &mut Lcg) -> String {
    let bits = (rng.next() & 0xFFFF) as u16;
    let s = (bits >> 15) & 1;
    let e = (bits >> 10) & 0x1F;
    let sig = bits & 0x3FF;
    let bound = (rng.next() % 21) as i64 - 10;
    let bound_term = if bound < 0 {
        format!("(- {}.0)", -bound)
    } else {
        format!("{bound}.0")
    };
    let ops = ["<=", "<", ">=", ">", "="];
    let op = ops[(rng.next() % ops.len() as u64) as usize];
    // Half the corpus reads through a store at a random index.
    let sel = if rng.next() % 2 == 0 {
        "(select arr i)".to_string()
    } else {
        let k = rng.next() % 4;
        format!("(select (store arr {k} {bound_term}) i)")
    };
    format!(
        "(declare-fun x () Float16)\n\
         (declare-fun arr () (Array Int Real))\n\
         (declare-fun i () Int)\n\
         (assert (= x (fp #b{s:01b} #b{e:05b} #b{sig:010b})))\n\
         (assert (= {sel} (fp.to_real x)))\n\
         (assert ({op} {sel} {bound_term}))\n\
         (check-sat)\n"
    )
}

#[cfg(feature = "oracle")]
#[test]
fn differential_qf_fp_to_real_array() {
    let mut rng = Lcg(0xA88A_5EED_0A10);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let s = gen_to_real_array_script(&mut rng);
        let ours = shinri_outcome(&s);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => n_unknown += 1,
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_logic(&mut ctx, "ALL", &s);
        assert!(
            !matches!(
                (ours, theirs),
                (SolveOutcome::Sat, easy_smt::Response::Unsat)
                    | (SolveOutcome::Unsat, easy_smt::Response::Sat)
            ),
            "Array+bridge DISAGREEMENT (iter {iter}): shinri={ours:?} z3={theirs:?}\n{s}"
        );
    }
    println!("differential_qf_fp_to_real_array: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
}

/// Slice-10 §3: String-Real EUF operand mixed with the bridge, using
/// SUPPORTED string ops only (eq/distinct over literals, concat, str.len —
/// design §1.1 item 5; prefixof/suffixof/contains are unimplemented and
/// would panic the parse-strict harness). Fenced upstream today
/// (string_stage::fenced condition 1) — expected all-Unknown. Same contract
/// as the array family.
#[cfg(feature = "oracle")]
fn gen_to_real_str_script(rng: &mut Lcg) -> String {
    let bits = (rng.next() & 0xFFFF) as u16;
    let s_bit = (bits >> 15) & 1;
    let e = (bits >> 10) & 0x1F;
    let sig = bits & 0x3FF;
    let bound = (rng.next() % 21) as i64 - 10;
    let bound_term = if bound < 0 {
        format!("(- {}.0)", -bound)
    } else {
        format!("{bound}.0")
    };
    let ops = ["<=", "<", ">=", ">", "="];
    let op = ops[(rng.next() % ops.len() as u64) as usize];
    let lits = ["\"a\"", "\"ab\"", "\"\"", "\"ba\""];
    let lit = lits[(rng.next() % lits.len() as u64) as usize];
    let str_atom = match rng.next() % 3 {
        0 => format!("(= s {lit})"),
        1 => format!("(distinct s {lit})"),
        _ => format!("(= (str.len s) {})", rng.next() % 4),
    };
    format!(
        "(declare-fun x () Float16)\n\
         (declare-fun g (String) Real)\n\
         (declare-fun s () String)\n\
         (assert (= x (fp #b{s_bit:01b} #b{e:05b} #b{sig:010b})))\n\
         (assert (= (g s) (fp.to_real x)))\n\
         (assert ({op} (g s) {bound_term}))\n\
         (assert {str_atom})\n\
         (check-sat)\n"
    )
}

#[cfg(feature = "oracle")]
#[test]
fn differential_qf_fp_to_real_str() {
    let mut rng = Lcg(0xA88A_5EED_0B20);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let s = gen_to_real_str_script(&mut rng);
        let ours = shinri_outcome(&s);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => n_unknown += 1,
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_logic(&mut ctx, "ALL", &s);
        assert!(
            !matches!(
                (ours, theirs),
                (SolveOutcome::Sat, easy_smt::Response::Unsat)
                    | (SolveOutcome::Unsat, easy_smt::Response::Sat)
            ),
            "Str+bridge DISAGREEMENT (iter {iter}): shinri={ours:?} z3={theirs:?}\n{s}"
        );
    }
    println!("differential_qf_fp_to_real_str: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
}
```

- [ ] **Step 3: Run the two new oracles plus the existing bridge oracles**

Run (background, multi-minute): `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_to_real -- --nocapture`
Expected: the two new tests pass with 0 disagreements (unknown counts will be ≈N_ITERS — that is expected and fine); the four pre-existing `differential_qf_fp_to_real*` tests still pass (the `z3_outcome_arith` delegation must be behavior-identical). On a disagreement: STOP — that is a live soundness bug at the seam; debug before proceeding.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(solver): z3 differential oracles for Array/Str x fp.to_real bridge (0 disagreements, unknown-tolerant) — closes slice-9 follow-up (slice 10)"
```

---

### Task 6: Spec truth-up + full verification gates

**Files:**
- Modify: `docs/superpowers/specs/2026-07-04-shinri-qffp-slice9-real-bridge-seam-design.md` (Status header, lines 12–15)
- Modify: `docs/superpowers/specs/2026-07-06-shinri-slice10-ite-soundness-bridge-coverage-design.md` (Status header)

**Interfaces:** none — documentation and verification only.

- [ ] **Step 1: Correct the slice-9 Status follow-up note**

In `docs/superpowers/specs/2026-07-04-shinri-qffp-slice9-real-bridge-seam-design.md`, replace the sentence spanning lines 12–15:

```
                                            **FOLLOW-UP:** the Real-sorted
recognizer also admits Array/Str-Real bridge operands (structurally the same
shared-Real case as the validated EUF path) but they lack dedicated differential
coverage — add an Array/Str+bridge oracle in a later slice.
```

with:

```
                                            **FOLLOW-UP (closed by slice 10):**
the Real-sorted recognizer admits Array-Real bridge operands but the combined
solve does not decide Real-valued arrays (sound Unknown), and Str-Real EUF
operands are fenced upstream by the string stage — the original "structurally
the same as the validated EUF path" assumption did not hold end-to-end. Slice
10 pinned these fences (fp_e2e canaries) and added unknown-tolerant z3
differential families (differential_qf_fp_to_real_array/_str), and separately
found+fixed a pre-existing non-string-path wrong-SAT for ite over
Int/Real/uninterpreted/Array sorts (see the slice-10 design doc).
```

- [ ] **Step 2: Update the slice-10 spec Status header**

In the slice-10 design doc, change the `Status:` line to:

```
Status: IMPLEMENTED (slice 10 landed). word_norm eliminates ite over every
sort except Bool/String (wrong-SAT closed on LRA/LIA/UF/ABV paths, z3
differential-validated 3×200 @ 0 unknown); arith/EUF ite! model channel
filtered; Array/Str×bridge fences pinned + unknown-tolerant oracles added.
```

- [ ] **Step 3: Run the full verification gates**

Run each, in the background where multi-minute, and read the actual output:

```bash
cargo fmt --all -- --check
# Clippy warm-cache false-pass guard: force the changed crates to recompile.
touch crates/shinri-solver/src/lib.rs crates/shinri-solver/src/word_norm.rs
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo test -p shinri-solver --features oracle --test ite_oracle --test fp_oracle -- --nocapture
```

Expected: all green, 0 clippy warnings, oracle families report 0 disagreements. Fix anything red before committing (fmt nits: run `cargo fmt --all`).

- [ ] **Step 4: Commit**

```bash
git add docs/superpowers/specs/2026-07-04-shinri-qffp-slice9-real-bridge-seam-design.md docs/superpowers/specs/2026-07-06-shinri-slice10-ite-soundness-bridge-coverage-design.md
git commit -m "docs(qffp): close slice-9 Array/Str+bridge follow-up + sync slice-10 spec Status to implemented (slice 10)"
```

---

## Post-plan notes for the executor

- **Branch:** create `slice-10-ite-soundness-bridge-coverage` off `main` before Task 1 (the repo lands slices via PR; see slice 9 / PR #2).
- **Debugging aid:** `cargo build -p shinri-cli --release` gives `/workspace/target/release/shinri <file.smt2>` for quick probes. READ EVERY OUTPUT LINE — the CLI prints `(error …)` for a failed command and continues, so a dropped assert silently changes the verdict (this exact trap produced false findings during pre-flight; design §1.1).
- **Known-good probe corpus:** the pre-flight scripts live in the session scratchpad and are reproduced inline in the tests above; the tests are the durable form.
