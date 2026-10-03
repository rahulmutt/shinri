# Slice 56 — Atomic Bool constants as UF arguments Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the wrong `sat` where a nullary user Bool constant used only as an argument of a non-connective parent (`(P q)`, `(mk q)`) is never tied to `true`/`false`.

**Architecture:** `word_norm`'s slice-54 item 3 (the loop over a non-connective parent's arguments) gains a second branch: a nullary, non-internal, Bool-sorted argument `k` stays in place and the definition `(or k (not k))` is appended once per `normalize` call. The tautology makes Tseitin encode `k` as a SAT atom, so SAT decides it and EUF's existing ⊤/⊥ merge links `(P k)` to `(P true)`/`(P false)` by congruence. No term rewrite, no new symbol.

**Tech Stack:** Rust (workspace, toolchain pinned in `mise.toml`), cargo-nextest 0.9.140, z3 (from mise) for the oracle, `shinri-bench` for the SMT-LIB 2024 run.

**Spec:** `docs/superpowers/specs/2026-10-02-shinri-slice56-uf-bool-const-arg-design.md`

## Global Constraints

- Code change is confined to `crates/shinri-solver/src/word_norm.rs`. No parser, `lower`, Tseitin, EUF, Combiner, fence, theory-crate, printer or `get-value`/`get-model` change (spec §4).
- The slice-54 proxy rule (`needs_bool_proxy`) is unchanged in behaviour.
- No term rewrite: an assertion whose only change is the new definition keeps its identical `TermId`; nothing new is added to `orig_rewrite` or `internal` (spec §3.2).
- Each constant gets at most one `(or k (not k))` per `normalize` call, deduped through the existing `seen_defs` (spec §3.2).
- Bench: logics QF_UF, QF_DT, QF_UFLIA, QF_UFLRA; `--timeout 20 --mem-mb 3072 --jobs 6`; detached under `taskset -c 12-23`; base is `bench/results/slice55/` (binary `target/slice55-after/shinri`, md5 `6a753b2e1c088e0eefefc0a5ae4b1b38`) (spec §7).
- Oracle tests only run with `--features oracle`; without it they silently run 0 tests. Always confirm a non-zero discovered count (AGENTS.md).
- nextest filters use the expression form: `-E 'test(<name>)'` or `-E 'binary(<name>)'` (AGENTS.md).
- Run `cargo fmt --all` before every commit; `mise run lint` (clippy `-D warnings`) must be clean.
- Branch: `slice56-uf-bool-const-arg` off `main`; PR to `main`, merge commit after CI is green (AGENTS.md).

## Review Focus

1. **QF_SLIA header** — `(P q)`, `(not (P true))`, `(not (P false))` with a string assertion alongside: z3 `unsat`, shinri at `1a9db04` `sat`. Must not be `sat` after the fix (`unsat`, or `unknown` from the string model gate). Pinned in Task 1 (`rf1_string_logic_header`).
2. **QF_UFBV header with no BV term** — a1 under `QF_UFBV`: z3 `unsat`, shinri `sat` today. Must not be `sat`. With a BV term present the fence answers `unknown` today; that must not turn into `sat`. Pinned in Task 1 (`rf2_ufbv_header_*`).
3. **Bool array index** — `(distinct (select a q) (select a true) (select a false))`, `a : (Array Bool Int)`, QF_AUFLIA: z3 `unsat`, shinri `unknown` (fenced). Must never become `sat`. Pinned in Task 1 (`rf3_bool_index_array_not_sat`).
4. **Constant both bare and negated as arguments** — `(P q)` and `(P (not q))`: `(not q)` is proxied (slice 54), `q` gets the new definition; both must agree. Today `unsat` (z3 `unsat`); must stay `unsat`. Pinned in Task 1 (`rf4_bare_and_negated_argument`).
5. **A user symbol literally named `bool!0`, declared before any mint, used as a bare argument** — it is not in `internal`, so it must get the definition (it is a user constant, not a proxy). Pinned in Task 1's unit test.

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-solver/src/word_norm.rs` | Modify | New `WordNorm::needs_excluded_middle` + `WordNorm::excluded_middle`; second branch in `walk` item 3; doc fixes; unit tests |
| `crates/shinri-solver/tests/slice56_probes.rs` | Create | End-to-end probes a1–a8 and Review Focus 1–4 |
| `crates/shinri-solver/tests/bool_arg_oracle.rs` | Modify | Drop the Ruling-8 `@` exclusion; add an argument-only Bool constant `s` to every family |
| `docs/superpowers/research/2026-10-0X-smtlib-2024-slice56-uf-bool-const-report.md` | Create | Bench report and carried queue |
| `docs/superpowers/specs/2026-10-02-shinri-slice56-uf-bool-const-arg-design.md` | Modify | §11 *Measured outcomes* |

---

### Task 0: Branch

- [ ] **Step 1: Create the slice branch**

```bash
cd /workspace && git checkout main && git pull --ff-only && git checkout -b slice56-uf-bool-const-arg
```

---

### Task 1: Excluded-middle definition for atomic Bool arguments (probes, unit tests, fix)

**Files:**
- Create: `crates/shinri-solver/tests/slice56_probes.rs`
- Modify: `crates/shinri-solver/src/word_norm.rs` (module doc item 3 at ~lines 15–24; `needs_bool_proxy` doc at ~123–125; `walk` item-3 loop at ~221–228; new methods next to `bool_proxy` at ~177; test module: update `bare_constants_and_connective_children_are_not_purified` at ~804, add one test)

**Interfaces:**
- Consumes: `WordNorm { internal: FxHashSet<TermId>, .. }`, `WordNorm::bool_proxy`, `needs_bool_proxy(ctx, t)`, `is_bool_connective(op)` (all existing, `word_norm.rs`).
- Produces:
  - `fn needs_excluded_middle(&self, ctx: &Context, t: TermId) -> bool` (private method on `WordNorm`)
  - `fn excluded_middle(&self, ctx: &mut Context, k: TermId, defs: &mut Vec<TermId>, seen_defs: &mut FxHashSet<TermId>)` (private method on `WordNorm`)
  - Observable: `WordNorm::normalize` output gains `(or k (not k))` (built as `mk_app(Or, [k, mk_app(Not, [k])])`) after the rewritten assertions, alongside the other definitions.

- [ ] **Step 1: Write the failing end-to-end probes**

Create `crates/shinri-solver/tests/slice56_probes.rs`:

```rust
//! Slice 56 probes (spec §6.2). A nullary user Bool constant used only as an
//! argument of a non-connective parent (UF, datatype constructor) was never a
//! SAT atom, so EUF never merged it with ⊤/⊥ and `(P q)`, `(P true)`,
//! `(P false)` could take three different values (wrong `sat`; `get-model`
//! bound `q` to `@elem0`). `word_norm` now appends `(or q (not q))` for such
//! an argument. Every `unsat` case answered `sat` at `1a9db04`; each `pair`
//! has a `sat` sibling so the fix cannot pass by over-refuting.
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

const UF: &str = "(set-logic QF_UF)(declare-sort U 0)(declare-fun q () Bool)\
    (declare-fun r () Bool)(declare-fun P (Bool) Bool)(declare-fun P2 (Bool Bool) Bool)\
    (declare-fun g (Bool) U)";
const UFLIA: &str =
    "(set-logic QF_UFLIA)(declare-fun q () Bool)(declare-fun f (Bool) Int)";
const UFLRA: &str =
    "(set-logic QF_UFLRA)(declare-fun q () Bool)(declare-fun f (Bool) Real)";
const DT: &str = "(set-logic QF_DT)(declare-datatypes ((B 0)) (((mk (fld Bool)))))\
    (declare-fun q () Bool)";

/// a1's three assertions over `P` and `q`.
const A1: &str = "(assert (P q))(assert (not (P true)))(assert (not (P false)))";

fn verdict(header: &str, body: &str) -> String {
    let out = run_script(&format!("{header}{body}(check-sat)"));
    out.first().cloned().unwrap_or_default()
}

/// Asserts `body` is unsat and `sibling` (one constraint relaxed) is sat.
fn pair(header: &str, body: &str, sibling: &str) {
    assert_eq!(verdict(header, body), "unsat", "{header}{body}");
    assert_eq!(verdict(header, sibling), "sat", "{header}{sibling}");
}

// ── spec §1.2 ──────────────────────────────────────────────────────────────

/// a1 — the slice-55 report's reproducer. HEAD: sat; z3: unsat.
#[test]
fn a1_bare_constant_uf_argument() {
    pair(UF, A1, "(assert (P q))(assert (not (P true)))");
}

/// a2 — Int-valued UF over the constant. HEAD: sat; z3: unsat.
#[test]
fn a2_int_valued_uf() {
    pair(
        UFLIA,
        "(assert (distinct (f q) (f true) (f false)))",
        "(assert (distinct (f q) (f true)))",
    );
}

/// a3 — uninterpreted-sort-valued UF. HEAD: sat; z3: unsat.
#[test]
fn a3_usort_valued_uf() {
    pair(
        UF,
        "(assert (distinct (g q) (g true) (g false)))",
        "(assert (distinct (g q) (g true)))",
    );
}

/// a4 — multi-argument UF, second argument pinned by an atom. HEAD: sat; z3: unsat.
#[test]
fn a4_multi_argument_uf() {
    pair(
        UF,
        "(assert (P2 q r))(assert (not (P2 true true)))(assert (not (P2 false true)))(assert r)",
        "(assert (P2 q r))(assert (not (P2 true true)))(assert (not (P2 false true)))",
    );
}

/// a5 — datatype constructor argument. HEAD: sat; z3: unsat.
#[test]
fn a5_datatype_constructor_argument() {
    pair(
        DT,
        "(assert (distinct (mk q) (mk true) (mk false)))",
        "(assert (distinct (mk q) (mk true)))",
    );
}

/// a6 — Real-valued UF. HEAD: sat; z3: unsat.
#[test]
fn a6_real_valued_uf() {
    pair(
        UFLRA,
        "(assert (distinct (f q) (f true) (f false)))",
        "(assert (distinct (f q) (f true)))",
    );
}

/// a7 — completeness side and model. HEAD: sat with `((q @elem0))`;
/// z3: sat with `((q false))`. Also pins that the tautology is not folded
/// away anywhere downstream (if it were, `q` would print `@elem0` again).
#[test]
fn a7_model_binds_constant_to_false() {
    let out = run_script(&format!(
        "(set-option :produce-models true){UF}(assert (P q))(assert (not (P true)))\
         (check-sat)(get-value (q))(get-model)"
    ));
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "((q false))");
    assert!(
        out[2].contains("(define-fun q () Bool false)"),
        "{:?}",
        out[2]
    );
    assert!(!out[2].contains('@'), "abstract value in get-model: {:?}", out[2]);
}

/// a8 — incremental: the definition is re-emitted after `pop`.
/// HEAD: sat sat sat; z3: unsat sat unsat.
#[test]
fn a8_push_pop_reemits_definition() {
    let out = run_script(&format!(
        "{UF}(push 1){A1}(check-sat)(pop 1)(check-sat){A1}(check-sat)"
    ));
    assert_eq!(out, vec!["unsat", "sat", "unsat"]);
}

// ── Review Focus ───────────────────────────────────────────────────────────

/// Review Focus 1. HEAD: sat; z3: unsat. `unknown` is acceptable (string
/// model gate).
#[test]
fn rf1_string_logic_header() {
    let v = verdict(
        "(set-logic QF_SLIA)(declare-fun q () Bool)(declare-fun s () String)\
         (declare-fun P (Bool) Bool)(assert (= s \"ab\"))",
        A1,
    );
    assert_ne!(v, "sat");
}

/// Review Focus 2a. HEAD: sat; z3: unsat. No BV term, so no fence.
#[test]
fn rf2_ufbv_header_without_bv_term() {
    let v = verdict(
        "(set-logic QF_UFBV)(declare-fun q () Bool)(declare-fun P (Bool) Bool)",
        A1,
    );
    assert_ne!(v, "sat");
}

/// Review Focus 2b. HEAD: unknown (fenced); z3: unsat. Must not become sat.
#[test]
fn rf2_ufbv_header_with_bv_term() {
    let v = verdict(
        "(set-logic QF_UFBV)(declare-fun q () Bool)(declare-fun v () (_ BitVec 4))\
         (declare-fun P (Bool) Bool)(assert (= v #x1))",
        A1,
    );
    assert_ne!(v, "sat");
}

/// Review Focus 3. HEAD: unknown (fenced); z3: unsat. Must not become sat.
#[test]
fn rf3_bool_index_array_not_sat() {
    let v = verdict(
        "(set-logic QF_AUFLIA)(declare-fun q () Bool)(declare-fun a () (Array Bool Int))",
        "(assert (distinct (select a q) (select a true) (select a false)))",
    );
    assert_ne!(v, "sat");
}

/// Review Focus 4. Regression pin (HEAD: unsat; z3: unsat): `(not q)` is
/// proxied, `q` gets the definition; both must agree.
#[test]
fn rf4_bare_and_negated_argument() {
    assert_eq!(
        verdict(UF, &format!("{A1}(assert (P (not q)))")),
        "unsat"
    );
}
```

- [ ] **Step 2: Run the probes and confirm the expected failures**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice56_probes)'`
Expected: 13 tests discovered. FAIL: `a1`–`a8` (each reports `sat` where `unsat` is expected, or `((q @elem0))` for a7), `rf1_string_logic_header`, `rf2_ufbv_header_without_bv_term`. PASS: `rf2_ufbv_header_with_bv_term`, `rf3_bool_index_array_not_sat`, `rf4_bare_and_negated_argument`. If the discovered count is 0, the filter is wrong — fix it before continuing.

- [ ] **Step 3: Write the failing unit test and update the slice-54 one**

In `crates/shinri-solver/src/word_norm.rs`, test module, replace the body of `bare_constants_and_connective_children_are_not_purified` with:

```rust
    #[test]
    fn bare_constants_and_connective_children_are_not_purified() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let q = bool_var(&mut ctx, "q");
        let p = bool_pred(&mut ctx, "P");
        let t = ctx.mk_const_bool(true);
        let pq = ctx.mk_app(Op::Uninterpreted(p), &[q]).unwrap();
        let pt = ctx.mk_app(Op::Uninterpreted(p), &[t]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let conj = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[eq, q]).unwrap();
        let iff = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[q, eq]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[pq, pt, conj, iff]);
        // Slice 56: `q` as P's argument is not proxied, but gets its
        // excluded-middle definition; nothing else is appended.
        let not_q = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[q]).unwrap();
        let em_q = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[q, not_q]).unwrap();
        assert_eq!(
            out,
            vec![pq, pt, conj, iff, em_q],
            "same TermIds, only q's definition appended"
        );
        assert!(wn.internal.is_empty());
    }
```

Add, directly after it:

```rust
    #[test]
    fn bare_bool_constant_argument_gets_excluded_middle_definition() {
        let mut ctx = Context::new();
        let bs = ctx.bool_sort();
        // A user symbol named like a proxy, declared before any mint: it is a
        // user constant (not in `internal`), so it gets the definition too.
        let ub_sym = ctx.declare_fun("bool!0", &[], bs);
        let ub = ctx.mk_app(Op::Uninterpreted(ub_sym), &[]).unwrap();
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let p = bool_pred(&mut ctx, "P");
        let f = bool_pred(&mut ctx, "F");
        let pq = ctx.mk_app(Op::Uninterpreted(p), &[q]).unwrap();
        let fq = ctx.mk_app(Op::Uninterpreted(f), &[q]).unwrap();
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[q, r]).unwrap();
        let pqr = ctx.mk_app(Op::Uninterpreted(p), &[qr]).unwrap();
        let fls = ctx.mk_const_bool(false);
        let pf = ctx.mk_app(Op::Uninterpreted(p), &[fls]).unwrap();
        let pub_ = ctx.mk_app(Op::Uninterpreted(p), &[ub]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[pq, fq, pqr, pf, pub_]);

        let em = |ctx: &mut Context, k| {
            let n = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[k]).unwrap();
            ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[k, n]).unwrap()
        };
        let em_q = em(&mut ctx, q);
        let em_r = em(&mut ctx, r);
        let em_ub = em(&mut ctx, ub);
        // No rewrite of the bare-argument parents: identical TermIds.
        assert_eq!(&out[..2], &[pq, fq]);
        assert_eq!(out[3], pf);
        assert_eq!(out[4], pub_);
        // Exactly one definition for q although it sits under P and F.
        assert_eq!(out.iter().filter(|&&t| t == em_q).count(), 1);
        // None for r (only under the connective `and`), none for `false`.
        assert!(!out.contains(&em_r));
        let em_f = em(&mut ctx, fls);
        assert!(!out.contains(&em_f));
        // The user `bool!0` gets one.
        assert_eq!(out.iter().filter(|&&t| t == em_ub).count(), 1);
        // Exactly one proxy (for `(and q r)`), and the proxy gets no
        // excluded-middle definition.
        assert_eq!(wn.internal.len(), 1);
        let b = *wn.internal.iter().next().unwrap();
        let em_b = em(&mut ctx, b);
        assert!(!out.contains(&em_b));
        // 5 rewritten assertions + (= b (and q r)) + em_q + em_ub.
        assert_eq!(out.len(), 8, "{out:?}");
    }
```

Note: `em(&mut ctx, b)` hash-conses a fresh `(or b (not b))`; that is fine because `out` is already computed.

- [ ] **Step 4: Run the unit tests to confirm they fail**

Run: `cargo nextest run -p shinri-solver -E 'test(bare_constants_and_connective_children_are_not_purified) | test(bare_bool_constant_argument_gets_excluded_middle_definition)'`
Expected: 2 tests discovered, both FAIL (no definition appended; `out.len()` is 6 in the new test).

- [ ] **Step 5: Implement the rule**

In `crates/shinri-solver/src/word_norm.rs`, add these two methods inside `impl WordNorm`, directly after `bool_proxy`:

```rust
    /// Slice 56: a nullary user Bool constant in argument position is tied to
    /// ⊤/⊥ only if it is also a SAT atom; when it occurs nowhere else it was
    /// an opaque e-graph node (`(P q)`, `(not (P true))`, `(not (P false))`
    /// was a wrong `sat`). Proxies are excluded: `(= b t)` already makes them
    /// atoms. `true`/`false` are `TermNode::Const` and fail the match.
    fn needs_excluded_middle(&self, ctx: &Context, t: TermId) -> bool {
        ctx.sort_of(t) == ctx.bool_sort()
            && !self.internal.contains(&t)
            && matches!(
                ctx.term_node(t),
                TermNode::App { op: Op::Uninterpreted(_), args, .. }
                    if ctx.children(*args).is_empty()
            )
    }

    /// Slice 56: append `(or k (not k))` once per call. The tautology changes
    /// no verdict; it only makes Tseitin encode `k` as an atom, so SAT decides
    /// it and EUF merges it with ⊤/⊥. `k` itself stays in place.
    fn excluded_middle(
        &self,
        ctx: &mut Context,
        k: TermId,
        defs: &mut Vec<TermId>,
        seen_defs: &mut FxHashSet<TermId>,
    ) {
        let not_k = ctx
            .mk_app(Op::Builtin(BuiltinOp::Not), &[k])
            .expect("(not k) over Bool is well-sorted");
        let def = ctx
            .mk_app(Op::Builtin(BuiltinOp::Or), &[k, not_k])
            .expect("(or k (not k)) over Bool is well-sorted");
        if seen_defs.insert(def) {
            defs.push(def);
        }
    }
```

Replace the item-3 loop in `walk`:

```rust
        // Slice 54 (item 3): purify compound Bool arguments of non-connectives.
        if !is_bool_connective(op) {
            for k in new_kids.iter_mut() {
                if needs_bool_proxy(ctx, *k) {
                    *k = self.bool_proxy(ctx, *k, defs, seen_defs);
                }
            }
        }
```

with:

```rust
        // Slice 54 (item 3): purify compound Bool arguments of non-connectives;
        // slice 56: give a bare user Bool constant its excluded-middle definition.
        if !is_bool_connective(op) {
            for k in new_kids.iter_mut() {
                if needs_bool_proxy(ctx, *k) {
                    *k = self.bool_proxy(ctx, *k, defs, seen_defs);
                } else if self.needs_excluded_middle(ctx, *k) {
                    self.excluded_middle(ctx, *k, defs, seen_defs);
                }
            }
        }
```

- [ ] **Step 6: Correct the doc comments**

Replace the `needs_bool_proxy` doc comment:

```rust
/// Slice 54: a Bool-sorted argument needs a proxy unless it is already a
/// single atom EUF links to ⊤/⊥: a Bool constant (`true`/`false`) or a
/// nullary symbol (a user Bool constant, or an earlier proxy).
```

with:

```rust
/// Slice 54: a Bool-sorted argument needs a proxy unless it is a Bool
/// constant (`true`/`false`) or a nullary symbol (a user Bool constant, or an
/// earlier proxy). A nullary user constant is NOT automatically linked to
/// ⊤/⊥: it is only when it is also a SAT atom, which slice 56 guarantees via
/// `WordNorm::needs_excluded_middle`.
```

In the module doc, item 3, replace the sentence fragment

```rust
//!    `(P (= x 1))`, `(not (P true))`, `(= x 1)` was a wrong `sat`. `b` takes
//!    the same path as a user Bool constant (an EUF atom merged with ⊤/⊥), and
//!    the definition puts `t` in a Boolean position (so slice 53's arithmetic
//!    `=` axioms reach it).
```

with:

```rust
//!    `(P (= x 1))`, `(not (P true))`, `(= x 1)` was a wrong `sat`. `b` takes
//!    the same path as a user Bool constant (an EUF atom merged with ⊤/⊥), and
//!    the definition puts `t` in a Boolean position (so slice 53's arithmetic
//!    `=` axioms reach it). A bare nullary user Bool constant `k` in the same
//!    position (slice 56) is not proxied; it gets one appended definition
//!    `(or k (not k))`, which makes it a SAT atom — without it a `k` that
//!    occurs nowhere else was never merged with ⊤/⊥ (wrong `sat`).
```

- [ ] **Step 7: Run the unit tests and probes**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice56_probes) | test(bare_constants_and_connective_children_are_not_purified) | test(bare_bool_constant_argument_gets_excluded_middle_definition)'`
Expected: 15 tests discovered, 15 PASS.

Then the whole `word_norm` module and slice 54/55 probes (other unit tests may now see an extra definition when a bare Bool constant is a non-connective argument; if one fails only because `out` gained `(or k (not k))`, update its expectation and say so in the task report — any other failure is a real regression):

Run: `cargo nextest run -p shinri-solver -E 'test(/^word_norm::/) | binary(slice54_probes) | binary(slice55_probes)'`
Expected: non-zero discovered count, all PASS.

- [ ] **Step 8: Full CI**

Run: `cargo fmt --all && mise run ci`
Expected: green. Record the test totals (run / passed / skipped) for the report.

- [ ] **Step 9: Commit**

```bash
git add crates/shinri-solver/src/word_norm.rs crates/shinri-solver/tests/slice56_probes.rs
git commit -m "fix(word_norm): slice56 - excluded-middle definition for bare Bool constant arguments"
```

---

### Task 2: Oracle — drop the Ruling-8 exclusion, add an argument-only constant

**Files:**
- Modify: `crates/shinri-solver/tests/bool_arg_oracle.rs` (module doc ~1–9; `Family::decls` ~44–60; `arg` ~99–112; `is_unvalued` ~273; `z3_accepts_values` ~277–287; `run_family` ~289–360)

**Interfaces:**
- Consumes: Task 1's fix (observable only: `get-value` returns `true`/`false` for a bare Bool argument).
- Produces: nothing consumed later; the gate command below is cited in the Task 3 report.

- [ ] **Step 1: Declare `s` in every family and draw it as an argument**

`s` is a Bool constant that appears only as an argument (never in `leaves`), which is exactly the slice-56 shape. In `Family::decls`, add `(declare-const s Bool)\n` to each of the three strings, after the `q` declaration. For example the `UfLia` arm becomes:

```rust
            Family::UfLia => {
                "(declare-const p Bool)\n(declare-const q Bool)\n(declare-const s Bool)\n\
                 (declare-const x Int)\n(declare-const y Int)\n\
                 (declare-fun P (Bool) Bool)\n(declare-fun f (Bool Int) Int)\n"
            }
```

(`UfLra` and `Dt` likewise: insert `(declare-const s Bool)\n` right after `(declare-const q Bool)\n`.)

Replace `arg`:

```rust
/// A Bool argument: `true`/`false` (so congruence with a constant matters),
/// the argument-only constant `s` (slice 56: never an atom elsewhere), or a
/// depth-≤1 formula (a leaf or one connective over leaves). Everything but
/// `true`/`false` is recorded in `sink` for the get-value check.
fn arg(rng: &mut Lcg, fam: Family, sink: &mut Vec<String>) -> String {
    let a = match rng.below(6) {
        0 => "true".to_string(),
        1 => "false".to_string(),
        2 => "s".to_string(),
        _ => formula(rng, fam, 1),
    };
    if a != "true" && a != "false" && !sink.contains(&a) {
        sink.push(a.clone());
    }
    a
}
```

(This changes the random stream for the existing seeds; the `n_sat > 0 && n_unsat > 0` and `n_valued > 0` asserts still guard against a degenerate stream.)

- [ ] **Step 2: Remove the `@` exclusion and make an abstract value a failure**

Replace `is_unvalued` and `z3_accepts_values`:

```rust
fn is_unvalued(v: &str) -> bool {
    v == "?"
}

fn z3_accepts_values(logic: &str, src: &str, pairs: &[(String, String)]) -> easy_smt::Response {
    let mut extra = String::new();
    for (term, val) in pairs.iter().filter(|(_, v)| !is_unvalued(v)) {
        extra.push_str(&format!("(assert (= {term} {val}))\n"));
    }
    z3_outcome(logic, &format!("{src}{extra}"))
}
```

In `run_family`: delete `let mut n_abstract = 0usize;` and the `n_abstract += …` line; drop `n_abstract={n_abstract}` from the `println!`. Inside the `if ours == SolveOutcome::Sat && theirs == easy_smt::Response::Sat {` block, directly after `let pairs = get_value_pairs(…);`, add:

```rust
            // Slice 56: an abstract `@…` value for a Bool term is the
            // closed wrong-`sat` trace; report it rather than let z3 reject
            // the line.
            if let Some((t, v)) = pairs.iter().find(|(_, v)| v.starts_with('@')) {
                value_disagreements.push(format!(
                    "iter {iter}: abstract value {v} for {t}\n{src}"
                ));
                continue;
            }
```

Update the module doc's first paragraph by appending:

```rust
//! Slice 56: every family also passes `s`, a Bool constant that occurs only
//! as an argument, and an abstract `@…` value is a failure (the slice-55
//! Ruling-8 exclusion is gone).
```

- [ ] **Step 3: Run the oracle gate**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle) | binary(qfdt_oracle) | test(differential_qf_uflia_compound_args)'`
Expected: the same discovered count as slice 55 (22), all PASS. Capture each family's `println!` line (`--no-capture` if needed) — the report quotes `disagreements`, `value_disagreements` and `n_valued`. A count of 0 tests means `--features oracle` is missing.

- [ ] **Step 4: Optional before-evidence**

To show the oracle now catches the defect: `git stash` the Task 1 change to `word_norm.rs` only (`git stash push crates/shinri-solver/src/word_norm.rs`), run `cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)'`, record which families fail (expected: `disagreements` or `abstract value` lines mentioning `s`), then `git stash pop`. Note the result in the Task 3 report.

- [ ] **Step 5: Lint and commit**

Run: `cargo fmt --all && mise run lint`
Expected: clean.

```bash
git add crates/shinri-solver/tests/bool_arg_oracle.rs
git commit -m "test(oracle): slice56 - argument-only Bool constant, abstract values fail"
```

---

### Task 3: Bench run, report, measured outcomes

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice56-uf-bool-const-report.md` (date = the day the run finishes)
- Modify: `docs/superpowers/specs/2026-10-02-shinri-slice56-uf-bool-const-arg-design.md` (append §11)

**Interfaces:**
- Consumes: the branch HEAD after Task 2; base run `bench/results/slice55/results.jsonl`; base binary `target/slice55-after/shinri`.
- Produces: the report and §11 cited by the PR.

- [ ] **Step 1: Confirm the base exists**

Run: `ls bench/results/slice55/results.jsonl target/slice55-after/shinri && md5sum target/slice55-after/shinri`
Expected: both exist; md5 `6a753b2e1c088e0eefefc0a5ae4b1b38`. If either is missing, stop and ask the user (a fresh base run is ~2 h).

- [ ] **Step 2: Build and launch the after-run detached**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice56-after && cp target/release/shinri target/slice56-after/shinri
md5sum target/slice56-after/shinri | tee target/slice56-after/md5.txt
git rev-parse --short HEAD | tee target/slice56-after/commit.txt
date -u +%FT%TZ > target/slice56-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_UF,QF_DT,QF_UFLIA,QF_UFLRA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice56-after/shinri --run-id slice56 \
  > target/slice56-after/run.log 2>&1; date -u +%FT%TZ > target/slice56-after/finished.txt' &
```

The run takes about 2 h. Wait for `target/slice56-after/finished.txt` (poll it with a Monitor/until-loop, not a foreground sleep).

- [ ] **Step 3: Report and verdict comparison**

Run: `BENCH_RUN_ID=slice56 mise run bench-report`

Then join the two runs by `path` with a scratch script (in the session scratchpad, not committed):

```bash
python3 - <<'EOF'
import json, collections
def load(p): return {r["path"]: r for r in map(json.loads, open(p))}
a = load("bench/results/slice55/results.jsonl")
b = load("bench/results/slice56/results.jsonl")
assert a.keys() == b.keys(), "row sets differ"
c = collections.Counter()
changed = []
for p in a:
    va, vb = a[p]["verdict"], b[p]["verdict"]
    if va != vb:
        c[(a[p]["logic"], va, vb)] += 1
        changed.append((p, va, vb))
for k, n in sorted(c.items()): print(*k, n)
print("total", sum(c.values()))
open("target/slice56-after/changed.txt", "w").write(
    "\n".join(f"{p}\t{va}\t{vb}" for p, va, vb in changed))
EOF
```

(If the field names differ, read one line of `results.jsonl` and adjust; the slice-55 report used the same join.)

- [ ] **Step 4: Re-run every `correct → *` and every `* → wrong` row**

For each such path, 3× on each binary:

```bash
for bin in target/slice55-after/shinri target/slice56-after/shinri; do
  for i in 1 2 3; do
    timeout 25 prlimit --as=3221225472 taskset -c 12-23 $bin bench/corpus/<path> \
      | grep -m1 -E '^(sat|unsat|unknown)$' || echo none
  done
done
```

A row is a reproducible loss only if the after binary never gives the correct answer in its 3 runs while the base binary gives it in all 3. Any `wrong` row is a stop-and-investigate (spec criterion 2).

- [ ] **Step 5: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md`: *Headline*; *Commands*; *Runs* (both binaries, md5, started/finished, rows); *Success criteria* (spec §7 table, each with PASS/FAIL and evidence: probe results from Task 1 Step 2/7, the oracle line from Task 2 Step 3, the `mise run ci` totals from Task 1 Step 8); *Per-logic matrix*; *Verdict comparison* (transition table + re-run outcome); *What changed versus the spec* (every deviation, including any unit-test expectation updated in Task 1 Step 7 and the Task 2 Step 4 before-evidence); *Gates*; *Queued for the next slice* — the slice-55 report's queue items 2 onwards and its carried lists, copied verbatim, with item 1 removed and a line noting it is closed by slice 56. Also note that Review Focus 1–2 (QF_SLIA, QF_UFBV headers) are probe-covered only, not benched.

- [ ] **Step 6: Append spec §11**

Append to the spec:

```markdown
## 11. Measured outcomes

Full evidence:
`docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice56-uf-bool-const-report.md`.

| # | Criterion | Result |
| --- | --- | --- |
| 1 | a1–a8 pass; all eight fail on `main` | <PASS/FAIL + one line> |
| 2 | Bench: 0 `wrong`, 0 panic, no reproducible `correct → *` loss | <PASS/FAIL + rows, changed count> |
| 3 | Oracle: non-zero count, 0 disagreements, no `@` values | <PASS/FAIL + counts per family> |
| 4 | `mise run ci` green, fmt clean | <PASS/FAIL + totals> |

### Deviations from this spec

- <each deviation, or "None.">
```

Fill every `<…>` with the measured values before committing; none may remain.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all --check
git add docs/superpowers/research/*slice56* docs/superpowers/specs/2026-10-02-shinri-slice56-uf-bool-const-arg-design.md
git commit -m "docs(bench+spec): slice56 - bench run and measured outcomes"
```

Then hand off to superpowers:finishing-a-development-branch (push, PR to `main`, merge commit after CI is green, delete the branch) — only with the user's consent.
