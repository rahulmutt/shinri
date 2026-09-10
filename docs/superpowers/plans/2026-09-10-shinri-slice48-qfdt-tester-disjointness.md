# Slice 48 — QF_DT tester disjointness — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make QF_DT tester disjointness re-check after every merge instead of once at assert time, closing 166 wrong-`sat` answers in the `20172804-Barrett` family.

**Architecture:** The rule "an asserted `is-D(t)` whose class holds `C(..)` with `C ≠ D` is a conflict" currently lives only in `DtSolver::assert`, so it sees the class exactly once. This plan relocates a second copy into `DtSolver::check`, where it re-runs after every merge. Because a conflict cites the asserting literal, the record it reads (`asserted_testers`) must become backtrack-accurate first — it is monotone today, and a stale entry would cite a literal the trail no longer holds.

**Tech Stack:** Rust workspace, `mise` tasks, `cargo nextest` 0.9.140, z3/cvc5 from mise behind the `oracle` cargo feature, `shinri-bench` for corpus runs.

**Spec:** `docs/superpowers/specs/2026-09-10-shinri-slice48-qfdt-tester-disjointness-design.md` — read it alongside this plan; every task argues from it.

## Global Constraints

- **Branch:** all work on `slice48-qfdt-tester-disjointness`, branched from `main` at `c9df881a`. PR to `main`, merge commit when CI is green, then delete the branch remote and local.
- **Pure-Rust mandate:** no native-link dependencies. `deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`. This slice adds **no** dependency of any kind.
- **Oracle feature gate:** `crates/shinri-solver/tests/qfdt_oracle.rs` is `#![cfg(feature = "oracle")]`. Every oracle command carries `--features oracle`. **Without it the file compiles to zero tests and the run reads as green.** Always confirm a non-zero discovered count before believing a result.
- **nextest filters:** use the expression form. `-E 'binary(qfdt_oracle)'` selects a whole integration-test binary; `-E 'test(<name>)'` selects by test name. A positional `mod::name` filter matches nothing on the pinned nextest 0.9.140.
- **Formatting gate:** `cargo fmt --all` before every push. CI runs `cargo fmt --check` and fails fast.
- **Lint gate:** `cargo clippy --workspace --all-targets -- -D warnings` must be clean. `mise run lint` covers both.
- **Test tier:** nothing in this slice may exceed the 5-minute threshold that would require `#[ignore = "exhaustive: nightly tier"]`. Never remove `#[ignore]` from the `shinri-fp` exhaustive suites.
- **Commit trailer:** every commit ends with `Claude-Session: https://claude.ai/code/session_014DanY52GZfbnAH4zSApFZY`.

**Ordering note — this plan reorders spec §4.** The spec lists `tester_clash` as task 2 and the level-indexed record as task 3. The plan swaps them: landing the conflict rule while `asserted_testers` is still monotone would put a transient wrong-`unsat` hazard on the branch between two commits. Task 2 here is the record (a behaviour-preserving refactor), Task 3 is the rule.

---

### Task 1: Randomized QF_DT oracle generator

The existing `qfdt_oracle.rs` is a fixed list of hand-written shapes. `qfdt_oracle_disjointness` (`:155`) exists and **passes today** — it happens to use the conjunct order that works. That blind spot is why 166 wrong answers shipped. This task adds a generator that can emit the failing shape, and it **must fail on pre-slice `main`**.

**Files:**
- Modify: `crates/shinri-solver/tests/qfdt_oracle.rs` (append; do not touch the existing fixed-shape tests)

**Interfaces:**
- Consumes: the file's existing `shinri_answer(&str) -> String` (`:25`) and `z3_answer(&str) -> String` (`:95`).
- Produces: nothing other tasks call. Task 5 re-runs this binary; Task 6 quotes its result.

- [ ] **Step 1: Write the generator and the failing test**

Append to `crates/shinri-solver/tests/qfdt_oracle.rs`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 48: randomized generator.
//
// The fixed shapes above cannot find the slice-48 defect, because tester
// disjointness was order-dependent: the SAME formula answered `sat` or `unsat`
// depending on which conjunct SAT asserted first, and every hand-written shape
// here happens to use the order that worked. The generator's load-bearing
// dimension is therefore CONJUNCT ORDER — it shuffles, and it alternates
// between separate `(assert ..)` commands and one `(and ..)`.
// ─────────────────────────────────────────────────────────────────────────────

/// A tiny deterministic LCG so the corpus is reproducible without `rand`.
/// Copied verbatim from tests/qfabv_oracle.rs to match the existing convention.
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

const N_ITERS: usize = 300;

/// The Barrett family, names copied verbatim from
/// `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30072.cvc.smt2`, plus a
/// flat enum standing in for the blocksworld-style enums.
const BARRETT: &str = "(declare-datatypes ((nat 0)(list 0)(tree 0)) (\
((succ (pred nat)) (zero))\
((cons (car tree) (cdr list)) (null))\
((node (children list)) (leaf (data nat)))))\
(declare-datatype Color ((red) (green) (blue)))\
(declare-fun n1 () nat)(declare-fun l1 () list)(declare-fun l2 () list)\
(declare-fun t1 () tree)(declare-fun c1 () Color)";

fn nat_term(rng: &mut Lcg, depth: u32) -> String {
    match rng.below(if depth == 0 { 3 } else { 4 }) {
        0 => "zero".into(),
        1 => "n1".into(),
        2 => format!("(data {})", tree_term(rng, depth.saturating_sub(1))),
        _ => format!("(succ {})", nat_term(rng, depth - 1)),
    }
}

fn list_term(rng: &mut Lcg, depth: u32) -> String {
    match rng.below(if depth == 0 { 4 } else { 6 }) {
        0 => "null".into(),
        1 => "l1".into(),
        2 => "l2".into(),
        // A selector applied to a possibly-WRONG constructor: where the corpus
        // reproducer v1l30072 lives.
        3 => format!("(children {})", tree_term(rng, depth.saturating_sub(1))),
        4 => format!("(cdr {})", list_term(rng, depth - 1)),
        _ => format!(
            "(cons {} {})",
            tree_term(rng, depth - 1),
            list_term(rng, depth - 1)
        ),
    }
}

fn tree_term(rng: &mut Lcg, depth: u32) -> String {
    match rng.below(if depth == 0 { 2 } else { 4 }) {
        0 => "t1".into(),
        1 => format!("(leaf {})", if depth == 0 { "zero".into() } else { nat_term(rng, depth - 1) }),
        2 => format!("(car {})", list_term(rng, depth - 1)),
        _ => format!("(node {})", list_term(rng, depth - 1)),
    }
}

/// One conjunct. Testers and equalities are drawn from the same pool so a
/// generated instance mixes both — the mix is what the defect needs.
fn conjunct(rng: &mut Lcg) -> String {
    let d = 2;
    let body = match rng.below(9) {
        0 => format!("(= {} {})", list_term(rng, d), list_term(rng, d)),
        1 => format!("(= {} {})", tree_term(rng, d), tree_term(rng, d)),
        2 => format!("(= {} {})", nat_term(rng, d), nat_term(rng, d)),
        3 => format!("((_ is cons) {})", list_term(rng, d)),
        4 => format!("((_ is null) {})", list_term(rng, d)),
        5 => format!("((_ is node) {})", tree_term(rng, d)),
        6 => format!("((_ is leaf) {})", tree_term(rng, d)),
        7 => format!("((_ is succ) {})", nat_term(rng, d)),
        _ => {
            let k = ["red", "green", "blue"][rng.below(3) as usize];
            format!("(= c1 {k})")
        }
    };
    if rng.below(4) == 0 {
        format!("(not {body})")
    } else {
        body
    }
}

fn gen_instance(rng: &mut Lcg) -> String {
    let n = 2 + rng.below(4) as usize;
    let mut cs: Vec<String> = (0..n).map(|_| conjunct(rng)).collect();
    // Fisher-Yates over the LCG: the order dimension the fixed shapes lack.
    for i in (1..cs.len()).rev() {
        let j = rng.below((i + 1) as u64) as usize;
        cs.swap(i, j);
    }
    let asserts = if rng.below(2) == 0 {
        // Separate commands: SAT sees them in file order.
        cs.iter().map(|c| format!("(assert {c})")).collect::<String>()
    } else {
        // One conjunction: the assert order is SAT's to choose. This is the
        // encoding the minimal reproducer uses.
        format!("(assert (and {}))", cs.join(""))
    };
    format!("(set-logic QF_DT){BARRETT}{asserts}(check-sat)")
}

#[test]
fn qfdt_random_matches_z3() {
    let mut rng = Lcg(0xD7_0000_0048u64);
    let (mut n_sat, mut n_unsat, mut n_skipped) = (0usize, 0usize, 0usize);

    for it in 0..N_ITERS {
        let src = gen_instance(&mut rng);
        let ours = shinri_answer(&src);
        if ours == "unknown" {
            n_skipped += 1; // our incompleteness fence — not a disagreement
            continue;
        }
        let theirs = z3_answer(&src);
        if theirs == "unknown" {
            n_skipped += 1; // no ground truth
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_DT SOUNDNESS DISAGREEMENT (iter {it}): shinri={ours} z3={theirs}\n\
             Reproduce with this instance:\n{src}"
        );
        if ours == "sat" {
            n_sat += 1;
        } else {
            n_unsat += 1;
        }
    }

    println!(
        "qfdt_random_matches_z3: {N_ITERS} iters, {n_sat} sat / {n_unsat} unsat / \
         {n_skipped} skipped, 0 mismatches"
    );
    // Both directions must be exercised, or the oracle proves nothing.
    assert!(n_sat > 0, "generator produced no sat instances");
    assert!(n_unsat > 0, "generator produced no unsat instances");
}
```

- [ ] **Step 2: Run it on pre-slice `main` and capture the failure verbatim**

Run:
```bash
cargo nextest run -p shinri-solver --features oracle -E 'binary(qfdt_oracle)' --no-capture
```

Expected: a non-zero discovered count (the existing fixed shapes plus `qfdt_random_matches_z3`), and `qfdt_random_matches_z3` **FAILS** with `QF_DT SOUNDNESS DISAGREEMENT (iter N): shinri=sat z3=unsat` followed by the generated instance.

**Copy the failing instance verbatim into the task report and the commit message.** This is the slice's criterion 4 evidence and it can only be collected before the fix lands.

If the test *passes*, the generator is not reaching the defect — do not proceed and do not weaken the criterion. Widen it in this order and re-run after each: raise `N_ITERS` to 1000; raise the `conjunct` tester weight; add `l1`/`l2` equalities against bare `null` more often. The shape it must be able to produce is `is-cons(X) ∧ X = null` with the tester emitted first.

- [ ] **Step 3: Confirm the discovered count was non-zero**

Read the nextest summary line. If it says `0 tests run`, the `--features oracle` flag was dropped or the filter was wrong — a 0-test run reads as green and must never be recorded as evidence. Re-run correctly before continuing.

- [ ] **Step 4: Format and commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfdt_oracle.rs
git commit
```

Commit message:
```
test(qfdt): slice48 T1 - randomized generator over testers, equalities and order

The fixed-shape oracle cannot find the slice-48 defect: tester disjointness is
order-dependent and every hand-written shape uses the order that works. The
generator shuffles conjuncts and alternates separate asserts with one (and ..).

FAILS on pre-slice main, as required by spec §5.1:

<paste the verbatim QF_DT SOUNDNESS DISAGREEMENT output and instance here>

Claude-Session: https://claude.ai/code/session_014DanY52GZfbnAH4zSApFZY
```

The branch is now red and stays red until Task 3. Do not push it for a PR yet.

---

### Task 2: Level-index `asserted_testers`

Behaviour-preserving on its own — nothing yet reads the record for a conflict. It lands first so Task 3's rule never runs against a monotone record.

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs:33-41` (the field and its doc comment), `:788-810` (`assert`), `:883-884` (`push`/`pop`), `:390-393` (`instantiate_constructor`'s read of the record)
- Test: `crates/shinri-dt/src/lib.rs` `mod tests` (append)

**Interfaces:**
- Consumes: nothing from Task 1.
- Produces: `DtSolver.asserted_testers: Vec<TermId>` (insertion-ordered) alongside `asserted_tester_set: FxHashSet<TermId>` and `tester_marks: Vec<usize>`. Task 3 iterates `&self.asserted_testers`.

- [ ] **Step 1: Write the failing backtracking tests**

Append to `mod tests` in `crates/shinri-dt/src/lib.rs`:

```rust
    /// Slice 48: the assertion record is per-level. A tester asserted inside a
    /// scope must be gone once that scope is popped — spec §3.2. Until this
    /// slice the record was monotone, which was sound only while it fed a
    /// GUARDED lemma; slice 48 feeds it into a CONFLICT, and a stale entry
    /// would cite a literal the trail no longer holds.
    #[test]
    fn asserted_tester_recorded_in_a_scope_is_dropped_on_pop() {
        let mut ctx = Context::new();
        let (list, _nil, _cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_cons_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_cons_x);

        dt.push(); // level 1
        dt.push(); // level 2
        let _ = dt.assert(&mut cx, Lit::new(v, true));
        assert!(
            dt.asserted_testers().contains(&is_cons_x),
            "the level-2 assertion must be recorded"
        );

        dt.pop(1);
        assert!(
            !dt.asserted_testers().contains(&is_cons_x),
            "popping to level 1 must discard a level-2 assertion"
        );
    }

    /// The mirror case: a level-0 assertion is permanent, so `pop(0)` must NOT
    /// discard it. This is the off-by-one that `pop_to` semantics decide, and
    /// the reason it gets its own fence.
    #[test]
    fn level_zero_asserted_tester_survives_pop_to_zero() {
        let mut ctx = Context::new();
        let (list, _nil, _cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_cons_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_cons_x);

        // Asserted at level 0, before any scope is opened.
        let _ = dt.assert(&mut cx, Lit::new(v, true));
        dt.push(); // level 1
        dt.pop(0);
        assert!(
            dt.asserted_testers().contains(&is_cons_x),
            "a level-0 assertion is permanent and must survive pop(0)"
        );
    }

    /// The record must not grow a duplicate when the same tester is asserted
    /// twice in one scope — `assert` relied on set semantics before slice 48.
    #[test]
    fn asserted_tester_is_recorded_once_per_scope() {
        let mut ctx = Context::new();
        let (list, _nil, _cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_cons_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_cons_x);

        let _ = dt.assert(&mut cx, Lit::new(v, true));
        let _ = dt.assert(&mut cx, Lit::new(v, true));
        assert_eq!(
            dt.asserted_testers().len(),
            1,
            "the same tester asserted twice must be recorded once"
        );
    }
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo nextest run -p shinri-dt -E 'test(asserted_tester_recorded_in_a_scope_is_dropped_on_pop)'`

Expected: FAIL to **compile** — `no method named 'asserted_testers'`. That is the intended first failure; the accessor arrives in Step 3.

- [ ] **Step 3: Replace the field with the level-indexed record**

In `crates/shinri-dt/src/lib.rs`, replace the field at `:36-41`:

```rust
    /// Slice 40, corrected by slice 48: tester atoms asserted true — the
    /// trigger set for `instantiate_constructor` AND for `tester_clash`.
    ///
    /// PER-LEVEL, unlike every other field on this struct. The watch sets
    /// (`ctor_apps`, `sel_apps`, `testers`, `dt_terms`, `emitted`,
    /// `split_done`) are assignment-independent and stay monotone; this one is
    /// a record of the current branch's assertions and must be retracted with
    /// it. Slice 40 could leave it monotone because a stale entry only
    /// re-emitted a GUARDED (hence inert) lemma. Slice 48 feeds it into
    /// `TCheck::Conflict`, whose `EqLeaf::Asserted(lit)` names a literal that
    /// conflict analysis expects to be false under the current assignment — a
    /// stale entry would hand the SAT seam a clause it cannot analyse.
    /// `TheoryCtx` exposes no trail, so the record itself must be accurate.
    asserted_testers: Vec<TermId>,
    /// Membership index for `asserted_testers`, preserving the dedup that
    /// `assert` relied on when this was a set.
    asserted_tester_set: FxHashSet<TermId>,
    /// `asserted_testers.len()` at the moment each open scope began.
    /// `push`/`pop` maintain it; the semantics mirror
    /// `crates/shinri-str/src/trail.rs`'s `pop_to`.
    tester_marks: Vec<usize>,
```

In `assert` (`:799`), replace `self.asserted_testers.insert(atom);` with:

```rust
        if self.asserted_tester_set.insert(atom) {
            self.asserted_testers.push(atom);
        }
```

In `instantiate_constructor` (`:391`), replace
`let asserted: Vec<TermId> = self.asserted_testers.iter().copied().collect();` with:

```rust
        let asserted: Vec<TermId> = self.asserted_testers.clone();
```

Replace the `push`/`pop` no-ops at `:883-884`:

```rust
    fn push(&mut self) {
        self.tester_marks.push(self.asserted_testers.len());
    }

    /// ABSOLUTE target level, matching `EqualityEngine`/`UndoLog` and the
    /// `shinri-str` trail. Truncating to the mark taken when the FIRST
    /// discarded scope opened is what makes `pop(0)` keep level-0 assertions
    /// (no mark was ever taken for level 0) while discarding everything a
    /// scope introduced.
    fn pop(&mut self, level: usize) {
        let mut restore = None;
        while self.tester_marks.len() > level {
            restore = self.tester_marks.pop();
        }
        if let Some(n) = restore {
            for t in self.asserted_testers.drain(n..) {
                self.asserted_tester_set.remove(&t);
            }
        }
    }
```

Add the test accessor beside the existing `watches_*` accessors (`:749-766`):

```rust
    #[cfg(test)]
    pub(crate) fn asserted_testers(&self) -> &[TermId] {
        &self.asserted_testers
    }
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo nextest run -p shinri-dt`

Expected: PASS, including the three new tests and **every pre-existing `shinri-dt` test** — especially `asserted_tester_instantiates_guarded_constructor` (`:1652`) and `asserted_tester_conflicting_with_constructor_is_rejected_at_assert` (`:1367`), which read this record. This task changes no behaviour; a pre-existing failure here means the record's semantics moved and must be fixed before Task 3.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-dt/src/lib.rs
git commit
```

Commit message:
```
refactor(dt): slice48 T2 - asserted_testers becomes per-level

Slice 40 left the record monotone, justified because a stale entry only
re-emitted a guarded, inert lemma. Slice 48 feeds it into a conflict, which
voids that justification: a stale entry would cite a literal the trail no
longer holds. TheoryCtx exposes no trail, so the record must be accurate by
construction. push/pop stop being no-ops for DT; every other field stays
monotone. No behaviour change on its own.

Claude-Session: https://claude.ai/code/session_014DanY52GZfbnAH4zSApFZY
```

---

### Task 3: `tester_clash` in `check`

The fix. After this task the branch goes green.

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs` (new method beside `constructor_clash` at `:251`; call site in `check` at `:823`)
- Test: `crates/shinri-dt/src/lib.rs` `mod tests` (append); `crates/shinri-solver/tests/qfdt_e2e.rs` (append)

**Interfaces:**
- Consumes: `self.asserted_testers: &[TermId]` from Task 2; the existing `Self::uapp`, `self.ctor_of_class`, `cx.atoms.var_of_atom`.
- Produces: `fn tester_clash(&self, cx: &mut TheoryCtx) -> Option<TCheck>`.

- [ ] **Step 1: Write the failing e2e tests**

Append to `crates/shinri-solver/tests/qfdt_e2e.rs`. All four reproduce on `c9df881a`; the fifth must keep passing.

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 48: tester disjointness re-checked after every merge.
// Before slice 48 these answered `sat` because the disjointness rule ran only
// in `assert`, against the class as it stood at that instant.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn tester_conflicting_with_later_merge_is_unsat() {
    // is-cons(x) AND x = nil. Inside one `and`, so the assert order is SAT's
    // to choose — this is the minimal form of the 166 Barrett wrong answers.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (and ((_ is cons) x) (= x nil)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn tester_conflicting_with_earlier_merge_is_unsat() {
    // The same formula with the conjuncts swapped. It already answered `unsat`
    // before slice 48; pinned so the ORDER-DEPENDENCE itself cannot come back.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (and (= x nil) ((_ is cons) x)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn tester_conflicting_through_transitive_merge_is_unsat() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)(declare-fun y () List)\
         (assert (and ((_ is cons) x) (= x y) (= y nil)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn tester_over_selector_collapse_is_unsat() {
    // is-cons(tail(cons 1 nil)). The class of `tail(cons 1 nil)` gains its
    // constructor `nil` from collapse_lemma, INSIDE check — so `assert` is
    // never re-entered. This is the corpus reproducer's shape
    // (QF_DT/20172804-Barrett/.../v1l30072.cvc.smt2, `is-cons(children(node null))`).
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (assert ((_ is cons) (tail (cons 1 nil))))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn tester_over_selector_of_a_free_variable_stays_sat() {
    // The over-fire guard. `tail(x)` with `x` free has no established
    // constructor, so is-cons(tail(x)) is satisfiable. A disjointness rule that
    // fires on a merely CANDIDATE constructor turns this into a wrong `unsat` —
    // trading a wrong-sat cluster for a wrong-unsat one. Passes before slice 48
    // and must keep passing.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert ((_ is cons) (tail x)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn barrett_v1l30072_body_is_unsat() {
    // The corpus reproducer's assert, verbatim, with its own datatype block.
    // 966 B file; answers `sat` before slice 48, `:status unsat`, z3 unsat.
    let out = run_script(
        "(set-logic QF_DT)\
         (declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))\
         ((cons (car tree) (cdr list)) (null))\
         ((node (children list)) (leaf (data nat)))))\
         (declare-fun x1 () nat)(declare-fun x2 () list)(declare-fun x3 () tree)\
         (assert (and (and (= (children (leaf zero)) null) \
         ((_ is cons) (children (node null)))) (not ((_ is null) x2))))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}
```

- [ ] **Step 2: Run them to verify four fail and one passes**

Run:
```bash
cargo nextest run -p shinri-solver -E 'binary(qfdt_e2e)'
```

Expected: `tester_conflicting_with_later_merge_is_unsat`, `tester_conflicting_through_transitive_merge_is_unsat`, `tester_over_selector_collapse_is_unsat` and `barrett_v1l30072_body_is_unsat` **FAIL** with `left: ["sat"], right: ["unsat"]`. `tester_conflicting_with_earlier_merge_is_unsat` and `tester_over_selector_of_a_free_variable_stays_sat` **PASS**.

If the free-variable test fails at this point, stop — the baseline is not what this plan assumes.

- [ ] **Step 3: Write the failing unit test**

Append to `mod tests` in `crates/shinri-dt/src/lib.rs`:

```rust
    /// Slice 48: the disjointness rule re-fires in `check` after a merge that
    /// arrived AFTER the tester was asserted — the case `assert`'s one-shot
    /// check structurally cannot see.
    #[test]
    fn asserted_tester_conflicting_with_a_later_merge_is_rejected_at_check() {
        let mut ctx = Context::new();
        let (list, nil, _cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_cons_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_cons_x);
        dt.new_var(&mut cx, Var::new(1), nil_t);

        // Tester FIRST, while x's class is still constructor-free: `assert`
        // sees nothing to clash with and returns None.
        let at_assert = dt.assert(&mut cx, Lit::new(v, true));
        assert!(
            at_assert.is_none(),
            "no constructor in the class yet — assert must not conflict"
        );

        // The merge arrives afterwards.
        let (xn, nn) = (cx.eq.intern(x), cx.eq.intern(nil_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        let verdict = dt.check(&mut cx, Effort::Full);
        assert_eq!(
            tcheck_name(&verdict),
            "Conflict",
            "is-cons(x) with x ≡ nil must conflict at check time"
        );
    }

    /// The stale-record guard, stated as behaviour rather than as bookkeeping:
    /// a tester asserted inside a popped scope must NOT produce a conflict,
    /// even though the merge that would clash with it is still in the engine.
    #[test]
    fn popped_asserted_tester_does_not_conflict_at_check() {
        let mut ctx = Context::new();
        let (list, nil, _cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_cons_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_cons_x);
        dt.new_var(&mut cx, Var::new(1), nil_t);

        dt.push(); // level 1
        let _ = dt.assert(&mut cx, Lit::new(v, true));
        dt.pop(0); // the tester is retracted; the merge below is not

        let (xn, nn) = (cx.eq.intern(x), cx.eq.intern(nil_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        let verdict = dt.check(&mut cx, Effort::Full);
        assert_ne!(
            tcheck_name(&verdict),
            "Conflict",
            "a retracted tester must not produce a conflict citing its literal"
        );
    }
```

- [ ] **Step 4: Run them to verify the first fails**

Run: `cargo nextest run -p shinri-dt -E 'test(conflicting_with_a_later_merge)'`

Expected: FAIL — the verdict is `Split` or `Unknown`, not `Conflict`. Confirm the discovered count is 1, not 0.

`popped_asserted_tester_does_not_conflict_at_check` passes already (nothing conflicts at check yet); it is the guard that Task 2's retraction actually holds once Task 3 makes conflicts possible.

- [ ] **Step 5: Implement `tester_clash`**

Insert into `impl DtSolver`, immediately after `constructor_clash` (which ends at `:277`):

```rust
    /// Tester disjointness, slice 48: an asserted `is-D(t)` whose class holds a
    /// `C(..)` with `C != D` is a conflict — re-checked here after EVERY merge.
    ///
    /// `assert` (`fn assert`, below) carries the same rule at the other trigger
    /// point, and BOTH are kept deliberately. `assert` catches the clash more
    /// cheaply when the constructor is already in the class; this one catches
    /// the merges `assert` structurally cannot see, because they arrive through
    /// the shared `EqualityEngine` — from `collapse_lemma`, from
    /// `instantiate_constructor`, or from EUF congruence — rather than as a
    /// DT-owned literal. Before slice 48 only `assert` existed, which made the
    /// verdict depend on the order SAT asserted the literals in: `is-cons(x) ∧
    /// x = nil` answered `sat` one way round and `unsat` the other.
    ///
    /// The consequence in the disagreeing direction is the NEGATIVE literal
    /// `¬is-D(t)`, and `TCheck::Split` carries only positive atoms — which is
    /// why this is a conflict rule and not a lemma.
    fn tester_clash(&self, cx: &mut TheoryCtx) -> Option<TCheck> {
        for &tst in &self.asserted_testers {
            let Some((tsym, targs)) = Self::uapp(cx.terms, tst) else {
                continue;
            };
            let Some(DtRole::Tester { ctor }) = cx.terms.dt_role(tsym) else {
                continue;
            };
            let Some(&t) = targs.first() else {
                continue;
            };
            let Some((csym, capp)) = self.ctor_of_class(cx, t) else {
                continue; // no constructor in the class — nothing to clash with
            };
            if csym == ctor {
                continue; // agrees
            }
            // The literal that put `tst` in the record. `asserted_testers` holds
            // only POSITIVELY asserted testers (`assert` returns early on a
            // negative literal), so the polarity is `true` by construction.
            let Some(var) = cx.atoms.var_of_atom(tst) else {
                continue;
            };
            let tn = cx.eq.intern(t);
            let cn = cx.eq.intern(capp);
            let mut leaves = vec![EqLeaf::Asserted(Lit::new(var, true))];
            cx.eq.explain(tn, cn, &mut leaves);
            return Some(TCheck::Conflict(leaves));
        }
        None
    }
```

Then add the call in `check`, immediately after the `constructor_clash` block (`:823-825`):

```rust
        if let Some(conflict) = self.tester_clash(cx) {
            return conflict;
        }
```

**Placement is load-bearing.** It must precede `has_undetermined_class`'s `Unknown` fence and `constructor_graph_find_cycle`, on the principle `check` already documents for `instantiate_injectivity_selectors`: a rule that returns `Sat` or `Unknown` must not short-circuit a pending conflict. Putting it beside `constructor_clash` at the top satisfies that.

- [ ] **Step 6: Run the unit tests**

Run: `cargo nextest run -p shinri-dt`

Expected: PASS, all tests including both new ones and every pre-existing one.

- [ ] **Step 7: Run the e2e tests**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfdt_e2e)'`

Expected: PASS, all 27 (21 pre-existing + 6 new). In particular `tester_over_selector_of_a_free_variable_stays_sat` must **still** say `sat` — if it flipped to `unsat`, the rule is over-firing and the fix is wrong in the dangerous direction. Stop and diagnose rather than adjusting the test.

- [ ] **Step 8: Run the oracle that failed in Task 1**

Run:
```bash
cargo nextest run -p shinri-solver --features oracle -E 'binary(qfdt_oracle)' --no-capture
```

Expected: PASS, non-zero discovered count, and `qfdt_random_matches_z3` prints its `N sat / M unsat / K skipped, 0 mismatches` line with both `N > 0` and `M > 0`. Quote that line in the task report — with Task 1's failure it is criterion 4's evidence.

- [ ] **Step 9: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-dt/src/lib.rs crates/shinri-solver/tests/qfdt_e2e.rs
git commit
```

Commit message:
```
fix(dt): slice48 T3 - tester disjointness re-checked after every merge

The rule lived only in DtSolver::assert, against the class as it stood at that
instant, so a constructor arriving later - from collapse_lemma, from
instantiate_constructor, or from EUF congruence - was never compared against
the branch's asserted testers. The verdict therefore depended on SAT's assert
order: `(and ((_ is cons) x) (= x nil))` answered sat, and the same formula
with the conjuncts swapped answered unsat.

assert keeps its copy: the two are one rule at two trigger points.

Closes the Barrett shape; the randomized oracle from T1 now passes.

Claude-Session: https://claude.ai/code/session_014DanY52GZfbnAH4zSApFZY
```

---

### Task 4: `instantiate_constructor` defensive fence

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs:402-404`
- Test: `crates/shinri-dt/src/lib.rs` `mod tests` (append)

**Interfaces:**
- Consumes: `tester_clash` from Task 3.
- Produces: nothing.

- [ ] **Step 1: Add the fence**

`:402` currently reads:

```rust
            if self.ctor_of_class(cx, t).is_some() {
                continue; // class already has a constructor app
            }
```

It skips on *any* constructor and never compares symbols — a live gap before Task 3. With `tester_clash` running earlier in the same `check` call, a class holding a constructor that disagrees with an asserted tester can no longer reach this line. Replace with:

```rust
            if let Some((csym, _)) = self.ctor_of_class(cx, t) {
                // Slice 48: unreachable with a DISAGREEING symbol — `tester_clash`
                // runs earlier in this same `check` call and returns a Conflict
                // for exactly that state, and this loop iterates the same
                // `asserted_testers` record. Kept as a zero-cost fence rather
                // than a second conflict site, which would duplicate
                // `tester_clash` for no measured gain. The unit tests below are
                // the proof, not this branch.
                debug_assert_eq!(
                    csym, ctor,
                    "instantiate_constructor reached a class whose constructor \
                     disagrees with an asserted tester — tester_clash should \
                     have conflicted first"
                );
                continue; // class already has a constructor app
            }
```

- [ ] **Step 2: Add the test that proves the fence is unreachable**

Append to `mod tests`:

```rust
    /// Slice 48 / slice 38 pattern: the `debug_assert` in
    /// `instantiate_constructor` is end-to-end unreachable, and this is its
    /// proof. The state that would trip it — an asserted tester over a class
    /// holding a different constructor — is intercepted by `tester_clash`,
    /// so `check` returns Conflict and never reaches the instantiation loop.
    /// A debug build would panic here if the ordering ever regressed.
    #[test]
    fn instantiate_constructor_never_sees_a_disagreeing_constructor() {
        let mut ctx = Context::new();
        let (list, nil, _cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_cons_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_cons_x);
        dt.new_var(&mut cx, Var::new(1), nil_t);

        let _ = dt.assert(&mut cx, Lit::new(v, true));
        let (xn, nn) = (cx.eq.intern(x), cx.eq.intern(nil_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        // Runs under `cfg(debug_assertions)` in the test profile: reaching the
        // instantiation loop in this state would panic on the debug_assert.
        let verdict = dt.check(&mut cx, Effort::Full);
        assert_eq!(
            tcheck_name(&verdict),
            "Conflict",
            "tester_clash must intercept before instantiate_constructor runs"
        );
    }
```

- [ ] **Step 3: Run the tests**

Run: `cargo nextest run -p shinri-dt`

Expected: PASS. nextest builds tests with `debug_assertions` on, so a regression in the rule ordering surfaces as a panic rather than a silent skip.

- [ ] **Step 4: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-dt/src/lib.rs
git commit
```

Commit message:
```
fix(dt): slice48 T4 - fence instantiate_constructor's presence test

The skip tested for ANY constructor in the class and never compared symbols.
With tester_clash upstream in the same check call the state that made that a
gap is unreachable, so this adds a debug_assert and the test that proves the
ordering rather than a second conflict site. Slice-38 pattern: a zero-cost
defensive fence whose proof is a unit test.

Claude-Session: https://claude.ai/code/session_014DanY52GZfbnAH4zSApFZY
```

---

### Task 5: Full test sweep, hygiene, and PR

**Files:** none modified unless a gate fails.

**Interfaces:**
- Consumes: Tasks 1–4.
- Produces: a pushed branch and an open PR for Task 7's review.

- [ ] **Step 1: Run the fast blocking tier**

Run: `mise run test`

Expected: green, ~5 min. This is the tier CI gates on.

- [ ] **Step 2: Run the FULL unfiltered oracle**

Run:
```bash
cargo nextest run -p shinri-solver --features oracle
```

Expected: green, non-zero discovered count (the slice-47 run at a comparable point discovered 642). **Unfiltered on purpose.** A filtered run once skipped `qfs_differential` and nearly shipped a `Sat → Unknown` string regression on an unrelated slice; this slice changes only `shinri-dt` and test files, but the run is cheap and the failure mode it guards against is not.

Record the discovered/passed counts for the Task 6 report.

- [ ] **Step 3: Run `script_e2e` locally**

Run: `cargo nextest run -p shinri-solver -E 'binary(script_e2e)'`

Expected: green. This slice **shifts completeness** on QF_DT — queries that answered `sat` now answer `unsat` — so a pinned answer may flip. A flip that z3 confirms is an adjudicated flip: re-pin it and say so in the commit. A flip z3 does *not* confirm is a bug — stop and diagnose.

Note the filter form: `binary(script_e2e)`, because `script_e2e` is a binary name. `test(script_e2e)` finds 0 tests and reads as green.

- [ ] **Step 4: Lint and format**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
```

Expected: no diff from `fmt`, no warnings from clippy. CI gates on `fmt --check` and fails fast.

- [ ] **Step 5: Push and open the PR**

```bash
git push -u origin slice48-qfdt-tester-disjointness
gh pr create --base main --title "slice48: QF_DT tester disjointness re-checked after every merge"
```

PR body: the spec's §1 summary, the before/after of the minimal reproducer, and the Task 1 → Task 3 oracle evidence (failed pre-slice, passes now). End with:
```
https://claude.ai/code/session_014DanY52GZfbnAH4zSApFZY
```

- [ ] **Step 6: Confirm CI is green**

Run: `gh pr checks --watch`

Do not proceed to the merge while any check is red.

---

### Task 6: QF_DT corpus re-run and report

The gate that decides whether this slice delivered. Slice 42 was fully implemented with green reviews and delivered zero; only the measured end-to-end run caught it.

**Files:**
- Create: `docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md`
- Modify: `docs/superpowers/specs/2026-09-10-shinri-slice48-qfdt-tester-disjointness-design.md` (append `## 11. Measured outcomes`)

**Interfaces:**
- Consumes: the merged (or PR-green) branch build.
- Produces: the report and the spec's measured-outcomes section.

- [ ] **Step 1: Run the corpus**

```bash
BENCH_LOGICS=QF_DT BENCH_RUN_ID=slice48 mise run bench-run
```

Same limits as the baseline (20 s / 3072 MB / 6 jobs). 8,700 QF_DT instances — the same paths as the baseline, so every row is a same-path comparison rather than a resample.

Budget 30–60 minutes and check an interim read rather than assuming: baseline QF_DT is fast in the median (6 ms) but carries 507 timeouts at 20 s each. Slice 47's estimate was off by an order of magnitude for exactly this reason, so project from an interim row count before walking away.

- [ ] **Step 2: Render the report**

```bash
BENCH_RUN_ID=slice48 mise run bench-report
```

Renders `bench/results/slice48/report.md` from `bench/results/slice48/results.jsonl`. Both are git-ignored — the narrative document in Step 4 is what gets committed.

- [ ] **Step 3: Compute the transition matrix against the baseline**

Compare `bench/results/slice48/results.jsonl` against the baseline run's rows path-by-path. You need, per family (`20172804-Barrett`, `20230720-blocksworld`, `20210312-Bouvier`):

- wrong → {correct, timeout, unknown, other}
- correct → {timeout, unknown, oom} — **criterion 2, and it must be zero**
- every other changed cell

- [ ] **Step 4: Write the report**

Create `docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md`, following the structure of `2026-09-09-smtlib-2024-qfabv-slice47-report.md`: headline, per-logic matrix, verdict counts baseline vs. slice48, transitions (changed cells only, same-path comparison), success criteria, oracle evidence, and a "Queued for the next slice" section.

Success criteria to report, from spec §6:

| # | criterion | baseline | gate |
| --- | --- | ---: | --- |
| 1 | `20172804-Barrett` wrong rows | 166 | **0** — hard gate |
| 2 | `correct → timeout` / `correct → unknown` / `correct → oom` transitions | — | **0** — hard gate |
| 3 | QF_DT `correct` | 7,849 | ≥ 7,849 |
| 4 | the randomized generator failed pre-slice and passes now | — | yes |
| 5 | `20230720-blocksworld` wrong rows | 162 | **measured and reported, not gated** |

Report criterion 4 by quoting Task 1's verbatim failure and Task 3 Step 8's passing summary line.

For criterion 5, report the number whatever it is. If blocksworld moved, the spec's premise that it is a different bug was wrong — say so plainly in the report; that is a finding, not a failure. If a criterion is missed, **decompose it rather than relaxing it**: that is what slice 47's criterion-3 post-mortem did, and criterion 2 is shaped as a transition count precisely so a miss means something specific.

- [ ] **Step 5: Append measured outcomes to the spec**

Add `## 11. Measured outcomes` to the spec, mirroring slice 47's: the criteria table with verdicts, what the transitions actually were, and any hypothesis this run discarded.

- [ ] **Step 6: Commit**

```bash
git add docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md \
        docs/superpowers/specs/2026-09-10-shinri-slice48-qfdt-tester-disjointness-design.md
git commit
```

Commit message:
```
docs(bench+spec): slice48 - QF_DT re-run report and measured outcomes

Claude-Session: https://claude.ai/code/session_014DanY52GZfbnAH4zSApFZY
```

---

### Task 7: Whole-branch review

Not a substitute for per-task review — an addition to it. Slice 44's whole-branch review caught a Critical that all seven of its task reviews missed, and it was an identity/keying defect in a soundness path. This slice's Task 2 is exactly that kind of change: which tester belongs to which level.

**Files:** none unless the review finds something.

- [ ] **Step 1: Review the full branch diff against the spec**

```bash
git diff main...slice48-qfdt-tester-disjointness
```

Review the **whole diff at once**, not task by task. Specific things to hunt, each drawn from a way this slice could be wrong:

1. **The `pop` off-by-one.** Walk `push`/`pop` by hand for: assert at level 0 then `pop(0)`; assert at level 2 then `pop(1)`; two asserts at different levels then `pop(0)`; `pop` to a level deeper than any open scope. Does `tester_marks` stay consistent with `asserted_testers.len()` in every case?
2. **The dedup interaction with retraction.** A tester asserted at level 1, then again at level 2: the set dedups, so only one entry exists, taken at level 1. Does `pop(1)` correctly *keep* it? Does the reverse order behave?
3. **Polarity.** `tester_clash` builds `Lit::new(var, true)`. Confirm `assert` really does return early for negative literals (`:789-791`), so the record can only hold positive assertions.
4. **Over-firing.** Is there any path where `ctor_of_class` returns a constructor that is a candidate rather than an established class member? That would be a wrong-`unsat`, which is worse than the wrong-`sat` this slice fixes.
5. **Rule ordering in `check`.** Confirm `tester_clash` precedes `has_undetermined_class` and `constructor_graph_find_cycle`.

- [ ] **Step 2: Verify any claimed-blocked or unreachable path by direct repro**

If the review concludes a path is unreachable, do not accept it on a read. Construct the state and run it — a read-found defect is not a diagnosis until a named reproducer traces to that path, and an "unreachable" claim is the same kind of assertion in reverse.

- [ ] **Step 3: Fix findings, re-run the gates, and merge on green**

Any fix repeats Task 5's gates: `mise run test`, the full unfiltered `--features oracle` run, `script_e2e`, `cargo fmt --all`, `mise run lint`.

Then, once CI is green:

```bash
gh pr merge --merge
git checkout main && git pull
git branch -d slice48-qfdt-tester-disjointness
git push origin --delete slice48-qfdt-tester-disjointness
git remote prune origin
```

- [ ] **Step 4: Queue what this slice did not fix**

Confirm the report's "Queued for the next slice" section records:

- **`20230720-blocksworld`, 162 wrong rows** — no testers anywhere in the family, so this slice's rule cannot be the cause; five candidate shapes (enum clash, same-constructor injectivity conflict, nested-chain clash, record selector round-trip, selector-through-equality) all answer correctly. Needs a real bisect. Cheapest reproducer: `blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_5.smt2` (21,247 B, answers in 0.95 s). Whatever Task 6 measured about these rows is the starting evidence.
- **QF_DT's 507 `timeout`, 11 `unknown`, 5 `unverified` rows** — out of scope per spec §2, still in the slice-46 queue.
- **Approach B (propagating `¬is-D(t)`)** — banked per spec §8, un-banked only on a measured thrash signal.
