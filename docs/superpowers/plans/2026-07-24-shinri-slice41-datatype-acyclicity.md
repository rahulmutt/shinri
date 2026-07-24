# Slice 41 — Datatype Acyclicity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn the slice-40 cyclic-constructor-graph fence (`TCheck::Unknown`) into a proven `unsat` carrying a minimal cycle-explanation conflict clause, so `x = cons(h, x)` and longer datatype cycles decide `unsat`.

**Architecture:** Reuse slice-40's iterative-DFS occurs-check unchanged in shape, but have it return the *ordered cycle* it finds instead of a bare `bool`. `DtSolver::check` then builds an `EqLeaf` conflict from the merge-equalities along that cycle (`explain(field_i ↔ next_capp_i)` per edge) — mirroring how `constructor_clash` already cites leaves directly — and returns `TCheck::Conflict`. No new sorts, ops, registry fields, Combiner slot, N-O hooks, or explanation tags.

**Tech Stack:** Rust; `shinri-dt` crate (`crates/shinri-dt/src/lib.rs`); `shinri-theory` (`TCheck::Conflict`, `EqLeaf`, `EqualityEngine::{intern,find,explain,merge}`, `EqJust`); `shinri-solver` e2e + oracle tests; `cargo nextest`; z3 + cvc5 oracles via mise.

## Global Constraints

- **Oracle tests are feature-gated:** `cargo nextest run -p shinri-solver --features oracle`. **Without `--features oracle` the oracle suite silently compiles to zero tests** — never report a flagless run as coverage; confirm the discovered test count is non-zero.
- **Completeness-shifting slice:** run `script_e2e` locally pre-push. The `x = cons(h, x)` flip `unknown → unsat` is z3/cvc5-confirmed — an adjudicated flip, not a regression.
- **Soundness invariant:** a conflict must cite a non-empty antecedent whenever it claims `unsat`. A determined cycle in the real pipeline always has an asserted antecedent (constructor apps enter classes via asserted equalities or learnt guarded lemmas), so `explain` over its edges is non-empty; an *empty* conflict would be an unsound "unsat with no reason".
- **Pure-Rust mandate:** no native-link dependencies (nothing new is added here).
- **Hygiene gates:** `cargo fmt --all` before pushing (CI `fmt --check` fails fast); `mise run lint` clean (clippy `-D warnings`).
- **PR-tier budget:** 10–15 min wall-clock; all additions here are small and fast — no exhaustive suites.

---

### Task 1: Detector returns the cycle path (pure refactor, verdict unchanged)

Refactor the occurs-check to hand back the ordered cycle, while keeping `check`'s verdict byte-for-byte identical (still `Unknown` on a cycle). This isolates the graph-traversal change from the conflict change so a reviewer can gate it on "no behavior change, existing tests still green".

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs` — replace `ctor_child_class_reps` (`:467`) and `constructor_graph_has_cycle` (`:495`); update the single call site in `check` (`:761`).
- Test: `crates/shinri-dt/src/lib.rs` (`#[cfg(test)] mod tests`).

**Interfaces:**
- Produces:
  - `fn children_of(&self, cx: &mut TheoryCtx, rep: ENodeId) -> Option<(TermId, Vec<(TermId, ENodeId)>)>` — for the first registered constructor app in class `rep`, returns `(capp, [(field_term, child_rep) …])` over its datatype-sorted fields. `None` if the class holds no constructor app (undetermined / leaf).
  - `fn constructor_graph_find_cycle(&self, cx: &mut TheoryCtx) -> Option<Vec<(TermId, TermId)>>` — `Some(edges)` where each edge is `(field_term, next_capp)` along a cycle; `None` if the determined constructor graph is acyclic. Iterative DFS, never recursive (untrusted depth).
- Consumes: nothing from other tasks.

- [ ] **Step 1: Write the failing test — the detector surfaces the self-cycle edge**

Add to `mod tests` (reuses the existing `list_dt` / `uconst` helpers):

```rust
#[test]
fn find_cycle_returns_the_self_edge_for_x_eq_cons_h_x() {
    // x = cons(h, x): one datatype-sorted field (tail = x) points back to x's
    // own class → a single self-edge (field = the x subterm, next_capp = cons(h,x)).
    let mut ctx = Context::new();
    let (list, _nil, cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
    let int = ctx.int_sort();
    let h = uconst(&mut ctx, "h", int);
    let x = uconst(&mut ctx, "x", list);
    let cons_hx = ctx.mk_app(Op::Uninterpreted(cons), &[h, x]).unwrap();
    let atom = ctx.mk_eq(x, cons_hx).unwrap();

    let mut dt = DtSolver::default();
    let mut eq = EqualityEngine::default();
    let atoms = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
    dt.new_var(&mut cx, Var::new(0), atom);
    let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(cons_hx));
    let _ = cx.eq.merge(xn, cn, EqJust::Asserted(Lit::new(Var::new(0), true)));

    let cycle = dt.constructor_graph_find_cycle(&mut cx).expect("cycle expected");
    assert_eq!(cycle.len(), 1, "self-cycle has exactly one edge");
    let (field, next_capp) = cycle[0];
    // the edge's field is in the same class as x, and next_capp is cons(h,x)
    assert_eq!(cx.eq.find(cx.eq.intern(field)), cx.eq.find(xn));
    assert_eq!(next_capp, cons_hx);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo nextest run -p shinri-dt find_cycle_returns_the_self_edge_for_x_eq_cons_h_x`
Expected: FAIL to compile — `constructor_graph_find_cycle` does not exist yet (only `constructor_graph_has_cycle`).

- [ ] **Step 3: Replace `ctor_child_class_reps` with `children_of`**

Replace the whole `ctor_child_class_reps` fn (`:467`–`:485`) with:

```rust
/// For the first registered constructor application in class `rep`, return
/// `(capp, edges)` where `edges` lists, per datatype-sorted field, the pair
/// `(field_term, child_class_rep)`. `None` when the class holds no
/// constructor app (undetermined / leaf). The field `TermId` and `capp`
/// `TermId` are retained (not reduced to reps) so the acyclicity conflict can
/// cite the merge-equality `field = next_capp` along each cycle edge.
fn children_of(
    &self,
    cx: &mut TheoryCtx,
    rep: ENodeId,
) -> Option<(TermId, Vec<(TermId, ENodeId)>)> {
    for &capp in &self.ctor_apps {
        let capp_n = cx.eq.intern(capp);
        if cx.eq.find(capp_n) != rep {
            continue;
        }
        let (_, cargs) = Self::uapp(cx.terms, capp)?;
        let kids = cargs
            .iter()
            .copied()
            .filter(|&a| cx.terms.is_datatype_sort(cx.terms.sort_of(a)))
            .map(|a| (a, cx.eq.find(cx.eq.intern(a))))
            .collect();
        return Some((capp, kids));
    }
    None
}
```

- [ ] **Step 4: Replace `constructor_graph_has_cycle` with `constructor_graph_find_cycle`**

Replace the whole `constructor_graph_has_cycle` fn (`:495`–`:535`) with:

```rust
/// The ordered cycle in the constructor graph over the currently determined
/// classes, or `None` if it is acyclic. Each edge is `(field_term,
/// next_capp)`: the datatype-sorted field of one constructor application, and
/// the constructor application sitting in the class that field points to. A
/// cycle means the only ground model is an infinite term; slice 41 turns it
/// into a proven `unsat` (the caller builds the conflict). Iterative (explicit
/// DFS stack), never recursive: the term graph comes from untrusted input and
/// may be arbitrarily deep (threat model).
fn constructor_graph_find_cycle(&self, cx: &mut TheoryCtx) -> Option<Vec<(TermId, TermId)>> {
    struct Frame {
        rep: ENodeId,
        capp: TermId,
        via_field: Option<TermId>, // field of the parent's capp that reached this frame
        kids: Vec<(TermId, ENodeId)>,
    }
    let mut done: FxHashSet<ENodeId> = FxHashSet::default();
    for t in self.watched_dt_terms() {
        let root = cx.eq.find(cx.eq.intern(t));
        if done.contains(&root) {
            continue;
        }
        let Some((capp, kids)) = self.children_of(cx, root) else {
            done.insert(root);
            continue;
        };
        // grey rep -> its index in `stack`, for O(1) back-edge / cycle slicing.
        let mut on_path: FxHashMap<ENodeId, usize> = FxHashMap::default();
        on_path.insert(root, 0);
        let mut stack: Vec<Frame> = vec![Frame { rep: root, capp, via_field: None, kids }];
        while let Some(top) = stack.last_mut() {
            let Some((field, child)) = top.kids.pop() else {
                let f = stack.pop().unwrap();
                on_path.remove(&f.rep);
                done.insert(f.rep);
                continue;
            };
            if let Some(&i) = on_path.get(&child) {
                // Back-edge: build the cycle stack[i..] plus the closing edge.
                let mut edges: Vec<(TermId, TermId)> = Vec::new();
                edges.push((field, stack[i].capp)); // closing: top's field -> child's capp
                for f in &stack[i + 1..] {
                    edges.push((f.via_field.expect("non-root frame has a via_field"), f.capp));
                }
                return Some(edges);
            }
            if done.contains(&child) {
                continue;
            }
            let Some((ccapp, ckids)) = self.children_of(cx, child) else {
                done.insert(child);
                continue;
            };
            on_path.insert(child, stack.len());
            stack.push(Frame { rep: child, capp: ccapp, via_field: Some(field), kids: ckids });
        }
    }
    None
}
```

Add `use rustc_hash::FxHashMap;` alongside the existing `FxHashSet` import if not already present (check the top of the file; `FxHashSet` is already imported — extend that `use`).

- [ ] **Step 5: Keep `check`'s verdict identical**

At `:761`, change the fence predicate to use the new fn but keep `Unknown`:

```rust
if self.has_undetermined_class(cx) || self.constructor_graph_find_cycle(cx).is_some() {
    return TCheck::Unknown;
}
TCheck::Sat
```

- [ ] **Step 6: Run the new test + the slice-40 regression tests**

Run: `cargo nextest run -p shinri-dt find_cycle_returns_the_self_edge_for_x_eq_cons_h_x cyclic_constructor_graph_fences_to_unknown determined_acyclic_datatype_child_renders_full_nested_term`
Expected: all PASS — the detector returns the cycle, and `check` still answers `Unknown` on the cyclic case and `Sat` on the acyclic one (no behavior change).

- [ ] **Step 7: Run the whole dt crate to confirm no regression**

Run: `cargo nextest run -p shinri-dt`
Expected: PASS (all existing tests green; the only change is an internal refactor).

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-dt/src/lib.rs
git commit -m "refactor(dt): slice41 T1 — occurs-check returns the ordered cycle path (verdict unchanged)"
```

---

### Task 2: Cyclic determined state → `Conflict` with a minimal cycle-explanation clause

Flip the fence: a determined cycle becomes `TCheck::Conflict` citing exactly the merge-equalities along the cycle. The undetermined-class branch keeps returning `Unknown` (slice-42 territory).

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs` — add `acyclicity_conflict`; split the fence in `check` (`:761`); update the `explain` doc comment (`:767`).
- Test: `crates/shinri-dt/src/lib.rs` (`mod tests`).

**Interfaces:**
- Consumes: `constructor_graph_find_cycle` (Task 1).
- Produces: `fn acyclicity_conflict(&self, cx: &mut TheoryCtx, edges: Vec<(TermId, TermId)>) -> TCheck` — builds `TCheck::Conflict(leaves)` by `explain`-ing each edge's `field ↔ next_capp` equality.

- [ ] **Step 1: Write the failing tests**

Rewrite the existing `cyclic_constructor_graph_fences_to_unknown` test (`:1535`–`:1580`) into a conflict test (rename it), and add two more. Note the key change vs the slice-40 test: merge via `EqJust::Asserted(lit)` — **not** `EqJust::Definitional`, which `explain` contributes *zero* leaves for (`eq_engine.rs:448`), so a Definitional merge would yield a vacuous empty conflict. Add `EqLeaf` to the test-module `use` (`use shinri_theory::{… EqLeaf …}` or reference `shinri_theory::types::EqLeaf`).

```rust
#[test]
fn cyclic_constructor_graph_is_conflict_citing_the_asserted_equality() {
    // x = cons(h, x): determined, cyclic → proven unsat by acyclicity. The
    // conflict cites exactly the one asserted equality that formed the cycle.
    let mut ctx = Context::new();
    let (list, _nil, cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
    let int = ctx.int_sort();
    let h = uconst(&mut ctx, "h", int);
    let x = uconst(&mut ctx, "x", list);
    let cons_hx = ctx.mk_app(Op::Uninterpreted(cons), &[h, x]).unwrap();
    let atom = ctx.mk_eq(x, cons_hx).unwrap();

    let mut dt = DtSolver::default();
    let mut eq = EqualityEngine::default();
    let atoms = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
    dt.new_var(&mut cx, Var::new(0), atom);
    let eq_lit = Lit::new(Var::new(0), true);
    let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(cons_hx));
    let _ = cx.eq.merge(xn, cn, EqJust::Asserted(eq_lit));

    match dt.check(&mut cx, Effort::Full) {
        TCheck::Conflict(leaves) => {
            assert_eq!(
                leaves,
                vec![shinri_theory::types::EqLeaf::Asserted(eq_lit)],
                "minimal cycle path cites exactly the asserted x = cons(h, x)"
            );
        }
        other => panic!("cyclic determined state must be Conflict, got {}", tcheck_name(&other)),
    }
}

#[test]
fn mutual_cycle_is_conflict_citing_both_equalities() {
    // x = cons(1, y) ∧ y = cons(2, x): a two-node cycle → unsat, conflict cites
    // both asserted equalities.
    let mut ctx = Context::new();
    let (list, _nil, cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
    let int = ctx.int_sort();
    let one = uconst(&mut ctx, "one", int);
    let two = uconst(&mut ctx, "two", int);
    let x = uconst(&mut ctx, "x", list);
    let y = uconst(&mut ctx, "y", list);
    let cons_1y = ctx.mk_app(Op::Uninterpreted(cons), &[one, y]).unwrap();
    let cons_2x = ctx.mk_app(Op::Uninterpreted(cons), &[two, x]).unwrap();
    let e0 = ctx.mk_eq(x, cons_1y).unwrap();
    let e1 = ctx.mk_eq(y, cons_2x).unwrap();

    let mut dt = DtSolver::default();
    let mut eq = EqualityEngine::default();
    let atoms = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
    dt.new_var(&mut cx, Var::new(0), e0);
    dt.new_var(&mut cx, Var::new(1), e1);
    let (l0, l1) = (Lit::new(Var::new(0), true), Lit::new(Var::new(1), true));
    let _ = cx.eq.merge(cx.eq.intern(x), cx.eq.intern(cons_1y), EqJust::Asserted(l0));
    let _ = cx.eq.merge(cx.eq.intern(y), cx.eq.intern(cons_2x), EqJust::Asserted(l1));

    match dt.check(&mut cx, Effort::Full) {
        TCheck::Conflict(leaves) => {
            assert_eq!(leaves.len(), 2, "two cycle edges → two asserted leaves");
            assert!(leaves.contains(&shinri_theory::types::EqLeaf::Asserted(l0)));
            assert!(leaves.contains(&shinri_theory::types::EqLeaf::Asserted(l1)));
        }
        other => panic!("mutual cycle must be Conflict, got {}", tcheck_name(&other)),
    }
}

#[test]
fn cycle_through_undetermined_class_stays_unknown_not_conflict() {
    // x = cons(h, x) but x's tail is left undetermined by never determining the
    // class the cycle would pass through: an undetermined watched class must
    // fence to Unknown (slice-42 territory), never a false acyclicity conflict.
    // Registering a bare undetermined datatype term alongside forces the
    // has_undetermined_class branch first.
    let mut ctx = Context::new();
    let (list, _nil, _cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
    let z = uconst(&mut ctx, "z", list); // bare, undetermined

    let mut dt = DtSolver::default();
    let mut eq = EqualityEngine::default();
    let atoms = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
    dt.new_var(&mut cx, Var::new(0), z);

    assert!(
        matches!(dt.check(&mut cx, Effort::Full), TCheck::Unknown),
        "an undetermined class must fence to Unknown before the cycle walk"
    );
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo nextest run -p shinri-dt cyclic_constructor_graph_is_conflict_citing_the_asserted_equality mutual_cycle_is_conflict_citing_both_equalities cycle_through_undetermined_class_stays_unknown_not_conflict`
Expected: the two cycle tests FAIL (current `check` returns `Unknown`, not `Conflict`); the undetermined test may already PASS.

- [ ] **Step 3: Add `acyclicity_conflict`**

Add near `constructor_graph_find_cycle`:

```rust
/// Build the acyclicity conflict from a cycle's edges. For each edge the one
/// fact that closes it is the merge equality `field = next_capp`; the
/// constructor applications sit in their classes definitionally and the
/// syntactic `C(…)` structure needs no citation. Leaves are cited directly
/// (no dedup) exactly as `constructor_clash` does — `Combiner::expand_conflict`
/// sorts and dedups the final learnt clause. In the real pipeline every edge
/// equality carries an asserted antecedent, so `leaves` is non-empty (an empty
/// conflict would be an unsound "unsat with no reason").
fn acyclicity_conflict(&self, cx: &mut TheoryCtx, edges: Vec<(TermId, TermId)>) -> TCheck {
    let mut leaves = Vec::new();
    for (field, next_capp) in edges {
        let fnode = cx.eq.intern(field);
        let cnode = cx.eq.intern(next_capp);
        cx.eq.explain(fnode, cnode, &mut leaves);
    }
    TCheck::Conflict(leaves)
}
```

- [ ] **Step 4: Split the fence in `check`**

Replace the fence block (`:761`–`:764`, now using `find_cycle().is_some()` from Task 1) with:

```rust
// Model-tied residual fence (spec §5). An undetermined class that survived
// splitting stays Unknown (defensive; slice 42 leaves infinite-sort terms
// free). A cycle in the constructor graph over determined classes is a proven
// `unsat` by datatype acyclicity — build the minimal cycle-explanation
// conflict. MUST be the last step: every lemma rule above must be saturated
// first. The undetermined check precedes the cycle walk so the walk only ever
// runs over fully-determined classes (a cycle through an undetermined class is
// caught as Unknown, never mis-reported as a conflict).
if self.has_undetermined_class(cx) {
    return TCheck::Unknown;
}
if let Some(edges) = self.constructor_graph_find_cycle(cx) {
    return self.acyclicity_conflict(cx, edges);
}
TCheck::Sat
```

- [ ] **Step 5: Update the `explain` doc comment (stays a no-op)**

Replace the `explain` body comment (`:768`) to reflect that slice 41 adds no tag:

```rust
fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
    // DT conflicts (constructor clash, acyclicity) cite EqLeafs directly via
    // TCheck::Conflict; the mint_eq_tag/explain channel is for propagations,
    // which this theory does not emit. No tags of its own.
}
```

- [ ] **Step 6: Run the new tests + the acyclic-Sat regression**

Run: `cargo nextest run -p shinri-dt cyclic_constructor_graph_is_conflict_citing_the_asserted_equality mutual_cycle_is_conflict_citing_both_equalities cycle_through_undetermined_class_stays_unknown_not_conflict determined_acyclic_datatype_child_renders_full_nested_term`
Expected: all PASS — cycles are `Conflict` with the minimal leaves, acyclic stays `Sat`, undetermined stays `Unknown`.

- [ ] **Step 7: Run the whole dt crate**

Run: `cargo nextest run -p shinri-dt`
Expected: PASS. (If any *other* slice-40 test asserted `Unknown` on a determined cyclic shape, it must be updated to `Conflict` here and noted in the commit — the fences_to_unknown test is the only such case and was rewritten in Step 1.)

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-dt/src/lib.rs
git commit -m "feat(dt): slice41 T2 — determined cycle → unsat via minimal cycle-explanation conflict"
```

---

### Task 3: End-to-end flip + longer cycle (`shinri-solver`)

Flip the pinned slice-40 `unknown` e2e case to `unsat` and add a mutual-cycle case, proving the fence-lift end to end through the real Combiner/SAT pipeline.

**Files:**
- Modify: `crates/shinri-solver/tests/qfdt_e2e.rs` — rewrite `cyclic_equation_is_unknown_until_slice41` (`:295`–`:314`); add a mutual-cycle test.

**Interfaces:**
- Consumes: `run_script` (`:10`) and the `LIST` fixture (`:30`), both already in the file.

- [ ] **Step 1: Rewrite the pinned case to expect `unsat`**

Replace `cyclic_equation_is_unknown_until_slice41` (`:295`–`:314`) with:

```rust
#[test]
fn cyclic_self_reference_is_unsat() {
    // x = cons(h, x) has no finite ground model and, by datatype acyclicity, no
    // model at all. Slice 40 fenced this to `unknown`; slice 41 proves `unsat`
    // via the cycle-explanation conflict. Adjudicated completeness flip
    // (z3/cvc5 agree unsat), not a regression.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)(declare-fun h () Int)\
         (assert (= x (cons h x)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn mutual_cycle_is_unsat() {
    // x = cons(1, y) ∧ y = cons(2, x): a two-node datatype cycle → unsat.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)(declare-fun y () List)\
         (assert (= x (cons 1 y)))(assert (= y (cons 2 x)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}
```

- [ ] **Step 2: Run the two e2e tests**

Run: `cargo nextest run -p shinri-solver -E 'test(cyclic_self_reference_is_unsat) or test(mutual_cycle_is_unsat)'`
Expected: PASS (both `unsat`).

- [ ] **Step 3: Run the whole e2e file to confirm regression anchors hold**

Run: `cargo nextest run -p shinri-solver -E 'test(qfdt_e2e)'`
Expected: PASS — the acyclic `sat` and exhaustiveness `unsat` anchors are unchanged.

- [ ] **Step 4: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfdt_e2e.rs
git commit -m "test(dt): slice41 T3 — e2e cyclic self-reference and mutual cycle decide unsat"
```

---

### Task 4: Oracle differential vs z3 + cvc5

Add cyclic cases to the feature-gated oracle suite; now that they decide `unsat`, route them through `agree_decided` so a regression back to `unknown` fails loudly.

**Files:**
- Modify: `crates/shinri-solver/tests/qfdt_oracle.rs` — add two tests using `agree_decided` (`:127`).

**Interfaces:**
- Consumes: `agree_decided` (`:127`) and the `LIST` fixture (`:107`), both already in the file. `agree_decided` asserts `ours != "unknown"` then cross-checks z3.

- [ ] **Step 1: Add the cyclic oracle cases**

Append near the other `qfdt_oracle_*` tests:

```rust
#[test]
fn qfdt_oracle_cyclic_self_reference() {
    // x = cons(h, x): z3/cvc5 return unsat by acyclicity; slice 41 must too.
    agree_decided("(declare-fun x () List)(declare-fun h () Int)(assert (= x (cons h x)))");
}

#[test]
fn qfdt_oracle_cyclic_mutual() {
    // x = cons(1, y) ∧ y = cons(2, x): mutual datatype cycle → unsat.
    agree_decided(
        "(declare-fun x () List)(declare-fun y () List)\
         (assert (= x (cons 1 y)))(assert (= y (cons 2 x)))",
    );
}
```

- [ ] **Step 2: Run the oracle suite WITH the feature flag and confirm non-zero test count**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfdt_oracle)'`
Expected: PASS, and the nextest summary shows a **non-zero** number of tests run (a flagless run compiles the file to zero tests and proves nothing). Confirm `qfdt_oracle_cyclic_self_reference` and `qfdt_oracle_cyclic_mutual` appear in the run.

- [ ] **Step 3: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfdt_oracle.rs
git commit -m "test(dt): slice41 T4 — QF_DT oracle differential for cyclic unsat vs z3/cvc5"
```

---

### Task 5: Gates, script_e2e, and PR

Run the full local gate set (this slice shifts completeness) and open the slice PR bundling the spec, plan, and implementation.

**Files:**
- Modify: none (verification + PR).

- [ ] **Step 1: Format and lint**

Run: `cargo fmt --all && mise run lint`
Expected: `fmt` makes no changes (already run per-task); clippy clean with `-D warnings`.

- [ ] **Step 2: Full dt + solver test run (non-oracle) and the completeness gate**

Run: `cargo nextest run -p shinri-dt && cargo nextest run -p shinri-solver -E 'test(qfdt_e2e) or test(script_e2e)'`
Expected: PASS. `script_e2e` is the completeness-shifting gate — confirm any changed pins are the adjudicated `unknown → unsat` cyclic flips, not unexpected regressions.

- [ ] **Step 3: Oracle differential (feature-gated), full unfiltered run**

Run: `cargo nextest run -p shinri-solver --features oracle`
Expected: PASS with non-zero test count. Run the **full** oracle suite (not a `-E 'test(qfdt_oracle)'` filter) so any shared-core regression in the broader differential (e.g. a string Sat→Unknown) is caught, per project discipline.

- [ ] **Step 4: Commit the plan doc (bundled with the already-committed spec)**

```bash
git add docs/superpowers/plans/2026-07-24-shinri-slice41-datatype-acyclicity.md
git commit -m "docs(dt): slice41 implementation plan — datatype acyclicity, cycle→unsat conflict"
```

- [ ] **Step 5: Push and open the PR**

```bash
git push -u origin slice41-datatype-acyclicity
gh pr create --base main --title "slice41: datatype acyclicity — cycle → unsat" \
  --body "Turns the slice-40 cyclic-constructor-graph fence (Unknown) into a proven unsat with a minimal cycle-explanation conflict clause. Spec + plan in docs/superpowers/{specs,plans}/2026-07-24-shinri-slice41-*. Oracle differential (z3/cvc5) confirms the x=cons(h,x) unknown→unsat flip. See spec §5 for the explain-stays-no-op correction to slice-40 §5.E."
```

Expected: PR opens against `main`. Merge with a merge commit when CI is green, then delete the branch (remote + local) and prune, per the standing merge-on-green discipline.

---

## Self-Review

**Spec coverage:**
- Spec §1 (cycle → unsat) → Tasks 1–2. ✓
- Spec §2 (no new surface; `TCheck::Conflict` direct-cite; no tag) → Task 2 Steps 3–5. ✓
- Spec §3 (detector refactor: `children_of` carries field+capp; reconstruct ordered edges) → Task 1. ✓
- Spec §4 (minimal cycle path conflict; structure needs no citation) → Task 2 Step 3 + the self-cycle leaf-set assertion (Task 2 Step 1). ✓
- Spec §5 (fence split; `explain` no-op; residual Unknown = undetermined) → Task 2 Steps 4–5 + `cycle_through_undetermined` test. ✓
- Spec §6 (model/render unchanged) → no task modifies `render_value`; `determined_acyclic…renders_full_nested_term` stays green (Task 1 Step 6, Task 2 Step 6). ✓
- Spec §7 (unit: find_cycle ordered; minimal leaf set; acyclic Sat; cycle-through-undetermined Unknown; e2e flip + longer cycle; oracle non-zero count; gates) → Tasks 1–5. ✓
- Spec §8 (scope-out: finiteness→42, N-O→43) → nothing here touches them. ✓
- Spec §9 (success criteria) → Task 5 gate set. ✓

**Placeholder scan:** No TBD/TODO; every code step shows complete code; commands have expected output. ✓

**Type consistency:** `children_of → (TermId, Vec<(TermId, ENodeId)>)`, `constructor_graph_find_cycle → Option<Vec<(TermId, TermId)>>`, `acyclicity_conflict(edges: Vec<(TermId, TermId)>) → TCheck` — the `(field, next_capp)` edge tuple type is consistent across Task 1 (produce) and Task 2 (consume). `EqJust::Asserted(Lit::new(Var::new(_), true))` and `EqLeaf::Asserted` are the verified names/paths. ✓
