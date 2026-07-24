# Slice 40 — Datatype tester case-splitting Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add exhaustiveness case-splitting and lazy constructor instantiation to `DtSolver` so shinri decides the non-cyclic QF_DT `sat` fragment end to end, replacing slice 39's coarse completeness fence with a sound model-tied one.

**Architecture:** Two new rules in `DtSolver::check`, both riding the existing `TCheck::Split` channel. Rule 1 (exhaustiveness) emits the tester disjunction `is-C₁(t) ∨ … ∨ is-Cₙ(t)` (a `guard: None` tautology) for an undetermined watched datatype class. Rule 2 (instantiation) emits the guarded lemma `is-C(t) ⇒ t = C(sel₁(t), …)` for a tester asserted true, minting and watching the constructor's field selectors so collapse fires and datatype fields recurse. Laziness lives in Rule 2 being gated on *asserted* testers, so only the branch's chosen constructor is ever instantiated; termination is closed by nullary-first phase preference plus a constructor-graph occurs-check that returns `Unknown` (not `sat`) on cyclic states.

**Tech Stack:** Rust, `shinri-dt` crate (`crates/shinri-dt/src/lib.rs`), `shinri-theory` (`TCheck::Split`, `AtomRegistry::var_of_atom`, `EqualityEngine::find`), `shinri-solver` integration/oracle tests, `cargo nextest`, z3 + cvc5 oracles via mise.

## Global Constraints

- **Pure-Rust mandate:** no native-link deps; nothing in this slice adds a dependency (`deny.toml` bans `rug`, `z3-sys`, etc.).
- **No panics on hostile input:** `declare-datatypes` is untrusted (`docs/threat-model.md`); this slice adds no new parser surface, but any new term-graph walk that could be deep on hostile input must be iterative, not recursive (matches `dt_first_ill_founded`).
- **Blocking PR tier budget 10–15 min:** all tests added here are small and fast; add no exhaustive/`#[ignore]`d suites.
- **Oracle tests are feature-gated:** `cargo nextest run -p shinri-solver --features oracle`. **Without `--features oracle` the oracle suite silently runs zero tests** — never report a flagless run as coverage.
- **Hygiene gates:** `cargo fmt --all` before pushing (CI `fmt --check` fails fast); `cargo clippy --workspace --all-targets -- -D warnings` clean; run `script_e2e` locally pre-push (this slice shifts completeness).
- **Soundness invariant:** never report `sat` on a state whose only ground model is infinite (cyclic). `unknown` is the sound under-approximation until slice 41.

---

## File Structure

- **Modify** `crates/shinri-dt/src/lib.rs` — new struct fields, `exhaustiveness_split`, `instantiate_constructor`, `constructor_graph_has_cycle`, `ctor_child_class_reps`; rewrite `render_value` and `check`; extend `assert`. Unit tests appended to the in-file `#[cfg(test)] mod tests`.
- **Modify** `crates/shinri-solver/tests/qfdt_e2e.rs` — new end-to-end `.smt2` cases (unsat via exhaustiveness, sat via instantiation, mutual recursion, pinned `unknown`).
- **Modify** `crates/shinri-solver/tests/qfdt_oracle.rs` — new feature-gated differential cases vs z3/cvc5.
- **Modify** the fuzz corpus seed area used by `qfs_fuzz_corpus.rs` / `parse_script` fuzz — add datatype scripts exercising the split paths (locate the existing DT seeds first; add beside them).

Current anchors in `crates/shinri-dt/src/lib.rs`: struct at `16-35`, `assert` at `457-476`, `check` at `486-520`, `render_value` at `374-415`, `model` at `526-536`, `has_undetermined_class` at `353-361`, `ctor_of_class` at `322-334`.

---

### Task 1: Exhaustiveness split (Rule 1) + struct fields

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs` (struct `16-35`; add method; wire into `check` `486-520`)
- Test: `crates/shinri-dt/src/lib.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `DtSolver::watched_dt_terms`, `ctor_of_class`, `Context::{sort_of, dt_constructors, dt_tester, dt_selectors, mk_app}`, `TCheck::Split`.
- Produces: `fn exhaustiveness_split(&mut self, cx: &mut TheoryCtx) -> Option<TCheck>`; new fields `split_done: FxHashSet<TermId>`, `asserted_testers: FxHashSet<TermId>` (the second is populated in Task 2).

- [ ] **Step 1: Write the failing test**

Append to `mod tests`:

```rust
#[test]
fn undetermined_class_emits_exhaustiveness_disjunction() {
    // A bare List var with no constructor and no tester: Rule 1 must offer the
    // exhaustiveness split `is-nil(x) ∨ is-cons(x)`, guard-free (a tautology),
    // biasing the nullary `nil` branch via phase preference.
    let mut ctx = Context::new();
    let (list, _nil, _cons, _head, _tail, is_nil, is_cons) = list_dt(&mut ctx);
    let x = uconst(&mut ctx, "x", list);
    let y = uconst(&mut ctx, "y", list);
    let atom = ctx.mk_eq(x, y).unwrap();

    let mut dt = DtSolver::default();
    let mut eq = EqualityEngine::default();
    let atoms = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
    dt.new_var(&mut cx, Var::new(0), atom);

    match dt.check(&mut cx, Effort::Full) {
        TCheck::Split { atoms, guard, phases } => {
            assert_eq!(guard, None, "exhaustiveness is a tautology");
            let is_nil_x = cx.terms.mk_app(Op::Uninterpreted(is_nil), &[x]).unwrap();
            let is_cons_x = cx.terms.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();
            assert!(atoms.contains(&is_nil_x) && atoms.contains(&is_cons_x));
            assert_eq!(atoms.len(), 2, "one atom per constructor");
            // Nullary `nil` is preferred true; `cons` carries no preference.
            let nil_pos = atoms.iter().position(|&a| a == is_nil_x).unwrap();
            assert_eq!(phases[nil_pos], Some(true), "nullary-first phase bias");
        }
        other => panic!("expected Split, got {}", tcheck_name(&other)),
    }

    // Deduped: a second check does not re-emit; with no SAT to decide the
    // disjunction the class stays undetermined, so the fence still says Unknown.
    assert!(matches!(dt.check(&mut cx, Effort::Full), TCheck::Unknown));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo nextest run -p shinri-dt undetermined_class_emits_exhaustiveness_disjunction`
Expected: FAIL — currently `check` returns `Unknown` on the first call (no split rule), so the `TCheck::Split` arm panics.

- [ ] **Step 3: Add the struct fields**

In the `DtSolver` struct (after `emitted` at line `28`):

```rust
    /// Slice 40: watched terms whose exhaustiveness disjunction has already
    /// been emitted, so `check` reaches a fixpoint instead of re-offering the
    /// same split. Monotone — the `emitted`/watch-set discipline of slice 39.
    split_done: FxHashSet<TermId>,
    /// Slice 40: tester atoms asserted true — the trigger set for
    /// `instantiate_constructor`. Monotone (never popped): a stale entry from a
    /// backtracked branch only re-emits a GUARDED (hence inert) lemma, never an
    /// unsound one, so retraction is unnecessary and `push`/`pop` stay no-ops.
    asserted_testers: FxHashSet<TermId>,
```

- [ ] **Step 4: Implement `exhaustiveness_split`**

Add after `tester_lemma` (around line `319`):

```rust
    /// Exhaustiveness (slice 40): a watched datatype class with no constructor
    /// application IS some constructor — offer the tester disjunction
    /// `is-C1(t) ∨ … ∨ is-Cn(t)`. Guard-free: it is a T-tautology whose
    /// at-most-one companion is the assert-time tester disjointness (slice 39).
    /// Deduped per watched term. Nullary constructors get a `Some(true)` phase
    /// preference so the SAT search tries finite models first, which bounds the
    /// instantiation descent on recursive types.
    fn exhaustiveness_split(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        for t in self.watched_dt_terms() {
            if self.ctor_of_class(cx, t).is_some() {
                continue; // already constructor-determined
            }
            if !self.split_done.insert(t) {
                continue; // disjunction already offered for this term
            }
            let sort = cx.terms.sort_of(t);
            let Some(ctors) = cx.terms.dt_constructors(sort).map(<[SymbolId]>::to_vec) else {
                continue;
            };
            let mut atoms = Vec::with_capacity(ctors.len());
            let mut phases = Vec::with_capacity(ctors.len());
            for c in ctors {
                let Some(tester) = cx.terms.dt_tester(c) else {
                    continue;
                };
                let is_c_t = cx
                    .terms
                    .mk_app(Op::Uninterpreted(tester), &[t])
                    .expect("tester applies to its own datatype sort");
                let nullary = cx
                    .terms
                    .dt_selectors(c)
                    .is_none_or(<[SymbolId]>::is_empty);
                atoms.push(is_c_t);
                phases.push(if nullary { Some(true) } else { None });
            }
            if atoms.is_empty() {
                continue;
            }
            return Some(TCheck::Split {
                atoms,
                guard: None,
                phases,
            });
        }
        None
    }
```

- [ ] **Step 5: Wire `exhaustiveness_split` into `check`**

In `check`, insert the call immediately before the fence (between the `tester_lemma` block at line `504-506` and the `has_undetermined_class` fence at line `516`):

```rust
        if let Some(split) = self.exhaustiveness_split(cx) {
            return split;
        }
```

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo nextest run -p shinri-dt undetermined_class_emits_exhaustiveness_disjunction`
Expected: PASS

- [ ] **Step 7: Run the full DT unit suite for regressions**

Run: `cargo nextest run -p shinri-dt`
Expected: PASS — including the slice-39 `undetermined_datatype_class_yields_unknown_not_sat` test, which still holds: its second `check` is deduped and falls through to the fence, returning `Unknown`. (If that test now sees a `Split` on its single `check` call, that is expected new behavior — it calls `check` once and asserts `Unknown`; update it to drain one split then assert `Unknown`, mirroring the dedupe check above.)

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-dt/src/lib.rs
git commit -m "feat(dt): slice40 T1 — exhaustiveness split (Rule 1) with nullary-first phase bias"
```

---

### Task 2: Constructor instantiation (Rule 2) + assert recording

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs` (`assert` `457-476`; add method; wire into `check`)
- Test: `crates/shinri-dt/src/lib.rs` (`mod tests`)

**Interfaces:**
- Consumes: `asserted_testers` (Task 1), `ctor_of_class`, `Context::{dt_selectors, mk_app, mk_eq, is_datatype_sort, sort_of}`, `AtomRegistry::var_of_atom`, `Lit::{new, negate}`, `DtRole::Tester`.
- Produces: `fn instantiate_constructor(&mut self, cx: &mut TheoryCtx) -> Option<TCheck>`; `assert` now records positive tester atoms into `asserted_testers`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn asserted_tester_instantiates_guarded_constructor() {
    // is-cons(x) asserted, x's class holds no constructor: Rule 2 must offer the
    // guarded lemma  ¬is-cons(x) ∨ x = cons(head(x), tail(x)),  and register the
    // minted selector apps as watched (head(x) Int-sorted; tail(x) a dt_term).
    let mut ctx = Context::new();
    let (list, _nil, cons, head, tail, _is_nil, is_cons) = list_dt(&mut ctx);
    let x = uconst(&mut ctx, "x", list);
    let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

    let mut dt = DtSolver::default();
    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let v = Var::new(0);
    atoms.register(v, is_cons_x, shinri_theory::types::Owner::Datatypes);
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
    dt.new_var(&mut cx, v, is_cons_x);

    // Assert the tester true; it must be recorded, not conflict (empty class).
    assert!(dt.assert(&mut cx, Lit::new(v, true)).is_none());

    match dt.check(&mut cx, Effort::Full) {
        TCheck::Split { atoms: lemma, guard, .. } => {
            assert_eq!(lemma.len(), 1, "instantiation emits a unit equality");
            let head_x = cx.terms.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
            let tail_x = cx.terms.mk_app(Op::Uninterpreted(tail), &[x]).unwrap();
            let capp = cx.terms.mk_app(Op::Uninterpreted(cons), &[head_x, tail_x]).unwrap();
            let expected = cx.terms.mk_eq(x, capp).unwrap();
            assert_eq!(lemma[0], expected, "x = cons(head(x), tail(x))");
            assert_eq!(guard, Some(Lit::new(v, true).negate()), "guarded by ¬is-cons(x)");
            assert!(dt.watches_sel(head_x) && dt.watches_sel(tail_x), "fields watched");
            assert!(dt.watches_dt_term(tail_x), "datatype field is a watched dt_term");
        }
        other => panic!("expected Split, got {}", tcheck_name(&other)),
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo nextest run -p shinri-dt asserted_tester_instantiates_guarded_constructor`
Expected: FAIL — `assert` does not yet record the tester, and no instantiation rule exists, so `check` returns the exhaustiveness `Split` (wrong atoms) or `Unknown`.

- [ ] **Step 3: Record asserted testers in `assert`**

In `assert` (line `457`), after resolving the tester role and **before** the disjointness lookup (`let &t = targs.first()?;` at line `466`), insert the record. The method becomes:

```rust
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        if !lit.is_positive() {
            return None; // ¬is-D(t) constrains nothing here (handled below)
        }
        let atom = cx.atoms.atom(lit.var());
        let (tsym, targs) = Self::uapp(cx.terms, atom)?;
        let DtRole::Tester { ctor } = cx.terms.dt_role(tsym)? else {
            return None;
        };
        // Slice 40: record the positive tester so `instantiate_constructor`
        // (in `check`) can introduce `t = C(sel(t)…)` on this branch.
        self.asserted_testers.insert(atom);
        let &t = targs.first()?;
        let (csym, capp) = self.ctor_of_class(cx, t)?;
        if csym == ctor {
            return None; // agrees
        }
        let tn = cx.eq.intern(t);
        let cn = cx.eq.intern(capp);
        let mut leaves = vec![EqLeaf::Asserted(lit)];
        cx.eq.explain(tn, cn, &mut leaves);
        Some(leaves)
    }
```

- [ ] **Step 4: Implement `instantiate_constructor`**

Add after `exhaustiveness_split`:

```rust
    /// Constructor instantiation (slice 40): for a tester `is-C(t)` asserted
    /// true whose class holds no constructor application, offer the guarded
    /// definitional lemma  `is-C(t) ⇒ t = C(sel1(t), …, seln(t))`. The guard
    /// `¬is-C(t)` keeps the pinned clause a permanent tautology (sound at
    /// level 0); EUF installs the equality on exactly the branches where
    /// `is-C(t)` holds and retracts it on backtrack. The minted field selectors
    /// are watched, so `collapse_lemma` fires on the new constructor app and any
    /// datatype-sorted field recurses through its own exhaustiveness split —
    /// the lazy descent that terminates recursive types. Gating on ASSERTED
    /// testers (not all watched testers) is the laziness lever: only the
    /// branch's chosen constructor is ever instantiated.
    fn instantiate_constructor(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        let asserted: Vec<TermId> = self.asserted_testers.iter().copied().collect();
        for tst in asserted {
            let Some((tsym, targs)) = Self::uapp(cx.terms, tst) else {
                continue;
            };
            let Some(DtRole::Tester { ctor }) = cx.terms.dt_role(tsym) else {
                continue;
            };
            let Some(&t) = targs.first() else {
                continue;
            };
            if self.ctor_of_class(cx, t).is_some() {
                continue; // class already has a constructor app
            }
            let Some(sels) = cx.terms.dt_selectors(ctor).map(<[SymbolId]>::to_vec) else {
                continue;
            };
            // Mint the field selectors on `t` and the constructor app.
            let mut fields = Vec::with_capacity(sels.len());
            for sel in &sels {
                let app = cx
                    .terms
                    .mk_app(Op::Uninterpreted(*sel), &[t])
                    .expect("selector applies to its own datatype sort");
                self.sel_apps.insert(app);
                if cx.terms.is_datatype_sort(cx.terms.sort_of(app)) {
                    self.dt_terms.insert(app);
                }
                fields.push(app);
            }
            let capp = cx
                .terms
                .mk_app(Op::Uninterpreted(ctor), &fields)
                .expect("constructor applies to its own field sorts");
            self.ctor_apps.insert(capp);
            if cx.terms.is_datatype_sort(cx.terms.sort_of(capp)) {
                self.dt_terms.insert(capp);
            }
            let lemma = cx
                .terms
                .mk_eq(t, capp)
                .expect("t and C(sel(t)…) share the datatype sort");
            // Guard by ¬is-C(t). An asserted tester always has a SAT var; the
            // `?` is defensive and simply defers to a later check if not.
            let var = cx.atoms.var_of_atom(tst)?;
            if !self.emitted.insert(lemma) {
                continue; // already offered on this branch
            }
            return Some(TCheck::Split {
                atoms: vec![lemma],
                guard: Some(Lit::new(var, true).negate()),
                phases: Vec::new(),
            });
        }
        None
    }
```

- [ ] **Step 5: Wire `instantiate_constructor` into `check` before the exhaustiveness split**

In `check`, place instantiation immediately before the `exhaustiveness_split` call added in Task 1, so a just-asserted tester determines its class before Rule 1 would re-split it:

```rust
        if let Some(split) = self.instantiate_constructor(cx) {
            return split;
        }
        if let Some(split) = self.exhaustiveness_split(cx) {
            return split;
        }
```

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo nextest run -p shinri-dt asserted_tester_instantiates_guarded_constructor`
Expected: PASS

- [ ] **Step 7: Run the full DT unit suite**

Run: `cargo nextest run -p shinri-dt`
Expected: PASS

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-dt/src/lib.rs
git commit -m "feat(dt): slice40 T2 — guarded constructor instantiation (Rule 2) + assert recording"
```

---

### Task 3: Model-tied residual fence (occurs-check) + visited-set model

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs` (`render_value` `374-415`; `model` `526-536`; `check` fence `516-519`; add two helpers; add `use shinri_theory::ENodeId;` at line `9`)
- Test: `crates/shinri-dt/src/lib.rs` (`mod tests`)

**Interfaces:**
- Consumes: `EqualityEngine::{intern, find}`, `ctor_of_class`, `ctor_apps`, `Context::{is_datatype_sort, sort_of, symbol_name}`, `Self::uapp`.
- Produces: `fn constructor_graph_has_cycle(&self, cx: &mut TheoryCtx) -> bool`; `fn ctor_child_class_reps(&self, cx: &mut TheoryCtx, rep: ENodeId) -> Option<Vec<ENodeId>>`; `render_value` re-signed to `(&self, cx, t, visited: &mut FxHashSet<ENodeId>) -> Option<String>`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn cyclic_constructor_graph_fences_to_unknown() {
    // x ≡ cons(h, x): x's class holds a constructor app whose `tail` field is x
    // itself. Determined, so slice-39 rules are satisfied — but the only ground
    // model is infinite. The occurs-check fence must return Unknown, NOT Sat.
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
    let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

    // Drain any collapse tautologies to a fixpoint, then the fence must fire.
    let mut verdict = dt.check(&mut cx, Effort::Full);
    for _ in 0..8 {
        match verdict {
            TCheck::Split { atoms: l, .. } => {
                if let TermNode::App { args, .. } = cx.terms.term_node(l[0]) {
                    let kids = cx.terms.children(*args).to_vec();
                    let (a, b) = (cx.eq.intern(kids[0]), cx.eq.intern(kids[1]));
                    let _ = cx.eq.merge(a, b, EqJust::Definitional);
                }
                verdict = dt.check(&mut cx, Effort::Full);
            }
            _ => break,
        }
    }
    assert!(
        matches!(verdict, TCheck::Unknown),
        "cyclic (infinite-only) model must fence to Unknown, got {}",
        tcheck_name(&verdict)
    );
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo nextest run -p shinri-dt cyclic_constructor_graph_fences_to_unknown`
Expected: FAIL — with the class determined and no cycle check, `check` returns `Sat` (the wrong-`sat` this task prevents).

- [ ] **Step 3: Add the `ENodeId` import and the occurs-check helpers**

At line `9`, extend the `shinri_theory` import to bring in `ENodeId`:

```rust
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};
use shinri_theory::ENodeId;
```

(If `ENodeId` is re-exported elsewhere, adjust the path; confirm with `grep -n "pub use\|pub type ENodeId\|pub struct ENodeId" crates/shinri-theory/src/*.rs`.)

Add both helpers after `ctor_of_class` (line `334`):

```rust
    /// The datatype-sorted argument class reps of the constructor application in
    /// `rep`'s class, or `None` if the class holds no constructor app. Used by
    /// the occurs-check to walk the constructor graph one level down.
    fn ctor_child_class_reps(&self, cx: &mut TheoryCtx, rep: ENodeId) -> Option<Vec<ENodeId>> {
        for &capp in &self.ctor_apps {
            if cx.eq.find(cx.eq.intern(capp)) != rep {
                continue;
            }
            let (_, cargs) = Self::uapp(cx.terms, capp)?;
            let kids = cargs
                .iter()
                .filter(|&&a| cx.terms.is_datatype_sort(cx.terms.sort_of(a)))
                .map(|&a| cx.eq.find(cx.eq.intern(a)))
                .collect();
            return Some(kids);
        }
        None
    }

    /// True iff the constructor graph over the currently determined classes has
    /// a cycle — a class reachable from itself by following constructor
    /// arguments. A cycle means the only ground model is an infinite term, so no
    /// finite model exists on this branch: slice 40 answers `Unknown` here (the
    /// residual fence), and slice 41 will turn the same detection into an
    /// `unsat` conflict. Iterative (explicit DFS stack), never recursive: the
    /// term graph comes from untrusted input and may be arbitrarily deep
    /// (threat model), matching `dt_first_ill_founded`.
    fn constructor_graph_has_cycle(&self, cx: &mut TheoryCtx) -> bool {
        let mut on_path: FxHashSet<ENodeId> = FxHashSet::default(); // grey: DFS stack
        let mut done: FxHashSet<ENodeId> = FxHashSet::default(); // black: fully explored
        for t in self.watched_dt_terms() {
            let root = cx.eq.find(cx.eq.intern(t));
            if done.contains(&root) {
                continue;
            }
            let Some(children) = self.ctor_child_class_reps(cx, root) else {
                done.insert(root);
                continue;
            };
            on_path.insert(root);
            let mut stack: Vec<(ENodeId, Vec<ENodeId>)> = vec![(root, children)];
            while let Some((node, mut kids)) = stack.pop() {
                if let Some(child) = kids.pop() {
                    stack.push((node, kids)); // more siblings to visit after
                    if on_path.contains(&child) {
                        return true; // back-edge → cycle
                    }
                    if done.contains(&child) {
                        continue;
                    }
                    match self.ctor_child_class_reps(cx, child) {
                        Some(gk) => {
                            on_path.insert(child);
                            stack.push((child, gk));
                        }
                        None => {
                            done.insert(child);
                        }
                    }
                } else {
                    on_path.remove(&node);
                    done.insert(node);
                }
            }
        }
        false
    }
```

- [ ] **Step 4: Extend the `check` fence with the occurs-check**

Replace the fence at lines `516-519` (`if self.has_undetermined_class(cx) { return TCheck::Unknown; } TCheck::Sat`) with:

```rust
        // Model-tied residual fence (spec §4). Slice 40 replaces slice 39's
        // coarse "any undetermined class → Unknown" with a finer one: an
        // undetermined class that survived splitting stays Unknown (defensive —
        // SAT satisfies every emitted disjunction before a Full check), and a
        // cyclic constructor graph is Unknown because its only model is
        // infinite. Slice 41 turns the cycle into a proven `unsat`.
        if self.has_undetermined_class(cx) || self.constructor_graph_has_cycle(cx) {
            return TCheck::Unknown;
        }
        TCheck::Sat
```

- [ ] **Step 5: Rewrite `render_value` to use a visited set**

Replace `render_value` (lines `374-415`) with:

```rust
    /// Render the ground constructor term for `t`'s class as an SMT-LIB string
    /// (e.g. `nil`, `(cons 1 nil)`), or `None` when the class is not
    /// constructor-determined or a cycle is hit. `visited` holds the class reps
    /// on the current path: a repeat is a cycle (no finite ground term), while a
    /// rep is removed on the way back up so a DAG-shared subterm still renders
    /// under sibling branches. Unreachable with a cycle once `check` has
    /// returned `Sat` — the fence rejects cyclic states first — but the guard is
    /// kept as fail-safe defense in depth.
    fn render_value(
        &self,
        cx: &mut TheoryCtx,
        t: TermId,
        visited: &mut FxHashSet<ENodeId>,
    ) -> Option<String> {
        let rep = cx.eq.find(cx.eq.intern(t));
        if !visited.insert(rep) {
            return None; // cycle
        }
        let rendered = self.render_value_inner(cx, t, visited);
        visited.remove(&rep);
        rendered
    }

    fn render_value_inner(
        &self,
        cx: &mut TheoryCtx,
        t: TermId,
        visited: &mut FxHashSet<ENodeId>,
    ) -> Option<String> {
        let (csym, capp) = self.ctor_of_class(cx, t)?;
        let (_, cargs) = Self::uapp(cx.terms, capp)?;
        let name = cx.terms.symbol_name(csym).to_string();
        if cargs.is_empty() {
            return Some(name);
        }
        let parts: Option<Vec<String>> = cargs
            .iter()
            .map(|&a| {
                if cx.terms.is_datatype_sort(cx.terms.sort_of(a)) {
                    self.render_value(cx, a, visited)
                } else {
                    match Self::uapp(cx.terms, a) {
                        Some((s, kids)) if kids.is_empty() => {
                            Some(cx.terms.symbol_name(s).to_string())
                        }
                        _ => Some("?".to_string()),
                    }
                }
            })
            .collect();
        Some(format!("({} {})", name, parts?.join(" ")))
    }
```

- [ ] **Step 6: Update `model` to pass a fresh visited set**

In `model` (line `531`), replace the `render_value(cx, t, 0)` call:

```rust
            let mut visited = FxHashSet::default();
            let Some(v) = self.render_value(cx, t, &mut visited) else {
                continue;
            };
```

- [ ] **Step 7: Run tests to verify they pass**

Run: `cargo nextest run -p shinri-dt`
Expected: PASS — the new `cyclic_constructor_graph_fences_to_unknown` plus the existing `determined_datatype_class_is_sat` (a `nil`-determined class has no datatype-sorted fields → no cycle → still `Sat`) and `model_assigns_ground_constructor_term` (renders `nil`).

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-dt/src/lib.rs
git commit -m "feat(dt): slice40 T3 — occurs-check residual fence + visited-set model rendering"
```

---

### Task 4: End-to-end `.smt2` decisions in `shinri-solver`

**Files:**
- Modify: `crates/shinri-solver/tests/qfdt_e2e.rs`
- Test: same file

**Interfaces:**
- Consumes: the existing `qfdt_e2e.rs` harness that runs an SMT-LIB script and asserts the `(check-sat)` outcome. **Read the file first** to reuse its exact helper (e.g. `solve_script(src) -> outcome` and the outcome enum names) — do not invent a new harness.

- [ ] **Step 1: Read the existing harness**

Run: `sed -n '1,60p' crates/shinri-solver/tests/qfdt_e2e.rs`
Note the helper name, the script-string convention, and how `sat`/`unsat`/`unknown` are asserted. Use those verbatim below (the code blocks assume a helper `expect_unsat(src)`, `expect_sat(src)`, `expect_unknown(src)` — rename to match what the file actually provides).

- [ ] **Step 2: Write the failing tests**

Append (adapting helper names to the file's conventions):

```rust
// Exhaustiveness makes this unsat: x is a List, so it must be nil or cons, but
// both testers are negated. Slice 39 answered `unknown`; slice 40 decides unsat.
#[test]
fn negated_all_testers_is_unsat() {
    expect_unsat(
        "(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
         (declare-const x List)
         (assert (not ((_ is nil) x)))
         (assert (not ((_ is cons) x)))
         (check-sat)",
    );
}

// Sat requires instantiating cons to satisfy head(x) = 5.
#[test]
fn instantiation_yields_sat_model() {
    expect_sat(
        "(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
         (declare-const x List)
         (assert ((_ is cons) x))
         (assert (= (head x) 5))
         (check-sat)",
    );
}

// Mutually recursive datatypes: a Tree is a leaf or a node holding a Forest.
#[test]
fn mutually_recursive_group_is_sat() {
    expect_sat(
        "(declare-datatypes ((Tree 0) (Forest 0))
           (((leaf (val Int)) (node (kids Forest)))
            ((fnil) (fcons (fhd Tree) (ftl Forest)))))
         (declare-const t Tree)
         (assert ((_ is node) t))
         (check-sat)",
    );
}

// Cyclic constraint: no finite model. Slice 40's residual fence answers
// `unknown`; slice 41's acyclicity will flip this to `unsat`.
#[test]
fn cyclic_equation_is_unknown_until_slice41() {
    expect_unknown(
        "(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
         (declare-const x List)
         (declare-const h Int)
         (assert (= x (cons h x)))
         (check-sat)",
    );
}
```

- [ ] **Step 3: Run to verify they fail**

Run: `cargo nextest run -p shinri-solver -E 'test(negated_all_testers_is_unsat) or test(instantiation_yields_sat_model) or test(mutually_recursive_group_is_sat) or test(cyclic_equation_is_unknown_until_slice41)'`
Expected: the three decided cases FAIL as `unknown` on the pre-slice-40 solver (fence not lifted); `cyclic_equation_is_unknown_until_slice41` may already pass as `unknown`.

- [ ] **Step 4: Confirm they pass on the slice-40 solver**

The engine work is already done (Tasks 1–3). Run the same command:

Run: `cargo nextest run -p shinri-solver -E 'test(negated_all_testers_is_unsat) or test(instantiation_yields_sat_model) or test(mutually_recursive_group_is_sat) or test(cyclic_equation_is_unknown_until_slice41)'`
Expected: PASS (all four).

- [ ] **Step 5: Run the whole DT e2e file + the completeness gate**

Run: `cargo nextest run -p shinri-solver -E 'test(qfdt_e2e)'`
Then: `cargo nextest run -p shinri-solver -E 'test(script_e2e)'`
Expected: PASS — `script_e2e` confirms no previously-pinned outcome regressed (any `unknown → sat/unsat` flip here is an intended, adjudicated completeness gain, not a regression).

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfdt_e2e.rs
git commit -m "test(dt): slice40 T4 — e2e exhaustiveness unsat, instantiation sat, mutual recursion, cyclic unknown"
```

---

### Task 5: Oracle differential vs z3 + cvc5, and fuzz seeds

**Files:**
- Modify: `crates/shinri-solver/tests/qfdt_oracle.rs`
- Modify: the datatype fuzz-corpus seed location (find it in Step 1)

**Interfaces:**
- Consumes: the existing `qfdt_oracle.rs` differential harness (feature `oracle`, z3 + cvc5 from mise). **Read it first** for the exact assertion helper and how it treats a shinri `unknown` (the oracle harness must accept shinri `unknown` where z3/cvc5 say `sat`/`unsat` — `unknown` is a sound under-approximation, never a mismatch).

- [ ] **Step 1: Read the oracle harness and locate the fuzz seeds**

Run: `sed -n '1,50p' crates/shinri-solver/tests/qfdt_oracle.rs`
Run: `grep -rn "declare-datatype" crates/shinri-solver/fuzz crates/*/fuzz 2>/dev/null; ls crates/shinri-solver/tests/ | grep -i fuzz`
Note the `#![cfg(feature = "oracle")]` gate and the corpus-seed directory used by the DT fuzz target.

- [ ] **Step 2: Write the differential cases**

Append to `qfdt_oracle.rs`, matching the file's helper name (assumed `differential(src)` below):

```rust
// Case-split-driven queries where slice 40 now returns a definite verdict.
// The harness accepts shinri `unknown` as a non-mismatch, but these should
// agree definitely with both oracles.
#[test]
fn oracle_exhaustiveness_and_instantiation() {
    differential(
        "(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
         (declare-const x List)
         (assert (not ((_ is nil) x))) (assert (not ((_ is cons) x)))
         (check-sat)",
    );
    differential(
        "(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Bool)))))
         (declare-const p Pair)
         (assert (= (fst p) 7)) (assert (snd p))
         (check-sat)",
    );
    differential(
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))
         (declare-const c Color)
         (assert (not ((_ is red) c))) (assert (not ((_ is green) c)))
         (check-sat)",
    );
}
```

- [ ] **Step 3: Add datatype fuzz-corpus seeds**

Add small `.smt2` seed files (exercising nested `cons`, a tester disjunction, a mutually-recursive group, and a cyclic equality) to the DT fuzz corpus directory found in Step 1. If seeds are inline strings in a corpus module instead of files, append them there.

- [ ] **Step 4: Run the oracle suite WITH the feature flag**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfdt_oracle)'`
Expected: PASS. **A run without `--features oracle` compiles to zero tests and proves nothing — do not report it as green.** Confirm the discovered test count is non-zero in the nextest summary.

- [ ] **Step 5: Smoke the DT fuzz target**

Run: `ASAN_OPTIONS=detect_leaks=0 FUZZ_SECONDS=30 mise run fuzz-smoke` (or the single-target invocation the repo uses for the DT target)
Expected: no crash/panic on the new seeds. (Local cargo-fuzz needs `detect_leaks=0`; nightly CI is authoritative.)

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfdt_oracle.rs
git add <fuzz-corpus-seed-paths>
git commit -m "test(dt): slice40 T5 — QF_DT oracle differential vs z3/cvc5 + fuzz seeds"
```

---

### Task 6: Doc-comment corrections, hygiene, and full gate

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs` (comment corrections only)

**Interfaces:** none — this task changes comments and runs the gates.

- [ ] **Step 1: Correct the stale slice-39 fence narrative**

The module-level and `check` comments still describe the fence as "any undetermined class → Unknown … slice 40" as *future* work. Update the `check` fence comment block (formerly lines `507-515`) and the `has_undetermined_class` doc (`348-352`) to state that slice 40 now (a) actively splits undetermined classes on exhaustiveness and (b) fences to `Unknown` only on a surviving-undetermined class or a cyclic constructor graph, with slice 41 owning the cycle→`unsat` upgrade. Ensure no comment claims `x = cons(h, x)` is decidable here.

- [ ] **Step 2: Verify the crate builds and lints clean**

Run: `cargo clippy -p shinri-dt --all-targets -- -D warnings`
Expected: no warnings. (In particular the `map(<[SymbolId]>::to_vec)` / `is_none_or` idioms must satisfy clippy; if `is_none_or` is unavailable on the pinned toolchain, use `.map_or(true, <[SymbolId]>::is_empty)` and re-run.)

- [ ] **Step 3: Format**

Run: `cargo fmt --all`
Expected: clean (CI gates on `fmt --check`).

- [ ] **Step 4: Full workspace lint + fast test tier**

Run: `cargo clippy --workspace --all-targets -- -D warnings`
Run: `mise run test`
Expected: PASS — the whole fast suite, no regressions.

- [ ] **Step 5: Oracle + completeness gate before push**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfdt_oracle)'`
Run: `cargo nextest run -p shinri-solver -E 'test(script_e2e)'`
Expected: PASS (non-zero oracle test count; `script_e2e` clean).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-dt/src/lib.rs
git commit -m "docs(dt): slice40 T6 — correct fence narrative to case-split + occurs-check reality"
```

- [ ] **Step 7: Full CI parity**

Run: `mise run ci`
Expected: lint + deny + secrets + fast test suite all green — the blocking PR tier.

---

## Self-Review

**Spec coverage (spec §-by-§):**
- §1 summary / §3.1 exhaustiveness split → Task 1.
- §3.2 guarded instantiation + laziness → Task 2.
- §4 model-tied fence, occurs-check, termination → Task 3.
- §5.C visited-set model → Task 3 (Steps 5–6).
- §5.D nullary-first phase preference → Task 1 (Step 4, `phases`).
- §5.E wiring (no new Combiner slot; testers flow via existing registration) → no code needed; exercised by Task 4 e2e.
- §6 testing (unit / e2e / oracle+flag / fuzz / gates) → Tasks 1–3 (unit), 4 (e2e), 5 (oracle+fuzz), 6 (fmt/lint/script_e2e/ci).
- §7 scope-out (acyclicity `unsat`, finiteness, N-O arith) → explicitly deferred; the cyclic e2e (Task 4) and comments (Task 6) pin the boundary.
- §8 success criteria → Tasks 4 (decisions), 5 (no `sat`/`unsat` oracle mismatch), 3 (no wrong-`sat`), 6 (`mise run ci`).

**Placeholder scan:** none — every code step carries complete code. Helper names in Tasks 4–5 (`expect_unsat`/`differential`/corpus path) are explicitly gated behind a "read the file first" step because they must match the existing harness verbatim; the plan states the assumed name and the rename rule rather than inventing an API.

**Type consistency:** `exhaustiveness_split`/`instantiate_constructor` return `Option<TCheck>` (matching `collapse_lemma`/`tester_lemma`); `constructor_graph_has_cycle -> bool`; `ctor_child_class_reps -> Option<Vec<ENodeId>>`; `render_value` re-signed to take `&mut FxHashSet<ENodeId>` and its sole caller `model` is updated in the same task. New fields `split_done`/`asserted_testers` are `FxHashSet<TermId>`, introduced in Task 1 and both consumed by Task 2. `push`/`pop` remain no-ops (justified: `asserted_testers` monotonicity is sound because instantiation lemmas are guarded).
