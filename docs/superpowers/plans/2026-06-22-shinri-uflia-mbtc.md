# QF_UFLIA via Model-Based Theory Combination — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Activate `Combiner<Euf, Arith>` for pure-Int QF_UFLIA, sound and complete, by deciding each undecided shared-Int arrangement with an integer trichotomy split via the existing splitting-on-demand machinery (MBTC).

**Architecture:** The Nelson–Oppen framework already works for QF_UFLRA. This adds: (1) an arith seam `model_equal_shared_pairs` reporting shared Int vars equal under the current model, plus Int integrality on shared vars; (2) a combiner MBTC step that, at the N-O Sat fixpoint, emits `(= u v) ∨ (< u v) ∨ (> u v)` for the first model-equal-unmerged Int pair — the `=` branch merges in EUF (congruence, exchanged to arith), the `<`/`>` branches separate them in arith; (3) a `bind_fresh` generalization so the fresh `=` atom routes to EUF and `<`/`>` to arith; (4) generalization of EUF term-sharing from Real-only to Real ∪ Int, which flips QF_UFLIA on. The MBTC step + `bind_fresh` + arith seam land **before** Int sharing, so every intermediate commit is sound.

**Tech Stack:** Rust (`shinri-arith`, `shinri-theory`, `shinri-euf`, `shinri-solver`, `shinri-sat`); exact rationals via `shinri-num`; `easy_smt` + `z3` for the differential oracle.

## Global Constraints

- **Soundness is total.** Never return SAT/UNSAT unless justified; `unknown` only for genuinely unsupported constructs (nonlinear, mixed-sort, QF_LIRA). (spec §2.1)
- **Exact arithmetic only.** No floats in any theory core.
- **No `dyn` on the hot path.** `Combiner<Euf, Arith>` stays a concrete monomorphized struct.
- **Backtracking via `UndoLog`, never snapshots**, synchronized to SAT decision levels.
- **Split Int pairs only.** Real model-equal pairs are never split — convex N-O is already verdict-sound for QF_UFLRA, so splitting them would be wasteful and would regress QF_UFLRA.
- **Commit ordering preserves soundness:** Tasks 1–3 are inert (the shared set has no Int terms yet, and `bind_fresh` stays behavior-preserving for existing arith splits); Task 4 flips Int sharing on, by which point the MBTC machinery is already in place.
- Spec: `docs/superpowers/specs/2026-06-22-shinri-uflia-design.md` (§3 mechanism, §4 components, §6 soundness/termination, §8 DoD, §9 build order).

---

### Task 1: Arith seam — Int integrality on shared vars + `model_equal_shared_pairs`

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (`ensure_shared_var` at `lib.rs:413`; add `model_equal_shared_pairs` inherent method after `entailed_equalities` at `lib.rs:538`; add trait override in `impl TheorySolver for Arith` after `consume_interface_equality` at `lib.rs:1042`)
- Modify: `crates/shinri-theory/src/solver_trait.rs` (add a defaulted trait method after `register_arith_uf_terms` at `solver_trait.rs:105`)
- Test: `crates/shinri-arith/src/lib.rs` (the existing `#[cfg(test)] mod model_tests` at `lib.rs:1071`)

**Interfaces:**
- Consumes: `VarStore::problem_var_sorted(t, is_int)` (`vars.rs:46`), `VarStore::is_int(v)` (`vars.rs:80`), `self.value: Vec<DeltaRational>`, `Context::sort_of`, `Context::int_sort`.
- Produces:
  - `Arith::ensure_shared_var(&mut self, ctx: &Context, t: TermId)` — now stamps Int-sortedness.
  - `Arith::model_equal_shared_pairs(&mut self, shared: &[TermId]) -> Vec<(TermId, TermId)>` (inherent) + the `TheorySolver` trait method `fn model_equal_shared_pairs(&mut self, cx: &mut TheoryCtx, shared: &[TermId]) -> Vec<(TermId, TermId)>` (default `Vec::new()`).

- [ ] **Step 1: Add the defaulted trait method**

In `crates/shinri-theory/src/solver_trait.rs`, immediately after the `register_arith_uf_terms` default (ends at `solver_trait.rs:105`, before the trait's closing `}`), add:

```rust
    /// The shared INT-sorted pairs equal under this theory's current model `β`
    /// (whether or not entailed). The combiner resolves any such pair not merged
    /// in the shared engine with an integer trichotomy split (MBTC). State-safe
    /// (read-only). Real pairs are excluded — convex exchange handles them, so
    /// they need no split. Arith implements; EUF / stubs default to none.
    fn model_equal_shared_pairs(
        &mut self,
        _cx: &mut TheoryCtx,
        _shared: &[TermId],
    ) -> Vec<(TermId, TermId)> {
        Vec::new()
    }
```

- [ ] **Step 2: Make shared vars carry Int integrality**

In `crates/shinri-arith/src/lib.rs`, change the first line of `ensure_shared_var` (`lib.rs:414`) from:

```rust
        let v = self.vars.problem_var(t);
```

to:

```rust
        // Stamp Int-sortedness so shared Int terms (f-apps, numerals, vars) are
        // integral in the simplex / integer layer — required for QF_UFLIA.
        let is_int = ctx.sort_of(t) == ctx.int_sort();
        let v = self.vars.problem_var_sorted(t, is_int);
```

- [ ] **Step 3: Add the `model_equal_shared_pairs` inherent method**

In `crates/shinri-arith/src/lib.rs`, directly after `entailed_equalities` (after `lib.rs:538`), add:

```rust
    /// Shared INT-sorted pairs equal under the current model `β` (MBTC candidate
    /// pairs). Read-only / state-safe. Int-only via `is_int`, reliable because
    /// `ensure_shared_var` stamps Int-sortedness. Excludes Real pairs (convex
    /// exchange handles those; splitting them would regress QF_UFLRA).
    pub fn model_equal_shared_pairs(&mut self, shared: &[TermId]) -> Vec<(TermId, TermId)> {
        let mut items: Vec<(TermId, ArithVar)> = Vec::new();
        for &t in shared {
            let v = self.vars.problem_var(t);
            if self.vars.is_int(v) && !items.iter().any(|(_, w)| *w == v) {
                items.push((t, v));
            }
        }
        let mut out = Vec::new();
        for i in 0..items.len() {
            for j in (i + 1)..items.len() {
                if self.value[items[i].1.index()] == self.value[items[j].1.index()] {
                    out.push((items[i].0, items[j].0));
                }
            }
        }
        out
    }
```

- [ ] **Step 4: Add the trait override**

In `crates/shinri-arith/src/lib.rs`, in `impl TheorySolver for Arith`, directly after the `consume_interface_equality` override (after `lib.rs:1042`), add:

```rust
    fn model_equal_shared_pairs(
        &mut self,
        _cx: &mut TheoryCtx,
        shared: &[TermId],
    ) -> Vec<(TermId, TermId)> {
        Arith::model_equal_shared_pairs(self, shared)
    }
```

- [ ] **Step 5: Write the test**

In `crates/shinri-arith/src/lib.rs`, inside `mod model_tests` (after the imports at `lib.rs:1077`), add (and add any missing imports — the test needs `shinri_core::{Lit, Var}`, `shinri_sat::Effort`, `shinri_theory::TCheck`, plus the already-present `BuiltinOp, Context, Op, Rational, AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver`):

```rust
    #[test]
    fn model_equal_shared_pairs_reports_beta_equal_int_pair() {
        // Two Int consts both pinned to 5: β(x)=β(y)=5 ⇒ reported as a pair.
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xs = ctx.declare_fun("x", &[], int);
        let ys = ctx.declare_fun("y", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(ys), &[]).unwrap();
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), int);
        let mk = |ctx: &mut Context, op, a, b| ctx.mk_app(Op::Builtin(op), &[a, b]).unwrap();
        let atom_terms = [
            mk(&mut ctx, BuiltinOp::Ge, x, five),
            mk(&mut ctx, BuiltinOp::Le, x, five),
            mk(&mut ctx, BuiltinOp::Ge, y, five),
            mk(&mut ctx, BuiltinOp::Le, y, five),
        ];
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        for (i, &atom) in atom_terms.iter().enumerate() {
            let v = Var::new(i as u32);
            let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
            <Arith as TheorySolver>::new_var(&mut arith, &mut cx, v, atom);
        }
        for i in 0..atom_terms.len() {
            let v = Var::new(i as u32);
            let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
            assert!(
                <Arith as TheorySolver>::assert(&mut arith, &mut cx, Lit::new(v, true)).is_none(),
                "asserting [5,5] bounds must not conflict"
            );
        }
        {
            let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
            arith.ensure_shared_var(cx.terms, x);
            arith.ensure_shared_var(cx.terms, y);
            assert!(matches!(
                <Arith as TheorySolver>::check(&mut arith, &mut cx, Effort::Full),
                TCheck::Sat
            ));
        }
        assert_eq!(arith.model_equal_shared_pairs(&[x, y]), vec![(x, y)]);
    }
```

- [ ] **Step 6: Run**

Run: `cargo test -p shinri-arith model_equal_shared_pairs_reports_beta_equal_int_pair && cargo test -p shinri-arith`
Expected: the new test PASSES and all existing arith tests still PASS (`problem_var_sorted(t, false)` ≡ `problem_var(t)`, so Real is unaffected).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-arith/src/lib.rs crates/shinri-theory/src/solver_trait.rs
git commit -m "feat(arith): Int integrality on shared vars + model_equal_shared_pairs seam (QF_UFLIA)"
```

---

### Task 2: Generalize `Combiner::bind_fresh` to classify-and-route

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs` (`bind_fresh` at `combiner.rs:196`)
- Test: `crates/shinri-theory/src/combiner.rs` (`#[cfg(test)] mod tests` at `combiner.rs:519`)

**Interfaces:**
- Consumes: `classify` (already imported, `combiner.rs:5`), `Owner`, the theory `new_var` / `register_arith_uf_terms` hooks.
- Produces: `bind_fresh` routes a fresh `(= u v)` atom to `Owner::Euf` and `(< u v)`/`(> u v)` (and existing QF_LIA `(x≤k)`/`(x≥k)`) to `Owner::Arith`.

- [ ] **Step 1: Replace `bind_fresh`**

In `crates/shinri-theory/src/combiner.rs`, replace `bind_fresh` (`combiner.rs:196-205`):

```rust
    fn bind_fresh(&mut self, v: Var, atom: TermId) {
        self.atoms.register(v, atom, Owner::Arith);
        // Borrow-split: build the ctx from the non-arith fields, then call arith.
        let mut cx = TheoryCtx {
            terms: &mut self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        self.arith.new_var(&mut cx, v, atom);
    }
```

with:

```rust
    fn bind_fresh(&mut self, v: Var, atom: TermId) {
        // A fresh split atom: QF_LIA branch/cut atoms (Le/Ge) → Arith; QF_UFLIA
        // MBTC's interface `(= u v)` → Euf, `(< u v)`/`(> u v)` → Arith. Classify
        // and route to the owning theory, mirroring `register_atom`. A fresh atom
        // is always supported by construction; fall back to Arith defensively.
        let owner = classify(&self.terms, atom).unwrap_or(Owner::Arith);
        self.atoms.register(v, atom, owner);
        let mut cx = TheoryCtx {
            terms: &mut self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        match owner {
            Owner::Euf => self.euf.new_var(&mut cx, v, atom),
            Owner::Arith => {
                self.arith.new_var(&mut cx, v, atom);
                self.euf.register_arith_uf_terms(&mut cx, atom);
            }
            Owner::Shared => {
                self.euf.new_var(&mut cx, v, atom);
                self.arith.new_var(&mut cx, v, atom);
                self.euf.register_arith_uf_terms(&mut cx, atom);
            }
        }
    }
```

- [ ] **Step 2: Write the test**

In `crates/shinri-theory/src/combiner.rs`, inside `mod tests`, add (the module already imports `Op` at `combiner.rs:525` and brings `Context, Var, Combiner, Theory, TheoryResult` via `use super::*`):

```rust
    #[test]
    fn bind_fresh_routes_eq_to_euf_and_lt_to_arith() {
        use crate::types::Owner;
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let us = ctx.declare_fun("u", &[], int);
        let vs = ctx.declare_fun("v", &[], int);
        let u = ctx.mk_app(Op::Uninterpreted(us), &[]).unwrap();
        let v = ctx.mk_app(Op::Uninterpreted(vs), &[]).unwrap();
        let eq = ctx.mk_eq(u, v).unwrap();
        let lt = ctx
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Lt), &[u, v])
            .unwrap();
        let mut c: Combiner<Spy, Spy> = Combiner::with_context(ctx);
        let ve = Var::new(0);
        let vl = Var::new(1);
        Theory::bind_fresh(&mut c, ve, eq);
        Theory::bind_fresh(&mut c, vl, lt);
        assert_eq!(c.atoms_ref().owner(ve), Owner::Euf);
        assert_eq!(c.atoms_ref().owner(vl), Owner::Arith);
    }
```

- [ ] **Step 3: Run**

Run: `cargo test -p shinri-theory bind_fresh_routes_eq_to_euf_and_lt_to_arith && cargo test -p shinri-theory`
Expected: the new test PASSES; the existing `combiner_lifts_split_and_binds_fresh` test (which binds a fresh arith atom) still PASSES — the QF_LIA path is behavior-preserving (an arith atom classifies to `Owner::Arith` and `register_arith_uf_terms` is a no-op for atoms with no UF subterms).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-theory/src/combiner.rs
git commit -m "feat(theory): bind_fresh classifies+routes fresh split atoms (enables QF_UFLIA MBTC interface atoms)"
```

---

### Task 3: Combiner MBTC step — integer trichotomy split for undecided pairs

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs` (the terminal `if !progressed` block of `drive_final_check` at `combiner.rs:381-383`)
- Test: `crates/shinri-theory/src/combiner.rs` (`mod tests`)

**Interfaces:**
- Consumes: `Arith::model_equal_shared_pairs` (Task 1, via the trait), `EqualityEngine::{intern, are_equal}`, `Context::{mk_eq, mk_app}`, `FinalCheck::Split` (already exists, `combiner.rs:21`).
- Produces: at the N-O Sat fixpoint, `drive_final_check` returns `FinalCheck::Split([eq, lt, gt])` for the first model-equal-unmerged shared Int pair, else `FinalCheck::Sat`.

- [ ] **Step 1: Add the MBTC step**

In `crates/shinri-theory/src/combiner.rs`, replace the terminal block of `drive_final_check` (`combiner.rs:381-383`):

```rust
            if !progressed {
                return FinalCheck::Sat;
            }
```

with:

```rust
            if !progressed {
                // MBTC: decide the first undecided shared-Int arrangement. A pair
                // equal in arith's model but not merged in the shared engine is
                // resolved by an integer trichotomy split. The `=` branch merges
                // in EUF (congruence, exchanged to arith); the `<`/`>` branches
                // separate them in arith. The disjunction is integer-valid, so SAT
                // must pick a branch — and each split permanently decides one pair,
                // so the undecided set strictly shrinks (termination).
                let undecided = if shared.is_empty() {
                    None
                } else {
                    let mut cx = TheoryCtx {
                        terms: &mut self.terms,
                        eq: &mut self.eq,
                        atoms: &self.atoms,
                    };
                    let pairs = self.arith.model_equal_shared_pairs(&mut cx, &shared);
                    pairs.into_iter().find(|&(a, b)| {
                        let an = cx.eq.intern(a);
                        let bn = cx.eq.intern(b);
                        !cx.eq.are_equal(an, bn)
                    })
                };
                if let Some((u, v)) = undecided {
                    let eq = self.terms.mk_eq(u, v).expect("(= u v) well-sorted");
                    let lt = self
                        .terms
                        .mk_app(shinri_core::Op::Builtin(shinri_core::BuiltinOp::Lt), &[u, v])
                        .expect("(< u v) well-sorted");
                    let gt = self
                        .terms
                        .mk_app(shinri_core::Op::Builtin(shinri_core::BuiltinOp::Gt), &[u, v])
                        .expect("(> u v) well-sorted");
                    return FinalCheck::Split(vec![eq, lt, gt]);
                }
                return FinalCheck::Sat;
            }
```

- [ ] **Step 2: Add the stubs + test**

In `crates/shinri-theory/src/combiner.rs`, inside `mod tests`, add two stubs and a test. (`SharedEuf` overrides `shared_real_terms` for now; Task 4 renames it to `shared_arith_terms` alongside the trait rename.)

```rust
    /// EUF stub that declares two shared terms but never merges them.
    #[derive(Default)]
    struct SharedEuf {
        t1: Option<TermId>,
        t2: Option<TermId>,
    }
    impl TheorySolver for SharedEuf {
        const THEORY_ID: u16 = 1;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
        fn shared_real_terms(&self, _cx: &mut TheoryCtx) -> Vec<TermId> {
            vec![self.t1.unwrap(), self.t2.unwrap()]
        }
    }

    /// Arith stub that reports its two terms as model-equal (undecided pair).
    #[derive(Default)]
    struct ModelEqArith {
        t1: Option<TermId>,
        t2: Option<TermId>,
    }
    impl TheorySolver for ModelEqArith {
        const THEORY_ID: u16 = 2;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
        fn model_equal_shared_pairs(
            &mut self,
            _cx: &mut TheoryCtx,
            _shared: &[TermId],
        ) -> Vec<(TermId, TermId)> {
            vec![(self.t1.unwrap(), self.t2.unwrap())]
        }
    }

    #[test]
    fn mbtc_emits_trichotomy_split_for_undecided_int_pair() {
        use crate::atom::classify;
        use crate::types::Owner;
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let us = ctx.declare_fun("u", &[], int);
        let vs = ctx.declare_fun("v", &[], int);
        let u = ctx.mk_app(Op::Uninterpreted(us), &[]).unwrap();
        let v = ctx.mk_app(Op::Uninterpreted(vs), &[]).unwrap();
        let mut c: Combiner<SharedEuf, ModelEqArith> = Combiner::with_context(ctx);
        c.euf.t1 = Some(u);
        c.euf.t2 = Some(v);
        c.arith.t1 = Some(u);
        c.arith.t2 = Some(v);
        match Theory::check(&mut c, Effort::Full) {
            TheoryResult::SplitAtoms(atoms) => {
                assert_eq!(atoms.len(), 3, "integer trichotomy = 3 atoms");
                assert_eq!(classify(&c.terms, atoms[0]), Ok(Owner::Euf)); // (= u v)
                assert_eq!(classify(&c.terms, atoms[1]), Ok(Owner::Arith)); // (< u v)
                assert_eq!(classify(&c.terms, atoms[2]), Ok(Owner::Arith)); // (> u v)
            }
            other => panic!("expected SplitAtoms, got {other:?}"),
        }
    }
```

- [ ] **Step 3: Run**

Run: `cargo test -p shinri-theory mbtc_emits_trichotomy_split_for_undecided_int_pair && cargo test -p shinri-theory`
Expected: the new test PASSES; all existing combiner tests still PASS (the MBTC step only fires when `model_equal_shared_pairs` returns an unmerged pair, which existing stubs never do).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-theory/src/combiner.rs
git commit -m "feat(theory): MBTC integer trichotomy split for undecided shared-Int arrangements (QF_UFLIA)"
```

---

### Task 4: Generalize EUF term-sharing from Real to Real ∪ Int (activation)

> **This is the activation task.** Until now the shared set has had no Int terms, so the MBTC step (Task 3) was inert. This task makes EUF share Int-sorted terms, which simultaneously turns on Int entailed-equality exchange *and* the MBTC split — soundly, because Tasks 1–3 are already in place.

**Files:**
- Modify: `crates/shinri-euf/src/solver.rs` (`walk_real_uf_apps` at `solver.rs:28`; `shared_real_terms` at `solver.rs:224`; the `register_arith_uf_terms` caller at `solver.rs:256`)
- Modify: `crates/shinri-theory/src/solver_trait.rs` (rename the default `shared_real_terms` at `solver_trait.rs:55`)
- Modify: `crates/shinri-theory/src/combiner.rs` (the call site at `combiner.rs:250`, and the `SharedEuf` stub override from Task 3)
- Test: `crates/shinri-euf/src/solver.rs` (`#[cfg(test)] mod tests` at `solver.rs:274`)

**Interfaces:**
- Produces: `TheorySolver::shared_arith_terms` (renamed from `shared_real_terms`) — now returns registered terms of sort **Real or Int**.

- [ ] **Step 1: Rename the trait method**

In `crates/shinri-theory/src/solver_trait.rs`, rename the default method `shared_real_terms` (`solver_trait.rs:55`) to `shared_arith_terms`, updating its doc to "shared arith-sorted (Real or Int) TermIds":

```rust
    /// The set of shared arith-sorted (Real OR Int) TermIds this theory reasons
    /// about. EUF returns its registered Real/Int terms; arith returns none (the
    /// combiner drives the set FROM the EUF side). Used to compute the N-O set S.
    fn shared_arith_terms(&self, _cx: &mut TheoryCtx) -> Vec<TermId> {
        Vec::new()
    }
```

- [ ] **Step 2: Update the combiner call site + the Task-3 stub**

In `crates/shinri-theory/src/combiner.rs`: change `self.euf.shared_real_terms(&mut cx)` (`combiner.rs:250`) to `self.euf.shared_arith_terms(&mut cx)`, and rename the `SharedEuf::shared_real_terms` override (added in Task 3) to `shared_arith_terms`.

- [ ] **Step 3: Generalize the EUF sharing filter and the UF-app walk**

In `crates/shinri-euf/src/solver.rs`:

(a) Rename `shared_real_terms` (`solver.rs:224`) to `shared_arith_terms` and broaden the filter:

```rust
    /// The shared arith-sorted terms EUF reasons about: every registered term of
    /// Real OR Int sort. Handed to arith (interns vars / pins numerals) and used
    /// as the N-O candidate set for entailed-equality exchange and MBTC splits.
    fn shared_arith_terms(&self, cx: &mut TheoryCtx) -> Vec<TermId> {
        let real_s = cx.terms.real_sort();
        let int_s = cx.terms.int_sort();
        self.inner
            .registered_terms()
            .iter()
            .map(|(t, _)| *t)
            .filter(|&t| {
                let s = cx.terms.sort_of(t);
                s == real_s || s == int_s
            })
            .collect()
    }
```

(b) Rename `walk_real_uf_apps` (`solver.rs:28`) to `walk_arith_uf_apps`, update its two recursive call sites (`solver.rs:45-46`) and the caller in `register_arith_uf_terms` (`solver.rs:256`), and broaden the sort gate. Insert after `solver.rs:30`:

```rust
        let int_s = cx.terms.int_sort();
```

and change the gate at `solver.rs:38` from:

```rust
        if matches!(op, Op::Uninterpreted(_)) && !kids.is_empty() && cx.terms.sort_of(t) == real_s {
```

to:

```rust
        let sort = cx.terms.sort_of(t);
        if matches!(op, Op::Uninterpreted(_)) && !kids.is_empty() && (sort == real_s || sort == int_s) {
```

Update both methods' doc comments, replacing "Real-sorted" with "arith-sorted (Real or Int)".

- [ ] **Step 4: Write the test**

In `crates/shinri-euf/src/solver.rs`, inside `mod tests` (after `solver.rs:282`), add:

```rust
    #[test]
    fn shared_arith_terms_includes_int_uf_apps() {
        use shinri_core::{BuiltinOp, Context, Op};
        use shinri_theory::{AtomRegistry, EqualityEngine};

        // f : Int -> Int ; register arith atom `(>= (f x) 0)` so EUF interns the
        // Int-sorted f-app via register_arith_uf_terms (CRITICAL-2 path).
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xs = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let f = ctx.declare_fun("f", &[int], int);
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let zero = ctx.mk_numeral(shinri_num::Rational::zero(), int);
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[fx, zero]).unwrap();

        let mut euf = Euf::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        euf.register_arith_uf_terms(&mut cx, atom);

        let shared = euf.shared_arith_terms(&mut cx);
        assert!(shared.contains(&fx), "Int-sorted f-app must join the shared set");
    }
```

- [ ] **Step 5: Run**

Run: `cargo test -p shinri-euf shared_arith_terms_includes_int_uf_apps`
Expected: PASS. Then the inert-path regression:

Run: `cargo test -p shinri-euf && cargo test -p shinri-theory && cargo test -p shinri-solver --test qfuf_e2e --test uflra_e2e --test qflra_e2e --test lia_e2e`
Expected: all PASS (QF_UF over sort `U` is untouched; QF_LIA has no EUF-registered terms so the shared set stays empty; QF_UFLRA exchange is unchanged).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-euf/src/solver.rs crates/shinri-theory/src/solver_trait.rs crates/shinri-theory/src/combiner.rs
git commit -m "feat(euf): share Int-sorted terms (shared_real_terms->shared_arith_terms) — activates QF_UFLIA MBTC"
```

---

### Task 5: QF_UFLIA end-to-end witnesses (definite verdicts)

**Files:**
- Create: `crates/shinri-solver/tests/uflia_e2e.rs`

**Interfaces:**
- Consumes: the full activated stack. Public `Solver` API: `Solver::new`, `declare_const`, `numeral`, `declare_fun`, `app`, `eq`, `assert`, `check_sat() -> SolveOutcome`, `int_sort`.

- [ ] **Step 1: Write the witnesses**

Create `crates/shinri-solver/tests/uflia_e2e.rs`:

```rust
//! End-to-end QF_UFLIA (EUF + linear integer arithmetic) via MBTC. Every witness
//! gets a DEFINITE verdict (no `unknown`): convex/entailed cases via N-O exchange,
//! non-convex/free arrangements via the integer trichotomy split. z3 ground truth
//! is noted per witness.

use shinri_core::{BuiltinOp, Op};
use shinri_num::Rational;
use shinri_solver::{SolveOutcome, Solver};

fn int_const(s: &mut Solver, name: &str) -> shinri_core::TermId {
    let int = s.int_sort();
    s.declare_const(name, int)
}
fn int_num(s: &mut Solver, n: i128) -> shinri_core::TermId {
    let int = s.int_sort();
    s.numeral(Rational::from_int(n.into()), int)
}
fn int_fun1(s: &mut Solver, name: &str) -> shinri_core::SymbolId {
    let int = s.int_sort();
    s.declare_fun(name, &[int], int)
}

/// Entailed (pinned): x>=5 ∧ x<=5 ∧ distinct(f x)(f 5) ⇒ UNSAT (z3: unsat).
#[test]
fn int_bounds_pinned_unsat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let five = int_num(&mut s, 5);
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let f5 = s.app(Op::Uninterpreted(f), &[five]);
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[x, five]);
    let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, five]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, f5]);
    s.assert(ge);
    s.assert(le);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Non-fixed entailed: x<=y ∧ y<=x ∧ distinct(f x)(f y) ⇒ UNSAT (z3: unsat).
#[test]
fn int_nonfixed_entailed_unsat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let le1 = s.app(Op::Builtin(BuiltinOp::Le), &[x, y]);
    let le2 = s.app(Op::Builtin(BuiltinOp::Le), &[y, x]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fy]);
    s.assert(le1);
    s.assert(le2);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Genuinely SAT: (= x y) ∧ (= (f x) (f y)) ⇒ SAT (z3: sat).
#[test]
fn int_genuinely_sat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let xy = s.eq(x, y);
    let ffeq = s.eq(fx, fy);
    s.assert(xy);
    s.assert(ffeq);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

/// SOUNDNESS HEADLINE — non-convex: 1<=x ∧ x<=2 ∧ y=1 ∧ z=2 ∧
/// distinct(f x)(f y) ∧ distinct(f x)(f z) ⇒ UNSAT (z3: unsat). No single
/// equality is entailed; the MBTC trichotomy split on x decides x=1 (→ f(x)=f(y)
/// conflict) or x=2 (→ f(x)=f(z) conflict) ⇒ UNSAT. Was wrongly SAT pre-MBTC.
#[test]
fn int_nonconvex_unsat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let z = int_const(&mut s, "z");
    let one = int_num(&mut s, 1);
    let two = int_num(&mut s, 2);
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let fz = s.app(Op::Uninterpreted(f), &[z]);
    let xge1 = s.app(Op::Builtin(BuiltinOp::Ge), &[x, one]);
    let xle2 = s.app(Op::Builtin(BuiltinOp::Le), &[x, two]);
    let yeq = s.eq(y, one);
    let zeq = s.eq(z, two);
    let dxy = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fy]);
    let dxz = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fz]);
    for a in [xge1, xle2, yeq, zeq, dxy, dxz] {
        s.assert(a);
    }
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Free arrangement: x<=y ∧ distinct(f x)(f y) ⇒ SAT (z3: sat). arith may park
/// x=y; the trichotomy split picks x<y, then f(x)<f(y), yielding a valid model.
#[test]
fn int_free_arrangement_sat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, y]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fy]);
    s.assert(le);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}
```

- [ ] **Step 2: Run**

Run: `cargo test -p shinri-solver --test uflia_e2e`
Expected: all 5 PASS. Debugging guide: if `int_nonconvex_unsat` returns `Sat`, the MBTC split is not firing (re-check Task 3 placement and that Int terms reach the shared set, Task 4). If `int_bounds_pinned_unsat` returns `Sat`/`Unknown`, Int entailed-equality exchange is not running (re-check Task 1 Step 2 Int stamping and Task 4 `shared_arith_terms`). If a test hangs, suspect split non-termination (a pair being re-split); confirm the chosen branch actually changes `β`/merges so the pair leaves the model-equal-unmerged set.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/uflia_e2e.rs
git commit -m "test(uflia): MBTC e2e witnesses — entailed UNSAT, non-convex UNSAT, free-arrangement SAT"
```

---

### Task 6: Differential oracle — QF_UFLIA vs z3

**Files:**
- Modify: `crates/shinri-solver/tests/oracle.rs` (add `differential_qf_uflia_small`, mirroring `differential_qf_uf_small` at `oracle.rs:22`)
- Modify: `crates/shinri-theory/tests/oracle.rs` (update the `#[ignore]` note at `tests/oracle.rs:9`)

**Interfaces:**
- Consumes: the activated stack; `easy_smt` (`ContextBuilder`, `atom`, `declare_const`, `declare_fun`, `list`, `eq`, `not`, `lte`, `numeral`, `assert`, `check`, `Response`) and the `(SolveOutcome::Unknown, _) => {}` tolerance at `oracle.rs:89-94`. Note this harness references built-in sorts by atom (`ctx.atom("Real")`, `oracle.rs:167`), so Int is `ctx.atom("Int")`.

- [ ] **Step 1: Add the differential test**

In `crates/shinri-solver/tests/oracle.rs`, append (reusing the file's `Lcg`):

```rust
/// Differential QF_UFLIA vs z3. Random conjunctions of Int bounds and
/// (dis)equalities over `f : Int -> Int`. Any definite SAT/UNSAT that disagrees
/// with z3 is a P0 bug; `unknown` is tolerated (it should not occur for these,
/// but the match keeps the harness robust).
#[test]
fn differential_qf_uflia_small() {
    let mut rng = Lcg(0x171a);
    for _ in 0..200 {
        let mut s = Solver::new();
        let consts: Vec<_> = (0..3)
            .map(|i| {
                let int = s.int_sort();
                s.declare_const(&format!("c{i}"), int)
            })
            .collect();
        let f = s.declare_fun("f", &[s.int_sort()], s.int_sort());

        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        // Built-in sorts are referenced by atom in this harness (cf. ctx.atom("Real")).
        let zint = ctx.atom("Int");
        let z_consts: Vec<_> = (0..3)
            .map(|i| ctx.declare_const(format!("c{i}"), zint).unwrap())
            .collect();
        let _zf = ctx.declare_fun("f", vec![zint], zint).unwrap();
        let zf_atom = ctx.atom("f");

        let n_lits = 2 + rng.below(4) as usize;
        for _ in 0..n_lits {
            let i = rng.below(3) as usize;
            match rng.below(4) {
                2 => {
                    let k = rng.below(5) as i32;
                    let kn = {
                        let int = s.int_sort();
                        s.numeral(Rational::from_int((k as i128).into()), int)
                    };
                    let le = s.app(Op::Builtin(BuiltinOp::Le), &[consts[i], kn]);
                    s.assert(le);
                    ctx.assert(ctx.lte(z_consts[i], ctx.numeral(k))).unwrap();
                }
                3 => {
                    let j = rng.below(3) as usize;
                    let fi = s.app(Op::Uninterpreted(f), &[consts[i]]);
                    let fj = s.app(Op::Uninterpreted(f), &[consts[j]]);
                    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fi, fj]);
                    s.assert(dist);
                    let zfi = ctx.list(vec![zf_atom, z_consts[i]]);
                    let zfj = ctx.list(vec![zf_atom, z_consts[j]]);
                    ctx.assert(ctx.not(ctx.eq(zfi, zfj))).unwrap();
                }
                other => {
                    let j = rng.below(3) as usize;
                    let neg = other == 1;
                    let eqt = s.eq(consts[i], consts[j]);
                    let lit = if neg {
                        s.app(Op::Builtin(BuiltinOp::Not), &[eqt])
                    } else {
                        eqt
                    };
                    s.assert(lit);
                    let zeq = ctx.eq(z_consts[i], z_consts[j]);
                    ctx.assert(if neg { ctx.not(zeq) } else { zeq }).unwrap();
                }
            }
        }

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();
        match (ours, theirs) {
            (SolveOutcome::Unknown, _) => {}
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {}
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {}
            (o, t) => panic!("DISAGREEMENT (QF_UFLIA): shinri={o:?} z3={t:?}"),
        }
    }
}
```

If `s.declare_fun("f", &[s.int_sort()], s.int_sort())` trips the borrow checker (two `&self` calls in one expression), bind `let int = s.int_sort();` first and pass `&[int], int`.

- [ ] **Step 2: Update the combination-framework oracle note**

In `crates/shinri-theory/tests/oracle.rs`, change the ignore annotation (`tests/oracle.rs:9`):

```rust
#[ignore = "live in shinri-solver/tests/oracle.rs (differential_qf_uflia_small, --features oracle); \
            Combiner<Euf, Arith> activated for QF_UFLIA via MBTC"]
```

- [ ] **Step 3: Run (requires `z3` on PATH)**

Run: `cargo test -p shinri-solver --features oracle differential_qf_uflia_small -- --nocapture`
Expected: PASS — no `DISAGREEMENT` panic across 200 instances.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/oracle.rs crates/shinri-theory/tests/oracle.rs
git commit -m "test(oracle): QF_UFLIA differential vs z3 (MBTC) — milestone DoD"
```

---

## Final verification

- [ ] `cargo test --workspace` — all PASS.
- [ ] `cargo test -p shinri-solver --features oracle -- --nocapture` (z3 + cvc5 on PATH) — all differentials PASS, including `differential_qf_uflia_small`.
- [ ] Confirm the DoD (spec §8): the §1.1 non-convex witness returns UNSAT; the curated convex/entailed/free witnesses return their definite verdicts; QF_UFLRA / QF_UF / QF_LIA suites are unchanged.

## Notes for the implementer

- **Why the commit order matters (soundness):** Tasks 1–3 are inert because the shared set has no Int terms until Task 4, and the `bind_fresh` change is behavior-preserving for existing arith splits. Do not reorder Task 4 before Tasks 1–3, or there will be a transient commit where Int terms are shared but MBTC cannot decide their arrangement (unsound SAT).
- **Termination intuition:** the MBTC step emits one split per Full check; each split permanently decides one pair's `=`/`<`/`>` relation, after which that pair is no longer model-equal-unmerged and is never re-split. The undecided set strictly shrinks. This mirrors the existing integer-branching split, which also emits one split per check.
