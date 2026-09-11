# Slice 49 — EUF congruence lost for terms registered mid-search — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `EGraph`'s congruence index correct across backtracking for terms registered above decision level 0, closing the wrong-`sat` that loses datatype injectivity (and any other mid-search registration).

**Architecture:** `add_term` today does two things with the same, permanent, lifetime: *registration* (`apps`, `terms`, `seen_terms`) and *indexing* (a push onto each argument representative's use-list, and a `lookup` insert). Indexing is only valid for the classes of the level it ran at. The plan keeps registration permanent, makes indexing undoable through one new undo entry (`Undo::AppIndexed`), queues un-indexed apps on `pop`, and re-indexes them lazily at the next entry point that holds the equality engine. A new `close` drains congruences found at registration or re-index time, and it is called from `Euf::propagate` and `Euf::check`.

**Tech Stack:** Rust workspace, `mise` tasks, `cargo nextest` 0.9.140, `proptest` 1 (already a `shinri-euf` dev-dependency), z3/cvc5 from mise behind the `oracle` cargo feature, `shinri-bench` for corpus runs.

**Spec:** `docs/superpowers/specs/2026-09-11-shinri-slice49-euf-midsearch-index-design.md`. Read it alongside this plan; every task argues from it. §1.2 is the mechanism, §3 the fix, §4 the invariants and edge cases, §6 the tests, §7 the measurement.

## Global Constraints

- **Branch:** all work on `slice49-euf-midsearch-index`, branched from `main` at the commit that adds this plan (the spec+plan pair). PR to `main`, merge commit when CI is green, then delete the branch remote and local.
- **Pure-Rust mandate:** no native-link dependencies. `deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`. This slice adds **no** dependency of any kind.
- **Shared core:** `shinri-euf` backs every logic that routes atoms through EUF. The full **unfiltered** oracle run (`cargo nextest run -p shinri-solver --features oracle`) is a gate. A filtered run once skipped `qfs_differential` and nearly shipped a string `Sat → Unknown` regression.
- **Oracle feature gate:** `crates/shinri-solver/tests/qfdt_oracle.rs` is `#![cfg(feature = "oracle")]`. Every oracle command carries `--features oracle`. **Without it the file compiles to zero tests and the run reads as green.** Always confirm a non-zero discovered count.
- **nextest filters:** expression form only. `-E 'test(<name>)'` selects by test name; `-E 'binary(<name>)'` selects an integration-test binary. A positional `mod::name` filter matches nothing on nextest 0.9.140.
- **Formatting gate:** `cargo fmt --all` before every push. CI runs `cargo fmt --check` and fails fast.
- **Lint gate:** `cargo clippy --workspace --all-targets -- -D warnings` must be clean (`mise run lint` covers fmt + clippy).
- **Test tier:** nothing new may exceed the 5-minute threshold that would require `#[ignore = "exhaustive: nightly tier (~N min in CI)"]`. Never remove `#[ignore]` from the `shinri-fp` exhaustive suites.
- **Tests before fixes:** Tasks 1–3 commit tests that are **red** on the branch until Task 4/5 lands. Do not push before Task 6. Each "must fail on `main`" step records the verbatim failure output in the task report.
- **Never weaken a test to get green.** If a test that must pass after the fix still fails, the failing input is evidence: minimize it and trace it to a named code path before changing anything. A read-found cause is not a diagnosis until a named reproducer traces to it (slice 48's root-cause text was wrong for exactly this reason, spec §1.1).
- **Commit trailer:** every commit ends with `Claude-Session: https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH`.

**Ordering note: this plan folds spec §5 task 6 (the e2e pin) into Task 1.** The e2e repro fails on `main` today, so under TDD it belongs with the other tests that land first. The rest of spec §5 maps as follows: spec 1–5 → plan 1–5, spec 7 (gates) → plan 6, spec 8 (bench) → plan 7, spec 9 (review) → plan 8.

## File Structure

| file | responsibility | task |
| --- | --- | --- |
| `crates/shinri-euf/src/egraph.rs` | production change: `Undo::AppIndexed`, `reindex`, `index_app`, `flush_reindex`, `close`, the debug `UseSplice` check, the `pending` contract comment; declares the three test child modules | 1, 2, 4, 5 |
| `crates/shinri-euf/src/egraph/test_rig.rs` (new, `#[cfg(test)]`) | `Rig` (a scratch EUF world with push/pop in combiner order) and `EGraph::check_index` (spec §4.1) | 1, 2, 4 |
| `crates/shinri-euf/src/egraph/index_tests.rs` (new, `#[cfg(test)]`) | spec §4.2 cases 1–8 | 1, 4 |
| `crates/shinri-euf/src/egraph/index_props.rs` (new, `#[cfg(test)]`) | spec §6.2 differential property test | 2 |
| `crates/shinri-euf/src/solver.rs` | `Euf::propagate` / `Euf::check` call `close`; spec §4.2 case 9 tests | 5 |
| `crates/shinri-solver/tests/qfdt_oracle.rs` | spec §6.3 guarded-record generator | 3 |
| `crates/shinri-solver/tests/qfdt_e2e.rs` | spec §6.4 repro pins | 1 |
| `docs/superpowers/research/2026-09-11-smtlib-2024-slice49-euf-report.md` (new) | the measured outcome | 7 |
| `docs/superpowers/specs/2026-09-11-shinri-slice49-euf-midsearch-index-design.md` | append `## 12. Measured outcomes` | 7 |

The three test files are child modules of `egraph` (`egraph.rs` is a non-`mod.rs` file, so its children live in `src/egraph/`). As children they can read `EGraph`'s private fields, which `check_index` and several edge cases need.

---

### Task 1: Test rig, index checker, unit regression, and e2e repro pins

The defect's minimal unit shape (spec §1.3) and its end-to-end shape (spec §1), both failing on `main`, plus the checker every later test calls.

**Files:**
- Modify: `crates/shinri-euf/src/egraph.rs` (add two module declarations directly above the existing `#[cfg(test)] mod tests {` at `:482`)
- Create: `crates/shinri-euf/src/egraph/test_rig.rs`
- Create: `crates/shinri-euf/src/egraph/index_tests.rs`
- Modify: `crates/shinri-solver/tests/qfdt_e2e.rs` (append)

**Interfaces:**
- Consumes: `EGraph::{add_term, merge_eq, push, pop, signature}` and its private fields `apps`, `use_list`, `lookup`, `pending` (all exist on `main`).
- Produces, all `pub(crate)` inside `egraph`:
  - `struct Rig { ctx: Context, eq: EqualityEngine, atoms: AtomRegistry, g: EGraph, .. }` with `Rig::new() -> Rig`, `konst(&mut self, &str) -> TermId`, `fun(&mut self, &str, usize) -> SymbolId`, `app(&mut self, SymbolId, &[TermId]) -> TermId`, `add(&mut self, TermId)`, `merge(&mut self, TermId, TermId) -> Option<Vec<EqLeaf>>`, `push(&mut self)`, `pop(&mut self, usize)`, `equal(&mut self, TermId, TermId) -> bool`, `assert_index(&self)`.
  - `EGraph::check_index(&self, eq: &EqualityEngine) -> Result<(), String>`.
  - Task 2 adds `Rig::diseq` and `Rig::drain`; Task 4 extends `check_index`.

- [ ] **Step 1: Declare the test modules**

In `crates/shinri-euf/src/egraph.rs`, directly above the line `#[cfg(test)]` that opens `mod tests {` (`:482`), insert:

```rust
#[cfg(test)]
mod index_tests;
#[cfg(test)]
mod test_rig;

```

- [ ] **Step 2: Write the rig and the index checker**

Create `crates/shinri-euf/src/egraph/test_rig.rs`:

```rust
//! Test-only harness and index-invariant checker for `EGraph` (slice 49,
//! spec §4.1). A child module of `egraph`, so it reads private fields.

use super::{AppId, EGraph};
use rustc_hash::FxHashMap;
use shinri_core::{Context, Lit, Op, SortId, SymbolId, TermId, Var};
use shinri_theory::types::{ENodeId, EqJust, EqLeaf};
use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx};

impl EGraph {
    /// Spec §4.1. `Ok` iff, for every indexed app:
    ///
    /// * (I-use) it sits on the use-list of each argument's CURRENT
    ///   representative, exactly as often as that representative occurs among
    ///   its argument representatives, and on no other use-list;
    /// * (I-lookup) `lookup` holds its current signature, naming either the
    ///   app itself or an app in the same class or linked to it through live,
    ///   non-stale `pending` entries.
    ///
    /// Not meaningful between a returned conflict and the `pop` that follows
    /// it: a conflict can consume a `pending` entry whose merge never happened.
    pub(crate) fn check_index(&self, eq: &EqualityEngine) -> Result<(), String> {
        let mut on_lists: FxHashMap<AppId, Vec<usize>> = FxHashMap::default();
        for (idx, list) in self.use_list.iter().enumerate() {
            for &app in list {
                on_lists.entry(app).or_default().push(idx);
            }
        }

        // Classes, plus the links that live, non-stale pending congruences add.
        let mut link: FxHashMap<ENodeId, ENodeId> = FxHashMap::default();
        fn root(link: &FxHashMap<ENodeId, ENodeId>, mut x: ENodeId) -> ENodeId {
            while let Some(&p) = link.get(&x) {
                x = p;
            }
            x
        }
        for (na, nb, pairs) in &self.pending {
            if pairs.iter().all(|&(pa, pb)| eq.find(pa) == eq.find(pb)) {
                let ra = root(&link, eq.find(*na));
                let rb = root(&link, eq.find(*nb));
                if ra != rb {
                    link.insert(ra, rb);
                }
            }
        }
        let linked = |a: ENodeId, b: ENodeId| root(&link, eq.find(a)) == root(&link, eq.find(b));

        for (i, a) in self.apps.iter().enumerate() {
            let app = i as AppId;
            let mut want: Vec<usize> = a.args.iter().map(|&x| eq.find(x).index()).collect();
            want.sort_unstable();
            let mut have = on_lists.get(&app).cloned().unwrap_or_default();
            have.sort_unstable();
            if want != have {
                return Err(format!(
                    "(I-use) app {app} (op {:?}): argument representatives {want:?} but on use-lists {have:?}",
                    a.op
                ));
            }
            let sig = self.signature(eq, app);
            match self.lookup.get(&sig) {
                None => {
                    return Err(format!(
                        "(I-lookup) app {app} (op {:?}): current signature {sig:?} is missing from lookup",
                        a.op
                    ))
                }
                Some(&other) if other != app && !linked(a.node, self.apps[other as usize].node) => {
                    return Err(format!(
                        "(I-lookup) app {app}: lookup[{sig:?}] = app {other}, which is neither in its class nor pending-linked"
                    ))
                }
                Some(_) => {}
            }
        }
        Ok(())
    }
}

/// A scratch EUF world: one uninterpreted sort `U`, a shared equality engine,
/// an `EGraph`, and push/pop in the combiner's order (engine first, then the
/// EGraph — `combiner.rs:500-501`).
pub(crate) struct Rig {
    pub(crate) ctx: Context,
    pub(crate) eq: EqualityEngine,
    pub(crate) atoms: AtomRegistry,
    pub(crate) g: EGraph,
    u: SortId,
    next_lit: u32,
}

impl Rig {
    pub(crate) fn new() -> Rig {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        Rig {
            ctx,
            eq: EqualityEngine::default(),
            atoms: AtomRegistry::default(),
            g: EGraph::default(),
            u,
            next_lit: 1,
        }
    }

    pub(crate) fn konst(&mut self, name: &str) -> TermId {
        let s = self.ctx.declare_fun(name, &[], self.u);
        self.ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    pub(crate) fn fun(&mut self, name: &str, arity: usize) -> SymbolId {
        let params = vec![self.u; arity];
        self.ctx.declare_fun(name, &params, self.u)
    }

    pub(crate) fn app(&mut self, f: SymbolId, args: &[TermId]) -> TermId {
        self.ctx.mk_app(Op::Uninterpreted(f), args).unwrap()
    }

    /// Register `t` and its subterms with the EGraph at the current level.
    pub(crate) fn add(&mut self, t: TermId) {
        let mut cx = TheoryCtx {
            terms: &mut self.ctx,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        self.g.add_term(&mut cx, t);
    }

    fn just(&mut self) -> EqJust {
        let l = Lit::new(Var::new(self.next_lit), true);
        self.next_lit += 1;
        EqJust::Asserted(l)
    }

    /// `merge_eq(a, b)`, then empty the engine's merge-event queue so a later
    /// `pop` is legal (`EqualityEngine::pop` asserts it is drained).
    pub(crate) fn merge(&mut self, a: TermId, b: TermId) -> Option<Vec<EqLeaf>> {
        let (na, nb) = (self.eq.intern(a), self.eq.intern(b));
        let j = self.just();
        let r = self.g.merge_eq(&mut self.eq, na, nb, j);
        self.eq.drain_merges(&mut Vec::new());
        r
    }

    pub(crate) fn push(&mut self) {
        self.eq.push();
        self.g.push();
    }

    pub(crate) fn pop(&mut self, level: usize) {
        self.eq.drain_merges(&mut Vec::new());
        self.eq.pop(level);
        self.g.pop(level);
    }

    pub(crate) fn equal(&mut self, a: TermId, b: TermId) -> bool {
        let (na, nb) = (self.eq.intern(a), self.eq.intern(b));
        self.eq.are_equal(na, nb)
    }

    pub(crate) fn assert_index(&self) {
        if let Err(e) = self.g.check_index(&self.eq) {
            panic!("index invariant violated: {e}");
        }
    }
}
```

- [ ] **Step 3: Write the unit regression (spec §4.2 case 8)**

Create `crates/shinri-euf/src/egraph/index_tests.rs`:

```rust
//! Slice 49: the congruence index across backtracking (spec §4.2).

use super::test_rig::Rig;

/// Spec §4.2 case 8 / §1.3. An app registered above level 0, while its
/// argument's class is the product of a merge at that level, must keep its
/// congruence after the level is popped and the classes merge again.
///
/// Pre-slice, `add_term` filed `f(b)` under `a`'s use-list (the level-1
/// representative) with no undo record; after the pop `b` is its own
/// representative again but `f(b)` is still on `a`'s list, so the re-merge
/// (same winner, `a`) walks `b`'s empty list and never re-detects
/// `f(a) = f(b)`.
#[test]
fn midsearch_registration_keeps_congruence_across_backtrack() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);

    // Level 1: a = b, then register f(a) and f(b) over the merged class.
    r.push();
    assert!(r.merge(a, b).is_none());
    r.add(fa);
    r.add(fb);
    assert!(r.merge(a, a).is_none(), "a no-op merge drains the registration-time collision");
    assert!(r.equal(fa, fb), "level 1: congruence must hold");
    r.assert_index();

    // Backtrack: a = b and f(a) = f(b) are both undone.
    r.pop(0);
    assert!(!r.equal(fa, fb));
    r.assert_index();

    // Re-derive a = b: the congruence must be re-detected.
    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(
        r.equal(fa, fb),
        "congruence lost after mid-search add_term + backtrack"
    );
    r.assert_index();
}
```

- [ ] **Step 4: Run it and confirm it fails on `main`**

Run: `cargo nextest run -p shinri-euf -E 'test(midsearch_registration_keeps_congruence_across_backtrack)' --no-capture`

Expected: 1 test discovered, **FAIL**, panicking at the post-pop `assert_index` with a message of this shape (apps are `a`=0, `b`=1, `f(a)`=2, `f(b)`=3):

```
index invariant violated: (I-use) app 3 (op Uninterpreted(..)): argument representatives [1] but on use-lists [0]
```

Record the verbatim output in the task report. If it fails in some *other* way (a compile error, or a different assertion), stop: the checker or the rig is wrong, not the fix target.

- [ ] **Step 5: Append the e2e repro pins**

Append to `crates/shinri-solver/tests/qfdt_e2e.rs`:

```rust
#[test]
fn injectivity_over_selector_minted_under_a_case_split_is_unsat() {
    // Slice 49 (spec §1). `(right u) = (right q)` is derived only inside an
    // `ite` whose branches are equal, so `(stack C empty)` and
    // `(stack H empty)` merge above decision level 0. DT's injectivity rule
    // then mints `top(..)`/`rest(..)` on both applications mid-search. EUF
    // filed those apps under the merged class with no undo record, lost them
    // on the next backtrack, never re-derived `top(stack C empty) =
    // top(stack H empty)` (so `C = H` never surfaced), and answered `sat`.
    // Delta-debugged by slice 48 from
    // QF_DT/20230720-blocksworld/blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2;
    // z3 and cvc5 both answer `unsat`.
    let out = run_script(
        "(set-logic QF_DT)\
         (declare-datatypes ((E 0)) (((A) (C) (H))))\
         (declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))\
         (declare-datatypes ((R 0)) (((R (right T)))))\
         (declare-fun p () R)(declare-fun q () R)(declare-fun u () R)(declare-fun c () E)\
         (assert (= (right p) (stack C empty)))\
         (assert (= q p))\
         (assert (ite (= c A) (= (right u) (right q)) (= (right u) (right q))))\
         (assert (= (right u) (stack H empty)))\
         (check-sat)",
    );
    assert_eq!(
        out,
        vec!["unsat"],
        "a selector application minted while a same-constructor merge holds only \
         inside a case split must keep its congruence across backtracking"
    );
}

#[test]
fn injectivity_over_selector_with_the_equality_as_a_unit_is_unsat() {
    // Guard for the test above: the same query with the `ite` replaced by its
    // unit equality. Every literal is then at level 0, so this was already
    // `unsat` before slice 49; it pins that the fix does not depend on the
    // `ite`.
    let out = run_script(
        "(set-logic QF_DT)\
         (declare-datatypes ((E 0)) (((A) (C) (H))))\
         (declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))\
         (declare-datatypes ((R 0)) (((R (right T)))))\
         (declare-fun p () R)(declare-fun q () R)(declare-fun u () R)(declare-fun c () E)\
         (assert (= (right p) (stack C empty)))\
         (assert (= q p))\
         (assert (= (right u) (right q)))\
         (assert (= (right u) (stack H empty)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}
```

- [ ] **Step 6: Run the e2e pins and confirm the split verdict on `main`**

Run: `cargo nextest run -p shinri-solver -E 'test(injectivity_over_selector_minted_under_a_case_split_is_unsat) | test(injectivity_over_selector_with_the_equality_as_a_unit_is_unsat)'`

Expected: 2 tests discovered. `…_minted_under_a_case_split_is_unsat` **FAILS** with `left: ["sat"]`, `right: ["unsat"]`. `…_with_the_equality_as_a_unit_is_unsat` **PASSES**. Record both.

- [ ] **Step 7: Commit (red on purpose)**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/egraph/test_rig.rs \
        crates/shinri-euf/src/egraph/index_tests.rs crates/shinri-solver/tests/qfdt_e2e.rs
git commit
```

Commit message:
```
test(euf): slice49 T1 - index checker, backtrack regression, e2e repro pins

Red until T4: the unit regression and the ite-guarded e2e repro both fail on
main (spec 1.3), the unit-equality guard passes.

Claude-Session: https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH
```

---

### Task 2: Differential property test

Random traces over push/pop/merge/diseq/register, compared against a from-scratch congruence closure, with `check_index` after every step (spec §6.2). This test finds the defect class generally rather than the one shape Task 1 pins.

**Files:**
- Modify: `crates/shinri-euf/src/egraph.rs` (add one more module declaration beside Task 1's)
- Modify: `crates/shinri-euf/src/egraph/test_rig.rs` (add `diseq` and `drain`)
- Create: `crates/shinri-euf/src/egraph/index_props.rs`

**Interfaces:**
- Consumes: Task 1's `Rig` and `EGraph::check_index`; `EGraph::registered_terms()` (`egraph.rs:85`).
- Produces: `Rig::diseq(&mut self, TermId, TermId) -> Option<Vec<EqLeaf>>` and `Rig::drain(&mut self, TermId) -> Option<Vec<EqLeaf>>`. Task 4 uses `drain`.

- [ ] **Step 1: Add `diseq` and `drain` to the rig**

In `crates/shinri-euf/src/egraph/test_rig.rs`, inside `impl Rig`, directly after `merge`:

```rust
    pub(crate) fn diseq(&mut self, a: TermId, b: TermId) -> Option<Vec<EqLeaf>> {
        let (na, nb) = (self.eq.intern(a), self.eq.intern(b));
        let j = self.just();
        let r = self.g.assert_diseq(&mut self.eq, na, nb, j);
        self.eq.drain_merges(&mut Vec::new());
        r
    }

    /// Close pending congruences using only APIs that exist before slice 49:
    /// `merge_eq(k, k)` returns before merging and then drains `pending` (the
    /// idiom of `stale_pending_congruence_not_drained_after_backtrack`). After
    /// slice 49, `merge_eq` flushes the re-index queue first, so this behaves
    /// like `EGraph::close`.
    pub(crate) fn drain(&mut self, k: TermId) -> Option<Vec<EqLeaf>> {
        self.merge(k, k)
    }
```

- [ ] **Step 2: Declare the property module**

In `crates/shinri-euf/src/egraph.rs`, extend Task 1's declarations to:

```rust
#[cfg(test)]
mod index_props;
#[cfg(test)]
mod index_tests;
#[cfg(test)]
mod test_rig;
```

- [ ] **Step 3: Write the property test**

Create `crates/shinri-euf/src/egraph/index_props.rs`:

```rust
//! Slice 49, spec §6.2: `EGraph` against a from-scratch congruence closure,
//! over random push/pop/merge/diseq/register traces, with the index
//! invariants (spec §4.1) checked after every step.

use super::test_rig::Rig;
use proptest::prelude::*;
use rustc_hash::FxHashMap;
use shinri_core::{Op, TermId, TermNode};

#[derive(Clone, Debug)]
enum Step {
    Push,
    Pop(u8),
    Merge(u8, u8),
    Diseq(u8, u8),
    Register(u8),
    /// A merge immediately followed by a registration: spec §1.2 step 1, the
    /// defect's shape, which independent steps reach too rarely.
    MergeThenRegister(u8, u8, u8),
    Drain,
}

fn step() -> impl Strategy<Value = Step> {
    prop_oneof![
        2 => Just(Step::Push),
        1 => any::<u8>().prop_map(Step::Pop),
        2 => (any::<u8>(), any::<u8>()).prop_map(|(a, b)| Step::Merge(a, b)),
        1 => (any::<u8>(), any::<u8>()).prop_map(|(a, b)| Step::Diseq(a, b)),
        2 => any::<u8>().prop_map(Step::Register),
        3 => (any::<u8>(), any::<u8>(), any::<u8>())
            .prop_map(|(a, b, p)| Step::MergeThenRegister(a, b, p)),
        2 => Just(Step::Drain),
    ]
}

const MAX_LEVEL: usize = 5;

struct World {
    r: Rig,
    /// Candidate terms: constants c0..c3, f(ci), g(ci,cj), f(f(ci)), g(f(ci),cj).
    pool: Vec<TermId>,
    /// `levels[k]`: equalities (`true`) and disequalities (`false`) asserted at level k.
    levels: Vec<Vec<(TermId, TermId, bool)>>,
    /// A level-0 constant whose no-op merge drains `pending`.
    anchor: TermId,
}

impl World {
    fn new() -> World {
        let mut r = Rig::new();
        let consts: Vec<TermId> = (0..4).map(|i| r.konst(&format!("c{i}"))).collect();
        let f = r.fun("f", 1);
        let g = r.fun("g", 2);
        let mut pool = consts.clone();
        for &c in &consts {
            pool.push(r.app(f, &[c]));
        }
        for &x in &consts {
            for &y in &consts {
                pool.push(r.app(g, &[x, y]));
            }
        }
        for &c in &consts {
            let fc = r.app(f, &[c]);
            pool.push(r.app(f, &[fc]));
        }
        for &x in &consts {
            let fx = r.app(f, &[x]);
            for &y in &consts {
                pool.push(r.app(g, &[fx, y]));
            }
        }
        for &c in &consts {
            r.add(c);
        }
        World {
            r,
            pool,
            levels: vec![Vec::new()],
            anchor: consts[0],
        }
    }

    fn level(&self) -> usize {
        self.levels.len() - 1
    }

    fn registered(&self) -> Vec<TermId> {
        self.r.g.registered_terms().iter().map(|&(t, _)| t).collect()
    }

    fn pick(&self, i: u8) -> TermId {
        let reg = self.registered();
        reg[i as usize % reg.len()]
    }

    fn pop_to(&mut self, k: usize) {
        self.r.pop(k);
        self.levels.truncate(k + 1);
    }

    /// A theory conflict: backtrack one level, as the SAT solver would.
    /// Returns `false` when the conflict is at level 0 (the trace is over).
    fn on_conflict(&mut self) -> bool {
        match self.level() {
            0 => false,
            l => {
                self.pop_to(l - 1);
                true
            }
        }
    }

    fn merge(&mut self, a: u8, b: u8) -> bool {
        let (ta, tb) = (self.pick(a), self.pick(b));
        self.levels.last_mut().unwrap().push((ta, tb, true));
        if self.r.merge(ta, tb).is_some() {
            self.on_conflict()
        } else {
            true
        }
    }

    fn register(&mut self, p: u8) {
        let t = self.pool[p as usize % self.pool.len()];
        self.r.add(t);
    }

    /// Run one step. `Ok(false)` ends the trace.
    fn run(&mut self, s: &Step) -> Result<bool, TestCaseError> {
        let alive = match *s {
            Step::Push => {
                if self.level() >= MAX_LEVEL {
                    true
                } else if self.r.drain(self.anchor).is_some() {
                    // Spec §3.4's drain-before-push contract: the SAT loop
                    // propagates (and EUF closes) before every decision push.
                    self.on_conflict()
                } else {
                    self.compare()?;
                    self.r.push();
                    self.levels.push(Vec::new());
                    true
                }
            }
            Step::Pop(k) => {
                if self.level() > 0 {
                    let k = k as usize % self.level();
                    self.pop_to(k);
                }
                true
            }
            Step::Merge(a, b) => self.merge(a, b),
            Step::Diseq(a, b) => {
                let (ta, tb) = (self.pick(a), self.pick(b));
                if self.level() == 0 || ta == tb {
                    true
                } else {
                    self.levels.last_mut().unwrap().push((ta, tb, false));
                    if self.r.diseq(ta, tb).is_some() {
                        self.on_conflict()
                    } else {
                        true
                    }
                }
            }
            Step::Register(p) => {
                self.register(p);
                true
            }
            Step::MergeThenRegister(a, b, p) => {
                let alive = self.merge(a, b);
                if alive {
                    self.register(p);
                }
                alive
            }
            Step::Drain => {
                if self.r.drain(self.anchor).is_some() {
                    self.on_conflict()
                } else {
                    self.compare()?;
                    true
                }
            }
        };
        if alive {
            self.r
                .g
                .check_index(&self.r.eq)
                .map_err(TestCaseError::fail)?;
        }
        Ok(alive)
    }

    /// Only valid right after a drain that returned no conflict: the engine's
    /// equivalence over registered terms must equal a from-scratch congruence
    /// closure of the live equalities.
    fn compare(&mut self) -> Result<(), TestCaseError> {
        fn find(uf: &mut [usize], mut x: usize) -> usize {
            while uf[x] != x {
                uf[x] = uf[uf[x]];
                x = uf[x];
            }
            x
        }
        let reg = self.registered();
        let idx: FxHashMap<TermId, usize> = reg.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let mut uf: Vec<usize> = (0..reg.len()).collect();
        for &(a, b, pos) in self.levels.iter().flatten() {
            if pos {
                let (ra, rb) = (find(&mut uf, idx[&a]), find(&mut uf, idx[&b]));
                uf[ra] = rb;
            }
        }
        let shapes: Vec<Option<(Op, Vec<usize>)>> = reg
            .iter()
            .map(|&t| match self.r.ctx.term_node(t) {
                TermNode::App { op, args, .. } => Some((
                    *op,
                    self.r.ctx.children(*args).iter().map(|k| idx[k]).collect(),
                )),
                TermNode::Const { .. } => None,
            })
            .collect();
        loop {
            let mut changed = false;
            let mut table: FxHashMap<(Op, Vec<usize>), usize> = FxHashMap::default();
            for (i, shape) in shapes.iter().enumerate() {
                let Some((op, kids)) = shape else { continue };
                let key = (*op, kids.iter().map(|&k| find(&mut uf, k)).collect::<Vec<_>>());
                match table.get(&key) {
                    Some(&j) => {
                        let (ri, rj) = (find(&mut uf, i), find(&mut uf, j));
                        if ri != rj {
                            uf[ri] = rj;
                            changed = true;
                        }
                    }
                    None => {
                        table.insert(key, i);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for &(a, b, pos) in self.levels.iter().flatten() {
            if !pos && find(&mut uf, idx[&a]) == find(&mut uf, idx[&b]) {
                return Err(TestCaseError::fail(format!(
                    "reference: live disequality {a:?} != {b:?} is violated, but the engine reported no conflict"
                )));
            }
        }
        for (i, &ti) in reg.iter().enumerate() {
            for (j, &tj) in reg.iter().enumerate().skip(i + 1) {
                let want = find(&mut uf, i) == find(&mut uf, j);
                let got = self.r.equal(ti, tj);
                if want != got {
                    return Err(TestCaseError::fail(format!(
                        "engine: {ti:?} {} {tj:?}; reference: {}",
                        if got { "==" } else { "!=" },
                        if want { "equal" } else { "distinct" }
                    )));
                }
            }
        }
        Ok(())
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 512,
        failure_persistence: None,
        ..ProptestConfig::default()
    })]

    #[test]
    fn egraph_matches_reference_closure(steps in prop::collection::vec(step(), 1..80)) {
        let mut w = World::new();
        for s in &steps {
            if !w.run(s)? {
                return Ok(());
            }
        }
        if w.r.drain(w.anchor).is_none() {
            w.compare()?;
        }
    }
}
```

`failure_persistence: None` keeps proptest from writing a `proptest-regressions/` directory into the source tree. The repo commits none.

- [ ] **Step 4: Run it and confirm it fails on `main`**

Run: `cargo nextest run -p shinri-euf -E 'test(egraph_matches_reference_closure)' --no-capture`

Expected: 1 test discovered, **FAIL**. The output ends with `minimal failing input: steps = [...]` and an `(I-use)` or `(I-lookup)` violation, or an `engine: … != …; reference: equal` mismatch. Quote the minimal failing input and the message in the task report. A typical minimal trace has the §1.2 shape: `Push`, a `MergeThenRegister` whose registered term's argument is the merge loser, then `Pop`.

**If it passes on `main`:** the generator does not reach the defect, and the test proves nothing. Raise `cases` to 2048 and the trace length bound to `1..120`, and re-run. If it still passes, stop and report. Do not proceed to Task 4 with a property test that cannot see the bug.

**If it fails with a message that is not about the index or congruence** (for example a panic inside `EqualityEngine`): the model violates an engine precondition. Fix the model, write down why in the task report, and re-run until the failure is the defect.

- [ ] **Step 5: Confirm the runtime budget**

The Step 4 run's wall time for this test must be under 10 s. If it is not, halve `cases`, then confirm Step 4 still fails.

- [ ] **Step 6: Commit (red on purpose)**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/egraph/test_rig.rs \
        crates/shinri-euf/src/egraph/index_props.rs
git commit
```

Commit message:
```
test(euf): slice49 T2 - differential property test against a reference closure

Red until T4: fails on main with <quote the one-line failure message>.

Claude-Session: https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH
```

---

### Task 3: `qfdt_oracle` guarded-record generator

`gen_instance` (`qfdt_oracle.rs:373`) emits only top-level ground conjuncts, so every literal lands at level 0 and EUF never registers a term mid-search. Its 300 iterations with 0 mismatches did not cover this defect (spec §6.3). A throwaway Python prototype of the generator below produced 7 mismatches in 300 iterations on `main` (shinri `sat`, z3 `unsat`) during planning. The Rust version must be shown to fail too.

**Files:**
- Modify: `crates/shinri-solver/tests/qfdt_oracle.rs` (append; do not touch existing tests)

**Interfaces:**
- Consumes: the file's `shinri_answer(&str) -> String` (`:25`), `z3_answer(&str) -> String` (`:95`), `Lcg` (`:282`), and `N_ITERS` (`:293`).
- Produces: nothing other tasks call. Task 6 re-runs the binary.

- [ ] **Step 1: Write the generator and the test**

Append to `crates/shinri-solver/tests/qfdt_oracle.rs`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 49: guarded-record generator.
//
// `gen_instance` above emits only top-level ground conjuncts, so every literal
// lands at decision level 0 and EUF never registers a term mid-search. The
// slice-49 defect (spec §1.2) needs exactly that: a selector application
// minted by DT's injectivity rule while a same-constructor merge holds only
// inside a case split. This generator wraps equalities over a record of a
// constructor-bearing datatype in `ite`/`or` guards, including the degenerate
// both-branches-equal guard the reduced repro uses.
// ─────────────────────────────────────────────────────────────────────────────

const GUARDED_RECORD: &str = "(declare-datatypes ((E 0)) (((A) (C) (H))))\
(declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))\
(declare-datatypes ((R 0)) (((R (right T)))))\
(declare-fun p () R)(declare-fun q () R)(declare-fun u () R)\
(declare-fun c () E)(declare-fun e1 () E)(declare-fun t1 () T)";

const RECS: [&str; 3] = ["p", "q", "u"];
const ENUMS: [&str; 3] = ["A", "C", "H"];

fn gr_rec(rng: &mut Lcg) -> &'static str {
    RECS[rng.below(3) as usize]
}

fn gr_enum(rng: &mut Lcg) -> &'static str {
    ["A", "C", "H", "e1", "c"][rng.below(5) as usize]
}

fn gr_stack(rng: &mut Lcg) -> String {
    match rng.below(5) {
        0 => format!("(stack {} empty)", gr_enum(rng)),
        1 => format!("(right {})", gr_rec(rng)),
        2 => "empty".into(),
        3 => "t1".into(),
        _ => format!("(stack {} t1)", gr_enum(rng)),
    }
}

fn gr_atom(rng: &mut Lcg) -> String {
    match rng.below(5) {
        0 => {
            let (x, y) = (gr_rec(rng), gr_rec(rng));
            format!("(= {x} {y})")
        }
        1 => {
            let (x, e) = (gr_rec(rng), gr_enum(rng));
            format!("(= (top (right {x})) {e})")
        }
        _ => {
            let x = gr_rec(rng);
            format!("(= (right {x}) {})", gr_stack(rng))
        }
    }
}

fn gr_guarded(rng: &mut Lcg) -> String {
    let b1 = gr_atom(rng);
    let b2 = if rng.below(2) == 0 {
        b1.clone()
    } else {
        gr_atom(rng)
    };
    if rng.below(2) == 0 {
        let k = ENUMS[rng.below(3) as usize];
        format!("(ite (= c {k}) {b1} {b2})")
    } else {
        format!("(or {b1} {b2})")
    }
}

fn gen_guarded_record(rng: &mut Lcg) -> String {
    let n = 3 + rng.below(4) as usize;
    let mut asserts = String::new();
    for _ in 0..n {
        let c = if rng.below(2) == 0 {
            gr_guarded(rng)
        } else {
            gr_atom(rng)
        };
        asserts.push_str(&format!("(assert {c})"));
    }
    format!("(set-logic QF_DT){GUARDED_RECORD}{asserts}(check-sat)")
}

#[test]
fn qfdt_random_guarded_records_match_z3() {
    let mut rng = Lcg(0xD7_0000_0049u64);
    let (mut n_sat, mut n_unsat, mut n_skipped) = (0usize, 0usize, 0usize);

    for it in 0..N_ITERS {
        let src = gen_guarded_record(&mut rng);
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
            "QF_DT SOUNDNESS DISAGREEMENT (guarded records, iter {it}): shinri={ours} z3={theirs}\n\
             Reproduce with this instance:\n{src}"
        );
        if ours == "sat" {
            n_sat += 1;
        } else {
            n_unsat += 1;
        }
    }

    println!(
        "qfdt_random_guarded_records_match_z3: {N_ITERS} iters, {n_sat} sat / {n_unsat} unsat / \
         {n_skipped} skipped, 0 mismatches"
    );
    assert!(n_sat > 0, "generator produced no sat instances");
    assert!(n_unsat > 0, "generator produced no unsat instances");
}
```

- [ ] **Step 2: Run it and confirm it fails on `main`**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfdt_random_guarded_records_match_z3)' --no-capture`

Expected: **1 test discovered** (0 means the feature flag is missing, so stop), **FAIL** with `QF_DT SOUNDNESS DISAGREEMENT (guarded records, iter N): shinri=sat z3=unsat` and the instance. Quote the instance verbatim in the task report.

**If it passes on `main`:** do not change the seed to hunt for a failing one. Change the loop bound to a new `const N_GUARDED_ITERS: usize = 900;` and re-run. If it still passes, stop and report: the prototype's 7/300 rate did not carry over, and the generator needs re-shaping before its coverage claim means anything.

- [ ] **Step 3: Confirm the existing QF_DT oracle suite is unaffected**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'binary(qfdt_oracle)'`

Expected: every test except `qfdt_random_guarded_records_match_z3` passes. The discovered count is the pre-existing 17 plus 1.

- [ ] **Step 4: Commit (red on purpose)**

```bash
git add crates/shinri-solver/tests/qfdt_oracle.rs
git commit
```

Commit message:
```
test(qfdt): slice49 T3 - guarded-record generator reaches mid-search selectors

Red until the fix: fails on main at iter <N> (shinri sat, z3 unsat).

Claude-Session: https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH
```

---

### Task 4: `index_app`, `Undo::AppIndexed`, and the lazy re-index

The fix itself (spec §3.1–3.3, §3.5). After this task, Tasks 1 and 2 are green. Task 3 is expected green; if it is not, Task 5 must turn it green, and the task report says which.

**Files:**
- Modify: `crates/shinri-euf/src/egraph.rs`
- Modify: `crates/shinri-euf/src/egraph/test_rig.rs` (`check_index` gains the queue)
- Modify: `crates/shinri-euf/src/egraph/index_tests.rs` (spec §4.2 cases 1–7)

**Interfaces:**
- Consumes: Task 1's `Rig` and `check_index`; Task 2's `Rig::drain`.
- Produces (private to `egraph`):
  - `Undo::AppIndexed { app: AppId, reps: Vec<ENodeId>, inserted_sig: Option<Signature> }`
  - the `UseSplice` field `moved: Vec<AppId>` (populated only in debug builds)
  - `EGraph.reindex: Vec<AppId>`
  - `fn index_app(&mut self, eq: &EqualityEngine, app: AppId)`
  - `fn flush_reindex(&mut self, eq: &EqualityEngine)`

  Task 5 calls `flush_reindex` from `close`.

- [ ] **Step 1: Write the edge-case tests (spec §4.2 cases 1–7)**

Append to `crates/shinri-euf/src/egraph/index_tests.rs`:

```rust
/// Spec §4.2 case 1: duplicate arguments. `g(a, a)` is pushed twice onto one
/// use-list; undo must pop both, LIFO. Pre-slice, `UseSplice`'s undo moves the
/// wrong tail block back and strands `g(b, b)` on `a`'s list.
#[test]
fn duplicate_argument_app_survives_backtrack() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let g = r.fun("g", 2);
    let gaa = r.app(g, &[a, a]);
    let gbb = r.app(g, &[b, b]);
    r.add(a);
    r.add(b);
    r.add(gbb);

    r.push();
    assert!(r.merge(a, b).is_none());
    r.add(gaa);
    assert!(r.drain(a).is_none());
    assert!(r.equal(gaa, gbb));
    r.assert_index();

    r.pop(0);
    assert!(!r.equal(gaa, gbb));
    r.assert_index();

    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(r.equal(gaa, gbb), "g(a,a) = g(b,b) must be re-derived");
    r.assert_index();
}

/// Spec §4.2 case 2: nested registration. `f(f(a))` registers `f(a)` first;
/// each gets its own `AppIndexed`, undone outer-first and re-indexed
/// inner-first.
#[test]
fn nested_midsearch_registration_survives_backtrack() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    let ffa = r.app(f, &[fa]);
    let ffb = r.app(f, &[fb]);
    r.add(a);
    r.add(b);
    r.add(ffb);

    r.push();
    assert!(r.merge(a, b).is_none());
    r.add(ffa);
    assert!(r.drain(a).is_none());
    assert!(r.equal(ffa, ffb));
    r.assert_index();

    r.pop(0);
    assert!(!r.equal(ffa, ffb));
    r.assert_index();

    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(r.equal(fa, fb), "f(a) = f(b) must be re-derived");
    assert!(r.equal(ffa, ffb), "f(f(a)) = f(f(b)) must be re-derived");
    r.assert_index();
}

/// Spec §4.2 case 3: the indexed-onto representative loses a later merge at
/// the same level. Undo reverses the splice first, which returns the app to
/// the loser's tail for `AppIndexed`'s pop. Already correct pre-slice (the app
/// is keyed on its own argument); pins the LIFO order the new debug checks
/// rely on.
#[test]
fn app_on_a_later_merge_loser_is_restored_before_its_index_is_undone() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let c = r.konst("c");
    let d = r.konst("d");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fc = r.app(f, &[c]);
    r.add(a);
    r.add(c);
    r.add(d);
    r.add(fc);
    assert!(r.merge(c, d).is_none()); // level 0: c's class has size 2

    r.push();
    r.add(fa); // indexed onto a
    assert!(r.merge(a, c).is_none()); // a (size 1) loses to c (size 2)
    assert!(r.equal(fa, fc));
    r.assert_index();

    r.pop(0);
    assert!(!r.equal(fa, fc));
    r.assert_index();

    r.push();
    assert!(r.merge(a, c).is_none());
    assert!(r.equal(fa, fc));
    r.assert_index();
}

/// Spec §4.2 case 4: a `LookupOverwrite` on the app's own signature, recorded
/// after its insert, is undone first, so `AppIndexed`'s undo finds its own
/// entry. Already correct pre-slice; pins the `lookup[sig] == app` debug check.
#[test]
fn lookup_overwrite_after_insert_is_undone_before_the_index() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(fb);

    r.push();
    r.add(fa); // inserts lookup[(f,[a])] = f(a)
    assert!(r.merge(a, b).is_none()); // f(b) re-signs to (f,[a]): overwrite
    assert!(r.equal(fa, fb));
    r.assert_index();

    r.pop(0);
    assert!(!r.equal(fa, fb));
    r.assert_index();

    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(r.equal(fa, fb));
    r.assert_index();
}

/// Spec §4.2 case 5: pop several levels, push again, and flush at the higher
/// level. The flush records `AppIndexed` at that level, so popping below it
/// re-queues the apps; once indexed at level 0 they stay.
#[test]
fn reindex_at_a_higher_level_is_requeued_by_a_lower_pop() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let c = r.konst("c");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(c);

    r.push(); // level 1
    assert!(r.merge(a, b).is_none());
    r.push(); // level 2
    r.add(fb);
    r.add(fa);
    assert!(r.drain(a).is_none());
    assert!(r.equal(fa, fb));
    r.assert_index();

    r.pop(0);
    assert_eq!(r.g.reindex.len(), 2, "both level-2 apps are queued");
    r.assert_index();

    r.push(); // level 1
    r.push(); // level 2
    r.add(c); // already registered: only flushes
    assert!(r.g.reindex.is_empty());
    assert!(!r.equal(fa, fb));
    r.assert_index();

    r.pop(1);
    assert_eq!(r.g.reindex.len(), 2, "indexed at level 2, so popping to 1 re-queues");
    r.assert_index();

    assert!(r.merge(a, b).is_none()); // level 1
    assert!(r.equal(fa, fb));
    r.assert_index();

    r.pop(0);
    assert!(r.merge(a, b).is_none()); // level 0: indexed for good
    assert!(r.equal(fa, fb));
    assert!(r.g.reindex.is_empty());
    r.assert_index();
}

/// Spec §4.2 case 6: `add_term` on an already-registered term whose index is
/// queued. The `seen_terms` guard returns early, but the flush must run first.
#[test]
fn seen_terms_early_return_still_flushes_the_queue() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(fa);

    r.push();
    assert!(r.merge(a, b).is_none());
    r.add(fb); // keyed on a, the level-1 representative

    r.pop(0);
    r.add(fb); // registered: the guard returns early, after the flush
    assert!(
        r.g.reindex.is_empty(),
        "the flush must run before the seen_terms early return"
    );
    r.assert_index();

    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(r.equal(fa, fb));
    r.assert_index();
}

/// Spec §4.2 case 7a: a flush that discovers a congruence only enqueues it;
/// the next drain closes it.
#[test]
fn congruence_found_by_a_flush_is_closed_by_the_next_drain() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(fa);

    r.push(); // level 1
    assert!(r.merge(a, b).is_none());
    r.push(); // level 2
    r.add(fb);
    assert!(r.drain(a).is_none());
    assert!(r.equal(fa, fb));

    r.pop(1); // a = b still holds; f(a) = f(b) was undone with level 2
    assert!(!r.equal(fa, fb));
    r.assert_index();

    r.add(a); // registered: flushes only
    assert!(!r.g.pending.is_empty(), "the flush enqueues the f(a)/f(b) collision");
    assert!(!r.equal(fa, fb), "enqueued, not yet merged");
    r.assert_index();

    assert!(r.drain(a).is_none());
    assert!(r.equal(fa, fb));
    r.assert_index();
}

/// Spec §4.2 case 7b: the same enqueue, then a pop below the level where the
/// arguments were equal. The entry is stale; the guard skips it.
#[test]
fn congruence_found_by_a_flush_goes_stale_across_a_pop() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(fa);

    r.push(); // level 1
    assert!(r.merge(a, b).is_none());
    r.push(); // level 2
    r.add(fb);
    assert!(r.drain(a).is_none());

    r.pop(1);
    r.add(a); // flush at level 1: enqueues f(a)/f(b)
    assert!(!r.g.pending.is_empty());

    r.pop(0); // a != b now: the entry is stale
    assert!(r.drain(a).is_none());
    assert!(!r.equal(fa, fb), "a stale congruence must not merge");
    r.assert_index();
}
```

- [ ] **Step 2: Run them and confirm they are red**

Run: `cargo nextest run -p shinri-euf -E 'test(/survives_backtrack|restored_before|undone_before_the_index|requeued|early_return|flush/)'`

Expected: **compile error** `no field 'reindex' on type 'EGraph'` (cases 5 and 6 read it). That is the red state for this task. Do not add the field yet.

- [ ] **Step 3: Add `AppIndexed`, the debug `moved` field, and `reindex`**

In `crates/shinri-euf/src/egraph.rs`, replace the `Undo` enum (`:23–36`) with:

```rust
/// An undo entry for backtracking the EUF-owned indices.
enum Undo {
    /// `lookup[sig]` was inserted with no prior value; remove it on undo.
    LookupInsert(Signature),
    /// `lookup[sig]` overwrote `prev`; restore `prev` on undo.
    LookupOverwrite(Signature, AppId),
    /// `count` apps were appended onto `use_list[winner]` from `loser`; move
    /// them back to `loser` on undo.
    UseSplice {
        winner: usize,
        loser: usize,
        count: usize,
        /// The spliced apps, in debug builds only (empty in release), so undo
        /// can assert that the tail block it moves back is exactly them
        /// (slice 49, spec §3.2).
        moved: Vec<AppId>,
    },
    /// `index_app` ran above level 0: `app` was pushed onto `use_list[r]` for
    /// each `r` in `reps` (in order) and, if `inserted_sig` is set, installed
    /// as `lookup[sig]`. Undo removes exactly those writes and queues `app` on
    /// `reindex`. Registration (`apps`, `terms`, `seen_terms`) is permanent;
    /// only this index is level-scoped (slice 49, spec §3.1–3.2).
    AppIndexed {
        app: AppId,
        reps: Vec<ENodeId>,
        inserted_sig: Option<Signature>,
    },
}
```

In `pub struct EGraph`, replace the `pending` field's doc comment and declaration (`:51–60`) with:

```rust
    /// Congruence work-queue: pairs of app nodes to merge, with arg pairs.
    ///
    /// INVARIANT (slice 8, cluster C): `drain_pending` is the SOLE consumer, and
    /// it is NOT backtracked on `pop` — it is normally drained to empty each cycle,
    /// but an early conflict-return can leave stale entries whose arg equalities a
    /// later `pop` invalidates. `drain_pending` tolerates that only because it
    /// re-checks arg equality (`eq.find(pa) == eq.find(pb)`) and skips stale
    /// entries. Any NEW consumer of `pending` MUST apply the same staleness check,
    /// or reintroduce the "explain: a,b not connected" unsound-merge bug.
    ///
    /// CONTRACT (slice 49, spec §3.4): `pending` must be drained before every
    /// decision `push`. An entry enqueued at level L but drained at L+1 has its
    /// merge undone by the pop back to L, and the entry is gone, so a congruence
    /// that holds at L would be lost. The SAT loop honours this: it always runs
    /// `propagate()` before `theory.push()`, and `Euf::propagate` calls `close`.
    pending: Vec<PendingEntry>,
```

At the end of `pub struct EGraph`, directly after the `propagated` field, add:

```rust
    /// Apps whose index a `pop` undid (`Undo::AppIndexed`), in undo (LIFO)
    /// order. `flush_reindex` re-indexes them against the current classes at
    /// the next entry point that holds the equality engine; `pop` itself
    /// cannot, because `TheorySolver::pop` has no `TheoryCtx` (slice 49,
    /// spec §3.3).
    reindex: Vec<AppId>,
```

- [ ] **Step 4: Undo the new entries in `pop`**

Replace `pub fn pop` (`:98–123`) with:

```rust
    pub fn pop(&mut self, level: usize) {
        let lookup = &mut self.lookup;
        let use_list = &mut self.use_list;
        let reindex = &mut self.reindex;
        self.undo.pop_to(level, |u| match u {
            Undo::LookupInsert(sig) => {
                lookup.remove(&sig);
            }
            Undo::LookupOverwrite(sig, prev) => {
                lookup.insert(sig, prev);
            }
            Undo::UseSplice {
                winner,
                loser,
                count,
                moved,
            } => {
                debug_assert!(use_list[winner].len() >= count, "use-splice underflow");
                let total = use_list[winner].len();
                let block = use_list[winner].split_off(total - count);
                debug_assert_eq!(
                    block, moved,
                    "use-splice undo: the tail block is not the spliced apps"
                );
                debug_assert!(
                    use_list[loser].is_empty(),
                    "loser use-list not empty on undo"
                );
                use_list[loser] = block;
            }
            Undo::AppIndexed {
                app,
                reps,
                inserted_sig,
            } => {
                for rep in reps.iter().rev() {
                    let popped = use_list[rep.index()].pop();
                    debug_assert_eq!(
                        popped,
                        Some(app),
                        "app-indexed undo: use-list tail is not the app"
                    );
                }
                if let Some(sig) = inserted_sig {
                    let removed = lookup.remove(&sig);
                    debug_assert_eq!(
                        removed,
                        Some(app),
                        "app-indexed undo: lookup entry is not the app"
                    );
                }
                reindex.push(app);
            }
        });
    }
```

The `lookup.remove` and the tail `pop` run in release builds too; only their checks are debug-gated.

- [ ] **Step 5: Extract `index_app`, add `flush_reindex`, and route `add_term` through them**

Replace the whole of `pub fn add_term` (`:135–193`, from its doc comment to its closing brace) with:

```rust
    /// Recursively intern `t` and all subterms, recording app structure.
    /// Returns the e-node of `t`. Idempotent (interning dedups).
    pub fn add_term(&mut self, cx: &mut TheoryCtx, t: TermId) -> ENodeId {
        // Re-index anything a pop un-indexed before touching the index. This
        // runs BEFORE the guard: a queued app must be indexed even when this
        // call returns early (slice 49, spec §3.3).
        self.flush_reindex(cx.eq);
        // Guard: process each distinct TermId exactly once.
        if !self.seen_terms.insert(t) {
            return cx.eq.intern(t);
        }
        let node = cx.eq.intern(t);
        self.terms.push((t, node));
        self.ensure_node(node);
        // Copy out op and args slice before releasing the borrow on cx.terms.
        let term_info = match cx.terms.term_node(t) {
            TermNode::App { op, args, .. } => Some((*op, *args)),
            TermNode::Const { .. } => None,
        };
        match term_info {
            Some((op, args_slice)) => {
                let child_terms: Vec<TermId> = cx.terms.children(args_slice).to_vec();
                let mut arg_nodes = Vec::with_capacity(child_terms.len());
                for ct in child_terms {
                    arg_nodes.push(self.add_term(cx, ct));
                }
                let app_id = self.apps.len() as AppId;
                self.apps.push(AppNode {
                    node,
                    op,
                    args: arg_nodes,
                });
                self.is_app[node.index()] = true;
                self.index_app(cx.eq, app_id);
                node
            }
            None => node,
        }
    }

    /// Index `app` against the CURRENT classes: push it onto the use-list of
    /// each argument's representative, then install its signature or enqueue a
    /// congruence with the app already holding it.
    ///
    /// Keyed by the representative, not the raw argument node. Use-lists live
    /// at class representatives: `recanonicalize_use_list` drains a loser's
    /// list into the winner and its `UseSplice` undo asserts the loser's list
    /// is empty, so pushing onto a raw node that is currently a loser would
    /// panic on undo. Interning a fresh app mid-search (a DT injectivity
    /// selector, a string F-split skolem, an empty-length-link disjunct) is
    /// exactly when that happens.
    ///
    /// The representative is only valid at THIS level, so above level 0 the
    /// writes are logged as one `AppIndexed`. Without that record a pop leaves
    /// the app on a list its argument no longer belongs to, and a later
    /// re-merge never re-signs it: the wrong-`sat` of slice 49 (spec §1.2).
    fn index_app(&mut self, eq: &EqualityEngine, app: AppId) {
        let args = self.apps[app as usize].args.clone();
        let mut reps = Vec::with_capacity(args.len());
        for an in args {
            let rep = eq.find(an);
            self.ensure_node(rep);
            self.use_list[rep.index()].push(app);
            reps.push(rep);
        }
        let sig = self.signature(eq, app);
        let inserted_sig = match self.lookup.get(&sig).copied() {
            Some(other) if other != app => {
                self.enqueue_congruence(eq, other, app);
                None
            }
            Some(_) => None,
            None => {
                self.lookup.insert(sig.clone(), app);
                Some(sig)
            }
        };
        if self.undo.level() > 0 {
            self.undo.record(Undo::AppIndexed {
                app,
                reps,
                inserted_sig,
            });
        }
    }

    /// Re-index every app a `pop` un-indexed, in registration order (`reindex`
    /// holds them in undo order, which is reversed). O(1) when the queue is
    /// empty. A collision found here is only enqueued; the caller's drain, or
    /// the next `close`/`merge_eq`, closes it.
    fn flush_reindex(&mut self, eq: &EqualityEngine) {
        if self.reindex.is_empty() {
            return;
        }
        let queued = std::mem::take(&mut self.reindex);
        for app in queued.into_iter().rev() {
            self.index_app(eq, app);
        }
    }
```

- [ ] **Step 6: Flush at `merge_eq` and `assert_diseq`, and record `moved` in `UseSplice`**

In `pub fn merge_eq` (`:218`), make the first statement of the body:

```rust
        self.flush_reindex(eq);
```

(so the body reads `self.flush_reindex(eq);` then the existing `if let Some(c) = self.do_merge(…)`).

In `pub fn assert_diseq` (`:232`), likewise make the first statement of the body:

```rust
        self.flush_reindex(eq);
```

In `fn recanonicalize_use_list`, replace its last two statements:

```rust
        self.use_list[winner.index()].extend(moved);
        self.undo.record(Undo::UseSplice {
            winner: winner.index(),
            loser: loser.index(),
            count,
        });
```

with:

```rust
        self.use_list[winner.index()].extend(moved.iter().copied());
        self.undo.record(Undo::UseSplice {
            winner: winner.index(),
            loser: loser.index(),
            count,
            moved: if cfg!(debug_assertions) {
                moved
            } else {
                Vec::new()
            },
        });
```

- [ ] **Step 7: Teach `check_index` about the queue**

In `crates/shinri-euf/src/egraph/test_rig.rs`, change the import line `use rustc_hash::FxHashMap;` to:

```rust
use rustc_hash::{FxHashMap, FxHashSet};
```

In `check_index`, directly after the doc comment's `pub(crate) fn check_index(...) -> Result<(), String> {` line, insert:

```rust
        // (I-queue) Apps a pop un-indexed are on no use-list and named by no
        // lookup entry until `flush_reindex` runs.
        let queued: FxHashSet<AppId> = self.reindex.iter().copied().collect();
        for (idx, list) in self.use_list.iter().enumerate() {
            if let Some(app) = list.iter().find(|a| queued.contains(a)) {
                return Err(format!("(I-queue) queued app {app} is still on use_list[{idx}]"));
            }
        }
        if let Some((sig, app)) = self.lookup.iter().find(|(_, a)| queued.contains(a)) {
            return Err(format!("(I-queue) queued app {app} is still lookup[{sig:?}]"));
        }
```

In the per-app loop, make the first statement after `let app = i as AppId;`:

```rust
            if queued.contains(&app) {
                continue;
            }
```

Also add `(I-queue)` to the doc comment's bullet list:

```rust
    /// * (I-queue) no app in `reindex` is on a use-list or named by `lookup`.
```

- [ ] **Step 8: Run the `shinri-euf` suite**

Run: `cargo nextest run -p shinri-euf`

Expected: all green, including:
- Task 1's `midsearch_registration_keeps_congruence_across_backtrack`;
- Task 2's `egraph_matches_reference_closure`;
- all eight Step 1 tests;
- the pre-existing `add_term_registers_apps_and_args` and `stale_pending_congruence_not_drained_after_backtrack`;
- everything in `tests/qfuf_euf.rs` and `tests/euf_props.rs`.

This is a debug build, so every new `debug_assert` is live. If any of them fires, the LIFO argument of spec §3.2 is wrong for that input. Stop and trace it; do not loosen the assertion.

If `egraph_matches_reference_closure` fails, read its minimal trace before touching code. It is either a defect this task has not fixed, or a modelling error in the test. The report must say which, with the trace.

- [ ] **Step 9: Run the e2e pins and the guarded-record oracle**

Run:
```bash
cargo nextest run -p shinri-solver -E 'test(injectivity_over_selector_minted_under_a_case_split_is_unsat) | test(injectivity_over_selector_with_the_equality_as_a_unit_is_unsat)'
cargo nextest run -p shinri-solver --features oracle -E 'test(qfdt_random_guarded_records_match_z3)' --no-capture
```

Expected: both e2e pins pass. The oracle test is expected to pass and print `… 0 mismatches` (confirm 1 test discovered). If it still fails, record the instance. Task 5 must turn it green, or its report must trace the instance to a different, named cause.

- [ ] **Step 10: Commit**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/egraph/test_rig.rs \
        crates/shinri-euf/src/egraph/index_tests.rs
git commit
```

Commit message:
```
fix(euf): slice49 T4 - index mid-search registrations with an undo record

add_term filed new apps under the current representative and installed their
signature with no undo entry, so a pop left them on a use-list their argument
no longer belonged to and a re-merge never re-signed them (wrong sat, spec
1.2). Registration stays permanent; indexing is logged as Undo::AppIndexed,
queued on pop, and re-applied by flush_reindex at the next entry point.

Claude-Session: https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH
```

---

### Task 5: `close` at `Euf::propagate` and `Euf::check`

Spec §3.4. A congruence collision found at registration or re-index time is only enqueued, and only `merge_eq` drains `pending`. If no merge follows, the congruence never closes. This is a separate commit, so its search-trajectory effect can be reviewed and bisected apart from Task 4.

**Files:**
- Modify: `crates/shinri-euf/src/egraph.rs` (add `close`)
- Modify: `crates/shinri-euf/src/solver.rs` (`propagate` `:156`, `check` `:174`, and its test module `:324`)

**Interfaces:**
- Consumes: Task 4's `flush_reindex`; the existing `drain_pending` (`egraph.rs:286`).
- Produces: `pub fn close(&mut self, eq: &mut EqualityEngine) -> Option<Vec<EqLeaf>>` on `EGraph`.

- [ ] **Step 1: Write the failing tests (spec §4.2 case 9)**

In `crates/shinri-euf/src/solver.rs`, inside `mod tests` (after `model_does_not_assign_datatype_sorted_terms`), add:

```rust
    struct RegistrationCollision {
        ctx: shinri_core::Context,
        atoms: shinri_theory::AtomRegistry,
        v_ab: Var,
        v_ff: Var,
    }

    /// Spec §4.2 case 9. Level 1: assert a = b, THEN register the atom
    /// (= f(a) f(b)) (as `bind_fresh` does mid-search) and assert it false.
    /// Registration enqueues the f(a)/f(b) collision and nothing drains it, so
    /// the disequality is accepted.
    fn registration_collision() -> (Euf, shinri_theory::EqualityEngine, RegistrationCollision) {
        use shinri_core::{Context, Op};
        use shinri_theory::types::Owner;
        use shinri_theory::{AtomRegistry, EqualityEngine};

        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        let a_sym = ctx.declare_fun("a", &[], u);
        let a = ctx.mk_app(Op::Uninterpreted(a_sym), &[]).unwrap();
        let b_sym = ctx.declare_fun("b", &[], u);
        let b = ctx.mk_app(Op::Uninterpreted(b_sym), &[]).unwrap();
        let f = ctx.declare_fun("f", &[u], u);
        let fa = ctx.mk_app(Op::Uninterpreted(f), &[a]).unwrap();
        let fb = ctx.mk_app(Op::Uninterpreted(f), &[b]).unwrap();
        let eq_ab = ctx.mk_eq(a, b).unwrap();
        let eq_ff = ctx.mk_eq(fa, fb).unwrap();

        let mut atoms = AtomRegistry::default();
        let (v_ab, v_ff) = (Var::new(0), Var::new(1));
        atoms.register(v_ab, eq_ab, Owner::Euf);
        atoms.register(v_ff, eq_ff, Owner::Euf);

        let mut c = RegistrationCollision {
            ctx,
            atoms,
            v_ab,
            v_ff,
        };
        let mut euf = Euf::default();
        let mut eq = EqualityEngine::default();
        {
            let mut cx = TheoryCtx {
                terms: &mut c.ctx,
                eq: &mut eq,
                atoms: &c.atoms,
            };
            euf.new_var(&mut cx, v_ab, eq_ab);
        }
        eq.push();
        euf.push();
        {
            let mut cx = TheoryCtx {
                terms: &mut c.ctx,
                eq: &mut eq,
                atoms: &c.atoms,
            };
            assert!(euf.assert(&mut cx, Lit::new(v_ab, true)).is_none());
            euf.new_var(&mut cx, v_ff, eq_ff);
            assert!(
                euf.assert(&mut cx, Lit::new(v_ff, false)).is_none(),
                "the disequality is accepted: the collision is still undrained"
            );
        }
        (euf, eq, c)
    }

    fn assert_cites_both(leaves: &[EqLeaf], c: &RegistrationCollision) {
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(c.v_ab, true))),
            "the conflict must cite a = b: {leaves:?}"
        );
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(c.v_ff, false))),
            "the conflict must cite f(a) != f(b): {leaves:?}"
        );
    }

    #[test]
    fn registration_time_collision_is_closed_by_propagate() {
        let (mut euf, mut eq, mut c) = registration_collision();
        let mut cx = TheoryCtx {
            terms: &mut c.ctx,
            eq: &mut eq,
            atoms: &c.atoms,
        };
        let mut out = Vec::new();
        let leaves = euf.propagate(&mut cx, &mut out).expect(
            "a = b forces f(a) = f(b); with f(a) != f(b) asserted, propagate must report the conflict",
        );
        assert_cites_both(&leaves, &c);
    }

    #[test]
    fn registration_time_collision_is_closed_by_check() {
        let (mut euf, mut eq, mut c) = registration_collision();
        let mut cx = TheoryCtx {
            terms: &mut c.ctx,
            eq: &mut eq,
            atoms: &c.atoms,
        };
        match euf.check(&mut cx, Effort::Full) {
            TCheck::Conflict(leaves) => assert_cites_both(&leaves, &c),
            _ => panic!("a = b forces f(a) = f(b); with f(a) != f(b) asserted, check must report the conflict"),
        }
    }
```

- [ ] **Step 2: Run them and confirm they fail**

Run: `cargo nextest run -p shinri-euf -E 'test(/registration_time_collision_is_closed_by/)'`

Expected: 2 tests discovered, both **FAIL**. `…_by_propagate` panics at `expect` ("… propagate must report the conflict"). `…_by_check` panics with "… check must report the conflict". This is the pre-Task-5 behaviour with Task 4 applied, and by reading it is also `main`'s (spec §4.2 case 9). Record both.

- [ ] **Step 3: Add `close`**

In `crates/shinri-euf/src/egraph.rs`, directly after `pub fn assert_diseq`'s closing brace, add:

```rust
    /// Re-index anything a pop un-indexed, then close every pending
    /// congruence. Congruences found at registration (`add_term`) or re-index
    /// (`flush_reindex`) time are only enqueued, and only `merge_eq` drains
    /// otherwise, so without this a collision with no later merge never closes.
    /// Called from `Euf::propagate` and `Euf::check` (slice 49, spec §3.4).
    pub fn close(&mut self, eq: &mut EqualityEngine) -> Option<Vec<EqLeaf>> {
        self.flush_reindex(eq);
        self.drain_pending(eq)
    }
```

- [ ] **Step 4: Call it from `propagate` and `check`**

In `crates/shinri-euf/src/solver.rs`, replace the body of `fn propagate` (`:156–173`) so it reads:

```rust
    fn propagate(
        &mut self,
        cx: &mut TheoryCtx,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        // Close congruences enqueued outside `merge_eq` before scanning for
        // forced equalities. This also upholds `EGraph.pending`'s
        // drain-before-push contract: the SAT loop always propagates before a
        // decision push (slice 49, spec §3.4).
        if let Some(conflict) = self.inner.close(cx.eq) {
            return Some(conflict);
        }
        let props = self.inner.collect_eq_propagations(cx.eq);
        for (vi, tag) in props {
            let lit = Lit::new(Var::new(vi), true);
            out.push((
                lit,
                TheoryJust {
                    theory: Self::THEORY_ID,
                    tag,
                },
            ));
        }
        None
    }
```

Replace `fn check` (`:174–176`) with:

```rust
    fn check(&mut self, cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        // Same closure as `propagate`: a final check must not report
        // consistency over an undrained congruence (slice 49, spec §3.4).
        match self.inner.close(cx.eq) {
            Some(leaves) => TCheck::Conflict(leaves),
            None => TCheck::Sat,
        }
    }
```

The combiner already consumes both results: `combiner.rs:614` maps `TCheck::Conflict` from `euf.check` to `FinalCheck::Conflict`, and `combiner.rs:862` returns `euf.propagate`'s conflict.

- [ ] **Step 5: Run the EUF suite, the e2e pins, and the guarded-record oracle**

Run:
```bash
cargo nextest run -p shinri-euf
cargo nextest run -p shinri-theory
cargo nextest run -p shinri-solver -E 'test(injectivity_over_selector_minted_under_a_case_split_is_unsat) | test(injectivity_over_selector_with_the_equality_as_a_unit_is_unsat)'
cargo nextest run -p shinri-solver --features oracle -E 'test(qfdt_random_guarded_records_match_z3)' --no-capture
```

Expected: all green. The oracle line prints `… 0 mismatches` with 1 test discovered. `shinri-theory` covers the combiner's own tests, which now see `Euf::check` able to return a conflict.

If the guarded-record oracle still fails, trace the quoted instance to a named cause before going further (Global Constraints). Record the trace and the cause in the task report, and stop for a decision. Do not merge a slice whose own generator still disagrees with z3.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/solver.rs
git commit
```

Commit message:
```
fix(euf): slice49 T5 - close pending congruences at propagate and check

Collisions found at registration or re-index time were only enqueued and
only merge_eq drained them. EGraph::close (flush + drain) now runs at
Euf::propagate and Euf::check, which also upholds pending's drain-before-push
contract (spec 3.4).

Claude-Session: https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH
```

---

### Task 6: Gates, push, and PR

**Files:** none modified unless a gate fails.

**Interfaces:**
- Consumes: Tasks 1–5.
- Produces: a pushed branch and an open, CI-green PR for Tasks 7 and 8.

- [ ] **Step 1: Run the fast blocking tier**

Run: `mise run test`

Expected: green, ~5 min. This is the tier CI gates on.

- [ ] **Step 2: Run the FULL unfiltered oracle**

Run:
```bash
cargo nextest run -p shinri-solver --features oracle
```

Expected: green, with a non-zero discovered count; record discovered and passed for the Task 7 report. **Unfiltered on purpose:** this is a shared-core change, and every oracle suite exercises EUF.

- [ ] **Step 3: Run `script_e2e` locally**

Run: `cargo nextest run -p shinri-solver -E 'binary(script_e2e)'`

Expected: green, non-zero discovered count. This slice can **shift completeness**: a query that answered `sat` may now answer `unsat`. A pinned-answer flip that z3 confirms is an adjudicated flip; re-pin it and say so in the commit. A flip z3 does *not* confirm is a bug; stop and diagnose. Remember `test(script_e2e)` finds 0 tests, because `script_e2e` is a binary name.

- [ ] **Step 4: Lint and format**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
```

Expected: no clippy warnings. If `fmt` changed files, commit them:

```bash
git add -u
git commit
```

Commit message:
```
style: slice49 - cargo fmt

Claude-Session: https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH
```

- [ ] **Step 5: Push and open the PR**

```bash
git push -u origin slice49-euf-midsearch-index
gh pr create --base main --title "slice49: EUF congruence lost for terms registered mid-search"
```

PR body:
- the spec's §1.2 mechanism, in three sentences;
- the §1.1 correction of slice 48's root-cause text;
- before/after of the §1 repro;
- evidence that each new test failed first: Tasks 1, 2, 3 and 5 quoted as failing before their fix, and passing now.

End the body with:
```
https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH
```

- [ ] **Step 6: Confirm CI is green**

Run: `gh pr checks --watch`

Do not proceed to Task 8's merge while any check is red. Task 7 can start as soon as the branch builds.

---

### Task 7: Corpus re-run and report

The gate that decides whether this slice delivered anything on the corpus (spec §7). Slice 42 was fully implemented, with green reviews, and delivered zero; only the measured run caught it.

**Files:**
- Create: `docs/superpowers/research/2026-09-11-smtlib-2024-slice49-euf-report.md`
- Modify: `docs/superpowers/specs/2026-09-11-shinri-slice49-euf-midsearch-index-design.md` (append `## 12. Measured outcomes`)

**Interfaces:**
- Consumes: the branch build (`target/release/shinri` at the branch HEAD); the committed runs `bench/results/slice48b/` and `bench/results/baseline-8de004d44944/` (both git-ignored, present locally).
- Produces: the report and the spec's measured-outcomes section, which Task 8 reviews.

Throughout this task, `$SCRATCH` is your session scratch directory. Nothing under it is committed.

- [ ] **Step 1: Build a pre-slice binary for A/B checks**

```bash
BASE=$(git merge-base main slice49-euf-midsearch-index)
git worktree add "$SCRATCH/slice49-base" "$BASE"
(cd "$SCRATCH/slice49-base" && cargo build --release -p shinri-cli)
"$SCRATCH/slice49-base/target/release/shinri" bench/corpus/QF_DT/20230720-blocksworld/blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2 | grep -Ex 'sat|unsat|unknown'
```

Expected: the last command prints `sat`, which is spec §8's pre-slice answer. This binary is the "pre-slice `main`" for criteria 5–7.

- [ ] **Step 2: Run the corpus**

```bash
BENCH_LOGICS=QF_DT,QF_UF,QF_UFLIA,QF_UFLRA,QF_S BENCH_RUN_ID=slice49 mise run bench-run
```

Same limits as the baseline (20 s / 3072 MB / 6 jobs). 37,086 instances (8,700 + 7,503 + 659 + 1,284 + 18,940), the same paths as the comparison runs.

The spec's rough estimate is 2–2.5 h. Do not trust it: slice 47's estimate was off by an order of magnitude because timeouts dominate. Read `wc -l bench/results/slice49/results.jsonl` after ~15 minutes and project from the rate before walking away.

- [ ] **Step 3: Render the report**

```bash
BENCH_RUN_ID=slice49 mise run bench-report
```

This renders `bench/results/slice49/report.md` (git-ignored).

- [ ] **Step 4: Compute the transition matrices**

Save as `$SCRATCH/transitions.py` and run it with `python3 "$SCRATCH/transitions.py"`:

```python
import collections, json

def load(path):
    rows = {}
    with open(path) as f:
        next(f)  # fixture header
        for line in f:
            r = json.loads(line)
            rows[r["path"]] = r
    return rows

new = load("bench/results/slice49/results.jsonl")
old = {p: r for p, r in load("bench/results/baseline-8de004d44944/results.jsonl").items()
       if r["logic"] in {"QF_UF", "QF_UFLIA", "QF_UFLRA", "QF_S"}}
old.update(load("bench/results/slice48b/results.jsonl"))  # QF_DT comparison run

common = set(old) & set(new)
print(f"common {len(common)}  missing {len(set(old) - set(new))}  extra {len(set(new) - set(old))}")

per_logic = collections.defaultdict(lambda: [collections.Counter(), collections.Counter()])
cells = collections.Counter()
families = collections.defaultdict(collections.Counter)
rows = collections.defaultdict(list)
for p in sorted(common):
    a, b, logic = old[p]["verdict"], new[p]["verdict"], new[p]["logic"]
    per_logic[logic][0][a] += 1
    per_logic[logic][1][b] += 1
    if a != b:
        key = (logic, a, b)
        cells[key] += 1
        families[key][p.split("/")[1]] += 1
        rows[key].append((p, old[p]["wall_ms"], new[p]["wall_ms"]))

for logic, (before, after) in sorted(per_logic.items()):
    print(f"\n{logic}\n  before {dict(before)}\n  after  {dict(after)}")
print("\nchanged cells (logic, before, after, count, families):")
for key, n in sorted(cells.items()):
    print(" ", *key, n, dict(families[key]))
print("\nrows needing individual attention (from correct, or into wrong):")
for key, rs in sorted(rows.items()):
    if key[1] == "correct" or key[2] == "wrong":
        print("##", *key)
        for r in rs:
            print("  ", *r)
```

Expected: `common 37086 missing 0 extra 0`. Any missing or extra rows invalidate the same-path comparison; stop and find out why.

- [ ] **Step 5: A/B-time every `correct → {timeout, unknown:*, oom}` row (criteria 5 and 6)**

Write the paths from Step 4's `correct → …` cells (excluding `correct → wrong`) into `$SCRATCH/ab-rows.txt`, one per line. Then:

```bash
while read -r path; do
  for label in base branch; do
    if [ "$label" = base ]; then bin="$SCRATCH/slice49-base/target/release/shinri"; else bin=target/release/shinri; fi
    start=$(date +%s%3N)
    ans=$(timeout 20 prlimit --as=$((3072 * 1024 * 1024)) "$bin" "bench/corpus/$path" 2>/dev/null | grep -Ex 'sat|unsat|unknown' | tail -1)
    echo "$path $label $(( $(date +%s%3N) - start ))ms ${ans:-none}"
  done
done < "$SCRATCH/ab-rows.txt" | tee "$SCRATCH/ab-results.txt"
```

For each row:
- **Boundary noise:** `base` also fails to answer within 20 s on this re-run. It is excluded from criterion 5 and listed.
- **The slice's cost:** `base` answers and `branch` does not. It counts against criterion 5 and is listed under criterion 6.

- [ ] **Step 6: Check every non-`correct → wrong` row against pre-slice `main` (criterion 7)**

For each row in a `… → wrong` cell whose "before" verdict is not `correct`:

```bash
timeout 120 "$SCRATCH/slice49-base/target/release/shinri" "bench/corpus/$path" | grep -Ex 'sat|unsat|unknown'
```

Record whether pre-slice `main`, given 120 s, gives the same wrong answer (a pre-existing wrong answer this slice merely reached faster) or does not (the slice changed the answer; trace it).

- [ ] **Step 7: Write the report**

Create `docs/superpowers/research/2026-09-11-smtlib-2024-slice49-euf-report.md`, following the structure of `2026-09-10-smtlib-2024-qfdt-slice48-report.md`:

1. **Headline.**
2. **Per-logic matrix** copied from `bench/results/slice49/report.md`.
3. **Before/after verdict counts per logic** against spec §7's comparison table.
4. **Transition matrices** (changed cells only, with families), with the closure arithmetic `new = old − outbound + inbound` per logic.
5. **Success criteria**, the table below.
6. **The slice-48 root-cause correction** (spec §1.1): quote §1.2 and the §1.3 evidence.
7. **Oracle and test evidence:** Tasks 1, 2, 3 and 5 failing first, the Task 6 unfiltered-oracle counts.
8. **Queued for the next slice.**

| # | criterion | gate | how to report |
| --- | --- | --- | --- |
| 1 | Tasks 1–3's tests and Task 5's case 9 each failed on pre-slice `main` and pass now | hard | quote each task report's failure and today's pass |
| 2 | §1 repro answers `unsat` | hard | Task 5 Step 5 |
| 2b | `blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` answers `unsat` | measured | the `slice49` row. If still `sat`, trace it to a named cause **before merge** |
| 3 | `correct → wrong`, all five logics | **0**, hard | Step 4 |
| 4 | QF_DT `wrong` ≤ 200 | hard | the actual delta per family; no causal claim for any row without a trace |
| 5 | per-logic `correct` ≥ comparison run | hard | exclude only Step 5's boundary-noise rows, each listed |
| 6 | `correct → {timeout, unknown, oom}` | measured | every row with its Step 5 A/B result |
| 7 | `* → wrong` from a non-`correct` verdict | measured | every row with its Step 6 result |
| 8 | QF_UFLIA 11 and QF_S 2 wrong rows | measured | the numbers, whatever they are |

If a hard criterion is missed, **decompose it rather than relaxing it**, as slice 47's criterion-3 post-mortem did, and stop for a decision before merge.

Queued for the next slice: carry spec §10's list, updated with whatever this run showed. Name any slice-48 residual rows that moved, and which did not.

- [ ] **Step 8: Append measured outcomes to the spec**

Append `## 12. Measured outcomes` to the spec: the criteria table with verdicts, the transitions that actually happened, and any premise this run discarded. If fewer QF_DT wrong rows moved than §1.4's blast radius might suggest, say so plainly; that is a result, not a failure.

- [ ] **Step 9: Commit and push**

```bash
git add docs/superpowers/research/2026-09-11-smtlib-2024-slice49-euf-report.md \
        docs/superpowers/specs/2026-09-11-shinri-slice49-euf-midsearch-index-design.md
git commit
git push
```

Commit message:
```
docs(bench+spec): slice49 - EUF re-run report and measured outcomes

Claude-Session: https://claude.ai/code/session_01ErYvtBRua14fK4hYEJe3sH
```

- [ ] **Step 10: Remove the A/B worktree**

```bash
git worktree remove "$SCRATCH/slice49-base"
```

---

### Task 8: Whole-branch review and merge

An addition to per-task review, not a substitute. Slice 44's whole-branch review caught a Critical that all seven task reviews missed, and it was an identity/keying defect in a soundness path. This slice is exactly that kind of change: which use-list an app lives on, and which `lookup` entry it owns, per level.

**Files:** none unless the review finds something.

- [ ] **Step 1: Review the full branch diff against the spec**

```bash
git diff main...slice49-euf-midsearch-index
```

Review the **whole diff at once**. Hunt specifically for:

1. **An unlogged index write.** `grep -n "use_list\[" crates/shinri-euf/src/egraph.rs` and `grep -n "lookup\.insert\|lookup\.remove" crates/shinri-euf/src/egraph.rs`. Every write must be either logged (`AppIndexed`, `UseSplice`, `LookupInsert`, `LookupOverwrite`) or at level 0, or be an undo action itself. One unlogged write re-opens §1.2.
2. **A read of the index without a flush.** List every public `EGraph` method. Each one that reads or writes `use_list`, `lookup` or `pending` must call `flush_reindex` first, or be reachable only through one that does. `recanonicalize_use_list` and `drain_pending` are private; confirm every caller flushes.
3. **The LIFO argument by hand.** Walk the undo log for: an app indexed at level 2 whose representative loses a merge at level 3, then `pop(1)`; a duplicate-argument app whose representative wins a merge at the same level; a flush at level 3 after `pop(0)`, then `pop(2)`. Confirm every `debug_assert` in `pop` holds.
4. **Release-mode behaviour.** Every `debug_assert` in `pop` must be side-effect free. `lookup.remove` and the use-list `pop` must run in release. `UseSplice.moved` must be empty in release (`cfg!(debug_assertions)`), so no hot-path allocation is added.
5. **`check_index` permissiveness.** The pending-link clause of (I-lookup) could hide a real miss. Confirm it only links **non-stale** entries, and that the property test compares against the reference only after a drain that returned no conflict.
6. **`Euf::check` returning a conflict.** No caller may still assume `Sat`. `grep -rn "euf.check\|Euf::check" crates` must find only `combiner.rs:614`, which handles `Conflict`.
7. **The drain-before-push contract.** Confirm no production path calls `theory.push()` between a registration and the next `propagate`: `shinri-sat/src/solver.rs` search loop `:537–635`. Any path found is a Critical.
8. **The spec §10 queue** still holds: `combiner.rs:185` is untouched and still unverified.

- [ ] **Step 2: Verify any "unreachable" or "blocked" claim by direct repro**

If the review concludes a path is unreachable or a finding is not real, do not accept it on a read. Construct the state with `Rig` and run it. A read-found conclusion is not a diagnosis until a named reproducer traces to it.

- [ ] **Step 3: Fix findings, re-run the gates, and merge on green**

Any fix repeats Task 6's gates: `mise run test`, the full unfiltered `--features oracle` run, `script_e2e`, `cargo fmt --all`, and `mise run lint`. A fix that touches `egraph.rs` also re-runs Task 7 Step 4's transition check on QF_DT at minimum (`BENCH_LOGICS=QF_DT BENCH_RUN_ID=slice49-fix mise run bench-run`) and appends the result to the report.

Then, once CI is green and every hard criterion in Task 7 is met:

```bash
gh pr merge --merge
git checkout main && git pull
git branch -d slice49-euf-midsearch-index
git push origin --delete slice49-euf-midsearch-index
git remote prune origin
```

- [ ] **Step 4: Confirm the queue is recorded**

The merged report's "Queued for the next slice" section records at least:
- `combiner.rs:185`'s `Owner::Shared` definitional merge bypassing EUF (unverified; needs a repro above level 0);
- `pending` not backtracked, safe only by contract (spec §10);
- slice 48's residual QF_DT wrong rows that did not move, named by family;
- rank 3 of the slice-46 queue (the 55 small wrong-answer clusters, including the QF_S wrong `unsat`), then the `blast_word` panic bucket.
