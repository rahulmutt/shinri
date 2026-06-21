# QF_LIA Plan B1 Implementation Plan (baseline: a-priori bounds + branch-and-bound, cuts OFF)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `shinri-arith` decide **pure QF_LIA** soundly, completely, and terminatingly using only the a-priori finite bound + splitting-on-demand branch-and-bound (no Gomory cuts) — the known-correct Stage-A reference for Plan B2.

**Architecture:** The existing QF_LRA Dutertre–de Moura simplex solves the real relaxation unchanged. An additive integer layer runs *after* `check_full` reports the relaxation feasible: it scans Int problem vars for a non-integral value and, if found, builds a branch clause `(x ≤ ⌊v⌋) ∨ (x ≥ ⌈v⌉)` over freshly-minted atoms and returns `TCheck::Split` (the Plan A seam). Termination rests on an a-priori box `−M ≤ x ≤ M` seeded as level-0 bounds. Integer support is fenced off until the whole machinery is in place, then flipped on atomically (Task 7), so every intermediate commit stays sound.

**Tech Stack:** Rust 2021, `cargo test`, the `shinri-arith` simplex, `shinri-theory` Nelson–Oppen `Combiner`, `shinri-sat` DPLL(T), `shinri-num` bigint/rational, `easy-smt` (oracle, dev-only).

## Global Constraints

- `edition = "2021"`, `rust-version = "1.96.0"` (workspace floor — do not raise).
- Only `shinri-num` on any arithmetic shipping path; `num-bigint`/`num-rational`/`easy-smt` are dev-only oracle deps.
- The atom space is **append-only across a solve** — fresh branch atoms minted mid-search are *never* un-registered on backtrack (mirrors `AtomRegistry`).
- `TCheck::Split` payloads are theory-valid split clauses ONLY. `EmptyTheory`/`Euf` stay on the Sat/Conflict path.
- **Soundness ordering invariant:** the Int-sort fence is narrowed (integer queries reach `Arith`) ONLY in Task 7, after branching (Task 5), the a-priori box (Task 4), and Int diseq lowering (Task 6) all exist. Tasks 3–6 are exercised by direct `Arith` unit tests while integer queries are still fenced to `unknown`.
- Run `cargo test --workspace` after every task. Format before every commit: `cargo fmt`.
- Reference design spec: `docs/superpowers/specs/2026-06-21-shinri-lia-planB1-design.md`. Master design: `docs/superpowers/specs/2026-06-20-shinri-arith-lia-design.md`.

---

## File Structure

| File | Responsibility | Change |
|---|---|---|
| `crates/shinri-solver/src/lib.rs` | Public `Solver` API + `lower()` + query gate | Add `int_sort()`; extend `lower()` to Int Eq/Distinct; LIRA query gate |
| `crates/shinri-theory/src/solver_trait.rs` | `TheoryCtx` | `terms: &Context` → `&mut Context` |
| `crates/shinri-theory/src/combiner.rs` | Nelson–Oppen driver | Update all `TheoryCtx` construction sites to `&mut self.terms` |
| `crates/shinri-theory/src/atom.rs` | `classify` | Admit pure-Int arith (narrow the Int fence) |
| `crates/shinri-solver/src/tseitin.rs` | `Encoder` | Track `saw_int_arith`/`saw_real_arith` |
| `crates/shinri-arith/src/vars.rs` | `VarStore` | Track Int-sortedness per `ArithVar` |
| `crates/shinri-arith/src/bounds.rs` | bound storage | (reused as-is; new code lives in `lib.rs`) |
| `crates/shinri-arith/src/branch.rs` *(new)* | branch-var selection + floor/ceil + `Split` clause | new module |
| `crates/shinri-arith/src/lib.rs` | `Arith` theory | Int tracking, a-priori box, integer layer in `check` |
| `crates/shinri-solver/tests/oracle.rs` | differential oracle | QF_LIA generator + cvc5 backend |

`normalize.rs` / `build_encoding` are **deliberately untouched** — they are sort-blind and already handle Int atoms as rationals; the existing `Rel::Lt → (rhs, −δ)` encoding carries integer strictness (spec §3.5 reversal).

---

### Task 1: Public `Solver::int_sort()`

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (next to `real_sort`, ~line 69)
- Test: `crates/shinri-solver/src/lib.rs` (inline `#[cfg(test)]`) or `crates/shinri-solver/tests/` — match where `real_sort` is tested

**Interfaces:**
- Consumes: `shinri_core::Context::int_sort(&self) -> SortId` (exists).
- Produces: `Solver::int_sort(&self) -> shinri_core::SortId` — used by Tasks 4/7/8 tests and the oracle to declare Int constants.

- [ ] **Step 1: Write the failing test**

In a `#[cfg(test)]` block reachable from `shinri-solver` (mirror how `real_sort` is exercised; if none, add this inline in `lib.rs`):

```rust
#[test]
fn int_sort_is_exposed_and_distinct_from_real() {
    let s = Solver::new();
    assert_ne!(s.int_sort(), s.real_sort());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver int_sort_is_exposed_and_distinct_from_real`
Expected: FAIL to compile — `no method named int_sort`.

- [ ] **Step 3: Add the accessor**

In `crates/shinri-solver/src/lib.rs`, directly after the existing `real_sort`:

```rust
    pub fn int_sort(&self) -> SortId {
        self.ctx.int_sort()
    }
```

(`SortId` is already in scope where `real_sort` returns it; if not, add `use shinri_core::SortId;`.)

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-solver int_sort_is_exposed_and_distinct_from_real`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
cargo fmt -p shinri-solver
git add crates/shinri-solver/src/lib.rs
git commit -m "feat(solver): expose Solver::int_sort() public accessor"
```

---

### Task 2: `TheoryCtx.terms: &mut Context` seam

**Files:**
- Modify: `crates/shinri-theory/src/solver_trait.rs:14-18` (`TheoryCtx` struct)
- Modify: `crates/shinri-theory/src/combiner.rs` (15 `TheoryCtx { terms: &self.terms, .. }` sites)
- Test: the existing workspace suite (mechanical refactor, no behavior change)

**Interfaces:**
- Produces: `TheoryCtx.terms: &'a mut Context` — lets `Arith::check` build branch-atom `TermId`s via `cx.terms.mk_app(..)`/`mk_numeral(..)` (Task 5).
- Consumes: nothing new. Sub-theory methods that read `cx.terms` as `&Context` keep compiling (Rust reborrows `&mut Context` → `&Context` at call sites).

This is an enabling refactor with no new behavior, so the "test" is that the full suite still builds and passes.

- [ ] **Step 1: Change the field type**

In `crates/shinri-theory/src/solver_trait.rs`:

```rust
pub struct TheoryCtx<'a> {
    pub terms: &'a mut Context,
    pub eq: &'a mut EqualityEngine,
    pub atoms: &'a AtomRegistry,
}
```

- [ ] **Step 2: Run the build to enumerate the breaks**

Run: `cargo build -p shinri-theory`
Expected: FAIL — every `TheoryCtx { terms: &self.terms, .. }` now mismatches (`expected &mut Context, found &Context`). There are 15 sites in `combiner.rs` (lines approx 73, 81, 106, 132, 193, 239, 255, 281, 289, 318, 344, 389, 463, 472, 497).

- [ ] **Step 3: Update every construction site**

In `crates/shinri-theory/src/combiner.rs`, change each `terms: &self.terms,` to `terms: &mut self.terms,`. Use a global replace of the exact line `        terms: &self.terms,` → `        terms: &mut self.terms,` and verify the count is 15.

Note the one ordering constraint: in `register_atom`'s `Owner::Shared` arm, `crate::interface::purify(&mut self.terms, &mut self.iface, atom)` (≈line 97) takes `&mut self.terms` and must remain **before** the subsequent `TheoryCtx` is constructed (it already is — purify's borrow ends at its statement). No reordering needed.

If a `let cx = TheoryCtx {..}` site (the EUF→arith grouping read, ≈line 318) is bound immutably but a callee needs `&mut cx`, change it to `let mut cx`. Let the compiler guide this.

- [ ] **Step 4: Build the whole workspace green**

Run: `cargo build --workspace`
Expected: PASS. If `shinri-arith`'s `Arith::new_var`/`build_model` (which call `normalize_atom(cx.terms, ..)` expecting `&Context`) error, insert an explicit reborrow `&*cx.terms` at those call sites — but the implicit `&mut → &` coercion should make this unnecessary.

Run: `cargo test --workspace`
Expected: PASS — no behavior changed; all existing tests stay green.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-theory/src/solver_trait.rs crates/shinri-theory/src/combiner.rs
git commit -m "refactor(theory): TheoryCtx.terms becomes &mut Context (enables mid-search atom minting)"
```

---

### Task 3: Track Int-sortedness per `ArithVar`

**Files:**
- Modify: `crates/shinri-arith/src/vars.rs` (`VarStore`)
- Modify: `crates/shinri-arith/src/lib.rs` (`Arith::new_var` records the sort)
- Test: `crates/shinri-arith/src/vars.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Produces:
  - `VarStore::problem_var_sorted(&mut self, t: TermId, is_int: bool) -> ArithVar` — interns a problem var and records its integer-ness.
  - `VarStore::is_int(&self, v: ArithVar) -> bool` — true iff `v` is an Int-sorted **problem** var (slacks and Real vars → false).
- Consumes: `shinri_core::Context::{int_sort, sort_of}` in `Arith::new_var`.

- [ ] **Step 1: Write the failing test**

In `crates/shinri-arith/src/vars.rs` `#[cfg(test)] mod tests`:

```rust
#[test]
fn problem_var_records_int_sortedness() {
    let mut s = VarStore::default();
    let ti = TermId::new(1).unwrap();
    let tr = TermId::new(2).unwrap();
    let xi = s.problem_var_sorted(ti, true);
    let xr = s.problem_var_sorted(tr, false);
    assert!(s.is_int(xi));
    assert!(!s.is_int(xr));
    // Re-interning the same term returns the same var, keeps its flag.
    assert_eq!(s.problem_var_sorted(ti, true), xi);
    assert!(s.is_int(xi));
    // Slacks are never int.
    let comb = LinComb(vec![(xi, Rational::one()), (xr, Rational::one())]);
    let sl = s.slack_var(&comb);
    assert!(!s.is_int(sl));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-arith problem_var_records_int_sortedness`
Expected: FAIL to compile — `no method named problem_var_sorted`/`is_int`.

- [ ] **Step 3: Implement the tracking**

In `crates/shinri-arith/src/vars.rs`, add an `is_int: Vec<bool>` field parallel to `is_slack`:

```rust
#[derive(Default, Debug)]
pub struct VarStore {
    by_term: FxHashMap<TermId, ArithVar>,
    by_comb: FxHashMap<LinComb, ArithVar>,
    term_of: Vec<Option<TermId>>,
    is_slack: Vec<bool>,
    is_int: Vec<bool>,
}
```

Update `fresh` to push the new column, and add the sorted interner + accessor:

```rust
    fn fresh(&mut self, term: Option<TermId>, slack: bool, is_int: bool) -> ArithVar {
        let v = ArithVar(self.term_of.len() as u32);
        self.term_of.push(term);
        self.is_slack.push(slack);
        self.is_int.push(is_int);
        v
    }

    pub fn problem_var_sorted(&mut self, t: TermId, is_int: bool) -> ArithVar {
        if let Some(&v) = self.by_term.get(&t) {
            return v;
        }
        let v = self.fresh(Some(t), false, is_int);
        self.by_term.insert(t, v);
        v
    }

    #[inline]
    pub fn is_int(&self, v: ArithVar) -> bool {
        self.is_int[v.index()]
    }
```

Update the existing `problem_var` and `slack_var` to call the new `fresh` signature: `problem_var` → `self.fresh(Some(t), false, false)`; `slack_var` → `self.fresh(None, true, false)`. (Keep `problem_var` as the Real-path entry point; it interns with `is_int=false`.)

- [ ] **Step 4: Wire `Arith::new_var` to record the sort**

In `crates/shinri-arith/src/lib.rs` `normalize.rs` is sort-blind, so record the flag at registration. In `Arith::new_var` (≈line 587), the atom's operands carry the sort. Replace the body's interning so problem vars get their integer-ness. The simplest correct hook: in `normalize_atom`, problem vars are interned via `vars.problem_var(t)`. To avoid threading sort into `normalize`, do a post-pass in `new_var`: after `let n = normalize_atom(cx.terms, &mut self.vars, atom);`, re-stamp each problem var in `n.comb` with its sort:

```rust
    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId) {
        let n = normalize_atom(cx.terms, &mut self.vars, atom);
        // Stamp Int-sortedness on each problem var this atom interned, so the
        // integer layer (Task 5) and the a-priori box (Task 4) know which vars
        // must be integral. normalize.rs is sort-blind; we read the sort here.
        let int_s = cx.terms.int_sort();
        for (av, _) in &n.comb.0 {
            if let Some(t) = self.vars.term_of(*av) {
                if cx.terms.sort_of(t) == int_s {
                    self.vars.mark_int(*av);
                }
            }
        }
        let enc = self.build_encoding(&n);
        let idx = v.index();
        if idx >= self.enc.len() {
            self.enc.resize_with(idx + 1, || None);
        }
        self.enc[idx] = Some(enc);
        self.grow_value();
    }
```

Add `mark_int` to `VarStore` (idempotent set):

```rust
    pub fn mark_int(&mut self, v: ArithVar) {
        self.is_int[v.index()] = true;
    }
```

> NOTE: `problem_var_sorted` from Step 3 is the clean interface; `mark_int` is used here because `normalize_atom` interns via the existing `problem_var` before `new_var` sees the comb. Both are kept: `problem_var_sorted` is unit-tested in Step 1; `mark_int` is the post-pass stamp. The Step-1 test still validates the storage column.

- [ ] **Step 5: Run tests + commit**

Run: `cargo test -p shinri-arith`
Expected: PASS (new test + all existing).

```bash
cargo fmt -p shinri-arith
git add crates/shinri-arith/src/vars.rs crates/shinri-arith/src/lib.rs
git commit -m "feat(arith): track Int-sortedness per problem ArithVar"
```

---

### Task 4: A-priori finite box `−M ≤ x ≤ M`

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (`Arith` fields, `new_var` coeff tracking, `check`)
- Test: `crates/shinri-arith/src/lib.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Produces:
  - `Arith::apriori_bound(&self) -> shinri_num::Integer` — the box magnitude `M` (a dominating small-model bound).
  - `Arith::seed_apriori_if_needed(&mut self)` — installs `−M ≤ x ≤ M` on every Int problem var once, at level 0, under fresh sentinel lits.
  - `Arith::strip_apriori(&self, leaves: Vec<EqLeaf>) -> Vec<EqLeaf>` — drops a-priori sentinel lits from a conflict core.
- Consumes: `VarStore::is_int` (Task 3), the existing `fresh_sentinel`, `bounds.tighten`, `DeltaRational`, `shinri_num::{Integer, Rational}`.

**Soundness note (why dropping a-priori sentinels from a conflict is sound).** `M` is computed from the magnitudes of *all* registered coefficients/constants, so it dominates the small-model bound of every *subset* of constraints. A `check_full` (real-relaxation) conflict that cites the box means the asserted input lits `L` are real-infeasible within the box. If `L` were integer-feasible, the small-model property gives an integer (hence real) witness within the box of `L`'s coefficients ⊆ the box of `M` — contradiction. Hence `L` is integer-unsat and the learned clause `¬L` is valid. The box lits are therefore safely droppable from the core. (Full argument: spec §3.3 + master spec §1.1.)

- [ ] **Step 1: Write the failing test**

In `crates/shinri-arith/src/lib.rs` `#[cfg(test)]` (these tests construct `Arith` directly and access private fields — the module's own tests can). Use the existing test harness helpers for building a `Context` + `TheoryCtx`; mirror an existing arith test that calls `arith.check(&mut cx, Effort::Full)`. Build an **Int** atom so `is_int` is set:

```rust
#[test]
fn apriori_box_seeded_on_int_vars_at_level_zero() {
    use shinri_theory::Effort;
    let mut ctx = Context::new();
    let int = ctx.int_sort();
    let xi = ctx.declare_fun("xi", &[], int);
    let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
    let three = ctx.mk_numeral(Rational::from_int(3i128.into()), int);
    let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, three]).unwrap();

    let mut arith = Arith::default();
    let mut eq = shinri_theory::eq_engine::EqualityEngine::default();
    let atoms = shinri_theory::AtomRegistry::default();
    let v = Var::new(0);
    {
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        arith.new_var(&mut cx, v, le);
        // First Full check at level 0 seeds the box.
        let _ = arith.check(&mut cx, Effort::Full);
    }
    let xv = arith.vars.problem_var(x); // already interned by new_var
    let m = arith.apriori_bound();
    let lo = arith.bounds.lower(xv).expect("lower box seeded").0.c().clone();
    let hi = arith.bounds.upper(xv).expect("upper box seeded").0.c().clone();
    assert_eq!(hi, Rational::from_int(m.clone()));
    assert_eq!(lo, Rational::from_int(-m));
}
```

> NOTE: adapt `EqualityEngine`/`AtomRegistry`/`TheoryCtx` construction to the exact paths the other arith tests use (read the existing `#[cfg(test)]` harness in `lib.rs`; it already builds a `cx`). The assertion targets are the seeded box values.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-arith apriori_box_seeded_on_int_vars_at_level_zero`
Expected: FAIL — `no method named apriori_bound`/`seed_apriori_if_needed`; box not seeded.

- [ ] **Step 3: Add fields + coeff tracking**

Add to the `Arith` struct (`lib.rs` ≈line 36):

```rust
    /// Max |coefficient| and |constant| over all registered atoms — the input
    /// magnitude `a` feeding the a-priori bound `M`. Updated in `new_var`.
    apriori_coeff_max: Integer,
    /// Count of registered arith atoms — the constraint count `m` feeding `M`.
    apriori_atom_count: usize,
    /// One-shot guard: the a-priori box is seeded at the first level-0 Full check.
    apriori_seeded: bool,
    /// Sentinel lit codes used for a-priori box bounds, stripped from conflicts.
    apriori_lits: rustc_hash::FxHashSet<u32>,
```

`Integer` does not impl `Default` as zero via `#[derive(Default)]` on the struct? It does via `Integer::zero()` only. Since `Arith` derives `Default`, ensure `Integer: Default`. If `Integer` lacks `Default`, replace the struct-level `#[derive(Default)]` with a manual `Default` impl, OR initialize `apriori_coeff_max` lazily. Simplest: keep `#[derive(Default)]` and confirm `shinri_num::Integer` derives `Default` (it is `Repr::Small(0)` by default). If it does not, add a manual `impl Default for Arith` mirroring `#[derive(Default)]` but with `apriori_coeff_max: Integer::zero()`.

In `new_var`, after computing `n`, accumulate magnitudes (this also runs for Real atoms — harmless, the box is only *seeded* on Int vars):

```rust
        self.apriori_atom_count += 1;
        for (_, coeff) in &n.comb.0 {
            let mag = coeff.numer().abs();
            if mag > self.apriori_coeff_max { self.apriori_coeff_max = mag; }
            let dmag = coeff.denom().abs();
            if dmag > self.apriori_coeff_max { self.apriori_coeff_max = dmag; }
        }
        let rmag = n.rhs.numer().abs();
        if rmag > self.apriori_coeff_max { self.apriori_coeff_max = rmag; }
```

- [ ] **Step 4: Implement `apriori_bound`, `seed_apriori_if_needed`, `strip_apriori`, and wire `check`**

Add methods to `impl Arith`:

```rust
    /// A dominating small-model bound (Papadimitriou 1981). Generously
    /// over-approximated: `M = (n+1) * ((m+1)*(a+1))^(2*(m+1))` where n = #Int
    /// problem vars, m = #atoms, a = max |coeff/const|. Larger is always sound
    /// (only slower); only a too-small M could be unsound, so we over-shoot.
    fn apriori_bound(&self) -> Integer {
        let n_int = (0..self.vars.len())
            .filter(|&i| {
                let v = ArithVar(i as u32);
                !self.vars.is_slack(v) && self.vars.is_int(v)
            })
            .count();
        let n = Integer::from(n_int as i128);
        let m = Integer::from(self.apriori_atom_count as i128);
        let a = self.apriori_coeff_max.clone();
        let one = Integer::one();
        let base = (m.clone() + one.clone()) * (a + one.clone()); // (m+1)*(a+1)
        // exponent = 2*(m+1)
        let exp_int = (self.apriori_atom_count + 1) * 2;
        let mut pow = Integer::one();
        for _ in 0..exp_int {
            pow = pow * base.clone();
        }
        (n + one) * pow
    }

    /// Seed `−M ≤ x ≤ M` on every Int problem var, once, at level 0. Bounds ride
    /// under fresh sentinel lits (stripped from conflicts by `strip_apriori`).
    fn seed_apriori_if_needed(&mut self) {
        if self.apriori_seeded {
            return;
        }
        debug_assert_eq!(self.level, 0, "a-priori box must seed at decision level 0");
        self.apriori_seeded = true;
        let m = self.apriori_bound();
        let hi = DeltaRational::from_rational(Rational::from_int(m.clone()));
        let lo = DeltaRational::from_rational(Rational::from_int(-m));
        for i in 0..self.vars.len() {
            let v = ArithVar(i as u32);
            if self.vars.is_slack(v) || !self.vars.is_int(v) {
                continue;
            }
            let lo_lit = self.fresh_sentinel();
            let hi_lit = self.fresh_sentinel();
            self.apriori_lits.insert(lo_lit.code());
            self.apriori_lits.insert(hi_lit.code());
            let _ = self.apply_bound(v, BoundKind::Lower, lo.clone(), lo_lit);
            let _ = self.apply_bound(v, BoundKind::Upper, hi.clone(), hi_lit);
        }
    }

    /// Drop a-priori box sentinel lits from a conflict core (see Soundness note).
    fn strip_apriori(&self, leaves: Vec<EqLeaf>) -> Vec<EqLeaf> {
        leaves
            .into_iter()
            .filter(|leaf| !matches!(leaf, EqLeaf::Asserted(l) if self.apriori_lits.contains(&l.code())))
            .collect()
    }
```

Modify the `TheorySolver::check` impl (≈line 625) so the box is seeded before the relaxation check and box sentinels are stripped from conflicts:

```rust
    fn check(&mut self, _cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        self.seed_apriori_if_needed();
        match self.check_full() {
            TCheck::Conflict(leaves) => TCheck::Conflict(self.strip_apriori(leaves)),
            TCheck::Split(_) => unreachable!("check_full never emits Split"),
            TCheck::Sat => TCheck::Sat,
        }
    }
```

(The integer layer is added to this method in Task 5.)

- [ ] **Step 5: Run tests + commit**

Run: `cargo test -p shinri-arith`
Expected: PASS (new test + all existing; pure-Real queries seed nothing because no Int vars).

Run: `cargo test --workspace`
Expected: PASS.

```bash
cargo fmt -p shinri-arith
git add crates/shinri-arith/src/lib.rs
git commit -m "feat(arith): a-priori finite box seeded as level-0 bounds (termination backstop)"
```

---

### Task 5: Integer layer — fractional scan + `branch.rs` + `TCheck::Split`

**Files:**
- Create: `crates/shinri-arith/src/branch.rs`
- Modify: `crates/shinri-arith/src/lib.rs` (`pub mod branch;`, the integer layer in `check`)
- Test: `crates/shinri-arith/src/branch.rs` (floor/ceil unit) + `crates/shinri-arith/src/lib.rs` (integer-layer integration)

**Interfaces:**
- Produces:
  - `branch::floor_ceil(value: &DeltaRational) -> (Integer, Integer)` — integer floor/ceil of a δ-value (handles the δ-component sign).
  - `Arith::integer_check(&mut self, cx: &mut TheoryCtx) -> TCheck` — after the relaxation is feasible, returns `Sat` if all Int problem vars are integral, else `TCheck::Split([le, ge])` with freshly-built branch atoms.
- Consumes: `VarStore::{is_int, is_slack, term_of}`, `self.value`, `cx.terms.{int_sort, mk_numeral, mk_app}`, `shinri_num::{Integer, Rational, DeltaRational}`, `shinri_core::{Op, BuiltinOp}`.

- [ ] **Step 1: Write the failing tests**

(a) `branch.rs` floor/ceil unit test — create `crates/shinri-arith/src/branch.rs` with only its test first will not compile; instead put the test alongside the impl skeleton. Write the test in the new file's `#[cfg(test)]`:

```rust
#[cfg(test)]
mod tests {
    use super::floor_ceil;
    use shinri_num::{DeltaRational, Integer, Rational};

    fn r(n: i128, d: i128) -> Rational {
        Rational::new(Integer::from(n), Integer::from(d))
    }

    #[test]
    fn floor_ceil_handles_fractions_and_delta() {
        // 5/2 → (2, 3)
        let v = DeltaRational::from_rational(r(5, 2));
        assert_eq!(floor_ceil(&v), (Integer::from(2i128), Integer::from(3i128)));
        // integer 5 with +δ → (5, 6)
        let v = DeltaRational::new(Rational::from_int(5i128.into()), Rational::one());
        assert_eq!(floor_ceil(&v), (Integer::from(5i128), Integer::from(6i128)));
        // integer 5 with −δ → (4, 5)
        let v = DeltaRational::new(Rational::from_int(5i128.into()), -Rational::one());
        assert_eq!(floor_ceil(&v), (Integer::from(4i128), Integer::from(5i128)));
        // −5/2 → (−3, −2)
        let v = DeltaRational::from_rational(r(-5, 2));
        assert_eq!(floor_ceil(&v), (Integer::from(-3i128), Integer::from(-2i128)));
    }
}
```

(b) Integer-layer integration test in `lib.rs` `#[cfg(test)]`: assert a fractional Int var triggers `Split` with two atoms. Build `(2x = 1)`-style via a single Int atom forcing a fractional relaxation — e.g. assert `2x ≥ 1` and `2x ≤ 1` so the relaxation pins `x = 1/2`:

```rust
#[test]
fn fractional_int_var_triggers_split() {
    use shinri_theory::Effort;
    let mut ctx = Context::new();
    let int = ctx.int_sort();
    let xi = ctx.declare_fun("xi", &[], int);
    let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
    let two = ctx.mk_numeral(Rational::from_int(2i128.into()), int);
    let one = ctx.mk_numeral(Rational::one(), int);
    let twox = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
    let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[twox, one]).unwrap();
    let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[twox, one]).unwrap();

    let mut arith = Arith::default();
    let mut eq = shinri_theory::eq_engine::EqualityEngine::default();
    let atoms = shinri_theory::AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
    arith.new_var(&mut cx, Var::new(0), ge);
    arith.new_var(&mut cx, Var::new(1), le);
    // Assert both so the relaxation pins x = 1/2.
    let _ = arith.assert(&mut cx, Lit::new(Var::new(0), true));
    let _ = arith.assert(&mut cx, Lit::new(Var::new(1), true));
    match arith.check(&mut cx, Effort::Full) {
        TCheck::Split(atoms) => assert_eq!(atoms.len(), 2),
        other => panic!("expected Split on fractional x, got {other:?}"),
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-arith floor_ceil_handles_fractions_and_delta fractional_int_var_triggers_split`
Expected: FAIL — `branch` module / `floor_ceil` / integer layer absent.

- [ ] **Step 3: Implement `branch.rs`**

Create `crates/shinri-arith/src/branch.rs`:

```rust
//! Branch-and-bound support: integer floor/ceil of a δ-value, used to build the
//! split clause `(x ≤ ⌊v⌋) ∨ (x ≥ ⌈v⌉)` for a fractional Int problem var.

use shinri_num::{DeltaRational, Integer, Rational};

/// Integer floor/ceil of `c + k·δ`. δ is a positive infinitesimal, so when `c`
/// is itself an integer the result depends on the sign of `k`.
pub fn floor_ceil(value: &DeltaRational) -> (Integer, Integer) {
    let c = value.c();
    let k = value.k();
    let f = floor_rational(c);
    if &Rational::from_int(f.clone()) == c {
        // c is an exact integer; δ breaks the tie.
        if !k.is_zero() && !k.is_negative() {
            // c + (positive δ): floor = c, ceil = c+1
            (f.clone(), f + Integer::one())
        } else if k.is_negative() {
            // c − δ: floor = c−1, ceil = c
            (f.clone() - Integer::one(), f)
        } else {
            // exact integer (k == 0): floor == ceil == c
            (f.clone(), f)
        }
    } else {
        // c non-integer: |kδ| < distance to nearest integer, so δ is irrelevant.
        (f.clone(), f + Integer::one())
    }
}

/// `⌊n/d⌋` for a Rational `n/d` (d > 0 in canonical form). Uses truncating
/// `div_rem` and corrects toward −∞ for negative non-exact values.
fn floor_rational(r: &Rational) -> Integer {
    let n = r.numer();
    let d = r.denom();
    let (q, rem) = n.div_rem(&d);
    if rem.is_zero() || !n.is_negative() {
        q
    } else {
        // n negative, non-exact: truncation rounded toward zero ⇒ subtract 1.
        q - Integer::one()
    }
}
```

> NOTE: `Rational` canonical form keeps `denom > 0` (confirmed: `numer`/`denom` derive from `Repr`), so `floor_rational` only needs the numerator-sign correction. If a build surfaces a negative denom, normalize first — but the existing `Rational::new` canonicalizes sign into the numerator.

- [ ] **Step 4: Implement the integer layer in `lib.rs`**

Add `pub mod branch;` near the other `pub mod` lines (≈line 6).

Add `integer_check` to `impl Arith`:

```rust
    /// After the real relaxation is feasible (`check_full` Sat), scan Int problem
    /// vars for a non-integral value. All integral ⇒ Sat. Otherwise pick the
    /// most-fractional var (ties by smallest ArithVar index = Bland order) and
    /// return `Split` on `(x ≤ ⌊v⌋) ∨ (x ≥ ⌈v⌉)`, building the atoms via cx.terms.
    fn integer_check(&mut self, cx: &mut TheoryCtx) -> TCheck {
        let mut best: Option<(ArithVar, Rational)> = None; // (var, fractional distance)
        for i in 0..self.vars.len() {
            let v = ArithVar(i as u32);
            if self.vars.is_slack(v) || !self.vars.is_int(v) {
                continue;
            }
            let val = &self.value[v.index()];
            let integral = val.k().is_zero()
                && val.c().denom() == shinri_num::Integer::one();
            if integral {
                continue;
            }
            // Fractional distance to the floor, as a tie-break key (most fractional).
            let (f, _c) = crate::branch::floor_ceil(val);
            let dist = val.c().clone() - Rational::from_int(f);
            match &best {
                Some((_, bd)) if &dist <= bd => {}
                _ => best = Some((v, dist)),
            }
        }
        let Some((bv, _)) = best else {
            return TCheck::Sat; // all Int problem vars integral
        };
        let (floor, ceil) = crate::branch::floor_ceil(&self.value[bv.index()]);
        let term = self
            .vars
            .term_of(bv)
            .expect("branch var is a problem var with a term");
        let int_s = cx.terms.int_sort();
        let floor_num = cx.terms.mk_numeral(Rational::from_int(floor), int_s);
        let ceil_num = cx.terms.mk_numeral(Rational::from_int(ceil), int_s);
        let le = cx
            .terms
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Le), &[term, floor_num])
            .expect("(x <= floor) well-sorted");
        let ge = cx
            .terms
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Ge), &[term, ceil_num])
            .expect("(x >= ceil) well-sorted");
        TCheck::Split(vec![le, ge])
    }
```

Wire it into `check` (replacing the `TCheck::Sat => TCheck::Sat` arm from Task 4):

```rust
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        self.seed_apriori_if_needed();
        match self.check_full() {
            TCheck::Conflict(leaves) => return TCheck::Conflict(self.strip_apriori(leaves)),
            TCheck::Split(_) => unreachable!("check_full never emits Split"),
            TCheck::Sat => {}
        }
        self.integer_check(cx)
    }
```

(Note `check`'s first param is now used: rename `_cx` → `cx`.)

- [ ] **Step 5: Run tests + commit**

Run: `cargo test -p shinri-arith`
Expected: PASS (floor/ceil + split tests + all existing; pure-Real queries hit `integer_check`, find no Int vars, return Sat — unchanged behavior).

Run: `cargo test --workspace`
Expected: PASS.

```bash
cargo fmt -p shinri-arith
git add crates/shinri-arith/src/branch.rs crates/shinri-arith/src/lib.rs
git commit -m "feat(arith): integer branch-and-bound layer — fractional scan emits TCheck::Split"
```

---

### Task 6: Extend `lower()` to Int Eq/Distinct

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (`lower()`, the Eq and Distinct arms ~lines 335, 375)
- Test: `crates/shinri-solver/src/lib.rs` (inline `#[cfg(test)]` for `lower`, or a `tests/` lowering test if that's the existing pattern)

**Interfaces:**
- Produces: `lower()` rewrites Int-sorted `(distinct a b)` → `(or (Lt a b) (Gt a b))` and Int-sorted `(= a b)` → `Eq` + companion `Le`/`Ge`, identical to the Real path.
- Consumes: `Context::int_sort()`.

This change is inert until Task 7 narrows the fence (Int Lt/Gt atoms are still refused by `classify` until then), so it lands green on its own.

- [ ] **Step 1: Write the failing test**

In `crates/shinri-solver/src/lib.rs` `#[cfg(test)]` (mirror any existing `lower` test; if lowering is only tested via solve, add a direct one). The test drives `lower` on an Int distinct and asserts the top op became `Or`:

```rust
#[test]
fn lower_rewrites_int_distinct_to_or_lt_gt() {
    use shinri_core::{BuiltinOp, Op, TermNode};
    let mut s = Solver::new();
    let int = s.int_sort();
    let a = s.declare_const("a", int);
    let b = s.declare_const("b", int);
    let d = s.app(Op::Builtin(BuiltinOp::Distinct), &[a, b]);
    let lowered = s.lower(d);
    match s.ctx().term_node(lowered) {
        TermNode::App { op: Op::Builtin(BuiltinOp::Or), .. } => {}
        other => panic!("expected (or ..), got {other:?}"),
    }
}
```

> NOTE: `lower` and the `ctx()` accessor visibility — if `lower` is private, this test must live in the same module (`lib.rs` inline tests can call private `self.lower`). If there is no `ctx()` accessor, add `#[cfg(test)] pub(crate) fn ctx(&self) -> &shinri_core::Context { &self.ctx }`, or assert via re-lowering. Match the existing test conventions in the file.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver lower_rewrites_int_distinct_to_or_lt_gt`
Expected: FAIL — Int distinct currently falls through unchanged (`_ => t`), so the top op is `Distinct`, not `Or`.

- [ ] **Step 3: Generalize the sort gate**

In `lower()`, the Eq arm gate is `self.ctx.sort_of(kids[0]) == self.ctx.real_sort()` and the Distinct arm gate is the same. Replace both with an arithmetic-sort test. Add a small helper near `lower`:

```rust
    fn is_arith_sorted(&self, t: TermId) -> bool {
        let s = self.ctx.sort_of(t);
        s == self.ctx.real_sort() || s == self.ctx.int_sort()
    }
```

Then change the Eq arm condition:

```rust
            if kids.len() >= 2 && self.is_arith_sorted(kids[0]) {
```

and the Distinct binary arm condition:

```rust
                if self.is_arith_sorted(kids[0]) {
```

The `mk_app` calls for `Lt`/`Gt`/`Le`/`Ge`/`Eq` are sort-polymorphic (they type-check against the operands' shared Int sort), so the bodies need no other change.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-solver lower_rewrites_int_distinct_to_or_lt_gt`
Expected: PASS.

Run: `cargo test -p shinri-solver`
Expected: PASS — Real lowering unchanged (Real still satisfies `is_arith_sorted`).

- [ ] **Step 5: Commit**

```bash
cargo fmt -p shinri-solver
git add crates/shinri-solver/src/lib.rs
git commit -m "feat(solver): lower() rewrites Int Eq/Distinct like Real (drops real-only gate)"
```

---

### Task 7: Narrow the Int fence + LIRA query gate — flip integer support ON

**Files:**
- Modify: `crates/shinri-theory/src/atom.rs` (`classify`, remove the Int fence; update/replace the fence test)
- Modify: `crates/shinri-solver/src/tseitin.rs` (`Encoder`: `saw_int_arith`/`saw_real_arith`)
- Modify: `crates/shinri-solver/src/lib.rs` (the `refused || mixed` gate → add `lira`)
- Test: `crates/shinri-solver/tests/` (new end-to-end Int sat/unsat/termination) + `crates/shinri-theory/src/atom.rs` (admit pure-Int) + `crates/shinri-solver/src/tseitin.rs` or `lib.rs` (LIRA gate)

**Interfaces:**
- Consumes: everything from Tasks 1–6.
- Produces: pure-Int queries decided soundly end-to-end; mixed Int/Real queries → `Unknown`.

- [ ] **Step 1: Write the failing tests**

(a) `atom.rs` — replace the fence test `int_sorted_arith_is_fenced_to_unsupported` with one asserting admission:

```rust
#[test]
fn pure_int_arith_is_admitted_to_owner_arith() {
    let mut ctx = Context::new();
    let int = ctx.int_sort();
    let xi = ctx.declare_fun("xi", &[], int);
    let yi = ctx.declare_fun("yi", &[], int);
    let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
    let y = ctx.mk_app(Op::Uninterpreted(yi), &[]).unwrap();
    let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
    assert_eq!(classify(&ctx, le), Ok(Owner::Arith));
    // Real still arith.
    let real = ctx.real_sort();
    let xr = ctx.declare_fun("xr", &[], real);
    let yr = ctx.declare_fun("yr", &[], real);
    let xrt = ctx.mk_app(Op::Uninterpreted(xr), &[]).unwrap();
    let yrt = ctx.mk_app(Op::Uninterpreted(yr), &[]).unwrap();
    let ler = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xrt, yrt]).unwrap();
    assert_eq!(classify(&ctx, ler), Ok(Owner::Arith));
}
```

(b) End-to-end Int decision tests — create `crates/shinri-solver/tests/lia_e2e.rs`:

```rust
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

#[test]
fn int_unsat_2x_eq_1() {
    // 2x = 1 has no integer solution.
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let two = int_num(&mut s, 2);
    let one = int_num(&mut s, 1);
    let twox = s.app(Op::Builtin(BuiltinOp::Mul), &[two, x]);
    let atom = s.eq(twox, one);
    s.assert(atom);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn int_sat_with_branching() {
    // 2x = 4 ∧ x ≥ 1 → x = 2 (sat, requires integer feasibility).
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let two = int_num(&mut s, 2);
    let four = int_num(&mut s, 4);
    let onec = int_num(&mut s, 1);
    let twox = s.app(Op::Builtin(BuiltinOp::Mul), &[two, x]);
    let eq = s.eq(twox, four);
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[x, onec]);
    s.assert(eq);
    s.assert(ge);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

#[test]
fn int_diseq_is_a_split() {
    // x ≠ 0 ∧ -1 ≤ x ≤ 1 → x = 1 or x = -1 (sat).
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let zero = int_num(&mut s, 0);
    let lo = int_num(&mut s, -1);
    let hi = int_num(&mut s, 1);
    let ne = {
        let eq = s.eq(x, zero);
        s.app(Op::Builtin(BuiltinOp::Not), &[eq])
    };
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[x, lo]);
    let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, hi]);
    s.assert(ne);
    s.assert(ge);
    s.assert(le);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

#[test]
fn unbounded_infeasible_terminates() {
    // 3x − 3y = 1 has no integer solution; the a-priori box makes the search
    // terminate (unsat) instead of branching forever.
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let three = int_num(&mut s, 3);
    let one = int_num(&mut s, 1);
    let tx = s.app(Op::Builtin(BuiltinOp::Mul), &[three, x]);
    let ty = s.app(Op::Builtin(BuiltinOp::Mul), &[three, y]);
    let lhs = s.app(Op::Builtin(BuiltinOp::Sub), &[tx, ty]);
    let atom = s.eq(lhs, one);
    s.assert(atom);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn mixed_int_real_query_is_unknown() {
    // An Int atom and a Real atom in one query → fenced to Unknown (QF_LIRA).
    let mut s = Solver::new();
    let xi = int_const(&mut s, "xi");
    let zi = int_num(&mut s, 0);
    let gei = s.app(Op::Builtin(BuiltinOp::Ge), &[xi, zi]);
    let real = s.real_sort();
    let xr = s.declare_const("xr", real);
    let zr = s.numeral(Rational::from_int(0i128.into()), real);
    let ger = s.app(Op::Builtin(BuiltinOp::Ge), &[xr, zr]);
    s.assert(gei);
    s.assert(ger);
    assert_eq!(s.check_sat(), SolveOutcome::Unknown);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-theory pure_int_arith_is_admitted_to_owner_arith` → FAIL (currently `Err(Unsupported)`).
Run: `cargo test -p shinri-solver --test lia_e2e` → FAIL (Int currently fenced → `Unknown` for the sat/unsat cases; the mixed case may already pass).

- [ ] **Step 3a: Narrow the fence in `classify`**

In `crates/shinri-theory/src/atom.rs`, delete the Int fence block and the now-unused helper:

```rust
    // DELETE these lines from `classify`:
    //   if contains_int_arith(terms, atom) {
    //       return Err(Unsupported(atom));
    //   }
```

Delete the `contains_int_arith` function entirely (it has no other caller) and its dedicated test if separate. Keep `contains_nonlinear_mul` and its fence. `classify_equality` is unchanged (Int equalities route to `Owner::Euf`, and `lower()` from Task 6 now emits their `Le`/`Ge` companions for arith).

- [ ] **Step 3b: Track Int/Real arith in the `Encoder`**

In `crates/shinri-solver/src/tseitin.rs`, add fields to `Encoder`:

```rust
    pub saw_int_arith: bool,
    pub saw_real_arith: bool,
```

Initialize both `false` in `Encoder::new`. In the `atom()` method, in the `Ok(Owner::Arith)` arm, split by sort:

```rust
            Ok(shinri_theory::types::Owner::Arith) => {
                self.saw_arith = true;
                if self.arith_atom_is_int(t) {
                    self.saw_int_arith = true;
                } else {
                    self.saw_real_arith = true;
                }
            }
```

Add the helper to `impl Encoder`:

```rust
    /// True iff this arith relation atom's operands are Int-sorted. `mk_app`
    /// forbids mixed Int/Real arithmetic, so checking the first child suffices.
    fn arith_atom_is_int(&self, t: TermId) -> bool {
        use shinri_core::TermNode;
        if let TermNode::App { args, .. } = self.ctx.term_node(t) {
            let kids = self.ctx.children(*args);
            if let Some(&c0) = kids.first() {
                return self.ctx.sort_of(c0) == self.ctx.int_sort();
            }
        }
        false
    }
```

- [ ] **Step 3c: Add the LIRA query gate**

In `crates/shinri-solver/src/lib.rs`, where `mixed = enc.saw_shared;` is set (≈line 249), capture the LIRA signal too, and extend the early return:

```rust
            mixed = enc.saw_shared;
            // QF_LIRA (Int and Real arith vars in one query) is out of scope —
            // the simplex cannot share a tableau across sorts soundly here. Fence.
            lira = enc.saw_int_arith && enc.saw_real_arith;
```

Declare `let lira: bool;` alongside `let refused: bool;`/`let mixed: bool;` (≈line 216), and change the gate:

```rust
        if refused || mixed || lira {
            return SolveOutcome::Unknown;
        }
```

- [ ] **Step 4: Run the full suite**

Run: `cargo test -p shinri-theory` → PASS (admission test green; no consumer broke).
Run: `cargo test -p shinri-solver --test lia_e2e` → PASS (unsat/sat/diseq decided; mixed → Unknown).
Run: `cargo test --workspace`
Expected: PASS — pure-Real QF_LRA/QF_UFLRA behavior unchanged (Real atoms set `saw_real_arith`, never `saw_int_arith`, so `lira` stays false).

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-theory/src/atom.rs crates/shinri-solver/src/tseitin.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/lia_e2e.rs
git commit -m "feat(lia): admit pure-Int arith, fence QF_LIRA — pure QF_LIA decided end-to-end"
```

---

### Task 8: Differential oracle — QF_LIA generator + cvc5 backend

**Files:**
- Modify: `crates/shinri-solver/tests/oracle.rs` (new `differential_qf_lia_small` + cvc5 helper)
- Test: the new oracle function itself (gated behind `--features oracle`)

**Interfaces:**
- Consumes: the public `Solver` Int API (Task 1), the existing `Lcg`, `z_coeff_times_var`, `z_int`, `Rel` helpers in `oracle.rs`.
- Produces: a random QF_LIA corpus comparing `shinri-solver` sat/unsat against **both** z3 and cvc5; cuts are absent so this is the Stage-A baseline corpus.

- [ ] **Step 1: Write the failing test**

Append to `crates/shinri-solver/tests/oracle.rs`. It mirrors `differential_qf_lra_small` but declares **Int** vars on both sides, sets logic `QF_LIA`, and checks two oracles. Add a helper to build a second easy-smt context:

```rust
fn smt_ctx(solver: &str, logic: &str) -> easy_smt::Context {
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver(solver, ["-smt2", "-in"])
        .build()
        .unwrap();
    ctx.set_logic(logic).unwrap();
    ctx
}

#[test]
fn differential_qf_lia_small() {
    let mut rng = Lcg(0x11A_5eed);
    const N_VARS: usize = 3;
    const N_ITERS: usize = 300;
    let mut unknowns = 0usize;

    for iter in 0..N_ITERS {
        // ── shinri (Int) ────────────────────────────────────────────────────
        let mut s = Solver::new();
        let int = s.int_sort();
        let vars: Vec<shinri_core::TermId> =
            (0..N_VARS).map(|i| s.declare_const(&format!("x{i}"), int)).collect();

        // ── two oracles: z3 + cvc5, both Int ────────────────────────────────
        let mut z = smt_ctx("z3", "QF_LIA");
        let mut c = smt_ctx("cvc5", "QF_LIA");
        let z_int_sort = z.atom("Int");
        let c_int_sort = c.atom("Int");
        let zv: Vec<easy_smt::SExpr> =
            (0..N_VARS).map(|i| z.declare_const(format!("x{i}"), z_int_sort).unwrap()).collect();
        let cv: Vec<easy_smt::SExpr> =
            (0..N_VARS).map(|i| c.declare_const(format!("x{i}"), c_int_sort).unwrap()).collect();

        let n_constraints = 4 + rng.below(4) as usize;
        let mut dump = format!("iter={iter}");
        for _ in 0..n_constraints {
            let rel = match rng.below(6) {
                0 => Rel::Le, 1 => Rel::Lt, 2 => Rel::Ge, 3 => Rel::Gt, 4 => Rel::Eq, _ => Rel::Ne,
            };
            let mut coeffs: Vec<i32> = (0..N_VARS).map(|_| (rng.below(5) as i32) - 2).collect();
            if coeffs.iter().all(|&c| c == 0) { coeffs[0] = 1; }
            let rhs_val: i32 = (rng.below(7) as i32) - 3;
            dump.push_str(&format!("\n  {coeffs:?} {rel:?} {rhs_val}"));

            // shinri lhs
            let mut terms = Vec::new();
            for (i, &coeff) in coeffs.iter().enumerate() {
                if coeff == 0 { continue; }
                let ct = s.numeral(Rational::from_int((coeff as i128).into()), int);
                terms.push(s.app(Op::Builtin(BuiltinOp::Mul), &[ct, vars[i]]));
            }
            let s_lhs = terms.into_iter().reduce(|a, t| s.app(Op::Builtin(BuiltinOp::Add), &[a, t])).unwrap();
            let s_rhs = s.numeral(Rational::from_int((rhs_val as i128).into()), int);
            let s_atom = match rel {
                Rel::Le => s.app(Op::Builtin(BuiltinOp::Le), &[s_lhs, s_rhs]),
                Rel::Lt => s.app(Op::Builtin(BuiltinOp::Lt), &[s_lhs, s_rhs]),
                Rel::Ge => s.app(Op::Builtin(BuiltinOp::Ge), &[s_lhs, s_rhs]),
                Rel::Gt => s.app(Op::Builtin(BuiltinOp::Gt), &[s_lhs, s_rhs]),
                Rel::Eq => s.eq(s_lhs, s_rhs),
                Rel::Ne => { let e = s.eq(s_lhs, s_rhs); s.app(Op::Builtin(BuiltinOp::Not), &[e]) }
            };
            s.assert(s_atom);

            // both oracles (same coeffs)
            for (ctx, cvars) in [(&mut z, &zv), (&mut c, &cv)] {
                let zt: Vec<easy_smt::SExpr> = coeffs.iter().enumerate()
                    .filter_map(|(i, &coeff)| z_coeff_times_var(ctx, coeff, cvars[i])).collect();
                let z_lhs = zt.into_iter().reduce(|a, t| ctx.plus(a, t)).unwrap();
                let z_rhs = z_int(ctx, rhs_val);
                let z_atom = match rel {
                    Rel::Le => ctx.lte(z_lhs, z_rhs),
                    Rel::Lt => ctx.lt(z_lhs, z_rhs),
                    Rel::Ge => ctx.gte(z_lhs, z_rhs),
                    Rel::Gt => ctx.gt(z_lhs, z_rhs),
                    Rel::Eq => ctx.eq(z_lhs, z_rhs),
                    Rel::Ne => { let e = ctx.eq(z_lhs, z_rhs); ctx.not(e) }
                };
                ctx.assert(z_atom).unwrap();
            }
        }

        let ours = s.check_sat();
        let z_res = z.check().unwrap();
        let c_res = c.check().unwrap();
        // The two oracles must agree with each other.
        assert_eq!(format!("{z_res:?}"), format!("{c_res:?}"), "z3≠cvc5 (iter {iter})\n{dump}");
        match (ours, z_res) {
            (SolveOutcome::Unknown, _) => unknowns += 1,
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {}
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {}
            (o, t) => panic!("LIA DISAGREEMENT (iter {iter}): shinri={o:?} oracle={t:?}\n{dump}"),
        }
    }
    assert_eq!(unknowns, 0, "pure QF_LIA must not go Unknown ({unknowns} did)");
}
```

> NOTE: `z_coeff_times_var`/`z_int` take `&easy_smt::Context`; the `for (ctx, cvars)` loop borrows each mutably for `assert` but those helpers need `&` — pass `ctx` (a `&mut`) where `&` is expected via reborrow `&*ctx`, or split the calls. Match the existing helper signatures; if the borrow fights, build the `z_lhs`/`z_rhs` with an immutable borrow first, then `ctx.assert`.

- [ ] **Step 2: Run it (requires z3 + cvc5 on PATH)**

Run: `cargo test -p shinri-solver --features oracle differential_qf_lia_small -- --nocapture`
Expected: FAIL initially only if the harness has a wiring bug; once wired it must PASS (Tasks 1–7 supply the decision procedure). If `cvc5` is not installed, the test errors at context build — document the dependency in the test's module comment alongside the existing z3 note.

- [ ] **Step 3: Fix wiring until green**

Resolve any easy-smt borrow/typing issues per the NOTE. No production code should be needed; if a disagreement fires, that is a real soundness bug in Tasks 1–7 — debug there (use the dumped instance), do not paper over it in the oracle.

- [ ] **Step 4: Confirm gating + full suite**

Run: `cargo test -p shinri-solver --features oracle differential_qf_lia_small`
Expected: PASS.

Run: `cargo test --workspace`
Expected: PASS (the oracle is feature-gated off by default, so the default suite is unaffected).

- [ ] **Step 5: Commit**

```bash
cargo fmt -p shinri-solver
git add crates/shinri-solver/tests/oracle.rs
git commit -m "test(oracle): random QF_LIA differential vs z3 + cvc5 (Stage-A baseline)"
```

---

## Self-Review

**Spec coverage (vs `2026-06-21-shinri-lia-planB1-design.md`):**
- §3.1 mutable term seam → Task 2. ✅
- §3.2 narrow Int fence (admit pure-Int, fence mixed) → Task 7 (classify) + Task 7c (LIRA query gate). ✅
- §3.3 a-priori box `M` (bigint, lazy level-0 seed, ordinary bounds) → Task 4. ✅ (sentinel-lit attribution + strip, with soundness note.)
- §3.4 fractional scan + branch `Split` (most-fractional, Bland tiebreak) → Task 5. ✅
- §3.5 Int diseq via `lower()` → `(or Lt Gt)`; δ-reuse for strictness (no tightening) → Task 6; strictness handled by the existing δ encoding + Task 5 scan. ✅
- §3.6 integer model emission → **no code change**: at a Sat leaf the scan guarantees every Int var has `k=0` and integer `c`, so the existing `build_model` (`c + k·δ` with `k=0`) already emits the integer. Verified end-to-end by Task 7's `int_sat_with_branching`/`int_diseq_is_a_split` (a wrong model fails `shinri-solver`'s self-check). ✅
- §4 tests: differential oracle z3+cvc5 → Task 8; unit (M, branch freshness, diseq lowering, fence admission, LIRA) → Tasks 4/5/6/7; the non-terminating-without-a-bound regression (`unbounded_infeasible_terminates`) → Task 7 `lia_e2e.rs`. ✅
- §5 file plan ↔ tasks: all rows mapped; `normalize.rs` untouched as stated. ✅
- `Solver::int_sort()` prerequisite → Task 1. ✅

**Gap found + filled:** the spec §4 names "the classic non-terminating-without-a-bound instance must terminate" as a test, not pinned to a task in the first draft. Now folded in as `unbounded_infeasible_terminates` in Task 7's `lia_e2e.rs` (Step 1) and its commit.

**Placeholder scan:** no "TBD"/"add error handling"/"similar to" — every code step is complete. The only guided-adaptation points are explicit `NOTE`s pinned to "match the file as it exists" (test-harness construction in Tasks 4/5, `lower`/`ctx()` visibility in Task 6, easy-smt borrow shape in Task 8), not undecided design.

**Type consistency:** `TCheck::Split(Vec<TermId>)` (Task 5) matches the Plan-A `TheoryResult::SplitAtoms(Vec<TermId>)` lift; `branch::floor_ceil(&DeltaRational) -> (Integer, Integer)` consumed identically in Task 5; `VarStore::is_int`/`mark_int`/`problem_var_sorted` consistent across Tasks 3–5; `apriori_lits: FxHashSet<u32>` keyed by `Lit::code()` consistent between `seed_apriori_if_needed` and `strip_apriori`; `int_sort()` (Task 1) used in Tasks 4/5/6/7/8.

**Soundness ordering:** the fence opens only in Task 7, after Tasks 3–6; Tasks 3–6 are validated by direct `Arith`/`lower`/`classify` unit tests while integer queries are still `Unknown`. Every commit leaves `cargo test --workspace` green and sound.
