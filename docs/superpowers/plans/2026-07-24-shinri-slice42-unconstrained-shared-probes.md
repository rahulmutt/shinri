# Slice 42 — Pruning N-O probes over unconstrained shared vars: Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stop `shinri-arith` from running Nelson–Oppen entailment probes and MBTC splits over shared problem vars it has received no constraint about, eliminating a ≈1600× slowdown on any QF_DT query whose datatype has an `Int` field.

**Architecture:** `Arith` gains a monotone `constrained: Vec<bool>` marking problem vars it has actually been told something about, set at four semantic entry points. `entailed_equalities` and `model_equal_shared_pairs` skip any pair containing an unmarked var, at candidate-construction time — before any slack is minted. Nothing outside `shinri-arith` changes: the `Combiner`, the shared set `S`, and both exchange directions are untouched.

**Tech Stack:** Rust, `cargo nextest`, `mise` tasks, z3/cvc5 oracle differential (feature-gated).

**Spec:** [docs/superpowers/specs/2026-07-24-shinri-slice42-unconstrained-shared-probes-design.md](../specs/2026-07-24-shinri-slice42-unconstrained-shared-probes-design.md)

## Global Constraints

- **Pure-Rust mandate.** Native-link dependencies are banned (`deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`). This slice adds no dependencies.
- **`cargo fmt --all` before every push.** CI gates on `fmt --check` and fails fast. Subagents do not auto-format.
- **`mise run lint` must be clean** — `cargo clippy --workspace --all-targets -- -D warnings`.
- **Blocking PR tier budget: 10–15 min wall-clock.** Any test measured >5 min must be `#[ignore = "exhaustive: nightly tier (~N min in CI)"]`d.
- **Oracle tests are feature-gated.** `cargo nextest run -p shinri-solver --features oracle`. **Without `--features oracle` they silently run 0 tests** — never report that as green coverage.
- **Never remove `#[ignore]`** from the exhaustive `shinri-fp` suites.
- **Nextest filter syntax:** use `-E 'test(name)'`, not a positional `mod::name` filter (which finds 0 tests on nextest 0.9.140). Always confirm a non-zero discovered test count.
- **Feature work happens on a slice branch** with a PR to `main`; merge with a merge commit when CI is green, then delete the branch (remote and local).

## File Structure

| File | Responsibility | Change |
|---|---|---|
| `crates/shinri-arith/src/lib.rs` | The `Arith` theory solver: field, helpers, four marking sites, two guards, unit tests | Modify |
| `crates/shinri-solver/tests/qfdt_e2e.rs` | End-to-end QF_DT verdicts; gains the performance gate | Modify |
| `docs/superpowers/specs/2026-07-24-shinri-slice42-unconstrained-shared-probes-design.md` | Records the §3.A entry-point audit findings | Modify (Task 2) |

All production changes are confined to one file. That is deliberate: the spec (§2) rejected the `Combiner`-side fix specifically to keep the blast radius inside `shinri-arith`.

---

## Task 1: Constrainedness tracking (no pruning yet)

Adds the state and the four marking sites. **No behavior changes** — every existing test must still pass, unchanged. This task is separately reviewable because a reviewer can confirm the marking is correct without yet reasoning about what is pruned.

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (struct field ~line 125, `Default` ~line 153, helpers in `impl Arith` ~line 182, marking sites at ~537, ~750, ~1104, ~1142)
- Test: `crates/shinri-arith/src/lib.rs`, `mod nelson_oppen_tests` (starts line 1553)

**Interfaces:**
- Consumes: nothing.
- Produces: `Arith::mark_constrained(&mut self, v: ArithVar)` and `Arith::is_constrained(&self, v: ArithVar) -> bool`, both private to `shinri-arith`. Tasks 3 and 4 call `is_constrained`.

- [ ] **Step 1: Write the failing test**

Add to `mod nelson_oppen_tests` in `crates/shinri-arith/src/lib.rs` (after the `pairset` helper, ~line 1692):

```rust
    // ----- Slice 42: constrainedness marking -----

    fn int_var_no(ctx: &mut Context, name: &str) -> TermId {
        let int = ctx.int_sort();
        let s = ctx.declare_fun(name, &[], int);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    #[test]
    fn ensure_shared_var_alone_does_not_constrain() {
        // A shared term arith was merely TOLD about — no atom, not a numeral —
        // must stay unconstrained. This is the `head(t)` population that slice
        // 42 exists to prune.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        let xv = h.arith.vars.problem_var(x);
        assert!(
            !h.arith.is_constrained(xv),
            "a merely-shared non-numeral term must not be marked constrained"
        );
    }

    #[test]
    fn registered_atom_constrains_its_problem_vars() {
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let xy = h.ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let five = num(&mut h.ctx, 5);
        let a = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[xy, five])
            .unwrap();
        h.assert_atom(0, a);
        let xv = h.arith.vars.problem_var(x);
        let yv = h.arith.vars.problem_var(y);
        assert!(h.arith.is_constrained(xv), "x occurs in a registered atom");
        assert!(h.arith.is_constrained(yv), "y occurs in a registered atom");
    }

    #[test]
    fn numeral_pin_constrains() {
        let mut h = Harness::new();
        let five = num(&mut h.ctx, 5);
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, five);
        let fv = h.arith.vars.problem_var(five);
        assert!(
            h.arith.is_constrained(fv),
            "a pinned numeral IS constrained"
        );
    }

    #[test]
    fn interface_equality_constrains_both_sides() {
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        let just = TheoryJust { theory: 0, tag: 0 };
        let _ = h.arith.assert_interface_equality(&ctx, x, y, just);
        let xv = h.arith.vars.problem_var(x);
        let yv = h.arith.vars.problem_var(y);
        assert!(h.arith.is_constrained(xv), "interface eq constrains lhs");
        assert!(h.arith.is_constrained(yv), "interface eq constrains rhs");
    }

    #[test]
    fn apriori_box_does_not_constrain() {
        // The a-priori box (`seed_apriori_if_needed`) puts bounds on EVERY Int
        // problem var, including free ones. Those bounds must NOT count as a
        // constraint: a uniform [-M, M] box entails no equality, and treating it
        // as constraining would defeat the whole slice.
        let mut h = Harness::new();
        let x = int_var_no(&mut h.ctx, "xi");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        assert!(matches!(h.arith.check_full(), TCheck::Sat));
        let xv = h.arith.vars.problem_var(x);
        assert!(
            !h.arith.is_constrained(xv),
            "a-priori box bounds must not mark a var constrained"
        );
    }

    #[test]
    fn constrained_marking_survives_pop() {
        // The set is MONOTONE by design: never un-marked, including on pop.
        // Over-approximating constrainedness errs toward more probing, which is
        // the sound direction.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let five = num(&mut h.ctx, 5);
        let a = h.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, five]).unwrap();
        h.arith.push();
        h.assert_atom(0, a);
        let xv = h.arith.vars.problem_var(x);
        assert!(h.arith.is_constrained(xv));
        h.arith.pop(0);
        assert!(
            h.arith.is_constrained(xv),
            "constrainedness is monotone across pop"
        );
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

```bash
cargo nextest run -p shinri-arith -E 'test(constrain) or test(apriori_box_does_not) or test(numeral_pin) or test(interface_equality_constrains)'
```

Expected: FAIL to compile with `no method named 'is_constrained' found for struct 'Arith'`. Confirm the run reports a **non-zero** number of tests attempted once it compiles — a 0-test run proves nothing.

- [ ] **Step 3: Add the field**

In `pub struct Arith` in `crates/shinri-arith/src/lib.rs`, immediately before the closing `}` of the struct (after the `pivot_budget` field, ~line 125):

```rust
    /// Problem vars arith has actually received a constraint about (slice 42).
    /// Indexed by `ArithVar::index()`; `false`/absent means arith knows the var
    /// exists but nothing about its value, so no equality over it can be
    /// entailed and no arrangement of it needs deciding.
    ///
    /// MONOTONE: never un-marked, including on `pop`. After backtracking, a var
    /// constrained only by a since-retracted assertion stays marked and is still
    /// probed. That over-approximates constrainedness, which errs toward MORE
    /// probing — the sound direction.
    ///
    /// Deliberately NOT inferred from `bounds`: `seed_apriori_if_needed` puts a
    /// uniform box on every Int problem var (free ones included), and
    /// `entailed_equalities`' probe slacks persist across calls, so both the
    /// bounds table and the tableau report free vars as constrained.
    constrained: Vec<bool>,
```

- [ ] **Step 4: Initialize the field**

In `impl Default for Arith`, after `pivot_budget: Self::DEFAULT_PIVOT_BUDGET,` (~line 152):

```rust
            constrained: Vec::default(),
```

- [ ] **Step 5: Add the helpers**

In `impl Arith`, immediately after `fn grow_value` (~line 187):

```rust
    /// Mark `v` as a var arith has received a constraint about (slice 42).
    /// Resizes on demand rather than tracking `grow_value` ordering.
    fn mark_constrained(&mut self, v: ArithVar) {
        if v.index() >= self.constrained.len() {
            self.constrained.resize(v.index() + 1, false);
        }
        self.constrained[v.index()] = true;
    }

    /// Whether arith has received any constraint about `v` (slice 42). An
    /// unmarked var is free: `u = v` is not entailed for any `v`, and any
    /// arrangement of it is arith-satisfiable.
    fn is_constrained(&self, v: ArithVar) -> bool {
        self.constrained.get(v.index()).copied().unwrap_or(false)
    }
```

- [ ] **Step 6: Mark at atom registration (`new_var`)**

In `fn new_var` (~line 1104), immediately after the existing Int-stamping loop that ends with the closing `}` before `// Track max |coeff| and |constant| across all atoms`:

```rust
        // Slice 42: every problem var occurring in a registered arith atom is
        // constrained. This is the dominant marking site — it subsumes `assert`
        // for single-var atoms and covers multi-var atoms whose encoding is over
        // a slack.
        for (av, _) in &n.comb.0 {
            self.mark_constrained(*av);
        }
```

- [ ] **Step 7: Mark at the numeral pin (`ensure_shared_var`)**

In `fn ensure_shared_var` (~line 537), change:

```rust
        if let Some(r) = ctx.numeral_value(t) {
            let dr = DeltaRational::from_rational(r.clone());
```

to:

```rust
        if let Some(r) = ctx.numeral_value(t) {
            // Slice 42: pinning a numeral to its value IS a constraint. Marked
            // outside the `already` guard so re-entry keeps the mark. The
            // non-numeral path deliberately does NOT mark — that asymmetry is
            // the whole point of the slice.
            self.mark_constrained(v);
            let dr = DeltaRational::from_rational(r.clone());
```

- [ ] **Step 8: Mark at interface equalities (`assert_interface_equality`)**

In `fn assert_interface_equality` (~line 750), change:

```rust
        if av == bv {
            return None;
        }
        let comb = Self::diff_comb(av, bv);
```

to:

```rust
        if av == bv {
            return None;
        }
        // Slice 42: an EUF→arith interface equality pins `av - bv = 0`, which
        // constrains both sides.
        self.mark_constrained(av);
        self.mark_constrained(bv);
        let comb = Self::diff_comb(av, bv);
```

- [ ] **Step 9: Mark at assertion (`assert`)**

In `fn assert` (~line 1142), change:

```rust
            Some(AtomEncoding::Ineq { var, pos, neg }) => {
                let (kind, val) = if lit.is_positive() { pos } else { neg };
                self.apply_bound(var, kind, val, lit)
            }
```

to:

```rust
            Some(AtomEncoding::Ineq { var, pos, neg }) => {
                let (kind, val) = if lit.is_positive() { pos } else { neg };
                // Slice 42: belt-and-braces. `new_var` already marked this atom's
                // problem vars, and `var` here is a slack for multi-var atoms
                // (slacks never appear in the shared set). Marking anyway costs
                // nothing and keeps the invariant true even if an encoding path
                // reaches `assert` without `new_var`.
                self.mark_constrained(var);
                self.apply_bound(var, kind, val, lit)
            }
```

- [ ] **Step 10: Run the new tests to verify they pass**

```bash
cargo nextest run -p shinri-arith -E 'test(constrain) or test(apriori_box_does_not) or test(numeral_pin) or test(interface_equality_constrains)'
```

Expected: PASS, with a non-zero test count (6 tests).

- [ ] **Step 11: Run the whole arith crate to verify no behavior changed**

```bash
cargo nextest run -p shinri-arith
```

Expected: PASS. This task adds state only — no existing test may change behavior. If anything fails here, a marking site has side effects it should not have.

- [ ] **Step 12: Format, lint, and commit**

```bash
cargo fmt --all
cargo clippy -p shinri-arith --all-targets -- -D warnings
git add crates/shinri-arith/src/lib.rs
git commit -m "feat(arith): slice42 T1 — track which problem vars arith is constrained about

Monotone Vec<bool> marked at four entry points: registered-atom vars, the
ensure_shared_var numeral pin, interface equalities, and assert. Deliberately
NOT inferred from bounds/tableau — the a-priori box bounds every Int var and
probe slacks persist, so both report free vars as constrained. No pruning yet;
behavior is unchanged."
```

---

## Task 2: Entry-point audit

The guard's soundness rests entirely on the claim that Task 1's marking sites are exhaustive. This task establishes that claim and records it. **It is a reading-and-writing task with no production code change** — it is separate precisely so a reviewer gates the argument independently of the code that depends on it.

**Files:**
- Modify: `docs/superpowers/specs/2026-07-24-shinri-slice42-unconstrained-shared-probes-design.md` (append §4.B)

**Interfaces:**
- Consumes: `mark_constrained` / `is_constrained` from Task 1.
- Produces: an audit record. Tasks 3–4 depend on its conclusion, not on any symbol.

- [ ] **Step 1: Enumerate every writer of `bounds`**

```bash
grep -n "apply_bound(\|bounds.tighten(" crates/shinri-arith/src/*.rs
```

Expected sites: `assert_interface_equality` (2 calls, ~781/784), `seed_apriori_if_needed` (~1074/1075), `run_fbbt` (~1096), `assert` (~1156), and `ensure_shared_var`'s numeral pin (~551/552). For each, answer: *can this constrain a problem var that Task 1 leaves unmarked?*

- [ ] **Step 2: Enumerate every writer of the tableau**

```bash
grep -n "define_slack(" crates/shinri-arith/src/*.rs
```

For each slack definition, answer: *whose linear combination is it built from, and are those vars marked?*

- [ ] **Step 3: Check the cut and branch paths**

```bash
grep -rn "fn add_cut\|fn emit_branch\|GmiCut" crates/shinri-arith/src/cuts.rs crates/shinri-arith/src/branch.rs | head -20
```

Confirm that cuts and branch atoms are derived from existing rows/bounds and cannot introduce a constraint on a var that occurs in no registered atom. Branch atoms route back through `Combiner::bind_fresh` → `Arith::new_var`, which marks.

- [ ] **Step 4: Write the audit into the spec**

Append to `docs/superpowers/specs/2026-07-24-shinri-slice42-unconstrained-shared-probes-design.md`, immediately after §4.A:

```markdown
### 4.B Entry-point audit (recorded during implementation)

Every writer of `bounds` and of the tableau, and what it means for the
invariant:

| Site | Marks? | Why that is correct |
|---|---|---|
| `assert` (`lib.rs:1156`) | yes | the atom's bound goes on the trail |
| `new_var` atom registration (`lib.rs:1104`) | yes | dominant site; covers multi-var atoms whose encoding is over a slack |
| `assert_interface_equality` (`lib.rs:781`, `784`) | yes | pins `av - bv = 0` |
| `ensure_shared_var` numeral pin (`lib.rs:551`) | yes | a numeral is fixed to its value |
| `ensure_shared_var` non-numeral path | **no** | arith is told the var exists, nothing more — the population this slice prunes |
| `seed_apriori_if_needed` (`lib.rs:1074`) | **no** | seeds a UNIFORM `[-M, M]` box on every non-slack Int var. Two vars each ranging over a box of width ≥ 2 are not entailed equal, so this cannot make a skipped pair a missed deduction. Marking here would mark every Int var and defeat the slice. |
| `run_fbbt` (`lib.rs:1096`) | **no** | FBBT derives tightenings by propagating along tableau rows. A var occurring in no registered atom appears only in probe slacks, which carry no bounds after `restore` — so FBBT has nothing to propagate to it. |
| `cuts.rs` GMI cuts | **no** | derived from existing rows and bounds; generates no constraint on a var absent from all of them |
| `branch.rs` B&B split atoms | n/a | routed back through `Combiner::bind_fresh` → `Arith::new_var`, which marks |

**Conclusion.** A problem var left unmarked by Task 1 has, at most, a-priori box
bounds and membership in bound-free probe-slack rows. Neither pins its value, so
the §4 invariant holds: at least two values remain admissible for it in any
satisfying assignment, and therefore `u = v` is not entailed for any `v`.
```

Replace any row above whose finding differs from what Steps 1–3 actually show. **If a site is found that constrains without marking, do not proceed to Task 3** — add the marking site to Task 1 first and re-run its tests.

- [ ] **Step 5: Commit**

```bash
git add docs/superpowers/specs/2026-07-24-shinri-slice42-unconstrained-shared-probes-design.md
git commit -m "docs(arith): slice42 T2 — record the entry-point audit backing the guard

Enumerates every writer of bounds and of the tableau and states why the
a-priori box, FBBT, cuts, and branch atoms need not mark constrainedness. The
guard in T3/T4 is sound only if this table is exhaustive."
```

---

## Task 3: The guard in `entailed_equalities`

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (~line 588–600, the candidate pre-filter)
- Test: `crates/shinri-arith/src/lib.rs`, `mod nelson_oppen_tests`

**Interfaces:**
- Consumes: `Arith::is_constrained` (Task 1); the audit conclusion (Task 2).
- Produces: no new symbols. Behavior: `entailed_equalities` returns a subset of what it returned before — never a superset.

- [ ] **Step 1: Write the failing test**

Add to `mod nelson_oppen_tests`:

```rust
    #[test]
    fn unconstrained_pair_is_not_probed_and_mints_no_slack() {
        // Two shared vars arith knows nothing about. No equality can be
        // entailed, AND no slack may be minted: `entailed_equalities` snapshots
        // AFTER `define_slack`, so a slack created here would persist for the
        // rest of the solve and re-admit the cost on every later call.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);
        assert!(matches!(h.arith.check_full(), TCheck::Sat));

        let vars_before = h.arith.vars.len();
        let got = h.arith.entailed_equalities(&ctx, &[x, y]);

        assert!(got.is_empty(), "no equality is entailed over free vars");
        assert_eq!(
            h.arith.vars.len(),
            vars_before,
            "no slack may be minted for a skipped pair"
        );
    }

    #[test]
    fn mixed_pair_with_one_free_var_is_skipped() {
        // x is fixed to 3; y is free. `x = y` is not entailed, and the pair must
        // be skipped rather than probed.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let three = num(&mut h.ctx, 3);
        let le = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[x, three])
            .unwrap();
        let ge = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[x, three])
            .unwrap();
        h.assert_atom(0, le);
        h.assert_atom(1, ge);
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);

        let vars_before = h.arith.vars.len();
        let got = h.arith.entailed_equalities(&ctx, &[x, y]);

        assert!(got.is_empty(), "a free var is not entailed equal to a fixed one");
        assert_eq!(h.arith.vars.len(), vars_before, "no slack for a skipped pair");
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

```bash
cargo nextest run -p shinri-arith -E 'test(unconstrained_pair_is_not_probed) or test(mixed_pair_with_one_free_var)'
```

Expected: FAIL — `no slack may be minted for a skipped pair`, because the unguarded candidate loop admits both pairs and `define_slack` runs.

- [ ] **Step 3: Add the guard**

In `pub fn entailed_equalities` (~line 588), change:

```rust
        // Pre-filter (R3 necessary condition): only same-β pairs can be entailed.
        // Group by current β (DeltaRational equality).
        let mut candidates: Vec<(usize, usize)> = Vec::new();
        for i in 0..items.len() {
            for j in (i + 1)..items.len() {
                if self.value[items[i].1.index()] == self.value[items[j].1.index()] {
                    candidates.push((i, j));
                }
            }
        }
```

to:

```rust
        // Pre-filter (R3 necessary condition): only same-β pairs can be entailed.
        // Group by current β (DeltaRational equality).
        //
        // Slice 42: additionally skip any pair containing a var arith has
        // received no constraint about. Such a var is free, so `u = v` is not
        // entailed for any `v` and the probe cannot succeed. The skip MUST
        // happen here, before the `define_slack` loop below: the R1 snapshot is
        // taken AFTER slack definition and the final `restore` restores to it,
        // so a slack minted for a hopeless pair would persist for the rest of
        // the solve. Without this, a datatype with an Int field makes every
        // DT-minted selector app a free shared var at β = 0, admitting every
        // pair — the ≈1600× regression this slice fixes.
        let mut candidates: Vec<(usize, usize)> = Vec::new();
        for i in 0..items.len() {
            if !self.is_constrained(items[i].1) {
                continue;
            }
            for j in (i + 1)..items.len() {
                if !self.is_constrained(items[j].1) {
                    continue;
                }
                if self.value[items[i].1.index()] == self.value[items[j].1.index()] {
                    candidates.push((i, j));
                }
            }
        }
```

- [ ] **Step 4: Run the new tests to verify they pass**

```bash
cargo nextest run -p shinri-arith -E 'test(unconstrained_pair_is_not_probed) or test(mixed_pair_with_one_free_var)'
```

Expected: PASS (2 tests).

- [ ] **Step 5: Run the N-O anti-regression anchors**

```bash
cargo nextest run -p shinri-arith -E 'test(order_independence) or test(fixed_vars_entailed_equal) or test(probe_does_not_perturb_state)'
```

Expected: PASS. `order_independence` is the critical anchor — three vars each pinned by asserted atoms, all three pairs entailed. If the guard is too aggressive it drops these and the count assertion (`fwd.len() == 3`) fails.

- [ ] **Step 6: Run the whole arith crate**

```bash
cargo nextest run -p shinri-arith
```

Expected: PASS.

- [ ] **Step 7: Format, lint, and commit**

```bash
cargo fmt --all
cargo clippy -p shinri-arith --all-targets -- -D warnings
git add crates/shinri-arith/src/lib.rs
git commit -m "perf(arith): slice42 T3 — skip N-O entailment probes over free vars

A problem var arith has no constraint about cannot be entailed equal to
anything, so probing the pair is guaranteed waste. Guard sits at candidate
construction, before define_slack, because the R1 snapshot is taken after slack
definition and a slack minted for a hopeless pair persists for the whole solve."
```

---

## Task 4: The guard in `model_equal_shared_pairs` (MBTC)

Same invariant, second consumer. The spec (§3.C) treats this as a **distinct soundness sub-claim**: arrangement agreement rather than equality entailment.

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (~line 671–690)
- Test: `crates/shinri-arith/src/lib.rs`, `mod nelson_oppen_tests`

**Interfaces:**
- Consumes: `Arith::is_constrained` (Task 1).
- Produces: no new symbols. `model_equal_shared_pairs` returns a subset of its previous result.

- [ ] **Step 1: Write the failing test**

Add to `mod nelson_oppen_tests`:

```rust
    #[test]
    fn mbtc_skips_pairs_with_a_free_var() {
        // Two free Int shared vars both sit at β = 0, so the unguarded sweep
        // reports them as a model-equal pair and the Combiner turns that into a
        // 3-way trichotomy split. Arith constrains neither side, so any
        // arrangement EUF picks is arith-satisfiable and the split is waste.
        let mut h = Harness::new();
        let x = int_var_no(&mut h.ctx, "xm");
        let y = int_var_no(&mut h.ctx, "ym");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);
        assert!(matches!(h.arith.check_full(), TCheck::Sat));

        let pairs = h.arith.model_equal_shared_pairs(&[x, y]);
        assert!(pairs.is_empty(), "free vars need no MBTC arrangement split");
    }

    #[test]
    fn mbtc_still_reports_constrained_model_equal_pairs() {
        // Both vars pinned to 3: still a model-equal pair, still reported.
        let mut h = Harness::new();
        let x = int_var_no(&mut h.ctx, "xc");
        let y = int_var_no(&mut h.ctx, "yc");
        let three = h
            .ctx
            .mk_numeral(Rational::from_int(3i128.into()), h.ctx.int_sort());
        for (i, v) in [x, y].iter().enumerate() {
            let le = h
                .ctx
                .mk_app(Op::Builtin(BuiltinOp::Le), &[*v, three])
                .unwrap();
            let ge = h
                .ctx
                .mk_app(Op::Builtin(BuiltinOp::Ge), &[*v, three])
                .unwrap();
            h.assert_atom(2 * i as u32, le);
            h.assert_atom(2 * i as u32 + 1, ge);
        }
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);

        let pairs = h.arith.model_equal_shared_pairs(&[x, y]);
        assert_eq!(pairs.len(), 1, "constrained model-equal pair must survive");
    }
```

- [ ] **Step 2: Run the tests to verify the first fails**

```bash
cargo nextest run -p shinri-arith -E 'test(mbtc_skips_pairs) or test(mbtc_still_reports)'
```

Expected: `mbtc_skips_pairs_with_a_free_var` FAILS (returns 1 pair, expected 0); `mbtc_still_reports_constrained_model_equal_pairs` PASSES already.

- [ ] **Step 3: Add the guard**

In `pub fn model_equal_shared_pairs` (~line 671), change:

```rust
        let mut out = Vec::new();
        for i in 0..items.len() {
            for j in (i + 1)..items.len() {
                if self.value[items[i].1.index()] == self.value[items[j].1.index()] {
                    out.push((items[i].0, items[j].0));
                }
            }
        }
```

to:

```rust
        // Slice 42: skip pairs containing a var arith has no constraint about.
        // Arith constrains neither side, so every arrangement EUF chooses is
        // arith-satisfiable and MBTC has nothing to decide. This is a DISTINCT
        // soundness claim from the one in `entailed_equalities` — arrangement
        // agreement, not equality entailment — over the same var set.
        let mut out = Vec::new();
        for i in 0..items.len() {
            if !self.is_constrained(items[i].1) {
                continue;
            }
            for j in (i + 1)..items.len() {
                if !self.is_constrained(items[j].1) {
                    continue;
                }
                if self.value[items[i].1.index()] == self.value[items[j].1.index()] {
                    out.push((items[i].0, items[j].0));
                }
            }
        }
```

- [ ] **Step 4: Run the tests to verify they pass**

```bash
cargo nextest run -p shinri-arith -E 'test(mbtc_skips_pairs) or test(mbtc_still_reports)'
```

Expected: PASS (2 tests).

- [ ] **Step 5: Run the whole arith crate**

```bash
cargo nextest run -p shinri-arith
```

Expected: PASS.

- [ ] **Step 6: Format, lint, and commit**

```bash
cargo fmt --all
cargo clippy -p shinri-arith --all-targets -- -D warnings
git add crates/shinri-arith/src/lib.rs
git commit -m "perf(arith): slice42 T4 — skip MBTC arrangement splits over free vars

Same var set as T3, distinct soundness claim: arith constrains neither side of
such a pair, so any arrangement EUF chooses is arith-satisfiable and the
trichotomy split decides nothing."
```

---

## Task 5: End-to-end performance gate and DT⋈arith regression

**Files:**
- Modify: `crates/shinri-solver/tests/qfdt_e2e.rs` (append; existing DT⋈arith tests at lines 146–231 are the untouched regression anchors)

**Interfaces:**
- Consumes: the guards from Tasks 3 and 4, via the full solver.
- Produces: nothing consumed downstream.

- [ ] **Step 1: Write the failing test**

Append to `crates/shinri-solver/tests/qfdt_e2e.rs`:

```rust
/// Slice 42 performance gate. A datatype with an `Int` field makes every
/// DT-minted `head(t)` selector application an Int-sorted UF app, so the
/// sort-only filter in `Euf::shared_arith_terms` sweeps all of them into the
/// Nelson-Oppen shared set. Pre-slice-42 every pair sat at β = 0 and was probed
/// with two simplex solves: 24.1 s at n = 24, against 6 ms for the same query
/// with an uninterpreted field sort.
///
/// The bound is deliberately loose (5 s against a 24.1 s baseline). Wall-clock
/// assertions are normally a flakiness smell; a ≈1600× fault leaves enough
/// margin to be worth one, and without it a regression silently consumes the
/// blocking tier's 10-15 min budget.
#[test]
fn int_field_chain_does_not_blow_up() {
    let n = 24;
    let mut src = String::from(
        "(set-logic QF_DT)\
         (declare-datatype List ((nil) (cons (head Int) (tail List))))\
         (declare-const x List)",
    );
    let mut t = String::from("x");
    for _ in 0..n {
        src.push_str(&format!("(assert (not ((_ is nil) {t})))"));
        t = format!("(tail {t})");
    }
    src.push_str("(check-sat)");

    let start = std::time::Instant::now();
    let out = run_script(&src);
    let elapsed = start.elapsed();

    assert_eq!(out.last().map(String::as_str), Some("sat"));
    assert!(
        elapsed.as_secs() < 5,
        "n={n} Int-field chain took {elapsed:?}; pre-slice-42 baseline was 24.1s \
         and the post-fix target is milliseconds"
    );
}

/// Companion control: the same query shape with an uninterpreted field sort
/// never entered the shared set and was always fast. Pinning it here makes a
/// future regression attributable — if BOTH tests slow down the cause is not
/// the arith seam.
#[test]
fn uninterpreted_field_chain_is_fast() {
    let n = 24;
    let mut src = String::from(
        "(set-logic ALL)\
         (declare-sort U 0)\
         (declare-datatype List ((nil) (cons (head U) (tail List))))\
         (declare-const x List)",
    );
    let mut t = String::from("x");
    for _ in 0..n {
        src.push_str(&format!("(assert (not ((_ is nil) {t})))"));
        t = format!("(tail {t})");
    }
    src.push_str("(check-sat)");

    let start = std::time::Instant::now();
    let out = run_script(&src);
    let elapsed = start.elapsed();

    assert_eq!(out.last().map(String::as_str), Some("sat"));
    assert!(elapsed.as_secs() < 5, "control query took {elapsed:?}");
}
```

- [ ] **Step 2: Verify the gate catches the fault**

The guards are already committed by now, so `git stash` would only stash this new test — it would **not** reproduce the fault, and `git reset --hard` would destroy the test. Measure against a baseline worktree instead, leaving the working tree untouched:

```bash
BASE=$(git merge-base HEAD main)
git worktree add /tmp/slice42-baseline "$BASE"
cargo build --manifest-path /tmp/slice42-baseline/Cargo.toml -p shinri-cli --release
```

Then write the same n = 24 query to a file and time the baseline binary:

```bash
python3 - <<'PY'
src = ["(set-logic QF_DT)",
       "(declare-datatype List ((nil) (cons (head Int) (tail List))))",
       "(declare-const x List)"]
t = "x"
for _ in range(24):
    src.append(f"(assert (not ((_ is nil) {t})))")
    t = f"(tail {t})"
src.append("(check-sat)")
open("/tmp/slice42-deep24.smt2", "w").write("\n".join(src))
PY
time /tmp/slice42-baseline/target/release/shinri /tmp/slice42-deep24.smt2
```

Expected: `sat` in roughly **24 s**, confirming the gate's 5 s bound is a real fence and not vacuously satisfied. Then clean up:

```bash
git worktree remove /tmp/slice42-baseline
```

If the baseline finishes in well under 5 s, the test is not exercising the fault — fix the query shape before continuing.

- [ ] **Step 3: Run the new tests with the guards in place**

```bash
cargo nextest run -p shinri-solver -E 'test(int_field_chain_does_not_blow_up) or test(uninterpreted_field_chain_is_fast)'
```

Expected: PASS (2 tests), both in milliseconds.

- [ ] **Step 4: Run the DT⋈arith regression anchors**

```bash
cargo nextest run -p shinri-solver -E 'test(mixed_datatype_and_arith_unsat) or test(arith_lt_over_selector_unsat) or test(arith_le_over_selector_unsat) or test(arith_gt_over_selector_sat) or test(arith_ge_over_selector_unsat) or test(arith_wrapped_selector_unsat)'
```

Expected: PASS, 6 tests, verdicts unchanged. These are the queries where the shared set legitimately matters — if the guard were too aggressive they would flip.

- [ ] **Step 5: Format, lint, and commit**

```bash
cargo fmt --all
cargo clippy -p shinri-solver --all-targets -- -D warnings
git add crates/shinri-solver/tests/qfdt_e2e.rs
git commit -m "test(dt): slice42 T5 — e2e gate on the Int-field chain blowup

Pins the 24-deep Int-field chain under 5s (24.1s pre-slice) plus an
uninterpreted-field control, so a future regression is attributable to the
arith seam rather than to DT itself."
```

---

## Task 6: Full verification gates

No production code. This task runs the gates that the change's blast radius demands and adjudicates any flip.

**Files:** none modified unless a gate demands a fix.

**Interfaces:**
- Consumes: everything from Tasks 1–5.

- [ ] **Step 1: Run the full workspace test suite**

```bash
mise run test
```

Expected: PASS, ~5 min. This is the fast gate; the 5 `shinri-fp` exhaustives stay `#[ignore]`d.

- [ ] **Step 2: Run the FULL unfiltered oracle differential**

```bash
cargo nextest run -p shinri-solver --features oracle
```

**Do not add `-E`.** A filtered run on slice 40 skipped `qfs_differential` and nearly shipped a Sat→Unknown regression; this change touches the same shared arith path and, per spec §4.A, the **string** path is in its blast radius too. Record the discovered test count from the output and confirm it is non-zero — a flagless or over-filtered run compiles to 0 tests and proves nothing.

Expected: PASS with a non-zero count.

- [ ] **Step 3: Run `script_e2e` and adjudicate any flips**

```bash
cargo nextest run -p shinri-solver -E 'test(script_e2e)'
```

(`mise run test` is `cargo nextest run --all` and does not forward a filter, so invoke `cargo nextest` directly here. `script_e2e` lives at `crates/shinri-solver/tests/script_e2e.rs`.)

Expected: no flips. If any appear, adjudicate strictly by direction (spec §5):

| Flip | Action |
|---|---|
| `unknown` → `sat`/`unsat` | **Permitted** (§4.A) — a budget-limited string-path query now finishes. Confirm the new verdict against z3 **and** cvc5 before updating the pin, and note the adjudication in the commit message. |
| `sat` ↔ `unsat` | **Regression. Stop and diagnose** — the guard dropped a real deduction. |
| decided → `unknown` | **Regression. Stop and diagnose.** |

- [ ] **Step 4: Confirm the measured win**

Re-measure the shape from spec §1 and record actual numbers for the PR description:

```bash
cargo build -p shinri-cli --release
```

Then build and time the n = 12/16/20/24 Int-field chains (same shape as Task 5's test). Expected: all in milliseconds, against the recorded baseline of 0.76 s / 3.1 s / 9.4 s / 24.1 s.

- [ ] **Step 5: Final format and lint over the whole workspace**

```bash
cargo fmt --all
mise run lint
```

Expected: both clean. CI gates on `fmt --check` and fails fast.

- [ ] **Step 6: Commit any gate-driven fixes and open the PR**

```bash
git add -A
git commit -m "chore(arith): slice42 T6 — full gates green

mise run test, full unfiltered oracle (non-zero count confirmed), script_e2e
with no regressive flips, fmt and clippy clean."
git push -u origin slice42-unconstrained-shared-probes
gh pr create --fill
```

Merge with a merge commit once CI is green, then delete the branch remote and local.

---

## Self-Review

**Spec coverage:**

| Spec section | Task |
|---|---|
| §3.A constrainedness tracking, four entry points | Task 1, Steps 3–9 |
| §3.A monotone across `pop` | Task 1, Step 1 (`constrained_marking_survives_pop`) |
| §3.B guard at candidate construction, before `define_slack` | Task 3, Step 3 |
| §3.B "no slack minted" fence | Task 3, Step 1 |
| §3.C MBTC guard | Task 4 |
| §4 invariant + exhaustiveness audit as its own task | Task 2 |
| §4.A permitted `unknown` → decided flip | Task 6, Step 3 |
| §5 unit tests (all six bullets) | Tasks 1, 3, 4 |
| §5 DT⋈arith e2e anchors | Task 5, Step 4 |
| §5 performance gate | Task 5 |
| §5 full unfiltered oracle | Task 6, Step 2 |
| §5 `script_e2e` | Task 6, Step 3 |
| §5 standing gates | every task's final step + Task 6, Step 5 |
| §7 success criteria | Task 5 (perf), Task 6 (no regressive flips), Task 2 (audit recorded) |

**Type consistency:** `mark_constrained(&mut self, v: ArithVar)` and `is_constrained(&self, v: ArithVar) -> bool` are defined once (Task 1, Step 5) and called with those exact signatures in Tasks 1, 3, and 4. `items[i].1` is an `ArithVar` per `let mut items: Vec<(TermId, ArithVar)>` at `lib.rs:581` and `lib.rs:672`. The test helper is named `int_var_no` throughout to avoid colliding with the unrelated `int_var` private to `mod rounding_tests` (`lib.rs:2551`), which is not in scope in `mod nelson_oppen_tests`.

**Placeholder scan:** no TBD/TODO; every code step carries the full replacement text; every command carries its expected outcome.
