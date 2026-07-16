# Slice 26 — Leaf-Membership Length-Seam Termination Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Constant-regex memberships over free leaf string variables decide Sat via model repair instead of churning the string↔arith length seam to the fuel fence — flipping the constant-on-left `str.<`/`str.<=` order pins (and the membership cells behind them) from Unknown to decided.

**Architecture:** Three coordinated changes per the spec
(`docs/superpowers/specs/2026-07-16-shinri-slice26-leaf-membership-length-seam-design.md`):
(a) `regex.rs` gains `min_len`/`max_len` (sound length bounds on a `Rex`) and
`search_shortest` (capped BFS for a shortest accepted word); (b) `memb.rs`
gains a general LEAF carve-out arm — a lone repair-eligible leaf residual
with any const `cur` (other than the bare-`Range` sibling arm, `Empty`, and
`Eps`) is never unfolded by Rule S/E; instead a guarded
`lit → min_len ≤ len ≤ max_len` axiom is emitted and the atom is left for
Rule G / model repair; (c) `model.rs`'s `memb_seeds` falls back from
`search_word(goal, n)` to `search_shortest(goal)`, subsuming the slice-25
amendment-1 length-1 bump. Soundness never rests on the search: seeds are
candidates re-verified by the post-solve self-check.

**Tech Stack:** Rust workspace (`crates/shinri-str`, `crates/shinri-solver`); z3 on PATH (mise-provisioned) for the differential oracle.

## Global Constraints

- Scope fence (spec): NO changes to `order.rs`, `fuel.rs`, the word-equation engine (`wordeq.rs`), the SAT budgets, or the bare-`Range` leaf arm in `memb.rs` (`memb.rs:222-287` stays byte-for-byte).
- `crates/shinri-solver/tests/qfs_differential.rs` is `#![cfg(feature = "oracle")]` — **every** test command against it MUST carry `--features oracle` (without it, 0 tests run silently) and MUST run **foreground with captured output** (`-- --nocapture`), never backgrounded.
- Do NOT run `cargo test --workspace` (≈50 min; shinri-fp exhaustive). Iterate per-crate: `cargo test -p shinri-str`, plus the oracle file.
- CI gates on `cargo fmt --check` and clippy: run `cargo fmt --all` before every commit and `cargo clippy --workspace --all-targets` in the final task.
- Commit message house style: `feat(str): … (slice 26)`, `test(str): … (slice 26)`, `docs: … (slice 26)`. Commits go to a feature branch `slice26-leaf-membership-length-seam`; plan+spec docs ride main (spec already committed, `336de21`).
- Soundness posture (spec): every new decisive path is candidate-only; a failed search leaves the variable un-seeded (`""`-fill → self-check → sound Unknown). No new hard verdicts except arith conflicts from the tautological length-bounds axiom.

---

### Task 0: Branch setup

**Files:** none (git only)

- [ ] **Step 1: Create the feature branch**

```bash
cd /workspace && git checkout -b slice26-leaf-membership-length-seam
```

Expected: `Switched to a new branch 'slice26-leaf-membership-length-seam'`

---

### Task 1: `regex.rs` — `min_len` / `max_len`

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (add two functions after `nullable`, which ends at `regex.rs:251`; add tests in the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `Rex` enum (`regex.rs:57-72`: `Empty | Eps | Range(u32,u32) | Concat(Vec<Rex>) | Union(Vec<Rex>) | Inter(Vec<Rex>) | Star(Box<Rex>) | Comp(Box<Rex>) | Loop(Box<Rex>, u32, u32)`).
- Produces: `pub(crate) fn min_len(r: &Rex) -> u32` and `pub(crate) fn max_len(r: &Rex) -> Option<u32>`. Task 4 (memb.rs) calls both; Task 2's tests may use `min_len`.

- [ ] **Step 1: Write the failing tests**

Add to the `tests` module in `regex.rs` (it has `use super::*` in effect — pattern-match the existing `search_word_finds_and_bounds` test):

```rust
    #[test]
    fn min_max_len_bounds() {
        let sigma = Rex::Range(0, MAX_CODE);
        let sigma_star = star(Rex::Range(0, MAX_CODE));
        let b = Rex::Range('b' as u32, 'b' as u32);
        let c = Rex::Range('c' as u32, 'c' as u32);
        // The strict-< gadget arm: b·Σ·Σ* — min 2, no upper bound.
        let strict = concat(vec![b.clone(), sigma.clone(), sigma_star.clone()]);
        assert_eq!(min_len(&strict), 2);
        assert_eq!(max_len(&strict), None);
        // The full order gadget: Range(c,MAX)·Σ* ∪ b·Σ·Σ* — min 1 (above arm).
        let above = concat(vec![Rex::Range('c' as u32, MAX_CODE), sigma_star.clone()]);
        let gadget = union(vec![above, strict.clone()]);
        assert_eq!(min_len(&gadget), 1);
        assert_eq!(max_len(&gadget), None);
        // Finite concat: b·Σ·Σ — exactly [3,3].
        let finite = concat(vec![b.clone(), sigma.clone(), sigma.clone()]);
        assert_eq!(min_len(&finite), 3);
        assert_eq!(max_len(&finite), Some(3));
        // Bare range: the degenerate [1,1] (the sibling leaf arm's axiom).
        assert_eq!(min_len(&b), 1);
        assert_eq!(max_len(&b), Some(1));
        // Word via concat of ranges: "bc" then Σ* — min 2, unbounded.
        let bc_star = concat(vec![b.clone(), c.clone(), sigma_star.clone()]);
        assert_eq!(min_len(&bc_star), 2);
        assert_eq!(max_len(&bc_star), None);
        // Nullable shapes: 0.
        assert_eq!(min_len(&sigma_star), 0);
        assert_eq!(max_len(&sigma_star), None);
        assert_eq!(min_len(&Rex::Eps), 0);
        assert_eq!(max_len(&Rex::Eps), Some(0));
        // Comp is conservative: [0, None] — sound, not exact.
        assert_eq!(min_len(&comp(b.clone())), 0);
        assert_eq!(max_len(&comp(b.clone())), None);
        // Inter: min is the MAX of arm minima; max is the MIN of finite arm maxima.
        let i = inter(vec![strict.clone(), finite.clone()]);
        assert_eq!(min_len(&i), 3);
        assert_eq!(max_len(&i), Some(3));
        // Loop: r{2,4} over a single char.
        let l = loop_(b.clone(), 2, 4);
        assert_eq!(min_len(&l), 2);
        assert_eq!(max_len(&l), Some(4));
        // Union with an unbounded arm has no finite max.
        assert_eq!(max_len(&union(vec![b.clone(), sigma_star])), None);
    }
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
cargo test -p shinri-str min_max_len_bounds
```

Expected: compile FAILURE — `cannot find function min_len in this scope`.

- [ ] **Step 3: Implement `min_len` / `max_len`**

Insert directly after `nullable` (after `regex.rs:251`):

```rust
/// Sound LOWER bound on accepted-word length: every `w ∈ L(r)` has
/// `|w| ≥ min_len(r)`. Exact for the range/concat/union/inter/star/loop
/// shapes the membership pass mints; conservative (0) for `Comp`. `Empty`
/// returns 0 — vacuously sound (L = ∅); the memb.rs leaf arm never consults
/// it for `Empty` (excluded there so the Rule-E conflict path keeps firing).
pub(crate) fn min_len(r: &Rex) -> u32 {
    match r {
        Rex::Empty | Rex::Eps | Rex::Star(_) | Rex::Comp(_) => 0,
        Rex::Range(..) => 1,
        Rex::Concat(ps) => ps.iter().map(min_len).fold(0u32, u32::saturating_add),
        Rex::Union(ps) => ps.iter().map(min_len).min().unwrap_or(0),
        Rex::Inter(ps) => ps.iter().map(min_len).max().unwrap_or(0),
        Rex::Loop(inner, lo, _) => min_len(inner).saturating_mul(*lo),
    }
}

/// Sound UPPER bound: `Some(k)` ⟹ every `w ∈ L(r)` has `|w| ≤ k`; `None`
/// when no finite bound is known (star, comp, or any unbounded part). For
/// `Inter` the MIN of the finite arm bounds is sound (a word must satisfy
/// every arm); for `Union`/`Concat` one unbounded arm forfeits the bound.
pub(crate) fn max_len(r: &Rex) -> Option<u32> {
    match r {
        Rex::Empty | Rex::Eps => Some(0),
        Rex::Range(..) => Some(1),
        Rex::Star(_) | Rex::Comp(_) => None,
        Rex::Concat(ps) => ps
            .iter()
            .map(max_len)
            .try_fold(0u32, |a, b| Some(a.saturating_add(b?))),
        Rex::Union(ps) => ps.iter().map(max_len).try_fold(0u32, |a, b| Some(a.max(b?))),
        Rex::Inter(ps) => ps.iter().filter_map(max_len).min(),
        Rex::Loop(inner, _, hi) => max_len(inner).map(|m| m.saturating_mul(*hi)),
    }
}
```

- [ ] **Step 4: Run the test to verify it passes**

```bash
cargo test -p shinri-str min_max_len_bounds
```

Expected: `test regex::tests::min_max_len_bounds ... ok`

- [ ] **Step 5: Commit**

```bash
cargo fmt --all && git add crates/shinri-str/src/regex.rs && git commit -m "feat(str): min_len/max_len sound length bounds on Rex (slice 26)"
```

---

### Task 2: `regex.rs` — `search_shortest`

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (add one function directly after `search_word`, which ends at `regex.rs:572`; tests in the same `tests` module)

**Interfaces:**
- Consumes: `nullable`, `deriv`, `next_classes` (`regex.rs:367`), `node_count`, `MEMB_SEARCH_STEP_CAP` (`regex.rs:335`), `FUEL_NODE_CAP` (`regex.rs:40`), `SURR_LO`/`SURR_HI` (`regex.rs:337-338`), `FxHashSet` (already imported for `search_word`).
- Produces: `pub(crate) fn search_shortest(r: &Rex) -> Option<String>`. Task 3 (model.rs) calls it.

- [ ] **Step 1: Write the failing tests**

```rust
    #[test]
    fn search_shortest_finds_minimal_words() {
        let sigma = Rex::Range(0, MAX_CODE);
        let sigma_star = star(Rex::Range(0, MAX_CODE));
        let b = Rex::Range('b' as u32, 'b' as u32);
        let c = Rex::Range('c' as u32, 'c' as u32);
        // b·Σ·Σ*: shortest word has exactly 2 chars and is a member.
        let strict = concat(vec![b.clone(), sigma.clone(), sigma_star.clone()]);
        let w = search_shortest(&strict).unwrap();
        assert_eq!(w.chars().count(), 2);
        assert_eq!(eval_membership(&w, &strict), Some(true));
        // Union with a trivially-short arm: (bc·Σ* ∪ "q") → the length-1 arm.
        let bc_star = concat(vec![b.clone(), c.clone(), sigma_star.clone()]);
        let q = Rex::Range('q' as u32, 'q' as u32);
        let u = union(vec![bc_star, q]);
        let wq = search_shortest(&u).unwrap();
        assert_eq!(wq, "q");
        // Nullable goal: the shortest word is ε.
        assert_eq!(search_shortest(&sigma_star), Some(String::new()));
        // Empty intersection: no word at any length — None, terminating.
        let empty = inter(vec![b.clone(), c.clone()]);
        assert_eq!(search_shortest(&empty), None);
        // Rex::Empty: None.
        assert_eq!(search_shortest(&Rex::Empty), None);
        // Pure-surrogate language: no Rust witness — None (skipped classes).
        assert_eq!(search_shortest(&Rex::Range(0xD800, 0xDFFF)), None);
    }
```

- [ ] **Step 2: Run to verify failure**

```bash
cargo test -p shinri-str search_shortest_finds_minimal_words
```

Expected: compile FAILURE — `cannot find function search_shortest`.

- [ ] **Step 3: Implement `search_shortest`**

Insert directly after `search_word`'s closing brace (`regex.rs:572`):

```rust
/// The SHORTEST word in L(r), or None if none is found within
/// `MEMB_SEARCH_STEP_CAP` expanded states (an abort is NOT a verdict — the
/// caller leaves the variable un-seeded and the post-solve self-check
/// backstops, exactly like `search_word`). Breadth-first over
/// next-character classes, so the first nullable state reached sits at the
/// minimal length; per class the witness char is the smallest non-surrogate
/// code point (pure-surrogate classes are skipped — sound: completeness
/// only). Visited Rex states are memoized globally: re-reaching a state at
/// a longer prefix can only yield longer words, so it is skipped.
pub(crate) fn search_shortest(r: &Rex) -> Option<String> {
    let mut steps = 0usize;
    let mut seen: FxHashSet<Rex> = FxHashSet::default();
    seen.insert(r.clone());
    let mut frontier: Vec<(Rex, String)> = vec![(r.clone(), String::new())];
    while !frontier.is_empty() {
        let mut next: Vec<(Rex, String)> = Vec::new();
        for (state, word) in frontier {
            if nullable(&state) {
                return Some(word);
            }
            if matches!(state, Rex::Empty) {
                continue;
            }
            if steps >= MEMB_SEARCH_STEP_CAP {
                return None;
            }
            steps += 1;
            let Some(classes) = next_classes(&state) else {
                continue;
            };
            for (lo, hi) in classes {
                let c = if (SURR_LO..=SURR_HI).contains(&lo) {
                    if hi > SURR_HI {
                        SURR_HI + 1
                    } else {
                        continue; // pure-surrogate class: no Rust witness
                    }
                } else {
                    lo
                };
                let d = deriv(c, &state);
                if node_count(&d) > FUEL_NODE_CAP {
                    continue;
                }
                if seen.insert(d.clone()) {
                    let mut w = word.clone();
                    w.push(char::from_u32(c).expect("non-surrogate in-alphabet"));
                    next.push((d, w));
                }
            }
        }
        frontier = next;
    }
    None
}
```

- [ ] **Step 4: Run to verify pass, plus the whole regex module**

```bash
cargo test -p shinri-str search_shortest_finds_minimal_words && cargo test -p shinri-str regex::
```

Expected: new test `ok`; all existing `regex::tests` still `ok`.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all && git add crates/shinri-str/src/regex.rs && git commit -m "feat(str): search_shortest — capped BFS for a shortest accepted word (slice 26)"
```

---

### Task 3: `model.rs` — seed fallback (cashes the re-banked repair item)

**Files:**
- Modify: `crates/shinri-str/src/model.rs:470-491` (the tail of `memb_seeds`)
- Tests: same file's `tests` module (existing slice-25 amendment-1 tests at `model.rs:538-616` must stay green unmodified)

**Interfaces:**
- Consumes: `regex::search_word(&Rex, usize) -> Option<String>` (existing), `regex::search_shortest(&Rex) -> Option<String>` (Task 2).
- Produces: no signature change — `memb_seeds` behavior only. Later tasks rely on: a free leaf whose goal is non-nullable with min length k now gets a length-k witness.

- [ ] **Step 1: Write the failing tests**

Add to `model.rs` tests, patterned on `memb_seed_wide_straddling_range_gets_length_one_witness` (`model.rs:541`):

```rust
    #[test]
    fn memb_seed_min_len_two_goal_gets_shortest_witness() {
        // Slice 26: `x ∈ "b"·Σ·Σ*` (the strict-< proper-prefix gadget arm)
        // over a fully-free leaf — no length constraint, so the model length
        // reads 0 and `search_word(goal, 0)` fails (non-nullable). The
        // shortest-word fallback must produce a length-2 member. Subsumes
        // the slice-25 amendment-1 length-1 bump (whose pins stay green).
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let sigma = crate::regex::Rex::Range(0, crate::regex::MAX_CODE);
        let goal = crate::regex::concat(vec![
            crate::regex::Rex::Range('b' as u32, 'b' as u32),
            sigma.clone(),
            crate::regex::star(sigma),
        ]);
        let re_t = crate::regex::rex_to_term(&mut ctx, &goal);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let m = ModelBuilder::default(); // no len(x) pinned -> model length 0.
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        let w = seeds
            .get(&x)
            .expect("min-len-2 star-tail leaf must get a shortest witness");
        assert_eq!(w.chars().count(), 2);
        assert_eq!(crate::regex::eval_membership(w, &goal), Some(true));
    }

    #[test]
    fn memb_seed_union_easy_arm_gets_witness() {
        // Slice 26: `x ∈ (bc·Σ* ∪ "q")` — the union-poisoning probe cell.
        // The shortest-word fallback finds the trivially-sat length-1 arm.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let sigma_star = crate::regex::star(crate::regex::Rex::Range(0, crate::regex::MAX_CODE));
        let goal = crate::regex::union(vec![
            crate::regex::concat(vec![
                crate::regex::Rex::Range('b' as u32, 'b' as u32),
                crate::regex::Rex::Range('c' as u32, 'c' as u32),
                sigma_star,
            ]),
            crate::regex::Rex::Range('q' as u32, 'q' as u32),
        ]);
        let re_t = crate::regex::rex_to_term(&mut ctx, &goal);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let m = ModelBuilder::default();
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        assert_eq!(seeds.get(&x).map(String::as_str), Some("q"));
    }
```

Note: `regex::concat`/`union`/`star`/`eval_membership`/`MAX_CODE` are
`pub(crate)` — reachable as `crate::regex::…` from `model.rs` tests.

- [ ] **Step 2: Run to verify failure**

```bash
cargo test -p shinri-str memb_seed_min_len_two_goal_gets_shortest_witness memb_seed_union_easy_arm
```

Expected: both FAIL on the `expect(...)` unwrap — no seed produced (pre-fix, `n == 0` bumps to 1, and `search_word(goal, 1)` finds nothing for a min-len-2 goal; the union test fails only under the pre-fix bump if "q" is found at n=1 — if it passes pre-fix, note that in the commit message and keep it as a pin).

- [ ] **Step 3: Implement the fallback**

In `memb_seeds`, replace the block at `model.rs:470-491` — everything from
`let mut n = class_len_in_model(…)` through the `search_word` call — with:

```rust
        let n = class_len_in_model(terms, eq, known, m, v);
        let goal = regex::inter(rexes);
        // Try the model length first: `n` comes from the arith model, so it
        // respects every genuinely-asserted length pin. It can still fail —
        // a fully-free variable reads 0 here, and the slice-26 leaf axiom is
        // a LOWER bound only, so arith may pick any feasible length the goal
        // cannot realize (parity-constrained languages, arbitrary slack). On
        // failure fall back to the SHORTEST accepted word (slice 26 —
        // subsumes the slice-25 amendment-1 length-1 bump: a nullable goal
        // at n=0 still resolves to "" via `search_word`, a non-nullable one
        // falls through to its true minimal witness). Seeds are only ever
        // CANDIDATES re-checked by the post-solve self-check against every
        // assertion, so a fallback seed that violates a real length pin can
        // only fall back to the prior sound Unknown, never fabricate a
        // wrong Sat.
        if let Some(w) =
            regex::search_word(&goal, n).or_else(|| regex::search_shortest(&goal))
        {
            out.insert(v, w);
        }
```

(The `if n == 0 && !regex::nullable(&goal) { n = 1 }` bump and its comment
are deleted; `n` is no longer `mut`.)

- [ ] **Step 4: Run the new tests AND the slice-25 amendment-1 pins**

```bash
cargo test -p shinri-str memb_seed
```

Expected: ALL `memb_seed_*` tests pass — the three slice-25 pins
(`…wide_straddling_range…`, `…wide_range_over_256…`,
`…nullable_goal_at_zero_length_unchanged`) stay green (the shortest word of
a bare non-nullable Range is length 1; the nullable goal still yields `""`).

- [ ] **Step 5: Run the full str crate**

```bash
cargo test -p shinri-str
```

Expected: all pass (nothing upstream consumes the bump).

- [ ] **Step 6: Commit**

```bash
cargo fmt --all && git add crates/shinri-str/src/model.rs && git commit -m "feat(str): memb_seeds shortest-word fallback replaces the length-1 bump (slice 26)"
```

---

### Task 4: `memb.rs` — the general leaf carve-out arm

**Files:**
- Modify: `crates/shinri-str/src/memb.rs` — insert the new arm immediately after the bare-`Range` arm's closing brace (`memb.rs:287`, i.e. after its final `continue;`), BEFORE the comment block at `memb.rs:289`. The bare-`Range` arm itself is untouched.
- Tests: same file's `tests` module — two new tests; two existing tests get a carrier truth-up (below).

**Interfaces:**
- Consumes: `regex::min_len` / `regex::max_len` (Task 1), `side_clean` (same call shape as `memb.rs:266`), `emit_split` (`memb.rs:75`), `s.emitted_len_axioms`, `wordeq::len_of`, `cx.terms.mk_numeral` / `mk_app` (patterns at `memb.rs:270-284`), `TermNode`/`Op` (already imported).
- Produces: behavioral contract for Tasks 5-6 — a lone-leaf membership with const non-`Range`/non-`Empty`/non-`Eps` `cur` emits only guarded length-bound clauses and never unfolds.

- [ ] **Step 1: Write the failing tests**

Add to `memb.rs` tests (pattern: `bare_range_leaf_emits_guarded_len1_axiom`, `memb.rs:770`):

```rust
    #[test]
    fn lone_leaf_star_tail_carves_out_with_min_len_axiom() {
        // Slice 26: x ∈ "b"·Σ·Σ* over a lone free leaf — the general LEAF
        // carve-out. NO Rule-S/E split ever fires (no skolems, no seam
        // churn); exactly ONE guarded [(>= (str.len x) 2)] clause (star
        // tail ⇒ no finite upper bound); then saturate to the model-repair
        // path.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let sigma = Rex::Range(0, regex::MAX_CODE);
        let r = regex::concat(vec![
            Rex::Range('b' as u32, 'b' as u32),
            sigma.clone(),
            regex::star(sigma),
        ]);
        let m = memb_atom(&mut ctx, x, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(
            matches!(terminal, TCheck::Sat),
            "leaf saturates to the model-repair path"
        );
        let is_memb = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        assert!(
            splits
                .iter()
                .all(|(a, _)| !a.iter().any(|&t| is_memb(cx.terms, t))),
            "leaf carve-out must never emit an S/E membership split"
        );
        let is_ge = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Ge),
                    ..
                }
            )
        };
        let is_le = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Le),
                    ..
                }
            )
        };
        let ge_splits: Vec<_> = splits
            .iter()
            .filter(|(a, g)| *g && a.len() == 1 && is_ge(cx.terms, a[0]))
            .collect();
        assert_eq!(
            ge_splits.len(),
            1,
            "exactly one guarded [(>= len 2)] lower-bound clause"
        );
        assert!(
            !splits
                .iter()
                .any(|(a, g)| *g && a.len() == 1 && is_le(cx.terms, a[0])),
            "star tail has no finite upper bound — no guarded le clause"
        );
    }

    #[test]
    fn lone_leaf_finite_concat_emits_both_bounds() {
        // Slice 26: x ∈ [a-c]·"b" — the shape the old Rule-S clause test
        // used. Now a LEAF: two guarded single-atom bound clauses
        // ([(>= len 2)] and [(<= len 2)]) across successive rounds, no
        // S-splits, terminal Sat.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let r = regex::concat(vec![
            Rex::Range('a' as u32, 'c' as u32),
            regex::lit_test("b"),
        ]);
        let m = memb_atom(&mut ctx, x, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(terminal, TCheck::Sat));
        let is_memb = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        assert!(
            splits
                .iter()
                .all(|(a, _)| !a.iter().any(|&t| is_memb(cx.terms, t))),
            "finite lone-leaf membership must not unfold either"
        );
        let is_cmp = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Ge | BuiltinOp::Le),
                    ..
                }
            )
        };
        let bound_splits: Vec<_> = splits
            .iter()
            .filter(|(a, g)| *g && a.len() == 1 && is_cmp(cx.terms, a[0]))
            .collect();
        assert_eq!(bound_splits.len(), 2, "ge + le bound clauses, one each");
    }
```

- [ ] **Step 2: Run to verify failure**

```bash
cargo test -p shinri-str lone_leaf
```

Expected: both FAIL — pre-fix, Rule S fires on the head-forced concats, so
the no-`StrInRe`-split assertions trip.

- [ ] **Step 3: Implement the carve-out arm**

Insert at `memb.rs:288` (immediately after the bare-`Range` arm's closing
brace, before the `// Residual: nf[i..] with a variable head.` comment
block):

```rust
        // ── Slice 26: general const-Rex LEAF carve-out ───────────────────
        // A LONE repair-eligible leaf residual (single NF atom, nullary
        // uninterpreted — the same shape `memb_seeds` requires; a class
        // holding a constant or concat never reaches here, deep NF resolves
        // it and Rule G consumes it) with any const `cur` is the GROUND-OUT
        // point of the unfolding, exactly like the bare-`Range` arm above:
        // Rule S/E on it mints fresh skolems whose `str.len` companions
        // flood the string↔arith seam every round until the shared fuel
        // dies in the length-axiom loop (`lib.rs::check`) — a hard Unknown
        // BEFORE model repair can ever search a witness (the slice-26 root
        // cause). Skip unfolding: emit the guarded tautology
        // `lit → min_len(cur) ≤ len(residual) [≤ max_len(cur) if finite]`
        // (bounds are sound by construction — `regex::min_len`/`max_len`
        // doc), deduped via `emitted_len_axioms`, one clause per round, same
        // posture as the sibling arm; then leave the atom in `memb_true`
        // for Rule G / `memb_seeds` / the post-solve self-check. `Empty`
        // and `Eps` are excluded so the existing decisive paths (Rule-E
        // conflict on ∅, ε-forcing) keep firing; `Range` took the sibling
        // arm. Mints NO concat — repair eligibility untouched.
        let lone_leaf = nf.len() - i == 1
            && matches!(
                cx.terms.term_node(nf[i]),
                shinri_core::TermNode::App { op: Op::Uninterpreted(_), args, .. }
                    if cx.terms.children(*args).is_empty()
            );
        if lone_leaf && !matches!(cur, Rex::Empty | Rex::Eps) {
            if !side_clean(cx.eq, cx.terms, t, input_cond_roots) {
                continue;
            }
            let residual = nf[i];
            let lr = wordeq::len_of(cx.terms, residual);
            let guard = Some(lit.negate());
            let mut bounds: Vec<TermId> = Vec::new();
            let lo = regex::min_len(&cur);
            if lo > 0 {
                let k = cx.terms.mk_numeral(
                    shinri_core::Rational::from_int(i128::from(lo).into()),
                    cx.terms.int_sort(),
                );
                bounds.push(
                    cx.terms
                        .mk_app(Op::Builtin(BuiltinOp::Ge), &[lr, k])
                        .expect("(>= len k) well-sorted"),
                );
            }
            if let Some(hi) = regex::max_len(&cur) {
                let k = cx.terms.mk_numeral(
                    shinri_core::Rational::from_int(i128::from(hi).into()),
                    cx.terms.int_sort(),
                );
                bounds.push(
                    cx.terms
                        .mk_app(Op::Builtin(BuiltinOp::Le), &[lr, k])
                        .expect("(<= len k) well-sorted"),
                );
            }
            for b in bounds {
                if s.emitted_len_axioms.contains(&b) {
                    continue;
                }
                s.emitted_len_axioms.insert(b);
                return Some(emit_split(s, cx.terms, vec![b], guard));
            }
            continue;
        }
```

Notes for the implementer: `Rex` must be in scope in `memb_check` (the file
already matches `Rex::Range(..)` at `memb.rs:247`, so it is). If
`BuiltinOp::Ge`/`Le` need importing, extend the existing `shinri_core` use
list at the top of the file. Do NOT touch the bare-`Range` arm above the
insertion point.

- [ ] **Step 4: Run the new tests**

```bash
cargo test -p shinri-str lone_leaf
```

Expected: both PASS.

- [ ] **Step 5: Truth-up the two Rule-S/E clause-shape tests (carrier change)**

Run the full memb suite first to see the expected failures:

```bash
cargo test -p shinri-str memb::
```

Expected failures: exactly `rule_e_expansion_shape` and
`rule_s_head_split_clause_sequence` — both use a LONE leaf carrier `x`,
which the carve-out now intercepts (no expansion/S splits). All other memb
tests (bare-range leaf, fuel saturation, ground conflict/discharge,
negative polarity, empty-language conflict) must still pass; any OTHER
failure is a finding to investigate, not to wave through.

Truth-up both tests to a TWO-ATOM carrier `x·y` (a multi-atom residual is
not a lone leaf, so Rule S/E still fire — the rules themselves are
unchanged and still need their shape pins). In `rule_e_expansion_shape`
(`memb.rs:596`), replace the setup lines

```rust
        let x = var(&mut ctx, "x");
        let r = regex::star_range_test('a', 'c');
        let m = memb_atom(&mut ctx, x, &r);
```

with

```rust
        // Slice 26 carrier truth-up: a LONE leaf x now takes the leaf
        // carve-out (no Rule-E expansion), so pin Rule E's shape on a
        // two-atom carrier x·y, which is not repair-eligible.
        let x = var(&mut ctx, "x");
        let y = var(&mut ctx, "y");
        let xy = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let r = regex::star_range_test('a', 'c');
        let m = memb_atom(&mut ctx, xy, &r);
```

and replace the membership-disjunct assertion `assert_eq!(mt, x);`
(`memb.rs:645`) with `assert_eq!(mt, xy);`. The ε-disjunct assertion
(`x = ""` sides) is shape-generic (checks a `""` side) and stays.

In `rule_s_head_split_clause_sequence` (`memb.rs:654`), make the same
carrier change (add `y`, build `xy`, pass `xy` to `memb_atom`). Rule S
peels `residual_atoms[0]`, which is still `x`, so every existing assertion
(S1 equalities on `x`; S3/S4 memberships on fresh witnesses `≠ x`) holds
verbatim — only the setup lines change. Update the test's header comment to
note the slice-26 carrier truth-up.

- [ ] **Step 6: Run the full str crate**

```bash
cargo test -p shinri-str
```

Expected: all pass.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all && git add crates/shinri-str/src/memb.rs && git commit -m "feat(str): general const-Rex leaf carve-out — no S/E unfolding on repair-eligible leaves (slice 26)"
```

---

### Task 5: e2e pins — flip the known gap, pin the membership cells

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` — retire `targeted_str_order_single_char_left_free_known_gap` (`:3902`), add new targeted tests next to it.

**Interfaces:**
- Consumes: `expect(src, Verdict)` and `shinri_verdict(src) -> Verdict` helpers (same file, `:2543` / `:82`); Tasks 1-4 landed.
- Produces: the pins Task 6's oracle adjudication treats as fixed points.

- [ ] **Step 1: Replace the known-gap pin with deciding pins**

Replace the entire `targeted_str_order_single_char_left_free_known_gap` test (`memb.rs`-adjacent comment included, `qfs_differential.rs:3901-3944`) with:

```rust
#[test]
fn targeted_str_order_single_char_left_free_now_decides() {
    // Slice 26 (leaf-membership length-seam termination): the four shapes
    // pinned Unknown since slice 25 — the strict-< proper-prefix gadget
    // (word("b")·Σ·Σ*) used to churn the string↔arith length seam to the
    // fuel fence before model repair could search a witness. The lone-leaf
    // carve-out (memb.rs) + shortest-word repair fallback (model.rs) now
    // decide them. z3-confirmed verdicts.
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.<= \"b\" s))(check-sat)",
        Verdict::Sat,
    );
    // len=1 is Sat too (z3-adjudicated during planning: the gadget's
    // above-arm Range(99,MAX)·Σ* admits the length-1 witness "c"; only the
    // PURE prefix-arm membership b·Σ·Σ* is Unsat at len 1 — pinned
    // separately in targeted_leaf_membership_min_len_conflict_unsat).
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))\
         (assert (= (str.len s) 1))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))\
         (assert (= (str.len s) 2))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))\
         (assert (= (str.len s) 3))(check-sat)",
        Verdict::Sat,
    );
}
```

Adjudication record (planning, z3 run 2026-07-16): the order shape with
`len(s)=1` is **sat** (witness `"c"` via the gadget's above-arm) and the
pure prefix-arm membership `s ∈ b·Σ·Σ* ∧ len(s)=1` is **unsat** — both
verified against z3 directly; the pins above and below encode exactly
those verdicts.

- [ ] **Step 2: Add the membership-cell pins**

Add directly after the test above:

```rust
#[test]
fn targeted_leaf_membership_star_tail_decides() {
    // Slice 26 membership-level cells (the mechanism behind the order
    // pins, str.< eliminated): min-len ≥ 2 shapes with star tails over a
    // free leaf. All z3-sat; all Unknown before the leaf carve-out.
    for re in [
        "(re.++ (str.to_re \"b\") re.allchar (re.* re.allchar))",
        "(re.++ (str.to_re \"bc\") (re.* re.allchar))",
        "(re.++ re.allchar re.allchar (re.* re.allchar))",
        "(re.++ (re.* re.allchar) (str.to_re \"b\") re.allchar)",
        "(re.++ (str.to_re \"b\") (re.range \"a\" \"z\") (re.* re.allchar))",
        "(re.++ (str.to_re \"b\") re.allchar (re.* (str.to_re \"x\")))",
        "(re.++ (str.to_re \"b\") (re.++ re.allchar (re.* re.allchar)))",
    ] {
        expect(
            &format!(
                "(set-logic QF_S)(declare-fun s () String)\
                 (assert (str.in_re s {re}))(check-sat)"
            ),
            Verdict::Sat,
        );
    }
    // Pinned length rescues too (the fuel used to die before repair saw it).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.++ (str.to_re \"b\") re.allchar (re.* re.allchar))))\
         (assert (= (str.len s) 2))(check-sat)",
        Verdict::Sat,
    );
    // Union with a trivially-sat arm no longer poisoned.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.union (re.++ (str.to_re \"bc\") (re.* re.allchar)) (str.to_re \"q\"))))\
         (check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_leaf_membership_min_len_conflict_unsat() {
    // Slice 26: the guarded lower-bound axiom (len ≥ 2 for b·Σ·Σ*) turns
    // an independently-asserted len(s)=1 into a direct arith conflict —
    // Unsat was already the verdict pre-slice (via churn-then-conflict);
    // it must survive the carve-out. z3: unsat.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.++ (str.to_re \"b\") re.allchar (re.* re.allchar))))\
         (assert (= (str.len s) 1))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_str_order_two_gadget_conjunction_decides() {
    // Slice 26: two order gadgets on one leaf — memb_seeds intersects all
    // of the leaf's Rexes, so ("b" < s) ∧ (s < "d") finds "c". z3: sat.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.< \"b\" s))(assert (str.< s \"d\"))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_leaf_membership_infinite_conflict_known_gap() {
    // KNOWN GAP (slice 26, banked): conflicting INFINITE leaf memberships
    // — s ∈ a·Σ* ∧ s ∈ b·Σ* (z3: unsat). The carve-out leaves both for
    // repair; the intersected goal is empty, no seed is found, and repair
    // can never produce Unsat — sound Unknown, same verdict as pre-slice.
    // Refutation needs Rex intersection-emptiness (banked non-goal §Non-
    // goals). A future slice should flip this to Unsat deliberately.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (str.in_re s (re.++ (str.to_re \"a\") (re.* re.allchar))))\
             (assert (str.in_re s (re.++ (str.to_re \"b\") (re.* re.allchar))))(check-sat)"
        ),
        Verdict::Unknown,
    );
}
```

- [ ] **Step 3: Run the targeted tests (foreground, oracle feature)**

```bash
cargo test -p shinri-solver --features oracle --test qfs_differential targeted_str_order -- --nocapture
cargo test -p shinri-solver --features oracle --test qfs_differential targeted_leaf_membership -- --nocapture
```

Expected: all pass. If any `expect` fails with a different verdict,
reproduce via the CLI (`/workspace/target/debug/shinri <file>`) and z3 on
the same script, adjudicate which side is right, and STOP (BLOCKED) if
shinri disagrees with z3 — that is a soundness finding, not a pin to edit.

- [ ] **Step 4: Run the neighboring slice-25 pins (regression fence)**

```bash
cargo test -p shinri-solver --features oracle --test qfs_differential targeted_ -- --nocapture
```

Expected: every `targeted_*` test passes — in particular
`targeted_str_order_single_char_left_free_len_pinned_decides`,
`targeted_str_order_single_char_right_decides`,
`targeted_straddling_range_membership_decides`,
`targeted_str_order_symbolic_pair_known_gap` (still Unknown), and
`targeted_regex_bare_range_multi_atom_residual_stays_unknown` (still
Unknown) are unchanged.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all && git add crates/shinri-solver/tests/qfs_differential.rs && git commit -m "test(str): flip left-free order pins to decided; pin slice-26 membership cells (slice 26)"
```

---

### Task 6: Oracle sweep, adjudication, truth-up, gates

**Files:**
- Modify: `docs/superpowers/specs/2026-07-16-shinri-slice26-leaf-membership-length-seam-design.md` (Status line + implementation-notes/truth-up section)
- No source changes expected; any adjudicated finding becomes a BLOCKED report, not a silent fix.

**Interfaces:**
- Consumes: all prior tasks landed and committed.
- Produces: recorded post-slice tallies; a green branch ready for PR.

- [ ] **Step 1: Run the order differential families (foreground)**

```bash
cargo test -p shinri-solver --features oracle --test qfs_differential qfs_str_order -- --nocapture 2>&1 | tail -40
```

Expected: 0 disagreements; the printed unknown tallies for
`qfs_str_order_matches_z3` (66 at slice-25 close) and
`qfs_str_order_single_char_matches_z3` drop substantially. Record the exact
numbers.

- [ ] **Step 2: Run the FULL differential file (foreground)**

```bash
cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture 2>&1 | tail -80
```

Expected: 62/62 (plus the new targeted tests) pass, 0 disagreements
anywhere. Compare per-family unknown tallies against the slice-25 truth-up:
movements must be **only** unknown→decided. Any decided→unknown,
sat↔unsat, or new disagreement is a finding: reproduce it standalone via
the CLI and z3, and report BLOCKED with both repros — do not adjust pins to
make it pass.

- [ ] **Step 3: Run the remaining solver tests and the str crate once more**

```bash
cargo test -p shinri-str && cargo test -p shinri-solver --features oracle
```

Expected: all pass (this covers `script_e2e.rs` and unit suites).

- [ ] **Step 4: Lint gates**

```bash
cargo fmt --all -- --check && cargo clippy --workspace --all-targets
```

Expected: no diffs, no warnings promoted to errors. Fix any clippy findings
in the new code only.

- [ ] **Step 5: Spec truth-up**

Edit the spec: change the Status line to
`Status: IMPLEMENTED (<date>). See "Implementation notes (truth-up)" at the end.`
and append an `## Implementation notes (truth-up)` section recording: the
commit list (`git log --oneline main..HEAD`), the exact post-slice unknown
tallies per family vs. their slice-25 baselines, the adjudicated z3 verdict
for the `len=1` order shape (Task 5 Step 1 note), and any deviations from
this plan (each marked user-approved or spec-consistent).

- [ ] **Step 6: Commit and open the PR**

```bash
cargo fmt --all && git add -A docs/ && git commit -m "docs: slice-26 spec truth-up (IMPLEMENTED) — leaf-membership length-seam termination (slice 26)"
git push -u origin slice26-leaf-membership-length-seam
gh pr create --title "Slice 26: leaf-membership length-seam termination" --body "See docs/superpowers/specs/2026-07-16-shinri-slice26-leaf-membership-length-seam-design.md (spec) and docs/superpowers/plans/2026-07-16-shinri-slice26-leaf-membership-length-seam.md (plan). Flips the constant-on-left str.< / str.<= free-variable pins to decided via the general const-Rex leaf carve-out + shortest-word repair fallback. Oracle: 0 disagreements; unknown tallies recorded in the truth-up."
```

Expected: PR opens against `main`.
