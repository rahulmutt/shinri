# Slice 62 — Length-consistent seeds and the compound-arithmetic gate Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the live wrong `sat` from compound length arithmetic the gate skips (slice-61 queue item 5), back it with a strict gate whenever a membership seed's length disagrees with the arith model, and teach arith the exact length bounds of a bare leaf's membership intersection so Norn `ab` 135/138 come back `sat` with valid models (queue item 3).

**Architecture:** Three independent changes plus one interface widening. (1) `Solver::eval_num_val` folds `+ - * neg` from its operands whenever they all evaluate. (2) `model::memb_seeds_flagged` reports a seed/model length mismatch and `model_with` turns it into `require_strict_check()`. (3) A new `regex::len_bounds` computes exact length bounds by a layered derivative walk, and a new module `leaf_bounds.rs` emits `¬m₁ ∨ … ∨ ¬mₖ ∨ bound` lemmas at the end of `memb_check`. (4) To state those lemmas, `TCheck::Split` / `FinalCheck::Split` / `TheoryResult::SplitAtoms` carry `guards: Vec<Lit>` instead of `guard: Option<Lit>`; the SAT arm orders a multi-guard clause so its watches are never two already-false guards. A base/after bench run and a report close the slice.

**Tech Stack:** Rust workspace (toolchain pinned in `mise.toml`), cargo-nextest 0.9.140, z3 from mise (oracle, via the existing `easy-smt` dev-dependency), `shinri-bench` for the SMT-LIB 2024 run, python3 for analysis scripts.

**Spec:** `docs/superpowers/specs/2026-10-06-shinri-slice62-length-consistent-seeds-design.md`

## Global Constraints

- Scope (spec §2, §5): no change to the parser, Rule G/S/E unfolding, the slice-26 per-atom carve-out and its dedup, the slice-28 emptiness conflict, joint seeds / R9, the reconciliation rebuild, `search_word`, `search_shortest`, fence names, `fence_detail` tags or the bench tool.
- `LEN_BOUND_DEPTH_CAP = 64` (spec §4.3). `MEMB_SEARCH_STEP_CAP` (10,000), `FUEL_NODE_CAP` (10,000) and `CLASS_SPLIT_CAP` keep their values.
- `len_bounds` returning `None` means "no lemma", never a verdict (spec §4.3).
- Group lemmas are guarded by **every** membership atom of the leaf group; dedup key is `(bound atom, sorted guard lits)` (spec §4.4).
- The interface migration (spec §4.5) is behaviour-neutral: `guard: None` → `guards: Vec::new()`, `guard: Some(g)` → `guards: vec![g]`. Clauses with 0 or 1 guard are built byte-for-byte as today.
- Existing tests keep their assertions. Allowed edits to existing tests: (a) the mechanical `guard`→`guards` syntax migration in Task 2; (b) the spec-sanctioned rewrite of `model_reject::tests::unevaluable_compound_len_arith` in Task 4. Any other existing-test failure: stop and report; do not edit it.
- `memb_seeds` keeps its signature (a wrapper over the new `memb_seeds_flagged`), so its existing tests are untouched.
- No new dependency of any kind (pure-Rust mandate).
- Oracle tests only run with `--features oracle`; without it they silently run 0 tests. Always confirm a non-zero discovered count (AGENTS.md).
- nextest filters use the expression form `-E 'test(<name>)'` / `-E 'binary(<name>)'` (AGENTS.md).
- `cargo fmt --all` before every commit; `mise run lint` (clippy `-D warnings`) must be clean.
- Bench base: slice 61's after runs `bench/results/slice61` and `bench/results/slice61-sample` (binary `f9fa4f9`). `target/` was cleaned, so Task 0 rebuilds the base binary from `main` (`cdb5630`, whose crate diff from `f9fa4f9` is comments only) into `target/slice62-base/shinri`, and re-creates the seed-59 sample corpus `target/slice59-sample-corpus`. After runs: `--timeout 20 --mem-mb 3072 --jobs 6`, detached with `setsid` under `taskset -c 12-23`.
- While a bench run is live, run builds and tests on cores 0–11 (`taskset -c 0-11 …`).
- Branch `slice62-length-consistent-seeds` off `main`; PR to `main`, merge commit when CI is green, then delete the branch remote and local (AGENTS.md). Ask the user before merging.

## Review Focus

1. **Two already-false guards as the clause's watched literals.** `add_learnt` (`crates/shinri-sat/src/solver.rs:451`) watches `lits[0]` and `lits[1]` as given. A clause `[¬m₁, ¬m₂, bound]` whose guards were falsified before emission would never notice `bound` going false. Expected: a multi-guard clause is ordered atoms first, then guards by descending level, and a violated group lemma is a conflict. Pinned in Task 2 (`two_guard_split_detects_violation`).
2. **A second branch with a different membership set on the same leaf.** Keyed only by the bound atom, the lemma learnt under `{m₁, m₂}` would suppress the one needed under `{m₁, m₃}`. Expected: both are emitted. Pinned in Task 3 (`group_dedup_key_includes_guards`).
3. **A finite language whose words reach one derivative state at two depths** (`(a|bb)c`). Expected: max 3, not 2 (cross-layer dedup would under-state it and emit an unsound `≤ 2`). Pinned in Task 1 (`len_bounds_cross_depth_state`).
4. **A length that reaches only an assertion the gate cannot evaluate** (a UF argument). `main` answers `sat ((x ""))` on `x ∈ (ab)*, f(len x) = 1, f(0) = 0, f(2) = 0, len x ≤ 3` (z3 `unsat`; verified on `cdb5630` while planning). Expected: not `sat`, while the satisfiable sibling (`f(2)` unconstrained) stays `sat`. Pinned in Task 6 (`uf_len_backstop_not_sat`, `uf_len_backstop_sat_sibling`).
5. **A negative membership in a leaf group** (`x ∉ R`). Expected: its complement joins the intersection and its literal (negative) contributes guard `lit.negate()`; bounds stay sound. Pinned in Task 3 (`negative_member_joins_group`) and swept by the oracle (Task 7 generates negative memberships).

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-str/src/regex.rs` | Modify | add `LEN_BOUND_DEPTH_CAP` and `len_bounds` (+ tests) |
| `crates/shinri-sat/src/types.rs` | Modify | `TheoryResult::SplitAtoms.guards: Vec<Lit>` |
| `crates/shinri-sat/src/solver.rs` | Modify | split arm pushes all guards; multi-guard watch order (+ test) |
| `crates/shinri-theory/src/solver_trait.rs`, `combiner.rs` | Modify | `TCheck::Split.guards`, `FinalCheck::Split.guards` |
| `crates/shinri-{arith,arrays,dt}/src/lib.rs`, `crates/shinri-str/src/{lib,memb,wordeq,length,order_engine}.rs`, `crates/shinri-sat/src/theory.rs`, `crates/shinri-theory/tests/splitting_on_demand.rs`, `crates/shinri-solver/tests/qfdt_e2e.rs` | Modify | mechanical `guard` → `guards` migration |
| `crates/shinri-str/src/leaf_bounds.rs` | Create | the per-leaf intersection-bound pass `bound_split` (+ tests) |
| `crates/shinri-str/src/memb.rs` | Modify | `emit_split_guards`; call `leaf_bounds::bound_split` at the end of `memb_check` |
| `crates/shinri-str/src/lib.rs` | Modify | `mod leaf_bounds;`, two `StrSolver` fields, a test hook, `memb_seeds_flagged` wiring in `model_with` (+ test) |
| `crates/shinri-str/src/model.rs` | Modify | `memb_seeds_flagged` (+ tests); `memb_seeds` becomes its wrapper |
| `crates/shinri-solver/src/lib.rs` | Modify | `eval_num_val` structural fold |
| `crates/shinri-solver/src/model_reject.rs` | Modify | rewritten `unevaluable_compound_len_arith`, two new tests |
| `crates/shinri-solver/tests/slice62_probes.rs` | Create | blocking-tier probes |
| `crates/shinri-solver/tests/len_bounds_oracle.rs` | Create | z3 differential (`--features oracle`) |
| `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice62-length-consistent-seeds-report.md` | Create | bench report and rewritten queue |
| `docs/superpowers/specs/2026-10-06-shinri-slice62-length-consistent-seeds-design.md` | Modify | append §11 *Measured outcomes* |

Task order follows spec §6. Tasks 1, 2, 4 and 5 are independent; Task 3 needs 1 and 2; Tasks 6–7 need 1–5.

---

### Task 0: Branch, base binary, sample corpus, base probe outcomes

**Files:** none in the repo (artifacts under `target/slice62-base/`, `target/slice59-sample-corpus/`).

**Interfaces:**
- Consumes: `main` at `cdb5630` (or later docs-only commits), `bench/results/slice61{,-sample}/results.jsonl`, `bench/corpus/`.
- Produces: `target/slice62-base/{shinri,shinri-bench,md5.txt,commit.txt,probes.txt}`, `target/slice59-sample-corpus/`, `target/slice62-base/probes/*.smt2`. Tasks 9 consumes them.

- [ ] **Step 1: Create the slice branch**

```bash
cd /workspace && git checkout main && git pull --ff-only && git checkout -b slice62-length-consistent-seeds
```

- [ ] **Step 2: Confirm `main`'s crates differ from the base runs' `f9fa4f9` in comments only**

```bash
git diff f9fa4f9 HEAD -- crates Cargo.toml Cargo.lock | grep -E '^[+-]' | grep -vE '^(\+\+\+|---)' \
  | grep -vE '^[+-]\s*(//|$)' ; echo "non-comment lines above (expect none)"
```

Expected: nothing printed before the echo line. If any non-comment line appears, stop and report: the base runs must be redone.

- [ ] **Step 3: Build the base binaries**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice62-base && cp target/release/shinri target/release/shinri-bench target/slice62-base/
md5sum target/slice62-base/shinri | tee target/slice62-base/md5.txt
git rev-parse --short HEAD | tee target/slice62-base/commit.txt
head -1 bench/results/slice61/results.jsonl | cut -c1-200
wc -l bench/results/slice61/results.jsonl bench/results/slice61-sample/results.jsonl
```

Expected: the fixture line shows sha `f9fa4f9dff52`; 103,336 and 2,001 lines (as slice 61).

- [ ] **Step 4: Re-create the neutrality-sample corpus (hard links, so row paths match `bench/corpus`)**

The bench's corpus walk skips symlinks, so the tree must be hard links. This is slice 59's seeded recipe verbatim.

```bash
python3 - <<'EOF'
import os, pathlib, random
corpus = pathlib.Path("bench/corpus")
out = pathlib.Path("target/slice59-sample-corpus")
logics = ["QF_BVFP", "QF_DT", "QF_LIA", "QF_LRA", "QF_UF", "QF_UFLIA", "QF_UFLRA"]
files = {lg: sorted(str(p.relative_to(corpus)) for p in (corpus / lg).rglob("*.smt2")) for lg in logics}
TOTAL, FLOOR = 2000, 100
alloc, rest, budget = {}, dict(files), TOTAL
while True:
    tot = sum(len(v) for v in rest.values())
    small = [lg for lg, v in rest.items() if budget * len(v) / tot < FLOOR]
    if not small:
        break
    for lg in small:
        alloc[lg] = min(FLOOR, len(rest[lg]))
        budget -= alloc[lg]
        del rest[lg]
tot = sum(len(v) for v in rest.values())
quota = {lg: budget * len(v) / tot for lg, v in rest.items()}
for lg in rest:
    alloc[lg] = int(quota[lg])
for lg in sorted(rest, key=lambda l: quota[l] - int(quota[l]), reverse=True)[: budget - sum(alloc[l] for l in rest)]:
    alloc[lg] += 1
rng = random.Random(59)
picked = []
for lg in logics:
    for rel in sorted(rng.sample(files[lg], alloc[lg])):
        dst = out / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        if not dst.exists():
            os.link(corpus / rel, dst)
        picked.append(rel)
pathlib.Path("target/slice59-sample.txt").write_text("\n".join(picked) + "\n")
print(alloc, sum(alloc.values()))
EOF
python3 - <<'EOF'
import json, pathlib
rows = {r["path"] for r in map(json.loads, open("bench/results/slice61-sample/results.jsonl")) if "path" in r}
picked = set(pathlib.Path("target/slice59-sample.txt").read_text().split())
print("sample matches slice61-sample rows:", rows == picked, len(rows), len(picked))
EOF
```

Expected: `sample matches slice61-sample rows: True 2000 2000`. If `False`, stop and report.

- [ ] **Step 5: Record the base behaviour of the probe shapes**

```bash
D=target/slice62-base/probes && mkdir -p $D
printf '(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\n(assert (str.in_re x (re.* (str.to_re "ab"))))\n(assert (str.in_re y (re.* (str.to_re "ab"))))\n(assert (and (<= (+ (str.len x) (str.len y)) 3) (>= (+ (str.len x) (str.len y)) 3)))\n(check-sat)\n' > $D/r11a-variant.smt2
printf '(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\n(assert (str.in_re x (re.* (str.to_re "ab"))))\n(assert (str.in_re y (re.* (str.to_re "ab"))))\n(assert (= (+ (str.len x) (str.len y)) 3))\n(check-sat)\n' > $D/r10.smt2
printf '(set-logic ALL)(declare-fun x () String)(declare-fun f (Int) Int)\n(assert (str.in_re x (re.* (str.to_re "ab"))))\n(assert (= (f (str.len x)) 1))\n(assert (= (f 0) 0))\n(assert (= (f 2) 0))\n(assert (<= (str.len x) 3))\n(check-sat)\n' > $D/uf-len.smt2
printf '(set-logic ALL)(declare-fun x () String)(declare-fun f (Int) Int)\n(assert (str.in_re x (re.* (str.to_re "ab"))))\n(assert (= (f (str.len x)) 1))\n(assert (= (f 0) 0))\n(assert (<= (str.len x) 3))\n(check-sat)\n' > $D/uf-len-sat.smt2
cp bench/corpus/QF_SLIA/2015-Norn/ab/norn-benchmark-135.smt2 $D/norn135.smt2
cp bench/corpus/QF_SLIA/2015-Norn/ab/norn-benchmark-138.smt2 $D/norn138.smt2
for f in $D/*.smt2; do printf '%s\t' $(basename $f); target/slice62-base/shinri --stats $f 2>&1 | grep -E '^stats:' | head -1; done | tee target/slice62-base/probes.txt
for f in $D/*.smt2; do printf '%s\t' $(basename $f); mise exec -- z3 -T:20 $f; done
```

Expected (base, by file name): `r11a-variant` and `uf-len` print `outcome=sat` (both wrong); `r10` prints `outcome=unknown`; `norn135`/`norn138` print `outcome=unknown fence=str-model-rejected`; `uf-len-sat` prints `outcome=sat`. z3: `unsat` for `r11a-variant`, `r10`, `uf-len`; `sat` for `uf-len-sat`, `norn135`, `norn138`. Record deviations; they are evidence for the report, not gates.

---

### Task 1: `regex::len_bounds`

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (new fn after `language_empty`, ~line 889; tests in `mod tests`, line 1500)

**Interfaces:**
- Consumes: `deriv`, `next_classes`, `nullable`, `node_count`, `MEMB_SEARCH_STEP_CAP`, `FUEL_NODE_CAP` (all in `regex.rs`).
- Produces: `pub(crate) const LEN_BOUND_DEPTH_CAP: u32 = 64;` and `pub(crate) fn len_bounds(r: &Rex) -> Option<(u32, Option<u32>)>`. Task 3 calls it.

- [ ] **Step 1: Write the failing tests** (append inside `mod tests` in `regex.rs`)

```rust
    // ── Slice 62: exact length bounds ───────────────────────────────────

    #[test]
    fn len_bounds_norn135_singleton() {
        // a*b ∩ a*b+ ∩ ab* ∩ [a-u]* = {ab}.
        let a_star = star_lit_test("a");
        let goal = inter(vec![
            concat(vec![a_star.clone(), lit_test("b")]),
            concat(vec![a_star, lit_test("b"), star_lit_test("b")]),
            concat(vec![lit_test("a"), star_lit_test("b")]),
            star_range_test('a', 'u'),
        ]);
        assert_eq!(len_bounds(&goal), Some((2, Some(2))));
    }

    #[test]
    fn len_bounds_cross_depth_state() {
        // (a|bb)c reaches the state `c` at depths 1 and 2: max must be 3.
        let r = concat(vec![union(vec![lit_test("a"), lit_test("bb")]), lit_test("c")]);
        assert_eq!(len_bounds(&r), Some((2, Some(3))));
    }

    #[test]
    fn len_bounds_unbounded() {
        assert_eq!(len_bounds(&star_lit_test("ab")), Some((0, None)));
    }

    #[test]
    fn len_bounds_counts_surrogate_shortest_path() {
        // The only length-2 word starts with a surrogate code point;
        // `search_shortest` skips that class and finds "bbb" (3).
        let r = union(vec![
            concat(vec![Rex::Range(0xD800, 0xDFFF), lit_test("a")]),
            lit_test("bbb"),
        ]);
        assert_eq!(search_shortest(&r).map(|w| w.chars().count()), Some(3));
        assert_eq!(len_bounds(&r), Some((2, Some(3))));
    }

    #[test]
    fn len_bounds_empty_language_is_none() {
        assert_eq!(len_bounds(&inter(vec![lit_test("a"), lit_test("b")])), None);
    }

    #[test]
    fn len_bounds_depth_cap_drops_max_only() {
        let long = "a".repeat(LEN_BOUND_DEPTH_CAP as usize + 6);
        let r = union(vec![lit_test("a"), lit_test(&long)]);
        assert_eq!(len_bounds(&r), Some((1, None)));
    }
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo nextest run -p shinri-str -E 'test(len_bounds_)'`
Expected: compile error `cannot find function len_bounds` / `LEN_BOUND_DEPTH_CAP`.

- [ ] **Step 3: Implement** (insert after `language_empty`'s closing brace)

```rust
/// Slice 62: layers the exact-bounds walk explores before giving up on a
/// finite maximum (spec §4.3).
pub(crate) const LEN_BOUND_DEPTH_CAP: u32 = 64;

/// Exact length bounds of `L(r)`: `Some((min, max))`, where `min` is the
/// shortest word length and `max` the longest (`None` when the language is
/// infinite or no finite bound was reached within `LEN_BOUND_DEPTH_CAP`).
/// `None` overall when `L(r)` is empty (slice 28 owns that case) or on any
/// taint (class-split cap, node cap, step cap) — "no lemma", never a verdict.
///
/// Layered walk: layer `d` is the set of distinct derivative states reached
/// by words of length exactly `d`. States are deduplicated WITHIN a layer
/// only: one state can sit at two depths without a cycle (`(a|bb)c` reaches
/// `c` at 1 and 2), and cross-layer dedup would under-state the max. Like
/// `language_empty`, every `next_classes` interval is explored, pure-surrogate
/// ones included (its `lo` represents the class), so `min` is a sound lower
/// bound — `search_shortest` skips surrogate classes and is not.
pub(crate) fn len_bounds(r: &Rex) -> Option<(u32, Option<u32>)> {
    let mut steps = 0usize;
    let mut layer: Vec<Rex> = vec![r.clone()];
    let mut min: Option<u32> = None;
    let mut last: Option<u32> = None;
    for d in 0..=LEN_BOUND_DEPTH_CAP {
        layer.retain(|s| !matches!(s, Rex::Empty));
        if layer.is_empty() {
            // Every path died: the language is finite (or empty).
            return min.map(|m| (m, last));
        }
        if layer.iter().any(nullable) {
            min.get_or_insert(d);
            last = Some(d);
        }
        if d == LEN_BOUND_DEPTH_CAP {
            break;
        }
        let mut seen: FxHashSet<Rex> = FxHashSet::default();
        let mut next: Vec<Rex> = Vec::new();
        for state in &layer {
            steps += 1;
            if steps > MEMB_SEARCH_STEP_CAP {
                return None;
            }
            let classes = next_classes(state)?;
            for (lo, _hi) in classes {
                let dd = deriv(lo, state);
                if node_count(&dd) > FUEL_NODE_CAP {
                    return None;
                }
                if !matches!(dd, Rex::Empty) && seen.insert(dd.clone()) {
                    next.push(dd);
                }
            }
        }
        layer = next;
    }
    // Depth cap with live states: the minimum (if found) is exact, the
    // maximum unknown.
    min.map(|m| (m, None))
}
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo nextest run -p shinri-str -E 'test(len_bounds_)'`
Expected: 6 passed. If `len_bounds_empty_language_is_none` fails because `inter` does not fold `a ∩ b` to `Empty`, the walk still returns `None` (no nullable layer before every state dies) — investigate before changing the test.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all && cargo clippy -p shinri-str --all-targets -- -D warnings
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): slice62 - exact length bounds by a layered derivative walk"
```

---

### Task 2: Lemmas with several guards (theory-interface migration)

**Files:**
- Modify: `crates/shinri-sat/src/types.rs:60-67`, `crates/shinri-sat/src/solver.rs` (`SplitAtoms` arm ~703-760, tests), `crates/shinri-sat/src/theory.rs`
- Modify: `crates/shinri-theory/src/solver_trait.rs:28-41`, `crates/shinri-theory/src/combiner.rs` (`FinalCheck`, line 17; all forwarding arms)
- Modify (mechanical): `crates/shinri-arith/src/lib.rs`, `crates/shinri-arrays/src/lib.rs`, `crates/shinri-dt/src/lib.rs`, `crates/shinri-str/src/{lib,memb,wordeq,length,order_engine}.rs`, `crates/shinri-theory/tests/splitting_on_demand.rs`, `crates/shinri-solver/tests/qfdt_e2e.rs`

**Interfaces:**
- Produces: `TCheck::Split { atoms: Vec<TermId>, guards: Vec<Lit>, phases: Vec<Option<bool>> }`; same field name in `FinalCheck::Split` and `TheoryResult::SplitAtoms`; `memb::emit_split_guards(s: &mut StrSolver, terms: &mut Context, atoms: Vec<TermId>, guards: Vec<shinri_core::Lit>) -> TCheck` (`pub(crate)`). Task 3 calls `emit_split_guards`.

- [ ] **Step 1: Write the failing SAT test** (in `crates/shinri-sat/src/solver.rs` `mod tests`, right after `guarded_split_does_not_force_spurious_unsat`)

```rust
    // ── Slice 62: a split guarded by TWO already-false literals ────────────
    //
    // Clause `¬e1 ∨ ¬e2 ∨ a` with e1, e2 true at level 0 and the theory then
    // propagating `a` false: the clause is violated, so the answer is UNSAT.
    // `add_learnt` watches lits[0] and lits[1] as given; ordered guards-first
    // both watches would be the already-false guards and `a := false` would
    // go unnoticed (a wrong SAT). Atoms-first ordering keeps `a` watched.
    #[test]
    fn two_guard_split_detects_violation() {
        use shinri_core::TermId;
        use std::cell::RefCell;
        use std::rc::Rc;

        #[derive(Default)]
        struct TwoGuardSplitter {
            fired: bool,
            eqns: Vec<Var>,
            fresh: Rc<RefCell<Vec<Var>>>,
            forced: Rc<RefCell<bool>>,
        }
        impl Theory for TwoGuardSplitter {
            fn new_var(&mut self, v: Var) {
                if self.eqns.len() < 2 {
                    self.eqns.push(v);
                }
            }
            fn assert(&mut self, _l: Lit) {}
            fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
                let fresh = self.fresh.borrow();
                if self.fired && fresh.len() == 1 && !*self.forced.borrow() {
                    *self.forced.borrow_mut() = true;
                    out.push((Lit::new(fresh[0], false), TheoryJust { theory: 99, tag: 0 }));
                }
                None
            }
            fn check(&mut self, _e: Effort) -> TheoryResult {
                if !self.fired {
                    self.fired = true;
                    TheoryResult::SplitAtoms {
                        atoms: vec![TermId::new(100).unwrap()],
                        guards: vec![
                            Lit::new(self.eqns[0], false),
                            Lit::new(self.eqns[1], false),
                        ],
                        phases: Vec::new(),
                    }
                } else {
                    TheoryResult::Sat
                }
            }
            fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
            fn push(&mut self) {}
            fn pop(&mut self, _n: usize) {}
            fn bind_fresh(&mut self, v: Var, _atom: TermId) {
                self.fresh.borrow_mut().push(v);
            }
        }

        let mut s: Solver<TwoGuardSplitter, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        let e1 = s.new_var();
        let e2 = s.new_var();
        s.add_clause(&[Lit::new(e1, true)]);
        s.add_clause(&[Lit::new(e2, true)]);
        let res = s.solve();
        assert!(
            matches!(res, SolveResult::Unsat { .. }),
            "e1 ∧ e2 → a with a forced false must be UNSAT; got {res:?}"
        );
    }
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo nextest run -p shinri-sat -E 'test(two_guard_split_detects_violation)'`
Expected: compile error (`no field guards on variant SplitAtoms`).

- [ ] **Step 3: Widen the three enums**

`crates/shinri-sat/src/types.rs`:

```rust
    SplitAtoms {
        atoms: Vec<TermId>,
        /// Literals over ALREADY-allocated vars, pushed as-is: the clause is
        /// `g₁ ∨ … ∨ gₖ ∨ atom₁ ∨ …`, i.e. `¬g₁ ∧ … ∧ ¬gₖ → (atom₁ ∨ …)`.
        /// Empty = an unconditional split. Slice 62 widened this from
        /// `Option<Lit>` for the per-leaf length-bound lemma.
        guards: Vec<Lit>,
```

`crates/shinri-theory/src/solver_trait.rs` `TCheck::Split` and `crates/shinri-theory/src/combiner.rs` `FinalCheck::Split`: replace `guard: Option<Lit>,` with `guards: Vec<Lit>,` (same doc comment, one line: `/// See shinri_sat::TheoryResult::SplitAtoms::guards.`).

- [ ] **Step 4: Rewrite the SAT split arm** (`crates/shinri-sat/src/solver.rs`, the `TheoryResult::SplitAtoms { atoms, guard, phases } =>` arm)

Change the destructuring to `guards`, and replace the guard push and the atom loop's tail:

```rust
                                    let mut lits: Vec<Lit> = Vec::with_capacity(atoms.len() + guards.len());
                                    // GUARDS: literals over ALREADY-allocated SAT vars, pushed
                                    // AS-IS (no fresh var, no bind_fresh), so the clause
                                    // expresses `¬g₁ ∧ … → (atom₁ ∨ …)`. (Comment block from the
                                    // old single-guard code, kept verbatim below this line.)
                                    let guard_was_present = !guards.is_empty();
                                    // Slice 62: with two or more guards (all false at emission),
                                    // guards-first ordering could make BOTH watched literals
                                    // (`add_learnt` watches lits[0], lits[1]) already-false
                                    // guards, and the atoms would never be watched. Put the atoms
                                    // first and the guards after, highest level first. 0 or 1
                                    // guard keeps the original guard-first order byte-for-byte.
                                    let multi_guard = guards.len() >= 2;
                                    if !multi_guard {
                                        lits.extend(guards.iter().copied());
                                    }
                                    for (i, atom) in atoms.iter().copied().enumerate() {
                                        /* existing body unchanged */
                                    }
                                    if multi_guard {
                                        let mut gs = guards;
                                        gs.sort_by_key(|g| std::cmp::Reverse(self.assign.level(g.var())));
                                        lits.extend(gs);
                                    }
```

Keep the existing explanatory comment about the guard (`// GUARD (optional): …`) above `guard_was_present`, adjusting "a literal" to "literals". Everything after the atom loop (unit path, `guard_was_present` branch path) is unchanged.

- [ ] **Step 5: Migrate every other site (compiler-driven)**

Run `cargo build --workspace --all-targets 2>&1 | grep -E '^error' -A5 | head -80` and fix each error by these rules only:
- constructor `guard: None` → `guards: Vec::new()`; `guard: Some(x)` → `guards: vec![x]`; `guard: g` where `g: Option<Lit>` → `guards: g.into_iter().collect()`;
- pass-through destructure/construct `guard,` → `guards,` (`FinalCheck` → `TheoryResult` lift at `combiner.rs:372`, the per-theory forwarding arms at ~633-680);
- reads: `guard.is_some()` → `!guards.is_empty()`, `guard.is_none()` → `guards.is_empty()`, `guard == None` → `guards.is_empty()`, `guard == Some(x)` / `assert_eq!(guard, Some(x))` → `guards == vec![x]` / `assert_eq!(guards, vec![x])`, `assert_eq!(guard, None)` → `assert!(guards.is_empty())`;
- `crates/shinri-str/src/memb.rs`: rename the body of `emit_split` into a new `pub(crate) fn emit_split_guards(s, terms, atoms: Vec<TermId>, guards: Vec<shinri_core::Lit>) -> TCheck` (constructing `TCheck::Split { atoms, guards, phases: Vec::new() }`) and make `emit_split` a one-line wrapper `emit_split_guards(s, terms, atoms, guard.into_iter().collect())`, keeping its doc comment; its callers do not change;
- the memb test helper `run_rounds` (`memb.rs` ~709): `TCheck::Split { atoms, guard, .. } => splits.push((atoms, guard.is_some()))` → `TCheck::Split { atoms, guards, .. } => splits.push((atoms, !guards.is_empty()))`.

No other edit. Then:

```bash
cargo build --workspace --all-targets
```

Expected: builds clean.

- [ ] **Step 6: Run the new test and the whole blocking tier**

```bash
cargo nextest run -p shinri-sat -E 'test(two_guard_split_detects_violation)'
taskset -c 0-11 mise run ci 2>&1 | tail -5
```

Expected: the new test passes; ci green with `1809 run / 1809 passed / 6 skipped` (slice 61's 1808 + 1). Temporarily swap `multi_guard` to `false` (guards-first) and confirm the new test FAILS with `got Sat`, then restore — this proves the test pins the ordering. If any pre-existing test fails, stop and report.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all && mise run lint
git add -A crates
git commit -m "refactor(theory): slice62 - splits carry several guard literals"
```

---

### Task 3: Per-leaf intersection length bounds (`leaf_bounds.rs`)

**Files:**
- Create: `crates/shinri-str/src/leaf_bounds.rs`
- Modify: `crates/shinri-str/src/lib.rs` (`mod leaf_bounds;` after `mod length;`; two fields in `StrSolver` after `emitted_len_axioms` (line 80); a test hook after `test_force_memb_true` (~line 1883))
- Modify: `crates/shinri-str/src/memb.rs` (the final `None` of `memb_check`, ~line 678)

**Interfaces:**
- Consumes: `regex::len_bounds`, `regex::{min_len, max_len, inter, comp, extract_const_regex}` (Task 1); `memb::emit_split_guards`, `memb::memb_sides` (Task 2); `model::is_repair_pinned`; `crate::side_clean`; `wordeq::len_of`.
- Produces: `pub(crate) fn bound_split(s: &mut StrSolver, cx: &mut TheoryCtx, known: &[TermId], input_cond_roots: &FxHashSet<ENodeId>) -> Option<TCheck>`; `StrSolver` fields `emitted_group_len_axioms: FxHashSet<(TermId, Vec<Lit>)>` and `len_bounds_cache: FxHashMap<Vec<Lit>, Option<(u32, Option<u32>)>>`; test hook `pub fn test_force_memb_true_lit(&mut self, atom: TermId, lit: Lit, positive: bool)`.

- [ ] **Step 1: Add the fields and the test hook** (`crates/shinri-str/src/lib.rs`)

After `emitted_len_axioms: FxHashSet<TermId>,`:

```rust
    /// Slice 62: dedup for per-leaf intersection length bounds, keyed by
    /// `(bound atom, sorted guard lits)` — the same bound under a different
    /// membership set is a different lemma. Monotone, like
    /// `emitted_len_axioms`.
    emitted_group_len_axioms: FxHashSet<(TermId, Vec<Lit>)>,
    /// Slice 62: `regex::len_bounds` of a leaf group's intersection, keyed by
    /// its sorted guard lits (lits ↔ atoms, so the key fixes the goal).
    /// Monotone.
    len_bounds_cache: FxHashMap<Vec<Lit>, Option<(u32, Option<u32>)>>,
```

(If `StrSolver` derives `Default`, nothing else is needed; if it has a hand-written `Default`/`new`, add both fields there with `Default::default()`.)

After `test_force_memb_true`:

```rust
    /// Like `test_force_memb_true`, with an explicit SAT literal (slice 62:
    /// group lemmas need distinct guard lits).
    pub fn test_force_memb_true_lit(&mut self, atom: TermId, lit: Lit, positive: bool) {
        self.memb_true.push((atom, lit, positive));
        self.memb_levels.push(0);
    }
```

Add `mod leaf_bounds;` after `mod length;`.

- [ ] **Step 2: Write the module with failing tests** (`crates/shinri-str/src/leaf_bounds.rs`)

```rust
//! Slice 62: exact length bounds of a bare leaf's membership intersection,
//! emitted as guarded lemmas `¬m₁ ∨ … ∨ ¬mₖ ∨ bound`. The slice-26 carve-out
//! bounds `len` per atom with the structural `min_len`/`max_len`; when every
//! arm has a `*` (Norn `ab` 135: `a*b ∩ a*b+ ∩ ab* ∩ [a-u]*` = `{ab}`) the
//! intersection's bounds never reach arith, which then picks a length no
//! word realizes. Each lemma is a string-theory tautology: a word in every
//! `mᵢ`'s language lies in `L(∩)`, whose lengths are within `len_bounds`.

use crate::regex::{self, Rex};
use crate::{memb, model, side_clean, wordeq, StrSolver};
use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Lit, Op, TermId, TermNode};
use shinri_theory::types::ENodeId;
use shinri_theory::{TCheck, TheoryCtx};

/// One bound lemma per call, or `None` (nothing new to say). Runs at the end
/// of `memb_check`, under the same fuel peek.
pub(crate) fn bound_split(
    s: &mut StrSolver,
    cx: &mut TheoryCtx,
    known: &[TermId],
    input_cond_roots: &FxHashSet<ENodeId>,
) -> Option<TCheck> {
    if s.fuel.remaining == 0 {
        return None;
    }
    // Group by bare-leaf subject, in first-seen order (determinism).
    let mut order: Vec<TermId> = Vec::new();
    let mut groups: FxHashMap<TermId, Vec<(Lit, Rex)>> = FxHashMap::default();
    let mut poisoned: FxHashSet<TermId> = FxHashSet::default();
    for &(atom, lit, pos) in &s.memb_true {
        let (t, re_t) = memb::memb_sides(cx.terms, atom);
        let is_leaf = matches!(
            cx.terms.term_node(t),
            TermNode::App { op: Op::Uninterpreted(_), args, .. }
                if cx.terms.children(*args).is_empty()
        );
        if !is_leaf {
            continue;
        }
        let Some(mut rex) = regex::extract_const_regex(cx.terms, re_t) else {
            poisoned.insert(t);
            continue;
        };
        if !pos {
            rex = regex::comp(rex);
        }
        if !groups.contains_key(&t) {
            order.push(t);
        }
        groups.entry(t).or_default().push((lit, rex));
    }
    for t in order {
        if poisoned.contains(&t) {
            continue;
        }
        if model::is_repair_pinned(cx.terms, cx.eq, known, t) {
            continue;
        }
        if !side_clean(cx.eq, cx.terms, t, input_cond_roots) {
            continue;
        }
        let members = &groups[&t];
        let mut guards: Vec<Lit> = members.iter().map(|(l, _)| l.negate()).collect();
        guards.sort_by_key(|l| l.code());
        guards.dedup();
        let bounds = match s.len_bounds_cache.get(&guards) {
            Some(b) => *b,
            None => {
                let goal = regex::inter(members.iter().map(|(_, r)| r.clone()).collect());
                let b = regex::len_bounds(&goal);
                s.len_bounds_cache.insert(guards.clone(), b);
                b
            }
        };
        let Some((lo, hi)) = bounds else {
            continue;
        };
        // What the per-atom (structural) bounds already tell arith.
        let lo0 = members.iter().map(|(_, r)| regex::min_len(r)).max().unwrap_or(0);
        let hi0 = members.iter().filter_map(|(_, r)| regex::max_len(r)).min();
        let lr = wordeq::len_of(cx.terms, t);
        let mut cands: Vec<TermId> = Vec::new();
        if lo > lo0 {
            cands.push(cmp(cx, BuiltinOp::Ge, lr, lo));
        }
        if let Some(h) = hi {
            if hi0.map_or(true, |h0| h < h0) {
                cands.push(cmp(cx, BuiltinOp::Le, lr, h));
            }
        }
        for b in cands {
            let key = (b, guards.clone());
            if s.emitted_group_len_axioms.contains(&key) {
                continue;
            }
            s.emitted_group_len_axioms.insert(key);
            return Some(memb::emit_split_guards(s, cx.terms, vec![b], guards));
        }
    }
    None
}

/// `(op len k)` over an Int numeral `k`.
fn cmp(cx: &mut TheoryCtx, op: BuiltinOp, len: TermId, k: u32) -> TermId {
    let n = cx.terms.mk_numeral(
        shinri_core::Rational::from_int(i128::from(k).into()),
        cx.terms.int_sort(),
    );
    cx.terms
        .mk_app(Op::Builtin(op), &[len, n])
        .expect("(cmp len k) well-sorted")
}

#[cfg(test)]
mod tests {
    use crate::regex::{self, Rex};
    use crate::StrSolver;
    use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    fn var(ctx: &mut Context, n: &str) -> TermId {
        let str_s = ctx.string_sort();
        let s = ctx.declare_fun(n, &[], str_s);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    fn memb_atom(ctx: &mut Context, t: TermId, r: &Rex) -> TermId {
        let re_t = regex::rex_to_term_test(ctx, r);
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[t, re_t]).unwrap()
    }

    /// Norn 135's four regexes on one leaf.
    fn norn135(ctx: &mut Context, x: TermId) -> Vec<TermId> {
        let a_star = regex::star_lit_test("a");
        let rs = [
            regex::concat(vec![a_star.clone(), regex::lit_test("b")]),
            regex::concat(vec![a_star, regex::lit_test("b"), regex::star_lit_test("b")]),
            regex::concat(vec![regex::lit_test("a"), regex::star_lit_test("b")]),
            regex::star_range_test('a', 'u'),
        ];
        rs.iter().map(|r| memb_atom(ctx, x, r)).collect()
    }

    /// Drive `check` to a fixpoint; return every Split as (atoms, guards).
    fn rounds(s: &mut StrSolver, cx: &mut TheoryCtx) -> Vec<(Vec<TermId>, Vec<Lit>)> {
        let mut out = Vec::new();
        for _ in 0..64 {
            match s.check(cx, Effort::Full) {
                TCheck::Split { atoms, guards, .. } => out.push((atoms, guards)),
                TCheck::Sat => return out,
                other => panic!("unexpected {other:?}"),
            }
        }
        panic!("no fixpoint");
    }

    fn is_op(terms: &Context, t: TermId, want: BuiltinOp) -> bool {
        matches!(terms.term_node(t), shinri_core::TermNode::App { op: Op::Builtin(o), .. } if *o == want)
    }

    fn numeral_arg(terms: &Context, t: TermId) -> Option<i128> {
        match terms.term_node(t) {
            shinri_core::TermNode::App { args, .. } => {
                let k = terms.children(*args)[1];
                terms.numeral_value(k).and_then(|r| r.numer().to_i128())
            }
            _ => None,
        }
    }

    fn setup(ctx: &mut Context, atoms: &[TermId], lits: &[Lit]) -> StrSolver {
        let mut s = StrSolver::default();
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx { terms: ctx, eq: &mut eq_e, atoms: &areg };
        for (i, &a) in atoms.iter().enumerate() {
            s.new_var(&mut cx, lits[i].var(), a);
            s.test_force_memb_true_lit(a, lits[i], lits[i].is_positive());
        }
        s
    }

    fn lits(n: u32) -> Vec<Lit> {
        (0..n).map(|i| Lit::new(Var::new(i), true)).collect()
    }

    #[test]
    fn norn135_group_emits_both_bounds_with_all_guards() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let atoms = norn135(&mut ctx, x);
        let ls = lits(4);
        let mut s = setup(&mut ctx, &atoms, &ls);
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &areg };
        let splits = rounds(&mut s, &mut cx);
        let group: Vec<_> = splits.iter().filter(|(_, g)| g.len() == 4).collect();
        assert_eq!(group.len(), 2, "one ≥ and one ≤ group lemma: {splits:?}");
        let mut want: Vec<Lit> = ls.iter().map(|l| l.negate()).collect();
        want.sort_by_key(|l| l.code());
        for (a, g) in &group {
            assert_eq!(g, &want);
            assert_eq!(a.len(), 1);
            assert_eq!(numeral_arg(cx.terms, a[0]), Some(2));
        }
        assert!(group.iter().any(|(a, _)| is_op(cx.terms, a[0], BuiltinOp::Ge)));
        assert!(group.iter().any(|(a, _)| is_op(cx.terms, a[0], BuiltinOp::Le)));
    }

    #[test]
    fn no_group_lemma_when_structural_bounds_are_tight() {
        // x ∈ [a-c]·"b": per-atom bounds are already 2..2.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let r = regex::concat(vec![Rex::Range('a' as u32, 'c' as u32), regex::lit_test("b")]);
        let m = memb_atom(&mut ctx, x, &r);
        let mut s = setup(&mut ctx, &[m], &lits(1));
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &areg };
        rounds(&mut s, &mut cx);
        assert!(s.emitted_group_len_axioms.is_empty());
    }

    #[test]
    fn pinned_leaf_emits_no_group_lemma() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let atoms = norn135(&mut ctx, x);
        let ab = ctx.mk_string_const("ab");
        let mut s = setup(&mut ctx, &atoms, &lits(4));
        s.test_force_str_term(ab);
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let (xn, cn) = (eq_e.intern(x), eq_e.intern(ab));
        let _ = eq_e.merge(xn, cn, shinri_theory::types::EqJust::Definitional);
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &areg };
        let _ = super::bound_split(&mut s, &mut cx, &[x, ab], &Default::default());
        assert!(s.emitted_group_len_axioms.is_empty());
    }

    #[test]
    fn group_dedup_key_includes_guards() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let mut atoms = norn135(&mut ctx, x);
        let extra = memb_atom(&mut ctx, x, &regex::star_range_test('a', 'z'));
        let mut s = setup(&mut ctx, &atoms, &lits(4));
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &areg };
        rounds(&mut s, &mut cx);
        let before = s.emitted_group_len_axioms.len();
        assert_eq!(before, 2);
        // A fifth membership (bounds unchanged) is a new guard set: the same
        // two bound atoms must be emitted again under 5 guards.
        let l5 = Lit::new(Var::new(4), true);
        s.new_var(&mut cx, l5.var(), extra);
        s.test_force_memb_true_lit(extra, l5, true);
        atoms.push(extra);
        let splits = rounds(&mut s, &mut cx);
        assert_eq!(splits.iter().filter(|(_, g)| g.len() == 5).count(), 2);
        assert_eq!(s.emitted_group_len_axioms.len(), before + 2);
    }

    #[test]
    fn negative_member_joins_group() {
        // x ∈ (a|b)(a|b)?  ∧  x ∉ (a|b): only length-2 words remain.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let ab = regex::union(vec![regex::lit_test("a"), regex::lit_test("b")]);
        let pos_r = regex::concat(vec![ab.clone(), regex::union(vec![ab.clone(), Rex::Eps])]);
        let mp = memb_atom(&mut ctx, x, &pos_r);
        let mn = memb_atom(&mut ctx, x, &ab);
        let lp = Lit::new(Var::new(0), true);
        let ln = Lit::new(Var::new(1), false); // asserted false: x ∉ (a|b)
        let mut s = setup(&mut ctx, &[mp, mn], &[lp, ln]);
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &areg };
        let splits = rounds(&mut s, &mut cx);
        let ge: Vec<_> = splits
            .iter()
            .filter(|(a, g)| g.len() == 2 && is_op(cx.terms, a[0], BuiltinOp::Ge))
            .collect();
        assert_eq!(ge.len(), 1, "{splits:?}");
        assert_eq!(numeral_arg(cx.terms, ge[0].0[0]), Some(2));
        let mut want = vec![lp.negate(), ln.negate()];
        want.sort_by_key(|l| l.code());
        assert_eq!(ge[0].1, want);
    }
}
```

Note: `setup` builds a throwaway `TheoryCtx` only to register vars; each test then builds the `cx` it drives. If `new_var` needs the same `EqualityEngine` as later rounds (it should not for membership atoms — check `StrSolver::new_var`), restructure `setup` to take `&mut TheoryCtx` instead. `Rational::numer()` may need `use num_traits::ToPrimitive` the way `model.rs` imports it; copy that import if the build asks for it.

- [ ] **Step 3: Run the tests to verify they fail**

Run: `cargo nextest run -p shinri-str -E 'test(/leaf_bounds::tests/)'`
Expected: `norn135_group_emits_both_bounds_with_all_guards`, `group_dedup_key_includes_guards` and `negative_member_joins_group` FAIL (no group lemma: `bound_split` is not called yet); the two "no lemma" tests pass vacuously.

- [ ] **Step 4: Wire the pass** (`crates/shinri-str/src/memb.rs`, the end of `memb_check`)

Replace the function's final `None` (after the slice-28 emptiness loop) with:

```rust
    // ── Slice 62: per-leaf intersection length bounds ────────────────────
    // Reached only when nothing above emitted this round. A leaf whose
    // memberships jointly bound its length more tightly than any single
    // atom does gets `¬m₁ ∨ … ∨ ¬mₖ ∨ bound` (leaf_bounds.rs).
    crate::leaf_bounds::bound_split(s, cx, known, input_cond_roots)
```

- [ ] **Step 5: Run the tests to verify they pass, then the crate**

```bash
cargo nextest run -p shinri-str -E 'test(/leaf_bounds::tests/)'
cargo nextest run -p shinri-str
```

Expected: 5 passed; the whole crate green. If an existing `memb.rs` test now sees an extra split and fails, stop and report (do not edit it): that would mean the pass fires where the spec says per-atom bounds already suffice.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all && cargo clippy -p shinri-str --all-targets -- -D warnings
git add crates/shinri-str/src/leaf_bounds.rs crates/shinri-str/src/lib.rs crates/shinri-str/src/memb.rs
git commit -m "feat(str): slice62 - guarded length bounds for a leaf's membership intersection"
```

---

### Task 4: Gate — structural evaluation of length arithmetic

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (`eval_num_val` doc comment ~1590-1600 and the `Add | Sub | Mul | Neg` arm ~1618-1640)
- Modify: `crates/shinri-solver/src/model_reject.rs` (tests, ~line 352)

**Interfaces:**
- Consumes: `Solver::{fold_arith, model_num, eval_str_val}` (unchanged).
- Produces: nothing new; `eval_num_val` behaviour as spec §4.1.

- [ ] **Step 1: Rewrite the pinned test and add the new ones** (`model_reject.rs`, replacing `unevaluable_compound_len_arith`)

```rust
    /// Slice 62: compound length arithmetic is folded from its operands even
    /// when the arith model never valued the compound term.
    #[test]
    fn compound_len_arith_evaluates_from_operands() {
        let (mut s, x, _) = fx();
        let len = b(&mut s, BuiltinOp::StrLen, &[x]);
        let one = int(&mut s, 1);
        let sum = b(&mut s, BuiltinOp::Add, &[len, one]);
        let two = int(&mut s, 2);
        let three = int(&mut s, 3);
        let holds = s.eq(sum, two);
        let fails = s.eq(sum, three);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(holds, &m), Some(true));
        assert_eq!(s.eval_bool(fails, &m), Some(false));
    }

    /// An operand with no value keeps the term unevaluable.
    #[test]
    fn unevaluable_compound_len_arith() {
        let (mut s, x, _) = fx();
        let len = b(&mut s, BuiltinOp::StrLen, &[x]);
        let is = s.ctx_mut().int_sort();
        let nf = s.declare_fun("n", &[], is);
        let n = s.app(Op::Uninterpreted(nf), &[]);
        let sum = b(&mut s, BuiltinOp::Add, &[len, n]);
        let two = int(&mut s, 2);
        let a = s.eq(sum, two);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(a, &m), None);
        assert_eq!(tag(&s, &[a], &m, true), "unevaluable:len-arith@not-needed");
    }

    /// Slice 62 (item 5): `len x + len y = 3` under `x = y = ""`, with no
    /// arith value for the sum, is a violation the non-strict gate sees.
    #[test]
    fn unvalued_sum_of_lengths_is_violated() {
        let (mut s, x, y) = fx();
        let lx = b(&mut s, BuiltinOp::StrLen, &[x]);
        let ly = b(&mut s, BuiltinOp::StrLen, &[y]);
        let sum = b(&mut s, BuiltinOp::Add, &[lx, ly]);
        let three = int(&mut s, 3);
        let a = s.eq(sum, three);
        let m = strs(&[(x, ""), (y, "")]);
        assert_eq!(s.eval_bool(a, &m), Some(false));
        assert!(!s.string_model_satisfies(&[a], &m, false));
    }
```

- [ ] **Step 2: Run them to verify the right ones fail**

Run: `cargo nextest run -p shinri-solver -E 'test(compound_len_arith) | test(unvalued_sum_of_lengths)'`
Expected: `compound_len_arith_evaluates_from_operands` and `unvalued_sum_of_lengths_is_violated` FAIL (`None` ≠ `Some(..)`); `unevaluable_compound_len_arith` passes. If the latter's tag is not `unevaluable:len-arith@not-needed`, stop and report the actual tag (do not change the classifier).

- [ ] **Step 3: Implement** (`crates/shinri-solver/src/lib.rs`)

Replace the `Add | Sub | Mul | Neg` arm with:

```rust
            // Length arithmetic is evaluated structurally whenever every
            // operand evaluates (slice 62; R11a required an arith value for
            // the compound term too). The fold is the term's true value under
            // the FINAL model — string lengths read from string values — so it
            // can only reject models that are actually wrong; an arith value
            // can be stale once a model-side seed changes a leaf's length.
            // With an unevaluable operand the arith value is used as before;
            // with neither the term stays unevaluable (`None`).
            TermNode::App {
                op:
                    Op::Builtin(
                        op @ (BuiltinOp::Add | BuiltinOp::Sub | BuiltinOp::Mul | BuiltinOp::Neg),
                    ),
                args,
                ..
            } => {
                let vals: Option<Vec<shinri_core::Rational>> = self
                    .ctx
                    .children(*args)
                    .iter()
                    .map(|&k| self.eval_num_val(model, k))
                    .collect();
                match vals.and_then(|v| Self::fold_arith(*op, v)) {
                    Some(r) => Some(r),
                    None => self.model_num(model, t),
                }
            }
```

and update the doc comment of `eval_num_val` to: "Compound arithmetic (`+`/`-`/`*`, unary `-`) is evaluated structurally whenever every operand evaluates (slice 62): the structural value is the term's true value under the final model, so it can only reject models that are actually wrong. Otherwise the arith model's value of the compound term is used, and with none the term is unevaluable (`None`), conservatively skipped."

- [ ] **Step 4: Run the tests, then the crate**

```bash
cargo nextest run -p shinri-solver -E 'test(compound_len_arith) | test(unvalued_sum_of_lengths)'
cargo nextest run -p shinri-solver
```

Expected: 3 passed; crate green. Any other failure: stop and report.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all && cargo clippy -p shinri-solver --all-targets -- -D warnings
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/src/model_reject.rs
git commit -m "fix(solver): slice62 - gate folds length arithmetic whenever its operands evaluate"
```

---

### Task 5: Backstop — strict gate on a seed/model length mismatch

**Files:**
- Modify: `crates/shinri-str/src/model.rs` (`memb_seeds`, line 467; tests after `memb_seed_replaces_free_fill`)
- Modify: `crates/shinri-str/src/lib.rs` (`model_with`, ~line 1598-1609; a test after the slice-57 `model_with` tests)

**Interfaces:**
- Produces: `pub(crate) fn memb_seeds_flagged(terms: &mut Context, eq: &mut EqualityEngine, known: &[TermId], membs: &[(TermId, bool)], m: &ModelBuilder) -> (FxHashMap<TermId, String>, bool)`; `memb_seeds` keeps its signature and returns `memb_seeds_flagged(..).0`.

- [ ] **Step 1: Write the failing tests**

In `model.rs` `mod tests`:

```rust
    // ── Slice 62: the seed/model length mismatch flag ────────────────────

    fn ab_star_leaf(ctx: &mut Context) -> (TermId, TermId) {
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let re_t = crate::regex::rex_to_term_test(ctx, &crate::regex::star_lit_test("ab"));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t]).unwrap();
        (x, atom)
    }

    fn pin_len(ctx: &mut Context, m: &mut ModelBuilder, x: TermId, n: i128) {
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        m.assign(l, ModelVal::Num(shinri_core::Rational::from_int(n.into())));
    }

    #[test]
    fn memb_seed_flag_unset_at_model_length() {
        let mut ctx = Context::new();
        let (x, atom) = ab_star_leaf(&mut ctx);
        let mut m = ModelBuilder::default();
        pin_len(&mut ctx, &mut m, x, 4);
        let mut eq = EqualityEngine::default();
        let (seeds, flag) = memb_seeds_flagged(&mut ctx, &mut eq, &[x], &[(atom, true)], &m);
        assert_eq!(seeds.get(&x).map(String::as_str), Some("abab"));
        assert!(!flag);
    }

    #[test]
    fn memb_seed_flag_set_on_shortest_fallback() {
        let mut ctx = Context::new();
        let (x, atom) = ab_star_leaf(&mut ctx);
        let mut m = ModelBuilder::default();
        pin_len(&mut ctx, &mut m, x, 3); // no word of (ab)* has length 3
        let mut eq = EqualityEngine::default();
        let (seeds, flag) = memb_seeds_flagged(&mut ctx, &mut eq, &[x], &[(atom, true)], &m);
        assert_eq!(seeds.get(&x).map(String::as_str), Some(""));
        assert!(flag);
    }
```

In `lib.rs` `mod tests`, after `slice57_model_with_budget_exhausted_keeps_default`:

```rust
    /// Slice 62: a fallback seed whose length differs from the arith model's
    /// requires the strict gate.
    #[test]
    fn slice62_model_with_flags_strict_on_seed_length_mismatch() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut m = ModelBuilder::default();
        let x = slice57_var(&mut ctx, "x");
        let re_t = crate::regex::rex_to_term_test(&mut ctx, &crate::regex::star_lit_test("ab"));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t]).unwrap();
        slice57_len(&mut ctx, &mut m, x, 3);
        let mut s = slice57_solver(&[], &[], &[x]);
        s.test_force_memb_true(atom, true);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.model_with(&mut cx, &mut m);
        assert!(matches!(m.get(x), Some(ModelVal::String(v)) if v.is_empty()));
        assert!(m.strict_check_required());
    }
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo nextest run -p shinri-str -E 'test(memb_seed_flag_) | test(slice62_model_with_flags_strict)'`
Expected: compile error (`memb_seeds_flagged` not found).

- [ ] **Step 3: Implement**

In `model.rs`, rename `pub(crate) fn memb_seeds(` to `pub(crate) fn memb_seeds_flagged(`, change its return type to `(FxHashMap<TermId, String>, bool)`, add `let mut len_changed = false;` before the output loop, replace the insertion with:

```rust
        if let Some(w) = regex::search_word(&goal, n).or_else(|| regex::search_shortest(&goal)) {
            // Slice 62: a fallback word whose length disagrees with the arith
            // model's leaves stale length facts behind; the caller requires
            // the strict gate (spec §4.2).
            if w.chars().count() != n {
                len_changed = true;
            }
            out.insert(v, w);
        }
```

return `(out, len_changed)`, add to its doc comment "Also returns whether some seed's length differs from the model length it was searched at (slice 62).", and add the wrapper right after it:

```rust
/// `memb_seeds_flagged` without the length-mismatch flag.
pub(crate) fn memb_seeds(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    membs: &[(TermId, bool)],
    m: &ModelBuilder,
) -> FxHashMap<TermId, String> {
    memb_seeds_flagged(terms, eq, known, membs, m).0
}
```

In `lib.rs` `model_with`, replace `let mut seeds = model::memb_seeds(cx.terms, cx.eq, &known, &membs, m);` with `let (mut seeds, seed_len_changed) = model::memb_seeds_flagged(cx.terms, cx.eq, &known, &membs, m);` and the `if joint_len_changed {` block with:

```rust
        if joint_len_changed || seed_len_changed {
            // A seed (joint, or a per-leaf shortest-word fallback) whose
            // length differs from the arith model's: length facts outside
            // what the gate re-reads from strings may be stale (a UF
            // argument, `str.to_int`), so require the strict gate (R9;
            // slice 62 adds the per-leaf case).
            m.require_strict_check();
        }
```

If clippy then reports `memb_seeds` as dead code outside tests, mark it `#[cfg(test)]` (its only remaining callers are the existing tests) rather than deleting it.

- [ ] **Step 4: Run the tests, then the crate**

```bash
cargo nextest run -p shinri-str -E 'test(memb_seed_flag_) | test(slice62_model_with_flags_strict)'
cargo nextest run -p shinri-str
```

Expected: 3 passed; crate green.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all && cargo clippy -p shinri-str --all-targets -- -D warnings
git add crates/shinri-str/src/model.rs crates/shinri-str/src/lib.rs
git commit -m "fix(str): slice62 - strict gate when a membership seed changes a leaf's length"
```

---

### Task 6: Blocking-tier probes

**Files:**
- Create: `crates/shinri-solver/tests/slice62_probes.rs`

**Interfaces:**
- Consumes: the solver after Tasks 1–5 (`shinri_solver::{Solver, CommandResponse}`, `shinri_parser::Parser`).
- Produces: scripts `R11A_VARIANT`, `R10`, `NORN_135`, `NORN_138`, `UF_LEN`, `UF_LEN_SAT`; Task 7 copies them verbatim.

- [ ] **Step 1: Write the probes**

```rust
//! Slice 62 probes (spec §7.2). Item 5: compound length arithmetic the
//! arith model never valued was skipped by the gate, so `x, y ∈ (ab)*` with
//! `len x + len y = 3` answered `sat` (z3 `unsat`). Item 3: Norn `ab` 135/138
//! need the leaf intersection's exact length bounds to reach a valid `sat`.
//! The backstop: a length used only under a UF answered `sat` with a model
//! violating it. Each `sat` witness is re-checked by pinning the `get-value`
//! answers and re-solving.
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

fn verdict(body: &str) -> String {
    run_script(&format!("{body}(check-sat)\n"))
        .into_iter()
        .find(|l| matches!(l.as_str(), "sat" | "unsat" | "unknown"))
        .expect("a verdict")
}

/// On `sat`, the `get-value` line for `vars`.
fn sat_values(body: &str, vars: &str) -> String {
    let out = run_script(&format!("{body}(check-sat)\n(get-value ({vars}))\n"));
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{out:?}\n{body}");
    out[1].clone()
}

const R11A_VARIANT: &str = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (and (<= (+ (str.len x) (str.len y)) 3) (>= (+ (str.len x) (str.len y)) 3)))
"#;

const R10: &str = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (= (+ (str.len x) (str.len y)) 3))
"#;

/// `QF_SLIA/2015-Norn/ab/norn-benchmark-135.smt2`, assertions verbatim
/// (z3 `sat`: `var_0 = "ab"`, `v = 2`).
const NORN_135: &str = r#"(set-logic QF_SLIA)
(declare-fun var_0 () String)
(declare-const v Int)
(assert (str.in_re var_0 (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(assert (str.in_re var_0 (re.++ (re.* (str.to_re "a")) (re.++ (str.to_re "b") (re.* (str.to_re "b"))))))
(assert (str.in_re var_0 (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
(assert (str.in_re var_0 (re.* (re.range "a" "u"))))
(assert (and (<= 0  (str.len var_0)) (= (* v 2 ) (+ (str.len var_0) 2 ))))
"#;

/// `QF_SLIA/2015-Norn/ab/norn-benchmark-138.smt2`, assertions verbatim.
const NORN_138: &str = r#"(set-logic QF_SLIA)
(declare-fun var_4 () String)
(declare-const v Int)
(assert (str.in_re var_4 (re.++ (re.* (str.to_re "a")) (re.++ (str.to_re "b") (re.* (str.to_re "b"))))))
(assert (str.in_re var_4 (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
(assert (str.in_re var_4 (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(assert (str.in_re var_4 (re.* (re.range "a" "u"))))
(assert (not (str.in_re (str.++ "a" var_4 "b" ) (str.to_re ""))))
(assert (and (<= 0  (str.len var_4)) (= (* v 2 ) (+ (str.len var_4) 2 ))))
"#;

/// The backstop's case: `len x` reaches only a UF argument (z3 `unsat`:
/// `len x` is even, ≤ 3, and `f` is 0 at 0 and 2). `main` printed
/// `sat ((x ""))`.
const UF_LEN: &str = r#"(set-logic ALL)
(declare-fun x () String)
(declare-fun f (Int) Int)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (= (f (str.len x)) 1))
(assert (= (f 0) 0))
(assert (= (f 2) 0))
(assert (<= (str.len x) 3))
"#;

/// Sibling: `f(2)` unconstrained, so `x = "ab"` is a model (z3 `sat`).
const UF_LEN_SAT: &str = r#"(set-logic ALL)
(declare-fun x () String)
(declare-fun f (Int) Int)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (= (f (str.len x)) 1))
(assert (= (f 0) 0))
(assert (<= (str.len x) 3))
"#;

#[test]
fn r11a_variant_not_sat() {
    assert_ne!(verdict(R11A_VARIANT), "sat");
}

#[test]
fn r10_not_sat() {
    assert_ne!(verdict(R10), "sat");
}

/// Parse `((s "w") (v k))` into (w, k).
fn word_and_int(vals: &str) -> (String, i64) {
    let w = vals.split('"').nth(1).expect("a quoted word").to_string();
    let k = vals
        .rsplit(|c: char| c == ' ' || c == '(')
        .find_map(|t| t.trim_end_matches(')').parse::<i64>().ok())
        .expect("an Int value");
    (w, k)
}

fn norn_witness_holds(body: &str, s: &str) {
    let (w, v) = word_and_int(&sat_values(body, &format!("{s} v")));
    assert_eq!(w, "ab", "the intersection is {{ab}}");
    assert_eq!(v * 2, w.chars().count() as i64 + 2, "v·2 = len + 2");
    let pinned = format!("{body}(assert (= {s} \"{w}\"))\n(assert (= v {v}))\n");
    assert_eq!(verdict(&pinned), "sat", "pinned witness re-solves sat");
}

#[test]
fn norn_135_sat_with_valid_model() {
    norn_witness_holds(NORN_135, "var_0");
}

#[test]
fn norn_138_sat_with_valid_model() {
    norn_witness_holds(NORN_138, "var_4");
}

#[test]
fn uf_len_backstop_not_sat() {
    assert_ne!(verdict(UF_LEN), "sat");
}

#[test]
fn uf_len_backstop_sat_sibling() {
    let vals = sat_values(UF_LEN_SAT, "x");
    let w = vals.split('"').nth(1).expect("a quoted word");
    assert!(w == "ab", "the only even length ≤ 3 with f ≠ 0 is 2: {vals}");
}
```

- [ ] **Step 2: Run them**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice62_probes)'`
Expected: 6 discovered, 6 passed. Then confirm they are RED on the base: `git stash -u` is not allowed to touch committed work, so instead build the base solver test binary from `main` in a worktree:

```bash
git worktree add ../slice62-red main && cp crates/shinri-solver/tests/slice62_probes.rs ../slice62-red/crates/shinri-solver/tests/
(cd ../slice62-red && cargo nextest run -p shinri-solver -E 'binary(slice62_probes)' 2>&1 | tail -12)
git worktree remove --force ../slice62-red
```

Expected on `main`: `r11a_variant_not_sat`, `uf_len_backstop_not_sat`, `norn_135_sat_with_valid_model`, `norn_138_sat_with_valid_model` FAIL; `r10_not_sat` and `uf_len_backstop_sat_sibling` pass. Record the result for the report. If a probe fails on HEAD, stop and report — do not loosen it.

- [ ] **Step 3: Commit**

```bash
cargo fmt --all && cargo clippy -p shinri-solver --all-targets -- -D warnings
git add crates/shinri-solver/tests/slice62_probes.rs
git commit -m "test(solver): slice62 - probes for the compound-arith gate, leaf bounds and backstop"
```

---

### Task 7: z3 differential oracle

**Files:**
- Create: `crates/shinri-solver/tests/len_bounds_oracle.rs`

**Interfaces:**
- Consumes: Task 6's scripts (copied verbatim without the `(set-logic …)` line), the `oracle` feature of `shinri-solver`, `easy_smt`.
- Produces: the oracle binary `len_bounds_oracle` (Task 8 counts it).

- [ ] **Step 1: Write the oracle**

```rust
//! Differential oracle (slice 62, spec §7.3): bare String leaves with 2–4
//! memberships each (mixed polarity), a compound length constraint (`+`,
//! scalar `*`) and optionally an Int `v`. Every decided shinri answer must
//! match z3; every shinri `sat` witness (strings and `v`), re-asserted into
//! z3, must be `sat`; a shinri `unsat` z3 cannot confirm fails.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(len_bounds_oracle)'
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Copied from tests/nary_arith_oracle.rs (the per-binary convention).
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

/// Copied verbatim from tests/slice62_probes.rs (minus `set-logic`).
const R11A_VARIANT: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (and (<= (+ (str.len x) (str.len y)) 3) (>= (+ (str.len x) (str.len y)) 3)))
"#;
const NORN_135: &str = r#"(declare-fun var_0 () String)
(declare-const v Int)
(assert (str.in_re var_0 (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(assert (str.in_re var_0 (re.++ (re.* (str.to_re "a")) (re.++ (str.to_re "b") (re.* (str.to_re "b"))))))
(assert (str.in_re var_0 (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
(assert (str.in_re var_0 (re.* (re.range "a" "u"))))
(assert (and (<= 0  (str.len var_0)) (= (* v 2 ) (+ (str.len var_0) 2 ))))
"#;

/// shinri's verdict on `body` and, on `sat`, the values of `strs` (quoted
/// words, in order) and of `v` when `with_v`.
fn shinri_run(body: &str, strs: &[&str], with_v: bool) -> (SolveOutcome, Vec<String>, Option<i64>) {
    let mut full = format!("(set-logic ALL)\n{body}(check-sat)\n");
    if !strs.is_empty() {
        full.push_str(&format!("(get-value ({}))\n", strs.join(" ")));
    }
    if with_v {
        full.push_str("(get-value (v))\n");
    }
    let mut solver = Solver::new();
    let mut parser = Parser::new(&full);
    let mut outcome = SolveOutcome::Unknown;
    let mut values: Vec<Vec<String>> = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            CommandResponse::Values(s) => values.push(vec![s]),
            _ => {}
        }
    }
    let mut words = Vec::new();
    let mut v = None;
    let mut it = values.into_iter().map(|mut x| x.remove(0));
    if outcome == SolveOutcome::Sat && !strs.is_empty() {
        let s = it.next().expect("string get-value");
        words = s.split('"').skip(1).step_by(2).map(str::to_string).collect();
    }
    if outcome == SolveOutcome::Sat && with_v {
        let s = it.next().expect("v get-value");
        let t = s.replace(['(', ')'], " ");
        let toks: Vec<&str> = t.split_whitespace().collect();
        // ((v k)) or ((v (- k)))
        v = Some(match toks.as_slice() {
            ["v", "-", k] => -k.parse::<i64>().expect("int"),
            ["v", k] => k.parse::<i64>().expect("int"),
            other => panic!("unexpected v value {other:?}"),
        });
    }
    (outcome, words, v)
}

/// `timeout_s` is z3's wall-clock limit; a timeout comes back as `Unknown`.
fn z3_outcome(body: &str, timeout_s: u32) -> easy_smt::Response {
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2".to_string(), "-in".to_string(), format!("-T:{timeout_s}")])
        .build()
        .expect("failed to launch z3 — run `mise install`");
    ctx.set_logic("QF_SLIA").expect("z3 set-logic failed");
    for line in body.lines() {
        let t = line.trim();
        if t.starts_with("(declare-") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            let ack = ctx.raw_recv().expect("z3 ack failed");
            let ack = ctx.display(ack).to_string();
            assert!(!ack.contains("error"), "z3 rejected a line (assertion dropped): {ack}\n{t}");
        }
    }
    match ctx.check() {
        Ok(r) => r,
        Err(e) if e.to_string().contains("timeout") => easy_smt::Response::Unknown,
        Err(e) => panic!("z3 check-sat failed: {e}\n{body}"),
    }
}

fn check(body: &str, strs: &[&str], with_v: bool, timeout_s: u32, z3_timeouts: &mut usize) -> SolveOutcome {
    let (ours, words, v) = shinri_run(body, strs, with_v);
    let theirs = z3_outcome(body, timeout_s);
    if matches!(theirs, easy_smt::Response::Unknown) {
        *z3_timeouts += 1;
    }
    match (ours, theirs) {
        (SolveOutcome::Sat, easy_smt::Response::Unsat) => panic!("shinri sat, z3 unsat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Sat) => panic!("shinri unsat, z3 sat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Unknown) => {
            panic!("shinri unsat, z3 timed out (-T:{timeout_s}), unconfirmed:\n{body}")
        }
        _ => {}
    }
    if ours == SolveOutcome::Sat {
        assert_eq!(words.len(), strs.len(), "get-value shape:\n{body}");
        let mut pinned = body.to_string();
        for (s, w) in strs.iter().zip(&words) {
            pinned.push_str(&format!("(assert (= {s} \"{w}\"))\n"));
        }
        if let Some(k) = v {
            pinned.push_str(&format!("(assert (= v {k}))\n"));
        }
        assert!(
            matches!(z3_outcome(&pinned, 20), easy_smt::Response::Sat),
            "z3 rejects shinri's witness {words:?} v={v:?}:\n{body}"
        );
    }
    ours
}

const REGEXES: [&str; 8] = [
    "(re.* (str.to_re \"ab\"))",
    "(re.++ (re.* (str.to_re \"a\")) (str.to_re \"b\"))",
    "(re.++ (str.to_re \"a\") (re.* (str.to_re \"b\")))",
    "(re.* (re.range \"a\" \"u\"))",
    "(re.++ (re.* (str.to_re \"a\")) (str.to_re \"b\") (re.* (str.to_re \"b\")))",
    "(re.union (str.to_re \"a\") (str.to_re \"bb\") (str.to_re \"abc\"))",
    "((_ re.loop 1 3) (re.union (str.to_re \"a\") (str.to_re \"b\")))",
    "(re.+ (re.union (str.to_re \"a\") (str.to_re \"ba\")))",
];
const NAMES: [&str; 3] = ["x", "y", "z"];

/// One generated script; returns (body, string leaves used, uses v).
fn gen(rng: &mut Lcg) -> (String, Vec<&'static str>, bool) {
    let leaves = 1 + rng.below(3) as usize;
    let mut body = String::new();
    for n in &NAMES[..leaves] {
        body.push_str(&format!("(declare-fun {n} () String)\n"));
    }
    let with_v = rng.below(2) == 0;
    if with_v {
        body.push_str("(declare-const v Int)\n(assert (>= v 0))\n");
    }
    for n in &NAMES[..leaves] {
        for _ in 0..2 + rng.below(3) {
            let re = REGEXES[rng.below(REGEXES.len() as u64) as usize];
            let a = format!("(str.in_re {n} {re})");
            if rng.below(4) == 0 {
                body.push_str(&format!("(assert (not {a}))\n"));
            } else {
                body.push_str(&format!("(assert {a})\n"));
            }
        }
    }
    let lens: Vec<String> = NAMES[..leaves].iter().map(|n| format!("(str.len {n})")).collect();
    let lhs = if lens.len() == 1 { lens[0].clone() } else { format!("(+ {})", lens.join(" ")) };
    let k = rng.below(7);
    let rhs = if with_v {
        format!("(+ (* 2 v) {k})")
    } else {
        k.to_string()
    };
    match rng.below(3) {
        0 => body.push_str(&format!("(assert (= {lhs} {rhs}))\n")),
        1 => body.push_str(&format!("(assert (and (<= {lhs} {rhs}) (>= {lhs} {rhs})))\n")),
        _ => body.push_str(&format!("(assert (= (* 2 {lhs}) {rhs}))\n")),
    }
    (body, NAMES[..leaves].to_vec(), with_v)
}

#[test]
fn len_bounds_probes_agree_with_z3() {
    let mut t = 0;
    assert_ne!(check(R11A_VARIANT, &["x", "y"], false, 20, &mut t), SolveOutcome::Sat);
    assert_eq!(check(NORN_135, &["var_0"], true, 20, &mut t), SolveOutcome::Sat);
}

#[test]
fn len_bounds_generated_agree_with_z3() {
    let mut rng = Lcg(62);
    let (mut sat, mut unsat, mut z3_timeouts) = (0usize, 0usize, 0usize);
    for _ in 0..N_ITERS {
        let (body, strs, with_v) = gen(&mut rng);
        match check(&body, &strs, with_v, 3, &mut z3_timeouts) {
            SolveOutcome::Sat => sat += 1,
            SolveOutcome::Unsat => unsat += 1,
            _ => {}
        }
    }
    eprintln!(
        "len_bounds_oracle: {sat} sat, {unsat} unsat, {} unknown, {z3_timeouts} z3 unknown/timeouts",
        N_ITERS - sat - unsat
    );
    assert!(sat > 0, "generator must reach sat: {sat} sat, {unsat} unsat");
}
```

- [ ] **Step 2: Run it**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'binary(len_bounds_oracle)' --no-capture 2>&1 | tail -15`
Expected: 2 discovered, 2 passed; the tally line printed. Record it for the report. A failure is a finding: reduce the failing script by hand, add it as a probe in `slice62_probes.rs`, fix the cause in the owning task's code, and note it in the report's deviations. Never weaken an assertion.

- [ ] **Step 3: Commit**

```bash
cargo fmt --all && cargo clippy -p shinri-solver --all-targets --features oracle -- -D warnings
git add crates/shinri-solver/tests/len_bounds_oracle.rs
git commit -m "test(solver): slice62 - z3 differential over leaf membership sets and length arithmetic"
```

---

### Task 8: Gates

**Files:** none in the repo (`target/slice62-gates.txt`).

**Interfaces:**
- Consumes: branch HEAD after Tasks 1–7.
- Produces: `target/slice62-gates.txt` (Task 9 cites it).

- [ ] **Step 1: Run the blocking tier and lint**

```bash
cargo fmt --all --check && taskset -c 0-11 mise run ci 2>&1 | tee target/slice62-ci.log | tail -5
```

Expected: exit 0; `N run / N passed / 6 skipped` with N = 1808 + this slice's blocking tests (regex 6, SAT 1, leaf_bounds 5, model_reject +2 net, model 2, lib 1, probes 6 → **1831**). If N differs, explain the difference in the report instead of forcing it.

- [ ] **Step 2: Run the oracle suite**

```bash
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice62-oracle.log | tail -5
```

Expected: `M run / M passed / 2 skipped` with M = 841 + shinri-solver's new blocking tests (model_reject +2, probes 6) + 2 oracle tests = **851**. State the number; if it differs, explain why. The discovered count is non-zero.

- [ ] **Step 3: Record**

```bash
{ git rev-parse --short HEAD; tail -3 target/slice62-ci.log; tail -3 target/slice62-oracle.log; } | tee target/slice62-gates.txt
```

---

### Task 9: After runs, triage, attribution, timing, report, measured outcomes, PR

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice62-length-consistent-seeds-report.md` (date = the day the after runs finish)
- Modify: `docs/superpowers/specs/2026-10-06-shinri-slice62-length-consistent-seeds-design.md` (append §11 *Measured outcomes*)

**Interfaces:**
- Consumes: branch HEAD after Tasks 1–8; Task 0's `target/slice62-base/*` and `target/slice59-sample-corpus/`; base runs `bench/results/slice61{,-sample}/results.jsonl`; `target/slice62-gates.txt`.
- Produces: the report and spec section cited by the PR.

- [ ] **Step 1: Build and launch the after runs detached**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice62-after && cp target/release/shinri target/release/shinri-bench target/slice62-after/
md5sum target/slice62-after/shinri | tee target/slice62-after/md5.txt
git rev-parse --short HEAD | tee target/slice62-after/commit.txt
uptime | tee target/slice62-after/uptime-start.txt
date -u +%FT%TZ > target/slice62-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice62-after/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice62-after/shinri --run-id slice62 \
  > target/slice62-after/run.log 2>&1; \
  taskset -c 12-23 target/slice62-after/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice62-after/shinri --run-id slice62-sample \
  > target/slice62-after/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice62-after/finished.txt' \
  > /dev/null 2>&1 &
```

About 103,335 string rows (~1.75 h) then 2,000 sample rows (~20 min). Wait for `target/slice62-after/finished.txt` with a Monitor/until-loop, not a foreground sleep. Record the 1-min load average at launch.

- [ ] **Step 2: Render reports and join the runs (criteria 1, 2, 6)**

```bash
for id in slice61 slice62 slice61-sample slice62-sample; do BENCH_RUN_ID=$id mise run bench-report; done
python3 - <<'EOF' | tee target/slice62-after/join.txt
import json, collections
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
changed = []
for base, after in (("slice61", "slice62"), ("slice61-sample", "slice62-sample")):
    a = load(f"bench/results/{base}/results.jsonl")
    b = load(f"bench/results/{after}/results.jsonl")
    assert a.keys() == b.keys(), f"row sets differ: {base} vs {after}"
    c = collections.Counter()
    for p in sorted(a):
        va, vb = a[p]["verdict"], b[p]["verdict"]
        if va != vb:
            c[(a[p]["logic"], va, vb)] += 1
            changed.append((p, a[p]["logic"], va, vb, a[p].get("fence_detail") or "-", b[p].get("fence_detail") or "-", after))
    print(f"== {base} -> {after}: {sum(c.values())} changed")
    for k, n in sorted(c.items()):
        print(" ", *k, n)
    print("  wrong rows after:", sum(1 for r in b.values() if r["verdict"] == "wrong"))
a = load("bench/results/slice61/results.jsonl")
b = load("bench/results/slice62/results.jsonl")
for p in ("QF_SLIA/2015-Norn/ab/norn-benchmark-135.smt2", "QF_SLIA/2015-Norn/ab/norn-benchmark-138.smt2"):
    print("criterion 2:", p, a[p]["verdict"], "->", b[p]["verdict"], b[p]["answers"])
def tags(rows):
    return collections.Counter(r.get("fence_detail") for r in rows.values() if r["verdict"] == "unknown:str-model-rejected")
ta, tb = tags(a), tags(b)
print("fence_detail movement (base -> after):")
for t in sorted(set(ta) | set(tb), key=lambda t: -(ta[t] + tb[t])):
    if ta[t] != tb[t]:
        print(f"  {t}: {ta[t]} -> {tb[t]}")
fam = lambda p: "/".join(p.split("/")[1:-1])
gain = [x for x in changed if x[2] != "correct" and x[3] == "correct"]
loss = [x for x in changed if x[2] == "correct" and x[3] != "correct"]
print("gains by family:", collections.Counter(fam(x[0]) for x in gain).most_common(10))
print("losses by family:", collections.Counter(fam(x[0]) for x in loss).most_common(10))
open("target/slice62-after/changed.tsv", "w").write("".join("\t".join(x) + "\n" for x in changed))
EOF
```

Expected: 0 wrong rows in both after runs (criterion 1; any hit stops the slice for a ruling). Criterion 2's two lines show `correct`.

- [ ] **Step 3: Triage changed rows (criteria 1, 3, 6)**

Triage every row whose transition is **not** `unknown:* → correct`, and a family-stratified sample of ≥ 32 `unknown:* → correct` rows, 3 runs per binary, interleaved, on cores 12–23 with nothing else running:

```bash
python3 - <<'EOF'
import random, collections
rows = [l.rstrip("\n").split("\t") for l in open("target/slice62-after/changed.tsv")]
gain = [r for r in rows if r[2].startswith("unknown") and r[3] == "correct"]
other = [r for r in rows if r not in gain]
rng = random.Random(62)
fam = collections.defaultdict(list)
for r in gain:
    fam["/".join(r[0].split("/")[1:-1])].append(r)
pick = []
while len(pick) < min(32, len(gain)):
    for f in sorted(fam):
        if fam[f] and len(pick) < 32:
            pick.append(fam[f].pop(rng.randrange(len(fam[f]))))
open("target/slice62-after/triage-in.tsv", "w").write("".join("\t".join(r) + "\n" for r in other + pick))
print(len(other), "non-gain rows,", len(pick), "sampled gain rows")
EOF
while IFS="$(printf '\t')" read -r p logic va vb tagA tagB run; do
  case "$run" in *sample) root=target/slice59-sample-corpus ;; *) root=bench/corpus ;; esac
  for i in 1 2 3; do
    for bin in target/slice62-base/shinri target/slice62-after/shinri; do
      r=$(taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats $root/$p 2>&1 \
          | grep -E '^(sat|unsat|unknown)$|^stats:|memory allocation' | tr '\n' ' ')
      printf '%s\t%s\t%s\t%s\n' "$p" "$(basename $(dirname $bin))" "$i" "$r"
    done
  done
done < target/slice62-after/triage-in.tsv | tee target/slice62-after/triage.tsv
```

If there are more than 200 non-gain rows, triage every small stratum in full and a seeded, family-stratified sample of ≥ 32 from each large one, and state the sizes. A row is *noise* if either binary's 3 runs disagree with each other or the two binaries agree on at least one run; *attributable* if each binary reproduces its own bench verdict 3/3 and they differ.

**Criterion 3 check for every attributable `correct → non-correct` row:** run the base binary with `(get-model)` appended (copy the script to `target/slice62-after/loss/<name>.smt2`, add `(get-model)` after `(check-sat)`), pin every printed value as `(assert (= name value))`, and run z3 on the pinned script. z3 `unsat` ⇒ the base model was invalid (the row is a rightful rejection; record it). z3 `sat` ⇒ a real loss: criterion 3 fails; stop for a ruling. Attributable sample-run rows fail criterion 6; a wrong answer from either binary fails criterion 1.

For newly `unverified` `unsat` rows (z3 timed out), run `z3 -T:120` and `cvc5 --tlimit=120000` per row; any `sat` is a criterion-1 failure. New `unsat` rows are possible this slice (the bound lemmas reach arith during search), so attribute every one.

- [ ] **Step 4: Attribution (spec §8 item 3; criterion 7) — throwaway, not committed**

Edit the working tree (reverted at the end of this step):
- in `crates/shinri-str/src/leaf_bounds.rs`, right before `return Some(memb::emit_split_guards(…))`, add `eprintln!("slice62-trace: group-bound");`;
- in `crates/shinri-str/src/lib.rs` `model_with`, inside the `if joint_len_changed || seed_len_changed {` block, add `eprintln!("slice62-trace: strict joint={joint_len_changed} seed={seed_len_changed}");`;
- in `crates/shinri-solver/src/lib.rs` `eval_num_val`'s compound arm, when the fold is `Some(r)` and `self.model_num(model, t)` is `None`, add `eprintln!("slice62-trace: unvalued-fold");`.

```bash
cargo build --release -p shinri-cli --target-dir target/slice62-trace
cut -f1,7 target/slice62-after/triage-in.tsv | while IFS="$(printf '\t')" read -r p run; do
  case "$run" in *sample) root=target/slice59-sample-corpus ;; *) root=bench/corpus ;; esac
  t=$(timeout 20 target/slice62-trace/release/shinri $root/$p 2>&1 | grep -o 'slice62-trace: [a-z=0-9 -]*' | sort | uniq -c | tr '\n' ' ')
  printf '%s\t%s\n' "$p" "${t:-none}"
done | tee target/slice62-after/attribution.tsv
python3 - <<'EOF' > target/slice62-after/strict-sample.txt
import json, random
b = [r for r in map(json.loads, open("bench/results/slice62/results.jsonl")) if "path" in r]
s = sorted(r["path"] for r in b if r["logic"] in ("QF_S", "QF_SLIA"))
print("\n".join(random.Random(62).sample(s, 400)))
EOF
while read -r p; do
  t=$(timeout 20 target/slice62-trace/release/shinri bench/corpus/$p 2>&1 | grep -o 'slice62-trace: [a-z=0-9 -]*' | sort -u | tr '\n' ' ')
  printf '%s\t%s\n' "$p" "${t:-none}"
done < target/slice62-after/strict-sample.txt | tee target/slice62-after/prevalence.tsv
git checkout -- crates && git status --short crates
```

Expected: `git status --short crates` prints nothing. Summarise for criterion 7: per changed row, which mechanism fired (group bound, strict seed/joint, unvalued fold); over the 400-row random sample, how often each fires (prevalence) and the verdict distribution of rows where `strict seed=true` fired.

- [ ] **Step 5: Timing (criterion 4)**

Gate on load: wait until the 1-min load average is ≤ 24 (record it). Then:

```bash
python3 - <<'EOF' | tee target/slice62-after/timing.txt
import json, random, subprocess, time, statistics
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
a = load("bench/results/slice61/results.jsonl")
b = load("bench/results/slice62/results.jsonl")
BIN = {"base": "target/slice62-base/shinri", "after": "target/slice62-after/shinri"}
rng = random.Random(62)
groups = {lg: sorted(p for p in a if a[p]["logic"] == lg and a[p]["verdict"] == b[p]["verdict"] == "correct")
          for lg in ("QF_S", "QF_SLIA")}
groups["newly-correct"] = sorted(p for p in a if a[p]["verdict"] != "correct" and b[p]["verdict"] == "correct")
for name, rows in groups.items():
    sample = rng.sample(rows, min(150, len(rows)))
    tot = {"base": 0.0, "after": 0.0}
    for p in sample:
        for which in ("base", "after"):
            t0 = time.monotonic()
            subprocess.run(["taskset", "-c", "12", BIN[which], f"bench/corpus/{p}"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
            tot[which] += time.monotonic() - t0
    print(name, len(sample), "rows: base %.2f s, after %.2f s, ratio %.3f"
          % (tot["base"], tot["after"], tot["after"] / tot["base"]))
for lg in ("QF_S", "QF_SLIA"):
    both = [p for p in a if a[p]["logic"] == lg and a[p]["verdict"] == b[p]["verdict"] == "correct"]
    for name, d in (("base", a), ("after", b)):
        ms = sorted(d[p]["wall_ms"] for p in both)
        print(lg, name, "median", statistics.median(ms), "p90", ms[int(0.9 * len(ms))])
EOF
```

Expected: QF_S and QF_SLIA ratios within 0.95–1.05 (criterion 4). If a pass lands outside, run it twice more and pool the three, stating so (slice 59–61 practice). The newly-correct ratio is reported, not gated.

- [ ] **Step 6: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-06-smtlib-2024-slice61-joint-concat-seeds-report.md`:
- *Headline*: rows moved to `correct` (sat/unsat split), criterion-2 rows, losses and their criterion-3 disposition, `unverified` count, criteria summary
- *Commands*: the exact commands from Tasks 0 and 9
- *Runs*: both binaries with md5 and commit (base = rebuilt from `cdb5630`, behaviour-identical to the `f9fa4f9` runs; say why), started/finished, row counts, load at launch
- *Success criteria*: spec §8 table, each PASS/FAIL with evidence (gates from `target/slice62-gates.txt`; Task 0 Step 5 and Task 6 RED-on-`main` outcomes; the oracle tally)
- *The two live wrong `sat`s on `main`*: the item-5 reproducer and the UF backstop case (found while planning), before/after
- *Verdict changes*: `join.txt` transitions; the `fence_detail` movement; gains and losses by family
- *Triage*: dispositions from `triage.tsv`; each criterion-3 pinned-model check; any unsat cross-check
- *Attribution and prevalence*: `attribution.tsv`, `prevalence.tsv` summarised (criterion 7)
- *Timing*: `timing.txt`
- *What changed versus the spec*: every deviation, including the SAT watch-order rule (plan Review Focus 1) and `memb_seeds` kept as a wrapper
- *Queued for the next slice*: slice-61 items 1, 2, 4 and 6–9 and the deferred minors, re-ranked on the after run's counts, plus **CEGAR length refinement** (target: the item-5 reproducer, z3 `unsat`); state every re-rank

- [ ] **Step 7: Append §11 *Measured outcomes* to the spec**

Add `## 11. Measured outcomes` at the end of the spec: a one-line pointer to the report, the criteria table with PASS/FAIL and key numbers, and a *Deviations from this spec* subsection.

- [ ] **Step 8: Commit and open the PR**

```bash
git add docs/superpowers/research docs/superpowers/specs/2026-10-06-shinri-slice62-length-consistent-seeds-design.md
git commit -m "docs(bench+spec): slice62 - length-consistent seeds run and measured outcomes"
git push -u origin slice62-length-consistent-seeds
gh pr create --base main --title "slice62: length-consistent seeds and the compound-arithmetic gate" --body "$(cat <<'EOF'
Spec: docs/superpowers/specs/2026-10-06-shinri-slice62-length-consistent-seeds-design.md
Plan: docs/superpowers/plans/2026-10-06-shinri-slice62-length-consistent-seeds.md
Report: docs/superpowers/research/<date>-smtlib-2024-slice62-length-consistent-seeds-report.md

The gate now folds length arithmetic whenever its operands evaluate (closes a live wrong `sat`), a membership seed that changes a leaf's length requires the strict gate (closes a second, UF-argument wrong `sat`), and a bare leaf's membership intersection tells arith its exact length bounds (Norn `ab` 135/138 back to `sat` with valid models). Splits now carry several guard literals.

<criteria table from spec §11>
EOF
)"
```

Fill `<date>` and the criteria lines from the report before running. Wait for CI; when it is green, ask the user before merging (merge commit, then delete the branch remote and local).
