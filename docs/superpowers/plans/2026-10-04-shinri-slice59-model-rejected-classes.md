# Slice 59 — Classify the `str-model-rejected` population Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Tag every `unknown fence=str-model-rejected` with a stable detail `<mode>:<kind>@<rebuild>` carried solver → `--stats` → bench JSONL → report, then use one bench run to rank the population's classes and pick the next fix slice, without changing any verdict.

**Architecture:** `shinri-theory` gains a diagnostic `RebuildOutcome` on `ModelBuilder` that `shinri-str`'s `model_with` sets on each branch of the slice-57 rebuild. A new `shinri-solver` module `model_reject.rs` classifies the first failing assertion only after the witness gate has already rejected, and the solver exposes the tag as `last_fence_detail()`. The CLI appends `detail=` to the `stats:` line; `shinri-bench` parses it into a new `fence_detail` JSONL field and renders a "Fence detail" report section.

**Tech Stack:** Rust workspace (toolchain pinned in `mise.toml`), cargo-nextest 0.9.140, z3 from mise for the oracle, `shinri-bench` for the SMT-LIB 2024 run, python3 for the analysis scripts.

**Spec:** `docs/superpowers/specs/2026-10-04-shinri-slice59-model-rejected-classes-design.md`

## Global Constraints

- No verdict change. Nothing reads `RebuildOutcome` or the detail tag to choose a model or a verdict; the classifier runs only after `string_model_satisfies` returned `false` (spec §4.3, §5).
- Tag grammar `<mode>:<kind>@<rebuild>`; `mode` ∈ {`violated`, `unevaluable`}; `kind` ∈ {`word-eq`, `str-diseq`, `memb`, `str-pred`, `str-order`, `int-conv`, `len-arith`, `bool`, `other:<op>`}, optionally `not-`-prefixed; `rebuild` ∈ {`not-needed`, `adopted`, `rejected`, `budget`}; `int-conv` wins over every other kind (spec §4.1). A tag never contains whitespace (the `stats:` line is split on whitespace).
- `absorb` keeps the more informative outcome: `NotNeeded < Adopted < Rejected < Budget` (spec §4.2).
- The `stats:` line field order is `cmd wall_ms outcome fence detail`; `detail=-` when absent (spec §4.4).
- The JSONL field is `fence_detail`, written right after `fence`; a row without it parses as `None` (spec §4.5).
- The report section "Fence detail" sits after "Ranked gaps" and is omitted when no row has a detail; `tests/fixtures/report_golden.md` must stay byte-identical (spec §4.5).
- Bench: string runs over QF_S and QF_SLIA; neutrality sample of 2,000 rows over the other seven logics, seed 59, floor 100 per logic; `--timeout 20 --mem-mb 3072 --jobs 6`; detached with `setsid` under `taskset -c 12-23`; base built from the branch point (spec §8).
- While a bench run is live, run builds and tests on cores 0–11 (`taskset -c 0-11 …`) (slice-53 R9).
- Oracle tests only run with `--features oracle`; without it they silently run 0 tests. Always confirm a non-zero discovered count (AGENTS.md).
- nextest filters use the expression form `-E 'test(<name>)'` / `-E 'binary(<name>)'` (AGENTS.md).
- `cargo fmt --all` before every commit; `mise run lint` (clippy `-D warnings`) must be clean.
- Branch `slice59-model-rejected-classes` off `main`; PR to `main`, merge commit when CI is green, then delete the branch (AGENTS.md). Ask the user before merging.

## Review Focus

1. **An incremental script: a rejected `check-sat` followed by a decided one.** Expected: the second `stats:` line says `fence=- detail=-` and `last_fence_detail()` is `None` (no stale tag). Pinned in Task 2 (`fence_tags::str_model_rejected_detail_clears_on_next_check`) and Task 3 (`stats_detail_clears_on_the_next_check_sat`).
2. **An operator whose SMT-LIB name contains spaces** (indexed ops such as `(_ extract 7 0)`) reaching `other:<op>`. Expected: whitespace becomes `_`, so `split_whitespace` in the bench still sees one `detail=` field. Pinned in Task 2 (`tag_safe_replaces_whitespace`).
3. **A heavily shared assertion DAG** (a 60-level `str.++` doubling under `str.len`). Expected: classification returns promptly (visited-set walk), tag `unevaluable:len-arith@…`. Pinned in Task 2 (`shared_dag_classifies_in_linear_time`).
4. **A solver binary that prints no `detail=` field** (the base binary under the new bench, or any pre-slice-59 build). Expected: `fence_detail` is `None`, verdicts unchanged. Pinned in Task 4 (`detail_from_last_stats_line`).
5. **An old results file without `fence_detail`.** Expected: it loads (`None`) and its report renders without the "Fence detail" section. Pinned in Task 4 (`older_rows_have_no_fence_detail`, `fence_detail_section_absent_without_details`, golden unchanged).

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-theory/src/model.rs` | Modify | `RebuildOutcome`, `ModelBuilder.rebuild`, setter/getter, `absorb` |
| `crates/shinri-theory/src/lib.rs` | Modify | re-export `RebuildOutcome` |
| `crates/shinri-str/src/lib.rs` | Modify | `model_with` records the outcome; slice-57 tests assert it |
| `crates/shinri-core/src/smtlib_print.rs` | Modify | `builtin_name` becomes `pub` (for `other:<op>`) |
| `crates/shinri-solver/src/model_reject.rs` | Create | the classifier (`model_reject_detail`) and its unit tests |
| `crates/shinri-solver/src/lib.rs` | Modify | `mod model_reject;`, `last_fence_detail` field/getter/reset, call at the gate |
| `crates/shinri-solver/tests/fence_tags.rs` | Modify | end-to-end detail + clearing test |
| `crates/shinri-cli/src/driver.rs` | Modify | `detail=` on the `stats:` line |
| `crates/shinri-cli/src/args.rs` | Modify | `--stats` help text names the detail |
| `crates/shinri-cli/tests/cli.rs` | Modify | stats-line shape (6 fields), detail tests |
| `crates/shinri-bench/src/runner.rs` | Modify | `stats_field`, `parse_stats_detail`, `fence_detail` on rows |
| `crates/shinri-bench/src/results.rs` | Modify | `Row.fence_detail`, JSON write/read |
| `crates/shinri-bench/src/report.rs` | Modify | `render_fence_detail` section |
| `crates/shinri-bench/tests/corpus/stub-solver.sh`, `tests/corpus/QF_T/rejected.smt2`, `tests/runner_e2e.rs` | Modify / Create | the stub emits a detail; the e2e asserts it lands in the JSONL |
| `docs/superpowers/research/<date>-smtlib-2024-slice59-model-rejected-classes-report.md` | Create | classification report and rewritten queue |
| `docs/superpowers/specs/2026-10-04-shinri-slice59-model-rejected-classes-design.md` | Modify | append *Measured outcomes* |

---

### Task 0: Branch, base binary, sample corpus, base runs

**Files:** none in the repo (artifacts under `target/slice59-base/`, `target/slice59-sample-corpus/`, `bench/results/slice59-base*/`).

- [ ] **Step 1: Create the slice branch**

```bash
cd /workspace && git checkout main && git pull --ff-only && git checkout -b slice59-model-rejected-classes
```

- [ ] **Step 2: Confirm the crates are unchanged from `de96d28`**

Run: `git diff --stat de96d28 HEAD -- crates`
Expected: empty (only the spec and plan commits sit on top of `de96d28`).

- [ ] **Step 3: Build and freeze the base binary**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice59-base && cp target/release/shinri target/slice59-base/shinri
cp target/release/shinri-bench target/slice59-base/shinri-bench
md5sum target/slice59-base/shinri | tee target/slice59-base/md5.txt
echo de96d28 > target/slice59-base/commit.txt
```

- [ ] **Step 4: Build the neutrality-sample corpus (hard links, so row paths match `bench/corpus`)**

The bench's corpus walk skips symlinks (`file_type.is_file()`), so the tree must be hard links.

```bash
python3 - <<'EOF'
import os, pathlib, random
corpus = pathlib.Path("bench/corpus")
out = pathlib.Path("target/slice59-sample-corpus")
logics = ["QF_BVFP", "QF_DT", "QF_LIA", "QF_LRA", "QF_UF", "QF_UFLIA", "QF_UFLRA"]
files = {lg: sorted(str(p.relative_to(corpus)) for p in (corpus / lg).rglob("*.smt2")) for lg in logics}
TOTAL, FLOOR = 2000, 100
alloc, rest, budget = {}, dict(files), TOTAL
while True:  # floors first, for logics whose proportional share is below FLOOR
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
```

Expected: `{'QF_LRA': 100, 'QF_UFLIA': 100, 'QF_UFLRA': 100, 'QF_BVFP': 627, 'QF_DT': 316, 'QF_LIA': 484, 'QF_UF': 273} 2000`. If a logic directory is missing, run `BENCH_LOGICS=<logic> mise run bench-fetch` first and repeat.

- [ ] **Step 5: Launch both base runs detached (strings, then the sample)**

```bash
date -u +%FT%TZ > target/slice59-base/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice59-base/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice59-base/shinri --run-id slice59-base \
  > target/slice59-base/run.log 2>&1; \
  taskset -c 12-23 target/slice59-base/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice59-base/shinri --run-id slice59-base-sample \
  > target/slice59-base/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice59-base/finished.txt' \
  > /dev/null 2>&1 &
```

About 103,335 string rows (~1.75 h) then 2,000 sample rows (~20 min). Do not wait: Tasks 1–5 proceed meanwhile on cores 0–11. Task 6 waits for `target/slice59-base/finished.txt`.

---

### Task 1: `RebuildOutcome` on `ModelBuilder`, recorded by `model_with`

**Files:**
- Modify: `crates/shinri-theory/src/model.rs` (struct at `:9-16`, flag methods at `:36-45`, `absorb` at `:59-71`, tests at `:262-279`)
- Modify: `crates/shinri-theory/src/lib.rs:23`
- Modify: `crates/shinri-str/src/lib.rs` (`model_with` at `:1566-1630`, slice-57 tests at `:2116-2240`)

**Interfaces:**
- Produces: `shinri_theory::RebuildOutcome` (`NotNeeded | Adopted | Rejected | Budget`, `Copy + Ord + Default`, `fn as_str(self) -> &'static str`); `ModelBuilder::set_rebuild_outcome(&mut self, RebuildOutcome)`; `ModelBuilder::rebuild_outcome(&self) -> RebuildOutcome`.

- [ ] **Step 1: Write the failing `shinri-theory` test**

Append to `mod strict_check_tests` in `crates/shinri-theory/src/model.rs`:

```rust
    #[test]
    fn rebuild_outcome_defaults_and_absorb_keeps_the_more_informative() {
        assert_eq!(
            ModelBuilder::default().rebuild_outcome(),
            RebuildOutcome::NotNeeded
        );
        for (a, b, want) in [
            (RebuildOutcome::NotNeeded, RebuildOutcome::Adopted, RebuildOutcome::Adopted),
            (RebuildOutcome::Budget, RebuildOutcome::Adopted, RebuildOutcome::Budget),
            (RebuildOutcome::Adopted, RebuildOutcome::Rejected, RebuildOutcome::Rejected),
            (RebuildOutcome::Rejected, RebuildOutcome::NotNeeded, RebuildOutcome::Rejected),
        ] {
            let mut x = ModelBuilder::default();
            x.set_rebuild_outcome(a);
            let mut y = ModelBuilder::default();
            y.set_rebuild_outcome(b);
            x.absorb(y);
            assert_eq!(x.rebuild_outcome(), want, "{a:?} absorb {b:?}");
        }
        assert_eq!(RebuildOutcome::NotNeeded.as_str(), "not-needed");
        assert_eq!(RebuildOutcome::Adopted.as_str(), "adopted");
        assert_eq!(RebuildOutcome::Rejected.as_str(), "rejected");
        assert_eq!(RebuildOutcome::Budget.as_str(), "budget");
    }
```

- [ ] **Step 2: Run it to verify it fails**

Run: `taskset -c 0-11 cargo nextest run -p shinri-theory -E 'test(rebuild_outcome_defaults_and_absorb_keeps_the_more_informative)'`
Expected: compile error, `RebuildOutcome` / `set_rebuild_outcome` not found.

- [ ] **Step 3: Implement `RebuildOutcome`**

In `crates/shinri-theory/src/model.rs`, add above `pub struct ModelBuilder`:

```rust
/// Slice 59: what the string theory's slice-57 reconciliation rebuild did
/// for this model. Diagnostic only (the `str-model-rejected` detail tag);
/// nothing reads it to choose a model or a verdict. Ordered by how much it
/// says, so `absorb` keeps the more informative value.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum RebuildOutcome {
    /// The default model held every input equation (or no rebuild applies).
    #[default]
    NotNeeded,
    /// The rebuild held every input equation and was adopted.
    Adopted,
    /// The rebuild completed but failed its checks; the default was kept.
    Rejected,
    /// The candidate-trial budget ran out; the default was kept.
    Budget,
}

impl RebuildOutcome {
    /// The tag spelling (spec §4.1).
    pub fn as_str(self) -> &'static str {
        match self {
            RebuildOutcome::NotNeeded => "not-needed",
            RebuildOutcome::Adopted => "adopted",
            RebuildOutcome::Rejected => "rejected",
            RebuildOutcome::Budget => "budget",
        }
    }
}
```

Add the field to `ModelBuilder` after `strict_check`:

```rust
    /// Slice 59: the string rebuild's outcome (diagnostic only).
    rebuild: RebuildOutcome,
```

Add after `strict_check_required`:

```rust
    /// Slice 59: record what the string rebuild did (diagnostic only).
    #[inline]
    pub fn set_rebuild_outcome(&mut self, o: RebuildOutcome) {
        self.rebuild = o;
    }
    /// Slice 59: what the string rebuild did for this model.
    #[inline]
    pub fn rebuild_outcome(&self) -> RebuildOutcome {
        self.rebuild
    }
```

Replace the body of `absorb` and extend its doc:

```rust
    /// caller has already verified agreement via `merge_check`). The strict
    /// flag is kept if either builder set it; the rebuild outcome keeps the
    /// more informative of the two.
    pub fn absorb(&mut self, other: ModelBuilder) {
        let ModelBuilder {
            values,
            strict_check,
            rebuild,
        } = other;
        for (t, v) in values {
            self.values.insert(t, v);
        }
        self.strict_check |= strict_check;
        self.rebuild = self.rebuild.max(rebuild);
    }
```

In `crates/shinri-theory/src/lib.rs`, change `pub use model::ModelBuilder;` to `pub use model::{ModelBuilder, RebuildOutcome};`.

- [ ] **Step 4: Run it to verify it passes**

Run: `taskset -c 0-11 cargo nextest run -p shinri-theory -E 'test(rebuild_outcome_defaults_and_absorb_keeps_the_more_informative)'`
Expected: 1 test, PASS.

- [ ] **Step 5: Extend the four slice-57 `model_with` tests (failing)**

In `crates/shinri-str/src/lib.rs` tests, add `use shinri_theory::RebuildOutcome;` to the test module's imports, then add one assertion at the end of each test:

- `slice57_model_with_adopts_rebuild_and_flags_strict`: `assert_eq!(m.rebuild_outcome(), RebuildOutcome::Adopted);`
- `slice57_model_with_keeps_default_when_rebuild_fails`: `assert_eq!(m.rebuild_outcome(), RebuildOutcome::Rejected);`
- `slice57_model_with_budget_exhausted_keeps_default`: `assert_eq!(m.rebuild_outcome(), RebuildOutcome::Budget);`
- `slice57_model_with_default_path_unflagged`: `assert_eq!(m.rebuild_outcome(), RebuildOutcome::NotNeeded);`

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(/^tests::slice57_model_with/)'`
Expected: 4 tests; `adopts`, `keeps_default_when_rebuild_fails`, `budget_exhausted` FAIL (outcome still `NotNeeded`); `default_path_unflagged` PASS. If the filter finds 0 tests, drop the `tests::` prefix (`-E 'test(/slice57_model_with/)'`) and confirm 4 discovered.

- [ ] **Step 6: Record the outcome in `model_with`**

In `crates/shinri-str/src/lib.rs` `model_with`, change the rebuild `match` to:

```rust
            // `None`: the candidate-trial budget ran out; the rebuild is
            // abandoned like a failed one (default model, flag unset).
            // Slice 59: each branch records its outcome for the detail tag.
            match model_reconcile::reconciled_values(cx.terms, cx.eq, m, &inp) {
                Some(rebuilt)
                    if model_reconcile::input_eqs_hold(cx.terms, &input_eqs, &rebuilt, m)
                        && model_reconcile::concats_consistent(cx.terms, &rebuilt, m) =>
                {
                    m.require_strict_check();
                    m.set_rebuild_outcome(RebuildOutcome::Adopted);
                    rebuilt
                }
                Some(_) => {
                    m.set_rebuild_outcome(RebuildOutcome::Rejected);
                    vals
                }
                None => {
                    m.set_rebuild_outcome(RebuildOutcome::Budget);
                    vals
                }
            }
```

and add `RebuildOutcome` to the file's existing `shinri_theory` import (`use shinri_theory::{…, RebuildOutcome};`). The default-path branch sets nothing (`NotNeeded` is the default).

- [ ] **Step 7: Run the tests to verify they pass**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -p shinri-theory`
Expected: all pass, including the 4 slice-57 tests. If `keeps_default_when_rebuild_fails` reports `Budget`, that fixture runs out of budget rather than failing the checks: stop and report it (the `rejected` path then needs a new fixture, which is a plan change).

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-theory/src/model.rs crates/shinri-theory/src/lib.rs crates/shinri-str/src/lib.rs
git commit -m "feat(slice59): record the string rebuild outcome on ModelBuilder"
```

---

### Task 2: Solver classifier and `last_fence_detail`

**Files:**
- Modify: `crates/shinri-core/src/smtlib_print.rs:270` (`fn builtin_name` → `pub fn builtin_name`)
- Create: `crates/shinri-solver/src/model_reject.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (`mod` list `:5-11`, field `:135`, ctor `:254`, getter `:409`, `check_sat` `:768`, gate `:1359` and `:1495`)
- Modify: `crates/shinri-solver/tests/fence_tags.rs`

**Interfaces:**
- Consumes: `shinri_theory::RebuildOutcome` and `ModelBuilder::rebuild_outcome()` (Task 1).
- Produces: `pub fn Solver::last_fence_detail(&self) -> Option<&str>` (Task 3 reads it); `pub(crate) fn Solver::model_reject_detail(&self, assertions: &[TermId], model: &Model, strict: bool, rebuild: RebuildOutcome) -> String`; `pub fn shinri_core::smtlib_print::builtin_name(b: BuiltinOp) -> String`.

- [ ] **Step 1: Make `builtin_name` public**

In `crates/shinri-core/src/smtlib_print.rs`, change `fn builtin_name(b: BuiltinOp) -> String {` to:

```rust
/// The SMT-LIB spelling of a builtin operator (indexed ops in `(_ op …)` form).
pub fn builtin_name(b: BuiltinOp) -> String {
```

- [ ] **Step 2: Write the module skeleton and its failing tests**

Create `crates/shinri-solver/src/model_reject.rs`:

```rust
//! Slice 59: classify a model the string witness gate rejected
//! (`str-model-rejected`) into a stable detail tag `<mode>:<kind>@<rebuild>`
//! (spec §4.1). Diagnostics only: it runs after the gate has already
//! rejected and never decides a verdict.

use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Op, TermId, TermNode};
use shinri_theory::RebuildOutcome;

use crate::model::Model;
use crate::Solver;

impl Solver {
    /// The detail tag for a model that `string_model_satisfies(assertions,
    /// model, strict)` rejected.
    pub(crate) fn model_reject_detail(
        &self,
        assertions: &[TermId],
        model: &Model,
        strict: bool,
        rebuild: RebuildOutcome,
    ) -> String {
        let _ = (assertions, model, strict);
        format!("todo@{}", rebuild.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Rational;
    use shinri_theory::types::ModelVal;

    fn fx() -> (Solver, TermId, TermId) {
        let mut s = Solver::new();
        let ss = s.ctx_mut().string_sort();
        let xf = s.declare_fun("x", &[], ss);
        let x = s.app(Op::Uninterpreted(xf), &[]);
        let yf = s.declare_fun("y", &[], ss);
        let y = s.app(Op::Uninterpreted(yf), &[]);
        (s, x, y)
    }

    fn strs(pairs: &[(TermId, &str)]) -> Model {
        let mut m = Model::default();
        for &(t, v) in pairs {
            m.values.insert(t, ModelVal::String(v.to_owned()));
        }
        m
    }

    fn lit(s: &mut Solver, v: &str) -> TermId {
        s.ctx_mut().mk_string_const(v)
    }

    fn int(s: &mut Solver, n: i128) -> TermId {
        let is = s.ctx_mut().int_sort();
        s.ctx_mut().mk_numeral(Rational::from_int(n.into()), is)
    }

    fn b(s: &mut Solver, op: BuiltinOp, args: &[TermId]) -> TermId {
        s.app(Op::Builtin(op), args)
    }

    fn tag(s: &Solver, a: &[TermId], m: &Model, strict: bool) -> String {
        s.model_reject_detail(a, m, strict, RebuildOutcome::NotNeeded)
    }

    #[test]
    fn violated_word_eq() {
        let (mut s, x, _) = fx();
        let bb = lit(&mut s, "b");
        let a = s.eq(x, bb);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(a, &m), Some(false));
        assert_eq!(tag(&s, &[a], &m, false), "violated:word-eq@not-needed");
    }

    #[test]
    fn violated_str_diseq() {
        let (mut s, x, _) = fx();
        let la = lit(&mut s, "a");
        let d = b(&mut s, BuiltinOp::Distinct, &[x, la]);
        assert!(matches!(
            s.ctx().term_node(d),
            TermNode::App { op: Op::Builtin(BuiltinOp::Distinct), .. }
        ));
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[d], &m, false), "violated:str-diseq@not-needed");
    }

    #[test]
    fn not_prefix_and_double_negation() {
        let (mut s, x, _) = fx();
        let la = lit(&mut s, "a");
        let e = s.eq(x, la);
        let ne = b(&mut s, BuiltinOp::Not, &[e]);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[ne], &m, false), "violated:not-word-eq@not-needed");
        let lb = lit(&mut s, "b");
        let e2 = s.eq(x, lb);
        let n1 = b(&mut s, BuiltinOp::Not, &[e2]);
        let n2 = b(&mut s, BuiltinOp::Not, &[n1]);
        assert_eq!(tag(&s, &[n2], &m, false), "violated:word-eq@not-needed");
    }

    #[test]
    fn violated_memb() {
        let (mut s, x, _) = fx();
        let lb = lit(&mut s, "b");
        let re = b(&mut s, BuiltinOp::StrToRe, &[lb]);
        let a = b(&mut s, BuiltinOp::StrInRe, &[x, re]);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(a, &m), Some(false));
        assert_eq!(tag(&s, &[a], &m, false), "violated:memb@not-needed");
    }

    #[test]
    fn violated_len_arith() {
        let (mut s, x, _) = fx();
        let len = b(&mut s, BuiltinOp::StrLen, &[x]);
        let two = int(&mut s, 2);
        let a = s.eq(len, two);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[a], &m, false), "violated:len-arith@not-needed");
    }

    #[test]
    fn violated_bool_skeleton() {
        let (mut s, x, _) = fx();
        let lb = lit(&mut s, "b");
        let lc = lit(&mut s, "c");
        let e1 = s.eq(x, lb);
        let e2 = s.eq(x, lc);
        let a = b(&mut s, BuiltinOp::Or, &[e1, e2]);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[a], &m, false), "violated:bool@not-needed");
    }

    #[test]
    fn unevaluable_str_pred_and_order() {
        let (mut s, x, y) = fx();
        let la = lit(&mut s, "a");
        let p = b(&mut s, BuiltinOp::StrPrefixOf, &[la, x]);
        let m = strs(&[(x, "a"), (y, "b")]);
        assert_eq!(s.eval_bool(p, &m), None);
        assert_eq!(
            s.model_reject_detail(&[p], &m, true, RebuildOutcome::Adopted),
            "unevaluable:str-pred@adopted"
        );
        let lt = b(&mut s, BuiltinOp::StrLt, &[x, y]);
        assert_eq!(tag(&s, &[lt], &m, true), "unevaluable:str-order@not-needed");
    }

    #[test]
    fn int_conv_wins_over_len_arith() {
        let (mut s, x, _) = fx();
        let ti = b(&mut s, BuiltinOp::StrToInt, &[x]);
        let five = int(&mut s, 5);
        let a = s.eq(ti, five);
        let m = strs(&[(x, "5")]);
        assert_eq!(s.eval_bool(a, &m), None);
        assert_eq!(tag(&s, &[a], &m, true), "unevaluable:int-conv@not-needed");
    }

    #[test]
    fn unevaluable_compound_len_arith() {
        let (mut s, x, _) = fx();
        let len = b(&mut s, BuiltinOp::StrLen, &[x]);
        let one = int(&mut s, 1);
        let sum = b(&mut s, BuiltinOp::Add, &[len, one]);
        let two = int(&mut s, 2);
        let a = s.eq(sum, two);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(a, &m), None);
        assert_eq!(tag(&s, &[a], &m, true), "unevaluable:len-arith@not-needed");
    }

    #[test]
    fn unevaluable_descends_to_the_first_undecided_leaf() {
        let (mut s, x, _) = fx();
        let la = lit(&mut s, "a");
        let lb = lit(&mut s, "b");
        let e = s.eq(x, lb); // false under x = "a"
        let p = b(&mut s, BuiltinOp::StrPrefixOf, &[la, x]); // undecided
        let or1 = b(&mut s, BuiltinOp::Or, &[e, p]);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[or1], &m, true), "unevaluable:str-pred@not-needed");
        let np = b(&mut s, BuiltinOp::Not, &[p]);
        let or2 = b(&mut s, BuiltinOp::Or, &[e, np]);
        assert_eq!(tag(&s, &[or2], &m, true), "unevaluable:not-str-pred@not-needed");
        // ite: the condition is true, so the undecided leaf is the then-branch.
        let ea = s.eq(x, la);
        let sfx = b(&mut s, BuiltinOp::StrSuffixOf, &[la, x]);
        let ite = b(&mut s, BuiltinOp::Ite, &[ea, sfx, e]);
        assert_eq!(tag(&s, &[ite], &m, true), "unevaluable:str-pred@not-needed");
    }

    #[test]
    fn the_first_failing_assertion_decides() {
        let (mut s, x, y) = fx();
        let lb = lit(&mut s, "b");
        let e = s.eq(x, lb);
        let lt = b(&mut s, BuiltinOp::StrLt, &[x, y]);
        let m = strs(&[(x, "a"), (y, "c")]);
        assert_eq!(tag(&s, &[lt, e], &m, true), "unevaluable:str-order@not-needed");
        assert_eq!(tag(&s, &[e, lt], &m, true), "violated:word-eq@not-needed");
        // Without the strict gate an undecided assertion is not a failure.
        assert_eq!(tag(&s, &[lt, e], &m, false), "violated:word-eq@not-needed");
    }

    #[test]
    fn uninterpreted_bool_constant_is_other_uf() {
        let (mut s, x, _) = fx();
        let bs = s.ctx_mut().bool_sort();
        let pf = s.declare_fun("p", &[], bs);
        let p = s.app(Op::Uninterpreted(pf), &[]);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[p], &m, true), "unevaluable:other:uf@not-needed");
    }

    #[test]
    fn rebuild_suffix_and_unclassified_fallback() {
        let (s, x, _) = fx();
        let m = strs(&[(x, "a")]);
        assert_eq!(
            s.model_reject_detail(&[], &m, true, RebuildOutcome::Budget),
            "unclassified:none@budget"
        );
    }

    #[test]
    fn tag_safe_replaces_whitespace() {
        assert_eq!(tag_safe("(_ extract 7 0)"), "(_extract_7_0)");
        assert_eq!(tag_safe("str.in_re"), "str.in_re");
    }

    /// Review Focus 3: a 60-level shared `str.++` doubling. A tree walk would
    /// visit 2^60 nodes; the visited-set walk visits 61.
    #[test]
    fn shared_dag_classifies_in_linear_time() {
        let (mut s, x, _) = fx();
        let mut t = x;
        for _ in 0..60 {
            t = b(&mut s, BuiltinOp::StrConcat, &[t, t]);
        }
        let len = b(&mut s, BuiltinOp::StrLen, &[t]);
        let zero = int(&mut s, 0);
        let a = s.eq(len, zero);
        let m = Model::default(); // x unvalued: eval stops at the first leaf
        let t0 = std::time::Instant::now();
        assert_eq!(tag(&s, &[a], &m, true), "unevaluable:len-arith@not-needed");
        assert!(t0.elapsed().as_secs() < 2, "{:?}", t0.elapsed());
    }
}
```

In `crates/shinri-solver/src/lib.rs`, add `mod model_reject;` after `mod model;`.

- [ ] **Step 3: Run the tests to verify they fail**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'test(/^model_reject::/)'`
Expected: compile error (`tag_safe` not found). Temporarily that is the failure; after Step 4 all 15 tests are discovered.

- [ ] **Step 4: Implement the classifier**

Replace the `impl Solver` block in `crates/shinri-solver/src/model_reject.rs` with:

```rust
impl Solver {
    /// The detail tag for a model that `string_model_satisfies(assertions,
    /// model, strict)` rejected: the first failing assertion in order
    /// decides the mode and kind (spec §4.1). `unclassified:none` only if
    /// nothing fails, which the gate's own rejection rules out.
    pub(crate) fn model_reject_detail(
        &self,
        assertions: &[TermId],
        model: &Model,
        strict: bool,
        rebuild: RebuildOutcome,
    ) -> String {
        let (mode, kind) = self
            .first_failure(assertions, model, strict)
            .unwrap_or(("unclassified", "none".to_owned()));
        format!("{mode}:{kind}@{}", rebuild.as_str())
    }

    /// Mirror of `string_model_satisfies`: the first assertion that is
    /// definitely false, or (strict gate only) undecided.
    fn first_failure(
        &self,
        assertions: &[TermId],
        model: &Model,
        strict: bool,
    ) -> Option<(&'static str, String)> {
        for &a in assertions {
            match self.eval_bool(a, model) {
                Some(true) => {}
                Some(false) => {
                    let (atom, neg) = self.strip_not(a);
                    return Some(("violated", polarised(neg, self.kind_of(atom))));
                }
                None if strict => {
                    let (leaf, neg) = self.first_none_leaf(a, false, model);
                    return Some(("unevaluable", polarised(neg, self.kind_of(leaf))));
                }
                None => {}
            }
        }
        None
    }

    /// Strip outer `not`s, returning the atom and whether an odd number was
    /// stripped.
    fn strip_not(&self, mut t: TermId) -> (TermId, bool) {
        let mut neg = false;
        while let TermNode::App {
            op: Op::Builtin(BuiltinOp::Not),
            args,
            ..
        } = self.ctx.term_node(t)
        {
            let kids = self.ctx.children(*args);
            if kids.len() != 1 {
                break;
            }
            t = kids[0];
            neg = !neg;
        }
        (t, neg)
    }

    /// `t` evaluates to `None`. Descend its Boolean skeleton to the first
    /// child (left to right; for `ite`, the condition or the chosen branch)
    /// that is also undecided; the first non-connective reached is the leaf
    /// the evaluator cannot decide. `neg` tracks `not`s on the way down.
    fn first_none_leaf(&self, t: TermId, neg: bool, model: &Model) -> (TermId, bool) {
        let TermNode::App {
            op: Op::Builtin(b),
            args,
            ..
        } = self.ctx.term_node(t)
        else {
            return (t, neg);
        };
        let b = *b;
        let kids = self.ctx.children(*args).to_vec();
        let bool_sort = self.ctx.bool_sort();
        let connective = match b {
            BuiltinOp::Not
            | BuiltinOp::And
            | BuiltinOp::Or
            | BuiltinOp::Implies
            | BuiltinOp::Xor => true,
            BuiltinOp::Ite => kids.len() == 3,
            BuiltinOp::Eq | BuiltinOp::Distinct => kids
                .first()
                .is_some_and(|&k| self.ctx.sort_of(k) == bool_sort),
            _ => false,
        };
        if !connective {
            return (t, neg);
        }
        let candidates: Vec<TermId> = if b == BuiltinOp::Ite {
            match self.eval_bool(kids[0], model) {
                None => vec![kids[0]],
                Some(true) => vec![kids[1]],
                Some(false) => vec![kids[2]],
            }
        } else {
            kids
        };
        let child_neg = if b == BuiltinOp::Not { !neg } else { neg };
        for k in candidates {
            if self.eval_bool(k, model).is_none() {
                return self.first_none_leaf(k, child_neg, model);
            }
        }
        (t, neg)
    }

    /// The §4.1 kind of an atom (outer `not`s already stripped).
    fn kind_of(&self, atom: TermId) -> String {
        if self.mentions_int_conv(atom) {
            return "int-conv".to_owned();
        }
        let (op, kids) = match self.ctx.term_node(atom) {
            TermNode::App { op, args, .. } => (*op, self.ctx.children(*args)),
            _ => return "other:leaf".to_owned(),
        };
        let b = match op {
            Op::Builtin(b) => b,
            Op::Uninterpreted(_) => return "other:uf".to_owned(),
        };
        let sort0 = kids.first().map(|&k| self.ctx.sort_of(k));
        let string_s = Some(self.ctx.string_sort());
        let bool_s = Some(self.ctx.bool_sort());
        let numeric = sort0 == Some(self.ctx.int_sort()) || sort0 == Some(self.ctx.real_sort());
        let kind = match b {
            BuiltinOp::Eq if sort0 == string_s => "word-eq",
            BuiltinOp::Distinct if sort0 == string_s => "str-diseq",
            BuiltinOp::Eq | BuiltinOp::Distinct if sort0 == bool_s => "bool",
            BuiltinOp::Eq | BuiltinOp::Distinct if numeric => "len-arith",
            BuiltinOp::Le | BuiltinOp::Lt | BuiltinOp::Ge | BuiltinOp::Gt => "len-arith",
            BuiltinOp::StrInRe => "memb",
            BuiltinOp::StrContains | BuiltinOp::StrPrefixOf | BuiltinOp::StrSuffixOf => {
                "str-pred"
            }
            BuiltinOp::StrLt | BuiltinOp::StrLeq => "str-order",
            BuiltinOp::Not
            | BuiltinOp::And
            | BuiltinOp::Or
            | BuiltinOp::Implies
            | BuiltinOp::Xor
            | BuiltinOp::Ite => "bool",
            other => {
                return format!(
                    "other:{}",
                    tag_safe(&shinri_core::smtlib_print::builtin_name(other))
                )
            }
        };
        kind.to_owned()
    }

    /// Whether a string/int conversion occurs anywhere under `t`
    /// (visited-set walk: linear in the shared DAG).
    fn mentions_int_conv(&self, t: TermId) -> bool {
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut stack = vec![t];
        while let Some(u) = stack.pop() {
            if !seen.insert(u) {
                continue;
            }
            if let TermNode::App { op, args, .. } = self.ctx.term_node(u) {
                if matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::StrToInt
                            | BuiltinOp::StrFromInt
                            | BuiltinOp::StrToCode
                            | BuiltinOp::StrFromCode
                    )
                ) {
                    return true;
                }
                stack.extend_from_slice(self.ctx.children(*args));
            }
        }
        false
    }
}

fn polarised(neg: bool, kind: String) -> String {
    if neg {
        format!("not-{kind}")
    } else {
        kind
    }
}

/// A tag never contains whitespace: the `stats:` line is split on it.
fn tag_safe(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_whitespace() { '_' } else { c })
        .collect()
}
```

- [ ] **Step 5: Run the module tests to verify they pass**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'test(/^model_reject::/)'`
Expected: 15 tests discovered, all PASS. If `violated_str_diseq`'s head precondition fails (the context rewrote `distinct`), report it rather than changing the expected tag: the lowered form decides what the bench will show.

- [ ] **Step 6: Write the failing end-to-end test**

Append to `crates/shinri-solver/tests/fence_tags.rs`:

```rust
/// The §4.1 grammar: `<mode>:<kind>@<rebuild>`, no whitespace.
fn well_formed_detail(tag: &str) -> bool {
    let Some((head, rebuild)) = tag.rsplit_once('@') else {
        return false;
    };
    let Some((mode, kind)) = head.split_once(':') else {
        return false;
    };
    matches!(mode, "violated" | "unevaluable")
        && !kind.is_empty()
        && matches!(rebuild, "not-needed" | "adopted" | "rejected" | "budget")
        && !tag.contains(char::is_whitespace)
}

/// Slice 59: a `str-model-rejected` carries a well-formed detail, and the
/// next `check-sat` clears it (Review Focus 1). The first query is the
/// slice-58 `g1` guard shape, `unknown fence=str-model-rejected` at `de96d28`.
#[test]
fn str_model_rejected_detail_clears_on_next_check() {
    let src = "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
        (assert (str.prefixof \"a\" x))(assert (= x y))\
        (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))(check-sat)\
        (assert false)(check-sat)";
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut seen = Vec::new();
    while let Some(r) = parser.next_command(solver.ctx_mut()) {
        let resp = solver.execute(r.expect("fixture parses"));
        if matches!(
            resp,
            CommandResponse::Sat | CommandResponse::Unsat | CommandResponse::Unknown
        ) {
            seen.push((
                resp,
                solver.last_fence(),
                solver.last_fence_detail().map(str::to_owned),
            ));
        }
    }
    assert_eq!(seen.len(), 2);
    assert!(matches!(seen[0].0, CommandResponse::Unknown));
    assert_eq!(seen[0].1, Some("str-model-rejected"));
    let detail = seen[0].2.as_deref().expect("a detail on str-model-rejected");
    assert!(well_formed_detail(detail), "{detail:?}");
    assert!(matches!(seen[1].0, CommandResponse::Unsat));
    assert_eq!((seen[1].1, seen[1].2.as_deref()), (None, None));
}

#[test]
fn other_fences_carry_no_detail() {
    let mut solver = Solver::new();
    let mut parser = Parser::new(
        "(set-logic QF_S)(declare-fun a () String)(declare-fun b () String)\
         (assert (str.< a b))(check-sat)",
    );
    while let Some(r) = parser.next_command(solver.ctx_mut()) {
        solver.execute(r.expect("fixture parses"));
    }
    assert_eq!(solver.last_fence(), Some("str-order"));
    assert_eq!(solver.last_fence_detail(), None);
}
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(fence_tags)'`
Expected: compile error, `last_fence_detail` not found.

- [ ] **Step 7: Wire `last_fence_detail` into the solver**

In `crates/shinri-solver/src/lib.rs`:

After the `last_fence` field (`:135`):

```rust
    /// Slice 59: the `str-model-rejected` detail tag (`<mode>:<kind>@<rebuild>`,
    /// spec §4.1) of the most recent `check_sat`; `None` whenever `last_fence`
    /// is anything else. Read by `shinri-cli --stats`.
    last_fence_detail: Option<String>,
```

In the constructor, after `last_fence: None,` (`:254`): `last_fence_detail: None,`

After `pub fn last_fence` (`:409-411`):

```rust
    /// The detail tag behind a `str-model-rejected` `Unknown` (slice 59), or `None`.
    pub fn last_fence_detail(&self) -> Option<&str> {
        self.last_fence_detail.as_deref()
    }
```

In `check_sat` (`:768`), after `self.last_fence = None;`: `self.last_fence_detail = None;`

After `let strict_gate = mb.strict_check_required();` (`:1359`):

```rust
                // Slice 59: diagnostic only, for the str-model-rejected detail.
                let rebuild = mb.rebuild_outcome();
```

At the gate (`:1495-1498`):

```rust
                if on_string_path && !self.string_model_satisfies(&lowered, &model, strict_gate) {
                    self.last_fence = Some("str-model-rejected");
                    self.last_fence_detail =
                        Some(self.model_reject_detail(&lowered, &model, strict_gate, rebuild));
                    return SolveOutcome::Unknown;
                }
```

- [ ] **Step 8: Run the solver tests to verify they pass**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(fence_tags) + test(/^model_reject::/) + test(/slice52_gate_tests/)'`
Expected: all PASS, non-zero count (15 module tests + the `fence_tags` tests + the gate tests).

- [ ] **Step 9: Commit**

```bash
cargo fmt --all
git add crates/shinri-core/src/smtlib_print.rs crates/shinri-solver/src/model_reject.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/fence_tags.rs
git commit -m "feat(slice59): classify str-model-rejected into a detail tag"
```

---

### Task 3: `detail=` on the `stats:` line

**Files:**
- Modify: `crates/shinri-cli/src/driver.rs:162-167`
- Modify: `crates/shinri-cli/src/args.rs:31`
- Modify: `crates/shinri-cli/tests/cli.rs:177-201`

**Interfaces:**
- Consumes: `Solver::last_fence_detail() -> Option<&str>` (Task 2).
- Produces: the line `stats: cmd=check-sat wall_ms=<n> outcome=<o> fence=<f> detail=<d>` (Task 4 parses it).

- [ ] **Step 1: Update and add the failing CLI tests**

In `crates/shinri-cli/tests/cli.rs`, in `stats_line_shape_on_sat` replace the last assertion `assert_eq!(fields.len(), 5);` with:

```rust
    assert_eq!(fields[5], "detail=-");
    assert_eq!(fields.len(), 6);
```

Add after `stats_line_names_the_fence_on_unknown`:

```rust
const REJECTED_THEN_UNSAT: &str = "(set-option :print-success false)\
(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
(assert (str.prefixof \"a\" x))(assert (= x y))\
(assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))(check-sat)\
(assert false)(check-sat)";

/// Slice 59: a `str-model-rejected` names its detail; the next `check-sat`
/// prints `detail=-` (Review Focus 1).
#[test]
fn stats_detail_clears_on_the_next_check_sat() {
    let (stdout, stderr, _) = run_with(&["--stats"], REJECTED_THEN_UNSAT);
    assert_eq!(stdout, "unknown\nunsat\n");
    let lines: Vec<&str> = stderr.lines().filter(|l| l.starts_with("stats:")).collect();
    assert_eq!(lines.len(), 2, "stderr: {stderr:?}");
    let first: Vec<&str> = lines[0].split(' ').collect();
    assert_eq!(first[4], "fence=str-model-rejected");
    let detail = first[5].strip_prefix("detail=").expect("a detail field");
    assert!(detail != "-" && detail.contains(':') && detail.contains('@'), "{detail:?}");
    assert!(lines[1].ends_with("fence=- detail=-"), "{:?}", lines[1]);
}
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-cli -E 'test(stats_line_shape_on_sat) + test(stats_detail_clears_on_the_next_check_sat)'`
Expected: 2 tests, both FAIL (no `detail=` field yet).

- [ ] **Step 2: Print the field**

In `crates/shinri-cli/src/driver.rs`, replace the `eprintln!` in the `--stats` block with:

```rust
            eprintln!(
                "stats: cmd=check-sat wall_ms={} outcome={} fence={} detail={}",
                started.elapsed().as_millis(),
                outcome,
                self.solver.last_fence().unwrap_or("-"),
                self.solver.last_fence_detail().unwrap_or("-")
            );
```

In `crates/shinri-cli/src/args.rs:31`, change `(wall_ms, outcome, and the fence tag behind an unknown)` to `(wall_ms, outcome, the fence tag behind an unknown, and its detail)`. If that edit pushes the help text past its existing column, re-wrap it to match the neighbouring lines.

- [ ] **Step 3: Run the CLI tests to verify they pass**

Run: `taskset -c 0-11 cargo nextest run -p shinri-cli`
Expected: all PASS (non-zero count), including the two from Step 1 and `stats_line_names_the_fence_on_unknown` unchanged.

- [ ] **Step 4: Commit**

```bash
cargo fmt --all
git add crates/shinri-cli/src/driver.rs crates/shinri-cli/src/args.rs crates/shinri-cli/tests/cli.rs
git commit -m "feat(slice59): print the fence detail on the --stats line"
```

---

### Task 4: Bench — parse, store, report

**Files:**
- Modify: `crates/shinri-bench/src/runner.rs` (`:52-53`, Row literals `:99-113`, `:118-132`, `parse_stats_fence` `:196-209`, tests `:337-348`)
- Modify: `crates/shinri-bench/src/results.rs` (`Row` `:115-135`, `to_json` `:146-189`, `from_json` `:241-291`, tests `:415-457`)
- Modify: `crates/shinri-bench/src/report.rs` (`render` `:247-257`, new fn after `render_gaps`, test helper `bare` `:566-582`)
- Modify: `crates/shinri-bench/tests/corpus/stub-solver.sh`; Create: `crates/shinri-bench/tests/corpus/QF_T/rejected.smt2`; Modify: `crates/shinri-bench/tests/runner_e2e.rs`

**Interfaces:**
- Consumes: the Task 3 `stats:` line.
- Produces: `pub fn parse_stats_detail(stderr: &str) -> Option<String>`; `Row.fence_detail: Option<String>`; JSONL key `fence_detail`; report section `## Fence detail`.

- [ ] **Step 1: Write the failing parse test**

In `crates/shinri-bench/src/runner.rs` tests, add:

```rust
    #[test]
    fn detail_from_last_stats_line() {
        let two = "stats: cmd=check-sat wall_ms=3 outcome=unknown fence=str-model-rejected detail=violated:word-eq@adopted\n\
                   stats: cmd=check-sat wall_ms=1 outcome=unknown fence=str-model-rejected detail=unevaluable:str-pred@not-needed\n";
        assert_eq!(
            parse_stats_detail(two),
            Some("unevaluable:str-pred@not-needed".into())
        );
        assert_eq!(
            parse_stats_detail("stats: cmd=check-sat wall_ms=3 outcome=sat fence=- detail=-\n"),
            None
        );
        // Review Focus 4: an older solver prints no detail field.
        assert_eq!(
            parse_stats_detail("stats: cmd=check-sat wall_ms=3 outcome=unknown fence=str-model-rejected\n"),
            None
        );
        assert_eq!(parse_stats_detail("junk\n"), None);
    }
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-bench -E 'test(detail_from_last_stats_line)'`
Expected: compile error, `parse_stats_detail` not found.

- [ ] **Step 2: Implement the parser (shared with `parse_stats_fence`)**

Replace `parse_stats_fence` in `crates/shinri-bench/src/runner.rs` with:

```rust
/// The `fence=` tag of the last `stats:` line, or `None` for `-` / absent.
pub fn parse_stats_fence(stderr: &str) -> Option<String> {
    stats_field(stderr, "fence=")
}

/// The `detail=` tag of the last `stats:` line (slice 59), or `None` for `-`
/// / absent (a solver older than slice 59 prints no `detail=` field).
pub fn parse_stats_detail(stderr: &str) -> Option<String> {
    stats_field(stderr, "detail=")
}

/// The value of `key` on the last `stats:` line, or `None` for `-` / absent.
fn stats_field(stderr: &str, key: &str) -> Option<String> {
    let last = stderr
        .lines()
        .rev()
        .find(|line| line.trim_start().starts_with("stats:"))?;
    let tag = last
        .split_whitespace()
        .find_map(|field| field.strip_prefix(key))?;
    if tag == "-" {
        None
    } else {
        Some(tag.to_string())
    }
}
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-bench -E 'test(detail_from_last_stats_line) + test(fence_from_last_stats_line)'`
Expected: 2 tests PASS.

- [ ] **Step 3: Write the failing `Row` tests**

In `crates/shinri-bench/src/results.rs` tests: in `fn row()` add `fence_detail: Some("violated:word-eq@adopted".into()),` after `fence: None,`; in `row_round_trips` add `assert_eq!(back.fence_detail, r.fence_detail);`; and add:

```rust
    #[test]
    fn older_rows_have_no_fence_detail() {
        // Review Focus 5: a line written before slice 59 still parses.
        let older = r#"{"path":"a.smt2","logic":"QF_S","bytes":7,"status":null,"rc":0,"wall_ms":12,"answers":["unknown"],"fence":"str-model-rejected","stderr_head":"","verdict":"unknown:str-model-rejected","oracle":null}"#;
        let back = Row::from_json(older).expect("older rows stay readable");
        assert_eq!(back.fence.as_deref(), Some("str-model-rejected"));
        assert_eq!(back.fence_detail, None);
    }

    #[test]
    fn fence_detail_is_written_after_fence() {
        let json = row().to_json();
        let f = json.find("\"fence\":").unwrap();
        let d = json.find("\"fence_detail\":\"violated:word-eq@adopted\"").unwrap();
        assert!(f < d);
    }
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-bench`
Expected: compile error, no field `fence_detail` on `Row`.

- [ ] **Step 4: Add the field**

In `crates/shinri-bench/src/results.rs`:

`Row`, after `pub fence: Option<String>,`:

```rust
    /// Slice 59: the solver's `detail=` tag behind a `str-model-rejected`
    /// (`<mode>:<kind>@<rebuild>`); `None` on other rows and on rows written
    /// before the field existed.
    pub fence_detail: Option<String>,
```

`to_json`: after the `let fence = …;` block add

```rust
        let fence_detail = match &self.fence_detail {
            Some(d) => json::escape(d),
            None => "null".to_string(),
        };
```

and change the format string's `\"fence\":{},` to `\"fence\":{},\"fence_detail\":{},` with `fence_detail,` added right after `fence,` in the argument list.

`from_json`: after the `let fence = …;` block add

```rust
        // Absent in files written before the field existed (slice 59).
        let fence_detail = match get("fence_detail") {
            Some(JsonVal::Str(s)) => Some(s),
            _ => None,
        };
```

and add `fence_detail,` after `fence,` in the `Some(Row { … })` literal.

In `crates/shinri-bench/src/runner.rs`: after `let fence = parse_stats_fence(&exec.stderr);` add `let fence_detail = parse_stats_detail(&exec.stderr);`; add `fence_detail,` after `fence,` in the `run_one` row literal; add `fence_detail: None,` after `fence: None,` in `bare_row`.

In `crates/shinri-bench/src/report.rs` tests, `fn bare`: add `fence_detail: None,` after `fence: None,`.

Run: `taskset -c 0-11 cargo nextest run -p shinri-bench`
Expected: all PASS, including `report_matches_golden` unchanged.

- [ ] **Step 5: Write the failing report tests**

In `crates/shinri-bench/src/report.rs` tests, add:

```rust
    #[test]
    fn fence_detail_section_ranks_tags_per_fence() {
        let mk = |logic: &str, path: &str, bytes: u64, tag: &str| {
            let mut r = bare(Verdict::Unknown("str-model-rejected".into()));
            r.logic = logic.into();
            r.path = path.into();
            r.bytes = bytes;
            r.fence = Some("str-model-rejected".into());
            r.fence_detail = Some(tag.into());
            r
        };
        let rows = vec![
            mk("QF_SLIA", "QF_SLIA/b.smt2", 50, "violated:word-eq@not-needed"),
            mk("QF_S", "QF_S/a.smt2", 10, "violated:word-eq@not-needed"),
            mk("QF_SLIA", "QF_SLIA/c.smt2", 5, "unevaluable:str-pred@adopted"),
        ];
        let md = render(None, &rows);
        let at = md.find("## Fence detail").expect("section present");
        let sec = &md[at..];
        assert!(
            sec.starts_with("## Fence detail\n\n### str-model-rejected — 3\n\n"),
            "{sec}"
        );
        let first = sec
            .find("| violated:word-eq@not-needed | 1 | 1 | 2 | `QF_S/a.smt2` |")
            .expect("word-eq row");
        let second = sec
            .find("| unevaluable:str-pred@adopted | 0 | 1 | 1 | `QF_SLIA/c.smt2` |")
            .expect("str-pred row");
        assert!(first < second, "ranked by count");
        assert!(md.find("## Ranked gaps").unwrap() < at);
        assert!(at < md.find("## Wrong answers").unwrap());
    }

    #[test]
    fn fence_detail_section_absent_without_details() {
        let mut r = bare(Verdict::Unknown("str-order".into()));
        r.fence = Some("str-order".into());
        assert!(!render(None, &[r]).contains("## Fence detail"));
    }
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-bench -E 'test(/fence_detail_section/)'`
Expected: 2 tests; `ranks_tags_per_fence` FAILS (no section), `absent_without_details` PASSES.

- [ ] **Step 6: Implement the section**

In `crates/shinri-bench/src/report.rs`, add `render_fence_detail(&mut out, rows);` right after `render_gaps(&mut out, rows);` in `render`, update `render`'s doc to `/// Render the full Markdown report: fixture header, per-logic matrix, ranked\n/// gaps, fence detail (only when some row has one), wrong answers, perf tail.`, and add after `render_gaps`:

```rust
/// Slice 59: each fence's `fence_detail` tags, ranked by count. Omitted when
/// no row carries a detail, so runs from before slice 59 render unchanged.
fn render_fence_detail(out: &mut String, rows: &[Row]) {
    let mut by_fence: BTreeMap<&str, BTreeMap<&str, Bucket>> = BTreeMap::new();
    for row in rows {
        let (Some(fence), Some(tag)) = (row.fence.as_deref(), row.fence_detail.as_deref()) else {
            continue;
        };
        by_fence
            .entry(fence)
            .or_default()
            .entry(tag)
            .or_default()
            .add(row);
    }
    if by_fence.is_empty() {
        return;
    }
    out.push_str("## Fence detail\n\n");
    for (fence, tags) in &by_fence {
        let total: usize = tags.values().map(|b| b.count).sum();
        let _ = writeln!(out, "### {} — {}\n", cell(fence), total);
        out.push_str("| detail | QF_S | QF_SLIA | total | example |\n");
        out.push_str("| --- | ---: | ---: | ---: | --- |\n");
        // Count descending, then tag ascending.
        let mut ranked: Vec<(&&str, &Bucket)> = tags.iter().collect();
        ranked.sort_by(|a, b| b.1.count.cmp(&a.1.count).then_with(|| a.0.cmp(b.0)));
        for (tag, b) in ranked {
            let n = |logic: &str| b.per_logic.get(logic).copied().unwrap_or(0);
            let example = b.examples.first().map_or("", |(_, p)| *p);
            let _ = writeln!(
                out,
                "| {} | {} | {} | {} | `{}` |",
                cell(tag),
                n("QF_S"),
                n("QF_SLIA"),
                b.count,
                example
            );
        }
        out.push('\n');
    }
}
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-bench`
Expected: all PASS, including both new tests and `report_matches_golden` (golden byte-identical: its fixture rows carry no detail).

- [ ] **Step 7: Make the stub solver emit a detail; extend the runner e2e**

Create `crates/shinri-bench/tests/corpus/QF_T/rejected.smt2` with the single line:

```
(set-info :status sat)
```

In `crates/shinri-bench/tests/corpus/stub-solver.sh`, change the `sat.smt2` and `unsat.smt2` lines to end in `fence=- detail=-"` and add, before the `*)` line:

```sh
  rejected.smt2) echo unknown; echo "stats: cmd=check-sat wall_ms=1 outcome=unknown fence=str-model-rejected detail=violated:word-eq@not-needed" >&2 ;;
```

In `crates/shinri-bench/tests/runner_e2e.rs`: rename the module doc to `//! The runner end-to-end over a seven-file mini-corpus and a stub solver.`, rename the test to `seven_verdicts_from_the_stub_solver`, change every `6` count to `7` (`insts.len()`, `seen_progress.len()`, `seen_progress[5].0 == 6` → `seen_progress[6].0 == 7`, `*total == 7`, `seen.len() == 7`), and add after the `crash.smt2` assertion:

```rust
    assert_eq!(
        by["QF_T/rejected.smt2"],
        Verdict::Unknown("str-model-rejected".into())
    );
    let detail = |p: &str| {
        rows.iter()
            .find(|r| r.path == p)
            .unwrap()
            .fence_detail
            .clone()
    };
    assert_eq!(
        detail("QF_T/rejected.smt2").as_deref(),
        Some("violated:word-eq@not-needed")
    );
    assert_eq!(detail("QF_T/sat.smt2"), None);
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-bench -E 'binary(runner_e2e)'`
Expected: 1 test discovered, PASS (if the e2e prints `skipping:` because `prlimit`/`timeout` are missing, it is not real coverage: report it).

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-bench
git commit -m "feat(bench): slice59 - fence_detail in results and a Fence detail report section"
```

---

### Task 5: Gates

**Files:** none.

- [ ] **Step 1: Full blocking tier**

Run: `taskset -c 0-11 mise run ci 2>&1 | tee target/slice59-ci.log | tail -30`
Expected: exit 0; nextest summary all passed (slice-58 baseline: 1735 passed, 6 skipped; this slice adds tests, so the count rises).

- [ ] **Step 2: Oracle suite**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice59-oracle-suite.log | tail -15`
Expected: 808 passed, 2 skipped (the slice-58 count, spec §8 criterion 5). A count of 0 means the feature was not enabled: that is not a pass.

- [ ] **Step 3: Record**

```bash
{ echo "gates:"; tail -3 target/slice59-ci.log; tail -3 target/slice59-oracle-suite.log; } > target/slice59-gates.txt
cat target/slice59-gates.txt
```

Nothing to commit.

---

### Task 6: After runs, triage, timing, classification report, measured outcomes, PR

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice59-model-rejected-classes-report.md` (date = the day the after runs finish)
- Modify: `docs/superpowers/specs/2026-10-04-shinri-slice59-model-rejected-classes-design.md` (append *Measured outcomes*; if the report date is not 2026-10-04, fix the report path in spec §8)

**Interfaces:**
- Consumes: branch HEAD after Tasks 1–4; `bench/results/slice59-base*/results.jsonl`; `target/slice59-base/shinri`; `target/slice59-sample-corpus/`.
- Produces: the report and spec section cited by the PR.

- [ ] **Step 1: Wait for the base runs**

Wait for `target/slice59-base/finished.txt` (use a Monitor/until-loop, not a foreground sleep). Then confirm: `wc -l bench/results/slice59-base/results.jsonl bench/results/slice59-base-sample/results.jsonl` (103,335 + 1 and 2,000 + 1 lines).

- [ ] **Step 2: Build and launch the after runs detached**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice59-after && cp target/release/shinri target/slice59-after/shinri
md5sum target/slice59-after/shinri | tee target/slice59-after/md5.txt
git rev-parse --short HEAD | tee target/slice59-after/commit.txt
date -u +%FT%TZ > target/slice59-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice59-after/shinri --run-id slice59 \
  > target/slice59-after/run.log 2>&1; \
  taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice59-after/shinri --run-id slice59-sample \
  > target/slice59-after/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice59-after/finished.txt' \
  > /dev/null 2>&1 &
```

Wait for `target/slice59-after/finished.txt` the same way.

- [ ] **Step 3: Render reports and join the runs (criteria 1–3)**

```bash
for id in slice59-base slice59 slice59-base-sample slice59-sample; do BENCH_RUN_ID=$id mise run bench-report; done
python3 - <<'EOF'
import json, collections
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
changed = []
for base, after in (("slice59-base", "slice59"), ("slice59-base-sample", "slice59-sample")):
    a = load(f"bench/results/{base}/results.jsonl")
    b = load(f"bench/results/{after}/results.jsonl")
    assert a.keys() == b.keys(), f"row sets differ: {base} vs {after}"
    c = collections.Counter()
    for p in sorted(a):
        va, vb = a[p]["verdict"], b[p]["verdict"]
        if va != vb:
            c[(a[p]["logic"], va, vb)] += 1
            changed.append((p, a[p]["logic"], va, vb, after))
    print(f"== {base} -> {after}: {sum(c.values())} changed")
    for k, n in sorted(c.items()):
        print(" ", *k, n)
    print("  wrong rows after:", sum(1 for r in b.values() if r["verdict"] == "wrong"))
    rej = [r for r in b.values() if r["verdict"] == "unknown:str-model-rejected"]
    print("  str-model-rejected:", len(rej),
          "missing detail:", sum(1 for r in rej if not r.get("fence_detail")),
          "stray detail:", sum(1 for r in b.values() if r.get("fence_detail") and r["verdict"] != "unknown:str-model-rejected"))
open("target/slice59-after/changed.tsv", "w").write(
    "".join("\t".join(x) + "\n" for x in changed))
EOF
```

Expected: 0 wrong rows in both after runs (criterion 1); `missing detail: 0` and `stray detail: 0` (criterion 3); every changed row is a timing flip for Step 4 to confirm (criterion 2). Any `wrong` row stops the slice for a ruling.

- [ ] **Step 4: Triage every changed row (criterion 2)**

3 runs per binary, interleaved, the bench's command line, on cores 12–23 with nothing else running. Sample rows live under `target/slice59-sample-corpus`, string rows under `bench/corpus`:

```bash
while IFS="$(printf '\t')" read -r p logic va vb run; do
  case "$run" in *sample) root=target/slice59-sample-corpus ;; *) root=bench/corpus ;; esac
  for i in 1 2 3; do
    for bin in target/slice59-base/shinri target/slice59-after/shinri; do
      r=$(taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats $root/$p 2>&1 \
          | grep -E '^(sat|unsat|unknown)$|^stats:' | tr '\n' ' ')
      printf '%s\t%s\t%s\t%s\n' "$p" "$(basename $(dirname $bin))" "$i" "$r"
    done
  done
done < target/slice59-after/changed.tsv | tee target/slice59-after/triage.tsv
```

If more than 200 rows changed, triage a stratified sample of at least 32 rows across families and state its size. A row is *noise* if either binary's 3 runs disagree with each other or the two binaries agree on at least one run; *attributable* if each binary reproduces its own bench verdict 3/3 and they differ. Any attributable row fails criterion 2: stop the slice for a ruling. A wrong answer from either binary stops the slice (criterion 1).

- [ ] **Step 5: Timing (criterion 4)**

```bash
python3 - <<'EOF'
import json, random, subprocess, time
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
a = load("bench/results/slice59-base/results.jsonl")
b = load("bench/results/slice59/results.jsonl")
rng = random.Random(59)
groups = {lg: sorted(p for p in a if a[p]["logic"] == lg and a[p]["verdict"] == b[p]["verdict"] == "correct")
          for lg in ("QF_S", "QF_SLIA")}
groups["str-model-rejected"] = sorted(p for p in a if a[p]["verdict"] == b[p]["verdict"] == "unknown:str-model-rejected")
for name, rows in groups.items():
    sample = rng.sample(rows, min(150, len(rows)))
    tot = {"base": 0.0, "after": 0.0}
    for p in sample:
        for which in ("base", "after"):
            t0 = time.monotonic()
            subprocess.run(["taskset", "-c", "12", f"target/slice59-{which}/shinri", f"bench/corpus/{p}"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
            tot[which] += time.monotonic() - t0
    print(name, len(sample), "rows: base %.2f s, after %.2f s, ratio %.3f"
          % (tot["base"], tot["after"], tot["after"] / tot["base"]))
EOF
```

Expected: each of the three ratios within 0.95–1.05. Also report median/p90 `wall_ms` per logic over both-`correct` rows from the two `results.jsonl`.

- [ ] **Step 6: Rank the classes (criterion 6)**

```bash
python3 - <<'EOF' | tee target/slice59-after/classes.txt
import json, collections
rows = [r for r in map(json.loads, open("bench/results/slice59/results.jsonl")) if "path" in r]
rej = [r for r in rows if r["verdict"] == "unknown:str-model-rejected"]
N = len(rej)
print("population", N)
for label, key in (("mode", lambda t: t.split(":", 1)[0]), ("rebuild", lambda t: t.rsplit("@", 1)[1])):
    c = collections.Counter(key(r["fence_detail"]) for r in rej)
    print(label, dict(c.most_common()))
by = collections.defaultdict(list)
for r in rej:
    by[r["fence_detail"]].append(r)
ranked = sorted(by.items(), key=lambda kv: (-len(kv[1]), kv[0]))
cum, top = 0, []
for tag, rs in ranked:
    st = collections.Counter(r["status"] or "none" for r in rs)
    lg = collections.Counter(r["logic"] for r in rs)
    fam = collections.Counter("/".join(r["path"].split("/")[1:3]) for r in rs).most_common(3)
    small = min(rs, key=lambda r: (r["bytes"], r["path"]))
    print(f'{len(rs):5} {tag:48} QF_S={lg["QF_S"]} QF_SLIA={lg["QF_SLIA"]} '
          f'sat={st["sat"]} unsat={st["unsat"]} none={st["none"]} fam={fam} '
          f'min={small["path"]} ({small["bytes"]} B)')
    if cum < 0.8 * N and len(top) < 8:
        top.append(tag)
        cum += len(rs)
print("top classes", len(top), "cover", cum, "/", N, f"{cum / N:.1%}")
print("TOP", top)
EOF
```

Expected: the top set covers ≥80% (criterion 6). If the 8-class cap is reached below 80%, stop and report the coverage for a ruling (the tag may be too fine-grained); do not change the grammar unilaterally.

- [ ] **Step 7: Place the slice-58 guards**

```bash
H='(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)'
mkdir -p target/slice59-after/guards
printf '%s%s(check-sat)\n' "$H" '(assert (str.prefixof "a" x))(assert (= x y))(assert (str.in_re y (re.+ (re.range "a" "b"))))' > target/slice59-after/guards/g1.smt2
printf '%s%s(check-sat)\n' "$H" '(assert (= 2 (str.len x)))(assert (= x y))(assert (str.in_re y (re.* (re.union (re.range "a" "b") (str.to_re "1")))))(assert (str.prefixof "1" x))' > target/slice59-after/guards/g3.smt2
printf '%s%s(check-sat)\n' "$H" '(assert (str.prefixof "" x))(assert (= x y))(assert (str.in_re y (re.+ (re.range "a" "b"))))' > target/slice59-after/guards/rf2.smt2
printf '%s%s(check-sat)\n' "$H" '(assert (str.prefixof "\u{e9}" x))(assert (= x y))(assert (str.in_re y (re.* (re.range "\u{e0}" "\u{ff}"))))' > target/slice59-after/guards/rf3.smt2
printf '%s%s(check-sat)\n' "$H" '(assert (str.prefixof "a" x))(assert (str.in_re (str.++ x "b") (re.* (re.range "a" "b"))))' > target/slice59-after/guards/rf4.smt2
for g in g1 g3 rf2 rf3 rf4; do printf '%s\t' $g; target/slice59-after/shinri --stats target/slice59-after/guards/$g.smt2 2>&1 | grep '^stats:'; done | tee target/slice59-after/guards.txt
```

Expected: `g1`, `g3`, `rf2`, `rf3` print `fence=str-model-rejected detail=<tag>`; `rf4` prints `fence=sat-budget detail=-` (outside the population). Note each tag's rank in `classes.txt`.

- [ ] **Step 8: Offline class-shape analysis of the top reproducers**

For each tag in `TOP` (Step 6), take its `min=` reproducer. Trace it with throwaway debug output that is **not committed** (`git stash` or `git checkout -- crates` afterwards; confirm `git status` is clean):
- in the solver gate, `eprintln!` the failing assertion (`shinri_core::smtlib_print::print_term`) and the model values of its string leaves;
- in `StrSolver::model_with`, `eprintln!` for the failing assertion's string sides: the EUF class members, which members are concats, which are minted (`self.minted_eqs`), constant head/tail of each concat, and whether the class sits on a concat cycle.

Record per class: the failing assertion, its shape bucket (minted concat in class / constant head / constant tail / several concats / cycle / evaluator gap), and whether it matches a parked item: constant-head strip, cited deep NF on the word-equation path, minted length links, suffix G′ (a constant tail on a membership member). Save the notes in `target/slice59-after/shapes.md` for the report.

- [ ] **Step 9: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-04-smtlib-2024-slice58-member-prefix-report.md`:
- *Headline*: population size, mode split, the top classes and their coverage, the recommended next slice
- *Commands*: the exact commands from Tasks 0 and 6
- *Runs*: both binaries with md5, started/finished, row counts for all four runs
- *Success criteria*: spec §8 table, each PASS/FAIL with evidence (gates from `target/slice59-gates.txt`)
- *Verdict neutrality*: string runs and sample, transition counts, triage dispositions
- *Timing*: the three ratios and median/p90
- *Classes*: the ranked table from `classes.txt` (per logic, by corpus status, top families), the mode and rebuild splits
- *Top classes*: for each, the smallest reproducer (path, bytes, inline script if under ~1 KB), its shape analysis from `shapes.md`
- *Slice-58 guards*: `guards.txt` with each tag's class rank
- *Parked items*: a ruling per item (reproducer named, or stays parked) — constant-head strip; cited deep NF on the word-equation path; minted length links; suffix G′
- *What changed versus the spec*: every deviation
- *Queued for the next slice*: the recommended fix slice first (with its reproducers), then slice-58 queue items 2 onward and its carried lists, copied verbatim, re-ranked only where the classification says so (state each re-rank)

- [ ] **Step 10: Append *Measured outcomes* to the spec**

Replace `Filled in after the bench runs.` under spec §11 with: a one-line pointer to the report, the criteria table with PASS/FAIL and the key numbers (as slice 58 §11 does), the top-class list with counts, and a *Deviations from this spec* subsection.

- [ ] **Step 11: Commit and open the PR**

```bash
git add docs/superpowers/research docs/superpowers/specs/2026-10-04-shinri-slice59-model-rejected-classes-design.md
git commit -m "docs(bench+spec): slice59 - classification run and measured outcomes"
git push -u origin slice59-model-rejected-classes
gh pr create --base main --title "slice59: classify the str-model-rejected population" --body "$(cat <<'EOF'
Spec: docs/superpowers/specs/2026-10-04-shinri-slice59-model-rejected-classes-design.md
Plan: docs/superpowers/plans/2026-10-04-shinri-slice59-model-rejected-classes.md
Report: docs/superpowers/research/<date>-smtlib-2024-slice59-model-rejected-classes-report.md

Adds a `<mode>:<kind>@<rebuild>` detail to `str-model-rejected` (solver → `--stats` `detail=` → bench `fence_detail` → report "Fence detail"), verdict-neutral, and ranks the population's classes.

<criteria table and top classes from spec §11>
EOF
)"
```

Fill the `<date>` and the criteria/top-class lines from the report before running. Then wait for CI; when it is green, ask the user before merging (merge commit, then delete the branch remote and local).
