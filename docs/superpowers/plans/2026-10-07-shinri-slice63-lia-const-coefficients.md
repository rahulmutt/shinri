# Slice 63 — Constant coefficients in linear arithmetic Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stop refusing linear products whose constant factor is a unary minus over a numeral (`(* (- 4) x)`, `(* x (- 4))`). This shape alone accounts for all 4,874 `unknown:theory-refused` rows (QF_LIA 4,764).

**Architecture:** `Context::const_real_value` already folds a numeral or a unary `(- c)` to its exact `Rational`. It is renamed `const_arith_value`, keeping `const_real_value` as an alias so the FP fence is untouched. The three sites that decide whether a factor is constant switch to it: `contains_nonlinear_mul` (shinri-theory), and `is_linear_arith` plus `linearize`'s `Mul` arm (shinri-arith). A proptest pins that the three agree. E2E and z3 oracle tests check that the folded coefficient keeps its sign. A base/after bench over the refused rows plus three neutrality samples closes the slice.

**Tech Stack:** Rust workspace (toolchain pinned in `mise.toml`), cargo-nextest 0.9.140, `proptest` (existing dev-dependency of shinri-arith), z3/cvc5 from mise via the existing `easy-smt` dev-dependency, `shinri-bench`, python3 for analysis scripts.

**Spec:** `docs/superpowers/specs/2026-10-07-shinri-slice63-lia-const-coefficients-design.md`

## Global Constraints

- Scope (spec §2, §5): no change to term interning, the parser, the printer, `get-value` echo, string or FP semantics, the `lira` / `saw_shared` fences, simplex, or branch-and-bound. No folding of all-constant compound coefficients (`(* (+ 1 2) x)` stays refused).
- **Leave `is_compound_arith` (`crates/shinri-arith/src/lib.rs:193`) and the `numeral_value` pin in `ensure_shared_var` (`crates/shinri-arith/src/lib.rs:725`) unchanged.** A shared `(- 4)` must stay a compound, so slice 50's `define_shared_compound` pins it. Switching either to `const_arith_value` would make it opaque, unpinned and free, which is a wrong-`sat` risk. `normalize.rs`'s top-of-`linearize` `numeral_value` early return also stays; its `Neg` arm already handles `(- 4)`.
- `const_real_value` keeps its name and behaviour as a one-line alias. `crates/shinri-solver/src/fp_stage.rs` is not edited.
- Existing tests keep their assertions. The one allowed existing-file test edit is the doc comment on `smt2_real_coeff_times_var` in `crates/shinri-solver/tests/oracle.rs` (Task 3); its generator code stays byte-identical. Any other existing-test failure: stop and report; do not edit it.
- No new dependency of any kind (pure-Rust mandate).
- Oracle tests only run with `--features oracle`; without it they silently run 0 tests. Always confirm a non-zero discovered count (AGENTS.md).
- nextest filters use the expression form `-E 'test(<name>)'` / `-E 'binary(<name>)'` (AGENTS.md).
- `cargo fmt --all` before every commit; `mise run lint` (clippy `-D warnings`) must be clean.
- Work happens in the worktree `/workspace/.claude/worktrees/slice63` on branch `slice63-lia-const-coefficients`. Bench corpora, results and binaries live in the **main checkout** (`/workspace/bench/corpus`, `/workspace/bench/results`, `/workspace/target/slice63-*`), always passed by absolute path. Hard-linked sample corpora must stay on the same filesystem as `bench/corpus`.
- Cross-track host rule: bench runs use `--jobs 3` under `taskset -c 12-23`, detached with `setsid`. Builds and tests run under `taskset -c 0-11` while any bench is live. There's no timing criterion in this slice.
- PR to `main`, merge commit when CI is green, then delete the branch remote and local (AGENTS.md). **Ask the user before merging.**

## Review Focus

1. **A shared `(- k)` or `(* (- 1) y)` under a UF (QF_UFLIA purification).** Expected: the term stays pinned to its value or linearization, and `y = -4 ∧ f(y) = 0 ∧ f(-4) = 1` is `unsat`, as is `y = -4 ∧ f(4) = 0 ∧ f((* (- 1) y)) = 1`. Pinned in Task 3 (`slice63_shared_neg_numeral_stays_pinned`, `slice63_shared_neg_coeff_compound_is_pinned`).
2. **The sign of the folded coefficient.** A fix that accepts `(* (- 4) x)` but linearizes it as `4x` turns `−4x ≤ 3 ∧ x ≤ −1` from `unsat` into `sat`. Expected: `unsat`. Pinned in Task 1 (`linearize_folds_negated_numeral_coefficients`) and Task 3 (`slice63_neg_coeff_left_sign_unsat`), and swept by Task 4's oracle.
3. **A Real decimal coefficient in mirrored position** (`(* r (- 2.5))`, QF_LRA). Expected: `−2.5r > 5 ∧ r > −2` is `unsat`, and dropping the second conjunct is `sat`. Pinned in Task 3 (`slice63_real_neg_decimal_coeff`).
4. **Double negation and all-constant products** (`(* (- (- 4)) x)`, `(* (- 3) (- 5))`, `(* x (- 4) 2)`). Expected: coefficients 4, constant 15, coefficient −8. Pinned in Task 1 (unit tests in core, theory, arith).
5. **A negated variable as a factor, or a non-literal constant factor** (`(* (- x) y)`, `(* (+ 1 2) x)`). Expected: still refused by classify and rejected by `is_linear_arith`, and the three sites still agree. Pinned in Task 1 (`negated_variable_times_variable_stays_refused`) and Task 2 (the lockstep proptest generates both shapes).

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-core/src/context.rs` | modify ~1018–1041, tests ~1986 | `const_arith_value` (the shared constant admit set) + `const_real_value` alias |
| `crates/shinri-theory/src/atom.rs` | modify 222–240, tests | classify's nonlinear-product test uses `const_arith_value` |
| `crates/shinri-arith/src/lib.rs` | modify 211–237, add `mod` line | `is_linear_arith` uses `const_arith_value` |
| `crates/shinri-arith/src/normalize.rs` | modify 141–163, tests | `linearize`'s `Mul` arm folds `(- k)` factors |
| `crates/shinri-arith/src/linearity_lockstep_tests.rs` | create | unit tests for `is_linear_arith` + the three-site lockstep proptest |
| `crates/shinri-solver/tests/lia_e2e.rs` | modify (append) | script-level e2e: sign, mirrored, Real, shared-term pins |
| `crates/shinri-solver/tests/neg_coeff_oracle.rs` | create | z3 differential over `(- k)` coefficient shapes (`--features oracle`) |
| `crates/shinri-solver/tests/oracle.rs` | doc comment only (~719–724) | stale "refused as nonlinear" note |
| `docs/superpowers/research/<date>-smtlib-2024-slice63-lia-coefficients-report.md` | create | bench report |
| spec | append §11 | measured outcomes |

---

### Task 0: Worktree, base binary, row sets, base runs

**Files:** none in the repo. Artifacts go under `/workspace/target/slice63-base/` and `/workspace/target/slice63-*-corpus/`, and results under `/workspace/bench/results/slice63-base*`.

**Interfaces:**
- Consumes: local `main` (`c09475d` or later docs-only commits), `/workspace/bench/results/slice53/results.jsonl`, `/workspace/bench/corpus/`, `/workspace/target/slice59-sample-corpus/`.
- Produces: `/workspace/target/slice63-base/{shinri,shinri-bench,md5.txt,commit.txt}`; corpora `/workspace/target/slice63-refused-corpus/`, `/workspace/target/slice63-arith-sample-corpus/`, `/workspace/target/slice63-slia-sample-corpus/`; base runs `bench/results/slice63-base-{refused,arith,sample,slia}`; `/workspace/target/slice63-base/oracle-count.txt`. Task 5 consumes all of them.

- [ ] **Step 1: Create the worktree and branch**

```bash
cd /workspace && git worktree add .claude/worktrees/slice63 -b slice63-lia-const-coefficients main
cd /workspace/.claude/worktrees/slice63 && git log --oneline -1
```

Expected: the head is the slice-63 plan commit on top of `c09475d`.

- [ ] **Step 2: Build the base binaries from the unchanged branch**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 cargo build --release -p shinri-cli -p shinri-bench
mkdir -p /workspace/target/slice63-base
cp target/release/shinri target/release/shinri-bench /workspace/target/slice63-base/
md5sum /workspace/target/slice63-base/shinri | tee /workspace/target/slice63-base/md5.txt
git rev-parse --short HEAD | tee /workspace/target/slice63-base/commit.txt
printf '(set-logic QF_LIA)(declare-fun x () Int)\n(assert (<= (* (- 4) x) 3))\n(check-sat)\n' > /workspace/target/slice63-base/repro.smt2
/workspace/target/slice63-base/shinri --stats /workspace/target/slice63-base/repro.smt2
```

Expected: `stats: … outcome=unknown fence=theory-refused` then `unknown` (spec §1 reproducer).

- [ ] **Step 3: Record the base oracle test count**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee /workspace/target/slice63-base/oracle.log | grep -E 'Starting|Summary'
grep -oE 'Starting [0-9]+ tests' /workspace/target/slice63-base/oracle.log | tee /workspace/target/slice63-base/oracle-count.txt
```

Expected: a non-zero count (slice 62 reported 854 + 2 skipped), and every test passes. If any oracle test fails on unchanged `main`, stop and report.

- [ ] **Step 4: Build the three hard-link row-set corpora**

The bench's corpus walk skips symlinks, so these are hard links.

```bash
cd /workspace && python3 - <<'EOF'
import json, os, pathlib, random
corpus = pathlib.Path("bench/corpus")
rows = [r for r in map(json.loads, open("bench/results/slice53/results.jsonl")) if "path" in r]
arith = {"QF_LIA", "QF_LRA", "QF_UFLIA", "QF_UFLRA"}
refused = sorted(r["path"] for r in rows if r["verdict"] == "unknown:theory-refused")
others = sorted(r["path"] for r in rows if r["logic"] in arith and r["verdict"] != "unknown:theory-refused")
slia = sorted(str(p.relative_to(corpus)) for p in (corpus / "QF_SLIA").rglob("*.smt2"))
rng = random.Random(63)
arith_sample = sorted(rng.sample(others, 2000))
slia_sample = sorted(rng.sample(slia, 2000))
def link(paths, out):
    out = pathlib.Path(out)
    for rel in paths:
        dst = out / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        if not dst.exists():
            os.link(corpus / rel, dst)
    pathlib.Path(str(out) + ".txt").write_text("\n".join(paths) + "\n")
    print(out, len(paths))
link(refused, "target/slice63-refused-corpus")
link(arith_sample, "target/slice63-arith-sample-corpus")
link(slia_sample, "target/slice63-slia-sample-corpus")
import collections
print(collections.Counter(p.split("/")[0] for p in refused))
EOF
ls target/slice59-sample-corpus | head
```

Expected: 4,874 / 2,000 / 2,000 files. Refused by logic: `QF_LIA 4764, QF_LRA 58, QF_SLIA 35, QF_UFLIA 17`. `target/slice59-sample-corpus` exists. If it doesn't, re-create it with Task 0 Step 4 of `docs/superpowers/plans/2026-10-06-shinri-slice62-length-consistent-seeds.md`, which is the verbatim recipe.

- [ ] **Step 5: Launch the four base runs, detached**

```bash
cd /workspace && B=/workspace/target/slice63-base && uptime | tee $B/uptime-start.txt
setsid nohup sh -c "
  taskset -c 12-23 $B/shinri-bench run --logics QF_LIA,QF_LRA,QF_SLIA,QF_UFLIA \
    --corpus /workspace/target/slice63-refused-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $B/shinri --run-id slice63-base-refused > $B/run-refused.log 2>&1;
  taskset -c 12-23 $B/shinri-bench run --logics QF_LIA,QF_LRA,QF_UFLIA,QF_UFLRA \
    --corpus /workspace/target/slice63-arith-sample-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $B/shinri --run-id slice63-base-arith > $B/run-arith.log 2>&1;
  taskset -c 12-23 $B/shinri-bench run --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
    --corpus /workspace/target/slice59-sample-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $B/shinri --run-id slice63-base-sample > $B/run-sample.log 2>&1;
  taskset -c 12-23 $B/shinri-bench run --logics QF_SLIA \
    --corpus /workspace/target/slice63-slia-sample-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $B/shinri --run-id slice63-base-slia > $B/run-slia.log 2>&1;
  date -u +%FT%TZ > $B/finished.txt" > /dev/null 2>&1 &
```

Expected: the refused set finishes in minutes, since every row is refused instantly. The three samples take about 20–40 min each. Don't wait for them: continue with Task 1. Task 5 checks `$B/finished.txt`.

---

### Task 1: Shared constant helper and the three linearity sites

**Files:**
- Modify: `crates/shinri-core/src/context.rs:1018-1041` (+ test after `const_real_value_rejects_symbolic`, ~line 2027)
- Modify: `crates/shinri-theory/src/atom.rs:222-240` (+ tests in `mod tests`)
- Modify: `crates/shinri-arith/src/lib.rs:211-237` (+ `mod` declaration after the `use` block, ~line 30)
- Modify: `crates/shinri-arith/src/normalize.rs:141-163` (+ test in `mod tests`)
- Create: `crates/shinri-arith/src/linearity_lockstep_tests.rs`

**Interfaces:**
- Consumes: nothing new.
- Produces: `pub fn Context::const_arith_value(&self, t: TermId) -> Option<Rational>` (Task 2, Task 3 rely on it); `const_real_value` unchanged signature; the test module `linearity_lockstep_tests` (Task 2 appends to it).

- [ ] **Step 1: Write the failing core test**

Append inside `mod tests` of `crates/shinri-core/src/context.rs`, right after `const_real_value_rejects_symbolic`:

```rust
    #[test]
    fn const_arith_value_folds_int_and_double_neg() {
        use shinri_num::Rational;
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let seven = ctx.mk_numeral(Rational::from_int(7i128.into()), int);
        let neg = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[seven]).unwrap();
        let negneg = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[neg]).unwrap();
        assert_eq!(
            ctx.const_arith_value(seven),
            Some(Rational::from_int(7i128.into()))
        );
        assert_eq!(
            ctx.const_arith_value(neg),
            Some(Rational::from_int((-7i128).into()))
        );
        assert_eq!(
            ctx.const_arith_value(negneg),
            Some(Rational::from_int(7i128.into()))
        );
    }
```

- [ ] **Step 2: Write the failing theory tests**

Append inside `mod tests` of `crates/shinri-theory/src/atom.rs` (it already has `real_var` and `uconst` helpers):

```rust
    /// Slice 63: `(- k)` is a constant factor in either position, Int and
    /// Real, including `(- (- k))`.
    #[test]
    fn negated_numeral_coefficient_is_linear() {
        let mut ctx = Context::new();
        let sorts = [ctx.int_sort(), ctx.real_sort()];
        for (i, sort) in sorts.into_iter().enumerate() {
            let x = uconst(&mut ctx, &format!("x{i}"), sort);
            let four = ctx.mk_numeral(shinri_core::Rational::from_int(4i128.into()), sort);
            let three = ctx.mk_numeral(shinri_core::Rational::from_int(3i128.into()), sort);
            let neg4 = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[four]).unwrap();
            let negneg4 = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[neg4]).unwrap();
            for prod in [[neg4, x], [x, neg4], [negneg4, x]] {
                let m = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &prod).unwrap();
                let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[m, three]).unwrap();
                assert_eq!(classify(&ctx, le), Ok(Owner::Arith), "{prod:?}");
            }
        }
    }

    /// Slice 63 boundary: a negated *variable* is not a constant factor.
    #[test]
    fn negated_variable_times_variable_stays_refused() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), real);
        let negx = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[x]).unwrap();
        let m = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[negx, y]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[m, zero]).unwrap();
        assert_eq!(classify(&ctx, le), Err(Unsupported(le)));
    }
```

- [ ] **Step 3: Write the failing arith tests**

Append inside `mod tests` of `crates/shinri-arith/src/normalize.rs` (it has `real_var` and `num`):

```rust
    /// Slice 63: `(- k)` factors fold into the coefficient, with their sign.
    #[test]
    fn linearize_folds_negated_numeral_coefficients() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let two = num(&mut ctx, 2);
        let three = num(&mut ctx, 3);
        let four = num(&mut ctx, 4);
        let five = num(&mut ctx, 5);
        let neg = |ctx: &mut Context, t: TermId| ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[t]).unwrap();
        let mul = |ctx: &mut Context, a: &[TermId]| ctx.mk_app(Op::Builtin(BuiltinOp::Mul), a).unwrap();
        let n3 = neg(&mut ctx, three);
        let n4 = neg(&mut ctx, four);
        let n5 = neg(&mut ctx, five);
        let mut vs = VarStore::default();
        let xv = vs.problem_var(x);
        let q = |n: i128| Rational::from_int(n.into());

        let t = mul(&mut ctx, &[n4, x]);
        assert_eq!(linearize(&ctx, &mut vs, t), (vec![(xv, q(-4))], q(0)));
        let t = mul(&mut ctx, &[x, n4, two]);
        assert_eq!(linearize(&ctx, &mut vs, t), (vec![(xv, q(-8))], q(0)));
        let t = mul(&mut ctx, &[n3, n5]);
        assert_eq!(linearize(&ctx, &mut vs, t), (vec![], q(15)));
    }
```

Create `crates/shinri-arith/src/linearity_lockstep_tests.rs`:

```rust
//! Slice 63: the three "is this factor a constant" sites — classify's
//! `contains_nonlinear_mul` (shinri-theory), `is_linear_arith` and
//! `normalize::linearize` — must agree. All three use
//! `Context::const_arith_value`.

use super::is_linear_arith;
use shinri_core::{BuiltinOp, Context, Op, TermId};
use shinri_num::Rational;

fn int_var(ctx: &mut Context, name: &str) -> TermId {
    let int = ctx.int_sort();
    let sym = ctx.declare_fun(name, &[], int);
    ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
}

fn int(ctx: &mut Context, k: i64) -> TermId {
    let int = ctx.int_sort();
    ctx.mk_numeral(Rational::from_int((k as i128).into()), int)
}

fn app(ctx: &mut Context, op: BuiltinOp, args: &[TermId]) -> TermId {
    ctx.mk_app(Op::Builtin(op), args).unwrap()
}

#[test]
fn is_linear_arith_accepts_negated_numeral_factors() {
    let mut ctx = Context::new();
    let x = int_var(&mut ctx, "x");
    let y = int_var(&mut ctx, "y");
    let four = int(&mut ctx, 4);
    let n4 = app(&mut ctx, BuiltinOp::Neg, &[four]);
    let left = app(&mut ctx, BuiltinOp::Mul, &[n4, x]);
    let right = app(&mut ctx, BuiltinOp::Mul, &[x, n4]);
    assert!(is_linear_arith(&ctx, left));
    assert!(is_linear_arith(&ctx, right));
    let nx = app(&mut ctx, BuiltinOp::Neg, &[x]);
    let nonlinear = app(&mut ctx, BuiltinOp::Mul, &[nx, y]);
    assert!(!is_linear_arith(&ctx, nonlinear));
}
```

Register it in `crates/shinri-arith/src/lib.rs`, directly after the last top-level `use` line (`use shinri_theory::{Effort, Explainer, …};`, ~line 29):

```rust
#[cfg(test)]
mod linearity_lockstep_tests;
```

- [ ] **Step 4: Run the new tests and verify they fail**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 cargo nextest run -p shinri-core -p shinri-theory -p shinri-arith \
  -E 'test(const_arith_value_folds_int_and_double_neg) | test(negated_numeral_coefficient_is_linear) | test(negated_variable_times_variable_stays_refused) | test(linearize_folds_negated_numeral_coefficients) | test(is_linear_arith_accepts_negated_numeral_factors)'
```

Expected: shinri-core fails to compile (`no method named const_arith_value`). Run once more without `-p shinri-core` to see the others. `negated_numeral_coefficient_is_linear` FAILS (`Err(Unsupported(..))`). `linearize_folds_negated_numeral_coefficients` FAILS (panic `nonlinear reached normalize`). `is_linear_arith_accepts_negated_numeral_factors` FAILS on its first assert. `negated_variable_times_variable_stays_refused` PASSES; it is the boundary guard.

- [ ] **Step 5: Implement `const_arith_value`**

In `crates/shinri-core/src/context.rs` replace the whole `const_real_value` item (doc comment and body, lines ~1018–1041) with:

```rust
    /// The exact `Rational` of a **constant** arithmetic term, Int or Real — a
    /// numeral (literals and parser-folded `(/ lit lit)` both intern as
    /// numerals) or a unary `(- c)` of a constant — or `None` if `t` is
    /// symbolic (a variable, `(* recip x)`, nested arithmetic).
    ///
    /// SHARED admit set, a soundness invariant: every consumer must agree on
    /// what a constant is. Consumers: the FP `to_fp` fence (shinri-solver
    /// `fp_stage.rs`, via [`Context::const_real_value`]); classify's
    /// `contains_nonlinear_mul` (shinri-theory `atom.rs`); `is_linear_arith`
    /// and `normalize::linearize` (shinri-arith) — slice 63.
    pub fn const_arith_value(&self, t: TermId) -> Option<Rational> {
        if let Some(r) = self.numeral_value(t) {
            return Some(r.clone());
        }
        if let TermNode::App {
            op: Op::Builtin(BuiltinOp::Neg),
            args,
            ..
        } = self.term_node(t)
        {
            let kids = self.children(*args);
            if kids.len() == 1 {
                let inner = self.const_arith_value(kids[0])?;
                return Some(Rational::new(Integer::from(-1i64), Integer::one()) * inner);
            }
        }
        None
    }

    /// Alias of [`Context::const_arith_value`], kept for the FP fence's callers.
    #[inline]
    pub fn const_real_value(&self, t: TermId) -> Option<Rational> {
        self.const_arith_value(t)
    }
```

- [ ] **Step 6: Implement the theory site**

In `crates/shinri-theory/src/atom.rs` replace the doc line above `contains_nonlinear_mul` and its `filter` (lines ~222–232) so the function reads:

```rust
/// True if `t` contains a `Mul` with two or more non-constant factors. A
/// factor is constant iff `Context::const_arith_value` folds it (a numeral or
/// `(- c)`); this must agree with `is_linear_arith` and `linearize` in
/// shinri-arith (slice 63).
fn contains_nonlinear_mul(terms: &Context, t: TermId) -> bool {
    match terms.term_node(t) {
        TermNode::Const { .. } => false,
        TermNode::App { op, args, .. } => {
            let children = terms.children(*args);
            if let Op::Builtin(BuiltinOp::Mul) = op {
                let non_const = children
                    .iter()
                    .filter(|&&c| terms.const_arith_value(c).is_none())
                    .count();
                if non_const >= 2 {
                    return true;
                }
            }
            children.iter().any(|&c| contains_nonlinear_mul(terms, c))
        }
    }
}
```

- [ ] **Step 7: Implement the two arith sites**

In `crates/shinri-arith/src/lib.rs`, `is_linear_arith` (~211–237): change the first line of the doc comment's description and the two `numeral_value` uses, so it reads:

```rust
/// Slice 50: `t` is linear all the way down: every `*` has at most one
/// non-constant factor, which is itself linear. A factor is constant iff
/// `Context::const_arith_value` folds it (slice 63; must agree with
/// classify's `contains_nonlinear_mul`). This is exactly the input
/// `normalize::linearize` accepts without its "nonlinear reached normalize"
/// debug assertion. Opaque leaves are linear.
fn is_linear_arith(ctx: &Context, t: TermId) -> bool {
    use shinri_core::TermNode;
    if ctx.const_arith_value(t).is_some() {
        return true;
    }
    match ctx.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Add | BuiltinOp::Sub | BuiltinOp::Neg),
            args,
            ..
        } => ctx.children(*args).iter().all(|&k| is_linear_arith(ctx, k)),
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Mul),
            args,
            ..
        } => {
            let mut nonconst = ctx
                .children(*args)
                .iter()
                .copied()
                .filter(|&k| ctx.const_arith_value(k).is_none());
            match (nonconst.next(), nonconst.next()) {
                (None, _) => true,
                (Some(k), None) => is_linear_arith(ctx, k),
                (Some(_), Some(_)) => false,
            }
        }
        _ => true,
    }
}
```

Do **not** touch `is_compound_arith` (line 193) or `ensure_shared_var`'s `numeral_value` (line 725). See Global Constraints.

In `crates/shinri-arith/src/normalize.rs`, the `Mul` arm (~141–163) becomes:

```rust
                Op::Builtin(BuiltinOp::Mul) => {
                    // Linear: exactly one non-constant factor (classify rejected
                    // the rest). Constant factors — numerals and `(- c)` — fold
                    // via `const_arith_value` (slice 63).
                    let mut coeff = Rational::one();
                    let mut nonconst: Option<TermId> = None;
                    for k in &kids {
                        match terms.const_arith_value(*k) {
                            Some(r) => coeff = coeff * r,
                            None => {
                                debug_assert!(nonconst.is_none(), "nonlinear reached normalize");
                                nonconst = Some(*k);
                            }
                        }
                    }
                    match nonconst {
                        None => (Vec::new(), coeff), // all-constant product
                        Some(inner) => {
                            let (v, c) = linearize(terms, vars, inner);
                            (
                                v.into_iter().map(|(x, q)| (x, q * coeff.clone())).collect(),
                                c * coeff,
                            )
                        }
                    }
                }
```

- [ ] **Step 8: Run the new tests and the three crates' suites**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 cargo nextest run -p shinri-core -p shinri-theory -p shinri-arith -p shinri-fp
```

Expected: all pass, including the five new tests and the existing `const_real_value_*` tests, which now go through the alias. If an existing test fails, stop and report.

- [ ] **Step 9: Format, lint, commit**

```bash
cd /workspace/.claude/worktrees/slice63
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-core/src/context.rs crates/shinri-theory/src/atom.rs crates/shinri-arith/src/lib.rs crates/shinri-arith/src/normalize.rs crates/shinri-arith/src/linearity_lockstep_tests.rs
git commit -m "feat(arith): slice63 - (- k) is a constant factor in classify, is_linear_arith and linearize"
```

---

### Task 2: Three-site lockstep property test

**Files:**
- Modify: `crates/shinri-arith/src/linearity_lockstep_tests.rs` (append)

**Interfaces:**
- Consumes: `Context::const_arith_value` (Task 1); `shinri_theory::atom::classify(&Context, TermId) -> Result<Owner, Unsupported>`; `crate::normalize::linearize(&Context, &mut VarStore, TermId) -> (Vec<(ArithVar, Rational)>, Rational)` (`pub(crate)`); `crate::vars::VarStore::problem_var(&mut self, TermId) -> ArithVar`; `super::is_linear_arith`.
- Produces: the proptest `classify_is_linear_and_linearize_agree`.

- [ ] **Step 1: Write the property test**

Append to `crates/shinri-arith/src/linearity_lockstep_tests.rs`:

```rust
use crate::normalize::linearize;
use crate::vars::VarStore;
use proptest::prelude::*;
use shinri_theory::atom::classify;
use shinri_theory::types::Owner;

/// A generated Int arith term over x, y, z. `NegNum(k)` is the slice-63
/// shape `(- k)`; `Num` may be negative (an interned negative numeral).
#[derive(Clone, Debug)]
enum E {
    Var(usize),
    Num(i64),
    NegNum(i64),
    Neg(Box<E>),
    Add(Vec<E>),
    Sub(Box<E>, Box<E>),
    Mul(Vec<E>),
}

fn expr() -> impl Strategy<Value = E> {
    let leaf = prop_oneof![
        (0usize..3).prop_map(E::Var),
        (-5i64..=5).prop_map(E::Num),
        (0i64..=5).prop_map(E::NegNum),
    ];
    leaf.prop_recursive(4, 24, 3, |inner| {
        prop_oneof![
            inner.clone().prop_map(|e| E::Neg(Box::new(e))),
            prop::collection::vec(inner.clone(), 2..=3).prop_map(E::Add),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| E::Sub(Box::new(a), Box::new(b))),
            prop::collection::vec(inner, 2..=3).prop_map(E::Mul),
        ]
    })
}

fn build(ctx: &mut Context, vars: &[TermId; 3], e: &E) -> TermId {
    match e {
        E::Var(i) => vars[*i],
        E::Num(k) => int(ctx, *k),
        E::NegNum(k) => {
            let n = int(ctx, *k);
            app(ctx, BuiltinOp::Neg, &[n])
        }
        E::Neg(a) => {
            let a = build(ctx, vars, a);
            app(ctx, BuiltinOp::Neg, &[a])
        }
        E::Add(xs) => {
            let xs: Vec<TermId> = xs.iter().map(|x| build(ctx, vars, x)).collect();
            app(ctx, BuiltinOp::Add, &xs)
        }
        E::Sub(a, b) => {
            let a = build(ctx, vars, a);
            let b = build(ctx, vars, b);
            app(ctx, BuiltinOp::Sub, &[a, b])
        }
        E::Mul(xs) => {
            let xs: Vec<TermId> = xs.iter().map(|x| build(ctx, vars, x)).collect();
            app(ctx, BuiltinOp::Mul, &xs)
        }
    }
}

fn q(n: i64) -> Rational {
    Rational::from_int((n as i128).into())
}

fn eval(e: &E, asg: &[i64; 3]) -> Rational {
    match e {
        E::Var(i) => q(asg[*i]),
        E::Num(k) => q(*k),
        E::NegNum(k) => -q(*k),
        E::Neg(a) => -eval(a, asg),
        E::Add(xs) => xs.iter().fold(q(0), |acc, x| acc + eval(x, asg)),
        E::Sub(a, b) => eval(a, asg) - eval(b, asg),
        E::Mul(xs) => xs.iter().fold(q(1), |acc, x| acc * eval(x, asg)),
    }
}

proptest! {
    /// classify accepts `(<= t 0)` ⇔ `is_linear_arith(t)`; when accepted,
    /// `linearize(t)` does not trip its debug assertion and its linear form
    /// evaluates equal to `t`.
    #[test]
    fn classify_is_linear_and_linearize_agree(
        e in expr(),
        asg in [-4i64..=4, -4i64..=4, -4i64..=4],
    ) {
        let mut ctx = Context::new();
        let vars = [
            int_var(&mut ctx, "x"),
            int_var(&mut ctx, "y"),
            int_var(&mut ctx, "z"),
        ];
        let t = build(&mut ctx, &vars, &e);
        let zero = int(&mut ctx, 0);
        let atom = app(&mut ctx, BuiltinOp::Le, &[t, zero]);
        let accepted = classify(&ctx, atom).is_ok();
        prop_assert_eq!(accepted, is_linear_arith(&ctx, t), "term {:?}", e);
        if accepted {
            prop_assert_eq!(classify(&ctx, atom), Ok(Owner::Arith));
            let mut vs = VarStore::default();
            let pv: Vec<_> = vars.iter().map(|&x| vs.problem_var(x)).collect();
            let (lin, c) = linearize(&ctx, &mut vs, t);
            let mut val = c;
            for (v, coef) in lin {
                let i = pv.iter().position(|p| *p == v).expect("leaf is x, y or z");
                val = val + coef * q(asg[i]);
            }
            prop_assert_eq!(val, eval(&e, &asg), "term {:?}", e);
        }
    }
}
```

- [ ] **Step 2: Run it**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 cargo nextest run -p shinri-arith -E 'test(classify_is_linear_and_linearize_agree)'
```

Expected: 1 test, PASS, well under 5 s. A failure is a real disagreement between the sites. Read the shrunk case, fix the site that disagrees with `const_arith_value`, then re-run. Don't weaken the property.

- [ ] **Step 3: Check that the property can fail (mutation check, not committed)**

Temporarily change `filter(|&&c| terms.const_arith_value(c).is_none())` in `crates/shinri-theory/src/atom.rs` back to `filter(|&&c| !matches!(terms.term_node(c), TermNode::Const { .. }))`, then re-run Step 2's command.

Expected: FAIL with a shrunk case containing `NegNum`. Revert with `git checkout crates/shinri-theory/src/atom.rs` and re-run Step 2: PASS.

- [ ] **Step 4: Format, lint, commit**

```bash
cd /workspace/.claude/worktrees/slice63
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-arith/src/linearity_lockstep_tests.rs
git commit -m "test(arith): slice63 - classify/is_linear_arith/linearize lockstep property"
```

---

### Task 3: Script-level e2e tests

**Files:**
- Modify: `crates/shinri-solver/tests/lia_e2e.rs` (append)
- Modify: `crates/shinri-solver/tests/oracle.rs:719-724` (doc comment only)

**Interfaces:**
- Consumes: `shinri_parser::Parser::new(&str)`, `Parser::next_command(&mut Context) -> Option<Result<Command, _>>`, `Solver::ctx_mut()`, `Solver::execute(Command) -> CommandResponse` (as in `tests/nary_arith_oracle.rs`).
- Produces: six `slice63_*` tests.

- [ ] **Step 1: Write the tests**

Append to `crates/shinri-solver/tests/lia_e2e.rs`:

```rust
/// Run an SMT-LIB script; the outcome of its last `check-sat`.
fn script_outcome(src: &str) -> SolveOutcome {
    use shinri_parser::Parser;
    use shinri_solver::CommandResponse;
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = None;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = Some(SolveOutcome::Sat),
            CommandResponse::Unsat => outcome = Some(SolveOutcome::Unsat),
            CommandResponse::Unknown => outcome = Some(SolveOutcome::Unknown),
            _ => {}
        }
    }
    outcome.expect("script has a check-sat")
}

/// Slice 63 spec §1 reproducer, pinned to x = 0: −4x ≤ 3 ⇒ x ≥ 0 over Int.
#[test]
fn slice63_neg_coeff_left_sat() {
    let src = "(set-logic QF_LIA)(declare-fun x () Int)\
               (assert (<= (* (- 4) x) 3))(assert (<= x 0))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Sat);
}

/// Sign check: −4x ≤ 3 ∧ x ≤ −1 is unsat (a dropped sign gives 4x ≤ 3, sat).
#[test]
fn slice63_neg_coeff_left_sign_unsat() {
    let src = "(set-logic QF_LIA)(declare-fun x () Int)\
               (assert (<= (* (- 4) x) 3))(assert (<= x (- 1)))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Unsat);
}

/// Mirrored position: x·(−2) ≥ 1 ∧ x ≥ 0 is unsat.
#[test]
fn slice63_neg_coeff_right_unsat() {
    let src = "(set-logic QF_LIA)(declare-fun x () Int)\
               (assert (>= (* x (- 2)) 1))(assert (>= x 0))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Unsat);
}

/// Real decimal coefficient, mirrored: −2.5r > 5 ⇒ r < −2.
#[test]
fn slice63_real_neg_decimal_coeff() {
    let unsat = "(set-logic QF_LRA)(declare-fun r () Real)\
                 (assert (> (* r (- 2.5)) 5.0))(assert (> r (- 2.0)))(check-sat)";
    assert_eq!(script_outcome(unsat), SolveOutcome::Unsat);
    let sat = "(set-logic QF_LRA)(declare-fun r () Real)\
               (assert (> (* r (- 2.5)) 5.0))(check-sat)";
    assert_eq!(script_outcome(sat), SolveOutcome::Sat);
}

/// Guard (Global Constraints): a shared `(- 4)` under a UF stays pinned to −4.
#[test]
fn slice63_shared_neg_numeral_stays_pinned() {
    let src = "(set-logic QF_UFLIA)(declare-fun f (Int) Int)(declare-fun y () Int)\
               (assert (= y (- 4)))(assert (= (f y) 0))(assert (= (f (- 4)) 1))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Unsat);
}

/// A shared compound with a `(- 1)` coefficient is linear and pinned
/// (slice 50's `define_shared_compound`): (* (- 1) y) = 4 when y = −4.
#[test]
fn slice63_shared_neg_coeff_compound_is_pinned() {
    let src = "(set-logic QF_UFLIA)(declare-fun f (Int) Int)(declare-fun y () Int)\
               (assert (= y (- 4)))(assert (= (f 4) 0))(assert (= (f (* (- 1) y)) 1))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Unsat);
}
```

- [ ] **Step 2: Run them**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(lia_e2e) & test(slice63_)'
```

Expected: 6 tests run, all PASS. If the count is 0, the filter is wrong; fix it, because a 0-test run reads as green. If any test returns `Unknown`, stop and report the script: a fence other than `theory-refused` is involved and the spec's scope ruling applies.

- [ ] **Step 3a: Red check against the base binary**

The test bodies are scripts, so they can be checked against Task 0's base binary directly:

```bash
S=$(mktemp -d)
printf '(set-logic QF_LIA)(declare-fun x () Int)(assert (<= (* (- 4) x) 3))(assert (<= x (- 1)))(check-sat)\n' > $S/sign.smt2
printf '(set-logic QF_UFLIA)(declare-fun f (Int) Int)(declare-fun y () Int)(assert (= y (- 4)))(assert (= (f 4) 0))(assert (= (f (* (- 1) y)) 1))(check-sat)\n' > $S/compound.smt2
printf '(set-logic QF_UFLIA)(declare-fun f (Int) Int)(declare-fun y () Int)(assert (= y (- 4)))(assert (= (f y) 0))(assert (= (f (- 4)) 1))(check-sat)\n' > $S/guard.smt2
for f in $S/*.smt2; do printf '%s\t' $(basename $f); /workspace/target/slice63-base/shinri $f | tail -1; done
rm -r $S
```

Expected on the base binary: `compound` → `unknown`, `guard` → `unsat` (a guard passes before and after), `sign` → `unknown`. Record the output in the commit message body.

- [ ] **Step 3: Update the stale oracle doc comment**

In `crates/shinri-solver/tests/oracle.rs`, replace the four doc lines (from "Negative coefficients are rendered as" through "nonlinear-multiplication guard.") above `fn smt2_real_coeff_times_var` with:

```rust
/// Negative coefficients are rendered as `(- (* |c|.0 var))`. Before slice 63
/// the solver refused `(* (- |c|.0) var)` as nonlinear; the rendering is kept
/// so this oracle's generated corpus is unchanged. `neg_coeff_oracle.rs`
/// covers the `(* (- k) var)` shape.
```

The function body is not edited.

- [ ] **Step 4: Format, lint, commit**

```bash
cd /workspace/.claude/worktrees/slice63
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-solver/tests/lia_e2e.rs crates/shinri-solver/tests/oracle.rs
git commit -m "test(solver): slice63 - e2e for (- k) coefficients and shared-term pins"
```

---

### Task 4: z3 differential oracle

**Files:**
- Create: `crates/shinri-solver/tests/neg_coeff_oracle.rs`

**Interfaces:**
- Consumes: `shinri_parser::Parser`, `shinri_solver::{CommandResponse, SolveOutcome, Solver}`, `easy_smt` (existing dev-dependency), `oracle` feature.
- Produces: the test `differential_qf_lia_neg_coeff`.

- [ ] **Step 1: Write the oracle**

Create `crates/shinri-solver/tests/neg_coeff_oracle.rs`:

```rust
//! Differential oracle: shinri vs z3 on QF_LIA scripts whose products carry a
//! unary-minus constant coefficient, `(* (- k) v)` / `(* v (- k))` /
//! `(* (- (- k)) v)` (slice 63). Requires z3 on PATH.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(neg_coeff_oracle)'
//!
//! Variables are bounded to [-3, 3], so every script is small and decidable:
//! `Unknown` is not tolerated.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand
/// (same convention as tests/nary_arith_oracle.rs).
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
const VARS: &[&str] = &["a", "b", "c"];

fn shinri_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

fn z3_outcome_lia(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_LIA").expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-const ") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

/// SMT-LIB integer literal; negatives use the `(- k)` form.
fn int_lit(k: i64) -> String {
    if k < 0 {
        format!("(- {})", -k)
    } else {
        format!("{k}")
    }
}

/// `k·v` for k in -4..=4 \ {0}, in a slice-63 shape: the coefficient on
/// either side; one time in four the literal is `(- <literal of -k>)`,
/// which gives a double negation `(- (- k))` for positive k.
fn gen_product(rng: &mut Lcg) -> String {
    let v = VARS[rng.below(VARS.len() as u64) as usize];
    let mut k = rng.below(8) as i64 - 4;
    if k >= 0 {
        k += 1;
    }
    let lit = if rng.below(4) == 0 {
        format!("(- {})", int_lit(-k))
    } else {
        int_lit(k)
    };
    if rng.below(2) == 0 {
        format!("(* {lit} {v})")
    } else {
        format!("(* {v} {lit})")
    }
}

/// A linear sum of 1..=3 products, sometimes as a binary `-`.
fn gen_lhs(rng: &mut Lcg) -> String {
    match rng.below(4) {
        0 => format!("(- {} {})", gen_product(rng), gen_product(rng)),
        _ => {
            let n = 1 + rng.below(3) as usize;
            let ps: Vec<String> = (0..n).map(|_| gen_product(rng)).collect();
            if n == 1 {
                ps[0].clone()
            } else {
                format!("(+ {})", ps.join(" "))
            }
        }
    }
}

fn gen_atom(rng: &mut Lcg) -> String {
    let op = ["<=", ">=", "=", "<"][rng.below(4) as usize];
    let rhs = int_lit(rng.below(11) as i64 - 5);
    format!("({op} {} {rhs})", gen_lhs(rng))
}

fn gen_script(rng: &mut Lcg) -> String {
    let mut s = String::from("(set-logic QF_LIA)\n");
    for v in VARS {
        s.push_str(&format!("(declare-const {v} Int)\n"));
    }
    for v in VARS {
        s.push_str(&format!("(assert (and (<= (- 3) {v}) (<= {v} 3)))\n"));
    }
    for _ in 0..2 + rng.below(4) {
        let a = match rng.below(4) {
            0 => format!("(not {})", gen_atom(rng)),
            1 => format!("(or {} {})", gen_atom(rng), gen_atom(rng)),
            _ => gen_atom(rng),
        };
        s.push_str(&format!("(assert {a})\n"));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_lia_neg_coeff() {
    let mut rng = Lcg(0x51CE_0063);
    let (mut n_sat, mut n_unsat, mut n_z3_checked) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng);
        let ours = shinri_outcome(&src);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {
                panic!("unknown on a bounded QF_LIA script (iter {iter}):\n{src}")
            }
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        match (ours, z3_outcome_lia(&mut ctx, &src)) {
            (SolveOutcome::Sat, easy_smt::Response::Sat)
            | (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (_, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_LIA (- k) coefficient DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_lia_neg_coeff: sat={n_sat} unsat={n_unsat} z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat)"
    );
    assert!(
        n_z3_checked >= N_ITERS * 9 / 10,
        "z3 must confirm at least 90% of iterations ({n_z3_checked}/{N_ITERS})"
    );
}
```

- [ ] **Step 2: Run it**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle -E 'binary(neg_coeff_oracle)' --no-capture
```

Expected: `Starting 1 test`, PASS, and a printed line with both `sat` and `unsat` non-zero. If it panics on `unknown`, stop and report the script. If it reports a disagreement, that is a soundness bug in Task 1: fix it there, never in the generator.

- [ ] **Step 3: Format, lint, commit**

```bash
cd /workspace/.claude/worktrees/slice63
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-solver/tests/neg_coeff_oracle.rs
git commit -m "test(solver): slice63 - z3 differential oracle for (- k) coefficients"
```

---

### Task 5: Gates, after runs, report, PR

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice63-lia-coefficients-report.md` (date = the day the after runs finish)
- Modify: `docs/superpowers/specs/2026-10-07-shinri-slice63-lia-const-coefficients-design.md` (append `## 11. Measured outcomes`; fill §9 by pointing to the report's queue)

**Interfaces:**
- Consumes: branch HEAD after Tasks 1–4; Task 0's base binaries, corpora, `oracle-count.txt` and base runs.
- Produces: the report and spec section cited by the PR.

- [ ] **Step 1: Gates (criterion 5)**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 mise run ci 2>&1 | tee /workspace/target/slice63-ci.log | tail -5
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee /workspace/target/slice63-oracle.log | grep -E 'Starting|Summary'
cat /workspace/target/slice63-base/oracle-count.txt
```

Expected: `ci` is green. The oracle run's `Starting N tests` count is the base count + 1, and all pass. Record both lines in `/workspace/target/slice63-gates.txt`. The known pre-existing `clippy --features oracle` item (slice-54 carry) isn't a gate here.

- [ ] **Step 2: Confirm the base runs finished**

```bash
cat /workspace/target/slice63-base/finished.txt
wc -l /workspace/bench/results/slice63-base-{refused,arith,sample,slia}/results.jsonl
```

Expected: a timestamp, and 4,875 / 2,001 / 2,001 / 2,001 lines (rows + the fixture line). If `finished.txt` is missing, wait with a Monitor until-loop on that file; don't use a foreground sleep.

- [ ] **Step 3: Build and launch the after runs, detached**

```bash
cd /workspace/.claude/worktrees/slice63
taskset -c 0-11 cargo build --release -p shinri-cli -p shinri-bench
A=/workspace/target/slice63-after && mkdir -p $A
cp target/release/shinri target/release/shinri-bench $A/
md5sum $A/shinri | tee $A/md5.txt; git rev-parse --short HEAD | tee $A/commit.txt
$A/shinri --stats /workspace/target/slice63-base/repro.smt2
uptime | tee $A/uptime-start.txt
setsid nohup sh -c "
  taskset -c 12-23 $A/shinri-bench run --logics QF_LIA,QF_LRA,QF_SLIA,QF_UFLIA \
    --corpus /workspace/target/slice63-refused-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $A/shinri --run-id slice63-refused > $A/run-refused.log 2>&1;
  taskset -c 12-23 $A/shinri-bench run --logics QF_LIA,QF_LRA,QF_UFLIA,QF_UFLRA \
    --corpus /workspace/target/slice63-arith-sample-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $A/shinri --run-id slice63-arith > $A/run-arith.log 2>&1;
  taskset -c 12-23 $A/shinri-bench run --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
    --corpus /workspace/target/slice59-sample-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $A/shinri --run-id slice63-sample > $A/run-sample.log 2>&1;
  taskset -c 12-23 $A/shinri-bench run --logics QF_SLIA \
    --corpus /workspace/target/slice63-slia-sample-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $A/shinri --run-id slice63-slia > $A/run-slia.log 2>&1;
  date -u +%FT%TZ > $A/finished.txt" > /dev/null 2>&1 &
```

Expected: the reproducer now prints `outcome=sat` then `sat`. The refused set runs longest. If every row timed out it would take about 9 h at `--jobs 3`; Bromberger's "unbounded directions" rows are designed to stress branch-and-bound, so expect many timeouts. If no other track is benching, `--jobs 6` is allowed; record which was used. Wait for `$A/finished.txt` with a Monitor until-loop.

- [ ] **Step 4: Join base and after (criteria 1, 2, 3, 6)**

```bash
cd /workspace && for id in slice63-base-refused slice63-refused slice63-base-arith slice63-arith slice63-base-sample slice63-sample slice63-base-slia slice63-slia; do
  (cd /workspace/.claude/worktrees/slice63 && cargo run -q --release -p shinri-bench -- report /workspace/bench/results/$id); done
python3 - <<'EOF' | tee /workspace/target/slice63-after/join.txt
import json, collections
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
fam = lambda p: "/".join(p.split("/")[:2])
changed = []
for base, after in (("slice63-base-refused", "slice63-refused"), ("slice63-base-arith", "slice63-arith"),
                    ("slice63-base-sample", "slice63-sample"), ("slice63-base-slia", "slice63-slia")):
    a = load(f"bench/results/{base}/results.jsonl"); b = load(f"bench/results/{after}/results.jsonl")
    assert a.keys() == b.keys(), f"row sets differ: {base} vs {after}"
    c = collections.Counter()
    for p in sorted(a):
        va, vb = a[p]["verdict"], b[p]["verdict"]
        if va != vb:
            c[(a[p]["logic"], va, vb)] += 1
            changed.append((p, a[p]["logic"], va, vb, after))
    print(f"== {base} -> {after}: {sum(c.values())} changed; wrong after: {sum(r['verdict'] == 'wrong' for r in b.values())}")
    for k, n in sorted(c.items()):
        print("  ", *k, n)
b = load("bench/results/slice63-refused/results.jsonl")
dest = collections.Counter(r["verdict"] for r in b.values())
print("criterion 2: still theory-refused:", dest["unknown:theory-refused"], "of", len(b), "-> dropped", len(b) - dest["unknown:theory-refused"])
print("criterion 3 destinations:", dict(dest))
print("destinations by family:")
for (f, v), n in sorted(collections.Counter((fam(p), r["verdict"]) for p, r in b.items()).items()):
    print("  ", f, v, n)
open("/workspace/target/slice63-after/changed.tsv", "w").write("".join("\t".join(x) + "\n" for x in changed))
open("/workspace/target/slice63-after/still-refused.txt", "w").write("".join(p + "\n" for p, r in b.items() if r["verdict"] == "unknown:theory-refused"))
open("/workspace/target/slice63-after/unverified.txt", "w").write("".join(p + "\n" for p, r in b.items() if r["verdict"] == "unverified"))
EOF
```

Expected: `wrong after: 0` on all four lines (criterion 1; any `wrong` stops the slice for a ruling), and `dropped ≥ 4700` (criterion 2). The sample sets change only by timeout-edge rows, which Step 6 checks.

- [ ] **Step 5: Classify still-refused rows and confirm `unverified` (criteria 2, 3)**

```bash
cd /workspace && A=/workspace/target/slice63-after
for p in $(head -50 $A/still-refused.txt); do
  printf '%s\t' $p; grep -oE '\(\* [^ ()]+ [^ ()]+\)|\(\* \([^()]*\) [^ ()]+\)|\(\* [^ ()]+ \([^()]*\)\)' bench/corpus/$p | head -1; done | tee $A/still-refused-shapes.txt
shuf -n 20 --random-source=<(yes) $A/unverified.txt | while read p; do
  printf '%s\tshinri=%s\tz3=%s\tcvc5=%s\n' $p "$(timeout 25 $A/shinri bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$')" \
    "$(mise exec -- z3 -T:120 bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$')" \
    "$(mise exec -- cvc5 --tlimit=120000 bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$')"; done | tee $A/unverified-confirm.txt
```

Expected: every still-refused row gets a stated cause in the report (for example, a genuine nonlinear product). For the ≥ 20 sampled `unverified` rows, z3 or cvc5 agrees with shinri wherever either decides. Any disagreement is a `wrong` and stops the slice for a ruling. If there are fewer than 20 `unverified` rows, check them all.

- [ ] **Step 6: Re-run every `correct → non-correct` row 3× with both binaries (criteria 4, 6)**

```bash
cd /workspace && A=/workspace/target/slice63-after; B=/workspace/target/slice63-base
awk -F'\t' '$3=="correct" && $4!="correct" {print $1}' $A/changed.tsv > $A/losses.txt; wc -l < $A/losses.txt
for p in $(cat $A/losses.txt); do for bin in $B/shinri $A/shinri; do for i in 1 2 3; do
  printf '%s\t%s\t%s\t%s\n' $p $(basename $(dirname $bin)) $i "$(taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$' || echo timeout)"; done; done; done | tee $A/loss-reruns.txt
```

Expected: no row where the base binary answers `correct` 3/3 and the after binary fails to 3/3 (criterion 4). Sample-set changes reproduce as timeout-edge noise (criterion 6). A reproduced loss stops the slice for a ruling.

- [ ] **Step 7: Write the report**

Create `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice63-lia-coefficients-report.md` with these sections, in the style of `docs/superpowers/research/2026-10-07-smtlib-2024-slice62-length-consistent-seeds-report.md`:
- **Headline:** rows moved to `correct`, by logic and family; the drop in `theory-refused`; new `timeout`/`oom` counts by family (reported, not gated); the criteria table 1–6 with PASS/FAIL and evidence.
- **Commands:** the exact commands run (from this plan, with any deviations).
- **Runs:** table of the eight run ids with binary md5, commit, start/finish, rows, `--jobs`, and the load at launch.
- **Verdict changes:** from `join.txt`.
- **Still refused:** every remaining row's cause, from `still-refused-shapes.txt`.
- **Unverified confirmation:** from `unverified-confirm.txt`.
- **What changed versus the spec:** at least the §8 row-set amendment, plus anything else.
- **Gates:** from `slice63-gates.txt`.
- **Queued for the next slice:** ordered. It must include the LIA timeout/OOM population (base plus newly exposed, by family), for the re-baseline track to rank.
- **References.**

- [ ] **Step 8: Spec §11 and commit**

Append to the spec:

```markdown
## 11. Measured outcomes

See `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice63-lia-coefficients-report.md`.
Criteria 1–6: <PASS/FAIL each, one line with the key number>.
```

Then replace §9's body with `See the report, § Queued for the next slice.`

```bash
cd /workspace/.claude/worktrees/slice63
git add docs/superpowers/research/*slice63* docs/superpowers/specs/2026-10-07-shinri-slice63-lia-const-coefficients-design.md
git commit -m "docs(bench+spec): slice63 - report and measured outcomes"
```

- [ ] **Step 9: Push and open the PR; ask before merging**

```bash
cd /workspace/.claude/worktrees/slice63
git push -u origin slice63-lia-const-coefficients
gh pr create --base main --title "slice63: constant coefficients in linear arithmetic" \
  --body "Spec: docs/superpowers/specs/2026-10-07-shinri-slice63-lia-const-coefficients-design.md. Report: docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice63-lia-coefficients-report.md. <headline numbers and criteria table>"
```

Wait for CI to go green, then **ask the user** before merging with a merge commit. After the merge: `git push origin --delete slice63-lia-const-coefficients`, then from `/workspace`: `git worktree remove .claude/worktrees/slice63 && git branch -d slice63-lia-const-coefficients`.
