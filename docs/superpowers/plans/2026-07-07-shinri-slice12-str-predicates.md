# Slice 12 — String Predicates (prefixof / suffixof / contains) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [x]`) syntax for tracking.

**Goal:** Admit `str.prefixof`, `str.suffixof`, `str.contains` with the polarity-aware posture from the approved spec (`docs/superpowers/specs/2026-07-07-shinri-slice12-str-predicates-design.md`): constant-fold literal cases at any polarity, decide positive-only occurrences via existential concat decomposition, fence everything else to sound Unknown.

**Architecture:** Three new `BuiltinOp` variants flow parser → core sort rules → a new `shinri-str::predicates` pre-pass module (fold / polarity fence / positive rewrite) wired into the solver's string-path seam at `crates/shinri-solver/src/lib.rs:402-425`, ahead of the existing substr desugar. No new theory-atom or retraction machinery. New z3 differential oracle family + always-on e2e pins.

**Tech Stack:** Rust workspace (toolchain pinned 1.96.0), z3 on PATH for `oracle`-feature tests only.

> **COMPLETED 2026-07-09 (with a scope divergence).** Tasks 1–9 landed. During the
> oracle/differential phase a container OOM interrupted the session; on recovery, a
> differential fuzzer (added as `tests/qfs_fuzz_corpus.rs`) revealed that the
> predicate rewrite (predicates → word equations) surfaced a **pre-existing
> word-equation resolver unsoundness** (present on `main`, independent of this
> slice). Per user direction this was root-caused and fixed as part of the slice:
> dl0-gated merge-derived length lemmas + a complete 3-valued model gate +
> antecedent-precise citation, verified across 3 adversarial review rounds and ~24k
> differential fuzz iterations (0 wrong verdicts). The OOM cause (uncapped fuzz
> harness) was fixed with an `RLIMIT_AS` self-cap. See the spec Status line and
> `.superpowers/sdd/task-E1-report.md` for the full diagnosis, design, and
> validation. Net acceptance: workspace suite green, full oracle sweep 0
> disagreements, clean-cache clippy 0 warnings.

## Global Constraints

- Every commit message ends with `(slice 12)`.
- SMT-LIB argument order (spec §Goal): `(str.prefixof p s)` / `(str.suffixof p s)` = needle first; `(str.contains s sub)` = **haystack first**.
- Rewrite shapes (spec §2): `prefixof(p,s)` → `(= s (str.++ p k))`; `suffixof(p,s)` → `(= s (str.++ k p))`; `contains(s,sub)` → `(= s (str.++ k1 sub k2))`.
- Polarity classifier fails **sound**: any unrecognized Boolean structure treats children as both-polarity → fence (spec §2).
- Clippy only on a **clean cache** (`cargo clean` first) — warm-cache clippy false-passes in this environment.
- Long gates (workspace test suite, oracle sweeps) are run by the controller in the background — do NOT dispatch cargo-running subagents while a live gate runs (rlib race fakes doctest failures).
- Existing string oracle family `qfs_matches_z3` (seed `0x5_1_1A_0000_0001`) and the fp-bridge str family are NOT modified.
- No `str.indexof` / `str.replace` / regex. No substr-fence changes. `get-value` on a predicate term stays unsupported.

---

### Task 1: Pre-flight canary hunt

**Files:**
- Modify: `docs/superpowers/plans/2026-07-07-shinri-slice12-str-predicates.md` (this file — record findings below)

**Interfaces:**
- Produces: a recorded list of every test/canary that could break when the three ops stop being parse errors. Later tasks consult it before flipping behavior.

- [x] **Step 1: Run the hunt greps**

```bash
grep -rn "prefixof\|suffixof\|str\.contains" /workspace/crates --include="*.rs" | grep -v target
grep -rn "unknown operator" /workspace/crates --include="*.rs" | grep -v target
grep -rn "StrPrefixOf\|StrSuffixOf\|StrContains" /workspace/crates --include="*.rs" | grep -v target
```

Expected (design-time check, re-verify): only `crates/shinri-solver/tests/fp_oracle.rs:1818` (a comment saying the ops are unimplemented — truth-up in Task 9) and the parser's generic `unknown operator` diagnostic at `crates/shinri-parser/src/parser.rs:640` (no test pins these three op names to that error).

- [x] **Step 2: Record findings in this file**

Append under this step a bullet per hit with verdict `SAFE` (comment/unrelated) or `PIN` (test that pins current behavior — must be updated in the task that flips it). If any `PIN` is found, add a note to the affected task before starting it.

- Findings (executed 2026-07-07, worktree @ def9800):
  - `crates/shinri-solver/tests/fp_oracle.rs:1818` — doc comment "prefixof/suffixof/contains are unimplemented and" — **SAFE** (comment only; truth-up scheduled in Task 9 Step 4).
  - `crates/shinri-parser/src/parser.rs:640` — generic `unknown operator {head}` diagnostic — **SAFE** (generic fallback; hunt 1 confirms no test pins these three op names to that error).
  - Hunt 3 (`StrPrefixOf|StrSuffixOf|StrContains`): zero hits — variants do not exist yet, no stale references.
  - **No PIN findings.** No task notes needed; expected failure mode when ops stop being parse errors is confined to the above.

- [x] **Step 3: Commit**

```bash
git add docs/superpowers/plans/2026-07-07-shinri-slice12-str-predicates.md
git commit -m "docs(plan): slice-12 canary hunt findings recorded (slice 12)"
```

---

### Task 2: Core `BuiltinOp` variants + sort rules

**Files:**
- Modify: `crates/shinri-core/src/term.rs:82-86` (String ops block)
- Modify: `crates/shinri-core/src/context.rs:437-495` (String sort rules block)
- Test: inline `#[cfg(test)]` in `crates/shinri-core/src/context.rs` (mirror the string-ops test at `context.rs:1285-1303`)

**Interfaces:**
- Produces: `BuiltinOp::StrPrefixOf`, `BuiltinOp::StrSuffixOf`, `BuiltinOp::StrContains` — arity 2, both args String-sorted, result Bool. All later tasks consume these variant names exactly.

- [x] **Step 1: Write the failing test**

In the `tests` module of `crates/shinri-core/src/context.rs`, next to the existing string-ops sort test:

```rust
#[test]
fn string_predicate_sorts() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let int_s = ctx.int_sort();
    let bool_s = ctx.bool_sort();
    let f = ctx.declare_fun("x", &[], str_s);
    let x = ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap();
    let lit = ctx.mk_string_const("ab");
    for op in [
        BuiltinOp::StrPrefixOf,
        BuiltinOp::StrSuffixOf,
        BuiltinOp::StrContains,
    ] {
        let t = ctx.mk_app(Op::Builtin(op), &[x, lit]).unwrap();
        assert_eq!(ctx.sort_of(t), bool_s, "{op:?} must be Bool-sorted");
        // Arity 2 enforced.
        assert!(ctx.mk_app(Op::Builtin(op), &[x]).is_err());
        // Both args must be String-sorted.
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
        assert!(ctx.mk_app(Op::Builtin(op), &[x, one]).is_err());
    }
}
```

Note: if `Rational`/`mk_numeral` paths differ inside the core crate's own test module (no `shinri_core::` prefix — use `crate::Rational`), match the imports of the neighboring test at `context.rs:1285`.

- [x] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core string_predicate_sorts`
Expected: COMPILE FAIL — `StrPrefixOf` not found in `BuiltinOp`.

- [x] **Step 3: Add the variants**

In `crates/shinri-core/src/term.rs`, extend the String block:

```rust
    // Strings (QF_S core)
    StrConcat,
    StrLen,
    StrAt,
    StrSubstr,
    // String predicates (slice 12): String × String → Bool.
    // Arg order per SMT-LIB: prefixof/suffixof take the NEEDLE first;
    // contains takes the HAYSTACK first.
    StrPrefixOf,
    StrSuffixOf,
    StrContains,
```

In `crates/shinri-core/src/context.rs`, after the `StrSubstr` sort-rule arm (line ~495):

```rust
            StrPrefixOf | StrSuffixOf | StrContains => {
                expect_arity(args, 2)?;
                let str_s = self.string_sort();
                expect_all(self, args, str_s)?;
                Ok(self.bool_sort())
            }
```

- [x] **Step 4: Fix exhaustive-match fallout across the workspace**

Run: `cargo build --workspace`
Every non-exhaustive `match` on `BuiltinOp` will fail to compile — that is the desired discovery mechanism. Known site: `crates/shinri-parser/src/print.rs` `op_name` (handled properly in Task 3; to keep this task compiling, add the three arms there now with their final values — see Task 3 Step 3 for the exact lines). For any other site the compiler surfaces, route the three variants alongside the existing `StrConcat`/`StrLen`/`StrAt`/`StrSubstr` handling of that site and note it in the commit message.

- [x] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-core string_predicate_sorts`
Expected: PASS

- [x] **Step 6: Commit**

```bash
git add -A crates
git commit -m "feat(core): StrPrefixOf/StrSuffixOf/StrContains BuiltinOps — String×String→Bool sort rule (slice 12)"
```

---

### Task 3: Parser + printer support

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs:320-324` (op-name mapping)
- Modify: `crates/shinri-parser/src/print.rs:188-191` (op printing)
- Test: inline `#[cfg(test)]` in `crates/shinri-parser/src/parser.rs` (mirror `parses_strings_str_at` at `parser.rs:1745`)

**Interfaces:**
- Consumes: the three `BuiltinOp` variants from Task 2.
- Produces: `"str.prefixof"`/`"str.suffixof"`/`"str.contains"` parse to those variants and print back to the same names.

- [x] **Step 1: Write the failing tests**

In the parser's test module, following the style of `parses_strings_str_at` (`parser.rs:1745` — reuse its parse helper):

```rust
/// Parse each of the three string predicates and verify op + Bool sort.
#[test]
fn parses_string_predicates() {
    for (src, want) in [
        (r#"(assert (str.prefixof x "a"))"#, BuiltinOp::StrPrefixOf),
        (r#"(assert (str.suffixof x "a"))"#, BuiltinOp::StrSuffixOf),
        (r#"(assert (str.contains x "a"))"#, BuiltinOp::StrContains),
    ] {
        // Build the full script with a String-sorted `x`, parse, and dig out
        // the asserted term — copy the exact scaffolding used by
        // `parses_strings_str_at` (declare-fun x () String + parse loop).
        // Assert: term op == Op::Builtin(want), sort == bool_sort.
        let _ = (src, want); // replace with the real scaffolding
    }
}

/// A predicate with a non-String argument is a sort error, not a parse crash.
#[test]
fn string_predicate_wrong_sort_rejected() {
    // (str.contains x 1) — Int second arg → diagnostic, matching how the
    // existing sort-error tests in this module assert failures.
}
```

Fill both bodies from the neighboring tests' exact scaffolding (the parse helper and diagnostic-assertion patterns already in the module) — the assertions to make are stated in the comments above.

- [x] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-parser parses_string_predicates string_predicate_wrong_sort_rejected`
Expected: FAIL — `unknown operator str.prefixof` diagnostic (the mapping doesn't exist yet).

- [x] **Step 3: Add parser mapping + printer arms**

`crates/shinri-parser/src/parser.rs`, in the op-name match after `"str.substr" => StrSubstr,`:

```rust
            "str.prefixof" => StrPrefixOf,
            "str.suffixof" => StrSuffixOf,
            "str.contains" => StrContains,
```

`crates/shinri-parser/src/print.rs`, after `StrSubstr => "str.substr".to_owned(),`:

```rust
        StrPrefixOf => "str.prefixof".to_owned(),
        StrSuffixOf => "str.suffixof".to_owned(),
        StrContains => "str.contains".to_owned(),
```

(If Task 2 Step 4 already added these print arms to get the workspace compiling, verify they match exactly.)

- [x] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-parser parses_string_predicates string_predicate_wrong_sort_rejected`
Expected: PASS

- [x] **Step 5: Commit**

```bash
git add crates/shinri-parser
git commit -m "feat(parser): parse + print str.prefixof/str.suffixof/str.contains (slice 12)"
```

---

### Task 4: Constant folder (`shinri-str::predicates::fold_str_predicates`)

**Files:**
- Create: `crates/shinri-str/src/predicates.rs`
- Modify: `crates/shinri-str/src/lib.rs:1-8` (add `pub mod predicates;`)
- Test: inline `#[cfg(test)]` in `crates/shinri-str/src/predicates.rs`

**Interfaces:**
- Consumes: `BuiltinOp` variants (Task 2); `Context::{string_const_value, mk_const_bool, term_node, children, mk_app}`.
- Produces: `pub fn fold_str_predicates(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>` — every predicate app whose two args are string literals is replaced by `mk_const_bool(..)`; all other structure preserved (unchanged subtrees keep their `TermId`).

- [x] **Step 1: Write the failing tests**

Create `crates/shinri-str/src/predicates.rs`:

```rust
//! Slice 12 pre-pass: string predicates (`str.prefixof` / `str.suffixof` /
//! `str.contains`).
//!
//! Three stages, run by the solver's string-path seam in this order:
//! 1. [`fold_str_predicates`] — constant-fold literal-literal predicate atoms
//!    to Boolean constants (any polarity).
//! 2. [`has_unrewritable_str_predicate`] — polarity fence: any surviving
//!    predicate occurrence that is not positive-only (negative, mixed, or
//!    non-monotone context) makes the query fence to a sound `Unknown`.
//! 3. [`rewrite_str_predicates`] — rewrite positive-only atoms to their
//!    existential concat decomposition (fresh String vars).
//!
//! Folding on Rust `&str` is correct for SMT-LIB code-point semantics:
//! UTF-8 is concatenation-preserving and code-point-aligned, so byte-level
//! `starts_with`/`ends_with`/`contains` coincide with code-point
//! prefix/suffix/substring.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

fn is_str_predicate(op: &Op) -> bool {
    matches!(
        op,
        Op::Builtin(BuiltinOp::StrPrefixOf | BuiltinOp::StrSuffixOf | BuiltinOp::StrContains)
    )
}

/// Stage 1: constant-fold every predicate app whose BOTH args are string
/// literals, at any polarity/position. Returns rewritten assertions;
/// untouched subtrees keep their `TermId`s.
pub fn fold_str_predicates(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| fold_term(ctx, a, &mut memo))
        .collect()
}

fn fold_term(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> = children
                .iter()
                .map(|&c| fold_term(ctx, c, memo))
                .collect();
            let folded = if is_str_predicate(&op) {
                let a = ctx.string_const_value(new_children[0]).map(str::to_owned);
                let b = ctx.string_const_value(new_children[1]).map(str::to_owned);
                match (op, a, b) {
                    // prefixof/suffixof: args are (needle p, haystack s).
                    (Op::Builtin(BuiltinOp::StrPrefixOf), Some(p), Some(s)) => {
                        Some(s.starts_with(&p))
                    }
                    (Op::Builtin(BuiltinOp::StrSuffixOf), Some(p), Some(s)) => {
                        Some(s.ends_with(&p))
                    }
                    // contains: args are (haystack s, needle sub).
                    (Op::Builtin(BuiltinOp::StrContains), Some(s), Some(sub)) => {
                        Some(s.contains(&sub))
                    }
                    _ => None,
                }
            } else {
                None
            };
            if let Some(v) = folded {
                ctx.mk_const_bool(v)
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(nc, oc)| nc != oc);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("fold: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn pred(ctx: &mut Context, op: BuiltinOp, a: TermId, b: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(op), &[a, b]).unwrap()
    }

    #[test]
    fn folds_all_three_predicates_true_and_false() {
        let mut ctx = Context::new();
        let ab = ctx.mk_string_const("ab");
        let abc = ctx.mk_string_const("abc");
        let d = ctx.mk_string_const("d");
        let t_true = ctx.mk_const_bool(true);
        let t_false = ctx.mk_const_bool(false);
        // (str.prefixof "ab" "abc") → true ; (str.prefixof "d" "abc") → false
        let p1 = pred(&mut ctx, BuiltinOp::StrPrefixOf, ab, abc);
        let p2 = pred(&mut ctx, BuiltinOp::StrPrefixOf, d, abc);
        // (str.suffixof "ab" "abc") → false (needle-first arg order!)
        let p3 = pred(&mut ctx, BuiltinOp::StrSuffixOf, ab, abc);
        // (str.contains "abc" "d") → false (haystack-first arg order!)
        let p4 = pred(&mut ctx, BuiltinOp::StrContains, abc, d);
        let out = fold_str_predicates(&mut ctx, &[p1, p2, p3, p4]);
        assert_eq!(out, vec![t_true, t_false, t_false, t_false]);
    }

    #[test]
    fn folds_under_negation_and_leaves_symbolic_untouched() {
        let mut ctx = Context::new();
        let abc = ctx.mk_string_const("abc");
        let d = ctx.mk_string_const("d");
        let s = str_var(&mut ctx, "s");
        // (not (str.contains "abc" "d")) → (not false)
        let inner = pred(&mut ctx, BuiltinOp::StrContains, abc, d);
        let not_inner = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[inner]).unwrap();
        // symbolic: (str.prefixof "d" s) untouched, same TermId.
        let sym = pred(&mut ctx, BuiltinOp::StrPrefixOf, d, s);
        let out = fold_str_predicates(&mut ctx, &[not_inner, sym]);
        let f = ctx.mk_const_bool(false);
        let want_not = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[f]).unwrap();
        assert_eq!(out[0], want_not);
        assert_eq!(out[1], sym, "symbolic predicate must keep its TermId");
    }
}
```

Also add to `crates/shinri-str/src/lib.rs` module list (after `pub mod normalize;`):

```rust
pub mod predicates;
```

- [x] **Step 2: Run tests to verify current state**

Run: `cargo test -p shinri-str predicates::`
Expected: PASS (the module is written complete in Step 1 — the "failing" phase here was Task 2/3 making the variants exist; verify both tests green and, if either fails, fix before committing).

- [x] **Step 3: Commit**

```bash
git add crates/shinri-str
git commit -m "feat(str): predicates module — constant folder for prefixof/suffixof/contains (slice 12)"
```

---

### Task 5: Polarity classifier + fence (`has_unrewritable_str_predicate`)

**Files:**
- Modify: `crates/shinri-str/src/predicates.rs`
- Test: inline `#[cfg(test)]` in the same file

**Interfaces:**
- Consumes: `is_str_predicate` (Task 4).
- Produces: `pub fn has_unrewritable_str_predicate(ctx: &Context, assertions: &[TermId]) -> bool` — true iff any predicate atom has a reachable negative occurrence. The solver seam (Task 7) calls it AFTER folding.

- [x] **Step 1: Write the failing tests**

Append to the `tests` module in `predicates.rs`:

```rust
    fn bool_var(ctx: &mut Context, name: &str) -> TermId {
        let b = ctx.bool_sort();
        let f = ctx.declare_fun(name, &[], b);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn polarity_fence_classification() {
        let mut ctx = Context::new();
        let lit = ctx.mk_string_const("a");
        let s = str_var(&mut ctx, "s");
        let x = bool_var(&mut ctx, "x");
        let p = pred(&mut ctx, BuiltinOp::StrPrefixOf, lit, s);

        // Positive-only shapes: NOT fenced.
        let or_px = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[p, x]).unwrap();
        let and_px = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[p, x]).unwrap();
        let imp_xp = ctx
            .mk_app(Op::Builtin(BuiltinOp::Implies), &[x, p])
            .unwrap();
        assert!(!has_unrewritable_str_predicate(&ctx, &[p]));
        assert!(!has_unrewritable_str_predicate(&ctx, &[or_px, and_px, imp_xp]));

        // Negative / non-monotone shapes: fenced.
        let not_p = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[p]).unwrap();
        let imp_px = ctx
            .mk_app(Op::Builtin(BuiltinOp::Implies), &[p, x])
            .unwrap();
        let xor_px = ctx.mk_app(Op::Builtin(BuiltinOp::Xor), &[p, x]).unwrap();
        let eq_px = ctx.mk_eq(p, x).unwrap(); // Bool-eq: non-monotone
        let a_lit = ctx.mk_string_const("a");
        let b_lit = ctx.mk_string_const("b");
        let ite_p = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[p, a_lit, b_lit])
            .unwrap(); // predicate as ite condition
        let eq_ite = ctx.mk_eq(ite_p, s).unwrap();
        for bad in [not_p, imp_px, xor_px, eq_px, eq_ite] {
            assert!(
                has_unrewritable_str_predicate(&ctx, &[bad]),
                "shape must fence"
            );
        }

        // Mixed polarity across assertions: fenced.
        assert!(has_unrewritable_str_predicate(&ctx, &[or_px, not_p]));

        // Double negation is positive again: NOT fenced.
        let not_not_p = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[not_p]).unwrap();
        assert!(!has_unrewritable_str_predicate(&ctx, &[not_not_p]));
    }
```

(If `BuiltinOp::Xor` does not exist in this codebase, drop the `xor_px` case and rely on Bool-eq — check `term.rs` first.)

- [x] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str polarity_fence_classification`
Expected: COMPILE FAIL — `has_unrewritable_str_predicate` not defined.

- [x] **Step 3: Implement the classifier**

Add to `predicates.rs` (above the tests module):

```rust
#[derive(Clone, Copy, Default)]
struct Polarity {
    pos: bool,
    neg: bool,
}

/// Stage 2: polarity fence. True iff any string-predicate atom (surviving
/// stage-1 folding) has a reachable NEGATIVE occurrence — i.e. is not
/// positive-only. Positive-only atoms are safe for the stage-3 existential
/// rewrite; everything else must fence the query to a sound `Unknown`.
///
/// Polarity descent: `and`/`or` preserve; `not` flips; `=>` flips every
/// antecedent (all args but the last). ANY other enclosing structure —
/// `xor`, `=`/`distinct` over Bool, `ite` in any position, uninterpreted
/// applications, or a predicate nested inside another predicate's args —
/// marks descendants both-polarity. Unrecognized structure therefore fails
/// SOUND (fence), never unsound (wrong-side rewrite).
pub fn has_unrewritable_str_predicate(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut map: FxHashMap<TermId, Polarity> = FxHashMap::default();
    let mut seen: FxHashSet<(TermId, bool, bool)> = FxHashSet::default();
    for &a in assertions {
        collect_polarities(ctx, a, true, false, &mut map, &mut seen);
    }
    map.values().any(|p| p.neg)
}

fn collect_polarities(
    ctx: &Context,
    t: TermId,
    pos: bool,
    both: bool,
    map: &mut FxHashMap<TermId, Polarity>,
    seen: &mut FxHashSet<(TermId, bool, bool)>,
) {
    if !seen.insert((t, pos, both)) {
        return;
    }
    match ctx.term_node(t) {
        TermNode::Const { .. } => {}
        TermNode::App { op, args, .. } => {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            if is_str_predicate(op) {
                let e = map.entry(t).or_default();
                if both {
                    e.pos = true;
                    e.neg = true;
                } else if pos {
                    e.pos = true;
                } else {
                    e.neg = true;
                }
                // A predicate nested inside THIS predicate's String args can
                // only sit in a Bool position (an ite condition) — treat it
                // as non-monotone.
                for &k in &kids {
                    collect_polarities(ctx, k, true, true, map, seen);
                }
                return;
            }
            match op {
                Op::Builtin(BuiltinOp::And | BuiltinOp::Or) => {
                    for &k in &kids {
                        collect_polarities(ctx, k, pos, both, map, seen);
                    }
                }
                Op::Builtin(BuiltinOp::Not) => {
                    collect_polarities(ctx, kids[0], !pos, both, map, seen);
                }
                Op::Builtin(BuiltinOp::Implies) => {
                    // n-ary right-assoc: all but the last arg are antecedents.
                    let (last, ants) = kids.split_last().expect("=> has args");
                    for &k in ants {
                        collect_polarities(ctx, k, !pos, both, map, seen);
                    }
                    collect_polarities(ctx, *last, pos, both, map, seen);
                }
                // Everything else is a non-monotone context for anything below.
                _ => {
                    for &k in &kids {
                        collect_polarities(ctx, k, true, true, map, seen);
                    }
                }
            }
        }
    }
}
```

- [x] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-str polarity_fence_classification`
Expected: PASS

- [x] **Step 5: Commit**

```bash
git add crates/shinri-str
git commit -m "feat(str): polarity classifier + has_unrewritable_str_predicate fence (slice 12)"
```

---

### Task 6: Positive rewrite (`rewrite_str_predicates`)

**Files:**
- Modify: `crates/shinri-str/src/predicates.rs`
- Modify: `crates/shinri-str/src/reduce.rs:70` (`fn next_fresh` → `pub(crate) fn next_fresh`)
- Test: inline `#[cfg(test)]` in `predicates.rs`

**Interfaces:**
- Consumes: `crate::reduce::next_fresh()` (made `pub(crate)`), `Context::{declare_fun, mk_app, mk_eq, string_sort}`.
- Produces: `pub fn rewrite_str_predicates(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>` — every remaining predicate app (caller guarantees positive-only via Task 5's fence) is replaced by its existential concat equation. Fresh vars named `!pfx{n}` / `!sfx{n}` / `!ctnl{n}`+`!ctnr{n}` (the `!` prefix marks internal, matching `!pre{n}`/`!mid{n}`/`!post{n}`).

- [x] **Step 1: Write the failing tests**

Append to the `tests` module in `predicates.rs`:

```rust
    /// Destructure `(= lhs (str.++ …))` and return (lhs, concat kids).
    fn eq_concat_parts(ctx: &Context, t: TermId) -> (TermId, Vec<TermId>) {
        let shinri_core::TermNode::App { op, args, .. } = ctx.term_node(t) else {
            panic!("expected eq app");
        };
        assert!(matches!(op, Op::Builtin(BuiltinOp::Eq)));
        let kids: Vec<TermId> = ctx.children(*args).to_vec();
        let shinri_core::TermNode::App { op: cop, args: cargs, .. } = ctx.term_node(kids[1])
        else {
            panic!("expected concat rhs");
        };
        assert!(matches!(cop, Op::Builtin(BuiltinOp::StrConcat)));
        (kids[0], ctx.children(*cargs).to_vec())
    }

    #[test]
    fn rewrites_positive_predicates_to_concat_equations() {
        let mut ctx = Context::new();
        let p = ctx.mk_string_const("ab");
        let s = str_var(&mut ctx, "s");

        // prefixof(p, s) → (= s (str.++ p k))
        let pf = pred(&mut ctx, BuiltinOp::StrPrefixOf, p, s);
        let out = rewrite_str_predicates(&mut ctx, &[pf]);
        let (lhs, kids) = eq_concat_parts(&ctx, out[0]);
        assert_eq!(lhs, s);
        assert_eq!(kids.len(), 2);
        assert_eq!(kids[0], p, "needle must lead in prefixof decomposition");

        // suffixof(p, s) → (= s (str.++ k p))
        let sf = pred(&mut ctx, BuiltinOp::StrSuffixOf, p, s);
        let out = rewrite_str_predicates(&mut ctx, &[sf]);
        let (lhs, kids) = eq_concat_parts(&ctx, out[0]);
        assert_eq!(lhs, s);
        assert_eq!(kids.len(), 2);
        assert_eq!(kids[1], p, "needle must trail in suffixof decomposition");

        // contains(s, sub) → (= s (str.++ k1 sub k2))
        let ct = pred(&mut ctx, BuiltinOp::StrContains, s, p);
        let out = rewrite_str_predicates(&mut ctx, &[ct]);
        let (lhs, kids) = eq_concat_parts(&ctx, out[0]);
        assert_eq!(lhs, s);
        assert_eq!(kids.len(), 3);
        assert_eq!(kids[1], p, "needle must be the middle of contains");
    }

    #[test]
    fn rewrite_dedups_repeated_atom() {
        let mut ctx = Context::new();
        let p = ctx.mk_string_const("a");
        let s = str_var(&mut ctx, "s");
        let x = bool_var(&mut ctx, "x");
        let pf = pred(&mut ctx, BuiltinOp::StrPrefixOf, p, s);
        let or1 = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[pf, x]).unwrap();
        // Same atom in two assertions → SAME equation term (one fresh var set).
        let out = rewrite_str_predicates(&mut ctx, &[pf, or1]);
        let (_, kids0) = eq_concat_parts(&ctx, out[0]);
        let shinri_core::TermNode::App { args, .. } = ctx.term_node(out[1]) else {
            panic!("or app");
        };
        let or_kids: Vec<TermId> = ctx.children(*args).to_vec();
        let (_, kids1) = eq_concat_parts(&ctx, or_kids[0]);
        assert_eq!(kids0[1], kids1[1], "repeated atom must reuse its fresh var");
    }
```

- [x] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str rewrites_positive_predicates rewrite_dedups_repeated_atom`
Expected: COMPILE FAIL — `rewrite_str_predicates` not defined.

- [x] **Step 3: Implement the rewrite**

In `crates/shinri-str/src/reduce.rs:70`, change `fn next_fresh()` to `pub(crate) fn next_fresh()`.

Add to `predicates.rs`:

```rust
fn fresh_str_var(ctx: &mut Context, name: &str) -> TermId {
    let str_s = ctx.string_sort();
    let sym = ctx.declare_fun(name, &[], str_s);
    ctx.mk_app(Op::Uninterpreted(sym), &[])
        .expect("fresh string var")
}

/// Stage 3: rewrite every remaining (positive-only — the caller must have
/// fenced otherwise via [`has_unrewritable_str_predicate`]) predicate atom to
/// its existential concat decomposition:
///
/// - `(str.prefixof p s)` → `(= s (str.++ p k))`
/// - `(str.suffixof p s)` → `(= s (str.++ k p))`
/// - `(str.contains s sub)` → `(= s (str.++ k1 sub k2))`
///
/// Equisatisfiable for positive occurrences: the equation implies the
/// predicate, and any model of the predicate extends to the fresh vars.
/// Memoized on the atom's TermId so a repeated atom reuses one fresh-var set.
pub fn rewrite_str_predicates(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite_pred(ctx, a, &mut memo))
        .collect()
}

fn rewrite_pred(
    ctx: &mut Context,
    t: TermId,
    memo: &mut FxHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> = children
                .iter()
                .map(|&c| rewrite_pred(ctx, c, memo))
                .collect();
            match op {
                Op::Builtin(BuiltinOp::StrPrefixOf) => {
                    let (p, s) = (new_children[0], new_children[1]);
                    let n = crate::reduce::next_fresh();
                    let k = fresh_str_var(ctx, &format!("!pfx{n}"));
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[p, k])
                        .expect("p ++ k");
                    ctx.mk_eq(s, cat).expect("s = p ++ k")
                }
                Op::Builtin(BuiltinOp::StrSuffixOf) => {
                    let (p, s) = (new_children[0], new_children[1]);
                    let n = crate::reduce::next_fresh();
                    let k = fresh_str_var(ctx, &format!("!sfx{n}"));
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[k, p])
                        .expect("k ++ p");
                    ctx.mk_eq(s, cat).expect("s = k ++ p")
                }
                Op::Builtin(BuiltinOp::StrContains) => {
                    let (s, sub) = (new_children[0], new_children[1]);
                    let n = crate::reduce::next_fresh();
                    let kl = fresh_str_var(ctx, &format!("!ctnl{n}"));
                    let kr = fresh_str_var(ctx, &format!("!ctnr{n}"));
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[kl, sub, kr])
                        .expect("kl ++ sub ++ kr");
                    ctx.mk_eq(s, cat).expect("s = kl ++ sub ++ kr")
                }
                _ => {
                    let changed = new_children
                        .iter()
                        .zip(children.iter())
                        .any(|(nc, oc)| nc != oc);
                    if changed {
                        ctx.mk_app(op, &new_children)
                            .expect("rewrite: well-sorted rebuild")
                    } else {
                        t
                    }
                }
            }
        }
    };
    memo.insert(t, result);
    result
}
```

- [x] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str predicates::`
Expected: PASS (all predicates-module tests).

- [x] **Step 5: Commit**

```bash
git add crates/shinri-str
git commit -m "feat(str): rewrite_str_predicates — positive-occurrence existential concat decomposition (slice 12)"
```

---

### Task 7: Solver seam wiring + always-on e2e pins

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs:402-425` (string-path seam)
- Modify: `crates/shinri-solver/src/string_stage.rs:39-46` (`is_string_op`)
- Modify: `crates/shinri-str/src/reduce.rs:136-165` (`contains_string_op`)
- Test: `crates/shinri-solver/tests/script_e2e.rs` (non-oracle, always-on)

**Interfaces:**
- Consumes: `shinri_str::predicates::{fold_str_predicates, has_unrewritable_str_predicate, rewrite_str_predicates}` (Tasks 4-6).
- Produces: end-to-end behavior — folded/positive predicates decide; negative/mixed/non-monotone fence to `unknown`.

- [x] **Step 1: Write the failing e2e tests**

Append to `crates/shinri-solver/tests/script_e2e.rs` (reuse the file's `run_script` helper; match its existing set-logic conventions — if neighboring string tests omit `(set-logic …)`, omit it here too):

```rust
// ── Slice 12: string predicates ──────────────────────────────────────────────

#[test]
fn str_predicate_literal_folds_decide_any_polarity() {
    // Literal-literal predicates constant-fold at ANY polarity — including
    // under (not …) — so no fence applies and the query decides.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (not (str.contains "abc" "d")))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
    let out = run_script(r#"(set-logic QF_S)(assert (str.prefixof "b" "abc"))(check-sat)"#);
    assert_eq!(out, vec!["unsat"]);
    let out = run_script(r#"(set-logic QF_S)(assert (str.suffixof "bc" "abc"))(check-sat)"#);
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn str_prefixof_positive_decides() {
    // prefix "ab" forces len(s) >= 2 → UNSAT with len(s) = 1.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof "ab" s))(assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // len(s) = 2 forces s = "ab" exactly.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof "ab" s))(assert (= (str.len s) 2))
           (check-sat)(get-value (s))"#,
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"));
    assert!(
        out.get(1).is_some_and(|v| v.contains("\"ab\"")),
        "s must be \"ab\", got {out:?}"
    );
}

#[test]
fn str_suffixof_and_contains_positive_decide() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.suffixof "ab" s))(assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.contains s "ab"))(assert (<= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.contains s "b"))(assert (= (str.len s) 2))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn str_predicate_with_foldable_substr_decides() {
    // Predicate rewrite runs BEFORE the substr desugar; the constant substr
    // folds to "ab" inside the emitted equation (combined fresh-var minters).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof (str.substr "abc" 0 2) s))
           (assert (= (str.len s) 2))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof (str.substr "abc" 0 2) s))
           (assert (= (str.len s) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

// ── Fence canaries: flip-markers for a future negative-polarity slice ────────

#[test]
fn str_predicate_negative_polarity_fences_unknown() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (not (str.contains s "a")))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}

#[test]
fn str_predicate_under_ite_condition_fences_unknown() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)(declare-fun t () String)
           (assert (= t (ite (str.prefixof "a" s) "x" "y")))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}

#[test]
fn str_predicate_mixed_polarity_fences_unknown() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)(declare-fun b () Bool)
           (assert (or (str.contains s "a") b))
           (assert (or (not (str.contains s "a")) (not b)))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}

#[test]
fn str_predicate_over_uf_fences_unknown() {
    // Upstream string_stage fence condition 1 (String under non-nullary UF)
    // catches this BEFORE the predicate pass — unchanged behavior, pinned.
    let out = run_script(
        r#"(declare-fun s () String)(declare-fun g (String) String)
           (assert (str.prefixof (g s) s))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}
```

Execution notes: (a) if `(set-logic QF_S)` handling rejects `Bool`/mixed declarations in any of these, match whatever set-logic string the file's existing mixed tests use (or omit the command); (b) if `str_prefixof_positive_decides`'s SAT case returns `unknown` (word-equation fuel), that is a sound-but-incomplete result — replace the length pin with a shape that decides (e.g. drop the `get-value` and assert plain `sat` on `(assert (str.prefixof "a" s))(assert (= s "ab"))`) and record the weaker pin + reason in the test comment.

- [x] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-solver --test script_e2e str_predicate str_prefixof str_suffixof`
Expected: FAIL — parse errors surface as `(error "unknown operator str.prefixof")`-shaped output… actually the parser now accepts the ops (Task 3), so expected failures are wrong VERDICTS: the un-wired solver misroutes predicate atoms (EUF-opaque Bool atoms) — most tests fail on verdict mismatch. Either failure mode is acceptable evidence; record which one you saw.

- [x] **Step 3: Wire the seam**

In `crates/shinri-solver/src/lib.rs`, inside the `uses_strings` block (after the `string_stage::fenced` check at line ~403, before the substr fence at ~416):

```rust
            // ── Slice 12: string predicates (prefixof/suffixof/contains) ──────
            // 1. Constant-fold literal-literal predicate atoms (any polarity).
            // 2. Fence any surviving predicate occurrence that is not
            //    positive-only (negative / mixed / non-monotone context) →
            //    sound Unknown (canary-pinned; flip-markers for a future
            //    negative-polarity slice).
            // 3. (Below, after the substr fence) rewrite positive-only atoms
            //    to existential concat equations the wordeq engine owns.
            assertions =
                shinri_str::predicates::fold_str_predicates(&mut self.ctx, &assertions);
            if shinri_str::predicates::has_unrewritable_str_predicate(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

Then, immediately BEFORE the existing `reduce_assertions` call at line ~423:

```rust
            assertions =
                shinri_str::predicates::rewrite_str_predicates(&mut self.ctx, &assertions);
```

In `crates/shinri-solver/src/string_stage.rs` `is_string_op` (line 39), extend the matches:

```rust
        Op::Builtin(
            BuiltinOp::StrConcat
                | BuiltinOp::StrLen
                | BuiltinOp::StrAt
                | BuiltinOp::StrSubstr
                | BuiltinOp::StrPrefixOf
                | BuiltinOp::StrSuffixOf
                | BuiltinOp::StrContains
        )
```

In `crates/shinri-str/src/reduce.rs` `contains_string_op` (line 139), extend the same way (add the three variants to the `matches!`).

- [x] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-solver --test script_e2e str_predicate str_prefixof str_suffixof`
Expected: PASS (subject to the Step-1 execution notes).
Then the string-adjacent net: `cargo test -p shinri-solver --test script_e2e` and `cargo test -p shinri-str`
Expected: PASS, no regressions.

- [x] **Step 5: Commit**

```bash
git add crates/shinri-solver crates/shinri-str
git commit -m "feat(solver): wire string-predicate fold/fence/rewrite into string path + e2e pins & fence canaries (slice 12)"
```

---

### Task 8: Differential oracle family `qfs_predicates_matches_z3`

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (new generator method + new test fn; existing `qfs_matches_z3` untouched)

**Interfaces:**
- Consumes: the file's existing `Lcg`, `Gen`, `shinri_verdict`, `z3_verdict`, `parse_string_values`, `z3_with_model`, `Verdict`.
- Produces: a permanent z3-differential family for the predicate fragment — 0 disagreements, Unknowns tolerated + counted, `sat>0 ∧ unsat>0` asserted.

- [x] **Step 1: Add the generator + test**

Add to `impl Gen` (after `self_ref_eq`):

```rust
    /// A POSITIVE-polarity predicate assertion (slice 12). Never negated and
    /// never nested under non-monotone structure: negative/mixed occurrences
    /// are fenced to sound Unknown by design, and would make this family
    /// all-Unknown. Needle is a var or small literal; haystack is a var or a
    /// short concat. Arg order per SMT-LIB: prefixof/suffixof needle-first,
    /// contains haystack-first.
    fn predicate_assertion(&mut self) {
        let needle = self.atom_term();
        let hay = if self.rng.below(2) == 0 {
            self.var()
        } else {
            let n = 2 + self.rng.below(2);
            let parts: Vec<String> = (0..n).map(|_| self.atom_term()).collect();
            format!("(str.++ {})", parts.join(" "))
        };
        let atom = match self.rng.below(3) {
            0 => format!("(str.prefixof {needle} {hay})"),
            1 => format!("(str.suffixof {needle} {hay})"),
            _ => format!("(str.contains {hay} {needle})"),
        };
        self.body.push_str(&format!("(assert {atom})\n"));
    }

    /// Instance body for the predicate family: 1-2 positive predicate
    /// assertions + 1-2 general assertions (word eqs / lengths — these may be
    /// negated; they contain no predicates).
    fn finish_predicates(mut self) -> String {
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.predicate_assertion();
        }
        let na = 1 + self.rng.below(2);
        for _ in 0..na {
            self.assertion();
        }
        self.body
    }
```

Add after `gen_body`:

```rust
fn gen_predicates_body(seed: u64) -> String {
    Gen::new(seed).finish_predicates()
}
```

Add after `qfs_matches_z3` (mirroring its structure exactly; differences: seed, iter count, generator, and Unknown REPORTING — the contract tolerates Unknowns because `contains` mints two fresh vars per atom and the word-equation search is fuel-bounded):

```rust
const PRED_N_ITERS: usize = 200;

#[test]
fn qfs_predicates_matches_z3() {
    let mut rng = Lcg(0x51_2A_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness) =
        (0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..PRED_N_ITERS {
        let seed = rng.next();
        let body = gen_predicates_body(seed);

        let ours = shinri_verdict(&format!("{body}(check-sat)\n"));
        if ours == Verdict::Unknown {
            n_unknown += 1; // sound incompleteness (fuel): tolerated, counted
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S PREDICATE SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{body}(check-sat)"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let get = format!(
                    "{body}(check-sat)\n(get-value ({}))\n",
                    (0..N_VARS)
                        .map(|k| format!("s{k}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                let lines = shinri_lines(&get);
                if let Some(resp) = lines.get(1) {
                    let model = parse_string_values(resp);
                    if !model.is_empty() {
                        let w = z3_with_model(&body, &model);
                        assert_eq!(
                            w,
                            Verdict::Sat,
                            "WITNESS FAILURE (iter {it}, seed {seed}): model {model:?}\n{body}"
                        );
                        n_witness += 1;
                    }
                }
            }
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    println!(
        "qfs_predicates_matches_z3: {PRED_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown; \
         {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "predicate family produced zero SAT instances");
    assert!(n_unsat > 0, "predicate family produced zero UNSAT instances");
    assert!(n_witness > 0, "no witnesses checked — model path not exercised");
}
```

- [x] **Step 2: Run the family**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential qfs_predicates_matches_z3 -- --nocapture` (background if slow; z3 must be on PATH)
Expected: PASS, printed counts. Record the counts in the Task 9 docs truth-up. If `n_sat`/`n_unsat`/`n_witness` assertions fail, tune the generator mix (e.g. bias `hay` toward vars, keep 1 predicate + 1 length atom) — do NOT weaken the disagreement assertion.

- [x] **Step 3: Verify the existing family is untouched**

Run: `git diff --stat crates/shinri-solver/tests/qfs_differential.rs` — confirm `qfs_matches_z3` and its generator methods (`assertion`, `finish`, `gen_body`) have no changes; only additions.
Then: `cargo test -p shinri-solver --features oracle --test qfs_differential qfs_matches_z3 -- --nocapture`
Expected: PASS with its historical count profile (this family's stream is untouched).

- [x] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(solver): qfs_predicates_matches_z3 differential family — positive predicates, 0 disagreements, unknowns counted (slice 12)"
```

---

### Task 9: Full net + docs truth-up

**Files:**
- Modify: `docs/superpowers/specs/2026-07-07-shinri-slice12-str-predicates-design.md` (Status line)
- Modify: `crates/shinri-solver/tests/fp_oracle.rs:1818` (stale comment)
- Modify: this plan (final checkboxes)

**Interfaces:**
- Consumes: everything landed in Tasks 1-8.
- Produces: green full net + truthful docs; slice ready for finishing-a-development-branch.

- [x] **Step 1: Format + full workspace test (background, controller-run)**

```bash
cargo fmt --all
cargo test --workspace
```
Expected: fmt makes no or trivial diffs (commit any); workspace suite green. Run the suite in the background; do NOT dispatch cargo subagents while it runs.

- [x] **Step 2: Full oracle sweep (background; long — fp family alone ~915 s)**

```bash
cargo test -p shinri-solver --features oracle -- --nocapture
```
Expected: 0 disagreements everywhere; `qfs_matches_z3` count profile unchanged; new family counts recorded.

- [x] **Step 3: Clean-cache clippy**

```bash
cargo clean
cargo clippy --workspace --all-targets -- -D warnings
```
Expected: zero warnings. (Clean cache is mandatory — warm-cache clippy false-passes here. Never `clippy --fix`; it deadlocks in this environment.)

- [x] **Step 4: Docs truth-up**

- Spec Status line → `Status: IMPLEMENTED (slice 12 landed). <one-line summary: decisive counts from the new family, e.g. "predicate family sat=X/unsat=Y/unknown=Z @ 200 iters, 0 disagreements">` plus any residue (e.g. low decisive rate on `contains`) filed as an explicit follow-up line.
- `fp_oracle.rs:1818`: reword — the three predicates are now implemented; that str family stays equality/concat/len-only as a deliberate scope choice (slice-12 spec non-goal), not because the ops are unimplemented.
- Check off all boxes in this plan.

- [x] **Step 5: Commit**

```bash
git add -A
git commit -m "docs: slice-12 spec/ledger truth-up — predicate family counts, fp_oracle comment refresh (slice 12)"
```

- [x] **Step 6:** Use superpowers:finishing-a-development-branch (branch → PR → merge per house flow).

---

## Self-Review (performed at write time)

1. **Spec coverage:** §Goal posture → Tasks 4/5/6; §1 surface → Tasks 2/3/7; §2 mechanism + ordering → Tasks 4-7 (seam order: fold → predicate fence → substr fence → predicate rewrite → substr desugar); §3 model channel → witness path exercised by Task 8's `z3_with_model` + `get-value` pin in Task 7; §4 testing → Tasks 1 (canary hunt), 2-6 (unit), 7 (e2e + canaries), 8 (oracle), 9 (net); §5 risks → fuel risk owned by Task 8's tolerated-unknown contract, classifier risk by Task 5 tests + Task 8, fresh-var interplay by Task 7's combined pin, UF fence by Task 7 canary; §6 acceptance table → Tasks 7/8/9.
2. **Placeholder scan:** Task 3 Step 1 asks the implementer to copy in-module scaffolding by name (`parses_strings_str_at`, parser.rs:1745) with the assertions spelled out — deliberate, since the helper's exact shape lives beside the new test. No TBDs.
3. **Type consistency:** `fold_str_predicates(&mut Context, &[TermId]) -> Vec<TermId>`, `has_unrewritable_str_predicate(&Context, &[TermId]) -> bool`, `rewrite_str_predicates(&mut Context, &[TermId]) -> Vec<TermId>` used identically in Tasks 4-7; fresh-var names `!pfx`/`!sfx`/`!ctnl`/`!ctnr` consistent between Task 6 code and comments; `pub(crate) fn next_fresh` change matches its Task 6 call site.
