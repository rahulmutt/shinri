# Slice 23 — `str.<` / `str.<=` Lexicographic Ordering Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Parse `str.<` / `str.<=` and decide their tractable fragment (literal folds, empty-string boundaries, reflexivity) by equivalence rewrite, fencing every other symbolic comparison to sound Unknown.

**Architecture:** A pure rewrite slice in the mold of slices 20/22. Two net-new `BuiltinOp` variants get parsed, sorted (String×String→Bool), and routed into the string path. A new `shinri-str/src/order.rs` pass runs one bottom-up memoized rewrite (all arms are full equivalences — no fresh vars, no polarity tracking, no model repair), followed by a presence fence: any surviving `str.<`/`str.<=` application makes the solver return sound `Unknown`. Wired at the `code_conv` seam in the solver's string pipeline.

**Tech Stack:** Rust workspace (`cargo`), crates `shinri-core` (AST/Context), `shinri-parser` (SMT-LIB parse/print), `shinri-str` (string engine), `shinri-solver` (pipeline + tests). Differential testing against the `z3` CLI.

## Global Constraints

- **Zero changes** to the word-equation engine (`wordeq.rs`), the regex core (`regex.rs`/`memb.rs`), the arith seam, `Fuel`, or the SAT budgets. This slice only adds a rewrite pass + fence.
- **Every rewrite arm is a full two-way equivalence** — sound at any polarity, nesting, or occurrence count. Never a positive-only / existential rewrite. Soundness rule: the pass preserves satisfiability; the fence only ever weakens a verdict to Unknown, never flips one.
- **Folding uses Rust `&str` `<` / `<=`**, which equals SMT-LIB code-point order (UTF-8 is code-point-order-preserving byte-wise) — the same argument `predicates.rs:13-16` makes for prefix/suffix/contains.
- **Binary only.** `str.<`/`str.<=` are String×String→Bool, arity 2, mirroring `StrPrefixOf | StrSuffixOf | StrContains`.
- **ASCII-only** string literals in the differential generator (z3 CLI byte-parses multi-byte literals; a pre-existing artifact, per the slice-22 spec §5).
- Run `cargo fmt` before every commit (CI gates `cargo fmt --check`); subagents do not auto-format.

---

### Task 1: Operators — parse, sort, print, route

Add the two operators to the AST, parser, printer, sort checker, and the string-path router. Deliverable: `(str.< a b)` / `(str.<= a b)` parse to well-sorted Bool terms; no rewrite/decision yet.

**Files:**
- Modify: `crates/shinri-core/src/term.rs:92` (add variants after `StrContains`)
- Modify: `crates/shinri-parser/src/parser.rs:328` (`builtin_for` name→op arms) **and** `parser.rs:934` (`apply_builtin` delegation arm)
- Modify: `crates/shinri-parser/src/print.rs:195` (print arms after `StrContains`)
- Modify: `crates/shinri-core/src/context.rs:512` (extend the String×String→Bool sort arm)
- Modify: `crates/shinri-solver/src/string_stage.rs:52` (add to `is_string_op`)
- Test: `crates/shinri-parser/src/parser.rs` (new `#[test]` in the existing `mod tests`)

**Interfaces:**
- Produces: `BuiltinOp::StrLt`, `BuiltinOp::StrLeq` — both String×String→Bool. Later tasks match on `Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq)`.

- [ ] **Step 1: Write the failing test**

Add to the `#[test]` module in `crates/shinri-parser/src/parser.rs`:

```rust
#[test]
fn parse_str_order_ops_sort_to_bool() {
    use shinri_core::Context;
    fn parse(src: &str) -> (Context, shinri_core::TermId) {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        let t = p.parse_term_pub(&mut ctx).expect("parse term");
        (ctx, t)
    }
    // Both operators over string literals sort to Bool.
    let (ctx, t) = parse("(str.< \"a\" \"b\")");
    assert_eq!(ctx.sort_of(t), ctx.bool_sort());
    let (ctx, t) = parse("(str.<= \"a\" \"b\")");
    assert_eq!(ctx.sort_of(t), ctx.bool_sort());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser parse_str_order_ops_sort_to_bool`
Expected: FAIL — parse error `unknown operator str.<` (the arm does not exist yet).

- [ ] **Step 3a: Add the `BuiltinOp` variants**

In `crates/shinri-core/src/term.rs`, after line 92 (`StrContains,`):

```rust
    // Slice 23: lexicographic ordering, String × String → Bool.
    StrLt,  // str.<
    StrLeq, // str.<=
```

- [ ] **Step 3b: Add the parser arms**

In `crates/shinri-parser/src/parser.rs`, after line 328 (`"str.contains" => StrContains,`):

```rust
            "str.<" => StrLt,
            "str.<=" => StrLeq,
```

- [ ] **Step 3c: Add the print arms**

In `crates/shinri-parser/src/print.rs`, after line 195 (`StrContains => "str.contains".to_owned(),`):

```rust
        // Slice 23
        StrLt => "str.<".to_owned(),
        StrLeq => "str.<=".to_owned(),
```

- [ ] **Step 3c-bis: Add the `apply_builtin` delegation arm**

`apply_builtin` (`parser.rs`) is an exhaustive match that delegates each builtin to `Self::mk`. In the string-predicate delegation arm (the `BuiltinOp::StrPrefixOf | StrSuffixOf | StrContains | ... => Self::mk(ctx, Op::Builtin(op), &args, &sp)` block, ~line 934), add after `| BuiltinOp::StrContains`:

```rust
            | BuiltinOp::StrLt
            | BuiltinOp::StrLeq
```

Without this, `builtin_for` maps the name but `apply_builtin` cannot construct the term (build error / parse failure).

- [ ] **Step 3d: Extend the sort arm**

In `crates/shinri-core/src/context.rs:512`, change the predicate arm head from:

```rust
            StrPrefixOf | StrSuffixOf | StrContains => {
```

to:

```rust
            StrPrefixOf | StrSuffixOf | StrContains | StrLt | StrLeq => {
```

(The body is unchanged: arity 2, both args `string_sort()`, result `bool_sort()`.)

- [ ] **Step 3e: Add to the string-path router**

In `crates/shinri-solver/src/string_stage.rs`, inside `is_string_op` after line 52 (`| BuiltinOp::StrContains`):

```rust
                | BuiltinOp::StrLt
                | BuiltinOp::StrLeq
```

- [ ] **Step 4: Build the workspace and fix any exhaustiveness errors**

Run: `cargo build --workspace`
Expected: SUCCESS. The two known exhaustive `BuiltinOp` matches are `print.rs` (3c) and `apply_builtin` (3c-bis) — both handled. If the compiler reports a non-exhaustive `match` on `BuiltinOp` in any other file, add an arm mirroring the `StrContains` neighbor; passthrough/`_`-style matches (e.g. `is_string_op`, `reduce.rs:148`, the rewrite passes) need no change because surviving `str.<`/`str.<=` atoms are fenced to Unknown before `reduce` runs. Do not guess — let the compiler name the site.

- [ ] **Step 5: Run the test to verify it passes**

Run: `cargo test -p shinri-parser parse_str_order_ops_sort_to_bool`
Expected: PASS.

- [ ] **Step 6: Format and commit**

```bash
cargo fmt
git add crates/shinri-core/src/term.rs crates/shinri-parser/src/parser.rs \
        crates/shinri-parser/src/print.rs crates/shinri-core/src/context.rs \
        crates/shinri-solver/src/string_stage.rs
git commit -m "feat(str): parse + sort str.< / str.<= (slice 23)"
```

---

### Task 2: The `order` rewrite pass + fence

Create the library pass that decides the tractable fragment and the presence fence. Deliverable: a fully unit-tested `shinri-str::order` module; no solver wiring yet.

**Files:**
- Create: `crates/shinri-str/src/order.rs`
- Modify: `crates/shinri-str/src/lib.rs` (add `pub mod order;` next to the other module declarations)
- Test: `crates/shinri-str/src/order.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `BuiltinOp::StrLt`, `BuiltinOp::StrLeq` (Task 1).
- Produces:
  - `pub fn rewrite_str_order(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>` — one bottom-up memoized equivalence rewrite.
  - `pub fn has_unreduced_str_order(ctx: &Context, assertions: &[TermId]) -> bool` — presence fence; `true` iff any `StrLt`/`StrLeq` application survives.

- [ ] **Step 1: Write the module with failing tests**

Create `crates/shinri-str/src/order.rs`:

```rust
//! Slice 23 pre-pass: `str.<` / `str.<=` lexicographic ordering — exact
//! rewriting + fence.
//!
//! Every rewrite here is a FULL logical equivalence (sound at any polarity,
//! nesting, or occurrence count): literal–literal folds, empty-string boundary
//! idioms, and syntactic reflexivity. A single bottom-up memoized pass plus a
//! presence fence. No fresh vars, no polarity tracking, no model repair —
//! the same shape as slice 18's `code_conv` and slice 12's predicate fold.
//!
//! Folding on Rust `&str` is exactly SMT-LIB code-point order: UTF-8 is
//! code-point-order-preserving byte-wise, so `<`/`<=` on `&str` coincides with
//! `str.<`/`str.<=` (the same argument `predicates.rs` makes for
//! prefix/suffix/contains).

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// One bottom-up, memoized equivalence rewrite over each assertion. Untouched
/// subtrees keep their `TermId`s.
pub fn rewrite_str_order(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect()
}

fn rewrite(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> =
                children.iter().map(|&c| rewrite(ctx, c, memo)).collect();
            let special = match op {
                Op::Builtin(BuiltinOp::StrLt) => try_order_atom(ctx, &new_children, false),
                Op::Builtin(BuiltinOp::StrLeq) => try_order_atom(ctx, &new_children, true),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(n, o)| n != o);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("order: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// One equivalence-preserving rewrite of `(str.< a b)` / `(str.<= a b)`.
/// `reflexive` distinguishes `<=` (reflexive: `s <= s` is true) from `<`
/// (irreflexive: `s < s` is false). Returns `None` — leave the atom to the
/// fence — for anything not one of the three decided idioms.
fn try_order_atom(ctx: &mut Context, args: &[TermId], reflexive: bool) -> Option<TermId> {
    let (a, b) = (args[0], args[1]);

    // (c) Reflexivity: syntactically identical (same hash-consed term).
    //     s <= s -> true ; s < s -> false.
    if a == b {
        return Some(ctx.mk_const_bool(reflexive));
    }

    let av = ctx.string_const_value(a).map(str::to_owned);
    let bv = ctx.string_const_value(b).map(str::to_owned);

    match (av, bv) {
        // (a) Literal–literal fold: Rust &str order == code-point order.
        (Some(x), Some(y)) => {
            let v = if reflexive { x <= y } else { x < y };
            Some(ctx.mk_const_bool(v))
        }
        // (b) Empty-string boundary, symbolic right side:
        //     ("" <= s) -> true ; ("" < s) -> (not (= s "")).
        (Some(x), None) if x.is_empty() => {
            if reflexive {
                Some(ctx.mk_const_bool(true))
            } else {
                let empty = ctx.mk_string_const("");
                let eq = ctx.mk_eq(b, empty).expect("s = \"\"");
                Some(
                    ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq])
                        .expect("not (s = \"\")"),
                )
            }
        }
        // (b) Empty-string boundary, symbolic left side:
        //     (s <= "") -> (= s "") ; (s < "") -> false.
        (None, Some(y)) if y.is_empty() => {
            if reflexive {
                let empty = ctx.mk_string_const("");
                Some(ctx.mk_eq(a, empty).expect("s = \"\""))
            } else {
                Some(ctx.mk_const_bool(false))
            }
        }
        _ => None,
    }
}

/// Presence fence: `true` iff any `str.<`/`str.<=` application survives the
/// rewrite (a genuinely symbolic comparison outside the decided fragment).
/// Mirrors `code_conv::has_unreduced_code_conv`.
pub fn has_unreduced_str_order(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn order(ctx: &mut Context, op: BuiltinOp, a: TermId, b: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(op), &[a, b]).unwrap()
    }

    #[test]
    fn folds_literal_literal_both_ops() {
        let mut ctx = Context::new();
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let t = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        // "a" < "b" -> true ; "b" < "a" -> false ; "a" <= "a" -> true.
        let lt = order(&mut ctx, BuiltinOp::StrLt, a, b);
        let gt = order(&mut ctx, BuiltinOp::StrLt, b, a);
        let le = order(&mut ctx, BuiltinOp::StrLeq, a, a);
        let out = rewrite_str_order(&mut ctx, &[lt, gt, le]);
        assert_eq!(out, vec![t, f, t]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn empty_boundaries_rewrite() {
        let mut ctx = Context::new();
        let empty = ctx.mk_string_const("");
        let s = str_var(&mut ctx, "s");
        let t = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        // "" <= s -> true ; s < "" -> false.
        let le = order(&mut ctx, BuiltinOp::StrLeq, empty, s);
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, empty);
        // s <= "" -> (= s "") ; "" < s -> (not (= s "")).
        let le2 = order(&mut ctx, BuiltinOp::StrLeq, s, empty);
        let lt2 = order(&mut ctx, BuiltinOp::StrLt, empty, s);
        let out = rewrite_str_order(&mut ctx, &[le, lt, le2, lt2]);
        assert_eq!(out[0], t);
        assert_eq!(out[1], f);
        let eq = ctx.mk_eq(s, empty).unwrap();
        let neq = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq]).unwrap();
        assert_eq!(out[2], eq);
        assert_eq!(out[3], neq);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn reflexivity_decides() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let t = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        let le = order(&mut ctx, BuiltinOp::StrLeq, s, s);
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, s);
        let out = rewrite_str_order(&mut ctx, &[le, lt]);
        assert_eq!(out, vec![t, f]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn symbolic_pair_survives_to_fence() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let u = str_var(&mut ctx, "u");
        // s < u over two distinct free vars: no arm fires -> survives -> fenced.
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, u);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        assert_eq!(out, vec![lt]);
        assert!(has_unreduced_str_order(&ctx, &out));
    }
}
```

- [ ] **Step 2: Declare the module**

In `crates/shinri-str/src/lib.rs`, add alongside the other `pub mod` declarations (e.g. after `pub mod normalize;`):

```rust
pub mod order;
```

- [ ] **Step 3: Run tests to verify they fail, then pass**

Run: `cargo test -p shinri-str order::tests`
Expected: after Step 1–2 compile, all four tests PASS. (They are written against the final implementation, which is in the same file — so this is the go/no-go for the module.) If `declare_fun` / `mk_app(Op::Uninterpreted(..))` signatures differ from the ones copied from `predicates.rs`'s test helpers, align them with `predicates.rs:266-274`.

- [ ] **Step 4: Format and commit**

```bash
cargo fmt
git add crates/shinri-str/src/order.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): str.< / str.<= equivalence rewrite + presence fence (slice 23)"
```

---

### Task 3: Wire into the solver pipeline + e2e pins

Run the pass in the string path and pin one query per route end-to-end. Deliverable: `str.<`/`str.<=` decided/fenced through the real solver.

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs:474` (insert the pass + fence after the `code_conv` block, before the regex block)
- Test: `crates/shinri-solver/tests/qfs_differential.rs` (new `#[test]` targeted pins, near the other `targeted_*` tests around line 2341)

**Interfaces:**
- Consumes: `shinri_str::order::rewrite_str_order`, `shinri_str::order::has_unreduced_str_order` (Task 2); the `expect(src, Verdict)` and `shinri_lines(src)` test helpers already in `qfs_differential.rs`.

- [ ] **Step 1: Write the failing e2e pins**

Add near the other `targeted_*` tests in `crates/shinri-solver/tests/qfs_differential.rs`:

```rust
#[test]
fn targeted_str_order_literal_folds() {
    // Ground comparisons decide by fold.
    expect("(set-logic QF_S)(assert (str.< \"a\" \"b\"))(check-sat)", Verdict::Sat);
    expect("(set-logic QF_S)(assert (str.< \"b\" \"a\"))(check-sat)", Verdict::Unsat);
    expect("(set-logic QF_S)(assert (str.<= \"a\" \"a\"))(check-sat)", Verdict::Sat);
}

#[test]
fn targeted_str_order_empty_boundaries_decide() {
    // "" <= s is valid; s < "" is unsatisfiable.
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.<= \"\" s))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< s \"\"))(check-sat)",
        Verdict::Unsat,
    );
    // s <= "" forces s = "": consistent with s = "", contradicts s = "x".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.<= s \"\"))(assert (= s \"\"))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.<= s \"\"))(assert (= s \"x\"))(check-sat)",
        Verdict::Unsat,
    );
    // "" < s forces s != "": contradicts s = "".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.< \"\" s))(assert (= s \"\"))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_str_order_reflexivity_decides() {
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< s s))(check-sat)",
        Verdict::Unsat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.<= s s))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_str_order_symbolic_pair_known_gap() {
    // KNOWN GAP (slice 23 §4): general symbolic lexicographic comparison over two
    // free vars is NOT decided — it needs the existential first-differing-position
    // split (banked). shinri returns sound Unknown; z3 answers Sat. When the future
    // symbolic-decision slice lands, this pin flips to Sat.
    expect(
        "(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
         (assert (str.< s u))(check-sat)",
        Verdict::Unknown,
    );
}
```

- [ ] **Step 2: Run the pins to verify they fail**

Run: `cargo test -p shinri-solver --test qfs_differential targeted_str_order_`
Expected: FAIL — the decided pins currently return `Unknown` (the pass is not wired in, so `str.<`/`str.<=` reach the word-eq path undecided). The `known_gap` pin may pass vacuously; that is fine.

- [ ] **Step 3: Wire the pass into the pipeline**

In `crates/shinri-solver/src/lib.rs`, immediately after the `code_conv` fence block (after line 474, the `}` closing the `has_unreduced_code_conv` check) and before the `// ── Slices 19–21` comment, insert:

```rust
            // ── Slice 23: str.< / str.<= lexicographic ordering ──────────────
            // A SINGLE exact rewrite pass — every rule is a full equivalence
            // (literal folds, empty-string boundary idioms, reflexivity). Any
            // SURVIVING application (general symbolic comparison — needs the
            // existential first-differing-position split, banked) fences to
            // sound Unknown.
            assertions = shinri_str::order::rewrite_str_order(&mut self.ctx, &assertions);
            if shinri_str::order::has_unreduced_str_order(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

- [ ] **Step 4: Run the pins to verify they pass**

Run: `cargo test -p shinri-solver --test qfs_differential targeted_str_order_`
Expected: PASS — all four tests green.

- [ ] **Step 5: Run the broader string suite for regressions**

Run: `cargo test -p shinri-solver --test qfs_differential targeted_`
Expected: PASS — no existing `targeted_*` pin moves (this slice touches no existing path).

- [ ] **Step 6: Format and commit**

```bash
cargo fmt
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "feat(str): wire str.< / str.<= into the string pipeline + e2e pins (slice 23)"
```

---

### Task 4: Differential oracle family

Add a random-conjunction family checked against z3, per house cadence. Deliverable: `qfs_str_order_matches_z3` with 0 disagreements and tolerated unknowns.

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (add a `finish_str_order` generator method on `Gen`, a `gen_str_order_body` free fn, seed/iter consts, and the family `#[test]`)

**Interfaces:**
- Consumes: existing `Gen` (`new`/`var`/`lit`/`rng.below`), `Lcg`, `Verdict`, `shinri_lines_counting_bailouts`, `z3_verdict`, `ALPHABET`, `N_VARS`.
- Produces: the family test — no downstream consumers.

- [ ] **Step 1: Add the generator method**

Inside `impl Gen` in `crates/shinri-solver/tests/qfs_differential.rs`, add:

```rust
    /// A conjunction of 1–3 `str.<` / `str.<=` atoms over the declared string
    /// vars and small ASCII literals, plus the empty literal. Biased so decided
    /// idioms (empty-boundary, literal–literal) and fenced free-var comparisons
    /// both occur. Some atoms are negated. ASCII-only (z3-CLI byte-parse safety).
    fn finish_str_order(mut self) -> String {
        let n_atoms = 1 + self.rng.below(3); // 1..=3
        for _ in 0..n_atoms {
            let op = if self.rng.below(2) == 0 { "str.<" } else { "str.<=" };
            // Each side is independently: a var, a small literal, or "".
            let side = |g: &mut Gen| -> String {
                match g.rng.below(3) {
                    0 => g.var(),
                    1 => g.lit(),
                    _ => "\"\"".to_string(),
                }
            };
            let l = side(&mut self);
            let r = side(&mut self);
            let atom = format!("({op} {l} {r})");
            let atom = if self.rng.below(4) == 0 {
                format!("(not {atom})")
            } else {
                atom
            };
            self.body.push_str(&format!("(assert {atom})\n"));
        }
        self.body
    }
```

- [ ] **Step 2: Add the free fn, consts, and the family test**

Add near the other `gen_*_body` fns and family tests:

```rust
fn gen_str_order_body(seed: u64) -> String {
    Gen::new(seed).finish_str_order()
}

const SO_SEED: u64 = 0x53_00_0000_0003;
const SO_N_ITERS: usize = 200;
const SO_MAX_GUARD_BAILOUTS: usize = SO_N_ITERS / 10;

#[test]
fn qfs_str_order_matches_z3() {
    let mut rng = Lcg(SO_SEED);
    let (mut n_sat, mut n_unsat, mut n_shinri_unknown, mut n_z3_unknown, mut n_guard_bailouts) =
        (0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..SO_N_ITERS {
        let seed = rng.next();
        let body = gen_str_order_body(seed);

        let (lines, bailouts) = shinri_lines_counting_bailouts(&format!("{body}(check-sat)\n"));
        if bailouts > 0 {
            n_guard_bailouts += 1;
            continue;
        }
        let ours = match lines.first().map(String::as_str) {
            Some("sat") => Verdict::Sat,
            Some("unsat") => Verdict::Unsat,
            _ => Verdict::Unknown,
        };
        if ours == Verdict::Unknown {
            n_shinri_unknown += 1;
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3_unknown += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S STR_ORDER SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{body}(check-sat)"
        );
        match ours {
            Verdict::Sat => n_sat += 1,
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    println!(
        "qfs_str_order_matches_z3: {SO_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_shinri_unknown} shinri-unknown (tolerated) / {n_z3_unknown} z3-unknown / \
         {n_guard_bailouts} guard-bailout (tolerated); 0 disagreements"
    );
    assert!(n_sat > 0, "str-order family produced zero SAT instances");
    assert!(n_unsat > 0, "str-order family produced zero UNSAT instances");
    assert!(
        n_guard_bailouts <= SO_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailouts} exceed bound {SO_MAX_GUARD_BAILOUTS}"
    );
}
```

- [ ] **Step 3: Run the family**

Run: `cargo test -p shinri-solver --test qfs_differential qfs_str_order_matches_z3 -- --nocapture`
Expected: PASS — printed tally shows `0 disagreements`, `n_sat > 0`, `n_unsat > 0`, and a tolerated slice of shinri-unknowns (the fenced free-var comparisons). Requires the `z3` CLI on PATH. If `n_sat` or `n_unsat` is 0, the generator bias needs adjusting (widen the literal/empty mix), not the solver.

- [ ] **Step 4: Confirm the existing families are unchanged**

Run: `cargo test -p shinri-solver --test qfs_differential qfs_to_code_range_matches_z3 qfs_regex_ground_matches_z3 -- --nocapture`
Expected: PASS — tallies bit-for-bit identical to their slice-22 close values (this slice adds a new operator and touches no existing path). Any movement is a finding to adjudicate.

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_str_order_matches_z3 differential oracle family (slice 23)"
```

---

## Final verification (before closeout)

- [ ] Run `cargo fmt --check` (CI gate).
- [ ] Run `cargo clippy --workspace --all-targets -- -D warnings` and fix any lints (CI gate).
- [ ] Run `cargo test -p shinri-core -p shinri-parser -p shinri-str` (fast crates).
- [ ] Run the string oracle families: `cargo test -p shinri-solver --test qfs_differential -- --nocapture`.
- [ ] SDD pre-flight (per `commit-plan-docs-with-spec`): confirm BOTH `docs/superpowers/specs/2026-07-15-shinri-slice23-str-order-design.md` and this plan file are tracked in git.
