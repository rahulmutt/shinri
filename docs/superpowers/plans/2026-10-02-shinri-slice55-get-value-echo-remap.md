# Slice 55 — `get-value` echo, purified-term remap, symbol quoting — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `get-value` echoes each query term as valid SMT-LIB (no `tN` TermId
indices), terms containing a slice-54 purified Bool argument get their real
value instead of `?`, and `get-value` / `get-model` `|…|`-quote symbols that
need it. No verdict changes.

**Architecture:** The parser's complete term printer moves to
`shinri_core::smtlib_print`, where it gains a node budget and symbol/sort
quoting; the solver's partial `tseitin::display_term` is deleted. `WordNorm`
keeps a solver-lifetime original→rewritten map (replacing `orig_ite`), the
main and ABV paths stash every internal symbol's value whole, and
`format_value` resolves a query term through that map read-only.

**Tech Stack:** Rust 1.99 (pinned in `mise.toml`), cargo-nextest 0.9.140,
z3 (oracle, from mise), `shinri-bench`.

**Spec:** `docs/superpowers/specs/2026-10-02-shinri-slice55-get-value-echo-remap-design.md`

## Global Constraints

- No verdict change: no edit to any solving stage, fence, theory, Tseitin
  encoding or `lower`; nothing may mint a term (`mk_app`, `declare_fun`,
  `mk_*const`) at `get-value` / `get-model` time.
- Output budget: one `DISPLAY_TERM_BUDGET` (100 000 node visits) per
  `get-value` response, shared across all its labels (slice 43 T6).
- Budget/depth exhaustion prints the symbol `|<truncated>|` — never a
  TermId index.
- `?` stays the fallback for a term no value channel holds.
- Pure-Rust mandate: no new dependency (`deny.toml`).
- nextest filters use `-E 'test(<name>)'` / `-E 'binary(<name>)'`; confirm a
  non-zero discovered count on every run.
- Oracle tests run only with `--features oracle`; a run without it reports
  0 tests and is not coverage.
- Before every commit: `cargo fmt --all` and
  `cargo clippy --workspace --all-targets -- -D warnings` clean.
- Work on branch `slice55-get-value-echo-remap`; PR to `main`, merge commit
  when CI is green, delete the branch (remote and local).

## Review Focus

1. **Datatype tester echo.** `((_ is mk) v)` is stored as the minted
   `is-mk` symbol, so it echoes `(is-mk v)`. That is the legacy form z3 and
   cvc5 accept. Expected: the echo re-parses in shinri and in z3 (pinned in
   Task 2 probe `tester_echo_reparses`, and by the DT oracle family in
   Task 4).
2. **Nullary builtins.** `re.none` / `re.all` / `re.allchar` are
   zero-argument builtin applications; the old printer printed **nothing**
   for them. Expected: their names (Task 1 test
   `prints_nullary_builtins`).
3. **Stale remap after `push`/`pop`.** `orig_rewrite` is solver-lifetime.
   A query term rewritten in an earlier `check-sat` but absent from the
   current assertion set must print `?`, never the earlier value (Task 3
   probe `stale_rewrite_after_pop_prints_unknown_value`).
4. **Rewrites that are not purification.** n-ary `=` expands to an `and`;
   the remap must answer the original term with a correct value or `?`,
   never a wrong one (Task 3 probe `nary_eq_query_is_true_or_unknown`).
5. **Quoted function symbol in an echo.** `(|f g| x)` must echo with the
   function symbol quoted (Task 2 probe `quoted_uf_application_echo`).

## Facts established while planning (do not re-derive)

- The parser reads `(- 3)` as `Neg(3)`, never as a negative constant
  (`crates/shinri-parser/src/parser.rs:894-898`), and `Neg` already prints
  `(- 3)`. **The spec's §3.1 "negative numerals" change is therefore not
  needed and is dropped**; record this in the spec's measured outcomes
  (Task 5).
- The bench base is the existing `bench/results/slice54/results.jsonl`
  (binary built from `6212fa5`; `git diff --stat 6212fa5 a0d0fe9 -- crates`
  touches only `tests/bool_arg_oracle.rs` and `tests/slice54_probes.rs`).
  No base re-run.
- Consumer audit (done): no existing test breaks. `ite_e2e.rs:195`
  (`contains('2')`) and `fp_e2e.rs:1247` (`contains("RTZ")`) become
  vacuous once the label is the real term (the label contains the expected
  value) — Task 2 tightens them. `qfufbv_e2e.rs:866` pins `(((p x) ?))`;
  `(p x)` has no rewrite, so it must stay `?` (a regression there means the
  remap over-reaches). The `t<digits>` filter in
  `qfs_differential.rs:1330-1334` becomes dead but harmless; leave it.
- `Model::get(&self, TermId) -> Option<&ModelVal>`
  (`crates/shinri-theory/src/model.rs:21`);
  `shinri_theory::model::format_modelval(&ModelVal) -> String` (`:118`).
- `ite_map()` values already contain every `ite!` symbol, so the ABV
  harvest at `lib.rs:947-953` does not need `orig_ite_map()`.

---

### Task 1: `shinri_core::smtlib_print` — budgeted, quoting printer

**Files:**
- Create: `crates/shinri-core/src/smtlib_print.rs` (moved from
  `crates/shinri-parser/src/print.rs`, then extended)
- Delete: `crates/shinri-parser/src/print.rs`
- Modify: `crates/shinri-core/src/lib.rs` (add `pub mod smtlib_print;`)
- Modify: `crates/shinri-parser/src/lib.rs` (`mod print;` →
  re-export)
- Test: unit tests in `smtlib_print.rs`;
  `crates/shinri-parser/tests/roundtrip.rs`

**Interfaces:**
- Produces (all in `shinri_core::smtlib_print`):
  - `pub const DISPLAY_TERM_BUDGET: usize = 100_000;`
  - `pub fn print_term(ctx: &Context, t: TermId) -> String`
  - `pub fn print_term_budgeted(ctx: &Context, t: TermId, budget: &mut usize) -> String`
  - `pub fn quote_symbol(name: &str) -> std::borrow::Cow<'_, str>`
  - `pub fn print_sort(ctx: &Context, s: SortId) -> String`
- `shinri_parser::print_term` keeps its path (re-export).

- [ ] **Step 1: Branch**

```bash
git switch -c slice55-get-value-echo-remap
```

- [ ] **Step 2: Move the file and re-export (pure move, no behaviour change)**

```bash
git mv crates/shinri-parser/src/print.rs crates/shinri-core/src/smtlib_print.rs
```

In `crates/shinri-core/src/smtlib_print.rs`, change the first line
`use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermId, TermNode};` to
`use crate::{BuiltinOp, ConstVal, Context, Op, SortId, SortNode, TermId, TermNode};`,
replace every remaining `shinri_core::` path in the file with `crate::`
(`crate::smtlib_string::encode_literal`, `crate::RoundingMode::…`, and in
the test module `crate::Context`, `crate::Rational`, …). `shinri_num::` paths
stay (core depends on `shinri-num`). Add a module doc comment at the top:

```rust
//! SMT-LIB 2.6 term and sort printing (slice 55; moved from
//! `shinri-parser`). One printer for the parser's round-trip tests and for
//! every solver output path (`get-value` echo, `get-model`), so they agree
//! on one rule set — the same reason `smtlib_string` lives here.
```

In `crates/shinri-core/src/lib.rs` add after `pub mod smtlib_string;`:

```rust
pub mod smtlib_print;
```

In `crates/shinri-parser/src/lib.rs` delete `mod print;` and replace
`pub use print::print_term;` with:

```rust
pub use shinri_core::smtlib_print::print_term;
```

Run: `cargo nextest run -p shinri-core -p shinri-parser`
Expected: PASS, same counts as before the move (the `print` unit tests now
run under `shinri-core`).

- [ ] **Step 3: Commit the move**

```bash
cargo fmt --all
git add -A crates/shinri-core crates/shinri-parser
git commit -m "refactor(core): slice55 - move term printer to shinri_core::smtlib_print"
```

- [ ] **Step 4: Write the failing unit tests**

Append to the `#[cfg(test)] mod tests` in `smtlib_print.rs`:

```rust
    fn nullary(ctx: &mut Context, name: &str, sort: SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn quote_symbol_table() {
        for simple in ["x", "a.b", "<=>", "is-mk", "bool!0", "ite!3", "@x", "~q"] {
            assert_eq!(quote_symbol(simple), simple, "{simple}");
        }
        for (raw, quoted) in [
            ("a#b", "|a#b|"),
            ("my sort", "|my sort|"),
            ("0x", "|0x|"),
            ("", "||"),
            ("__ESBMC_rounding_mode&0#10", "|__ESBMC_rounding_mode&0#10|"),
            ("let", "|let|"),
            ("par", "|par|"),
            ("assert", "|assert|"),
            ("check-sat", "|check-sat|"),
            ("_", "|_|"),
            ("!", "|!|"),
        ] {
            assert_eq!(quote_symbol(raw), quoted, "{raw}");
        }
    }

    #[test]
    fn prints_quoted_symbols_in_terms() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let x = nullary(&mut ctx, "a#b", int);
        let g = ctx.declare_fun("f g", &[int], int);
        let app = ctx.mk_app(Op::Uninterpreted(g), &[x]).unwrap();
        assert_eq!(print_term(&ctx, app), "(|f g| |a#b|)");
    }

    #[test]
    fn prints_builtin_application() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let a = nullary(&mut ctx, "a", int);
        let one = ctx.mk_numeral(crate::Rational::from_int(1i128.into()), int);
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[a, one]).unwrap();
        assert_eq!(print_term(&ctx, sum), "(+ a 1)");
    }

    #[test]
    fn prints_nullary_builtins() {
        let mut ctx = Context::new();
        for (op, name) in [
            (BuiltinOp::ReNone, "re.none"),
            (BuiltinOp::ReAll, "re.all"),
            (BuiltinOp::ReAllChar, "re.allchar"),
        ] {
            let t = ctx.mk_app(Op::Builtin(op), &[]).unwrap();
            assert_eq!(print_term(&ctx, t), name);
        }
    }

    #[test]
    fn print_sort_quotes_user_sorts() {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("my sort");
        let int = ctx.int_sort();
        let arr = ctx.array_sort(int, u);
        assert_eq!(print_sort(&ctx, u), "|my sort|");
        assert_eq!(print_sort(&ctx, arr), "(Array Int |my sort|)");
        assert_eq!(print_sort(&ctx, int), "Int");
        let bv = ctx.bv_sort(8);
        assert_eq!(print_sort(&ctx, bv), "(_ BitVec 8)");
    }

    #[test]
    fn budget_truncates_with_placeholder_and_bounds_work() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let g = ctx.declare_fun("g", &[int, int], int);
        let mut t = ctx.mk_numeral(crate::Rational::from_int(0i128.into()), int);
        for _ in 0..30 {
            t = ctx.mk_app(Op::Uninterpreted(g), &[t, t]).unwrap();
        }
        let mut budget = 1_000;
        let s = print_term_budgeted(&ctx, t, &mut budget);
        assert_eq!(budget, 0);
        assert!(s.contains("|<truncated>|"), "{s}");
        // ≤ 1 000 visited nodes (`(g ` … `)`) plus ≤ 1 001 placeholders
        // (13 bytes each) — well under 32 bytes per budget unit.
        assert!(s.len() < 1_000 * 32, "output not bounded: {} bytes", s.len());
        assert!(!s.split(|c: char| c == ' ' || c == '(' || c == ')')
            .any(|tok| tok.len() > 1 && tok.starts_with('t')
                && tok[1..].chars().all(|c| c.is_ascii_digit())),
            "TermId index leaked: {s}");
    }

    #[test]
    fn unbounded_print_never_truncates() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let a = nullary(&mut ctx, "a", int);
        assert_eq!(print_term(&ctx, a), "a");
    }
```

If `Context::declare_sort`, `array_sort` or `bv_sort` are named differently,
use the existing constructor (`grep -n "pub fn .*sort(" crates/shinri-core/src/context.rs`)
— the assertions stay as written.

- [ ] **Step 5: Run to verify failure**

Run: `cargo nextest run -p shinri-core -E 'test(quote_symbol_table) | test(prints_quoted_symbols_in_terms) | test(prints_builtin_application) | test(prints_nullary_builtins) | test(print_sort_quotes_user_sorts) | test(budget_truncates_with_placeholder_and_bounds_work) | test(unbounded_print_never_truncates)'`
Expected: compile errors (`quote_symbol`, `print_sort`,
`print_term_budgeted` not found). Discovered count once it compiles: 7.

- [ ] **Step 6: Implement**

At the top of `smtlib_print.rs` (after the `use`), replace `print_term` and
the head of `write_term` with:

```rust
/// Node-visit budget for one `get-value` response (slice 43 T6: the labels
/// can all name the same `let`-shared term, so the budget is shared across
/// a response, not per label). Moved from `shinri-solver/src/tseitin.rs`.
pub const DISPLAY_TERM_BUDGET: usize = 100_000;

/// Printed in place of a subterm once the budget or the depth backstop is
/// exhausted: a parseable symbol that is visibly not a real term (never a
/// TermId index, which is what slice 55 removed).
const TRUNCATED: &str = "|<truncated>|";

/// Term depth is attacker-controlled (threat model); a mechanical backstop,
/// mirroring `render_value`'s cap. The operative output bound is the budget.
const MAX_DEPTH: u32 = 10_000;

/// SMT-LIB 2.6 reserved words (§3.1), including every command name.
const RESERVED: &[&str] = &[
    "!", "_", "as", "BINARY", "DECIMAL", "exists", "HEXADECIMAL", "forall", "let", "match",
    "NUMERAL", "par", "STRING", "assert", "check-sat", "check-sat-assuming", "declare-const",
    "declare-datatype", "declare-datatypes", "declare-fun", "declare-sort", "define-fun",
    "define-fun-rec", "define-funs-rec", "define-sort", "echo", "exit", "get-assertions",
    "get-assignment", "get-info", "get-model", "get-option", "get-proof",
    "get-unsat-assumptions", "get-unsat-core", "get-value", "pop", "push", "reset",
    "reset-assertions", "set-info", "set-logic", "set-option",
];

fn is_simple_symbol(name: &str) -> bool {
    const PUNCT: &str = "~!@$%^&*_+=<>.?/-";
    let mut cs = name.chars();
    let Some(first) = cs.next() else { return false };
    (first.is_ascii_alphabetic() || PUNCT.contains(first))
        && cs.all(|c| c.is_ascii_alphanumeric() || PUNCT.contains(c))
}

/// `name` bare if it is a simple SMT-LIB symbol (the lexer's rule) and not
/// reserved, else `|name|`. A name containing `|` or `\` cannot be quoted;
/// the lexer cannot produce one and internal names are simple.
pub fn quote_symbol(name: &str) -> Cow<'_, str> {
    if is_simple_symbol(name) && !RESERVED.contains(&name) {
        Cow::Borrowed(name)
    } else {
        debug_assert!(
            !name.contains(['|', '\\']),
            "unquotable symbol name: {name:?}"
        );
        Cow::Owned(format!("|{name}|"))
    }
}

/// A sort's SMT-LIB name with user sort / datatype names quoted.
pub fn print_sort(ctx: &Context, s: SortId) -> String {
    match ctx.sort_node(s) {
        SortNode::Uninterpreted(sym) | SortNode::Datatype(sym) => {
            quote_symbol(ctx.symbol_name(*sym)).into_owned()
        }
        SortNode::Array(i, e) => {
            format!("(Array {} {})", print_sort(ctx, *i), print_sort(ctx, *e))
        }
        _ => ctx.sort_name(s),
    }
}

/// Print a term as an s-expression that re-parses to the same id. Unbounded:
/// for the parser and tests. Solver output paths use `print_term_budgeted`.
pub fn print_term(ctx: &Context, t: TermId) -> String {
    let mut budget = usize::MAX;
    print_term_budgeted(ctx, t, &mut budget)
}

/// `print_term` with a node-visit budget shared by the caller across a whole
/// response. Each visit costs one unit, checked before recursing.
pub fn print_term_budgeted(ctx: &Context, t: TermId, budget: &mut usize) -> String {
    let mut s = String::new();
    write_term(ctx, t, 0, budget, &mut s);
    s
}

fn write_term(ctx: &Context, t: TermId, depth: u32, budget: &mut usize, out: &mut String) {
    if depth > MAX_DEPTH || *budget == 0 {
        out.push_str(TRUNCATED);
        return;
    }
    *budget -= 1;
```

Add `use std::borrow::Cow;` to the imports. Keep the existing
`match ctx.term_node(t).clone() { … }` body, with these edits inside it:

- The nullary `App` arm becomes:

```rust
            if children.is_empty() {
                match op {
                    Op::Uninterpreted(sym) => out.push_str(&quote_symbol(ctx.symbol_name(sym))),
                    Op::Builtin(b) => out.push_str(&builtin_name(b)),
                }
                return;
            }
```

- The applied-symbol head becomes
  `Op::Uninterpreted(sym) => out.push_str(&quote_symbol(ctx.symbol_name(sym))),`
- The child recursion becomes `write_term(ctx, c, depth + 1, budget, out);`

- [ ] **Step 7: Extend the round-trip tests**

Append to `crates/shinri-parser/tests/roundtrip.rs`:

```rust
#[test]
fn roundtrips_quoted_symbols_and_nullary_builtins() {
    let decl = |ctx: &mut Context, p: &mut Parser| {
        let mut d = Parser::new(
            "(declare-sort |my sort| 0)(declare-fun |a#b| () |my sort|)\
             (declare-fun |let| () Int)(declare-fun |f g| (Int) Int)\
             (declare-fun s () String)",
        );
        while let Some(r) = d.next_command(ctx) {
            r.expect("decl");
        }
        let _ = p;
    };
    roundtrip("|a#b|", decl);
    roundtrip("(|f g| |let|)", decl);
    roundtrip("(+ (|f g| 1) (- 3))", decl);
    roundtrip("(str.in_re s re.none)", decl);
    roundtrip("(str.in_re s (re.++ re.allchar re.all))", decl);
}
```

If `roundtrip`'s `seed` closure cannot declare through a second parser in
this crate's API, declare via `ctx.declare_fun` / the sort constructor
directly; what must be pinned is that each printed form re-parses to the
same TermId.

- [ ] **Step 8: Run to verify pass**

Run: `cargo nextest run -p shinri-core -p shinri-parser`
Expected: PASS; the 7 new core tests and the new round-trip test discovered
and passing.

- [ ] **Step 9: Commit**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add -A crates/shinri-core crates/shinri-parser
git commit -m "feat(core): slice55 - budgeted printer with symbol and sort quoting"
```

---

### Task 2: Output call sites use the new printer; delete `display_term`

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (`Command::GetValue` arm
  ~`:453-470`; `format_model` ~`:577-583`)
- Modify: `crates/shinri-solver/src/tseitin.rs` (delete
  `DISPLAY_TERM_BUDGET` ~`:407-439` doc+const and `display_term` /
  `display_term_at_depth` ~`:453-500`)
- Modify: `crates/shinri-solver/src/lib.rs:1364-1369` (comment mentions
  `display_term`)
- Create: `crates/shinri-solver/tests/slice55_probes.rs`
- Modify: `crates/shinri-solver/tests/ite_e2e.rs:194-198`,
  `crates/shinri-solver/tests/fp_e2e.rs:1247`
- Modify: `crates/shinri-solver/tests/qfdt_model_e2e.rs:292-336` (doc
  comment names `display_term`)

**Interfaces:**
- Consumes: `shinri_core::smtlib_print::{print_term_budgeted, quote_symbol, print_sort, DISPLAY_TERM_BUDGET}` (Task 1).
- Produces: `tests/slice55_probes.rs` with helpers `run_script(&str) -> Vec<String>`
  and `assert_no_leak(&str)`, extended by Task 3.

- [ ] **Step 1: Write the failing probes**

Create `crates/shinri-solver/tests/slice55_probes.rs`:

```rust
//! Slice 55 probes (spec §6.1). `get-value` echoed builtin terms as raw
//! TermId indices (`t9`), printed `?` for every term containing a slice-54
//! purified Bool argument, and neither `get-value` nor `get-model` quoted
//! symbols that need `|…|`. Each probe pins the exact response line.
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

/// e7: no internal name and no TermId index in any response line.
fn assert_no_leak(line: &str) {
    assert!(!line.contains("bool!"), "proxy name leaked: {line}");
    assert!(!line.contains("ite!"), "ite name leaked: {line}");
    let leaked = line
        .split(|c: char| c == ' ' || c == '(' || c == ')')
        .any(|tok| tok.len() > 1 && tok.starts_with('t') && tok[1..].chars().all(|c| c.is_ascii_digit()));
    assert!(!leaked, "TermId index leaked: {line}");
}

/// Runs `src`, requires `sat` first, checks every later line for leaks,
/// and returns the lines after `sat`.
fn sat_then(src: &str) -> Vec<String> {
    let out = run_script(src);
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{src}\n{out:?}");
    for l in &out[1..] {
        assert_no_leak(l);
    }
    out[1..].to_vec()
}

// ── echo (e1, e5, Review Focus 1, 5) ───────────────────────────────────────

#[test]
fn e1_builtin_echo() {
    let out = sat_then(
        "(set-logic QF_LIA)(declare-fun a () Int)(assert (= a 0))\
         (check-sat)(get-value ((+ a 1)))",
    );
    // The value of (+ a 1) is not a registered term; `?` is the honest
    // fallback (a V2 evaluator is queued). The echo is what this pins.
    assert!(
        out[0] == "(((+ a 1) 1))" || out[0] == "(((+ a 1) ?))",
        "{out:?}"
    );
}

#[test]
fn e5_quoted_symbol_and_sort() {
    let out = sat_then(
        "(set-logic QF_UF)(declare-sort |my sort| 0)\
         (declare-fun |a#b| () |my sort|)(declare-fun c () |my sort|)\
         (assert (= |a#b| c))(check-sat)(get-value (|a#b|))(get-model)",
    );
    assert!(out[0].starts_with("((|a#b| "), "{out:?}");
    assert!(out[1].contains("(define-fun |a#b| () |my sort| "), "{out:?}");
    assert!(out[1].contains("(define-fun c () |my sort| "), "{out:?}");
}

#[test]
fn e5_get_model_quotes_esbmc_style_name() {
    let out = sat_then(
        "(set-logic QF_BV)(declare-fun |__ESBMC_rounding_mode&0#10| () (_ BitVec 8))\
         (assert (= |__ESBMC_rounding_mode&0#10| #x2a))(check-sat)(get-model)",
    );
    assert_eq!(
        out[0],
        "((define-fun |__ESBMC_rounding_mode&0#10| () (_ BitVec 8) #x2a))"
    );
}

#[test]
fn quoted_uf_application_echo() {
    let out = sat_then(
        "(set-logic QF_UFLIA)(declare-fun |f g| (Int) Int)(declare-fun x () Int)\
         (assert (= (|f g| x) 3))(check-sat)(get-value ((|f g| x)))",
    );
    assert_eq!(out[0], "(((|f g| x) 3))");
}

#[test]
fn tester_echo_reparses() {
    let out = sat_then(
        "(set-logic QF_DT)(declare-datatypes ((B 0)) (((mk (fa Bool)) (nil))))\
         (declare-fun v () B)(assert ((_ is mk) v))(check-sat)(get-value (((_ is mk) v)))",
    );
    // Stored as the minted `is-mk` tester symbol (legacy form z3/cvc5 accept).
    assert!(out[0].starts_with("(((is-mk v) "), "{out:?}");
    // The echoed label must re-parse in shinri.
    let label = "(is-mk v)";
    let re = run_script(&format!(
        "(set-logic QF_DT)(declare-datatypes ((B 0)) (((mk (fa Bool)) (nil))))\
         (declare-fun v () B)(assert {label})(check-sat)"
    ));
    assert_eq!(re, vec!["sat"], "echo did not re-parse: {re:?}");
}

#[test]
fn e6_shared_let_chain_is_bounded_and_truncated() {
    // Same shape as qfdt_model_e2e's slice-43 T6 test: a 25-level chain of
    // `let`-shared `(g x x)` nodes, 2^25 nodes when unshared.
    let lets: String = (1..=25)
        .map(|i| format!("(let ((x{i} (g x{} x{}))) ", i - 1, i - 1))
        .collect();
    let query = format!("(let ((x0 0)) {lets}x25{})", ")".repeat(26));
    let src = format!(
        "(set-logic QF_UFLIA)(declare-fun g (Int Int) Int)(check-sat)(get-value ({query}))"
    );
    let out = run_script(&src);
    assert_eq!(out[0], "sat");
    assert!(out[1].len() < 2_000_000, "not bounded: {} bytes", out[1].len());
    assert!(out[1].contains("|<truncated>|"), "no placeholder");
    assert_no_leak(&out[1]);
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice55_probes)'`
Expected: 6 discovered; `e1_builtin_echo` fails (`t…` label), the two
`e5_*` and `quoted_uf_application_echo` fail (unquoted names),
`tester_echo_reparses` passes or fails on the label only,
`e6_*` fails (`|<truncated>|` absent, `t…` present).

- [ ] **Step 3: Switch `get-value` to the new printer**

In `lib.rs`, in the `Command::GetValue(ts)` arm, replace

```rust
                let mut budget = crate::tseitin::DISPLAY_TERM_BUDGET;
```
with
```rust
                let mut budget = shinri_core::smtlib_print::DISPLAY_TERM_BUDGET;
```
and
```rust
                    let name = crate::tseitin::display_term(&self.ctx, *t, &mut budget);
```
with
```rust
                    let name = shinri_core::smtlib_print::print_term_budgeted(
                        &self.ctx,
                        *t,
                        &mut budget,
                    );
```

- [ ] **Step 4: Quote names in `get-model`**

In `format_model`, replace the `out.push_str(&format!("(define-fun {} () {} {})", d.name, self.ctx.sort_name(d.result), val));`
call with:

```rust
            out.push_str(&format!(
                "(define-fun {} () {} {})",
                shinri_core::smtlib_print::quote_symbol(&d.name),
                shinri_core::smtlib_print::print_sort(&self.ctx, d.result),
                val
            ));
```

- [ ] **Step 5: Delete `display_term`**

In `tseitin.rs`, delete the `DISPLAY_TERM_BUDGET` doc comment and constant
and both `display_term` functions with their doc comments (the region
between the end of the preceding item and `#[cfg(test)] mod tests`).
Move the substance of the deleted `DISPLAY_TERM_BUDGET` doc comment (the
measurement and the once-per-response rule) onto the constant in
`smtlib_print.rs` if Task 1's shorter doc dropped any of it. In `lib.rs`
around `:1364-1369`, change the comment's "`display_term` index out of
bounds" to "the `get-value` printer index out of bounds". In
`qfdt_model_e2e.rs:292-300`, change "`display_term` has no memoization" to
"the `get-value` printer (`smtlib_print`) has no memoization".

Run: `grep -rn "display_term" crates` — Expected: no output.

- [ ] **Step 6: Tighten the two now-vacuous checks**

`ite_e2e.rs` — replace the `values[0].contains('2')` assertion with:

```rust
    assert_eq!(values[0], "(((ite b 2 0) 2))", "expected branch value 2");
```

`fp_e2e.rs:1247` — replace `assert!(values[0].contains("RTZ"), …)` with:

```rust
    assert_eq!(values[0], "(((ite p RTZ RNE) RTZ))", "expected RTZ");
```

- [ ] **Step 7: Run to verify pass**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice55_probes) | binary(ite_e2e) | binary(fp_e2e) | binary(qfdt_model_e2e) | binary(qfufbv_e2e)'`
Expected: all PASS, non-zero count per binary. `qfufbv_e2e`'s
`(((p x) ?))` pin still passes.

- [ ] **Step 8: Full solver suite, then commit**

Run: `cargo nextest run -p shinri-solver`
Expected: PASS (only pre-existing `#[ignore]`d tests skipped).

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add -A crates/shinri-solver
git commit -m "fix(solver): slice55 - get-value echoes real SMT-LIB terms, quote model names"
```

---

### Task 3: Original→rewritten remap for purified and rewritten terms

**Files:**
- Modify: `crates/shinri-solver/src/word_norm.rs` (field `orig_ite` →
  `orig_rewrite`; accessors; insert in `walk`; unit test)
- Modify: `crates/shinri-solver/src/lib.rs` (field
  `eliminated_ite_vals` → `internal_vals`, decl ~`:92-93`, init ~`:245`,
  clears ~`:386`, `:476`, `:762`; ABV harvest+remap ~`:945-974`; main-path
  remap ~`:1444-1458`; `format_value` ~`:520-528`; `pop` comment
  ~`:370-385`; `format_model` comment naming `eliminated_ite_vals`)
- Modify: `crates/shinri-solver/tests/slice55_probes.rs` (append)

**Interfaces:**
- Consumes: `run_script`, `sat_then`, `assert_no_leak` from Task 2.
- Produces (in `WordNorm`):
  - `pub(crate) fn orig_rewrite_map(&self) -> &FxHashMap<TermId, TermId>`
  - `pub(crate) fn bool_arg_map(&self) -> &FxHashMap<TermId, TermId>`
  - `orig_ite_map()` is removed.

- [ ] **Step 1: Verify the proxy-value fact (spec §3.4, no code kept)**

Temporarily add in the main path of `check_sat`, just after the RM
extraction loop and before the `// Answer get-value on eliminated ites`
block:

```rust
                eprintln!(
                    "SLICE55 internal_vals: {:?}",
                    internal_vals
                        .iter()
                        .map(|(k, v)| (
                            shinri_core::smtlib_print::print_term(&self.ctx, *k),
                            shinri_theory::model::format_modelval(v)
                        ))
                        .collect::<Vec<_>>()
                );
```

Run:

```bash
cat > /tmp/claude-1000/-workspace/0c49f566-bc58-4c66-8105-5bbfd11efbf3/scratchpad/r3.smt2 <<'EOF'
(set-logic QF_UFLIA)(declare-fun x () Int)(declare-fun P (Bool) Bool)
(assert (P (= x 1)))(assert (not (P true)))(assert (= x 2))
(check-sat)(get-value ((P (= x 1)) (= x 1) (P false)))
EOF
cargo run -q -p shinri-cli -- /tmp/claude-1000/-workspace/0c49f566-bc58-4c66-8105-5bbfd11efbf3/scratchpad/r3.smt2
```

Record in the task report: (i) whether `bool!0` appears among
`internal_vals` keys, (ii) the value. **If it appears**, proceed. **If it
does not**, add in the main path, next to the `atom_vars` loop, a loop over
`self.word_norm.bool_arg_map().values()` that reads each proxy's SAT
literal from `atom_vars` (`(v, term)` with `term == b`) and inserts
`ModelVal::Bool(sat.value_of(v).unwrap_or(false))` into `internal_vals` —
mirroring how the `atom_vars` loop values a user Bool constant — and note
it in the report. Remove the `eprintln!` before continuing.

- [ ] **Step 2: Write the failing probes**

Append to `slice55_probes.rs`:

```rust
// ── remap (e2, e3, e4, Review Focus 3, 4) ──────────────────────────────────

const UFLIA: &str = "(set-logic QF_UFLIA)(declare-fun x () Int)(declare-fun y () Int)\
    (declare-fun c () Bool)(declare-fun P (Bool) Bool)(declare-fun f (Bool) Int)";

#[test]
fn e2_purified_uf_argument_gets_value() {
    let out = sat_then(&format!(
        "{UFLIA}(assert (= (f (= x 1)) 7))(check-sat)(get-value ((f (= x 1))))"
    ));
    assert_eq!(out[0], "(((f (= x 1)) 7))");
}

#[test]
fn e3_slice54_report_query() {
    let out = sat_then(&format!(
        "{UFLIA}(assert (P (= x 1)))(assert (not (P true)))(assert (= x 2))\
         (check-sat)(get-value ((P (= x 1)) (= x 1) (P false)))"
    ));
    // (P (= x 1)) is asserted true; (= x 1) is false since x = 2. (P false)
    // occurs in no assertion: `?` (no evaluator; V2 is queued).
    assert_eq!(out[0], "(((P (= x 1)) true) ((= x 1) false) ((P false) ?))");
}

#[test]
fn e4_ite_inside_purified_argument() {
    let out = sat_then(&format!(
        "{UFLIA}(assert (P (> (ite c x y) 0)))(assert c)(assert (= x 5))\
         (check-sat)(get-value ((P (> (ite c x y) 0)) (> (ite c x y) 0) (ite c x y)))"
    ));
    assert_eq!(
        out[0],
        "(((P (> (ite c x y) 0)) true) ((> (ite c x y) 0) true) ((ite c x y) 5))"
    );
}

#[test]
fn stale_rewrite_after_pop_prints_unknown_value() {
    let out = sat_then(&format!(
        "{UFLIA}(push 1)(assert (= (f (= x 1)) 7))(check-sat)(pop 1)\
         (assert (= x 3))(check-sat)(get-value ((f (= x 1))))"
    ));
    // out[0] is the first sat's (absent) output; the second check-sat line:
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((f (= x 1)) ?))", "stale value served: {out:?}");
}

#[test]
fn nary_eq_query_is_true_or_unknown() {
    let out = sat_then(&format!(
        "{UFLIA}(declare-fun z () Int)(assert (= x y z))(check-sat)(get-value ((= x y z)))"
    ));
    assert!(
        out[0] == "(((= x y z) true))" || out[0] == "(((= x y z) ?))",
        "wrong value for an asserted n-ary =: {out:?}"
    );
}

#[test]
fn unrewritten_bool_uf_application_unchanged() {
    // Regression guard mirroring qfufbv_e2e.rs:866: a term the walk did not
    // rewrite takes the old path; the remap must not invent a value.
    let out = sat_then(&format!(
        "{UFLIA}(assert (P c))(check-sat)(get-value ((P c)))"
    ));
    assert_eq!(out[0], "(((P c) true))");
}
```

Note on `stale_rewrite_after_pop_prints_unknown_value`: `sat_then` strips
the first `sat`; the second `check-sat`'s `sat` is `out[0]` and the
`get-value` line is `out[1]`.

- [ ] **Step 3: Run to verify failure**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice55_probes)'`
Expected: 12 discovered; `e2_*`, `e3_*`, `e4_*` fail on `?` values;
`stale_*`, `nary_*`, `unrewritten_*` may already pass (they are guards).

- [ ] **Step 4: `WordNorm`: replace `orig_ite` with `orig_rewrite`**

In `word_norm.rs`, replace the `orig_ite` field and its doc comment with:

```rust
    /// Every ORIGINAL term the walk changed → its rewritten term (slice 55;
    /// replaces slice 7's ite-only `orig_ite`). `ite_var` is keyed by the
    /// post-rewrite ite and a purified argument's parent is rebuilt, so the
    /// user's original get-value query term matches neither; this map closes
    /// that gap for every rewrite. Get-value only; never read by solving.
    orig_rewrite: FxHashMap<TermId, TermId>,
```

Replace the `orig_ite_map` accessor with:

```rust
    /// Original term → rewritten term, for get-value (slice 55).
    pub(crate) fn orig_rewrite_map(&self) -> &FxHashMap<TermId, TermId> {
        &self.orig_rewrite
    }

    /// Compound Bool argument (post-child-rewrite) → its `bool!` proxy, for
    /// get-value on the argument itself (slice 55).
    pub(crate) fn bool_arg_map(&self) -> &FxHashMap<TermId, TermId> {
        &self.bool_arg_var
    }
```

In `walk`, delete the two `// Item 4 (slice 7)` comment lines and
`self.orig_ite.insert(t, w);` from the ite arm. Find where `walk` stores
its result in `memo` (the end of the function: `memo.insert(t, result);`)
and add immediately before it:

```rust
        if result != t {
            self.orig_rewrite.insert(t, result);
        }
```

Update the module doc INVARIANTS if it names `orig_ite`
(`grep -n orig_ite crates/shinri-solver/src/word_norm.rs` must print
nothing).

Add a unit test in `word_norm.rs`'s test module:

```rust
    #[test]
    fn orig_rewrite_records_purified_parent_and_skips_unchanged_terms() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let bs = ctx.bool_sort();
        let xf = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let pf = ctx.declare_fun("P", &[bs], bs);
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int);
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, one]).unwrap();
        let p = ctx.mk_app(Op::Uninterpreted(pf), &[eq]).unwrap();
        let mut wn = WordNorm::default();
        wn.normalize(&mut ctx, &[p]);
        let r = *wn.orig_rewrite_map().get(&p).expect("parent recorded");
        assert_ne!(r, p);
        assert!(!wn.orig_rewrite_map().contains_key(&eq), "unchanged arg recorded");
        assert!(!wn.orig_rewrite_map().contains_key(&x));
        let b = *wn.bool_arg_map().get(&eq).expect("proxy recorded");
        assert!(wn.internal.contains(&b));
    }
```

(Adjust the helper names to the module's existing test helpers if they
differ — e.g. how sibling tests at `word_norm.rs:780-930` build `x` and
numerals.)

- [ ] **Step 5: `lib.rs`: rename the stash and store it whole**

1. Rename first: `sed -i 's/eliminated_ite_vals/internal_vals/g' crates/shinri-solver/src/lib.rs`
   (field, init, `pop`, `Reset`, `check_sat` clear, comments). Then
   replace the field's doc comment (~`:92-93`) so it reads:

```rust
    /// Values of `word_norm`-internal symbols (`ite!`, `bool!`) from the last
    /// `sat`, keyed by the internal symbol. Never surfaced by `get-model`;
    /// `format_value` reaches them through `orig_rewrite` / `bool_arg_var`
    /// (slice 55; was the ite-only `eliminated_ite_vals`, slice 6).
    internal_vals: rustc_hash::FxHashMap<TermId, shinri_theory::types::ModelVal>,
```

2. Reword the `pop` and `format_model` comments that describe the map as
   "eliminated-ite" to "internal-symbol".

   The local variable `internal_vals` in the main path now shadows nothing
   (it is a local); keep it.

3. ABV path (~`:945-974`): the harvest becomes

```rust
            let internal_ite_syms: Vec<TermId> =
                self.word_norm.ite_map().values().copied().collect();
```

   and replace the `// Remap original ite terms …` block (the `ite_vals`
   map and its loop, through `self.internal_vals = ite_vals;`) with:

```rust
            // Keyed by the internal symbol; `format_value` remaps (slice 55).
            self.internal_vals = ite_sym_vals;
```

   (If `ite_sym_vals`' type is not `FxHashMap<TermId, ModelVal>`, collect
   it into one: `ite_sym_vals.into_iter().collect()`.)

4. Main path (~`:1444-1458`): replace the `// Answer get-value on
   eliminated ites …` block through `self.internal_vals = ite_vals;` with:

```rust
                // Keyed by the internal symbol; `format_value` remaps
                // original query terms through `orig_rewrite` (slice 55).
                self.internal_vals = internal_vals;
```

   If a later line in the function still reads the local `internal_vals`,
   use `self.internal_vals = internal_vals.clone();` instead.

- [ ] **Step 6: `format_value`: the lookup chain**

Replace `format_value` with:

```rust
    /// Read-only value lookup for a `get-value` / `get-model` term (spec
    /// §3.3). Never mints: a minted term would shift later TermIds, which is
    /// verdict-observable across further `assert`/`check-sat` commands.
    ///
    /// 1. the term itself in the model;
    /// 2. its `word_norm` rewrite in the model (e.g. `(f (= x 1))` →
    ///    `(f bool!0)`);
    /// 3. a purified Bool argument's proxy value (`(= x 1)` → `bool!0`);
    /// 4. an internal symbol it was rewritten to (an eliminated ite);
    /// 5. the ABV array model.
    ///
    /// A term rewritten in an earlier `check-sat` but absent from the last
    /// one finds nothing at 2–4 (the model and `internal_vals` are per-solve),
    /// so it prints `?` rather than a stale value.
    fn format_value(&self, t: TermId) -> Option<String> {
        use shinri_theory::model::format_modelval;
        let model = self.last_model.as_ref();
        if let Some(v) = model.and_then(|m| m.get(t)) {
            return Some(format_modelval(v));
        }
        let r = self.word_norm.orig_rewrite_map().get(&t).copied();
        if let Some(v) = r.and_then(|r| model.and_then(|m| m.get(r))) {
            return Some(format_modelval(v));
        }
        let arg = r.unwrap_or(t);
        if let Some(v) = self
            .word_norm
            .bool_arg_map()
            .get(&arg)
            .and_then(|b| self.internal_vals.get(b))
        {
            return Some(format_modelval(v));
        }
        if let Some(v) = r.and_then(|r| self.internal_vals.get(&r)) {
            return Some(format_modelval(v));
        }
        self.abv_array_models.get(&t).cloned()
    }
```

- [ ] **Step 7: Run to verify pass**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice55_probes) | test(orig_rewrite_records_purified_parent_and_skips_unchanged_terms) | binary(ite_e2e) | binary(fp_e2e) | binary(qfufbv_e2e) | binary(slice54_probes)'`
Expected: all PASS, non-zero counts. If `e3`'s `(P false)` value is not
`?` (some channel values it), check it is consistent with the assertions
(`(not (P true))` says nothing about `(P false)`) and pin the observed
value with a comment saying which step answered it.

- [ ] **Step 8: Full suite, then commit**

Run: `cargo nextest run -p shinri-solver && grep -rn "orig_ite\|eliminated_ite_vals" crates`
Expected: PASS; grep prints nothing.

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add -A crates/shinri-solver
git commit -m "fix(solver): slice55 - remap get-value through word_norm rewrites and bool proxies"
```

---

### Task 4: Oracle — echoed values re-checked by z3

**Files:**
- Modify: `crates/shinri-solver/tests/bool_arg_oracle.rs`

**Interfaces:**
- Consumes: the generator (`gen_script`, `Family`) and `z3_outcome`'s
  ack-checking send loop already in the file.

- [ ] **Step 1: Write the check**

Add to `bool_arg_oracle.rs`:

```rust
/// Slice 55 (spec §6.3): on a `sat`, ask shinri for the value of every
/// asserted term and every Bool argument inside it, then give z3 the
/// original script plus `(assert (= term value))` for each non-`?` pair.
/// z3 must answer `sat`: the echo re-parses in another solver and the
/// values are jointly consistent with the assertions.
fn get_value_pairs(logic: &str, src: &str, queries: &[String]) -> Vec<(String, String)> {
    let full = format!(
        "(set-logic {logic})\n{src}(get-value ({}))\n",
        queries.join(" ")
    );
    let mut solver = Solver::new();
    let mut parser = Parser::new(&full);
    let mut line = None;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        if let CommandResponse::Values(s) = solver.execute(result.expect("parse")) {
            line = Some(s);
        }
    }
    let line = line.expect("get-value answered");
    // The response is `((q1 v1) (q2 v2) …)` with the qi echoed. Split it on
    // balanced parentheses at depth 1, then each pair at its last top-level
    // space.
    let inner = &line[1..line.len() - 1];
    let mut pairs = Vec::new();
    let (mut depth, mut start) = (0i32, 0usize);
    for (i, ch) in inner.char_indices() {
        match ch {
            '(' => {
                if depth == 0 {
                    start = i;
                }
                depth += 1;
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    let pair = &inner[start + 1..i];
                    let (mut d, mut split) = (0i32, None);
                    for (j, c) in pair.char_indices() {
                        match c {
                            '(' => d += 1,
                            ')' => d -= 1,
                            ' ' if d == 0 => split = Some(j),
                            _ => {}
                        }
                    }
                    let j = split.expect("pair has a value");
                    pairs.push((pair[..j].to_string(), pair[j + 1..].to_string()));
                }
            }
            _ => {}
        }
    }
    assert_eq!(pairs.len(), queries.len(), "one pair per query: {line}");
    pairs
}

fn z3_accepts_values(logic: &str, src: &str, pairs: &[(String, String)]) -> easy_smt::Response {
    let mut extra = String::new();
    for (term, val) in pairs.iter().filter(|(_, v)| v != "?") {
        extra.push_str(&format!("(assert (= {term} {val}))\n"));
    }
    z3_outcome(logic, &format!("{src}{extra}"))
}
```

`queries` for an instance: every asserted formula plus every compound
Bool argument the generator produced. Thread them out:

```rust
/// A Bool argument: `true`/`false` (so congruence with a constant matters)
/// or a depth-≤1 formula. Compound ones are recorded in `sink` for the
/// slice-55 get-value check.
fn arg(rng: &mut Lcg, fam: Family, sink: &mut Vec<String>) -> String {
    let a = match rng.below(5) {
        0 => "true".to_string(),
        1 => "false".to_string(),
        _ => formula(rng, fam, 1),
    };
    if a != "true" && a != "false" && !sink.contains(&a) {
        sink.push(a.clone());
    }
    a
}
```

Change `assertion`'s signature to
`fn assertion(rng: &mut Lcg, fam: Family, sink: &mut Vec<String>) -> String`
and every `arg(rng, fam)` inside it to `arg(rng, fam, sink)`
(`sed -i 's/arg(rng, fam)/arg(rng, fam, sink)/g'` scoped to that function).
`gen_script` becomes:

```rust
fn gen_script(rng: &mut Lcg, fam: Family) -> (String, Vec<String>) {
    let mut src = String::from(fam.decls());
    let mut queries = Vec::new();
    for _ in 0..3 + rng.below(3) {
        let a = assertion(rng, fam, &mut queries);
        src.push_str(&format!("(assert {a})\n"));
        if !queries.contains(&a) {
            queries.push(a);
        }
    }
    src.push_str("(check-sat)\n");
    (src, queries)
}
```

and `run_family` destructures `let (src, queries) = gen_script(&mut rng, fam);`.
**The generator draws the same random numbers in the same order**, so the
slice-54 scripts per seed are unchanged.

In `run_family`, after the existing outcome comparison and only when
`ours == SolveOutcome::Sat` and z3 said `Sat`:

```rust
            let pairs = get_value_pairs(fam.logic(), &src, &queries);
            match z3_accepts_values(fam.logic(), &src, &pairs) {
                easy_smt::Response::Sat | easy_smt::Response::Unknown => {}
                easy_smt::Response::Unsat => value_disagreements.push(format!(
                    "iter {iter}: z3 rejects shinri's get-value\n{src}\n{pairs:?}"
                )),
            }
            n_valued += pairs.iter().filter(|(_, v)| v != "?").count();
```

Declare `let mut value_disagreements: Vec<String> = Vec::new();` and
`let mut n_valued = 0usize;` next to the existing counters, add them to the
`println!`, and assert `value_disagreements.is_empty()` (same message shape
as the existing assert) and `n_valued > 0` (so the check cannot pass by
every value being `?`).

Note: the existing `z3_outcome` asserts on any z3 `(error …)` ack, so a
non-re-parseable echo fails loudly there rather than dropping the
assertion.

- [ ] **Step 2: Run against Task 3's head**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)'`
Expected: 3 discovered, 3 PASS; the printed line per family shows
`value_disagreements=0` and `n_valued > 0`. If a family fails, report
the first instance verbatim — it is either an echo z3 cannot parse
(Review Focus 1: the tester form) or a wrong value; do not weaken the
check.

- [ ] **Step 3: Optional before-evidence**

`git stash` is not needed: run the same command on `a0d0fe9` in a scratch
worktree with this test file copied in, and record the failing count for
the report (it fails on the `t…` echo at z3 parse time).

```bash
git worktree add /tmp/claude-1000/-workspace/0c49f566-bc58-4c66-8105-5bbfd11efbf3/scratchpad/base a0d0fe9
cp crates/shinri-solver/tests/bool_arg_oracle.rs /tmp/claude-1000/-workspace/0c49f566-bc58-4c66-8105-5bbfd11efbf3/scratchpad/base/crates/shinri-solver/tests/
(cd /tmp/claude-1000/-workspace/0c49f566-bc58-4c66-8105-5bbfd11efbf3/scratchpad/base && cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)' --no-fail-fast) 2>&1 | tail -20
git worktree remove --force /tmp/claude-1000/-workspace/0c49f566-bc58-4c66-8105-5bbfd11efbf3/scratchpad/base
```

- [ ] **Step 4: Commit**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver/tests/bool_arg_oracle.rs
git commit -m "test(oracle): slice55 - z3 re-checks shinri's get-value echo and values"
```

---

### Task 5: Verdict-neutrality bench, report, spec outcomes, PR

**Files:**
- Create: `docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md`
- Modify: `docs/superpowers/specs/2026-10-02-shinri-slice55-get-value-echo-remap-design.md`
  (append `## 11. Measured outcomes`)

- [ ] **Step 1: Gates**

```bash
mise run ci
cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle) | binary(qfdt_oracle) | test(differential_qf_uflia_compound_args)'
```

Expected: both green, non-zero counts; record counts.

- [ ] **Step 2: After run (detached, frozen binary)**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice55-after
cp target/release/shinri target/slice55-after/shinri
md5sum target/slice55-after/shinri | tee target/slice55-after/md5.txt
date -u +%FT%TZ > target/slice55-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_UF,QF_DT,QF_UFLIA,QF_UFLRA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice55-after/shinri --run-id slice55 \
  > target/slice55-after/run.log 2>&1; date -u +%FT%TZ > target/slice55-after/finished.txt' &
```

It takes ~2 h. Wait for `target/slice55-after/finished.txt` with Monitor
(do not poll with sleep). Then `BENCH_RUN_ID=slice55 mise run bench-report`.

- [ ] **Step 3: Verdict comparison**

Base is `bench/results/slice54/results.jsonl` (see *Facts*). Compare by
`path` with a scratch script (not committed):

```bash
python3 - <<'EOF'
import json
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
b = load("bench/results/slice54/results.jsonl")
a = load("bench/results/slice55/results.jsonl")
assert b.keys() == a.keys(), (len(b.keys() - a.keys()), len(a.keys() - b.keys()))
from collections import Counter
t = Counter((r["logic"], b[p]["verdict"], r["verdict"]) for p, r in a.items() if b[p]["verdict"] != r["verdict"])
for k, n in sorted(t.items()): print(k, n)
print("changed rows:", sum(t.values()), "of", len(a))
for p, r in a.items():
    if r["verdict"] == "wrong": print("ESCALATE", p)
EOF
```

Success criterion 2 is **0 rows `* → wrong`**, and every changed row
explained as timing noise (`correct ↔ timeout` near the 20 s limit or
`unknown:sat-budget` flips, which slice 54 measured at the same scale).
Re-run every changed non-timeout row 3× on both binaries
(`target/slice54-after/shinri` is the base binary if still present; else
rebuild `6212fa5` into `target/slice55-base/shinri`) and record the
answers. A reproducible verdict difference is a defect of this slice:
stop and report it (`superpowers:systematic-debugging`), do not merge.

- [ ] **Step 4: Write the report**

Follow the slice-54 report's structure: measured outcome first; exact
commands (from Step 2/3); run table (solver path, md5, start/finish,
rows); success-criteria table (spec §7: 1–4 with PASS/FAIL and evidence
paths); *What changed versus the spec* — at least: the dropped
negative-numeral item (*Facts*), the bench base reuse, Task 3 Step 1's
proxy-value finding, `e1`'s `?` value for `(+ a 1)`; and
`## Queued for the next slice`: the slice-54 queue carried minus the two
`get-value` items and the `get-model` quoting item, plus the V2 evaluator,
plus slice 56 = the `Not(Eq)` / bare-E / string-order item.

- [ ] **Step 5: Spec outcomes, commit, PR**

Append `## 11. Measured outcomes` to the spec (criteria results and the
deviations, pointing at the report).

```bash
git add docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md \
        docs/superpowers/specs/2026-10-02-shinri-slice55-get-value-echo-remap-design.md
git commit -m "docs(bench+spec): slice55 - verdict-neutrality run and measured outcomes"
git push -u origin slice55-get-value-echo-remap
gh pr create --base main --title "slice55: get-value echo, purified-term remap, symbol quoting" \
  --body "Spec: docs/superpowers/specs/2026-10-02-shinri-slice55-get-value-echo-remap-design.md
Report: docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md"
```

Merge (merge commit) only when CI is green and the user approves; then
delete the branch remote and local.
