# QF_S Core (Strings + LIA) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add the core of the SMT-LIB `String` theory (concat, length, `str.at`, `str.substr`, (dis)equality) combined with linear integer arithmetic to shinri, decided by a length-aware DPLL(T) calculus that plugs into the existing lazy `Combiner`.

**Architecture:** A new `shinri-str` crate implements `StrSolver: TheorySolver`, a congruence-on-EUF + word-equation-splitting participant in the mold of `shinri-arrays`. String (dis)equalities flow through the shared `EqualityEngine` (EUF owns congruence over `str.++`/`str.len` as function symbols); `str.len t` terms become shared **Int** leaves interned into both EUF and Arith, so the *existing* EUF↔Arith Nelson–Oppen seam performs all length exchange. Word equations are resolved by normal-form alignment splits emitted as `TCheck::Split`. A fuel budget bounds non-termination to a sound `unknown`.

**Tech Stack:** Rust 2021 (workspace edition), `rustc-hash` (FxHashMap/FxHashSet), the existing `shinri-core` term DAG, `shinri-theory` (`TheorySolver` trait, `EqualityEngine`, `Combiner`), `shinri-sat`, `shinri-arith`, `shinri-euf`, `shinri-parser`, `shinri-solver`. Differential oracle: `z3` binary on `$PATH` (already used by QF_BV/QF_ABV tests).

**Reference spec:** `docs/superpowers/specs/2026-06-24-shinri-qfs-core-design.md`.

## Global Constraints

- `edition = "2021"`, `rust-version = "1.96.0"`, `license = "MIT OR Apache-2.0"` — copy from `[workspace.package]` for every new crate's `Cargo.toml` via `*.workspace = true`.
- New crate name: `shinri-str`; add it to the workspace `members` list in `/workspace/Cargo.toml`.
- Soundness is absolute: anything not decided returns `unknown`, never a wrong SAT/UNSAT. Every `TCheck::Split` must be a valid (model-preserving) disjunction; every `TCheck::Conflict` must be a genuine contradiction.
- Alphabet = SMT-LIB Unicode scalar values `0x0..=0x2FFFF`. String literal values are stored and compared as Rust `String` (UTF-8); character indexing is by **Unicode scalar value** (use `chars()`, not bytes).
- Default model fill character: `U+0041` (`'A'`).
- TDD throughout: write the failing test, watch it fail, implement minimally, watch it pass, commit. One logical change per commit.
- Run the full workspace build/test with `cargo test` (or the per-crate `cargo test -p <crate>`); the repo also has `cargo nextest` configured (`cargo nextest run -p <crate>`). Either is acceptable; this plan uses `cargo test`.
- `THEORY_ID` for the string theory is `4` (EUF/Arith are 1/2, Arrays is 3).

---

## File Structure

**New crate `crates/shinri-str/`:**
- `Cargo.toml` — package manifest, deps on `shinri-core`, `shinri-theory`, `shinri-sat`, `rustc-hash`.
- `src/lib.rs` — `pub struct StrSolver` + `impl TheorySolver`; re-exports. The crate root wires the pieces together; the `TheorySolver` methods live here and delegate to the modules below.
- `src/collect.rs` — walk atoms, collect string-sorted subterms, `str.len`/`str.at`/`str.substr` applications, and string (dis)equality atoms (`new_var` helper).
- `src/normalize.rs` — flatten `str.++` into atom sequences; compute normal forms modulo the shared `EqualityEngine`; concat-of-literals folding.
- `src/length.rs` — structural length-axiom generation (`len ≥ 0`, `len(concat)=Σ`, `len(literal)=k`, empty link) emitted as lemma atoms; the set of shared `str.len` terms.
- `src/wordeq.rs` — the F-split alignment calculus over normal forms, constant/constant prefix comparison, variable-vs-constant character splitting, disequality witnessing.
- `src/reduce.rs` — the `str.at`/`str.substr` desugaring pre-pass (operates on `Context`, run before solving).
- `src/model.rs` — concrete string-value construction from arith lengths + normal forms.
- `src/fuel.rs` — the fuel budget type.
- `src/trail.rs` — assignment-dependent state trail for `push`/`pop`.

**Modified `crates/shinri-core/src/`:** `sort.rs`, `term.rs`, `ids.rs`, `context.rs`, `lib.rs` — String sort, string-literal constants, `Str*` builtin ops + sort-checking.

**Modified `crates/shinri-theory/src/`:** `types.rs` (`Owner::String`, `ModelVal::String`), `atom.rs` (`classify` routing + fence), `combiner.rs` (4th theory slot + all dispatch sites + N-O gate), `model.rs` (string model value).

**Modified `crates/shinri-parser/src/`:** `parser.rs` — `"String"` sort, `str.*` ops, `Token::Str` term parsing. (Lexer already tokenizes `Token::Str`.)

**Modified `crates/shinri-solver/src/`:** `lib.rs` (routing, 4-theory `Combiner` type alias, string model surfacing), `model.rs` (render `ModelVal::String`), new `string_stage.rs` (detection + fence).

**StrSolver internal data model** (defined in Task 8, referenced throughout):
```rust
pub struct StrSolver {
    /// String-sorted equality atoms currently asserted TRUE (trail-managed).
    eq_true: Vec<TermId>,
    /// String-sorted (dis)equality atoms currently asserted (= asserted false / distinct).
    diseq_true: Vec<TermId>,
    /// Every str.len application term seen (the shared-Int set).
    len_terms: FxHashSet<TermId>,
    /// Every string-sorted subterm seen (vars, literals, concats, reduced at/substr).
    str_terms: FxHashSet<TermId>,
    /// Length axioms already emitted (dedup, so a lemma is emitted at most once).
    emitted_len_axioms: FxHashSet<TermId>,
    /// Word-equation split lemmas already emitted (dedup / termination).
    emitted_splits: FxHashSet<(TermId, TermId)>,
    /// Counter for fresh remainder string variables.
    fresh_ctr: u32,
    /// Remaining fuel; on 0 → check returns the `unknown` signal.
    fuel: Fuel,
    /// Assignment-dependent trail for push/pop.
    trail: Trail,
}
```

---

## PHASE A — Core term layer (`shinri-core`)

### Task 1: String sort

**Files:**
- Modify: `crates/shinri-core/src/sort.rs` (add `SortNode::String`)
- Modify: `crates/shinri-core/src/context.rs` (add `string_sort` field + accessor)
- Test: `crates/shinri-core/src/context.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Produces: `SortNode::String` variant; `Context::string_sort(&self) -> SortId`.

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod tests` block in `context.rs`:
```rust
#[test]
fn string_sort_is_stable_singleton() {
    let mut ctx = Context::new();
    let a = ctx.string_sort();
    let b = ctx.string_sort();
    assert_eq!(a, b, "string_sort must intern to one stable SortId");
    assert_ne!(a, ctx.int_sort());
    assert_ne!(a, ctx.bool_sort());
    assert!(matches!(ctx.sort_node(a), crate::sort::SortNode::String));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core string_sort_is_stable_singleton`
Expected: FAIL — `no method named string_sort` / `no variant String`.

- [ ] **Step 3: Add the `String` variant**

In `crates/shinri-core/src/sort.rs`, add to `SortNode` (after `Real`):
```rust
    String,
```

- [ ] **Step 4: Add the field + accessor**

In `context.rs`, add a field to the `Context` struct (next to `real_sort: SortId,`):
```rust
    string_sort: SortId,
```
In `Context::new()`, initialize it to a placeholder alongside the others (`string_sort: SortId::from_index(0),`), then after the existing `ctx.real_sort = ctx.intern_sort(SortNode::Real);`-style initialization, add:
```rust
        ctx.string_sort = ctx.intern_sort(SortNode::String);
```
Add the accessor next to `real_sort()`:
```rust
    pub fn string_sort(&self) -> SortId {
        self.string_sort
    }
```

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-core string_sort_is_stable_singleton`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-core/src/sort.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): add String sort"
```

---

### Task 2: String-literal constants

**Files:**
- Modify: `crates/shinri-core/src/ids.rs` (add `StringId`)
- Modify: `crates/shinri-core/src/term.rs` (add `ConstVal::String(StringId)`)
- Modify: `crates/shinri-core/src/context.rs` (`str_lits` store, `mk_string_const`, `string_const_value`)
- Modify: `crates/shinri-core/src/lib.rs` (export `StringId`)
- Test: `crates/shinri-core/src/context.rs`

**Interfaces:**
- Produces: `StringId`; `ConstVal::String(StringId)`; `Context::mk_string_const(&mut self, value: &str) -> TermId` (String-sorted); `Context::string_const_value(&self, t: TermId) -> Option<&str>`.

- [ ] **Step 1: Write the failing test**

In `context.rs` tests:
```rust
#[test]
fn string_const_roundtrips_and_dedups() {
    let mut ctx = Context::new();
    let a = ctx.mk_string_const("ab\"c");
    let b = ctx.mk_string_const("ab\"c");
    let d = ctx.mk_string_const("xyz");
    assert_eq!(a, b, "equal string literals must hash-cons to one TermId");
    assert_ne!(a, d);
    assert_eq!(ctx.sort_of(a), ctx.string_sort());
    assert_eq!(ctx.string_const_value(a), Some("ab\"c"));
    assert_eq!(ctx.string_const_value(d), Some("xyz"));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core string_const_roundtrips_and_dedups`
Expected: FAIL — `no method named mk_string_const`.

- [ ] **Step 3: Add `StringId`**

In `ids.rs`, mirror the `BvId` newtype (use the same macro/pattern the file uses for `RatId`/`BvId`):
```rust
// StringId — index into Context.str_lits.
crate::u32_id!(StringId);
```
(If `ids.rs` defines ids explicitly rather than via a macro, copy the `BvId` definition verbatim and rename to `StringId`.)

- [ ] **Step 4: Add the `ConstVal` variant**

In `term.rs`, add to `ConstVal` (after `BitVec(BvId)`):
```rust
    String(crate::ids::StringId),
```

- [ ] **Step 5: Add the store + constructors in `context.rs`**

Add field to `Context` (next to `bvs`):
```rust
    str_lits: Vec<Box<str>>,
```
Initialize in `Context::new()`: `str_lits: Vec::new(),`. Add methods (near `mk_bv_const`):
```rust
    pub fn mk_string_const(&mut self, value: &str) -> TermId {
        let sort = self.string_sort();
        let id = match self.str_lits.iter().position(|s| s.as_ref() == value) {
            Some(idx) => crate::ids::StringId::new(idx as u32),
            None => {
                let id = crate::ids::StringId::new(self.str_lits.len() as u32);
                self.str_lits.push(value.into());
                id
            }
        };
        let val = ConstVal::String(id);
        self.intern_with_key(
            TermKey::Const { val, sort },
            TermNode::Const { val, sort },
        )
    }

    pub fn string_const_value(&self, t: TermId) -> Option<&str> {
        match self.term_node(t) {
            TermNode::Const { val: ConstVal::String(id), .. } => {
                Some(self.str_lits[id.index()].as_ref())
            }
            _ => None,
        }
    }
```
(Match the exact `StringId::new` / `.index()` API to whatever `ids.rs` generates. If the constructor is `StringId::from_index`, use that.)

- [ ] **Step 6: Export `StringId`**

In `lib.rs`, add `StringId` to the `pub use ids::{...}` list.

- [ ] **Step 7: Run test to verify it passes**

Run: `cargo test -p shinri-core string_const_roundtrips_and_dedups`
Expected: PASS. Also run `cargo test -p shinri-core` to confirm no exhaustiveness breaks in other `match ConstVal` sites; fix any by adding a `ConstVal::String(_)` arm.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-core/src/ids.rs crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs crates/shinri-core/src/lib.rs
git commit -m "feat(core): add string-literal constants (StringId, ConstVal::String, mk_string_const)"
```

---

### Task 3: String operators + sort-checking

**Files:**
- Modify: `crates/shinri-core/src/term.rs` (add `BuiltinOp::{StrConcat, StrLen, StrAt, StrSubstr}`)
- Modify: `crates/shinri-core/src/context.rs` (`check_builtin` rules)
- Test: `crates/shinri-core/src/context.rs`

**Interfaces:**
- Produces: `BuiltinOp::StrConcat` (≥2 String args → String), `BuiltinOp::StrLen` (String → Int), `BuiltinOp::StrAt` (String × Int → String), `BuiltinOp::StrSubstr` (String × Int × Int → String). All constructed via `Context::mk_app(Op::Builtin(...), &args)`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn string_ops_sort_check() {
    use crate::term::{BuiltinOp, Op};
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let int_s = ctx.int_sort();
    let x = { let s = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let y = { let s = ctx.declare_fun("y", &[], str_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let i = { let s = ctx.declare_fun("i", &[], int_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };

    let cc = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y]).unwrap();
    assert_eq!(ctx.sort_of(cc), str_s);
    let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
    assert_eq!(ctx.sort_of(len), int_s);
    let at = ctx.mk_app(Op::Builtin(BuiltinOp::StrAt), &[x, i]).unwrap();
    assert_eq!(ctx.sort_of(at), str_s);
    let ss = ctx.mk_app(Op::Builtin(BuiltinOp::StrSubstr), &[x, i, i]).unwrap();
    assert_eq!(ctx.sort_of(ss), str_s);

    // Ill-sorted: str.len on Int must fail.
    assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[i]).is_err());
    // Ill-sorted: str.at with String index must fail.
    assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrAt), &[x, y]).is_err());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core string_ops_sort_check`
Expected: FAIL — `no variant StrConcat`.

- [ ] **Step 3: Add the `BuiltinOp` variants**

In `term.rs`, after `BvRepeat(u32)`:
```rust
    // Strings (QF_S core)
    StrConcat,
    StrLen,
    StrAt,
    StrSubstr,
```

- [ ] **Step 4: Add sort-checking in `check_builtin`**

In `context.rs`, add cases inside `check_builtin` (after the bitvector cases). Use the same `int_s`/`str_s` lookups the function already uses, and the existing `expect_arity`/`expect_all` helpers:
```rust
        StrConcat => {
            if args.len() < 2 {
                return Err(SortError::Arity { expected: 2, found: args.len() });
            }
            let str_s = self.string_sort();
            expect_all(self, args, str_s)?;
            Ok(str_s)
        }
        StrLen => {
            expect_arity(args, 1)?;
            let str_s = self.string_sort();
            if self.sort_of(args[0]) != str_s {
                return Err(SortError::Mismatch { expected: str_s, found: self.sort_of(args[0]) });
            }
            Ok(self.int_sort())
        }
        StrAt => {
            expect_arity(args, 2)?;
            let (str_s, int_s) = (self.string_sort(), self.int_sort());
            if self.sort_of(args[0]) != str_s {
                return Err(SortError::Mismatch { expected: str_s, found: self.sort_of(args[0]) });
            }
            if self.sort_of(args[1]) != int_s {
                return Err(SortError::Mismatch { expected: int_s, found: self.sort_of(args[1]) });
            }
            Ok(str_s)
        }
        StrSubstr => {
            expect_arity(args, 3)?;
            let (str_s, int_s) = (self.string_sort(), self.int_sort());
            if self.sort_of(args[0]) != str_s {
                return Err(SortError::Mismatch { expected: str_s, found: self.sort_of(args[0]) });
            }
            for &a in &args[1..3] {
                if self.sort_of(a) != int_s {
                    return Err(SortError::Mismatch { expected: int_s, found: self.sort_of(a) });
                }
            }
            Ok(str_s)
        }
```
(Confirm `expect_arity`/`expect_all` signatures match existing call sites; adjust the `SortError` variant names to those defined in `error.rs`.)

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-core string_ops_sort_check`
Expected: PASS. Run `cargo test -p shinri-core` and fix any non-exhaustive `match BuiltinOp` arms elsewhere (e.g. a pretty-printer) with the new variants.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): add str.++/str.len/str.at/str.substr ops with sort-checking"
```

---

## PHASE B — Parser (`shinri-parser`)

### Task 4: Parse the String sort, string literals, and `str.*` operators

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs` (sort dispatch, `builtin_for`, `parse_term` `Token::Str` case)
- Test: `crates/shinri-parser/src/parser.rs` (or the crate's existing test module / `tests/`)

**Interfaces:**
- Consumes: `Context::string_sort`, `Context::mk_string_const`, `BuiltinOp::{StrConcat,StrLen,StrAt,StrSubstr}` (Tasks 1–3).
- Produces: parser accepts `String` sort, `"..."` literals as terms, and `str.++`/`str.len`/`str.at`/`str.substr` symbols.

- [ ] **Step 1: Write the failing test**

Add a test that parses a small script and inspects the resulting term (use the crate's existing parse-entry helper; pattern-match the parser's public API used by other parser tests):
```rust
#[test]
fn parses_strings_concat_len_and_literal() {
    let src = r#"
        (declare-fun x () String)
        (assert (= (str.len (str.++ x "ab")) 5))
    "#;
    // Use the same parse harness other tests in this file use:
    let (ctx, asserts) = parse_script_for_test(src).expect("parse ok");
    assert_eq!(asserts.len(), 1);
    // The asserted term is an Int equality whose lhs is StrLen(StrConcat(x,"ab")).
    let a = asserts[0];
    // Spot-check: the literal "ab" round-tripped as a string const of value "ab".
    assert!(find_string_const(&ctx, a, "ab"), "literal \"ab\" must be present");
}
```
If no `parse_script_for_test`/`find_string_const` helpers exist, model the test on the nearest existing parser test (search the file for `declare-fun` in tests) and adapt — assert that parsing returns `Ok` and that the top assertion is an `Eq` App.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser parses_strings_concat_len_and_literal`
Expected: FAIL — `unknown sort String` (or panic on the literal).

- [ ] **Step 3: Add the `String` sort case**

In `parse_sort`'s simple-symbol match (where `"Bool"`/`"Int"`/`"Real"` are handled):
```rust
        "String" => Ok(ctx.string_sort()),
```

- [ ] **Step 4: Add the `str.*` operators to `builtin_for`**

In `builtin_for`, add (note: `str.++` etc. are valid SMT-LIB symbol tokens):
```rust
        "str.++" => StrConcat,
        "str.len" => StrLen,
        "str.at" => StrAt,
        "str.substr" => StrSubstr,
```

- [ ] **Step 5: Add the `Token::Str` case in `parse_term`**

In `parse_term`, alongside the `Numeral`/`Hex`/`Bin` constant cases, add:
```rust
        Token::Str(s) => {
            // Strip outer quotes and unescape "" -> " (SMT-LIB string literal syntax).
            let raw = &s[1..s.len() - 1];
            let val = raw.replace("\"\"", "\"");
            Ok(ctx.mk_string_const(&val))
        }
```
(Match the exact tokenizer slice semantics — confirm `Token::Str` carries the full quoted slice as the existing `token_value_text` assumes.)

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p shinri-parser parses_strings_concat_len_and_literal`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(parser): parse String sort, string literals, and str.* operators"
```

---

## PHASE C — Theory plumbing (`shinri-theory`)

### Task 5: `ModelVal::String` and its formatter

**Files:**
- Modify: `crates/shinri-theory/src/types.rs` (or wherever `ModelVal` is defined — add `String(String)`)
- Modify: `crates/shinri-theory/src/model.rs` (any `ModelVal` match in `ModelBuilder`)
- Modify: `crates/shinri-solver/src/model.rs` (`format_modelval`)
- Test: `crates/shinri-solver/src/model.rs`

**Interfaces:**
- Produces: `ModelVal::String(String)`; `format_modelval(&ModelVal::String(s))` → SMT-LIB quoted literal.

- [ ] **Step 1: Write the failing test**

In `crates/shinri-solver/src/model.rs` tests:
```rust
#[test]
fn format_string_modelval_escapes_quotes() {
    use shinri_theory::types::ModelVal;
    assert_eq!(format_modelval(&ModelVal::String("ab".into())), "\"ab\"");
    assert_eq!(format_modelval(&ModelVal::String("a\"b".into())), "\"a\"\"b\"");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver format_string_modelval_escapes_quotes`
Expected: FAIL — `no variant String`.

- [ ] **Step 3: Add the variant**

In the `ModelVal` enum (find its definition, likely `shinri-theory/src/types.rs` or `model.rs`):
```rust
    String(String),
```

- [ ] **Step 4: Add the formatter arm**

In `format_modelval` (`shinri-solver/src/model.rs`):
```rust
        ModelVal::String(s) => format!("\"{}\"", s.replace('"', "\"\"")),
```

- [ ] **Step 5: Run + fix exhaustiveness**

Run: `cargo test -p shinri-solver format_string_modelval_escapes_quotes`
Then `cargo build` the workspace; add `ModelVal::String(_)` arms to any other non-exhaustive matches the compiler flags (e.g. in `ModelBuilder::merge_check`/`absorb`). For `merge_check`, two `String` values agree iff equal.
Expected: PASS, workspace builds.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-theory/src/ crates/shinri-solver/src/model.rs
git commit -m "feat(theory): add ModelVal::String + SMT-LIB string value formatting"
```

---

### Task 6: `Owner::String`, `classify` routing, and the string fence

**Files:**
- Modify: `crates/shinri-theory/src/types.rs` (`Owner::String`)
- Modify: `crates/shinri-theory/src/atom.rs` (`classify`)
- Test: `crates/shinri-theory/src/atom.rs`

**Interfaces:**
- Consumes: `BuiltinOp::Str*`, `Context::string_sort` (Tasks 1–3).
- Produces: `Owner::String`; `classify` returns `Ok(Owner::String)` for string atoms in scope and `Err(Unsupported)` for out-of-scope mixes; helper `fn contains_string_op(terms, atom) -> bool`.

**Routing rules (v1):**
- A `str.len`/`str.at`/`str.substr` application is *not itself a Bool atom*; it appears inside arith or string atoms. The atoms the SAT layer registers are: string `(= s t)`/`(distinct s t)` (String-sorted operands), and arith atoms over `str.len` (Int). String equality atoms → `Owner::String`. Arith atoms mentioning `str.len` → `Owner::Arith` (str.len is a leaf to arith) — no change needed there.
- Fence: a String-sorted term that is an operand of `select`/`store` (arrays over strings), or any uninterpreted *function* (arity ≥ 1) applied to/returning String, is out of scope → `Err(Unsupported)`. (Plain String variables — arity-0 uninterpreted — are fine.)

- [ ] **Step 1: Write the failing test**

In `atom.rs` tests:
```rust
#[test]
fn classify_string_equality_is_owned_by_string() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let mk = |c: &mut Context, n: &str| { let s = c.declare_fun(n, &[], str_s); c.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let x = mk(&mut ctx, "x");
    let y = mk(&mut ctx, "y");
    let atom = ctx.mk_eq(x, y).unwrap();
    assert!(matches!(classify(&ctx, atom), Ok(Owner::String)));
}

#[test]
fn classify_fences_string_under_uninterpreted_function() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let f = ctx.declare_fun("f", &[str_s], str_s); // f : String -> String
    let x = { let s = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
    let atom = ctx.mk_eq(fx, x).unwrap();
    assert!(classify(&ctx, atom).is_err(), "string under a UF is out of scope in v1");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-theory classify_string`
Expected: FAIL — `no variant String` / equality currently routes elsewhere.

- [ ] **Step 3: Add `Owner::String`**

In `types.rs`, add `String,` to the `Owner` enum.

- [ ] **Step 4: Add the fence + routing in `classify`**

In `atom.rs`, add a helper and wire it into `classify` (place the string checks before the generic Eq/Distinct classification). First the fence: reject any atom containing a String-sorted operand of an uninterpreted function application, or a String-sorted select/store operand:
```rust
fn is_string_sorted(terms: &Context, t: TermId) -> bool {
    matches!(terms.sort_node(terms.sort_of(t)), SortNode::String)
}

fn contains_string_op(terms: &Context, atom: TermId) -> bool {
    fn walk(terms: &Context, t: TermId, seen: &mut FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return false; }
        match terms.term_node(t) {
            TermNode::App { op, args, .. } => {
                if matches!(op, Op::Builtin(BuiltinOp::StrConcat | BuiltinOp::StrLen
                    | BuiltinOp::StrAt | BuiltinOp::StrSubstr)) { return true; }
                terms.children(*args).iter().any(|&c| walk(terms, c, seen))
            }
            TermNode::Const { .. } => false,
        }
    }
    let mut seen = FxHashSet::default();
    walk(terms, atom, &mut seen)
}

/// True if `atom` applies an uninterpreted function (arity >= 1) to, or through,
/// a String-sorted term — out of scope in QF_S core.
fn string_under_uf(terms: &Context, atom: TermId) -> bool {
    fn walk(terms: &Context, t: TermId, seen: &mut FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return false; }
        if let TermNode::App { op, args, .. } = terms.term_node(t) {
            let kids = terms.children(*args);
            if let Op::Uninterpreted(_) = op {
                if !kids.is_empty()
                    && (is_string_sorted(terms, t) || kids.iter().any(|&k| is_string_sorted(terms, k))) {
                    return true;
                }
            }
            kids.iter().any(|&k| walk(terms, k, seen))
        } else { false }
    }
    let mut seen = FxHashSet::default();
    walk(terms, atom, &mut seen)
}
```
Then in `classify`, after the existing array fences and before the final `match`:
```rust
    // String fences: arrays-over-string and string-under-UF are out of scope (v1).
    if string_under_uf(terms, atom) {
        return Err(Unsupported(atom));
    }
    // A String-sorted (dis)equality, or any atom carrying a string op, is owned by String.
    if let TermNode::App { op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct), args, .. } = terms.term_node(atom) {
        if terms.children(*args).iter().any(|&c| is_string_sorted(terms, c)) {
            return Ok(Owner::String);
        }
    }
    if contains_string_op(terms, atom) {
        // e.g. an arith atom over str.len stays Arith (str.len is a leaf there);
        // only reached here if not already an arith/eq atom — route to String.
        // (Arith atoms are matched by the Le/Lt/Ge/Gt / Eq arms below first.)
    }
```
Note: the existing `array_touches_arith` / extensionality fences already run earlier; ensure the String-array fence is covered by adding, in the array-equality fence, that a String-sorted-array operand is also rejected (arrays-over-string is out of scope). If `is_array_sorted` already triggers for `(Array String String)`, no extra code is needed — verify with a test in Task 18.

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-theory classify_string`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-theory/src/types.rs crates/shinri-theory/src/atom.rs
git commit -m "feat(theory): classify string (dis)equality to Owner::String + fence string-under-UF"
```

---

### Task 7: Extend `Combiner` to a 4th theory slot (with a stub String theory)

This task makes the 4-theory `Combiner` compile and pass existing tests using a **no-op stub** string theory, isolating the large mechanical change from the real solver (Phase D). The stub returns `Sat` and registers nothing.

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs` (generic `<E,A,R,S>`, `string: S` field, all dispatch sites, N-O gate)
- Modify: `crates/shinri-theory/src/lib.rs` if it re-exports a concrete `Combiner` alias
- Test: `crates/shinri-theory/src/combiner.rs` (extend existing tests to the 4-tuple; add a stub)

**Interfaces:**
- Produces: `Combiner<E: TheorySolver, A: TheorySolver, R: TheorySolver, S: TheorySolver>` with field `string: S` and accessor `string_mut(&mut self) -> &mut S`. All `Owner::String` dispatch arms route to `self.string`.

- [ ] **Step 1: Write the failing test**

Add a stub and a wiring test to `combiner.rs` tests:
```rust
#[derive(Default)]
struct StubStr;
impl TheorySolver for StubStr {
    const THEORY_ID: u16 = 4;
    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> { None }
    fn propagate(&mut self, _cx: &mut TheoryCtx, _o: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> { None }
    fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck { TCheck::Sat }
    fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
    fn push(&mut self) {}
    fn pop(&mut self, _l: usize) {}
}

#[test]
fn combiner_accepts_fourth_theory_slot() {
    // Construct a 4-theory combiner; a string equality registers as Owner::String.
    let mut c: Combiner<NullTheory, NullTheory, NullTheory, StubStr> = Combiner::default();
    let str_s = c.context_mut().string_sort();
    let x = { let s = c.context_mut().declare_fun("x", &[], str_s); c.context_mut().mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let y = { let s = c.context_mut().declare_fun("y", &[], str_s); c.context_mut().mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let atom = c.context_mut().mk_eq(x, y).unwrap();
    assert!(c.register_atom(Var::new(0), atom).is_ok());
}
```
(Use whatever context-accessor exists; if there is none, add `pub fn context_mut(&mut self) -> &mut Context { &mut self.terms }` as part of this task.)

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-theory combiner_accepts_fourth_theory_slot`
Expected: FAIL — `Combiner` takes 3 type args, not 4.

- [ ] **Step 3: Add the 4th generic + field**

In `combiner.rs`, change every `impl`/`struct` header `Combiner<E: TheorySolver, A: TheorySolver, R: TheorySolver>` to add `, S: TheorySolver`. Add the field after `arrays: R,`:
```rust
    string: S,
```
Update `Default` impl to initialize `string: S::default(),`. Add the accessor near `arrays_mut`:
```rust
    pub fn string_mut(&mut self) -> &mut S { &mut self.string }
```

- [ ] **Step 4: Add `Owner::String` arms at every dispatch site**

Add a `Owner::String` arm mirroring `Owner::Arrays` in: `register_atom`, `bind_fresh` (the fresh-split router). For strings, route to BOTH EUF (congruence over string terms) and String:
```rust
            Owner::String => {
                let mut cx = TheoryCtx { terms: &mut self.terms, eq: &mut self.eq, atoms: &self.atoms };
                self.euf.new_var(&mut cx, v, atom);
                self.string.new_var(&mut cx, v, atom);
            }
```
In `assert`:
```rust
            Owner::String => {
                let mut cx = TheoryCtx { terms: &mut self.terms, eq: &mut self.eq, atoms: &self.atoms };
                let e = self.euf.assert(&mut cx, lit);
                let s = self.string.assert(&mut cx, lit);
                e.or(s)
            }
```
In `push`: add `self.string.push();`. In `pop`: add `self.string.pop(target);`.
In the explanation dispatch (`resolve`): add
```rust
            } else if j.theory == S::THEORY_ID {
                self.string.explain(&mut cx, j.tag, exp);
```
In `build_model`: add a `string_m` block mirroring `arrays_m` and `combined.absorb(string_m);`.

- [ ] **Step 5: Add the String `check` call in `drive_final_check`**

After the `self.arrays.check(...)` block, add (string checks last, lowest priority):
```rust
        match self.string.check(&mut cx, Effort::Full) {
            TCheck::Conflict(cf) => return FinalCheck::Conflict(cf),
            TCheck::Split(atoms) => return FinalCheck::Split(atoms),
            TCheck::Sat => {}
        }
```
And in `drive_propagation`, add `if let Some(cf) = self.string.propagate(&mut cx, out) { return Some(cf); }`.

- [ ] **Step 6: Extend the N-O gate to include string-length terms**

In `drive_final_check`, change the shared-set computation so the EUF↔Arith exchange also runs when the string theory contributes shared Int (length) terms. Replace the gate:
```rust
        let shared: Vec<TermId> = {
            let mut cx = TheoryCtx { terms: &mut self.terms, eq: &mut self.eq, atoms: &self.atoms };
            let euf_uf = self.euf.has_uf_application(&mut cx);
            let str_lens = self.string.shared_arith_terms(&mut cx); // str.len terms (empty for the stub)
            if !euf_uf && str_lens.is_empty() {
                Vec::new()
            } else {
                let mut s = self.euf.shared_arith_terms(&mut cx);
                for t in str_lens { if !s.contains(&t) { s.push(t); } }
                for &t in &s { self.arith.ensure_shared_var(&mut cx, t); }
                s
            }
        };
```
(The stub's `shared_arith_terms` default returns `Vec::new()`, so existing behavior is unchanged until Phase D.)

- [ ] **Step 7: Update all `Combiner<...>` instantiations to 4 args**

`grep -rn "Combiner<" crates/ --include=*.rs`. In `shinri-solver/src/lib.rs`, update the `Sat` type alias to `Combiner<Euf, Arith, Arrays, /* placeholder */>`. For now, to keep the workspace compiling before `shinri-str` exists, add a temporary `EmptyStr` no-op theory in `shinri-theory` (re-export `shinri_theory::empty`-style) OR gate this in Task 8 by introducing the real crate immediately. **Decision:** keep the solver compiling by temporarily using `shinri_theory::Empty` (the existing `empty.rs` null theory) as the 4th arg here; Task 8 swaps it for `shinri_str::StrSolver`.

- [ ] **Step 8: Run tests to verify they pass**

Run: `cargo test -p shinri-theory` then `cargo build` (workspace).
Expected: PASS — existing combiner tests still pass with the 4-tuple, new wiring test passes, workspace builds with `Empty` as the 4th theory.

- [ ] **Step 9: Commit**

```bash
git add crates/shinri-theory/src/ crates/shinri-solver/src/lib.rs
git commit -m "feat(theory): extend Combiner to a 4th (String) theory slot with N-O length gate"
```

---

## PHASE D — The string theory (`shinri-str`)

### Task 8: Crate skeleton + `StrSolver` collecting atoms (no reasoning yet)

**Files:**
- Create: `crates/shinri-str/Cargo.toml`
- Create: `crates/shinri-str/src/lib.rs`
- Create: `crates/shinri-str/src/collect.rs`
- Create: `crates/shinri-str/src/fuel.rs`
- Create: `crates/shinri-str/src/trail.rs`
- Modify: `/workspace/Cargo.toml` (add member)
- Modify: `crates/shinri-solver/src/lib.rs` (swap `Empty` → `shinri_str::StrSolver`)
- Test: `crates/shinri-str/src/lib.rs`

**Interfaces:**
- Produces: `pub struct StrSolver` (fields per the File Structure block) implementing `TheorySolver` with `THEORY_ID = 4`; `check` returns `Sat`; `new_var` collects string terms, `str.len` terms, and (dis)equality atoms. `Fuel { remaining: u32 }` with `fn spend(&mut self) -> bool`. `Trail` with `push`/`pop` of asserted-atom marks.

- [ ] **Step 1: Create the crate manifest + workspace member**

`crates/shinri-str/Cargo.toml`:
```toml
[package]
name = "shinri-str"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-theory = { path = "../shinri-theory" }
shinri-sat = { path = "../shinri-sat" }
rustc-hash = "2"
```
Add `"crates/shinri-str"` to `members` in `/workspace/Cargo.toml`.

- [ ] **Step 2: Write the failing test**

`crates/shinri-str/src/lib.rs` (test at bottom):
```rust
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Context, Op, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    #[test]
    fn collects_len_terms_and_returns_sat_initially() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = { let s = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
        let len = ctx.mk_app(shinri_core::Op::Builtin(shinri_core::BuiltinOp::StrLen), &[x]).unwrap();
        let ge = { // (>= (str.len x) 0) — an arith atom carrying str.len
            let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0.into()), ctx.int_sort());
            ctx.mk_app(shinri_core::Op::Builtin(shinri_core::BuiltinOp::Ge), &[len, zero]).unwrap()
        };
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        s.new_var(&mut cx, Var::new(0), ge);
        assert!(s.shared_arith_terms(&mut cx).contains(&len), "str.len term must be shared");
        assert!(matches!(s.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}
```

- [ ] **Step 3: Run test to verify it fails**

Run: `cargo test -p shinri-str collects_len_terms`
Expected: FAIL — crate/struct doesn't exist.

- [ ] **Step 4: Implement `Fuel`, `Trail`, `collect`, and `StrSolver` skeleton**

`src/fuel.rs`:
```rust
#[derive(Clone, Copy)]
pub struct Fuel { pub remaining: u32 }
impl Default for Fuel { fn default() -> Self { Fuel { remaining: 10_000 } } }
impl Fuel {
    /// Returns false when exhausted (caller must then signal `unknown`).
    pub fn spend(&mut self) -> bool {
        if self.remaining == 0 { return false; }
        self.remaining -= 1; true
    }
}
```
`src/trail.rs`:
```rust
#[derive(Default)]
pub struct Trail { marks: Vec<(usize, usize)> } // (eq_true_len, diseq_true_len) at each push
impl Trail {
    pub fn push(&mut self, eq_len: usize, diseq_len: usize) { self.marks.push((eq_len, diseq_len)); }
    /// Returns the (eq_true_len, diseq_true_len) to truncate to for absolute `target` level.
    pub fn pop_to(&mut self, target: usize) -> Option<(usize, usize)> {
        let mut last = None;
        while self.marks.len() > target { last = self.marks.pop(); }
        last
    }
}
```
`src/collect.rs`:
```rust
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

pub fn is_string_sorted(terms: &Context, t: TermId) -> bool {
    matches!(terms.sort_node(terms.sort_of(t)), shinri_core::SortNode::String)
}

/// Record every str.len application, string-sorted subterm, into the given sets.
pub fn collect(terms: &Context, t: TermId, len_terms: &mut FxHashSet<TermId>, str_terms: &mut FxHashSet<TermId>, seen: &mut FxHashSet<TermId>) {
    if !seen.insert(t) { return; }
    if is_string_sorted(terms, t) { str_terms.insert(t); }
    if let TermNode::App { op, args, .. } = terms.term_node(t) {
        if matches!(op, Op::Builtin(BuiltinOp::StrLen)) { len_terms.insert(t); }
        for k in terms.children(*args).to_vec() { collect(terms, k, len_terms, str_terms, seen); }
    }
}
```
`src/lib.rs`:
```rust
mod collect;
mod fuel;
mod trail;
pub use fuel::Fuel;

use rustc_hash::FxHashSet;
use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct StrSolver {
    eq_true: Vec<TermId>,
    diseq_true: Vec<TermId>,
    len_terms: FxHashSet<TermId>,
    str_terms: FxHashSet<TermId>,
    emitted_len_axioms: FxHashSet<TermId>,
    emitted_splits: FxHashSet<(TermId, TermId)>,
    fresh_ctr: u32,
    fuel: Fuel,
    trail: trail::Trail,
}

impl TheorySolver for StrSolver {
    const THEORY_ID: u16 = 4;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        let mut seen = FxHashSet::default();
        collect::collect(cx.terms, atom, &mut self.len_terms, &mut self.str_terms, &mut seen);
    }

    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
        // Filled in Task 10 (records asserted string (dis)equalities).
        None
    }

    fn propagate(&mut self, _cx: &mut TheoryCtx, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> { None }

    fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck { TCheck::Sat }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}

    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn push(&mut self) { self.trail.push(self.eq_true.len(), self.diseq_true.len()); }

    fn pop(&mut self, level: usize) {
        if let Some((e, d)) = self.trail.pop_to(level) {
            self.eq_true.truncate(e);
            self.diseq_true.truncate(d);
        }
    }

    fn shared_arith_terms(&self, _cx: &mut TheoryCtx) -> Vec<TermId> {
        self.len_terms.iter().copied().collect()
    }
}
```

- [ ] **Step 5: Swap the solver's 4th theory to `StrSolver`**

In `shinri-solver/Cargo.toml` add `shinri-str = { path = "../shinri-str" }`. In `shinri-solver/src/lib.rs`, change the `Sat` type alias 4th arg from `shinri_theory::Empty` to `shinri_str::StrSolver`.

- [ ] **Step 6: Run tests to verify they pass**

Run: `cargo test -p shinri-str collects_len_terms` then `cargo build` (workspace).
Expected: PASS, workspace builds.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-str/ Cargo.toml crates/shinri-solver/Cargo.toml crates/shinri-solver/src/lib.rs
git commit -m "feat(str): shinri-str crate skeleton — StrSolver collects string/len terms, returns Sat"
```

---

### Task 9: Length skeleton — emit structural length axioms as lemmas

**Files:**
- Create: `crates/shinri-str/src/length.rs`
- Modify: `crates/shinri-str/src/lib.rs` (`check` emits axioms; `new_var` populates concat/literal info)
- Test: `crates/shinri-str/src/length.rs`

**Interfaces:**
- Consumes: `StrSolver.len_terms`, `str_terms` (Task 8).
- Produces: `fn length_axiom(terms, len_term) -> Option<TermId>` returning the next un-emitted length-defining atom for a `str.len` application: `len ≥ 0`; `len("lit") = k`; `len(a++b++…) = len(a)+len(b)+…`. `StrSolver::check` returns `TCheck::Split(vec![axiom])` for each until all are emitted, then proceeds.

- [ ] **Step 1: Write the failing test**

`src/length.rs` tests:
```rust
#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};
    use crate::StrSolver;

    #[test]
    fn emits_concat_length_axiom() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| { let s = c.declare_fun(n, &[], str_s); c.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
        let x = mk(&mut ctx, "x"); let y = mk(&mut ctx, "y");
        let cc = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y]).unwrap();
        let len_cc = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[cc]).unwrap();
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0.into()), ctx.int_sort());
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[len_cc, zero]).unwrap();

        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        // The solver must, over successive checks, emit len(x++y) = len(x)+len(y) and len >= 0 axioms.
        let mut emitted = 0;
        for _ in 0..8 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split(a) => { assert_eq!(a.len(), 1, "length axioms are unit lemmas"); emitted += 1; }
                TCheck::Sat => break,
                TCheck::Conflict(_) => panic!("no conflict expected"),
            }
        }
        assert!(emitted >= 2, "must emit at least the >=0 and concat-sum axioms");
        assert!(matches!(s.check(&mut cx, Effort::Full), TCheck::Sat), "fixpoint after all axioms emitted");
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str emits_concat_length_axiom`
Expected: FAIL — `check` returns `Sat` immediately (no axioms).

- [ ] **Step 3: Implement `length.rs`**

```rust
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// Build `(>= len_term 0)`.
fn ge_zero(terms: &mut Context, len_term: TermId) -> TermId {
    let zero = terms.mk_numeral(shinri_core::Rational::from_int(0.into()), terms.int_sort());
    terms.mk_app(Op::Builtin(BuiltinOp::Ge), &[len_term, zero]).expect("well-sorted")
}

/// For `str.len(arg)`, the defining equation atom, or None if `arg` is an opaque variable.
fn defining_eq(terms: &mut Context, len_term: TermId, arg: TermId) -> Option<TermId> {
    match terms.term_node(arg) {
        TermNode::Const { val: shinri_core::ConstVal::String(_), .. } => {
            let n = terms.string_const_value(arg).unwrap().chars().count() as i64;
            let k = terms.mk_numeral(shinri_core::Rational::from_int(n.into()), terms.int_sort());
            Some(terms.mk_eq(len_term, k).expect("well-sorted"))
        }
        TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), args, .. } => {
            let kids = terms.children(*args).to_vec();
            let parts: Vec<TermId> = kids.iter()
                .map(|&c| terms.mk_app(Op::Builtin(BuiltinOp::StrLen), &[c]).expect("well-sorted"))
                .collect();
            let sum = terms.mk_app(Op::Builtin(BuiltinOp::Add), &parts).expect("well-sorted");
            Some(terms.mk_eq(len_term, sum).expect("well-sorted"))
        }
        _ => None,
    }
}

/// Return (axiom-atom, dedup-key) pairs for `len_term` not yet emitted.
pub fn next_axiom(terms: &mut Context, len_term: TermId, emitted: &rustc_hash::FxHashSet<TermId>) -> Option<TermId> {
    let arg = match terms.term_node(len_term) {
        TermNode::App { op: Op::Builtin(BuiltinOp::StrLen), args, .. } => terms.children(*args)[0],
        _ => return None,
    };
    let ge = ge_zero(terms, len_term);
    if !emitted.contains(&ge) { return Some(ge); }
    if let Some(eqn) = defining_eq(terms, len_term, arg) {
        if !emitted.contains(&eqn) { return Some(eqn); }
    }
    None
}
```

- [ ] **Step 4: Wire into `StrSolver::check`**

In `lib.rs`, add `mod length;` and make `check` emit pending length axioms first:
```rust
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full { return TCheck::Sat; }
        let lens: Vec<TermId> = self.len_terms.iter().copied().collect();
        for lt in lens {
            if let Some(axiom) = length::next_axiom(cx.terms, lt, &self.emitted_len_axioms) {
                self.emitted_len_axioms.insert(axiom);
                return TCheck::Split(vec![axiom]);
            }
        }
        TCheck::Sat
    }
```
Also, in `new_var`, after collecting, intern any newly discovered `str.len` arguments' nested `str.len` terms (collect already recurses; ensure `len_terms` captures nested ones — it does).

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-str emits_concat_length_axiom`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/src/length.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): emit structural length axioms (>=0, literal=k, concat=sum) as unit lemmas"
```

---

### Task 10: Record asserted (dis)equalities + normal forms + constant/constant resolution

**Files:**
- Create: `crates/shinri-str/src/normalize.rs`
- Modify: `crates/shinri-str/src/lib.rs` (`assert` records atoms; `check` runs word-equation resolution after length axioms)
- Test: `crates/shinri-str/src/normalize.rs`

**Interfaces:**
- Consumes: `EqualityEngine` (via `TheoryCtx`), `eq_true`/`diseq_true`.
- Produces: `fn normal_form(terms, eq, t) -> Vec<TermId>` — the flattened concat atom sequence of `t` with each atom mapped to its `EqualityEngine` representative term and adjacent string-literal atoms folded; `fn atoms_equal(eq, a, b) -> bool`. `StrSolver::assert` pushes a true string `=` atom into `eq_true`, a true `distinct` (or a false `=`) into `diseq_true`.

- [ ] **Step 1: Write the failing test**

`src/normalize.rs` tests:
```rust
#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_theory::EqualityEngine;
    use crate::normalize::normal_form;

    #[test]
    fn flattens_nested_concat_and_folds_literals() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = { let s = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
        let ab = ctx.mk_string_const("ab");
        let cd = ctx.mk_string_const("cd");
        let inner = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ab, cd]).unwrap();
        let outer = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, inner]).unwrap();
        let mut eq = EqualityEngine::default();
        let nf = normal_form(&mut ctx, &mut eq, outer);
        // x ++ "ab" ++ "cd"  ==  x ++ "abcd"  (literals folded)
        assert_eq!(nf.len(), 2);
        assert_eq!(ctx.string_const_value(nf[1]), Some("abcd"));
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str flattens_nested_concat`
Expected: FAIL — module/function missing.

- [ ] **Step 3: Implement `normalize.rs`**

```rust
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::EqualityEngine;

/// Representative term of `t`'s equivalence class (or `t` itself).
fn rep(terms: &mut Context, eq: &mut EqualityEngine, t: TermId) -> TermId {
    let n = eq.intern(t);
    // EqualityEngine exposes a representative TermId for a node; use its API.
    eq.rep_term(n).unwrap_or(t)
}

/// Flatten str.++ into a sequence; map each atom to its class rep; fold adjacent literals; drop "".
pub fn normal_form(terms: &mut Context, eq: &mut EqualityEngine, t: TermId) -> Vec<TermId> {
    let mut flat = Vec::new();
    flatten(terms, t, &mut flat);
    // Map to reps, fold literals.
    let mut out: Vec<TermId> = Vec::new();
    for a in flat {
        let r = rep(terms, eq, a);
        if let Some(s) = terms.string_const_value(r) {
            if s.is_empty() { continue; } // drop empty
            if let Some(&last) = out.last() {
                if let Some(ls) = terms.string_const_value(last) {
                    let merged = format!("{ls}{s}");
                    let m = terms.mk_string_const(&merged);
                    *out.last_mut().unwrap() = m;
                    continue;
                }
            }
        }
        out.push(r);
    }
    out
}

fn flatten(terms: &Context, t: TermId, out: &mut Vec<TermId>) {
    match terms.term_node(t) {
        TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), args, .. } => {
            for k in terms.children(*args).to_vec() { flatten(terms, k, out); }
        }
        _ => out.push(t),
    }
}
```
(If `EqualityEngine` has no `rep_term`, use the existing accessor used by other theories to get a class's representative term, e.g. via `find` + a node→term map; mirror how `shinri-euf` reads representatives. Adjust `rep` accordingly.)

- [ ] **Step 4: Implement `assert` recording**

In `lib.rs` `assert`, record string (dis)equality literals. Use `cx.atoms` to map the literal's `Var` to its atom `TermId` and polarity:
```rust
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        let atom = match cx.atoms.atom_of(lit.var()) { Some(a) => a, None => return None };
        let node = cx.terms.term_node(atom);
        if let TermNode::App { op, .. } = node {
            match op {
                Op::Builtin(BuiltinOp::Eq) => {
                    if lit.is_positive() { self.eq_true.push(atom); } else { self.diseq_true.push(atom); }
                }
                Op::Builtin(BuiltinOp::Distinct) => {
                    if lit.is_positive() { self.diseq_true.push(atom); } else { self.eq_true.push(atom); }
                }
                _ => {}
            }
        }
        None
    }
```
(Match `cx.atoms.atom_of` / `lit.is_positive` to the real `AtomRegistry`/`Lit` API — confirm method names; `arrays` and `euf` read atoms similarly.)

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-str flattens_nested_concat` then `cargo test -p shinri-str`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/src/normalize.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): normal-form flattening + literal folding; record asserted (dis)equalities"
```

---

### Task 11: Word-equation resolution — same-atom strip + constant prefix mismatch conflict

**Files:**
- Create: `crates/shinri-str/src/wordeq.rs`
- Modify: `crates/shinri-str/src/lib.rs` (`check` calls word-equation resolution after length axioms)
- Test: `crates/shinri-str/src/wordeq.rs`

**Interfaces:**
- Consumes: `normal_form`, `eq_true`, `EqualityEngine`.
- Produces: `enum StepResult { Done, Conflict(Vec<EqLeaf>), Split(Vec<TermId>) }`; `fn resolve_equation(solver, cx, lhs_nf, rhs_nf) -> StepResult`. For now it strips equal leading/trailing atoms and detects constant-prefix mismatch → `Conflict`.

- [ ] **Step 1: Write the failing test**

`src/wordeq.rs` tests:
```rust
#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqJust, EqualityEngine, TCheck, TheoryCtx, TheorySolver};
    use crate::StrSolver;

    // "ab" ++ x  =  "ac" ++ x   is UNSAT by prefix mismatch (b != c at index 1).
    #[test]
    fn constant_prefix_mismatch_is_conflict() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = { let s = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
        let ab = ctx.mk_string_const("ab");
        let ac = ctx.mk_string_const("ac");
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ab, x]).unwrap();
        let r = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ac, x]).unwrap();
        let atom = ctx.mk_eq(l, r).unwrap();

        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        // Simulate the SAT layer asserting the equality true:
        s.test_force_eq_true(atom);
        // Drain length axioms, then expect a conflict.
        loop {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split(_) => continue,
                TCheck::Conflict(_) => break,
                TCheck::Sat => panic!("expected conflict on prefix mismatch"),
            }
        }
    }
}
```
Add a `#[cfg(test)] pub fn test_force_eq_true(&mut self, atom: TermId) { self.eq_true.push(atom); }` helper to `StrSolver`.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str constant_prefix_mismatch_is_conflict`
Expected: FAIL — no word-equation resolution yet (returns Sat).

- [ ] **Step 3: Implement `wordeq.rs` (strip + mismatch)**

```rust
use shinri_core::{Context, TermId};
use shinri_theory::types::EqLeaf;
use shinri_theory::EqualityEngine;

pub enum StepResult { Done, Conflict(Vec<EqLeaf>), Split(Vec<TermId>) }

/// Compare two atoms for definite equality in the EqualityEngine or as identical literals.
fn same(terms: &mut Context, eq: &mut EqualityEngine, a: TermId, b: TermId) -> bool {
    if a == b { return true; }
    if let (Some(x), Some(y)) = (terms.string_const_value(a), terms.string_const_value(b)) { return x == y; }
    let (an, bn) = (eq.intern(a), eq.intern(b));
    eq.are_equal(an, bn)
}

/// Resolve one equation between two normal forms. Strips equal heads/tails; on two
/// constant heads with a character mismatch, returns Conflict. Otherwise Done (head
/// is variable — handled by the F-split task) or Done if fully consumed.
pub fn resolve_equation(terms: &mut Context, eq: &mut EqualityEngine, lhs: &[TermId], rhs: &[TermId], just: Vec<EqLeaf>) -> StepResult {
    let (mut i, mut j) = (0usize, 0usize);
    let (mut le, mut re) = (lhs.len(), rhs.len());
    // Strip equal heads.
    while i < le && j < re && same(terms, eq, lhs[i], rhs[j]) { i += 1; j += 1; }
    // Strip equal tails.
    while le > i && re > j && same(terms, eq, lhs[le - 1], rhs[re - 1]) { le -= 1; re -= 1; }
    // Both exhausted: equation holds.
    if i == le && j == re { return StepResult::Done; }
    // Both sides non-empty with constant heads: compare characters.
    if i < le && j < re {
        if let (Some(a), Some(b)) = (terms.string_const_value(lhs[i]), terms.string_const_value(rhs[j])) {
            let (ca, cb) = (a.chars().next(), b.chars().next());
            if ca != cb { return StepResult::Conflict(just); }
        }
    }
    // One side empty, other forced non-empty by a non-empty constant: conflict.
    if (i == le) ^ (j == re) {
        let rest = if i == le { &rhs[j..re] } else { &lhs[i..le] };
        if rest.iter().any(|&a| terms.string_const_value(a).map_or(false, |s| !s.is_empty())) {
            return StepResult::Conflict(just);
        }
    }
    StepResult::Done // residual variable-headed equation: F-split handles it (Task 12)
}
```

- [ ] **Step 4: Wire into `check`**

In `lib.rs` `check`, after the length-axiom loop, iterate asserted equalities:
```rust
        let eqs = self.eq_true.clone();
        for atom in eqs {
            let (l, r) = crate::wordeq::sides(cx.terms, atom);
            let lhs = crate::normalize::normal_form(cx.terms, cx.eq, l);
            let rhs = crate::normalize::normal_form(cx.terms, cx.eq, r);
            let just = vec![/* the equality literal as an EqLeaf — see Task 12 */];
            match crate::wordeq::resolve_equation(cx.terms, cx.eq, &lhs, &rhs, just) {
                crate::wordeq::StepResult::Conflict(cf) => return TCheck::Conflict(cf),
                crate::wordeq::StepResult::Split(atoms) => return TCheck::Split(atoms),
                crate::wordeq::StepResult::Done => {}
            }
        }
        TCheck::Sat
```
Add `pub fn sides(terms, atom) -> (TermId, TermId)` to `wordeq.rs` reading the two children of the `Eq` atom. For this task the `just` may be an empty `Vec` (refined in Task 12); the conflict is still sound because the asserted equality is in the trail.

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-str constant_prefix_mismatch_is_conflict`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/src/wordeq.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): word-equation head/tail strip + constant prefix-mismatch conflict"
```

---

### Task 12: The F-split rule (length-aware alignment) + conflict justifications

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs` (variable-headed F-split; build justifications)
- Modify: `crates/shinri-str/src/lib.rs` (fresh-variable minting; proper `EqLeaf` justification for asserted equalities)
- Test: `crates/shinri-str/src/wordeq.rs`

**Interfaces:**
- Consumes: `StrSolver.fresh_ctr`, `Context::declare_fun`/`mk_app`, `emitted_splits` dedup.
- Produces: when the residual equation has a variable head `a₁` vs head `b₁`, `resolve_equation` returns `Split` with three positive atoms:
  `(= (str.len a₁) (str.len b₁))`, plus the two prefix-equations using a fresh remainder `z`. The split is the disjunction `len-eq ∨ a₁=b₁++z ∨ b₁=a₁++z` encoded as the atom set the Combiner lifts. Fresh `z` is a new String constant `declare_fun("!strk<N>", &[], String)`.

- [ ] **Step 1: Write the failing test**

```rust
// x ++ "a"  =  "b" ++ y  with x,y variables → an F-split is emitted (not immediate sat/conflict).
#[test]
fn variable_head_emits_fsplit() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let mk = |c: &mut Context, n: &str| { let s = c.declare_fun(n, &[], str_s); c.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let x = mk(&mut ctx, "x"); let y = mk(&mut ctx, "y");
    let a = ctx.mk_string_const("a"); let b = ctx.mk_string_const("b");
    let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, a]).unwrap();
    let r = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[b, y]).unwrap();
    let atom = ctx.mk_eq(l, r).unwrap();
    let mut s = StrSolver::default();
    let mut eq = EqualityEngine::default();
    let areg = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
    s.new_var(&mut cx, shinri_core::Var::new(0), atom);
    s.test_force_eq_true(atom);
    let mut saw_split = false;
    for _ in 0..32 {
        match s.check(&mut cx, Effort::Full) {
            TCheck::Split(atoms) => { if atoms.len() >= 2 { saw_split = true; break; } }
            TCheck::Sat => break,
            TCheck::Conflict(_) => break,
        }
    }
    assert!(saw_split, "a variable-headed word equation must emit a multi-atom F-split");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str variable_head_emits_fsplit`
Expected: FAIL — `resolve_equation` currently returns `Done` for variable heads.

- [ ] **Step 3: Implement the F-split**

Add to `wordeq.rs`, replacing the final `StepResult::Done` for the variable-headed case. Provide a callback for minting fresh vars and length terms:
```rust
use shinri_core::{BuiltinOp, Op};

pub struct SplitCtx<'a> { pub fresh_ctr: &'a mut u32 }

fn fresh_str(terms: &mut Context, ctr: &mut u32) -> TermId {
    let name = format!("!strk{}", *ctr); *ctr += 1;
    let str_s = terms.string_sort();
    let sym = terms.declare_fun(&name, &[], str_s);
    terms.mk_app(Op::Uninterpreted(sym), &[]).expect("well-sorted")
}

fn len_of(terms: &mut Context, t: TermId) -> TermId {
    terms.mk_app(Op::Builtin(BuiltinOp::StrLen), &[t]).expect("well-sorted")
}

/// Build the three F-split atoms for heads a, b (at least one a variable).
pub fn fsplit_atoms(terms: &mut Context, a: TermId, b: TermId, ctr: &mut u32) -> Vec<TermId> {
    let la = len_of(terms, a); let lb = len_of(terms, b);
    let len_eq = terms.mk_eq(la, lb).expect("well-sorted");           // |a| = |b| → a = b (heads align)
    let z1 = fresh_str(terms, ctr);
    let a_pref = { let bc = terms.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[b, z1]).expect("ws"); terms.mk_eq(a, bc).expect("ws") }; // a = b ++ z1
    let z2 = fresh_str(terms, ctr);
    let b_pref = { let ac = terms.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, z2]).expect("ws"); terms.mk_eq(b, ac).expect("ws") }; // b = a ++ z2
    vec![len_eq, a_pref, b_pref]
}
```
Change `resolve_equation` to take `&mut u32` (the fresh counter) and `emitted: &mut FxHashSet<(TermId,TermId)>`. After the strip logic, when both sides non-empty and at least one head is a variable (no `string_const_value`), and the pair `(lhs[i], rhs[j])` is not in `emitted`:
```rust
    if i < le && j < re {
        let (ha, hb) = (lhs[i], rhs[j]);
        let var_head = terms.string_const_value(ha).is_none() || terms.string_const_value(hb).is_none();
        if var_head {
            let key = if ha.index() <= hb.index() { (ha, hb) } else { (hb, ha) };
            if emitted.insert(key) {
                return StepResult::Split(fsplit_atoms(terms, ha, hb, ctr));
            }
            return StepResult::Done; // already split this pair this search branch
        }
    }
```

- [ ] **Step 4: Build proper justifications + mint length terms for fresh splits**

In `lib.rs`, when iterating `eq_true`, build the `EqLeaf` justification from the asserted equality literal (mirror how `arrays`/`euf` construct `EqLeaf` antecedents — use the equality atom's class membership). Pass `&mut self.fresh_ctr` and `&mut self.emitted_splits` into `resolve_equation`. After emitting an F-split, register the new `str.len` terms (`la`, `lb`) into `self.len_terms` so their length axioms get emitted on the next check. Spend one unit of fuel per split (Task 15 enforces the budget; here just thread the counter).

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-str variable_head_emits_fsplit` then `cargo test -p shinri-str`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/src/wordeq.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): length-aware F-split for variable-headed word equations"
```

---

### Task 13: Variable-vs-constant head splitting (character split + empty branch)

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs`
- Test: `crates/shinri-str/src/wordeq.rs`

**Interfaces:**
- Produces: when one head is a variable `v` and the other a non-empty constant `c` (first char `ch`), `resolve_equation` returns a `Split` of: `(= v "")` (empty branch) ∨ `(= (str.at v 0) "<ch>")` realized as `v = "<ch>" ++ z` for fresh `z`. This specializes the F-split using the known constant character so arith+matching converge faster.

- [ ] **Step 1: Write the failing test**

```rust
// x = "ab"  with x a variable → x must be split toward the literal; eventually SAT with x="ab".
#[test]
fn variable_equals_constant_splits_then_sat() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let x = { let s = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let ab = ctx.mk_string_const("ab");
    let atom = ctx.mk_eq(x, ab).unwrap();
    let mut s = StrSolver::default();
    let mut eq = EqualityEngine::default();
    let areg = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
    s.new_var(&mut cx, shinri_core::Var::new(0), atom);
    s.test_force_eq_true(atom);
    // It should not produce a conflict; it should split or be Sat.
    let mut ok = false;
    for _ in 0..32 {
        match s.check(&mut cx, Effort::Full) {
            TCheck::Conflict(_) => panic!("x = \"ab\" is satisfiable"),
            TCheck::Split(_) => { ok = true; /* in real search the SAT layer picks a branch; here just confirm progress */ break; }
            TCheck::Sat => { ok = true; break; }
        }
    }
    assert!(ok);
}
```

- [ ] **Step 2: Run test to verify it fails (or is too coarse)**

Run: `cargo test -p shinri-str variable_equals_constant_splits_then_sat`
Expected: With only the generic F-split, this still emits a split — the test mainly guards against a spurious conflict. If it already passes via the generic F-split, extend the assertion to check the *shape*: the split must contain an empty-branch atom `(= x "")`. Then it fails until the specialized split is implemented.

- [ ] **Step 3: Implement the variable-vs-constant split**

In `resolve_equation`, before the generic F-split, handle the variable-vs-nonempty-constant case:
```rust
    if i < le && j < re {
        let (ha, hb) = (lhs[i], rhs[j]);
        let (var, cst) = match (terms.string_const_value(ha), terms.string_const_value(hb)) {
            (None, Some(_)) => (ha, hb),
            (Some(_), None) => (hb, ha),
            _ => (TermId::INVALID, TermId::INVALID), // not this case
        };
        if var != TermId::INVALID {
            let cs = terms.string_const_value(cst).unwrap();
            if let Some(ch) = cs.chars().next() {
                let key = if var.index() <= cst.index() { (var, cst) } else { (cst, var) };
                if emitted.insert(key) {
                    let empty = terms.mk_string_const("");
                    let v_empty = terms.mk_eq(var, empty).expect("ws");           // v = ""
                    let head = terms.mk_string_const(&ch.to_string());
                    let z = fresh_str(terms, ctr);
                    let hz = terms.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[head, z]).expect("ws");
                    let v_head = terms.mk_eq(var, hz).expect("ws");               // v = "ch" ++ z
                    return StepResult::Split(vec![v_empty, v_head]);
                }
                return StepResult::Done;
            }
        }
    }
```
(Provide a `TermId::INVALID` sentinel or restructure with `Option<(TermId,TermId)>` if `TermId` has no sentinel — prefer `Option`.)

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-str variable_equals_constant_splits_then_sat` then `cargo test -p shinri-str`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-str/src/wordeq.rs
git commit -m "feat(str): variable-vs-constant head split (empty branch + leading-char peel)"
```

---

### Task 14: Disequality handling (same-word conflict + witness split) and empty-length link

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs` (disequality check)
- Modify: `crates/shinri-str/src/length.rs` (empty link: `len(s)=0 ⟹ s=""`)
- Modify: `crates/shinri-str/src/lib.rs` (`check` runs diseq checks + empty link)
- Test: `crates/shinri-str/src/wordeq.rs`

**Interfaces:**
- Produces: `fn check_disequations(...)` → if any asserted `s ≠ t` has `normal_form(s) == normal_form(t)` (atom-wise equal reps), `Conflict`. Empty link: for each `str.len` term, if the EqualityEngine/arith model fixes `len(s)=0`, emit lemma `(=> (= (str.len s) 0) (= s ""))` as a unit split (atom `(= s "")` guarded — emit the implication atom once).

- [ ] **Step 1: Write the failing test**

```rust
// x = "a" ++ y  AND  x != "a" ++ y  → UNSAT (same normal form, asserted distinct).
#[test]
fn disequality_on_equal_normal_forms_conflicts() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let mk = |c: &mut Context, n: &str| { let s = c.declare_fun(n, &[], str_s); c.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let x = mk(&mut ctx, "x"); let y = mk(&mut ctx, "y");
    let a = ctx.mk_string_const("a");
    let ay = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, y]).unwrap();
    let eq_atom = ctx.mk_eq(x, ay).unwrap();
    let diseq_atom = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, ay]).unwrap();
    let mut s = StrSolver::default();
    let mut eqe = EqualityEngine::default();
    let areg = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eqe, atoms: &areg };
    s.new_var(&mut cx, shinri_core::Var::new(0), eq_atom);
    s.new_var(&mut cx, shinri_core::Var::new(1), diseq_atom);
    // Merge x and (a++y) in the EqualityEngine to model the asserted equality, then assert distinct.
    let xn = cx.eq.intern(x); let an = cx.eq.intern(ay); let _ = cx.eq.merge(xn, an, EqJust::Definitional);
    s.test_force_diseq_true(diseq_atom);
    let mut conflicted = false;
    for _ in 0..16 {
        match s.check(&mut cx, Effort::Full) {
            TCheck::Conflict(_) => { conflicted = true; break; }
            TCheck::Split(_) => continue,
            TCheck::Sat => break,
        }
    }
    assert!(conflicted, "asserted distinct over equal normal forms is UNSAT");
}
```
Add `#[cfg(test)] pub fn test_force_diseq_true(&mut self, atom: TermId) { self.diseq_true.push(atom); }`.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str disequality_on_equal_normal_forms_conflicts`
Expected: FAIL — disequalities not checked yet.

- [ ] **Step 3: Implement disequality checking**

In `wordeq.rs`:
```rust
/// True if the two normal forms are atom-wise equal (definitely the same word).
pub fn nf_equal(terms: &mut Context, eq: &mut EqualityEngine, lhs: &[TermId], rhs: &[TermId]) -> bool {
    if lhs.len() != rhs.len() { return false; }
    lhs.iter().zip(rhs).all(|(&a, &b)| same(terms, eq, a, b))
}
```
In `lib.rs` `check`, after the equality loop, iterate `diseq_true`: compute both sides' normal forms; if `nf_equal`, return `TCheck::Conflict(just)` where `just` cites the disequality literal plus the equalities forcing the merge. (For v1, the trail-asserted disequality literal in the conflict set is sufficient for soundness; the Combiner expands EqLeaf antecedents.)

- [ ] **Step 4: Implement the empty-length link**

In `length.rs`, add an axiom form: for each `str.len(s)` term, the implication atom `(=> (= (str.len s) 0) (= s ""))`. Build with the core `Implies`/`Eq` ops and emit as a unit split once (track in `emitted_len_axioms`). Add it to `next_axiom`'s sequence after the defining equation.

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-str disequality_on_equal_normal_forms_conflicts` then `cargo test -p shinri-str`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/src/wordeq.rs crates/shinri-str/src/length.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): disequality same-word conflict + empty-length link lemma"
```

---

### Task 15: Fuel budget → sound `unknown`

**Files:**
- Modify: `crates/shinri-str/src/lib.rs` (`check` spends fuel per split; on exhaustion signal unknown)
- Modify: `crates/shinri-theory/src/solver_trait.rs` and `combiner.rs` — propagate an `unknown` signal from a theory up to the solver
- Test: `crates/shinri-str/src/lib.rs`

**Interfaces:**
- Produces: a way for `StrSolver::check` to signal `unknown` when fuel is exhausted. **Decision:** add `TCheck::Unknown` to the `TCheck` enum (the cleanest sound path). The Combiner maps `TCheck::Unknown` → a new `FinalCheck::Unknown` → `TheoryResult` such that the SAT solver reports `unknown`. If `TheoryResult` has no `Unknown`, add one and map it in `shinri-solver` to `SolveOutcome::Unknown`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn fuel_exhaustion_yields_unknown_not_hang() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let mk = |c: &mut Context, n: &str| { let s = c.declare_fun(n, &[], str_s); c.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
    let x = mk(&mut ctx, "x"); let y = mk(&mut ctx, "y");
    // x ++ y = y ++ x : classic diverging word equation.
    let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y]).unwrap();
    let r = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[y, x]).unwrap();
    let atom = ctx.mk_eq(l, r).unwrap();
    let mut s = StrSolver::default();
    s.test_set_fuel(5); // tiny budget
    let mut eq = EqualityEngine::default();
    let areg = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
    s.new_var(&mut cx, shinri_core::Var::new(0), atom);
    s.test_force_eq_true(atom);
    let mut got_unknown = false;
    for _ in 0..50 {
        match s.check(&mut cx, Effort::Full) {
            TCheck::Unknown => { got_unknown = true; break; }
            TCheck::Split(_) => continue,
            _ => break,
        }
    }
    assert!(got_unknown, "tiny fuel must force Unknown, never an infinite split loop");
}
```
Add `#[cfg(test)] pub fn test_set_fuel(&mut self, n: u32) { self.fuel = Fuel { remaining: n }; }`.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str fuel_exhaustion_yields_unknown_not_hang`
Expected: FAIL — `no variant Unknown`.

- [ ] **Step 3: Add `TCheck::Unknown` and thread it**

In `solver_trait.rs`, add `Unknown` to `TCheck`. In `combiner.rs`, add `FinalCheck::Unknown` and map every `self.<theory>.check(...)` match to handle `TCheck::Unknown => return FinalCheck::Unknown`. Map `FinalCheck::Unknown => TheoryResult::Unknown` in the `Theory::check` impl. If `shinri_sat::TheoryResult` lacks `Unknown`, add it; in `shinri-sat`'s solve loop, a theory `Unknown` makes `solve()` return a `SolveResult::Unknown`. In `shinri-solver`, map that to `SolveOutcome::Unknown`. Update existing `TCheck` matches (arrays test helpers, combiner tests) with an `Unknown` arm (`unreachable!()` where a theory never returns it).

- [ ] **Step 4: Spend fuel in `StrSolver::check`**

Before emitting any `Split` (length axiom or word-equation), call `if !self.fuel.spend() { return TCheck::Unknown; }`. Conflicts and Sat do not spend fuel.

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-str fuel_exhaustion_yields_unknown_not_hang` then `cargo test` (workspace).
Expected: PASS; fix any non-exhaustive `TCheck`/`TheoryResult`/`SolveResult` matches the compiler flags.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/ crates/shinri-theory/ crates/shinri-sat/ crates/shinri-solver/
git commit -m "feat(str): fuel budget with sound TCheck::Unknown propagation to SolveOutcome::Unknown"
```

---

### Task 16: `str.at` / `str.substr` reduction pre-pass

**Files:**
- Create: `crates/shinri-str/src/reduce.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (call the pre-pass on assertions before solving)
- Test: `crates/shinri-str/src/reduce.rs`

**Interfaces:**
- Produces: `pub fn reduce_assertions(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>` — returns assertions with every `str.at`/`str.substr` application replaced by a fresh String variable `m`, conjoined with the guard constraints defining `m`. Because the pre-pass introduces fresh variables and constraints, it returns a possibly-larger assertion list (the extra constraints appended).

**Semantics (SMT-LIB):**
- `str.substr(s,i,l)`: fresh `pre,mid,post`; `s = pre ++ mid ++ post`; if `0 ≤ i < len(s) ∧ l > 0` then `len(pre)=i ∧ len(mid)=min(l, len(s)-i)` and result `=mid`; else result `=""` (and `mid=""`). Encode `min` via two guarded cases. Encode guards with `Ite`/`Implies` over the length atoms (Int), which arith owns.
- `str.at(s,i)` ≡ `str.substr(s,i,1)`.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use crate::reduce::reduce_assertions;
    #[test]
    fn substr_is_replaced_by_fresh_var_with_guards() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = { let f = ctx.declare_fun("s", &[], str_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
        let i = ctx.mk_numeral(shinri_core::Rational::from_int(1.into()), ctx.int_sort());
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1.into()), ctx.int_sort());
        let ss = ctx.mk_app(Op::Builtin(BuiltinOp::StrSubstr), &[s, i, one]).unwrap();
        let lit = ctx.mk_string_const("b");
        let atom = ctx.mk_eq(ss, lit).unwrap();
        let out = reduce_assertions(&mut ctx, &[atom]);
        // The reduced set must contain MORE than one assertion (guards added) and
        // must no longer contain a raw str.substr application at the top of `atom`'s replacement.
        assert!(out.len() > 1, "guards must be appended");
        assert!(out.iter().all(|&a| !crate::reduce::contains_substr_or_at(&ctx, a)),
            "no str.substr/str.at may remain after reduction");
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str substr_is_replaced_by_fresh_var`
Expected: FAIL — module missing.

- [ ] **Step 3: Implement `reduce.rs`**

Implement a bottom-up rewrite: walk each assertion; whenever a `StrAt`/`StrSubstr` application is found, allocate fresh `mid` (the result var) and `pre`/`post`, build the guard constraints, replace the application with `mid` in the parent term (rebuild via `mk_app`), and collect the guard atoms into a side list. Provide `contains_substr_or_at`. Use `Ite` for the `min` and the in-range/out-of-range result. Return original (rewritten) assertions ++ guard atoms. Key builders:
```rust
// result = ite(in_range && l>0, mid, "")  with  s = pre ++ mid ++ post,
// len(pre)=ite(in_range, i, 0), len(mid)=ite(in_range && l>0, min_expr, 0)
// min_expr = ite(l <= len(s)-i, l, len(s)-i)
```
Build each with `mk_app(Op::Builtin(BuiltinOp::{Ite,Add,Sub,Le,Lt,Ge,And}), ...)` and `mk_eq`. (Write the full constraint set; no placeholders — expand `min` and both guards explicitly.)

- [ ] **Step 4: Call the pre-pass in the solver**

In `shinri-solver/src/lib.rs`, in `check_sat`, after collecting assertions and before routing, if any assertion contains a String op, replace `assertions` with `shinri_str::reduce::reduce_assertions(&mut self.ctx, &assertions)`. (Guard so non-string queries are untouched.)

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-str substr_is_replaced_by_fresh_var` then `cargo test -p shinri-str`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/src/reduce.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(str): desugar str.at/str.substr to concat+length guards in a pre-pass"
```

---

### Task 17: Model construction (concrete string values)

**Files:**
- Create: `crates/shinri-str/src/model.rs`
- Modify: `crates/shinri-str/src/lib.rs` (`StrSolver::model`)
- Test: `crates/shinri-str/src/model.rs`

**Interfaces:**
- Consumes: the arith model (lengths) via the shared `ModelBuilder`/`EqualityEngine`; `str_terms`, `eq_true`.
- Produces: `StrSolver::model(cx, m)` writes a `ModelVal::String(...)` for each free string variable: length read from the arith model of its `str.len` term; characters pinned by constant atoms in unified normal forms; free positions filled with `'A'` (U+0041); compound terms assembled by concatenation.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_theory::{AtomRegistry, EqualityEngine, ModelBuilder, TheoryCtx, TheorySolver};
    use shinri_theory::types::ModelVal;
    use crate::StrSolver;

    // With len(x)=2 fixed and no constant constraints, x's model is "AA".
    #[test]
    fn free_var_model_filled_with_default_char() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = { let f = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
        let lenx = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut m = ModelBuilder::default();
        // Seed the model with len(x) = 2 (as arith would).
        m.set(lenx, ModelVal::Num(shinri_core::Rational::from_int(2.into())));
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
        s.new_var(&mut cx, shinri_core::Var::new(0), lenx);
        s.test_force_str_term(x);
        s.model_with(&mut cx, &mut m);
        assert_eq!(m.get(x), Some(ModelVal::String("AA".into())));
    }
}
```
Add `#[cfg(test)] pub fn test_force_str_term(&mut self, t: TermId) { self.str_terms.insert(t); }` and a `pub fn model_with(&mut self, cx, m)` that `model` delegates to (so the test can pass a seeded `ModelBuilder`). Confirm `ModelBuilder` has `set`/`get`; if named differently, adjust.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str free_var_model_filled_with_default_char`
Expected: FAIL — `model` is a no-op.

- [ ] **Step 3: Implement `model.rs`**

```rust
use shinri_core::{BuiltinOp, Context, Op, TermId};
use shinri_theory::types::ModelVal;
use shinri_theory::{EqualityEngine, ModelBuilder};

const FILL: char = 'A';

fn len_of_in_model(terms: &mut Context, m: &ModelBuilder, t: TermId) -> usize {
    let lt = terms.mk_app(Op::Builtin(BuiltinOp::StrLen), &[t]).expect("ws");
    match m.get(lt) {
        Some(ModelVal::Num(r)) => r.to_i64().max(0) as usize, // adjust to Rational API
        _ => 0,
    }
}

/// Assign each free string variable a concrete word; fill unknown positions with FILL.
pub fn assign(terms: &mut Context, _eq: &mut EqualityEngine, str_terms: &[TermId], m: &mut ModelBuilder) {
    for &t in str_terms {
        if let Some(v) = terms.string_const_value(t) {
            m.set(t, ModelVal::String(v.to_string()));
            continue;
        }
        if m.get(t).is_some() { continue; }
        let n = len_of_in_model(terms, m, t);
        let word: String = std::iter::repeat(FILL).take(n).collect();
        m.set(t, ModelVal::String(word));
    }
}
```
(Map `r.to_i64()` to the actual `Rational` accessor; if `Rational` is exact, take the integer numerator when denominator is 1.) In `lib.rs`, `model` collects `str_terms` into a Vec and calls `model::assign`. For v1, constant-pinning of individual characters within partially-constrained variables is approximated by the fill default; the differential E2E witness check (Task 19) validates correctness and any failures sharpen this in a follow-up. **Note in the plan:** if a witness check fails because a constant char was not pinned, extend `assign` to walk `eq_true` normal forms and overlay constant atoms at their offsets — but only if Task 19 surfaces such a failure.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-str free_var_model_filled_with_default_char` then `cargo test -p shinri-str`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-str/src/model.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): construct concrete string models (lengths from arith, default-fill free positions)"
```

---

## PHASE E — Solver routing + end-to-end (`shinri-solver`)

### Task 18: String query detection, routing, fence, and model surfacing

**Files:**
- Create: `crates/shinri-solver/src/string_stage.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (route string queries; fence mixed; surface string model values)
- Test: `crates/shinri-solver/src/lib.rs`

**Interfaces:**
- Consumes: `shinri_str::StrSolver` (already the 4th Combiner theory), `shinri_str::reduce::reduce_assertions` (Task 16).
- Produces: `pub fn uses_strings(ctx, assertions) -> bool`; `pub fn fenced(ctx, assertions) -> bool` (true if strings mixed with BV/array-over-non-string/uninterpreted-function-over-string). String queries route to the Combiner path; fenced → `SolveOutcome::Unknown`.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn string_concat_equation_routes_and_solves_sat() {
    // (declare-fun x () String)(declare-fun y () String)
    // (assert (= (str.++ x "a") (str.++ "a" y)))  -> SAT (x=y="")
    let src = "(declare-fun x () String)(declare-fun y () String)\
               (assert (= (str.++ x \"a\") (str.++ \"a\" y)))(check-sat)";
    assert_eq!(run_outcome(src), SolveOutcome::Sat);
}

#[test]
fn string_length_contradiction_is_unsat() {
    // (assert (= (str.len x) 1)) (assert (= x "")) -> UNSAT
    let src = "(declare-fun x () String)\
               (assert (= (str.len x) 1))(assert (= x \"\"))(check-sat)";
    assert_eq!(run_outcome(src), SolveOutcome::Unsat);
}

#[test]
fn string_under_uninterpreted_function_is_unknown() {
    let src = "(declare-fun f (String) String)(declare-fun x () String)\
               (assert (= (f x) x))(check-sat)";
    assert_eq!(run_outcome(src), SolveOutcome::Unknown);
}
```
(Use the crate's existing `run_outcome`/parse+solve test harness — model on existing QF_ABV routing tests at the bottom of `lib.rs`.)

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-solver string_`
Expected: FAIL — no string routing/fence; queries may panic or return wrong outcome.

- [ ] **Step 3: Implement `string_stage.rs`**

Mirror `abv_stage.rs` detection/fence shape. `uses_strings`: any assertion contains a String-sorted subterm or `str.*` op. `fenced`: true if (a) a String-sorted term is an operand/result of an uninterpreted function (arity ≥ 1), or (b) BV ops co-occur with strings, or (c) arrays over non-(String,String) co-occur. (Strings + LIA + plain string vars are *not* fenced.)

- [ ] **Step 4: Route in `check_sat`**

In `lib.rs check_sat`, before the QF_ABV/BV checks, add:
```rust
        if crate::string_stage::uses_strings(&self.ctx, &assertions) {
            if crate::string_stage::fenced(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
            let reduced = shinri_str::reduce::reduce_assertions(&mut self.ctx, &assertions);
            assertions = reduced; // continue into the Combiner path with reduced assertions
        }
```
Ensure the Combiner path registers the (reduced) assertions and that `build_model` now includes string values (the 4th theory's `model`). After a SAT result, surface string values into the output `Model` the same way other theory values are surfaced (the `mb.iter()` loop already copies all assigned terms — confirm `ModelVal::String` flows through).

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-solver string_`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/src/string_stage.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(solver): route QF_S queries to the Combiner, fence mixed theories, surface string models"
```

---

### Task 19: Differential oracle vs z3 + witness checks + fence tests

**Files:**
- Create: `crates/shinri-solver/tests/qfs_differential.rs`
- Test: the file itself

**Interfaces:**
- Consumes: the full pipeline (parse → reduce → Combiner). Uses the `z3` binary like the existing QF_BV/QF_ABV differential tests (find and reuse that harness — search `tests/` for `z3`).

- [ ] **Step 1: Write the differential + witness + fence tests**

Model on the existing QF_ABV differential test. Generate well-sorted QF_SLIA-core formulas (string vars, concat chains, literals, `str.len` constraints linking to Int, `str.at`/`str.substr`, equalities and disequalities). For each:
```rust
// Pseudocode shape — implement against the existing z3 harness:
for seed in 0..N {
    let smt = gen_qfs_formula(seed);
    let ours = solve_with_shinri(&smt);
    let z3 = solve_with_z3(&smt);
    match (ours, z3) {
        (SolveOutcome::Unknown, _) => {}          // fuel/fence unknown: non-disagreement
        (a, b) => assert_eq!(a, b, "seed {seed}: {smt}"), // SAT/UNSAT must agree
    }
    // Witness: on our SAT, substitute the model and re-check with z3 that it satisfies.
    if ours == SolveOutcome::Sat { assert!(z3_model_satisfies(&smt, &shinri_model)); }
}
```
Add explicit targeted cases: prefix-mismatch UNSAT, `x="ab"` SAT with model, ROW-of-length contradictions, disequality witnessing, `str.substr` in/out-of-range, and three fence cases (BV+string, array-over-int+string, UF-over-string) returning Unknown.

- [ ] **Step 2: Run to verify they fail (where unimplemented behavior remains)**

Run: `cargo test -p shinri-solver --test qfs_differential`
Expected: Most pass; any disagreement points to a bug. If a witness check fails due to unpinned constant characters, implement the `assign` overlay noted in Task 17 Step 3, then re-run.

- [ ] **Step 3: Fix any disagreements**

For each disagreement, use systematic-debugging: minimize the seed, inspect the calculus step, fix in the relevant module (`wordeq`/`length`/`reduce`/`model`), keep the failing seed as a regression unit test in the owning crate.

- [ ] **Step 4: Run the full suite**

Run: `cargo test` (workspace)
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): QF_S differential oracle vs z3 + witness + fence tests"
```

---

## Self-Review Notes (author)

- **Spec §1 scope** → Tasks 1–4 (sort/ops/literals/parser), 16 (`str.at`/`str.substr`), 18 (routing/fence). ✓
- **Spec §2 approach (lazy, no new path, N-O Int seam)** → Tasks 7 (4th slot + N-O gate), 8–9 (shared len terms). ✓
- **Spec §4.1 length skeleton** → Task 9; **§4.2 normal forms** → Task 10; **§4.3 F-split** → Tasks 12–13; **§4.4 disequalities** → Task 14; **§4.5 fuel** → Task 15. ✓
- **Spec §5 reductions** → Task 16. **§6 model** → Task 17. **§7 soundness/termination** → Tasks 14–15 (conflict/Unknown). **§8 testing** → Task 19 (+ per-task unit tests). ✓
- **Type consistency:** `StrSolver`, `Fuel`, `Trail`, `StepResult`, `resolve_equation`, `normal_form`, `next_axiom`, `reduce_assertions`, `assign`, `TCheck::Unknown`, `Owner::String`, `ModelVal::String`, `Combiner<E,A,R,S>` used consistently across tasks.
- **Known approximation (flagged, not a placeholder):** Task 17 model fill may need the constant-overlay refinement; Task 19 Step 2/3 explicitly drives that based on witness-check evidence. The conflict/soundness path does not depend on it.
- **API-name caveats** are called out inline where the exact `EqualityEngine`/`AtomRegistry`/`Lit`/`Rational`/`ModelBuilder` method names must be confirmed against the source at implementation time (e.g. `rep_term`, `atom_of`, `is_positive`, `to_i64`, `set`/`get`). These are real methods to bind, not undefined work.
