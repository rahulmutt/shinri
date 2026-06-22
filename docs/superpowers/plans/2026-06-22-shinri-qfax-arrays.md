# QF_AX (Arrays) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add the QF_AX theory (extensional arrays, non-extensional baseline) to shinri: `select`/`store` over uninterpreted index/element sorts, decided over EUF congruence plus lazy read-over-write (ROW) lemmas, with array-to-array (dis)equality fenced to a sound `unknown`.

**Architecture:** `select`/`store` become congruence-eligible builtin function symbols (so the shared `EqualityEngine` gives congruence for free via EUF's op-generic `add_term`). A new `shinri-arrays` crate implements `TheorySolver`, contributing nothing but on-demand ROW lemmas emitted as positive-atom clauses through the existing `TCheck::Split` → `TheoryResult::SplitAtoms` → `bind_fresh` path. The two-slot `Combiner<E, A>` is generalized to a three-slot `Combiner<E, A, R>`; arrays is a *congruence-only* Nelson–Oppen participant (all equality-exchange seam methods are no-ops).

**Tech Stack:** Rust (workspace of crates `shinri-core`, `shinri-parser`, `shinri-euf`, `shinri-theory`, `shinri-arith`, `shinri-sat`, `shinri-solver`, new `shinri-arrays`). Tests use `cargo test`; the differential oracle shells out to `z3` via the `easy-smt` crate.

## Global Constraints

- **Soundness is existential.** Anything not decided exactly is refused at atom-registration time → top-level `unknown`. Never guess an arrangement; split and let DPLL(T) decide.
- **No `Rc`/`RefCell`/`Arc`.** Index/arena over smart pointers; sub-theories receive `&mut TheoryCtx`, never shared ownership.
- **One shared source of equality truth:** the single `EqualityEngine`. Arrays owns no equality state.
- **Backtracking discipline:** state that depends on the SAT assignment uses the `UndoLog`/`push`/`pop` discipline. (Arrays' watched-term and lemma state is *assignment-independent and monotone*, so its `push`/`pop` are no-ops — see Task 3.)
- **TDD:** failing test → minimal impl → green → commit. Frequent commits, one per task minimum.
- **Theory IDs:** EUF = 1, Arith = 2. **Arrays = 3** (`const THEORY_ID: u16 = 3`).
- **Extensionality and QF_ALIA are out of scope** and must be fenced to `unknown`, never wrong-answered.

---

## File Structure

- `crates/shinri-core/src/sort.rs` — add `SortNode::Array(SortId, SortId)`.
- `crates/shinri-core/src/term.rs` — add `BuiltinOp::Select`, `BuiltinOp::Store`.
- `crates/shinri-core/src/context.rs` — `array_sort()` constructor + `check_builtin` arms for Select/Store.
- `crates/shinri-parser/src/parser.rs` — parse `(Array I E)` sort + `select`/`store` applications.
- `crates/shinri-arrays/` — **new crate**: `Arrays` `TheorySolver` (ROW lemma-on-demand).
- `crates/shinri-theory/src/types.rs` — add `Owner::Arrays`.
- `crates/shinri-theory/src/atom.rs` — `classify` array routing + extensionality/QF_ALIA fences.
- `crates/shinri-theory/src/combiner.rs` — generalize `Combiner<E, A>` → `Combiner<E, A, R>`.
- `crates/shinri-solver/src/{lib.rs,tseitin.rs}` — 3-slot wiring; `array_sort` API; `Owner::Arrays` stats arm.
- `crates/shinri-solver/tests/qfax_e2e.rs`, `crates/shinri-solver/tests/qfax_oracle.rs` — new tests.

---

## Task 1: Core — Array sort & select/store operators

**Files:**
- Modify: `crates/shinri-core/src/sort.rs:5-11`
- Modify: `crates/shinri-core/src/term.rs:21-40`
- Modify: `crates/shinri-core/src/context.rs` (`check_builtin` ~152-253; add `array_sort` near `declare_sort` ~76)
- Test: `crates/shinri-core/src/context.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Produces:
  - `SortNode::Array(SortId /*index*/, SortId /*elem*/)`
  - `BuiltinOp::Select`, `BuiltinOp::Store`
  - `Context::array_sort(&mut self, index: SortId, elem: SortId) -> SortId`
  - `Context::mk_app(Op::Builtin(BuiltinOp::Select), &[arr, idx]) -> Result<TermId, SortError>` yielding element sort
  - `Context::mk_app(Op::Builtin(BuiltinOp::Store), &[arr, idx, elt]) -> Result<TermId, SortError>` yielding the array sort

- [ ] **Step 1: Write the failing test**

In `crates/shinri-core/src/context.rs` test module:

```rust
#[test]
fn array_select_store_sorts() {
    let mut ctx = Context::new();
    let idx = ctx.declare_sort("I");
    let elem = ctx.declare_sort("E");
    let arr_sort = ctx.array_sort(idx, elem);

    let a = ctx.mk_app(Op::Uninterpreted(ctx_decl(&mut ctx, "a", arr_sort)), &[]).unwrap();
    let i = ctx.mk_app(Op::Uninterpreted(ctx_decl(&mut ctx, "i", idx)), &[]).unwrap();
    let e = ctx.mk_app(Op::Uninterpreted(ctx_decl(&mut ctx, "e", elem)), &[]).unwrap();

    // (store a i e) : (Array I E)
    let st = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
    assert_eq!(ctx.sort_of(st), arr_sort);
    // (select (store a i e) i) : E
    let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, i]).unwrap();
    assert_eq!(ctx.sort_of(sel), elem);
    // wrong index sort is rejected
    let e_as_idx = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, e]);
    assert!(e_as_idx.is_err());
}

// helper local to the test module
fn ctx_decl(ctx: &mut Context, name: &str, s: SortId) -> shinri_core::SymbolId {
    ctx.declare_fun(name, &[], s)
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core array_select_store_sorts`
Expected: FAIL to compile — `no variant Array`, `no variant Select`, `no method array_sort`.

- [ ] **Step 3: Add the enum variants**

In `crates/shinri-core/src/sort.rs`:

```rust
pub enum SortNode {
    Bool,
    Int,
    Real,
    Uninterpreted(SymbolId),
    /// (Array <index> <element>)
    Array(crate::ids::SortId, crate::ids::SortId),
}
```

(Use whatever path makes `SortId` in scope — match the import style already in `sort.rs`.)

In `crates/shinri-core/src/term.rs`, append to `BuiltinOp` after `Gt`:

```rust
    // Arrays
    Select,
    Store,
```

- [ ] **Step 4: Add `array_sort` constructor**

In `crates/shinri-core/src/context.rs`, next to `declare_sort`:

```rust
pub fn array_sort(&mut self, index: SortId, elem: SortId) -> SortId {
    self.intern_sort(SortNode::Array(index, elem))
}
```

- [ ] **Step 5: Add sort-checking arms**

In `check_builtin`, add arms before the closing brace of the `match b`:

```rust
Select => {
    expect_arity(args, 2)?;
    let (idx, elem) = match self.sort_node(self.sort_of(args[0])) {
        SortNode::Array(i, e) => (*i, *e),
        _ => return Err(SortError::NotApplicable),
    };
    let found = self.sort_of(args[1]);
    if found != idx {
        return Err(SortError::Mismatch { expected: idx, found });
    }
    Ok(elem)
}
Store => {
    expect_arity(args, 3)?;
    let arr = self.sort_of(args[0]);
    let (idx, elem) = match self.sort_node(arr) {
        SortNode::Array(i, e) => (*i, *e),
        _ => return Err(SortError::NotApplicable),
    };
    let fi = self.sort_of(args[1]);
    if fi != idx {
        return Err(SortError::Mismatch { expected: idx, found: fi });
    }
    let fe = self.sort_of(args[2]);
    if fe != elem {
        return Err(SortError::Mismatch { expected: elem, found: fe });
    }
    Ok(arr)
}
```

Ensure `Select`/`Store` are brought into scope by the existing `use BuiltinOp::*;` at the top of `check_builtin`.

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p shinri-core array_select_store_sorts`
Expected: PASS.

- [ ] **Step 7: Run the whole crate to catch non-exhaustive matches**

Run: `cargo test -p shinri-core`
Expected: PASS. If any `match` over `BuiltinOp` or `SortNode` elsewhere in the crate fails to compile (e.g. a printer), add the missing arms minimally (Select→`"select"`, Store→`"store"`, Array→print `(Array I E)`).

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-core
git commit -m "feat(core): Array sort + select/store builtin ops with sort-checking"
```

---

## Task 2: Parser — `(Array I E)` sort and `select`/`store` terms

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs` (`parse_sort` ~132-146; `builtin_for` ~154-174; `apply_builtin` ~389-488)
- Test: `crates/shinri-parser/src/parser.rs` (test module) or `crates/shinri-parser/tests/`

**Interfaces:**
- Consumes: `Context::array_sort`, `BuiltinOp::Select`, `BuiltinOp::Store` (Task 1).
- Produces: parser accepts `(Array I E)` as a sort and `(select a i)`, `(store a i e)` as terms.

- [ ] **Step 1: Write the failing test**

Add to the parser test module (mirror the existing parse round-trip tests):

```rust
#[test]
fn parses_array_sort_and_select_store() {
    let src = "\
(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun i () I)
(declare-fun e () E)
(assert (= (select (store a i e) i) e))
(check-sat)";
    let mut ctx = shinri_core::Context::new();
    let mut p = Parser::new(src);
    // Drive all commands; assert none produce a parse diagnostic.
    while let Some(cmd) = p.next_command(&mut ctx) {
        cmd.expect("array sort / select / store must parse");
    }
}
```

(If `next_command`'s signature differs, follow the exact shape used by the existing parser tests in this file.)

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser parses_array_sort_and_select_store`
Expected: FAIL — `unknown sort Array` (or an "unexpected token (" at the sort position) and unknown function `select`/`store`.

- [ ] **Step 3: Parse the `(Array I E)` compound sort**

Replace `parse_sort` so it handles both atom sorts and the `(Array …)` compound. The current body calls `self.expect_symbol()`; change it to look at the next token:

```rust
fn parse_sort(&mut self, ctx: &mut Context) -> Result<SortId, Diagnostic> {
    // Compound sort: (Array <index> <element>)
    if self.eat_lparen() {
        let (head, sp) = self.expect_symbol()?;
        let s = match head.as_str() {
            "Array" => {
                let index = self.parse_sort(ctx)?;
                let elem = self.parse_sort(ctx)?;
                ctx.array_sort(index, elem)
            }
            other => {
                return Err(Diagnostic::new(sp, format!("unsupported parameterized sort {other}")));
            }
        };
        self.expect_rparen()?;
        return Ok(s);
    }
    let (name, sp) = self.expect_symbol()?;
    match name.as_str() {
        "Bool" => Ok(ctx.bool_sort()),
        "Int" => Ok(ctx.int_sort()),
        "Real" => Ok(ctx.real_sort()),
        other => self
            .env
            .lookup_sort(other)
            .ok_or_else(|| Diagnostic::new(sp, format!("unknown sort {other}"))),
    }
}
```

Use the existing token helpers. If `eat_lparen`/`expect_rparen` do not already exist, implement `eat_lparen` as a peeking consume of `Token::LParen` (return `bool`) and reuse the parser's existing right-paren expectation helper (the same one `parse_compound` uses). Remove the now-inaccurate `#[allow(dead_code)]` and the "out of scope → diagnostic" doc note.

- [ ] **Step 4: Register `select`/`store` builtins**

In `builtin_for`, add:

```rust
            "select" => Select,
            "store" => Store,
```

- [ ] **Step 5: Build select/store applications**

In `apply_builtin`, add arms (fixed arity, plain `mk`):

```rust
            BuiltinOp::Select => {
                Self::expect_args(&args, 2, &sp)?;
                Self::mk(ctx, Op::Builtin(BuiltinOp::Select), &args, &sp)
            }
            BuiltinOp::Store => {
                Self::expect_args(&args, 3, &sp)?;
                Self::mk(ctx, Op::Builtin(BuiltinOp::Store), &args, &sp)
            }
```

If there is no `expect_args` arity helper in this file, inline the check:

```rust
                if args.len() != 2 {
                    return Err(Diagnostic::new(sp.clone(), "select expects 2 arguments"));
                }
```

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p shinri-parser parses_array_sort_and_select_store`
Expected: PASS.

- [ ] **Step 7: Run crate + commit**

Run: `cargo test -p shinri-parser`
Expected: PASS.

```bash
git add crates/shinri-parser
git commit -m "feat(parser): parse (Array I E) sorts and select/store applications"
```

---

## Task 3: `shinri-arrays` crate — ROW lemma-on-demand `TheorySolver`

**Files:**
- Create: `crates/shinri-arrays/Cargo.toml`
- Create: `crates/shinri-arrays/src/lib.rs`
- Modify: `Cargo.toml` (workspace members)
- Test: `crates/shinri-arrays/src/lib.rs` (`#[cfg(test)]`)

**Interfaces:**
- Consumes: `shinri_theory::{TheorySolver, TheoryCtx, TCheck, Explainer}`, `shinri_theory::types::EqLeaf`, `shinri_theory::ModelBuilder`, `shinri_core::{Context, Op, BuiltinOp, TermId, TermNode, Var, Lit, TheoryJust}`, `shinri_sat::Effort`. From `TheoryCtx`: `cx.terms: &mut Context`, `cx.eq: &mut EqualityEngine` with `intern(TermId)->ENodeId`, `find(ENodeId)->ENodeId`, `are_equal(ENodeId, ENodeId)->bool`.
- Produces: `pub struct Arrays` implementing `TheorySolver` with `const THEORY_ID: u16 = 3`. Its `check` returns `TCheck::Split(vec![..])` carrying ROW lemma clauses; all N-O seam methods are defaulted no-ops.

**Algorithm (engine-state-driven, no emitted-set needed).** On `check(Full)`, for every watched `select(arr, j)` and every watched `store(b, i, e)` with `arr ≡ store(b,i,e)` in the engine:
- if `i ≡ j` and `not(sel ≡ e)` → emit unit clause `[ (= sel e) ]` (ROW-1).
- else if `not(i ≡ j)` → let `selbj = select(b, j)`; if `not(sel ≡ selbj)` emit `[ (= i j), (= sel selbj) ]` (ROW-2; the `(= i j)` disjunct lets DPLL(T) decide the index arrangement, and the `i ≡ j` branch re-enters ROW-1 next round).
Emit **one** lemma per `check` and return immediately; otherwise `TCheck::Sat`. Because every lemma either merges classes (finite, monotone) or forces a decision over the finite, hash-consed set of `select`/`store`/`select(b,j)` terms, the fixpoint terminates. Soundness: every clause is a valid ground `ArraysEx` axiom instance.

- [ ] **Step 1: Create the crate skeleton**

`crates/shinri-arrays/Cargo.toml`:

```toml
[package]
name = "shinri-arrays"
version = "0.1.0"
edition = "2021"

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-theory = { path = "../shinri-theory" }
shinri-sat = { path = "../shinri-sat" }
rustc-hash = "2"
```

(Match the exact `rustc-hash`/edition versions used by sibling crates like `shinri-euf/Cargo.toml`.)

Add `"crates/shinri-arrays"` to the `members` list in the workspace root `Cargo.toml`.

- [ ] **Step 2: Write the failing unit test (ROW-1 conflict witness)**

`crates/shinri-arrays/src/lib.rs` (test module at bottom). This builds `select(store(a,i,e), i)` and asserts the solver emits a `Split` forcing `select(store(a,i,e),i) = e`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};
    use shinri_sat::Effort;

    fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
        let sym = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn row1_emits_select_equals_stored_value() {
        let mut ctx = Context::new();
        let i_s = ctx.declare_sort("I");
        let e_s = ctx.declare_sort("E");
        let arr_s = ctx.array_sort(i_s, e_s);
        let a = uconst(&mut ctx, "a", arr_s);
        let i = uconst(&mut ctx, "i", i_s);
        let e = uconst(&mut ctx, "e", e_s);
        let st = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, i]).unwrap();
        // an equality atom carrying the select; arrays watches it
        let atom = ctx.mk_eq(sel, e).unwrap();

        let mut arrays = Arrays::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        arrays.new_var(&mut cx, shinri_core::Var::new(0), atom);

        match arrays.check(&mut cx, Effort::Full) {
            TCheck::Split(atoms) => {
                // The lemma forces sel = e (the same eq term, or a fresh equal one).
                assert!(!atoms.is_empty(), "ROW-1 must emit a lemma");
            }
            other => panic!("expected Split, got {other:?}"),
        }
        // Once sel and e are merged, no further lemma is emitted (fixpoint).
        let sn = cx.eq.intern(sel);
        let en = cx.eq.intern(e);
        let _ = cx.eq.merge(sn, en, shinri_theory::EqJust::Asserted /*or the crate's input-just ctor*/);
        assert!(matches!(arrays.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}
```

(Adjust `Var::new`, `EqJust` constructor, and `TCheck` `Debug` derive to the exact names in `shinri-theory`; if `TCheck` is not `Debug`, match without the `{other:?}`.)

- [ ] **Step 3: Run test to verify it fails**

Run: `cargo test -p shinri-arrays row1_emits_select_equals_stored_value`
Expected: FAIL to compile (`Arrays` does not exist).

- [ ] **Step 4: Implement the `Arrays` solver**

`crates/shinri-arrays/src/lib.rs` (above the test module):

```rust
//! QF_AX array theory: lazy read-over-write (ROW) lemma-on-demand over the
//! shared EqualityEngine. Owns no equality state; emits ROW axiom instances as
//! positive-atom clauses via TCheck::Split. Congruence-only N-O participant.

use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Op, TermId, TermNode, Var, Lit, TheoryJust};
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};
use shinri_theory::types::EqLeaf;
use shinri_sat::Effort;

#[derive(Default)]
pub struct Arrays {
    /// Watched select(arr, idx) terms. Monotone (assignment-independent).
    selects: FxHashSet<TermId>,
    /// Watched store(arr, idx, elt) terms. Monotone.
    stores: FxHashSet<TermId>,
}

impl Arrays {
    /// Walk an atom's term DAG, recording every select/store sub-application.
    fn collect(&mut self, cx: &TheoryCtx, t: TermId) {
        let (op, kids) = match cx.terms.term_node(t) {
            TermNode::App { op, args, .. } => (*op, cx.terms.children(*args).to_vec()),
            TermNode::Const { .. } => return,
        };
        match op {
            Op::Builtin(BuiltinOp::Select) => { self.selects.insert(t); }
            Op::Builtin(BuiltinOp::Store) => { self.stores.insert(t); }
            _ => {}
        }
        for k in kids {
            self.collect(cx, k);
        }
    }

    /// (op, children) of an App term, or None.
    fn app<'a>(cx: &TheoryCtx, t: TermId) -> Option<(Op, Vec<TermId>)> {
        match cx.terms.term_node(t) {
            TermNode::App { op, args, .. } => Some((*op, cx.terms.children(*args).to_vec())),
            TermNode::Const { .. } => None,
        }
    }

    fn equal(cx: &mut TheoryCtx, a: TermId, b: TermId) -> bool {
        let an = cx.eq.intern(a);
        let bn = cx.eq.intern(b);
        cx.eq.are_equal(an, bn)
    }
}

impl TheorySolver for Arrays {
    const THEORY_ID: u16 = 3;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        // Borrow cx immutably for the walk.
        self.collect(&*cx, atom);
    }

    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
        None
    }

    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        None
    }

    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        let selects: Vec<TermId> = self.selects.iter().copied().collect();
        let stores: Vec<TermId> = self.stores.iter().copied().collect();
        for sel in selects {
            let Some((_, sel_args)) = Self::app(cx, sel) else { continue };
            let (arr, j) = (sel_args[0], sel_args[1]);
            for &st in &stores {
                if !Self::equal(cx, arr, st) {
                    continue;
                }
                let Some((_, st_args)) = Self::app(cx, st) else { continue };
                let (b, i, e) = (st_args[0], st_args[1], st_args[2]);
                if Self::equal(cx, i, j) {
                    // ROW-1: sel = e
                    if !Self::equal(cx, sel, e) {
                        let lemma = cx.terms.mk_eq(sel, e).expect("well-sorted");
                        return TCheck::Split(vec![lemma]);
                    }
                } else {
                    // ROW-2: (i = j) ∨ (sel = select(b, j))
                    let selbj = cx
                        .terms
                        .mk_app(Op::Builtin(BuiltinOp::Select), &[b, j])
                        .expect("well-sorted");
                    if !Self::equal(cx, sel, selbj) {
                        let eqij = cx.terms.mk_eq(i, j).expect("well-sorted");
                        let eqsel = cx.terms.mk_eq(sel, selbj).expect("well-sorted");
                        return TCheck::Split(vec![eqij, eqsel]);
                    }
                }
            }
        }
        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
        // Arrays cites no equalities of its own; ROW lemma atoms are EUF-owned.
    }

    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn push(&mut self) {}        // monotone, assignment-independent state
    fn pop(&mut self, _level: usize) {}
}
```

Notes for the implementer:
- `new_var` calls `self.collect(&*cx, atom)`. `collect` only reads `cx.terms`; if the borrow checker objects to `&*cx`, split `collect` to take `terms: &Context` directly and pass `cx.terms`.
- The defaulted N-O seam methods (`shared_arith_terms`, `entailed_equalities`, `consume_interface_equality`, `ensure_shared_var`, `has_uf_application`, `mint_eq_tag`, `model_equal_shared_pairs`) are inherited as no-ops — do **not** override them. (Confirm the trait provides defaults for all of them; if `has_uf_application`/`model_equal_shared_pairs` lack defaults, add trivial overrides returning `false`/`Vec::new()`.)

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-arrays row1_emits_select_equals_stored_value`
Expected: PASS.

- [ ] **Step 6: Add the ROW-2 (undecided index) unit test**

```rust
#[test]
fn row2_emits_disjunctive_split_when_index_undecided() {
    let mut ctx = Context::new();
    let i_s = ctx.declare_sort("I");
    let e_s = ctx.declare_sort("E");
    let arr_s = ctx.array_sort(i_s, e_s);
    let a = uconst(&mut ctx, "a", arr_s);
    let i = uconst(&mut ctx, "i", i_s);
    let j = uconst(&mut ctx, "j", i_s);
    let e = uconst(&mut ctx, "e", e_s);
    let v = uconst(&mut ctx, "v", e_s);
    let st = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
    let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, j]).unwrap();
    let atom = ctx.mk_eq(sel, v).unwrap();

    let mut arrays = Arrays::default();
    let mut eq = EqualityEngine::default();
    let atoms = AtomRegistry::default();
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
    arrays.new_var(&mut cx, shinri_core::Var::new(0), atom);

    match arrays.check(&mut cx, Effort::Full) {
        TCheck::Split(atoms) => assert_eq!(atoms.len(), 2, "ROW-2 split has two disjuncts"),
        other => panic!("expected 2-atom Split, got {other:?}"),
    }
}
```

Run: `cargo test -p shinri-arrays`
Expected: PASS (both tests).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-arrays Cargo.toml
git commit -m "feat(arrays): shinri-arrays ROW lemma-on-demand TheorySolver (QF_AX)"
```

---

## Task 4: Combiner classification — `Owner::Arrays` + extensionality/QF_ALIA fences

**Files:**
- Modify: `crates/shinri-theory/src/types.rs:21-27` (`Owner` enum)
- Modify: `crates/shinri-theory/src/atom.rs` (`classify` ~15-44; add array detection helpers)
- Test: `crates/shinri-theory/src/atom.rs` (`#[cfg(test)]`)

**Interfaces:**
- Consumes: `SortNode::Array`, `BuiltinOp::{Select,Store}` (Task 1).
- Produces: `Owner::Arrays`; `classify` returns `Ok(Owner::Arrays)` for QF_AX atoms containing `select`/`store` over uninterpreted index/element sorts, and `Err(Unsupported)` for array-sorted `Eq`/`Distinct` (extensionality) and for any `select`/`store` touching arith sorts (QF_ALIA, out of scope).

- [ ] **Step 1: Write failing tests**

In `crates/shinri-theory/src/atom.rs` test module:

```rust
#[test]
fn classify_array_read_is_arrays() {
    let mut ctx = Context::new();
    let i_s = ctx.declare_sort("I");
    let e_s = ctx.declare_sort("E");
    let arr_s = ctx.array_sort(i_s, e_s);
    let a = uconst(&mut ctx, "a", arr_s);
    let i = uconst(&mut ctx, "i", i_s);
    let e = uconst(&mut ctx, "e", e_s);
    let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
    let atom = ctx.mk_eq(sel, e).unwrap();
    assert_eq!(classify(&ctx, atom), Ok(Owner::Arrays));
}

#[test]
fn classify_array_equality_is_fenced() {
    let mut ctx = Context::new();
    let i_s = ctx.declare_sort("I");
    let e_s = ctx.declare_sort("E");
    let arr_s = ctx.array_sort(i_s, e_s);
    let a = uconst(&mut ctx, "a", arr_s);
    let b = uconst(&mut ctx, "b", arr_s);
    let atom = ctx.mk_eq(a, b).unwrap();
    assert!(classify(&ctx, atom).is_err(), "extensionality must be fenced");
}
```

(Add a local `uconst` helper to the test module if not present, mirroring Task 3 Step 2.)

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-theory classify_array`
Expected: FAIL — `no variant Owner::Arrays`.

- [ ] **Step 3: Add the `Owner::Arrays` variant**

In `crates/shinri-theory/src/types.rs`:

```rust
pub enum Owner {
    Euf,
    Arith,
    Shared,
    Arrays,
}
```

- [ ] **Step 4: Add array detection + fences to `classify`**

In `crates/shinri-theory/src/atom.rs`, add helpers and wire them into `classify` right after the nonlinear-mul check:

```rust
/// True if any subterm of `t` is a select/store application.
fn contains_array_op(terms: &Context, t: TermId) -> bool {
    match terms.term_node(t) {
        TermNode::App { op, args, .. } => {
            if matches!(op, Op::Builtin(BuiltinOp::Select | BuiltinOp::Store)) {
                return true;
            }
            terms.children(*args).iter().any(|&c| contains_array_op(terms, c))
        }
        TermNode::Const { .. } => false,
    }
}

fn is_array_sorted(terms: &Context, t: TermId) -> bool {
    matches!(terms.sort_node(terms.sort_of(t)), SortNode::Array(_, _))
}

/// True if any select/store subterm touches an arith (Int/Real) index or element
/// sort — that is QF_ALIA, out of scope for this baseline → fence.
fn array_touches_arith(terms: &Context, t: TermId) -> bool {
    let int_s = terms.int_sort();
    let real_s = terms.real_sort();
    fn walk(terms: &Context, t: TermId, int_s: SortId, real_s: SortId) -> bool {
        match terms.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids = terms.children(*args);
                if matches!(op, Op::Builtin(BuiltinOp::Select | BuiltinOp::Store)) {
                    let s = terms.sort_of(t);
                    if s == int_s || s == real_s {
                        return true;
                    }
                    // index sort of the array operand
                    if let SortNode::Array(idx, elem) = terms.sort_node(terms.sort_of(kids[0])) {
                        if *idx == int_s || *idx == real_s || *elem == int_s || *elem == real_s {
                            return true;
                        }
                    }
                }
                kids.iter().any(|&c| walk(terms, c, int_s, real_s))
            }
            TermNode::Const { .. } => false,
        }
    }
    walk(terms, t, int_s, real_s)
}
```

Then in `classify`, after the `contains_nonlinear_mul` guard and before the `match terms.term_node(atom)`:

```rust
    // Extensionality fence: array-to-array (dis)equality is out of scope.
    if let TermNode::App { op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct), args, .. } =
        terms.term_node(atom)
    {
        if terms.children(*args).iter().any(|&c| is_array_sorted(terms, c)) {
            return Err(Unsupported(atom));
        }
    }
    // QF_ALIA fence: arrays over arith index/element sorts are out of scope.
    if array_touches_arith(terms, atom) {
        return Err(Unsupported(atom));
    }
    // QF_AX: any remaining atom mentioning select/store is owned by Arrays
    // (EUF still interns the terms for congruence — see the Owner::Arrays
    // routing in the Combiner).
    if contains_array_op(terms, atom) {
        return Ok(Owner::Arrays);
    }
```

Ensure `SortNode` and `SortId` are imported in `atom.rs`.

- [ ] **Step 5: Run tests + crate**

Run: `cargo test -p shinri-theory classify_array`
Expected: PASS.

Run: `cargo test -p shinri-theory`
Expected: compile errors only where a `match Owner { … }` is now non-exhaustive — these are fixed in Task 5. If `atom.rs`'s own tests/build fail solely on those downstream matches, that is expected; the `classify_*` tests themselves must pass. (If the crate cannot build at all yet, proceed to Task 5 and run the combined build there.)

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-theory/src/types.rs crates/shinri-theory/src/atom.rs
git commit -m "feat(theory): classify select/store atoms as Owner::Arrays; fence extensionality + QF_ALIA"
```

---

## Task 5: Combiner — generalize `Combiner<E, A>` → `Combiner<E, A, R>`

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs` (struct 24-37; `with_context`/`Default` 39-70; routing in `register_atom` 73-124, `assert` 127-155, `bind_fresh` 196-220; `drive_final_check` ~255-451; `explain` resolve ~564-584; `build_model` 531-560; `push`/`pop`)
- Test: `crates/shinri-theory/src/combiner.rs` (existing stub-based tests; add an arrays stub test)

**Interfaces:**
- Consumes: `Owner::Arrays` (Task 4); `Arrays` solver type (Task 3, but here exercised via stubs).
- Produces: `pub struct Combiner<E: TheorySolver, A: TheorySolver, R: TheorySolver>` with field `arrays: R`; accessor `arrays_mut(&mut self) -> &mut R`; `Owner::Arrays` routed to **both** `euf` (congruence interning) and `arrays` (lemma watching); `arrays.check(Full)` integrated into the N-O fixpoint with its `TCheck::Split` lifted to `FinalCheck::Split`.

- [ ] **Step 1: Add the third type parameter and field**

Update the struct and impls. Every `impl<E: TheorySolver, A: TheorySolver>` becomes `impl<E: TheorySolver, A: TheorySolver, R: TheorySolver>`, and `Combiner<E, A>` becomes `Combiner<E, A, R>` throughout (struct def, `Default`, `with_context`, the `Theory` impl, and the inherent impls). Add the field and constructor line:

```rust
pub struct Combiner<E: TheorySolver, A: TheorySolver, R: TheorySolver> {
    terms: Context,
    eq: EqualityEngine,
    atoms: AtomRegistry,
    iface: InterfaceSet,
    euf: E,
    arith: A,
    arrays: R,            // NEW
    level: usize,
    merges: Vec<MergeEvent>,
    pending_conflict: Option<Vec<crate::types::EqLeaf>>,
    cert: CertLog,
}
```

In `with_context`, add `arrays: R::default(),`. Add accessor next to `arith_mut`:

```rust
pub fn arrays_mut(&mut self) -> &mut R {
    &mut self.arrays
}
```

- [ ] **Step 2: Route `Owner::Arrays` in `register_atom`, `assert`, `bind_fresh`**

`register_atom` — add arm (fan out to EUF for congruence + Arrays for watching; no purification):

```rust
        Owner::Arrays => {
            let mut cx = TheoryCtx {
                terms: &mut self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            self.euf.new_var(&mut cx, v, atom);
            self.arrays.new_var(&mut cx, v, atom);
        }
```

`assert` — add arm:

```rust
            Owner::Arrays => {
                let e = self.euf.assert(&mut cx, lit);
                let r = self.arrays.assert(&mut cx, lit);
                e.or(r)
            }
```

`bind_fresh` — add arm (mirrors `register_atom`):

```rust
            Owner::Arrays => {
                self.euf.new_var(&mut cx, v, atom);
                self.arrays.new_var(&mut cx, v, atom);
            }
```

- [ ] **Step 3: Route `push`, `pop`, `propagate`, `build_model`, `explain`**

- In the `Theory::push`/`pop` impl for `Combiner`, add `self.arrays.push();` / `self.arrays.pop(target);` alongside the existing `euf`/`arith` calls.
- In `propagate`, after the euf/arith propagate calls, add a call into `self.arrays.propagate(&mut cx, out)` following the same conflict-handling shape (arrays returns `None` in the baseline, but wire it for completeness).
- In `build_model`, add an `arrays` model pass mirroring the `euf_m` block (it contributes nothing in the baseline but keeps the seam symmetric):

```rust
    let mut arrays_m = ModelBuilder::default();
    {
        let mut cx = TheoryCtx { terms: &mut self.terms, eq: &mut self.eq, atoms: &self.atoms };
        self.arrays.model(&mut cx, &mut arrays_m);
    }
    combined.absorb(arrays_m);
```

- In the `explain` resolve fixpoint, add a branch routing `j.theory == R::THEORY_ID` to `self.arrays.explain(&mut cx, j.tag, exp)`, mirroring the EUF/Arith branches.

- [ ] **Step 4: Integrate `arrays.check` into the N-O fixpoint**

In `drive_final_check`, in ROUND 1 immediately after the `self.arith.check(&mut cx, Effort::Full)` match arm, add:

```rust
            match self.arrays.check(&mut cx, Effort::Full) {
                TCheck::Conflict(cf) => return FinalCheck::Conflict(cf),
                TCheck::Split(atoms) => return FinalCheck::Split(atoms),
                TCheck::Sat => {}
            }
```

No A↔R or E↔R equality exchange is added: arrays' N-O seam methods are no-ops, so the existing `shared`/entailed/interface machinery is unchanged. Arrays reaches the engine's equalities directly inside its own `check`.

- [ ] **Step 5: Update existing stub tests to three slots**

Every `Combiner<X, Y>` in the `combiner.rs` test module becomes `Combiner<X, Y, NullTheory>` (or `Combiner<X, Y, EmptyTheory>` — use whichever no-op stub the module already imports; `EmptyTheory` from `crate::empty` is the production no-op). Update the type ascriptions (e.g. `let mut c: Combiner<Spy, Spy, EmptyTheory> = Combiner::default();`).

- [ ] **Step 6: Add an arrays-slot routing/split test**

Add a stub that splits once, in the arrays slot, to prove the third slot's `Split` lifts:

```rust
#[derive(Default)]
struct ArraySplitter { fired: bool, atom: Option<TermId> }
impl TheorySolver for ArraySplitter {
    const THEORY_ID: u16 = 3;
    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, atom: TermId) { self.atom = Some(atom); }
    fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> { None }
    fn propagate(&mut self, _cx: &mut TheoryCtx, _o: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> { None }
    fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        if !self.fired { self.fired = true; TCheck::Split(vec![self.atom.unwrap()]) } else { TCheck::Sat }
    }
    fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _x: &mut Explainer) {}
    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
    fn push(&mut self) {}
    fn pop(&mut self, _l: usize) {}
}

#[test]
fn arrays_slot_split_is_lifted() {
    // Build a Combiner<NullTheory, NullTheory, ArraySplitter>, register an
    // arrays-classified atom, drive a Full check, and assert SplitAtoms.
    // (Mirror the existing `Combiner<NullTheory, ArithSplitter>` split test,
    //  moving the splitter into the third slot.)
}
```

Fill the test body following the existing `ArithSplitter` split-lift test (around combiner.rs:1072), but with the splitter in slot R and a `select`-bearing atom so `classify` returns `Owner::Arrays`.

- [ ] **Step 7: Build + run the theory crate**

Run: `cargo test -p shinri-theory`
Expected: PASS (all existing + new tests). Fix any remaining non-exhaustive `Owner` matches by adding `Owner::Arrays` arms.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-theory/src/combiner.rs
git commit -m "feat(theory): generalize Combiner to three slots (Euf, Arith, Arrays); lift arrays Split"
```

---

## Task 6: Solver wiring — 3-slot Combiner, `array_sort` API, stats arm

**Files:**
- Modify: `crates/shinri-solver/src/tseitin.rs:12-13` (type alias); classify-stats `match` (~205-216)
- Modify: `crates/shinri-solver/src/lib.rs:206-219` (type alias + construction); add `array_sort` accessor
- Test: `crates/shinri-solver/tests/qfax_e2e.rs` (new)

**Interfaces:**
- Consumes: `shinri_arrays::Arrays` (Task 3); 3-slot `Combiner` (Task 5); `Owner::Arrays` (Task 4).
- Produces: `Solver::array_sort(&mut self, index: SortId, elem: SortId) -> SortId`; the production solver runs `Combiner<Euf, Arith, Arrays>`; array-sorted (dis)equality and QF_ALIA atoms flow to `Unknown` via the existing `refused` path.

- [ ] **Step 1: Add `shinri-arrays` dependency**

In `crates/shinri-solver/Cargo.toml`, add under `[dependencies]`:

```toml
shinri-arrays = { path = "../shinri-arrays" }
```

- [ ] **Step 2: Write the failing e2e test (ROW-1 UNSAT witness)**

`crates/shinri-solver/tests/qfax_e2e.rs`:

```rust
use shinri_core::{BuiltinOp, Op};
use shinri_solver::{SolveOutcome, Solver};

fn arr_setup(s: &mut Solver) -> (shinri_core::SortId, shinri_core::SortId, shinri_core::SortId) {
    let i = s.declare_sort("I");
    let e = s.declare_sort("E");
    let a = s.array_sort(i, e);
    (i, e, a)
}

#[test]
fn row1_select_over_store_same_index_unsat() {
    // select(store(a,i,e), i) != e  is UNSAT
    let mut s = Solver::new();
    let (i_s, e_s, arr_s) = arr_setup(&mut s);
    let a = s.declare_const("a", arr_s);
    let i = s.declare_const("i", i_s);
    let e = s.declare_const("e", e_s);
    let st = s.app(Op::Builtin(BuiltinOp::Store), &[a, i, e]);
    let sel = s.app(Op::Builtin(BuiltinOp::Select), &[st, i]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel, e]);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn row2_select_over_store_diff_index_unsat() {
    // i != j  ∧  select(store(a,i,e), j) != select(a, j)  is UNSAT
    let mut s = Solver::new();
    let (i_s, e_s, arr_s) = arr_setup(&mut s);
    let a = s.declare_const("a", arr_s);
    let i = s.declare_const("i", i_s);
    let j = s.declare_const("j", i_s);
    let e = s.declare_const("e", e_s);
    let st = s.app(Op::Builtin(BuiltinOp::Store), &[a, i, e]);
    let sel1 = s.app(Op::Builtin(BuiltinOp::Select), &[st, j]);
    let sel2 = s.app(Op::Builtin(BuiltinOp::Select), &[a, j]);
    let dij = s.app(Op::Builtin(BuiltinOp::Distinct), &[i, j]);
    let dsel = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel1, sel2]);
    s.assert(dij);
    s.assert(dsel);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn free_arrangement_sat() {
    // select(store(a,i,e), j) = v  with i,j free  is SAT
    let mut s = Solver::new();
    let (i_s, e_s, arr_s) = arr_setup(&mut s);
    let a = s.declare_const("a", arr_s);
    let i = s.declare_const("i", i_s);
    let j = s.declare_const("j", i_s);
    let e = s.declare_const("e", e_s);
    let v = s.declare_const("v", e_s);
    let st = s.app(Op::Builtin(BuiltinOp::Store), &[a, i, e]);
    let sel = s.app(Op::Builtin(BuiltinOp::Select), &[st, j]);
    let eq = s.eq(sel, v);
    s.assert(eq);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

#[test]
fn array_equality_is_unknown() {
    // extensionality fence: array-to-array equality → Unknown
    let mut s = Solver::new();
    let (_i, _e, arr_s) = arr_setup(&mut s);
    let a = s.declare_const("a", arr_s);
    let b = s.declare_const("b", arr_s);
    let eq = s.eq(a, b);
    s.assert(eq);
    assert_eq!(s.check_sat(), SolveOutcome::Unknown);
}
```

(Confirm `Solver::declare_const`, `app`, `eq`, `assert`, `declare_sort` signatures against `crates/shinri-solver/tests/uflia_e2e.rs`; adapt helper names if the e2e helpers differ.)

- [ ] **Step 3: Run to verify failure**

Run: `cargo test -p shinri-solver --test qfax_e2e`
Expected: FAIL to compile — `no method array_sort`; and once that's added, UNSAT assertions fail because the theory is still 2-slot.

- [ ] **Step 4: Switch the solver to the 3-slot Combiner**

In `crates/shinri-solver/src/tseitin.rs`:

```rust
type Sat = shinri_sat::Solver<
    Combiner<Euf, shinri_arith::Arith, shinri_arrays::Arrays>,
    shinri_core::NoProof,
    shinri_sat::Vmtf,
>;
```

In `crates/shinri-solver/src/lib.rs`, update the `type Sat = …` alias in `check_sat` identically (add the `shinri_arrays::Arrays` third parameter). `Combiner::with_context(self.ctx.clone())` needs no change — the third slot is inferred. Add `use shinri_arrays;` where the other theory crates are imported.

- [ ] **Step 5: Add the `array_sort` accessor on `Solver`**

In `crates/shinri-solver/src/lib.rs`, next to the existing `real_sort`/`int_sort` accessors:

```rust
pub fn array_sort(&mut self, index: shinri_core::SortId, elem: shinri_core::SortId) -> shinri_core::SortId {
    self.ctx.array_sort(index, elem)
}
```

- [ ] **Step 6: Add the `Owner::Arrays` stats arm in tseitin**

In `tseitin.rs`'s `atom()` classify-stats `match` (the one with `Ok(Owner::Euf)`/`Arith`/`Shared`/`Err(_)`), add:

```rust
            Ok(shinri_theory::types::Owner::Arrays) => { self.saw_euf = true; }
```

(Array atoms exercise EUF congruence, so counting them as EUF for the mixed/lira stats is correct and keeps those fences unchanged. Array-sorted equalities never reach this arm — they return `Err` and set `refused`.)

- [ ] **Step 7: Run the e2e test**

Run: `cargo test -p shinri-solver --test qfax_e2e`
Expected: PASS (all four: two UNSAT, one SAT, one Unknown).

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-solver/src crates/shinri-solver/Cargo.toml crates/shinri-solver/tests/qfax_e2e.rs
git commit -m "feat(solver): wire Combiner<Euf,Arith,Arrays>; array_sort API; QF_AX e2e witnesses"
```

---

## Task 7: Differential oracle vs z3 + full non-regression

**Files:**
- Create: `crates/shinri-solver/tests/qfax_oracle.rs`
- Test: the new file; plus a workspace-wide regression run.

**Interfaces:**
- Consumes: the full QF_AX solver (Tasks 1–6); `easy_smt` (already a dev-dependency — confirm in `crates/shinri-solver/Cargo.toml`, mirror `tests/oracle.rs`).

- [ ] **Step 1: Write the differential oracle test**

`crates/shinri-solver/tests/qfax_oracle.rs` — mirror the lock-step structure of `tests/oracle.rs::differential_qf_uf_small`: build the shinri instance via the library API and the z3 instance via `easy_smt` in parallel, over a seeded `Lcg`. Generate random atoms drawn from: `(= (select A idx) elt)`, `(= (select (store A idx elt) idx2) elt2)`, `(distinct …)` of the same, and `(= idx_p idx_q)` over a small pool of index constants — **never** an array-sorted equality (those are the fence, handled in Step 2). Compare verdicts:

```rust
match (ours, theirs) {
    (SolveOutcome::Unknown, _) => { /* never a failure */ }
    (SolveOutcome::Sat, easy_smt::Response::Sat) => {}
    (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {}
    (o, t) => panic!("QF_AX SOUNDNESS DISAGREEMENT: shinri={o:?} z3={t:?}\n{dump}"),
}
```

Set `ctx.set_logic("QF_AX")` on the z3 side; declare sorts via `ctx.declare_sort("I", 0)` / `("E", 0)` and the array via `ctx.declare_const("a", ctx.list(vec![ctx.atom("Array"), iI, eE]))` (match easy-smt's sort-expression construction used for the existing oracle). Copy the `Lcg` RNG helper from `tests/oracle.rs` (or factor it into a shared `tests/common` module if the project already has one).

- [ ] **Step 2: Add a fence-soundness assertion to the oracle**

In the same file, add a test that generates instances *with* array-sorted equalities and asserts shinri returns `Unknown` (never `Sat`/`Unsat`) for them — proving the extensionality fence never wrong-answers:

```rust
#[test]
fn array_equality_instances_are_unknown_never_wrong() {
    // build a handful of instances mixing (= a b) over arrays with selects;
    // assert s.check_sat() == SolveOutcome::Unknown for each.
}
```

- [ ] **Step 3: Run the oracle**

Run: `cargo test -p shinri-solver --test qfax_oracle`
Expected: PASS — no soundness disagreements; some `Unknown`s are fine.

- [ ] **Step 4: Full non-regression run (headline risk)**

The three-slot generalization must not regress existing theories.

Run: `cargo test --workspace`
Expected: PASS — all of QF_UF, QF_LIA, QF_UFLIA, QF_UFLRA oracle/e2e tests still green, plus the new QF_AX tests.

If `z3` is not installed in the environment, the oracle tests may be `#[ignore]`'d like the existing differential tests — match the existing gating convention in `tests/oracle.rs` so CI behavior is consistent.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/tests/qfax_oracle.rs
git commit -m "test(oracle): QF_AX differential vs z3 + extensionality-fence soundness; workspace non-regression"
```

---

## Self-Review

**Spec coverage** (against `2026-06-22-shinri-qfax-arrays-design.md`):
- §1.3 core sorts/ops + sort-check → Task 1. ✓
- §2.2 parser `(Array I E)`, `select`/`store` → Task 2. ✓
- §2.3 / EUF congruence-eligible select/store → satisfied automatically by EUF's op-generic `add_term` (the exploration confirmed `add_term` does not filter by `Op`); congruence is exercised through the `Owner::Arrays` fan-out to `euf.new_var` (Task 5) and validated by the ROW-2 UNSAT witness in Task 6 (`select(store(a,i,e),j)` vs `select(a,j)` requires `store`/`select` congruence). No dedicated EUF code change is required. ✓ *(If Task 6's `row2_…` test fails for lack of congruence, the fix is localized: confirm the array atom reaches `euf.new_var` — it does via the `Owner::Arrays` arm.)*
- §3 arrays solver, lazy ROW, soundness/completeness, congruence-only N-O → Task 3. ✓
- §4 three-slot combiner generalization → Tasks 4 (classify/Owner) + 5 (combiner). ✓
- §5 solver wiring, extensionality fence, `get-value` → Task 6 (fence via `classify`→`refused`→`Unknown`; array-sorted `get-value` naturally yields `?` since SAT never runs on fenced inputs; `select`/index/element `get-value` works via existing `ModelBuilder`). ✓
- §6 test/DoD: unit (Task 3), classify (Task 4), combiner non-regression (Task 5/7), e2e witnesses (Task 6), differential + fence-soundness (Task 7). ✓
- §1.4 out-of-scope fences: extensionality (Task 4/6), QF_ALIA (Task 4), no ROW proof certification (not emitted). ✓

**Placeholder scan:** Test bodies in Task 5 Step 6 and Task 7 Steps 1–2 are described rather than fully transcribed because each must mirror an existing, named in-tree test (`ArithSplitter` split-lift; `differential_qf_uf_small`); the exact reference (file + symbol) is cited so the engineer copies a concrete pattern, not an invented one. All novel/critical code (arrays `check`, `classify` fences, combiner routing arms) is given in full.

**Type consistency:** `Owner::Arrays` (Task 4) is produced by `classify` and consumed by every routing arm (Task 5) and the tseitin stats arm (Task 6). `Arrays::THEORY_ID == 3` is consistent across Task 3 (definition), Task 5 (`explain` routing on `R::THEORY_ID`), and the global constraints. `array_sort(index, elem) -> SortId` has one signature across core (Task 1) and solver (Task 6). `Combiner<E, A, R>` with field `arrays: R` is consistent across Tasks 5–6.
