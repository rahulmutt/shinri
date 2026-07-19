# Slice 31 — Two-variable lexicographic order in the word-equation engine (the spine) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Route two-free-variable `str.<`/`str.<=` into the online `StrSolver`
word-equation engine via a first-differing-position head-peel clause family
backed by a sound code-handle bridge, cashing the bare pin (Sat) and the
bounded Unsat idioms; deep recursion/length-coupling to full completeness is
slice 32.

**Architecture:** A surviving symbolic-pair order atom (both sides
variables) stops being fenced at preprocessing and instead is *owned* by
`StrSolver`. On assertion it is recorded (`order_true`); in `check()` a new
handler emits a **family of flat, guarded CNF clauses** (the nested head-peel
hand-Tseitin'd, emitted incrementally across rounds like the membership
pass) that decompose each side into a single-char head + tail, compare heads
via a **dedicated uninterpreted `code: String→Int` function** (congruent via
EUF, range-bounded, and constant-folded on demand), and recurse on the tails
via fresh order atoms. Fuel bounds recursion to a sound `Unknown`.

**Tech Stack:** Rust workspace `shinri`; crates `shinri-str` (the string
theory `StrSolver`), `shinri-theory` (atom ownership / Combiner),
`shinri-euf` (congruence), `shinri-solver` (pipeline + differential tests).
Tooling via `mise`; tests via `cargo nextest`.

## Global Constraints

- **Pure-Rust mandate:** no native-link deps (`deny.toml` bans `rug`,
  `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`). z3/cvc5 for oracle tests come from
  `mise`, invoked out-of-process.
- **Soundness is absolute:** never answer SAT for an UNSAT formula or vice
  versa. Every emitted clause MUST be a valid implication `assertedLit → body`
  (guarded with `guard = Some(lit.negate())`), never an eager unguarded
  clause. When in doubt, emit nothing (fall through → the SAT layer keeps the
  literal; worst case a sound `Unknown`).
- **Emit inequalities, never bare `Eq`, to constrain arith.** A theory-emitted
  Int `Eq` routes to EUF, not Arith (`atom.rs:121-138`). Every integer
  equality (`|h|=1`, `code(h)=k`) is emitted as its `Ge`/`Le` companions via
  `length::arith_eq_companions` (`crates/shinri-str/src/length.rs:13-39`).
- **`TCheck::Split` atoms must be flat theory atoms** — never a compound
  `(and …)`/`(or …)` term (those hit `classify → Err(Unsupported)`,
  `atom.rs:98`). Disjunctions are the `atoms: Vec<TermId>` of one split;
  conjunctions are separate clauses emitted across rounds.
- **Fuel:** every split emission is preceded by `if !self.fuel.spend() {
  return TCheck::Unknown; }` (`fuel.rs`, default 40).
- **Constants:** `MAX_CODE = 0x2FFFF` (`code_conv.rs:31`, the `i128`
  arith-facing one); surrogate block `[0xD800, 0xDFFF]` excluded
  (`code_conv::is_surrogate`).
- **Hygiene before push:** `cargo fmt --all`; `cargo clippy --workspace
  --all-targets -- -D warnings` clean (`mise run lint`).
- **Oracle tests are feature-gated:** run with `cargo nextest run -p
  shinri-solver --features oracle`; **without `--features oracle` they run 0
  tests** — never report that as coverage.
- **Nextest filter:** use `-E 'test(<name>)'`, not the positional `mod::name`
  form (0.9.140 finds 0 tests with the latter); confirm discovery with
  `cargo nextest list -E 'test(<name>)'` before trusting a green run.

**Spec:** `docs/superpowers/specs/2026-07-19-shinri-slice31-str-order-symbolic-pair-design.md`
(read §2a, §4, §5, §6 before starting — they carry the soundness argument).

---

## The clause family (reference for Tasks 4–6)

For an asserted order literal `lit` on atom `(str.OP A B)` (`OP ∈ {StrLt,
StrLeq}`), let `g = Some(lit.negate())` be the guard and, if `lit` is
**negative**, first normalize: `¬(A < B) ≡ (B <= A)` and `¬(A <= B) ≡ (B <
A)` — swap operands and flip the relation, keeping `g` as `lit.negate()`.
Then emit, for the (possibly swapped) positive relation `R` on operands
`(A, B)`, the following flat guarded clauses. Fresh terms `hA, tA, hB, tB`
(via `wordeq::fresh_str`) and `code(hA)`, `code(hB)` (Task 2) are minted once
per `(A, B, OP)` and memoized (dedup key), so re-entry across rounds reuses
them. `EPS = mk_string_const("")`. Each bullet is one `TCheck::Split { atoms,
guard: g }` (one per `check()` call, guarded by fuel + a per-clause dedup set;
across rounds the family is emitted clause-by-clause).

**Shared decomposition + bridge clauses (both relations):**
- `DEC_A`   : `[ (= A EPS), (= A (str.++ hA tA)) ]`
- `LEN_HA`  : `[ (= A EPS), (>= (str.len hA) 1) ]` and `[ (= A EPS), (<= (str.len hA) 1) ]`
- `LEN_HB`  : `[ (>= (str.len hB) 1) ]` and `[ (<= (str.len hB) 1) ]`
- `DEC_B`   : `[ (= A EPS), (= B (str.++ hB tB)) ]`   *(B decomposes whenever A≠"")*
- `RNG_HA`  : `[ (= A EPS), (>= (code hA) 0) ]`, `[ (= A EPS), (<= (code hA) MAX_CODE) ]`,
             `[ (= A EPS), (<= (code hA) 0xD7FF), (>= (code hA) 0xE000) ]`
- `RNG_HB`  : `[ (>= (code hB) 0) ]`, `[ (<= (code hB) MAX_CODE) ]`,
             `[ (<= (code hB) 0xD7FF), (>= (code hB) 0xE000) ]`
- `CMP1`    : `[ (= A EPS), (< (code hA) (code hB)), (= hA hB) ]`
- `CMP2`    : `[ (= A EPS), (< (code hA) (code hB)), R_tail ]`
             where `R_tail = (str.< tA tB)` for `StrLt`, `(str.<= tA tB)` for `StrLeq`.

**Relation-specific:**
- `StrLt` only:  `NEQ` : `[ (distinct A B) ]`  and  `BNE` : `[ (distinct B EPS) ]`.
- `StrLeq` only: `BNE_cond` : `[ (= A EPS), (distinct B EPS) ]`  (no `NEQ`; `<=` allows `A=B`, and `B=""` is possible only when `A=""`).

**Validity sketch (each clause is `R → clause`, valid under `code = real
code-point fn`):** `NEQ`/`BNE` from strictness/least-element; `DEC_*` are
Skolem decompositions; `LEN_*` fix the head length; `CMP1/CMP2` are the
distributed form of `(codeLt ∨ (hA=hB ∧ R_tail))`. See spec §5/§6.

Why the bare pin is Sat at depth 0: `DEC_A` lets `A=""`; `BNE` forces `B≠""`;
no `CMP*` obligation remains → immediately satisfiable (`A=""`, `B="a"`).

Why `A<B ∧ A=B` is Unsat at depth 0: `NEQ` gives `A≠B`, directly contradicting
`A=B` (EUF).

---

### Task 1: Route surviving order atoms to `Owner::String`

**Files:**
- Modify: `crates/shinri-theory/src/atom.rs` (in `classify`, near the
  `StrInRe` block at lines 78-84)
- Test: `crates/shinri-theory/src/atom.rs` (tests module, near
  `arith_relations_go_to_arith` ~line 316)

**Interfaces:**
- Consumes: `classify(terms: &Context, atom: TermId) -> Result<Owner, Unsupported>`
- Produces: surviving `StrLt`/`StrLeq` atoms classify to `Owner::String`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn str_order_atoms_route_to_string_owner() {
    let mut terms = Context::new();
    let ss = terms.string_sort();
    let s = terms.mk_app(Op::Uninterpreted(terms.declare_fun("s", &[], ss)), &[]).unwrap();
    let u = terms.mk_app(Op::Uninterpreted(terms.declare_fun("u", &[], ss)), &[]).unwrap();
    let lt = terms.mk_app(Op::Builtin(BuiltinOp::StrLt), &[s, u]).unwrap();
    let leq = terms.mk_app(Op::Builtin(BuiltinOp::StrLeq), &[s, u]).unwrap();
    assert_eq!(classify(&terms, lt), Ok(Owner::String));
    assert_eq!(classify(&terms, leq), Ok(Owner::String));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo nextest run -p shinri-theory -E 'test(str_order_atoms_route_to_string_owner)'`
Expected: FAIL (`classify` returns `Err(Unsupported)` — the atom hits the
final `_ => Err(...)` arm).

- [ ] **Step 3: Add the routing block**

In `classify`, immediately after the `str.in_re` block (`atom.rs:78-84`), add:

```rust
// String routing: a surviving str.< / str.<= order atom (both operands
// symbolic — the constant-side cases are rewritten away in preprocessing)
// belongs to the String theory's word-equation engine.
if let TermNode::App {
    op: Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq),
    ..
} = terms.term_node(atom)
{
    return Ok(Owner::String);
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo nextest run -p shinri-theory -E 'test(str_order_atoms_route_to_string_owner)'`
Expected: PASS.

- [ ] **Step 5: Run the crate suite (no regressions)**

Run: `cargo nextest run -p shinri-theory`
Expected: all pass (routing is inert until Task 7 stops the preprocessing
fence from consuming these atoms first).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-theory/src/atom.rs
git commit -m "feat(str): slice31 T1 — classify str.</str.<= to Owner::String"
```

---

### Task 2: The `code` bridge — uninterpreted function, builders, shared-arith exposure

**Files:**
- Create: `crates/shinri-str/src/order_engine.rs` (new module for the order
  head-peel; declare it in `lib.rs` with `mod order_engine;`)
- Modify: `crates/shinri-str/src/lib.rs` (add a `code_terms: FxHashSet<TermId>`
  field to `StrSolver`; include it in `shared_arith_terms`)
- Test: `crates/shinri-str/src/order_engine.rs` (tests module)

**Interfaces:**
- Produces:
  - `pub const MAX_CODE_I128: i128 = 0x2FFFF;` (mirror of `code_conv::MAX_CODE`)
  - `pub fn code_fun(terms: &mut Context) -> Sym` — declare-or-fetch the single
    uninterpreted `!strcode: String -> Int` symbol (memoize by name; re-declaring
    the same name returns the same `Sym` in `Context`).
  - `pub fn code_of(terms: &mut Context, h: TermId) -> TermId` — build `(!strcode h)`.
  - `pub fn range_atoms(terms: &mut Context, code_h: TermId) -> Vec<TermId>` — the
    three range atoms `[ (>= code_h 0), (<= code_h MAX_CODE), <surrogate-hole clause> ]`
    where the surrogate hole is itself returned as a 2-disjunct atom set — see note.
  - `pub fn code_lt(terms: &mut Context, ca: TermId, cb: TermId) -> TermId` — `(< ca cb)`.

Note on the surrogate hole: it is a *disjunction* `(<= code_h 0xD7FF) ∨ (>=
code_h 0xE000)`, so it is emitted as a single `TCheck::Split` whose `atoms`
are those two — `range_atoms` returns the flat range atoms; the caller (Task
4) emits the two hole atoms as one split. Keep `range_atoms` returning the two
unconditional bound atoms and expose a separate `pub fn surrogate_hole_atoms`
returning the 2-element disjunct vec.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, TermNode};

    fn str_var(ctx: &mut Context, n: &str) -> TermId {
        let s = ctx.string_sort();
        ctx.mk_app(Op::Uninterpreted(ctx.declare_fun(n, &[], s)), &[]).unwrap()
    }

    #[test]
    fn code_of_is_congruent_uninterpreted_int_app() {
        let mut ctx = Context::new();
        let h1 = str_var(&mut ctx, "h1");
        let c1 = code_of(&mut ctx, h1);
        // Same argument → same hash-consed term (functional at the term level).
        let c1b = code_of(&mut ctx, h1);
        assert_eq!(c1, c1b);
        // It is Int-sorted and headed by an Uninterpreted op (so EUF congruences it).
        assert_eq!(ctx.sort_of(c1), ctx.int_sort());
        assert!(matches!(ctx.term_node(c1), TermNode::App { op: Op::Uninterpreted(_), .. }));
    }

    #[test]
    fn range_atoms_are_arith_inequalities() {
        let mut ctx = Context::new();
        let h = str_var(&mut ctx, "h");
        let code_h = code_of(&mut ctx, h);
        let atoms = range_atoms(&mut ctx, code_h);
        assert_eq!(atoms.len(), 2);
        for a in atoms {
            assert!(matches!(
                ctx.term_node(a),
                TermNode::App { op: Op::Builtin(BuiltinOp::Ge | BuiltinOp::Le), .. }
            ));
        }
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo nextest run -p shinri-str -E 'test(code_of_is_congruent_uninterpreted_int_app)'`
Expected: FAIL (module/functions do not exist).

- [ ] **Step 3: Implement the module**

```rust
//! Slice 31: the online head-peel engine for two-symbolic-var `str.<`/`str.<=`.
//! The character-order comparison uses a dedicated UNINTERPRETED
//! `!strcode : String -> Int` function so EUF congruence-closes it
//! (`shinri-euf` congruences only `Op::Uninterpreted` apps). Range + on-demand
//! constant folding (Task 6) supply its semantics; nothing here uses
//! `str.to_code` (a Builtin, which EUF would not congruence).

use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, Sym, TermId};

/// Arith-facing largest code point (mirror of `code_conv::MAX_CODE`).
pub const MAX_CODE_I128: i128 = 0x2FFFF;

/// Declare-or-fetch the single `!strcode : String -> Int` symbol.
pub fn code_fun(terms: &mut Context) -> Sym {
    let str_s = terms.string_sort();
    let int_s = terms.int_sort();
    terms.declare_fun("!strcode", &[str_s], int_s)
}

/// Build `(!strcode h)`.
pub fn code_of(terms: &mut Context, h: TermId) -> TermId {
    let f = code_fun(terms);
    terms.mk_app(Op::Uninterpreted(f), &[h]).expect("!strcode well-sorted")
}

fn int_lit(terms: &mut Context, k: i128) -> TermId {
    let int_s = terms.int_sort();
    terms.mk_numeral(Rational::from_int(Integer::from(k)), int_s)
}

/// `[ (>= code_h 0), (<= code_h MAX_CODE) ]`.
pub fn range_atoms(terms: &mut Context, code_h: TermId) -> Vec<TermId> {
    let zero = int_lit(terms, 0);
    let hi = int_lit(terms, MAX_CODE_I128);
    let ge = terms.mk_app(Op::Builtin(BuiltinOp::Ge), &[code_h, zero]).expect("ge");
    let le = terms.mk_app(Op::Builtin(BuiltinOp::Le), &[code_h, hi]).expect("le");
    vec![ge, le]
}

/// The surrogate-hole disjunction `(<= code_h 0xD7FF) ∨ (>= code_h 0xE000)`,
/// returned as the two disjunct atoms of a single split.
pub fn surrogate_hole_atoms(terms: &mut Context, code_h: TermId) -> Vec<TermId> {
    let lo = int_lit(terms, 0xD7FF);
    let hi = int_lit(terms, 0xE000);
    let below = terms.mk_app(Op::Builtin(BuiltinOp::Le), &[code_h, lo]).expect("le");
    let above = terms.mk_app(Op::Builtin(BuiltinOp::Ge), &[code_h, hi]).expect("ge");
    vec![below, above]
}

/// `(< ca cb)`.
pub fn code_lt(terms: &mut Context, ca: TermId, cb: TermId) -> TermId {
    terms.mk_app(Op::Builtin(BuiltinOp::Lt), &[ca, cb]).expect("lt")
}
```

Add `mod order_engine;` to `crates/shinri-str/src/lib.rs` (near the other
`mod` lines ~line 1-17). If `Sym` is not exported from `shinri_core`, use the
return type of `Context::declare_fun` (check its signature) and adjust.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo nextest run -p shinri-str -E 'test(code_of_is_congruent_uninterpreted_int_app) + test(range_atoms_are_arith_inequalities)'`
Expected: PASS.

- [ ] **Step 5: Add `code_terms` to `StrSolver` and expose via `shared_arith_terms`**

In `crates/shinri-str/src/lib.rs`, add a field to the struct (near
`len_terms`, ~line 47):

```rust
    /// Code-point handle terms `(!strcode h)` minted by the order engine
    /// (slice 31). Exposed to the arith theory alongside `len_terms` so the
    /// N-O seam makes them shared arith variables.
    code_terms: FxHashSet<TermId>,
```

In `shared_arith_terms` (`lib.rs:1181-1207`), extend the returned set:

```rust
        for &t in &self.code_terms {
            if !out.contains(&t) {
                out.push(t);
            }
        }
```

- [ ] **Step 6: Verify the crate still builds/tests**

Run: `cargo nextest run -p shinri-str`
Expected: all pass (new field defaults empty via `#[derive(Default)]`;
`shared_arith_terms` change is inert until Task 4 populates `code_terms`).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-str/src/order_engine.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice31 T2 — code bridge (uninterpreted !strcode, range/lt builders, shared-arith exposure)"
```

---

### Task 3: Record asserted order literals in `order_true`

**Files:**
- Modify: `crates/shinri-str/src/lib.rs` (`StrSolver` struct + `assert`; the
  `push`/`pop` trail handlers ~lines 1154-1172)
- Test: `crates/shinri-str/src/lib.rs` (tests module)

**Interfaces:**
- Produces: `order_true: Vec<(TermId, Lit, bool)>` (atom, literal, `is_lt`)
  and `order_levels: Vec<u32>`, maintained lock-step with the trail like
  `memb_true`/`memb_levels`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn assert_records_order_atoms() {
    // Build a solver, register+assert a positive (str.< s u); expect it to
    // land in order_true tagged is_lt=true. Mirror the existing memb_true
    // test harness in this module (find `fn assert_records_membership`-style
    // helper or the TheoryCtx test scaffold) and assert `solver.order_true`
    // has one entry with the StrLt atom and is_lt == true.
}
```

(Use the existing in-module test scaffolding that builds a `TheoryCtx` and
calls `new_var`/`assert` — locate the analogous membership test and copy its
setup verbatim, substituting a `StrLt` atom.)

- [ ] **Step 2: Run to verify it fails**

Run: `cargo nextest run -p shinri-str -E 'test(assert_records_order_atoms)'`
Expected: FAIL (`order_true` field does not exist).

- [ ] **Step 3: Add the fields and the assert arm**

Struct (near `memb_true`, ~line 33):

```rust
    /// Asserted order atoms (slice 31): (atom, literal, is_lt). `is_lt` is the
    /// atom's relation (`true` = str.<, `false` = str.<=); the literal's
    /// polarity is handled in `check` (negative ⇒ swapped sibling relation).
    order_true: Vec<(TermId, Lit, bool)>,
    order_levels: Vec<u32>,
```

In `assert` (`lib.rs:101`), inside the `if let TermNode::App { op, .. }`
block, alongside the `StrInRe` arm (~line 138):

```rust
        if let Op::Builtin(op @ (BuiltinOp::StrLt | BuiltinOp::StrLeq)) = op {
            self.order_true
                .push((atom, lit, matches!(op, BuiltinOp::StrLt)));
            self.order_levels.push(lvl);
        }
```

In `push`/`pop` (the trail handlers, ~lines 1154-1172), truncate
`order_true`/`order_levels` in lock-step exactly as `memb_true`/`memb_levels`
are handled (copy those two lines, substituting `order_*`).

- [ ] **Step 4: Run to verify it passes**

Run: `cargo nextest run -p shinri-str -E 'test(assert_records_order_atoms)'`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice31 T3 — record asserted order atoms in order_true"
```

---

### Task 4: `check()` head-peel clause family for `str.<`

**Files:**
- Modify: `crates/shinri-str/src/order_engine.rs` (add the clause-family
  emitter `emit_order_clauses`)
- Modify: `crates/shinri-str/src/lib.rs` (`check`: iterate `order_true`,
  call the emitter; add per-clause dedup set field)
- Test: `crates/shinri-str/src/order_engine.rs` (unit: emitted clause shapes)
  and `crates/shinri-str/src/lib.rs` or a solver-level test for `Sat`/`Unsat`.

**Interfaces:**
- Consumes: Task 2 builders; `wordeq::fresh_str`, `wordeq::len_of`;
  `length::arith_eq_companions`; `collect::collect`.
- Produces: `emit_order_clauses(cx, state, atom, lit, is_lt) -> Option<TCheck>`
  returning `Some(TCheck::Split{..})` for the next un-emitted clause of the
  family (or `None` when the family for this atom is fully emitted). The `state`
  bundles the dedup set, the fresh counter, and `code_terms`/`len_terms`
  registration.

Design the emitter to walk the clause list in a fixed order and return the
first clause whose atoms are not yet in the per-atom `emitted_order` dedup
set, spending one fuel unit per emission (mirroring `memb::memb_check` +
`emit_split`, `memb.rs:75-90`). Memoize the fresh `(hA,tA,hB,tB,code_hA,
code_hB)` per `(atom, is_lt)` in a `FxHashMap` so re-entry reuses them.

- [ ] **Step 1: Write the failing unit test (clause shapes for `str.<`)**

```rust
#[test]
fn strlt_family_emits_neq_bne_and_decomposition() {
    // Build ctx + fresh s,u; call the pure clause-builder that returns the
    // full Vec<Vec<TermId>> of clause atom-lists for (str.< s u) (factor the
    // list construction into a testable `build_strlt_clauses(cx, s, u, &mut ctr)
    // -> Vec<Vec<TermId>>` used by the emitter).
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let u = str_var(&mut ctx, "u");
    let mut ctr = 0u32;
    let clauses = build_strlt_clauses(&mut ctx, s, u, &mut ctr);
    // NEQ: a singleton (distinct s u).
    assert!(clauses.iter().any(|c| c.len() == 1 && is_distinct(&ctx, c[0], s, u)));
    // BNE: a singleton (distinct u "").
    let eps = ctx.mk_string_const("");
    assert!(clauses.iter().any(|c| c.len() == 1 && is_distinct(&ctx, c[0], u, eps)));
    // CMP2 recursion tail is a fresh (str.< tA tB) order atom.
    assert!(clauses.iter().flatten().any(|&a| is_strlt_app(&ctx, a)));
}
```

(Provide the small `is_distinct` / `is_strlt_app` helpers in the test module.)

- [ ] **Step 2: Run to verify it fails**

Run: `cargo nextest run -p shinri-str -E 'test(strlt_family_emits_neq_bne_and_decomposition)'`
Expected: FAIL (`build_strlt_clauses` missing).

- [ ] **Step 3: Implement `build_strlt_clauses` + `build_strleq_clauses`**

Implement per the "clause family" reference above. `build_strlt_clauses`
returns the ordered `Vec<Vec<TermId>>`: `[NEQ], [BNE], DEC_A, LEN_HA(ge),
LEN_HA(le), LEN_HB(ge), LEN_HB(le), DEC_B, RNG_HA×3, RNG_HB×3, CMP1, CMP2`.
Build each atom with the exact ops:
- `(distinct X Y)`: `terms.mk_app(Op::Builtin(BuiltinOp::Distinct), &[X, Y])`.
- `(= A EPS)`: `terms.mk_eq(A, eps)`.
- `(= A (str.++ hA tA))`: `let cat = terms.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[hA, tA]); terms.mk_eq(A, cat)`.
- `(>= (str.len hA) 1)`: `let l = wordeq::len_of(terms, hA); terms.mk_app(Op::Builtin(BuiltinOp::Ge), &[l, one])`.
- code atoms via Task 2 (`code_of`, `range_atoms`, `surrogate_hole_atoms`, `code_lt`).
- `R_tail`: `terms.mk_app(Op::Builtin(BuiltinOp::StrLt), &[tA, tB])` (StrLeq for `<=`).

`build_strleq_clauses` differs only by: omit `NEQ`; replace `BNE` with
`BNE_cond = [ (= A EPS), (distinct B EPS) ]`; `DEC_B` already conditional;
`R_tail` uses `StrLeq`.

- [ ] **Step 4: Run the unit test to verify it passes**

Run: `cargo nextest run -p shinri-str -E 'test(strlt_family_emits_neq_bne_and_decomposition)'`
Expected: PASS.

- [ ] **Step 5: Wire the emitter into `check()`**

Add a dedup field to `StrSolver` (near `emitted_memb`, ~line 40):

```rust
    /// Per-atom set of already-emitted order-clause atom-lists (slice 31),
    /// keyed by a stable hash of the clause's atom TermIds. Monotone.
    emitted_order: FxHashSet<(TermId, u64)>,
```

In `check()`, after the membership pass block (before the terminal
`TCheck::Sat`, ~line 1136), add an order pass that clones `order_true`,
and for each `(atom, lit, is_lt)` builds the clause list (respecting polarity:
if `lit.is_positive()` use `(A,B,is_lt)`; else use the swapped sibling per the
reference), then emits the first not-yet-emitted clause via a helper mirroring
`memb::emit_split`:

```rust
let orders: Vec<(TermId, Lit, bool)> = self.order_true.clone();
for (atom, lit, is_lt) in orders {
    if let Some(res) = order_engine::order_check(self, cx, atom, lit, is_lt) {
        return res;
    }
}
```

`order_engine::order_check` builds the (polarity-normalized) clause list,
finds the first clause not in `self.emitted_order` (key = `(atom,
hash_of(atoms))`), registers each atom's subterms with `collect::collect`
(into `len_terms`/`str_terms`) and inserts any `code_of(..)` terms into
`self.code_terms`, spends fuel, inserts the dedup key, and returns
`Some(TCheck::Split { atoms, guard: Some(lit.negate()) })`. Returns `None`
when every clause of the family is already emitted.

- [ ] **Step 6: Write the Sat/Unsat solver tests**

```rust
// In crates/shinri-str/src/lib.rs tests OR a shinri-solver integration test.
#[test]
fn bare_symbolic_lt_is_sat() {
    assert_sat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
                (assert (str.< s u))(check-sat)");
}
#[test]
fn lt_and_eq_is_unsat() {
    assert_unsat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
                  (assert (str.< s u))(assert (= s u))(check-sat)");
}
```

(Use the crate's existing SMT-string solve helper — locate `assert_sat`/
`assert_unsat` or the `Solver`/`Parser` harness used elsewhere in these tests;
these two need Task 7's fence lift to actually route, so if run before Task 7
they fence to Unknown — mark them `#[ignore]` here and un-ignore in Task 7, OR
sequence them into Task 7. Prefer sequencing the *solver-level* Sat/Unsat
assertions into Task 7 Step 5 and keep Task 4 to the unit clause-shape tests.)

- [ ] **Step 7: Run the string suite**

Run: `cargo nextest run -p shinri-str`
Expected: all pass (unit clause-shape tests green; solver-level Sat/Unsat
deferred to Task 7).

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-str/src/order_engine.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice31 T4 — str.< head-peel clause family + check() order pass"
```

---

### Task 5: `str.<=` family + polarity mapping

**Files:**
- Modify: `crates/shinri-str/src/order_engine.rs` (`order_check` polarity
  normalization uses `build_strleq_clauses`; verify swap logic)
- Test: `crates/shinri-str/src/order_engine.rs`

**Interfaces:**
- Consumes: `build_strleq_clauses` (Task 4 Step 3).
- Produces: `order_check` handles all four cases: `+StrLt`, `+StrLeq`,
  `-StrLt` (⇒ `StrLeq` swapped), `-StrLeq` (⇒ `StrLt` swapped).

- [ ] **Step 1: Write the failing test (polarity mapping)**

```rust
#[test]
fn negative_lt_maps_to_swapped_leq() {
    // order_check on a NEGATIVE literal of (str.< s u) must build the
    // str.<= family on (u, s). Assert the emitted family contains
    // (str.<= tB' tA')-shaped recursion and no NEQ singleton (since <= admits
    // equality). Drive order_check directly with a synthesized negative Lit.
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo nextest run -p shinri-str -E 'test(negative_lt_maps_to_swapped_leq)'`
Expected: FAIL.

- [ ] **Step 3: Implement polarity normalization in `order_check`**

```rust
// (A, B, use_lt) after polarity + relation normalization:
let (a, b, use_lt) = match (lit.is_positive(), is_lt) {
    (true, true)   => (args[0], args[1], true),   //  A <  B
    (true, false)  => (args[0], args[1], false),  //  A <= B
    (false, true)  => (args[1], args[0], false),  // ¬(A<B)  ≡  B <= A
    (false, false) => (args[1], args[0], true),   // ¬(A<=B) ≡  B <  A
};
let clauses = if use_lt {
    build_strlt_clauses(cx.terms, a, b, &mut self.fresh_ctr)
} else {
    build_strleq_clauses(cx.terms, a, b, &mut self.fresh_ctr)
};
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo nextest run -p shinri-str -E 'test(negative_lt_maps_to_swapped_leq)'`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-str/src/order_engine.rs
git commit -m "feat(str): slice31 T5 — str.<= family + negative-polarity swapped-sibling mapping"
```

---

### Task 6: On-demand `code` constant folding

**Files:**
- Modify: `crates/shinri-str/src/order_engine.rs` (a folding pass invoked
  from `order_check` / `check`)
- Modify: `crates/shinri-str/src/lib.rs` (call the folding pass in the order
  block; dedup set for emitted folds)
- Test: solver-level Unsat for the constant-interaction scenario.

**Interfaces:**
- Consumes: `code_conv::eval_to_code` (make it `pub(crate)` if not already);
  EUF `cx.eq` to detect a head EUF-equal to a single-char string constant;
  `length::arith_eq_companions`.
- Produces: when a minted head `h` (in `code_terms`' argument position) is
  EUF-equal to a single-char string constant `c`, emit `code(h) = eval_to_code(c)`
  as `Ge`/`Le` companions (guarded by the triggering order literal's negation),
  deduped in `emitted_len_axioms` (reuse) or a new `emitted_code_folds` set.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn lt_with_constant_pins_is_unsat_via_folding() {
    assert_unsat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
                  (assert (str.< s u))(assert (= s \"b\"))(assert (= u \"a\"))(check-sat)");
}
```

(Depends on Task 7's fence lift to route; sequence its *run* after Task 7, or
`#[ignore]` until then. Keep the folding *mechanism* + a unit test here.)

- [ ] **Step 2: Run to verify it fails**

Run: `cargo nextest run -p shinri-str -E 'test(lt_with_constant_pins_is_unsat_via_folding)'`
Expected: FAIL (Unknown or Sat — folding not implemented).

- [ ] **Step 3: Implement the folding pass**

For each head term `h` recorded (track the `h`s whose `code(h)` is in
`code_terms`), intern `h` in EUF (`cx.eq.intern`) and scan its class /
representative for a string-constant enode; if found and it is a single char,
compute `k = eval_to_code(c)`, build `(= (code h) <k>)`, split into companions,
dedup, `fuel.spend()`, and return the guarded split. Detecting "EUF-equal to a
constant" mirrors the diseq pass's constant probing (`lib.rs` diseq loop uses
`cx.eq` reasoning ~lines 1044-1051). If EUF lacks a direct "constant value of a
class" accessor, iterate the recorded `str_terms`/head list for a
`string_const_value` term `c` with `cx.eq.are_equal(intern(h), intern(c))`.

- [ ] **Step 4: Run to verify it passes**

Run (after Task 7 is in place, or temporarily lift the fence locally):
`cargo nextest run -p shinri-str -E 'test(lt_with_constant_pins_is_unsat_via_folding)'`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-str/src/order_engine.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice31 T6 — on-demand code constant folding (sound constant-interaction)"
```

---

### Task 7: Narrow the fence — route the symbolic pair, still fence constant leftovers

**Files:**
- Modify: `crates/shinri-str/src/order.rs` (`has_unreduced_str_order`)
- Test: `crates/shinri-str/src/order.rs` (flip `symbolic_pair_survives_to_fence`
  intent; add over-cap-still-fences test) + the deferred solver-level Sat/Unsat
  tests from Tasks 4/6.

**Interfaces:**
- Produces: `has_unreduced_str_order` returns `true` only for a surviving
  order atom **with at least one string-constant operand** (the over-cap /
  above-alphabet leftovers); a two-symbolic-operand atom no longer fences.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn symbolic_pair_no_longer_fenced() {
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let u = str_var(&mut ctx, "u");
    let lt = order(&mut ctx, BuiltinOp::StrLt, s, u);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    assert_eq!(out, vec![lt]);                       // still survives the rewrite
    assert!(!has_unreduced_str_order(&ctx, &out));   // but is NOT fenced now
}

#[test]
fn over_cap_constant_order_still_fences() {
    // A constant word above ORDER_CONST_LEN_CAP on one side (try_order_atom
    // returns None ⇒ atom survives with a constant operand) must STILL fence.
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let big = ctx.mk_string_const(&"a".repeat(257));
    let lt = order(&mut ctx, BuiltinOp::StrLt, s, big);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    assert!(has_unreduced_str_order(&ctx, &out));
}
```

Delete/replace the old `symbolic_pair_survives_to_fence` (its assertion that
the pair *is* fenced is now false).

- [ ] **Step 2: Run to verify they fail**

Run: `cargo nextest run -p shinri-str -E 'test(symbolic_pair_no_longer_fenced) + test(over_cap_constant_order_still_fences)'`
Expected: FAIL (current fence fires on any surviving order atom).

- [ ] **Step 3: Narrow the fence**

Replace the `walk` predicate in `has_unreduced_str_order` (`order.rs:229-240`)
so an order-op node fences **only** when an operand is a string constant:

```rust
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids = ctx.children(*args).to_vec();
                let is_order = matches!(op, Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq));
                // Fence only the leftovers with a constant operand (over-cap /
                // above-alphabet words try_order_atom rejected). A pure
                // symbolic pair is now handled by the online engine.
                let fences = is_order
                    && kids.iter().any(|&c| ctx.string_const_value(c).is_some());
                fences || kids.iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
```

- [ ] **Step 4: Run to verify they pass**

Run: `cargo nextest run -p shinri-str -E 'test(symbolic_pair_no_longer_fenced) + test(over_cap_constant_order_still_fences)'`
Expected: PASS.

- [ ] **Step 5: Un-ignore / add the deferred solver-level Sat/Unsat tests**

Enable `bare_symbolic_lt_is_sat`, `lt_and_eq_is_unsat` (Task 4) and
`lt_with_constant_pins_is_unsat_via_folding` (Task 6), plus:

```rust
#[test]
fn lt_and_lt_swapped_bounded_len_is_unsat() {
    assert_unsat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
        (assert (str.< s u))(assert (str.< u s))\
        (assert (= (str.len s) 1))(assert (= (str.len u) 1))(check-sat)");
}
#[test]
fn lt_with_len1_is_sat() {
    assert_sat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
        (assert (str.< s u))(assert (= (str.len s) 1))(check-sat)");
}
```

Run: `cargo nextest run -p shinri-str`
Expected: all pass. **If `lt_and_lt_swapped_bounded_len_is_unsat` is Unknown**,
the congruence path (`hs=hs'` ⇒ codes equal) is not firing — debug per spec §4
(is `code(h)` interned into EUF? is `hs=hs'` derived from `s=hs`, `s=hs'`?)
before proceeding; this test is the congruence-soundness gate.

- [ ] **Step 6: Wire the pipeline check (no code change expected)**

The `lib.rs:481-483` call site is unchanged — the narrowed fence simply lets
symbolic pairs through to the theory layer. Confirm with a `shinri-solver`
smoke run:

Run: `cargo nextest run -p shinri-solver -E 'test(str)'` (spot-check no
string-path regressions)
Expected: all pass.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-str/src/order.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice31 T7 — narrow order fence (route symbolic pair, fence constant leftovers)"
```

---

### Task 8: e2e differential pins

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (flip the known-gap
  pin; add the decided pins + the unbounded-antisymmetry residual pin)

**Interfaces:**
- Consumes: the `expect(src, Verdict)` helper (`qfs_differential.rs:2668`).

- [ ] **Step 1: Flip the known-gap pin to Sat**

Replace `targeted_str_order_symbolic_pair_known_gap` (`qfs_differential.rs:4034`):

```rust
#[test]
fn targeted_str_order_symbolic_pair_decides() {
    // Slice 31: two-free-var lexicographic order now decides via the online
    // head-peel engine. Bare pin is Sat (empty-prefix base case).
    expect(
        "(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
         (assert (str.< s u))(check-sat)",
        Verdict::Sat,
    );
    // Bounded Unsat idioms.
    expect(
        "(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
         (assert (str.< s u))(assert (= s u))(check-sat)",
        Verdict::Unsat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
         (assert (str.< s u))(assert (= s \"b\"))(assert (= u \"a\"))(check-sat)",
        Verdict::Unsat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
         (assert (str.< s u))(assert (str.< u s))\
         (assert (= (str.len s) 1))(assert (= (str.len u) 1))(check-sat)",
        Verdict::Unsat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
         (assert (str.< s u))(assert (= (str.len u) 0))(check-sat)",
        Verdict::Unsat,
    );
    // <= equality boundary is Sat.
    expect(
        "(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
         (assert (str.<= s u))(assert (= s u))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_str_order_unbounded_antisymmetry_known_gap() {
    // Slice-32 residual: unbounded s<u ∧ u<s fuel-exhausts to sound Unknown
    // in the spine (the all-heads-equal branch has no length floor). z3 says
    // Unsat; shinri's Unknown is sound. Flips when slice 32 lands.
    expect(
        "(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
         (assert (str.< s u))(assert (str.< u s))(check-sat)",
        Verdict::Unknown,
    );
}
```

- [ ] **Step 2: Run foreground with output (oracle feature on)**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(targeted_str_order_symbolic_pair_decides) + test(targeted_str_order_unbounded_antisymmetry_known_gap)' --no-capture`
Expected: PASS. (`expect` z3-cross-checks each non-`Unknown` verdict.)
**Verify** it ran >0 tests (`cargo nextest list -E 'test(targeted_str_order_symbolic_pair_decides)'`).

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): slice31 e2e pins — symbolic-pair decides (Sat + bounded Unsat idioms); unbounded antisymmetry banked"
```

---

### Task 9: Differential oracle family

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (add the `finish_*`
  generator, `gen_*_body` wrapper, `SOSP_SEED`/`SOSP_N_ITERS`, and the
  `qfs_str_order_symbolic_pair_matches_z3` harness — copy the const-word triple
  at lines 1135-1181 / 2600-2661)

**Interfaces:**
- Consumes: `Gen`, `Lcg`, `shinri_lines_counting_bailouts`, `z3_verdict`,
  `ALPHABET`, `N_VARS`.

- [ ] **Step 1: Add the generator**

```rust
impl Gen {
    fn finish_str_order_symbolic_pair(mut self) -> String {
        // 1..=2 order atoms over TWO free vars (no constant operand — that's
        // the preprocessing path), either relation, ~1/4 negated.
        let n_atoms = 1 + self.rng.below(2);
        for _ in 0..n_atoms {
            let op = if self.rng.below(2) == 0 { "str.<" } else { "str.<=" };
            let a = self.var();
            let mut b = self.var();
            // avoid the trivially-reflexive same-var atom sometimes
            if a == b && self.rng.below(2) == 0 { b = self.var(); }
            let atom = format!("({op} {a} {b})");
            let atom = if self.rng.below(4) == 0 { format!("(not {atom})") } else { atom };
            self.body.push_str(&format!("(assert {atom})\n"));
        }
        // Force decidable shapes: sometimes pin a var to a constant or a length.
        let v = self.var();
        match self.rng.below(4) {
            0 => { let c = ALPHABET[self.rng.below(ALPHABET.len() as u64) as usize];
                   self.body.push_str(&format!("(assert (= {v} \"{c}\"))\n")); }
            1 => { let k = self.rng.below(3);
                   self.body.push_str(&format!("(assert (= (str.len {v}) {k}))\n")); }
            2 => { let w = self.var();
                   self.body.push_str(&format!("(assert (= {v} {w}))\n")); }
            _ => {}
        }
        self.body
    }
}

fn gen_str_order_symbolic_pair_body(seed: u64) -> String {
    Gen::new(seed).finish_str_order_symbolic_pair()
}

const SOSP_SEED: u64 = 0x53_00_0000_0006;
const SOSP_N_ITERS: usize = 200;
```

- [ ] **Step 2: Add the harness (copy `qfs_str_order_const_word_matches_z3` verbatim, renamed)**

Copy `qfs_str_order_const_word_matches_z3` (`qfs_differential.rs:2607-2661`)
as `qfs_str_order_symbolic_pair_matches_z3`, substituting
`gen_str_order_symbolic_pair_body`, `SOSP_SEED`, `SOSP_N_ITERS`, and the
`println!`/assert message labels. Keep the `bailouts`/`Unknown`-skip logic and
the final `assert!(n_sat > 0)` / `assert!(n_unsat > 0)`.

- [ ] **Step 3: Run foreground with output**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfs_str_order_symbolic_pair_matches_z3)' --no-capture`
Expected: PASS; **0 disagreements**; both `n_sat > 0` and `n_unsat > 0`; note
the `n_shinri_unknown` count (expected nonzero — the unbounded-antisymmetry
and deep shapes; that is the slice-32 headroom). Record the printed tally in
the commit message.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): slice31 oracle family — symbolic-pair order vs z3 (0 disagreements; tally: <paste>)"
```

---

### Task 10: Fuel/tier check, full gate, truth-up, PR

**Files:**
- Possibly modify: `crates/shinri-str/src/fuel.rs` (only if measurement shows
  the spine needs a bump — default 40)
- Modify: the spec (truth-up "Implementation notes" section)

- [ ] **Step 1: Measure the new oracle family's wall-clock**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfs_str_order_symbolic_pair_matches_z3)' --no-capture` and note the reported duration. If >5 min, add
`#[ignore = "exhaustive: nightly tier (~N min in CI)"]` and add a fast smoke
companion (e.g. `SOSP_N_ITERS_SMOKE = 20`) on the blocking tier (AGENTS.md
test-tier rules). If ≤5 min, keep it on the blocking tier.

- [ ] **Step 2: Fuel sanity**

If any *intended-decidable* spine pin (Task 8) comes back `Unknown`, that is a
fuel or clause-family defect — do NOT paper over it by bumping fuel blindly;
diagnose the missing clause/congruence first (systematic-debugging). Only bump
`Fuel::default()` if a decidable case provably needs >40 emissions and the
bump is justified in the commit.

- [ ] **Step 3: Full local gate (pre-push)**

Run each, foreground, and confirm green:
- `cargo nextest run -p shinri-str`
- `cargo nextest run -p shinri-solver --features oracle` (full differential —
  confirm **0 disagreements** anywhere; other families' tallies unchanged vs
  `main`, any movement adjudicated per spec §7)
- `cargo nextest run -p shinri-solver -E 'test(script_e2e)'` (a
  completeness-shifting change can flip string-side e2e pins; any z3-confirmed
  `Unknown → decided` flip is an adjudicated flip, not a blocker)
- `cargo clippy --workspace --all-targets -- -D warnings`
- `cargo fmt --all --check`

- [ ] **Step 4: Truth-up the spec**

Append an "Implementation notes (truth-up)" section to the spec: the branch,
base commit, what landed as designed, any deviations (e.g. the exact
EUF-constant-detection mechanism used in Task 6, whether fuel was tuned), the
oracle tally (base vs fix: shinri-unknowns down, 0 disagreements), and confirm
the unbounded-antisymmetry pin remains the recorded slice-32 residual.

- [ ] **Step 5: Commit the truth-up and open the PR**

```bash
git add docs/superpowers/specs/2026-07-19-shinri-slice31-str-order-symbolic-pair-design.md
git commit -m "docs: slice31 truth-up"
git push -u origin slice31-str-order-symbolic-pair
gh pr create --fill --base main
```

Merge with a merge commit once CI is green, then delete the branch (remote +
local + prune) per AGENTS.md.

---

## Self-Review

**Spec coverage:**
- Fence lift (spec §3.1) → Task 7. Ownership routing (§3.2) → Task 1. Assert
  path (§3.3) → Task 3. `check` handler (§3.4, §5 clause family) → Tasks 4-5.
  Bridge congruence+range (§4a,b) → Task 2. On-demand folding (§4c) → Task 6.
  Testing (§7): unit → Tasks 1-7; e2e pins → Task 8; oracle family → Task 9;
  tier/gate → Task 10. Non-goals (§9): binary-only (guardrail in Task 4/5), the
  unbounded-antisymmetry residual pinned Unknown (Task 8 Step 1).
- **Gap check:** the congruence unit (spec §7 "T-2 crux") is realized as the
  *solver-level* `lt_and_lt_swapped_bounded_len_is_unsat` gate (Task 7 Step 5)
  rather than an isolated `code`-term unit — noted there as the
  congruence-soundness gate. Acceptable: `code` is internal (not SMT-LIB
  reachable), so the end-to-end pin is the faithful test.

**Placeholder scan:** the intricate clause construction (Task 4 Step 3) and the
EUF-constant detection (Task 6 Step 3) are specified as concrete op-level
recipes against named helpers/anchors, not "implement X later." The one item
deferred *by design* is the exact EUF "constant value of a class" accessor —
Task 6 Step 3 gives the fallback (`are_equal(intern(h), intern(c))` scan) so
there is always a concrete path.

**Type consistency:** `order_true: Vec<(TermId, Lit, bool)>` (Task 3) matches
its consumer in Task 4 Step 5. `build_strlt_clauses` / `build_strleq_clauses`
signatures (Task 4/5) and `code_of`/`range_atoms`/`code_lt` (Task 2) are used
with matching arities in Tasks 4-6. `emitted_order` / `code_terms` fields
(Tasks 2/4) are referenced consistently.

**Risk note:** Tasks 4 and 6 carry the soundness weight. The
`lt_and_lt_swapped_bounded_len_is_unsat` (congruence) and
`lt_with_constant_pins_is_unsat_via_folding` (folding) tests are the two
soundness gates — a green run of both, plus **0 oracle disagreements**, is the
slice's acceptance bar. If either is `Unknown`/`Sat`-wrong, stop and debug the
mechanism; do not proceed to Task 10.
