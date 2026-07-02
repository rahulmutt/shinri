# Slice 5: word-level ite + n-ary =/distinct + RM equality — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit `(ite c x y)` over BV/Float/RM-sorted branches (fixing the user-reachable `blast_bv_word` panic), fix the confirmed wrong-SAT family (n-ary `=`/`distinct` over BV/FP; RM equalities leaking to EUF), and admit RM `=`/`distinct` atoms.

**Architecture:** One new normalization pass (`word_norm.rs`) at the top of `check_sat()` rewrites word-sorted ites to fresh symbols + defining assertions and expands n-ary `=`/`distinct` over word sorts to binary — before atom collection, so every existing collector/fence/blaster sees only shapes it already handles. Plus: one new blast face (RM equality over one-hot selectors), RM routing into the FP path, and internal-symbol filtering in model output.

**Tech Stack:** Rust workspace (`cargo test -p <crate>`), z3 on PATH for oracle suites (`--features oracle`).

**Spec:** `docs/superpowers/specs/2026-07-02-shinri-qffp-slice5-ite-design.md` — read it before starting any task.

## Global Constraints

- Soundness contract: anything out of scope returns `unknown`, never a wrong SAT/UNSAT verdict — and never a panic.
- The normalization pass MUST stay the first assertion transform in `check_sat()` (everything downstream assumes ite-free, binary-atom word shapes).
- The pass MUST return the *identical* TermId when a term is unchanged (no equal-but-fresh rebuilds) — other stages key on TermIds.
- Only BitVec/Float/RoundingMode sorts rewrite; Bool/Int/Real/Array/String `ite` and n-ary `=`/`distinct` over non-word sorts pass through untouched.
- Fresh symbols: names `ite!<n>` uniquified against the ctx symbol table; model filtering keys on TermId set, never on name.
- FP equality semantics: NaN-aware `core_eq` (already what `blast_fp_atom`'s `Eq` arm does) — do not introduce bitwise equality for Float.
- The RM-eq gadget `OR_i(a_i ∧ b_i)` is only correct for one-hot words — only ever apply it to `blast_rm` outputs.
- Long test suites (shinri-fp exhaustive, oracle suites) are multi-minute: run them yourself in the background; do NOT delegate them to a subagent that will spin.
- Commit after every task. Conventional prefixes used in this repo: `feat(solver):`, `feat(fp):`, `test(fp):`, `docs(qffp):` with `(slice 5)` suffix in the subject.

## Confirmed-bug repro scripts (used throughout; verdicts are z3-confirmed 2026-07-02)

| # | Script (one line) | Correct verdict | shinri today |
|---|---|---|---|
| R1 | `(declare-const c Bool)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(declare-const z (_ BitVec 8))(assert (= (ite c x y) z))(check-sat)` | sat | **panic** at blast/mod.rs:430 |
| R2 | `(declare-const x (_ BitVec 1))(declare-const y (_ BitVec 1))(declare-const z (_ BitVec 1))(assert (distinct x y z))(check-sat)` | unsat | **sat** |
| R3 | `(declare-const a (_ FloatingPoint 2 2))(declare-const b (_ FloatingPoint 2 2))(declare-const c (_ FloatingPoint 2 2))(assert (distinct a b c))(assert (fp.isZero a))(assert (fp.isZero b))(assert (fp.isZero c))(check-sat)` | unsat | **sat** |
| R4 | `(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(declare-const z (_ BitVec 8))(assert (= x y z))(assert (distinct x z))(check-sat)` | unsat | **sat** |
| R5 | `(declare-const a Float32)(declare-const b Float32)(declare-const c Float32)(assert (= a b c))(assert (distinct a c))(check-sat)` | unsat | **sat** |
| R6 | `(declare-const r RoundingMode)(assert (distinct r RNE RNA RTP RTN RTZ))(check-sat)` | unsat | **sat** (EUF leak) |

---

### Task 1: `Context::lookup_symbol` (fresh-name probing support)

**Files:**
- Modify: `crates/shinri-core/src/symbol.rs` (StringInterner, ~line 12)
- Modify: `crates/shinri-core/src/context.rs` (near `declare_fun`, ~line 152)

**Interfaces:**
- Produces: `StringInterner::lookup(&self, text: &str) -> Option<SymbolId>`; `Context::lookup_symbol(&self, text: &str) -> Option<SymbolId>`. Task 2's fresh-variable minting probes these.

- [ ] **Step 1: Write the failing test** (in `symbol.rs`'s existing `mod tests`)

```rust
#[test]
fn lookup_finds_interned_and_misses_unknown() {
    let mut i = StringInterner::default();
    let id = i.intern("foo");
    assert_eq!(i.lookup("foo"), Some(id));
    assert_eq!(i.lookup("bar"), None);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core lookup_finds_interned -- --nocapture`
Expected: compile error, `lookup` not found.

- [ ] **Step 3: Implement**

In `StringInterner` (symbol.rs):

```rust
/// Look up already-interned text without interning it.
pub fn lookup(&self, text: &str) -> Option<SymbolId> {
    self.map.get(text).copied()
}
```

In `Context` (context.rs, next to `declare_fun`):

```rust
/// Look up a symbol by name without interning it. Used by the solver's
/// word-normalization pass to mint fresh names that cannot collide with
/// user-declared symbols.
pub fn lookup_symbol(&self, text: &str) -> Option<SymbolId> {
    self.symbols.lookup(text)
}
```

- [ ] **Step 4: Run tests to verify pass**

Run: `cargo test -p shinri-core`
Expected: all pass.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-core/src/symbol.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): Context::lookup_symbol — non-interning name probe for fresh-symbol minting (slice 5)"
```

---

### Task 2: the word-normalization pass (`word_norm.rs`)

**Files:**
- Create: `crates/shinri-solver/src/word_norm.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (add `mod word_norm;` next to the other `mod` decls near the top; do NOT wire into `check_sat` yet — that is Task 3)

**Interfaces:**
- Consumes: `Context::lookup_symbol` (Task 1), `Context::{declare_fun, mk_app, term_node, children, sort_of, sort_node}`.
- Produces: `pub struct WordNorm { pub internal: FxHashSet<TermId>, ... }` with `impl Default` and `pub fn normalize(&mut self, ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>`. Task 3 wires it; Task 6 reads `internal`.

- [ ] **Step 1: Write the failing tests** (bottom of the new `word_norm.rs`, `#[cfg(test)] mod tests`)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, TermNode};

    fn bv_var(ctx: &mut Context, name: &str, w: u32) -> shinri_core::TermId {
        let s = ctx.bv_sort(w);
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    fn bool_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let s = ctx.bool_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn unchanged_assertion_keeps_identical_termid() {
        // HARD REQUIREMENT: no-change must mean same TermId, not an equal rebuild.
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom]);
        assert!(wn.internal.is_empty());
    }

    #[test]
    fn bv_ite_becomes_fresh_var_plus_definition() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let z = bv_var(&mut ctx, "z", 8);
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, z]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        // Rewritten atom + appended definition.
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
        let w = *wn.internal.iter().next().unwrap();
        // Rewritten atom is (= w z).
        let expect_atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, z]).unwrap();
        assert_eq!(out[0], expect_atom);
        // Definition is (ite c (= w x) (= w y)).
        let wx = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, x]).unwrap();
        let wy = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, y]).unwrap();
        let expect_def = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, wx, wy]).unwrap();
        assert_eq!(out[1], expect_def);
    }

    #[test]
    fn shared_ite_and_repeated_calls_reuse_one_symbol() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let a1 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, x]).unwrap();
        let a2 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, y]).unwrap();
        let mut wn = WordNorm::default();
        let out1 = wn.normalize(&mut ctx, &[a1, a2]);
        assert_eq!(wn.internal.len(), 1, "one ite term → one fresh symbol");
        assert_eq!(out1.len(), 3, "two rewritten atoms + ONE deduped definition");
        // Second check-sat: same memoized symbol, definition re-emitted.
        let out2 = wn.normalize(&mut ctx, &[a1]);
        assert_eq!(wn.internal.len(), 1);
        assert_eq!(out2.len(), 2);
    }

    #[test]
    fn nested_ite_rewrites_bottom_up() {
        // (ite c (ite d x y) z): inner ite becomes w1, outer becomes w2,
        // and w2's definition references w1.
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let d = bool_var(&mut ctx, "d");
        let x = bv_var(&mut ctx, "x", 4);
        let y = bv_var(&mut ctx, "y", 4);
        let z = bv_var(&mut ctx, "z", 4);
        let inner = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[d, x, y]).unwrap();
        let outer = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, inner, z]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[outer, x]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(wn.internal.len(), 2);
        assert_eq!(out.len(), 3, "one rewritten atom + two definitions");
    }

    #[test]
    fn nary_eq_and_distinct_expand_for_word_sorts_only() {
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let z = bv_var(&mut ctx, "z", 8);
        let eq3 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y, z]).unwrap();
        let d3 = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, y, z]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[eq3, d3]);
        // (= x y z) → (and (= x y) (= y z))
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let yz = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[y, z]).unwrap();
        let expect_eq = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[xy, yz]).unwrap();
        assert_eq!(out[0], expect_eq);
        // (distinct x y z) → (and (distinct x y) (distinct x z) (distinct y z))
        let dxy = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, y]).unwrap();
        let dxz = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, z]).unwrap();
        let dyz = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[y, z]).unwrap();
        let expect_d = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[dxy, dxz, dyz]).unwrap();
        assert_eq!(out[1], expect_d);
        // Non-word sorts pass through untouched (arith keeps its existing path).
        let int_s = ctx.int_sort();
        let af = ctx.declare_fun("ai", &[], int_s);
        let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("bi", &[], int_s);
        let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let cf = ctx.declare_fun("ci", &[], int_s);
        let cc = ctx.mk_app(Op::Uninterpreted(cf), &[]).unwrap();
        let di = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, cc]).unwrap();
        let out2 = wn.normalize(&mut ctx, &[di]);
        assert_eq!(out2, vec![di], "Int-sorted n-ary distinct is untouched");
    }

    #[test]
    fn bool_and_nonword_ite_pass_through() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let p = bool_var(&mut ctx, "p");
        let q = bool_var(&mut ctx, "q");
        let bool_ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, p, q]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[bool_ite]);
        assert_eq!(out, vec![bool_ite]);
        assert!(wn.internal.is_empty());
    }

    #[test]
    fn fresh_name_skips_user_declared_collision() {
        let mut ctx = Context::new();
        // User squats on the first fresh name.
        let s8 = ctx.bv_sort(8);
        ctx.declare_fun("ite!0", &[], s8);
        let c = bool_var(&mut ctx, "c");
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, x]).unwrap();
        let mut wn = WordNorm::default();
        wn.normalize(&mut ctx, &[atom]);
        let w = *wn.internal.iter().next().unwrap();
        // The fresh symbol must NOT be the user's `ite!0` term.
        let user_sym = ctx.lookup_symbol("ite!0").unwrap();
        let user_term = ctx.mk_app(Op::Uninterpreted(user_sym), &[]).unwrap();
        assert_ne!(w, user_term, "fresh symbol must not alias a user symbol");
    }

    #[test]
    fn rm_ite_rewrites_too() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let rtz = ctx.mk_rm_const(shinri_core::RoundingMode::Rtz);
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, rne, rtz]).unwrap();
        // Embed under an FP op so the ite is in operand position:
        // (fp.sqrt (ite c RNE RTZ) x)
        let f32s = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32s);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let sq = ctx.mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[ite, x]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[sq, x]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
        // The rewritten atom's sqrt operand is the fresh RM variable.
        let w = *wn.internal.iter().next().unwrap();
        let new_sq = ctx.mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[w, x]).unwrap();
        let expect = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[new_sq, x]).unwrap();
        assert_eq!(out[0], expect);
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-solver word_norm -- --nocapture`
Expected: compile error, module/struct not found.

- [ ] **Step 3: Implement the pass**

`crates/shinri-solver/src/word_norm.rs`:

```rust
//! Word-level normalization (slice 5). Runs FIRST in check_sat(), before atom
//! collection, fences, and Tseitin, so every downstream consumer sees only
//! shapes the blasters already handle:
//!
//! 1. **ite elimination**: `(ite c x y)` with BitVec/Float/RoundingMode-sorted
//!    branches becomes a fresh nullary symbol `w` plus one appended defining
//!    assertion `(ite c (= w x) (= w y))` (Bool-sorted ite — plain Boolean
//!    structure for every stage). Equisatisfiable and model-preserving for
//!    user symbols: `w` is functionally determined by (c, x, y).
//! 2. **n-ary `=`/`distinct` expansion** over the same word sorts: `=` chains
//!    adjacent pairs, `distinct` expands pairwise, both under `and`. The blast
//!    arms are binary-only; unexpanded n-ary atoms were the confirmed
//!    wrong-SAT family (design doc §1).
//!
//! INVARIANTS (load-bearing; see design doc §4):
//! - A term with no rewritten subterm is returned with its ORIGINAL TermId —
//!   downstream stages key on TermIds.
//! - Other sorts (Bool/Int/Real/Array/String) pass through untouched.
//! - Fresh names `ite!<n>` are probed against the symbol table so they can
//!   never alias a user symbol; model filtering keys on the `internal`
//!   TermId set, never on the name.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, SortId, SortNode, TermId, TermNode};

#[derive(Default)]
pub struct WordNorm {
    /// ite TermId (post-child-rewrite) → its fresh symbol term. Solver-lifetime:
    /// repeated check-sats and shared subterms reuse one symbol.
    ite_var: FxHashMap<TermId, TermId>,
    /// Every fresh symbol term ever minted — the model-output filter set.
    pub internal: FxHashSet<TermId>,
    /// Monotone counter for fresh names.
    ctr: u32,
}

fn is_word_sort(ctx: &Context, s: SortId) -> bool {
    matches!(
        ctx.sort_node(s),
        SortNode::BitVec(_) | SortNode::Float(_, _) | SortNode::RoundingMode
    )
}

impl WordNorm {
    /// Rewrite `assertions`; returns the rewritten set with all defining
    /// assertions for the ites encountered THIS call appended (deduped).
    pub fn normalize(&mut self, ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
        let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut defs: Vec<TermId> = Vec::new();
        let mut seen_defs: FxHashSet<TermId> = FxHashSet::default();
        let mut out: Vec<TermId> = assertions
            .iter()
            .map(|&a| self.walk(ctx, a, &mut memo, &mut defs, &mut seen_defs))
            .collect();
        out.extend(defs);
        out
    }

    fn fresh_var(&mut self, ctx: &mut Context, sort: SortId) -> TermId {
        loop {
            let name = format!("ite!{}", self.ctr);
            self.ctr += 1;
            if ctx.lookup_symbol(&name).is_some() {
                continue; // user (or an earlier check) owns this name
            }
            let sym = ctx.declare_fun(&name, &[], sort);
            let w = ctx
                .mk_app(Op::Uninterpreted(sym), &[])
                .expect("nullary app of a declared symbol is well-sorted");
            self.internal.insert(w);
            return w;
        }
    }

    fn walk(
        &mut self,
        ctx: &mut Context,
        t: TermId,
        memo: &mut FxHashMap<TermId, TermId>,
        defs: &mut Vec<TermId>,
        seen_defs: &mut FxHashSet<TermId>,
    ) -> TermId {
        if let Some(&r) = memo.get(&t) {
            return r;
        }
        let TermNode::App { op, args, .. } = ctx.term_node(t).clone() else {
            memo.insert(t, t);
            return t;
        };
        let kids: Vec<TermId> = ctx.children(args).to_vec();
        let new_kids: Vec<TermId> = kids
            .iter()
            .map(|&k| self.walk(ctx, k, memo, defs, seen_defs))
            .collect();
        // No-change ⇒ SAME TermId (hard requirement); otherwise rebuild.
        let rebuilt = if new_kids == kids {
            t
        } else {
            ctx.mk_app(op.clone(), &new_kids)
                .expect("child-for-child rebuild preserves sorts")
        };
        let result = match op {
            Op::Builtin(BuiltinOp::Ite)
                if is_word_sort(ctx, ctx.sort_of(rebuilt)) =>
            {
                let (c, x, y) = (new_kids[0], new_kids[1], new_kids[2]);
                let w = if let Some(&w) = self.ite_var.get(&rebuilt) {
                    w
                } else {
                    let w = self.fresh_var(ctx, ctx.sort_of(rebuilt));
                    self.ite_var.insert(rebuilt, w);
                    w
                };
                let wx = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, x])
                    .expect("(= w then) well-sorted");
                let wy = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, y])
                    .expect("(= w else) well-sorted");
                let def = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, wx, wy])
                    .expect("definition well-sorted");
                if seen_defs.insert(def) {
                    defs.push(def);
                }
                w
            }
            Op::Builtin(BuiltinOp::Eq)
                if new_kids.len() > 2 && is_word_sort(ctx, ctx.sort_of(new_kids[0])) =>
            {
                // (= a b c ...) → (and (= a b) (= b c) ...): adjacent chain.
                let pairs: Vec<TermId> = new_kids
                    .windows(2)
                    .map(|w| {
                        ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w[0], w[1]])
                            .expect("binary = well-sorted")
                    })
                    .collect();
                ctx.mk_app(Op::Builtin(BuiltinOp::And), &pairs)
                    .expect("and well-sorted")
            }
            Op::Builtin(BuiltinOp::Distinct)
                if new_kids.len() > 2 && is_word_sort(ctx, ctx.sort_of(new_kids[0])) =>
            {
                // (distinct a b c ...) → conjunction over all pairs i<j.
                let mut pairs: Vec<TermId> = Vec::new();
                for i in 0..new_kids.len() {
                    for j in (i + 1)..new_kids.len() {
                        pairs.push(
                            ctx.mk_app(
                                Op::Builtin(BuiltinOp::Distinct),
                                &[new_kids[i], new_kids[j]],
                            )
                            .expect("binary distinct well-sorted"),
                        );
                    }
                }
                ctx.mk_app(Op::Builtin(BuiltinOp::And), &pairs)
                    .expect("and well-sorted")
            }
            _ => rebuilt,
        };
        memo.insert(t, result);
        result
    }
}
```

Add `mod word_norm;` in `crates/shinri-solver/src/lib.rs` next to the existing `mod` declarations (`mod fp_stage;` etc.).

- [ ] **Step 4: Run tests to verify pass**

Run: `cargo test -p shinri-solver word_norm`
Expected: all 8 tests pass.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/word_norm.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(solver): word_norm pass — ite elimination to fresh defs + n-ary =/distinct expansion over BV/FP/RM (slice 5)"
```

---

### Task 3: wire the pass into `check_sat` + verdict e2e (BV/FP ite, n-ary family)

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` — `Solver` struct (~line 52), `Solver::new` (~line 82), `check_sat` (~line 279)
- Test: `crates/shinri-solver/tests/fp_e2e.rs` (FP shapes), `crates/shinri-solver/tests/qfbv_witnesses.rs` (BV shapes)

**Interfaces:**
- Consumes: `word_norm::WordNorm::normalize` (Task 2).
- Produces: `Solver` field `word_norm: crate::word_norm::WordNorm` (Task 6 reads `self.word_norm.internal`); `check_sat` operates on normalized assertions.

- [ ] **Step 1: Write the failing e2e tests**

In `crates/shinri-solver/tests/qfbv_witnesses.rs` (uses the existing `run_script` helper in that file):

```rust
// ── Slice 5: word-level ite + the n-ary =/distinct wrong-SAT family ─────────

#[test]
fn bv_ite_eq_sat() {
    // R1 — was a panic at blast/mod.rs:430 before slice 5.
    let out = run_script(
        "(declare-const c Bool)(declare-const x (_ BitVec 8))\
         (declare-const y (_ BitVec 8))(declare-const z (_ BitVec 8))\
         (assert (= (ite c x y) z))(check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn bv_ite_pinned_branches_unsat() {
    // c forces the then-branch; then-branch contradicts the outer equality.
    let out = run_script(
        "(declare-const c Bool)(declare-const x (_ BitVec 8))\
         (declare-const y (_ BitVec 8))\
         (assert c)(assert (distinct x y))\
         (assert (= (ite c x y) y))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn bv_ite_shared_skeleton_bool_var_sat_twin() {
    // Same shape as above minus (assert c): pick c=false, ite = y. SAT.
    let out = run_script(
        "(declare-const c Bool)(declare-const x (_ BitVec 8))\
         (declare-const y (_ BitVec 8))\
         (assert (distinct x y))\
         (assert (= (ite c x y) y))(check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn bv_ite_mixed_condition_unsat() {
    // Condition is Bool structure over a nested BV atom and a skeleton var.
    let out = run_script(
        "(declare-const p Bool)(declare-const a (_ BitVec 8))\
         (declare-const b (_ BitVec 8))(declare-const x (_ BitVec 8))\
         (declare-const y (_ BitVec 8))\
         (assert p)(assert (bvult a b))(assert (distinct x y))\
         (assert (= (ite (and p (bvult a b)) x y) y))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn bv1_nary_distinct_pigeonhole_unsat() {
    // R2 — answered sat before slice 5 (wrong-SAT).
    let out = run_script(
        "(declare-const x (_ BitVec 1))(declare-const y (_ BitVec 1))\
         (declare-const z (_ BitVec 1))(assert (distinct x y z))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn bv2_nary_distinct_sat_twin() {
    let out = run_script(
        "(declare-const x (_ BitVec 2))(declare-const y (_ BitVec 2))\
         (declare-const z (_ BitVec 2))(assert (distinct x y z))(check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn bv_nary_eq_chain_unsat() {
    // R4 — answered sat before slice 5 (wrong-SAT).
    let out = run_script(
        "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (declare-const z (_ BitVec 8))\
         (assert (= x y z))(assert (distinct x z))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}
```

In `crates/shinri-solver/tests/fp_e2e.rs` (uses that file's `run` helper):

```rust
// ── Slice 5: FP-sorted ite + the FP n-ary =/distinct wrong-SAT family ───────

#[test]
fn fp_ite_isnan_of_non_nans_unsat() {
    let (o, _) = run(
        "(declare-const c Bool)(declare-const x Float32)(declare-const y Float32)\
         (assert (not (fp.isNaN x)))(assert (not (fp.isNaN y)))\
         (assert (fp.isNaN (ite c x y)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_ite_isnan_sat_twin() {
    // Drop the y pin: c=false, y=NaN works.
    let (o, _) = run(
        "(declare-const c Bool)(declare-const x Float32)(declare-const y Float32)\
         (assert (not (fp.isNaN x)))\
         (assert (fp.isNaN (ite c x y)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_ite_condition_with_fp_atom_unsat() {
    // Condition is itself an FP atom: (ite (fp.lt a b) a b) is min(a,b);
    // pinning a<b and result=b contradicts (a,b distinct non-NaN handled via lt).
    let (o, _) = run(
        "(declare-const a Float32)(declare-const b Float32)\
         (assert (fp.lt a b))\
         (assert (fp.eq (ite (fp.lt a b) a b) b))\
         (assert (not (fp.eq a b)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_nary_distinct_three_zeros_unsat() {
    // R3 — answered sat before slice 5 (wrong-SAT): only ±0 are zero values.
    let (o, _) = run(
        "(declare-const a (_ FloatingPoint 2 2))(declare-const b (_ FloatingPoint 2 2))\
         (declare-const c (_ FloatingPoint 2 2))\
         (assert (distinct a b c))\
         (assert (fp.isZero a))(assert (fp.isZero b))(assert (fp.isZero c))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_nary_distinct_two_zeros_sat_twin() {
    let (o, _) = run(
        "(declare-const a (_ FloatingPoint 2 2))(declare-const b (_ FloatingPoint 2 2))\
         (assert (distinct a b))\
         (assert (fp.isZero a))(assert (fp.isZero b))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_nary_eq_chain_unsat() {
    // R5 — answered sat before slice 5 (wrong-SAT).
    let (o, _) = run(
        "(declare-const a Float32)(declare-const b Float32)(declare-const c Float32)\
         (assert (= a b c))(assert (distinct a c))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}
```

- [ ] **Step 2: Run the new tests to verify they fail**

Run: `cargo test -p shinri-solver --test qfbv_witnesses bv_ite -- --nocapture 2>&1 | tail -20`
Expected: `bv_ite_eq_sat` PANICS (`non-BV builtin reached blast_word`) — the filed crash, reproduced as a test. The n-ary tests FAIL with `sat` vs expected `unsat`.
Run: `cargo test -p shinri-solver --test fp_e2e fp_ite fp_nary 2>&1 | tail -20`
Expected: ite tests fail with `Unknown` (the old fence); n-ary tests fail with `Sat`.

- [ ] **Step 3: Wire the pass**

In `Solver` struct (lib.rs ~line 72, after `abv_array_models`):

```rust
    /// Word-level normalization state (slice 5): ite→fresh-symbol memo and
    /// the internal-symbol set excluded from model output.
    word_norm: crate::word_norm::WordNorm,
```

In `Solver::new` (add to the struct literal):

```rust
            word_norm: crate::word_norm::WordNorm::default(),
```

In `check_sat`, immediately after `let mut assertions = self.assertions.clone();` (~line 279):

```rust
        // ── Word-level normalization (slice 5) ─────────────────────────────
        // MUST run before everything else that reads `assertions` (string
        // routing, ABV, atom collection, fences, Tseitin): eliminates
        // BV/FP/RM-sorted ite into fresh definitions and expands n-ary
        // =/distinct over word sorts to binary, so collectors and blast arms
        // only ever see shapes they handle. See word_norm.rs.
        assertions = self.word_norm.normalize(&mut self.ctx, &assertions);
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p shinri-solver --test qfbv_witnesses && cargo test -p shinri-solver --test fp_e2e`
Expected: all pass, including all pre-existing tests in both files.

- [ ] **Step 5: Run the wider non-oracle net for regressions**

Run: `cargo test -p shinri-solver 2>&1 | tail -15`
Expected: 0 failed across all suites (lib + every non-oracle test file). If a pre-existing test flips, STOP and investigate — it is either a canary pinning old wrong verdicts (fix the pin, document in the commit message) or a real regression.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/qfbv_witnesses.rs crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): run word_norm first in check_sat — BV/FP ite admitted, n-ary =/distinct wrong-SAT family fixed (slice 5)"
```

---

### Task 4: RM equality gadget (`rm::eq`) + `blast_fp_atom` RM arm

**Files:**
- Modify: `crates/shinri-fp/src/rm.rs` (add `eq` + tests in the existing `mod tests`)
- Modify: `crates/shinri-fp/src/lib.rs` — `blast_fp_atom` `Eq`/`Distinct` arms (~lines 310–323)

**Interfaces:**
- Consumes: `RmSel { sel: [BitLit; 5] }`, `Blaster::{and2, or2, not1, zero}`, `blast_rm` (private, same module as `blast_fp_atom`).
- Produces: `pub fn eq(b: &mut Blaster, x: &RmSel, y: &RmSel) -> BitLit` in `rm.rs`; `blast_fp_atom` handles `Eq`/`Distinct` whose operands are RoundingMode-sorted. Task 5 makes these reachable end-to-end.

- [ ] **Step 1: Write the failing unit tests** (in `rm.rs`'s existing `#[cfg(test)] mod tests`; follow the solve-helper conventions already in that module — look at how the existing `rm` tests SAT-check a `Blaster`)

```rust
#[test]
fn rm_eq_literal_pairs_exhaustive() {
    use shinri_core::RoundingMode::*;
    // 5×5 literal pairs: the reified eq bit must be constant-true iff modes match.
    for &m1 in &[Rne, Rna, Rtp, Rtn, Rtz] {
        for &m2 in &[Rne, Rna, Rtp, Rtn, Rtz] {
            let mut b = Blaster::new();
            let x = literal(&b, m1);
            let y = literal(&b, m2);
            let e = eq(&mut b, &x, &y);
            // Force e true and solve: SAT iff m1 == m2.
            b.add_clause(&[e]);
            let expect_sat = m1 == m2;
            assert_eq!(solve_ok(b), expect_sat, "rm_eq({m1:?},{m2:?})");
        }
    }
}

#[test]
fn rm_eq_symbolic_vs_literal_forces_mode() {
    use shinri_core::RoundingMode::*;
    // (= r RTZ) with symbolic r: SAT, and asserting also (= r RNE) is UNSAT.
    let mut b = Blaster::new();
    let r = symbolic(&mut b);
    let rtz = literal(&b, Rtz);
    let rne = literal(&b, Rne);
    let e1 = eq(&mut b, &r, &rtz);
    let e2 = eq(&mut b, &r, &rne);
    b.add_clause(&[e1]);
    b.add_clause(&[e2]);
    assert!(!solve_ok(b), "r cannot equal two distinct modes");
}
```

If the existing `rm.rs` tests have no SAT-solve helper, add one modeled on `lower.rs`'s `solve_with_units` (build `shinri_sat::Solver` over `b.finish()`, no units, return `matches!(result, SolveResult::Sat)`) and name it `solve_ok`.

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp rm_eq -- --nocapture`
Expected: compile error, `eq` not found.

- [ ] **Step 3: Implement**

In `rm.rs`:

```rust
/// Equality of two RoundingMode selectors. ONE-HOT PRECONDITION: both inputs
/// must come from `literal`/`symbolic` (exactly one bit set); under that
/// invariant the selected indices match iff some position has both bits set.
/// Wrong for general (non-one-hot) words — do not reuse outside RM.
pub fn eq(b: &mut Blaster, x: &RmSel, y: &RmSel) -> BitLit {
    let mut acc = b.zero();
    for i in 0..5 {
        let both = b.and2(x.sel[i], y.sel[i]);
        acc = b.or2(acc, both);
    }
    acc
}
```

In `blast_fp_atom` (lib.rs), replace the two arms' bodies to dispatch on the operand sort (add `SortNode` to the `shinri_core` import list in lib.rs if not present):

```rust
        Op::Builtin(Eq) => {
            if matches!(ctx.sort_node(ctx.sort_of(kids[0])), shinri_core::SortNode::RoundingMode) {
                // RM equality (slice 5): one-hot selector match. Reachable for
                // user-written (= r RNE) and for word_norm's RM-ite definitions.
                let x = blast_rm(sink, ctx, kids[0]);
                let y = blast_rm(sink, ctx, kids[1]);
                crate::rm::eq(sink.blaster(), &x, &y)
            } else {
                // core = over Float operands (NaN-aware).
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
                let x = sink.word(ctx, kids[0]);
                let y = sink.word(ctx, kids[1]);
                crate::blast::compare::core_eq(sink.blaster(), &x, &y, eb, sb)
            }
        }
        Op::Builtin(Distinct) => {
            if matches!(ctx.sort_node(ctx.sort_of(kids[0])), shinri_core::SortNode::RoundingMode) {
                let x = blast_rm(sink, ctx, kids[0]);
                let y = blast_rm(sink, ctx, kids[1]);
                let e = crate::rm::eq(sink.blaster(), &x, &y);
                sink.blaster().not1(e)
            } else {
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
                let x = sink.word(ctx, kids[0]);
                let y = sink.word(ctx, kids[1]);
                let eq = crate::blast::compare::core_eq(sink.blaster(), &x, &y, eb, sb);
                sink.blaster().not1(eq)
            }
        }
```

- [ ] **Step 4: Run tests to verify pass**

Run: `cargo test -p shinri-fp rm_eq && cargo test -p shinri-fp --lib 2>&1 | tail -5`
Expected: new tests pass; no pre-existing failures. (Do NOT run the exhaustive `shinri-fp` integration suites here — they are multi-minute and unaffected; the full net runs in Task 8.)

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/rm.rs crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): rm::eq one-hot selector equality + RM =/distinct arms in blast_fp_atom (slice 5)"
```

---

### Task 5: RM routing into the FP path (fixes the EUF wrong-SAT leak) + RM e2e

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` — `is_fp_sorted` area (~line 7), `solver_uses_fp` (~line 34), `collect_fp_atoms` Eq/Distinct arm (~line 115), `fp_atom_is_supported` Eq/Distinct arm (~line 403); unit tests in the same file's `mod tests`
- Test: `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: `blast_fp_atom` RM arms (Task 4), `word_norm` wiring (Task 3), `is_rounding_mode_term` (existing, unchanged).
- Produces: RM-sorted subterms trigger the FP path; RM `=`/`distinct` atoms collected and admitted. No signature changes.

- [ ] **Step 1: Write the failing e2e tests** (`fp_e2e.rs`)

```rust
// ── Slice 5: RM equality atoms + RM-sorted ite ───────────────────────────────

#[test]
fn rm_pigeonhole_six_distinct_unsat() {
    // R6 — answered sat before slice 5: RM equalities leaked to EUF, which
    // treats RoundingMode as an unbounded uninterpreted sort.
    let (o, _) = run(
        "(declare-const r RoundingMode)\
         (assert (distinct r RNE RNA RTP RTN RTZ))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn rm_pigeonhole_five_distinct_sat_twin() {
    let (o, _) = run(
        "(declare-const r RoundingMode)\
         (assert (distinct r RNE RNA RTP RTN))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat); // r = RTZ
}

#[test]
fn rm_eq_two_modes_unsat() {
    let (o, _) = run(
        "(declare-const r RoundingMode)\
         (assert (= r RNE))(assert (= r RTZ))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn rm_ite_steers_rounding_unsat() {
    // (ite c RNE RTP) over 1.0 + 2^-24 (exact halfway): RNE ties-to-even →
    // exactly 1.0; RTP → 1.0 + 2^-23 ≠ 1.0. Pinning the sum to 1.0 with
    // (not c) forces RTP → contradiction. z3-confirm both verdicts when
    // implementing (z3 on the same scripts) before trusting the pins.
    let (o, _) = run(
        "(declare-const c Bool)\
         (define-fun one () Float32 (fp #b0 #b01111111 #b00000000000000000000000))\
         (define-fun tiny () Float32 (fp #b0 #b01100111 #b00000000000000000000000))\
         (assert (fp.eq (fp.add (ite c RNE RTP) one tiny) one))\
         (assert (not c))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn rm_ite_steers_rounding_sat_twin() {
    let (o, _) = run(
        "(declare-const c Bool)\
         (define-fun one () Float32 (fp #b0 #b01111111 #b00000000000000000000000))\
         (define-fun tiny () Float32 (fp #b0 #b01100111 #b00000000000000000000000))\
         (assert (fp.eq (fp.add (ite c RNE RTP) one tiny) one))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat); // c = true → RNE → exact 1.0
}
```

NOTE: if the parser does not support `define-fun` (check `parser.rs` — search `"define-fun"`), inline the two `(fp …)` literals at their use sites instead; the constants are Float32 `1.0` (`#b0 #b01111111 #b0…0`) and `2^-24` (`#b0 #b01100111 #b0…0`, biased exponent 103). Before pinning, sanity-check both scripts against z3 on the command line.

- [ ] **Step 2: Write the failing unit tests** (in `fp_stage.rs`'s `mod tests`)

```rust
#[test]
fn rm_content_triggers_fp_path_and_collection() {
    let mut ctx = Context::new();
    let rms = ctx.rm_sort();
    let rf = ctx.declare_fun("r", &[], rms);
    let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[r, rne]).unwrap();
    // Routing: an RM-only script must enter the FP path (the EUF leak fix).
    assert!(solver_uses_fp(&ctx, &[atom]), "RM content routes to the FP path");
    // Collection: the RM equality is an FP atom.
    let atoms = collect_fp_atoms(&ctx, &[atom]);
    assert_eq!(atoms, vec![atom]);
    // Support: RM =/distinct over RM literals/variables is admitted.
    assert!(fp_atoms_fully_supported(&ctx, &atoms));
}
```

- [ ] **Step 3: Run to verify failures**

Run: `cargo test -p shinri-solver rm_content_triggers 2>&1 | tail -5`
Expected: FAIL — `solver_uses_fp` returns false.
Run: `cargo test -p shinri-solver --test fp_e2e rm_ 2>&1 | tail -10`
Expected: pigeonhole tests FAIL (wrong `Sat` via EUF); ite-steering tests FAIL (`Unknown` — RM-eq atoms not yet admitted, `fp_atoms_fully_supported` rejects the definitions).

- [ ] **Step 4: Implement in `fp_stage.rs`**

Next to `is_fp_sorted` (~line 7):

```rust
fn is_rm_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::RoundingMode)
}
```

In `solver_uses_fp`'s walk (~line 38), widen the sort check:

```rust
        if is_fp_sorted(ctx, t) || is_rm_sorted(ctx, t) { return true; }
```

Update the doc comment above it: "True if any subterm has a Float or RoundingMode sort or an FP builtin op. RoundingMode counts as FP content so RM-only scripts (e.g. `(= r RNE)`) route here instead of leaking to EUF, which would treat RM as an unbounded uninterpreted sort (confirmed wrong-SAT, design doc §1)."

In `collect_fp_atoms`'s Eq/Distinct arm (~line 116):

```rust
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) =>
                    kids.iter().any(|&k| is_fp_sorted(ctx, k) || is_rm_sorted(ctx, k)),
```

In `fp_atom_is_supported`'s `Eq | Distinct` arm (~line 403), replace the body:

```rust
        // core = or distinct over Float-sorted operands (all supported words),
        // or over RoundingMode-sorted operands (slice 5: all RM literals or
        // nullary RM variables — post-word_norm, no other RM shapes exist).
        Op::Builtin(Eq | Distinct) => {
            if kids.iter().all(|&k| is_rm_sorted(ctx, k)) {
                kids.iter().all(|&k| is_rounding_mode_term(ctx, k))
            } else {
                kids.iter().all(|&k| {
                    matches!(ctx.sort_node(ctx.sort_of(k)), SortNode::Float(_, _))
                        && is_supported_fp_word(ctx, k)
                })
            }
        }
```

(Keep whatever the existing Float body is verbatim in the `else` branch — read it first; the shape above matches lines 403–407.)

- [ ] **Step 5: Run tests to verify pass**

Run: `cargo test -p shinri-solver rm_content_triggers && cargo test -p shinri-solver --test fp_e2e rm_`
Expected: all pass. If `rm_ite_steers_rounding_unsat` returns `Unknown`, debug the chain in order: does `word_norm` rewrite the RM ite (unit test exists)? does the definition `(ite c (= w RNE) (= w RTP))` collect (`collect_fp_atoms` on Bool-ite structure)? does `fp_atom_is_supported` admit it (`w` is a nullary RM variable)?

- [ ] **Step 6: Run the solver-crate net**

Run: `cargo test -p shinri-solver 2>&1 | tail -10`
Expected: 0 failed.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): route RM-sorted content to the FP path; admit RM =/distinct atoms — fixes RM/EUF wrong-SAT leak (slice 5)"
```

---

### Task 6: model hygiene — exclude `ite!` internals from `get-model`

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` — the BV/FP model-extraction loops in `check_sat`'s Sat arm (~lines 570 and 583)
- Test: `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: `self.word_norm.internal: FxHashSet<TermId>` (Tasks 2–3).
- Produces: `get-model` output free of internal symbols; user values unchanged.

- [ ] **Step 1: Write the failing test** (`fp_e2e.rs`)

```rust
#[test]
fn model_never_leaks_ite_internals() {
    let (o, model) = run(
        "(declare-const c Bool)(declare-const x Float32)(declare-const y Float32)\
         (assert (fp.isNaN (ite c x y)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(!model.contains("ite!"), "internal ite symbols leaked into get-model: {model}");
    // The user constants still get values.
    assert!(model.contains("(x "), "user constant x missing from model: {model}");
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-solver --test fp_e2e model_never_leaks -- --nocapture`
Expected: FAIL — the model string contains an `(ite!0 (fp …))` entry (the fresh symbol's bits land in `fp_var_bits` via `var_bits_split`).

- [ ] **Step 3: Implement**

In the BV extraction loop (~line 570) add as the first statement of the loop body:

```rust
                    if self.word_norm.internal.contains(&term) {
                        continue; // slice 5: internal ite! symbols never reach models
                    }
```

Same guard, same position, in the FP extraction loop (~line 583).

- [ ] **Step 4: Run tests to verify pass**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: all pass (including the 4d/4e get-model pins).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): filter word_norm internal symbols out of model extraction (slice 5)"
```

---

### Task 7: differential z3 oracle — `differential_qf_bvfp_ite`

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (append a new suite; copy the harness conventions of the newest existing suite in that file, `differential_qf_bvfp_fp_to_bv` — Lcg seeding, z3 invocation helper, disagreement panic format, sat/unsat/unknown counters)

**Interfaces:**
- Consumes: everything landed in Tasks 2–6, plus the file's existing `run_shinri`/z3 helpers (reuse them — do not duplicate).

- [ ] **Step 1: Write the generator + suite** (shape below; adapt helper names to what the file actually defines — READ the existing `differential_qf_bvfp_fp_to_bv` suite first and mirror it exactly)

Script shape per iteration, seeded LCG:
- Declarations: `p:Bool`, `x,y:Float32`, `u,v,w:(_ BitVec 8)`, `r:RoundingMode`.
- 1..=3 assertions, each drawn from:
  1. `(= (ite <cond> <fp> <fp>) <fp>)` — FP ite (operands drawn from `x`, `y`, FP32 specials);
  2. `(bvult (ite <cond> <bv> <bv>) <bv>)` or `(= (ite <cond> <bv> <bv>) <bv>)` — BV ite (operands from `u`,`v`,`w`, `#x00`, `#xff`);
  3. `(distinct <t1> <t2> <t3>)` — n-ary distinct, all-BV or all-FP operands;
  4. `(= <t1> <t2> <t3>)` — n-ary eq, all-BV or all-FP operands;
  5. `(= r <RM-literal>)` / `(distinct r <RM-literal> <RM-literal>)` — RM atoms;
  6. `(fp.eq (fp.add (ite <cond> <RM-literal> <RM-literal>) x y) x)` — RM ite feeding a rounded op.
- `<cond>` drawn from: `p`, `(not p)`, `(bvult u v)`, `(fp.lt x y)`, `(and p (bvult u v))`, `(ite p (fp.lt x y) (bvult u v))` (Bool ite in condition position).
- `N_ITERS = 200`, every iteration z3-checked, `unknown` must be 0, zero disagreements. Panic message prefix: `"QF_BVFP ite DISAGREEMENT"`.

- [ ] **Step 2: Run the suite**

Run (background; multi-minute): `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_bvfp_ite -- --nocapture`
Expected: `sat=…, unsat=…, unknown=0, z3_checked=200/200`, zero disagreements. ANY disagreement is a stop-the-line soundness bug: minimize the script, diagnose, fix, re-run.

- [ ] **Step 3: Re-run the pre-existing oracle suites for baseline drift** (background, long)

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle 2>&1 | tail -20`
Expected: every pre-existing suite's sat/unsat/unknown counts byte-identical to the 4e baseline (the counts are asserted in the tests themselves — 0 failed means no drift).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential z3 oracle for word-ite, n-ary =/distinct, RM atoms (slice 5)"
```

---

### Task 8: comment sweep, full workspace net, docs landed

**Files:**
- Modify: `crates/shinri-bv/src/blast/mod.rs` (~line 459 and ~line 430 comments)
- Modify: `crates/shinri-solver/src/fp_stage.rs` (stale header lines 2–3; `is_supported_fp_word` doc ~line 190; `fp_atoms_fully_supported`/walk comments mentioning "FP-sorted ite" as the canonical unsupported example)
- Modify: `crates/shinri-solver/src/lib.rs` (~line 412 comment: "Lower n-ary distinct… BV atoms pass through unchanged")
- Modify: `docs/superpowers/specs/2026-07-02-shinri-qffp-slice5-ite-design.md` (Status → Landed, with the verification summary)

- [ ] **Step 1: Comment sweep** (docs-only, no behavior):
  - `blast/mod.rs:459` `// Assume binary Distinct (n-ary is lowered before this stage).` → `// Binary only: word_norm expands n-ary =/distinct before collection (slice 5).`
  - `blast/mod.rs:430` catch-all: add above it `// Word-sorted ite cannot reach here: word_norm eliminates it before any lowering (slice 5). This arm is an internal invariant for genuinely un-blastable ops.` Retire any "BV blaster is total over BV ops" phrasing found by `rg -n "total" crates/shinri-solver crates/shinri-bv`.
  - `fp_stage.rs:2-3` header ("FP gets its own Blaster (QF_BVFP unification is a later plan)") is stale since 4a/4b — rewrite to describe the current unified-Lowerer + word_norm reality.
  - `lib.rs` ~412: the "BV atoms pass through unchanged, so their TermIds are preserved" comment — now true only BECAUSE word_norm pre-expanded word-sorted n-ary distinct; say so.
  - `fp_stage.rs` comments using "FP-sorted ite" as the fenced example (e.g. above `fp_atoms_fully_supported`, and the lib.rs comment at the `fp_atoms_fully_supported` call site ~line 395): replace the example with one that still fences (e.g. a hypothetical future FP op), noting ite is now eliminated upstream. The unit test `bv_atoms_embedded_fp_support_walk` (fp_stage.rs ~line 811) still passes unchanged — the walk itself still rejects raw ite; keep it, but update its comment to say the shape is unreachable post-word_norm and the test pins the defensive arm.
- [ ] **Step 2: Canary + regression sweep**: `rg -in "ite" crates --glob '*/tests/*.rs' | rg -iv "iter|write|finite|criteria"` — verify no remaining test pins the old Unknown/panic behavior.
- [ ] **Step 3: Full workspace net** (background; multi-minute — run it yourself, budget ~45+ min): `cargo test --workspace 2>&1 | tail -30` → EXIT=0, all suites 0-failed. Then `cargo clippy --workspace --all-targets 2>&1 | tail -20` → no net-new warnings.
- [ ] **Step 4: Mark the spec landed**: edit the spec's `**Status:**` line to `Landed — <one-paragraph verification summary: suite counts, oracle counts, canaries updated>` (follow the 4e spec's landed header as the template).
- [ ] **Step 5: Commit**

```bash
git add -A
git commit -m "docs(qfbvfp): mark slice-5 landed — word ite + n-ary =/distinct + RM atoms admitted; comment sweep"
```

---

## Self-review notes (already applied)

- Spec §5 requires `Lowerer::atom` RM dispatch "explicit" — covered implicitly: RM operands fail `ctx.bv_width` and route to `blast_fp_atom` (Task 4 handles them there); no dispatch change needed. If a reviewer prefers the explicit sort match, it is a two-line cleanup in Task 4.
- Spec §6 `uses_crossing_conversion` on post-normalization assertions: automatic — Task 3 normalizes before the fence walks; defining assertions are ordinary assertions.
- `get_value` on original ite TermIds: unchanged behavior (returns `None`/`?`), per spec §6 — no task needed.
- Task 5's rounding pins (`rm_ite_steers_rounding_*`) MUST be z3-verified during implementation before trusting the expected verdicts (step 1 note) — the constants were derived by hand.
