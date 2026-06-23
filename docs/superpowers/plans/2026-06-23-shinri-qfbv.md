# shinri QF_BV (Bitvectors) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add full SMT-LIB QF_BV (fixed-size bitvectors) to shinri via eager bit-blasting with a word-level rewrite front-end, bypassing the theory `Combiner`.

**Architecture:** A new `shinri-bv` crate lowers BV terms to CNF over its own `BitVar` namespace (rewrite → bit-blast). `shinri-solver` replays that CNF into the existing CDCL SAT solver, maps each Bool-sorted BV atom to a surrogate literal, and lets the existing Tseitin encoder handle the Boolean skeleton. EUF/Arith/Arrays are never constructed for a pure-BV query; mixed BV+other-theory queries are refused as `unknown`.

**Tech Stack:** Rust workspace (cargo), `shinri-core` (hash-consed term DAG), `shinri-sat` (CDCL), `shinri-num` (`Integer`), `rustc_hash::FxHashMap`. Differential testing against `z3` (existing oracle pattern).

## Global Constraints

- **Soundness is existential:** anything out of scope returns `unknown`, never a wrong SAT/UNSAT. Mixed BV + EUF/Arith/Arrays → `unknown` in v1.
- **No persistent incremental bit-blasting in v1:** re-blast the current assertion stack on each `check-sat`.
- **Width is part of the sort.** Width agreement is enforced at sort-check time in `shinri-core`, before blasting.
- **Bit order convention (fixed for the whole crate):** a BV value is a `Vec<BitLit>` indexed LSB→MSB. `bits[0]` is bit 0 (least significant). Every gadget consumes and produces this order.
- **`shinri-bv` does NOT depend on `shinri-sat`.** It emits CNF over its own `BitVar(u32)` namespace; the solver crate maps `BitVar → Var`. (Gadget tests may use `shinri-sat` as a dev-dependency to solve.)
- Follow existing crate conventions: per-concern module files (mirror `shinri-arith`), `FxHashMap`, doc-comments referencing the spec.
- Spec: `docs/superpowers/specs/2026-06-23-shinri-qfbv-design.md`.

---

## File Structure

**`shinri-core`** (modify):
- `src/sort.rs` — add `SortNode::BitVec(u32)`.
- `src/term.rs` — add BV `BuiltinOp` variants + `ConstVal::BitVec(BvId)`.
- `src/context.rs` — `bv_sort(width)`, `mk_bv_const`, BV op sort-checking, a `bvs` literal table + `BvId`.

**`shinri-parser`** (modify):
- `src/parser.rs` / `src/env.rs` — `(_ BitVec n)` sorts, `#x`/`#b` literals, indexed BV identifiers.

**`shinri-bv`** (new crate):
- `src/lib.rs` — `lower()` orchestration + `Lowered`/`Cnf`/`BitLit` public types.
- `src/rewrite.rs` — word-level simplification.
- `src/blast/mod.rs` — `Blaster` (BitVar allocation, clause sink, term→bits cache) + dispatch.
- `src/blast/structural.rs` — concat/extract/zero_extend/sign_extend/repeat (no clauses).
- `src/blast/bitwise.rs` — not/and/or/xor/nand/nor/xnor.
- `src/blast/arith.rs` — add/sub/neg/mul.
- `src/blast/div.rs` — udiv/urem/sdiv/srem/smod.
- `src/blast/shift.rs` — shl/lshr/ashr/rotate_left/rotate_right.
- `src/blast/compare.rs` — eq + unsigned/signed comparisons (atom outputs).
- `src/model.rs` — reconstruct BV values from a bit assignment.

**`shinri-solver`** (modify):
- `src/bv_stage.rs` (new) — detect BV, run `shinri_bv::lower`, replay CNF into SAT, build surrogate map.
- `src/tseitin.rs` — hook BV atoms to surrogate literals.
- `src/lib.rs` — call the BV stage in `check_sat`; BV model formatting.

**Tests:**
- `crates/shinri-bv/tests/` — per-gadget exhaustive small-width tests.
- `crates/shinri-cli/tests/` (or existing oracle location) — z3 differential + e2e witnesses.

---

## Task 1: Core — BitVec sort

**Files:**
- Modify: `crates/shinri-core/src/sort.rs`
- Modify: `crates/shinri-core/src/context.rs`
- Test: `crates/shinri-core/src/context.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Produces: `SortNode::BitVec(u32)`; `Context::bv_sort(&mut self, width: u32) -> SortId`; `Context::bv_width(&self, s: SortId) -> Option<u32>`.

- [ ] **Step 1: Write the failing test**

In `crates/shinri-core/src/context.rs` tests module:

```rust
#[test]
fn bv_sort_interns_by_width() {
    let mut ctx = Context::new();
    let a = ctx.bv_sort(8);
    let b = ctx.bv_sort(8);
    let c = ctx.bv_sort(32);
    assert_eq!(a, b, "same width must intern to the same SortId");
    assert_ne!(a, c);
    assert_eq!(ctx.bv_width(a), Some(8));
    assert_eq!(ctx.bv_width(c), Some(32));
    assert_eq!(ctx.bv_width(ctx.bool_sort()), None);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core bv_sort_interns_by_width`
Expected: FAIL — `bv_sort`/`bv_width` not found.

- [ ] **Step 3: Implement**

In `sort.rs`, add a variant to `SortNode`:

```rust
    /// (_ BitVec n) — n >= 1.
    BitVec(u32),
```

In `context.rs`, mirror how `array_sort` interns a `SortNode` (find the existing sort-interning helper used by `array_sort` and reuse it):

```rust
    /// Intern the (_ BitVec width) sort. width must be >= 1.
    pub fn bv_sort(&mut self, width: u32) -> SortId {
        debug_assert!(width >= 1, "BitVec width must be >= 1");
        self.intern_sort(SortNode::BitVec(width))
    }

    /// The width of a BitVec sort, or None if `s` is not a BitVec sort.
    pub fn bv_width(&self, s: SortId) -> Option<u32> {
        match self.sort_node(s) {
            SortNode::BitVec(n) => Some(*n),
            _ => None,
        }
    }
```

If `array_sort` inlines its interning rather than calling a helper, extract the interning body into `fn intern_sort(&mut self, node: SortNode) -> SortId` and have both `array_sort` and `bv_sort` call it.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-core bv_sort_interns_by_width`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-core/src/sort.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): BitVec sort interned by width"
```

---

## Task 2: Core — BV literal constants

**Files:**
- Modify: `crates/shinri-core/src/term.rs`
- Modify: `crates/shinri-core/src/context.rs`
- Test: `crates/shinri-core/src/context.rs`

**Interfaces:**
- Consumes: `Context::bv_sort` (Task 1).
- Produces: `BvId` (newtype over `u32`); `ConstVal::BitVec(BvId)`; `Context::mk_bv_const(&mut self, width: u32, value: shinri_num::Integer) -> TermId`; `Context::bv_const_value(&self, t: TermId) -> Option<(u32, &shinri_num::Integer)>`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn bv_const_roundtrips_value_and_sort() {
    use shinri_num::Integer;
    let mut ctx = Context::new();
    let t = ctx.mk_bv_const(8, Integer::from(5u32));
    assert_eq!(ctx.sort_of(t), ctx.bv_sort(8));
    let (w, v) = ctx.bv_const_value(t).unwrap();
    assert_eq!(w, 8);
    assert_eq!(*v, Integer::from(5u32));
    // Hash-consing: identical literal interns once.
    let t2 = ctx.mk_bv_const(8, Integer::from(5u32));
    assert_eq!(t, t2);
}
```

(If `shinri_num::Integer`'s constructor differs, use the crate's actual `From`/`new` — check `crates/shinri-num/src/integer.rs`.)

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-core bv_const_roundtrips_value_and_sort`
Expected: FAIL — `mk_bv_const` not found.

- [ ] **Step 3: Implement**

In `term.rs`, add a literal table id and a `ConstVal` variant:

```rust
/// Index into `Context.bvs` (the BV literal table), analogous to `RatId`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BvId(pub u32);
```

Add to `ConstVal`:

```rust
    /// A bitvector literal; references `Context.bvs`.
    BitVec(BvId),
```

In `context.rs`, add the table and constructor. Store the value reduced mod 2^width:

```rust
    // field on Context:
    //   bvs: Vec<(u32 /*width*/, shinri_num::Integer /*value in [0,2^width)*/ )>,
    //   bv_index: FxHashMap<(u32, shinri_num::Integer), BvId>,

    pub fn mk_bv_const(&mut self, width: u32, value: shinri_num::Integer) -> TermId {
        let reduced = reduce_mod_pow2(&value, width);
        let id = if let Some(&id) = self.bv_index.get(&(width, reduced.clone())) {
            id
        } else {
            let id = BvId(self.bvs.len() as u32);
            self.bvs.push((width, reduced.clone()));
            self.bv_index.insert((width, reduced), id);
            id
        };
        let sort = self.bv_sort(width);
        self.intern_const(ConstVal::BitVec(id), sort)
    }

    pub fn bv_const_value(&self, t: TermId) -> Option<(u32, &shinri_num::Integer)> {
        match self.term_node(t) {
            TermNode::Const { val: ConstVal::BitVec(BvId(i)), .. } => {
                let (w, v) = &self.bvs[*i as usize];
                Some((*w, v))
            }
            _ => None,
        }
    }
```

Add a free helper `reduce_mod_pow2(value: &Integer, width: u32) -> Integer` returning `value mod 2^width` (use `shinri_num::Integer` bit ops or `% (Integer::from(1) << width)`, normalizing negatives into `[0, 2^width)`). Reuse `mk_numeral`'s interning pattern for `intern_const` (extract a helper if one does not exist).

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-core bv_const_roundtrips_value_and_sort`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): BV literal constants with width-reduced interning"
```

---

## Task 3: Core — BV operators + sort-checking

**Files:**
- Modify: `crates/shinri-core/src/term.rs`
- Modify: `crates/shinri-core/src/context.rs`
- Test: `crates/shinri-core/src/context.rs`

**Interfaces:**
- Consumes: `Context::bv_sort`, `bv_width` (Task 1).
- Produces: BV `BuiltinOp` variants (below); `Context::mk_app(Op::Builtin(bv_op), args)` returns the correctly-widthed result sort or `SortError`.

The variant set (add to `BuiltinOp`):

```rust
    // Bitvectors — fixed-arity
    BvNot, BvAnd, BvOr, BvXor, BvNand, BvNor, BvXnor,
    BvNeg, BvAdd, BvSub, BvMul,
    BvUdiv, BvUrem, BvSdiv, BvSrem, BvSmod,
    BvShl, BvLshr, BvAshr,
    BvUlt, BvUle, BvUgt, BvUge, BvSlt, BvSle, BvSgt, BvSge,
    BvConcat,
    // Bitvectors — indexed (parameters carried in the op)
    BvExtract { hi: u32, lo: u32 },
    BvZeroExtend(u32),
    BvSignExtend(u32),
    BvRotateLeft(u32),
    BvRotateRight(u32),
    BvRepeat(u32),
```

Result-sort rules:
- Bitwise/arith/shift binary ops (`BvAnd..BvMul`, `BvUdiv..BvSmod`, `BvShl..BvAshr`): both args same `BitVec(n)`, result `BitVec(n)`.
- `BvNot`, `BvNeg`: one arg `BitVec(n)`, result `BitVec(n)`.
- Comparisons (`BvUlt..BvSge`): both args same `BitVec(n)`, result `Bool`.
- `BvConcat`: args `BitVec(m)`, `BitVec(n)`, result `BitVec(m+n)`.
- `BvExtract { hi, lo }`: arg `BitVec(n)` with `n > hi >= lo`, result `BitVec(hi-lo+1)`.
- `BvZeroExtend(k)`, `BvSignExtend(k)`: arg `BitVec(n)`, result `BitVec(n+k)`.
- `BvRotateLeft(k)`, `BvRotateRight(k)`: arg `BitVec(n)`, result `BitVec(n)`.
- `BvRepeat(k)` (k>=1): arg `BitVec(n)`, result `BitVec(n*k)`.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn bv_op_result_widths() {
    use shinri_core::{BuiltinOp::*, Op};
    let mut ctx = Context::new();
    let s8 = ctx.bv_sort(8);
    let x = { let f = ctx.declare_fun("x", &[], s8); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let y = { let f = ctx.declare_fun("y", &[], s8); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };

    let add = ctx.mk_app(Op::Builtin(BvAdd), &[x, y]).unwrap();
    assert_eq!(ctx.bv_width(ctx.sort_of(add)), Some(8));

    let cat = ctx.mk_app(Op::Builtin(BvConcat), &[x, y]).unwrap();
    assert_eq!(ctx.bv_width(ctx.sort_of(cat)), Some(16));

    let ext = ctx.mk_app(Op::Builtin(BvExtract { hi: 3, lo: 1 }), &[x]).unwrap();
    assert_eq!(ctx.bv_width(ctx.sort_of(ext)), Some(3));

    let ze = ctx.mk_app(Op::Builtin(BvZeroExtend(4)), &[x]).unwrap();
    assert_eq!(ctx.bv_width(ctx.sort_of(ze)), Some(12));

    let ult = ctx.mk_app(Op::Builtin(BvUlt), &[x, y]).unwrap();
    assert_eq!(ctx.sort_of(ult), ctx.bool_sort());
}

#[test]
fn bv_width_mismatch_is_error() {
    use shinri_core::{BuiltinOp::*, Op};
    let mut ctx = Context::new();
    let s8 = ctx.bv_sort(8);
    let s16 = ctx.bv_sort(16);
    let x = { let f = ctx.declare_fun("x", &[], s8); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let z = { let f = ctx.declare_fun("z", &[], s16); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    assert!(ctx.mk_app(Op::Builtin(BvAdd), &[x, z]).is_err());
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p shinri-core bv_op_result_widths bv_width_mismatch_is_error`
Expected: FAIL — variants/arms missing.

- [ ] **Step 3: Implement**

Add the variants to `BuiltinOp` (above). In `context.rs::check_builtin`, add arms. Sketch:

```rust
            BvNot | BvNeg => {
                expect_arity(args, 1)?;
                let n = self.require_bv(args[0])?;
                Ok(self.bv_sort_const(n))
            }
            BvAnd | BvOr | BvXor | BvNand | BvNor | BvXnor
            | BvAdd | BvSub | BvMul
            | BvUdiv | BvUrem | BvSdiv | BvSrem | BvSmod
            | BvShl | BvLshr | BvAshr => {
                expect_arity(args, 2)?;
                let n = self.require_bv(args[0])?;
                let m = self.require_bv(args[1])?;
                if n != m { return Err(SortError::Mismatch {
                    expected: self.sort_of(args[0]), found: self.sort_of(args[1]) }); }
                Ok(self.bv_sort_const(n))
            }
            BvUlt | BvUle | BvUgt | BvUge | BvSlt | BvSle | BvSgt | BvSge => {
                expect_arity(args, 2)?;
                let n = self.require_bv(args[0])?;
                let m = self.require_bv(args[1])?;
                if n != m { return Err(SortError::Mismatch {
                    expected: self.sort_of(args[0]), found: self.sort_of(args[1]) }); }
                Ok(bool_s)
            }
            BvConcat => {
                expect_arity(args, 2)?;
                let n = self.require_bv(args[0])?;
                let m = self.require_bv(args[1])?;
                Ok(self.bv_sort_const(n + m))
            }
            BvExtract { hi, lo } => {
                expect_arity(args, 1)?;
                let n = self.require_bv(args[0])?;
                if !(hi < n && lo <= hi) { return Err(SortError::BvIndex); }
                Ok(self.bv_sort_const(hi - lo + 1))
            }
            BvZeroExtend(k) | BvSignExtend(k) => {
                expect_arity(args, 1)?;
                let n = self.require_bv(args[0])?;
                Ok(self.bv_sort_const(n + k))
            }
            BvRotateLeft(_) | BvRotateRight(_) => {
                expect_arity(args, 1)?;
                let n = self.require_bv(args[0])?;
                Ok(self.bv_sort_const(n))
            }
            BvRepeat(k) => {
                expect_arity(args, 1)?;
                if k < 1 { return Err(SortError::BvIndex); }
                let n = self.require_bv(args[0])?;
                Ok(self.bv_sort_const(n * k))
            }
```

`check_builtin` is `&self`, but `bv_sort` is `&mut self`. Since `mk_app` calls `check_app` (which returns the result `SortId`) *before* interning, and the result BitVec sort must already exist to be returned: add a non-mutating `fn bv_sort_const(&self, width: u32) -> SortId` that looks up an already-interned BitVec sort, **or** restructure so `check_app` can intern. Simplest: make `check_app`/`check_builtin` take `&mut self` (interning a sort during checking is harmless and idempotent). Update the `mk_app` call site accordingly. Add helpers:

```rust
    fn require_bv(&self, t: TermId) -> Result<u32, SortError> {
        self.bv_width(self.sort_of(t)).ok_or(SortError::NotBitVec)
    }
```

Add `SortError::NotBitVec` and `SortError::BvIndex` variants in `error.rs`.

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test -p shinri-core bv_op_result_widths bv_width_mismatch_is_error`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs crates/shinri-core/src/error.rs
git commit -m "feat(core): BV operators with width-computing sort checks"
```

---

## Task 4: Parser — BitVec sorts and `#x`/`#b` literals

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs`
- Modify: `crates/shinri-parser/src/lexer.rs` (if `#x`/`#b` tokens are not already lexed)
- Test: `crates/shinri-parser/src/parser.rs` (inline tests)

**Interfaces:**
- Consumes: `Context::bv_sort`, `Context::mk_bv_const` (Tasks 1–2).
- Produces: the parser maps the sort form `(_ BitVec n)` to `bv_sort(n)`, and the literal tokens `#xHH..`/`#bBB..` to `mk_bv_const`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn parses_bv_sort_and_hex_binary_literals() {
    // #xFF is an 8-bit constant 255; #b1010 is a 4-bit constant 10.
    let src = "(declare-const x (_ BitVec 8))\n(assert (= x #xFF))\n(assert (= ((_ extract 3 0) x) #b1010))\n";
    let cmds = parse_all(src).expect("parses");
    // Find the BV const sort and literal widths through the shared context.
    // (Adapt to the test harness used elsewhere in this file — assert no parse error
    //  and that the asserted terms are Bool-sorted equalities over BitVec args.)
    assert!(!cmds.is_empty());
}
```

Match the surrounding test style in `parser.rs` (how other `parse_all`/context assertions are written there).

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-parser parses_bv_sort_and_hex_binary_literals`
Expected: FAIL — unknown sort `BitVec` / unhandled `#x` token.

- [ ] **Step 3: Implement**

- **Sort parsing:** where the parser resolves `(_ <id> <index>...)` sort forms (the same path that handles `(Array I E)` and other sorts), add: if the head is `BitVec` with one numeral index `n`, return `ctx.bv_sort(n)`.
- **Literal lexing:** ensure the lexer emits a token for `#x[0-9a-fA-F]+` and `#b[01]+`. If not present, add a rule.
- **Literal parsing:** on a `#x` token of `h` hex digits → `width = 4*h`, `value = Integer::from_str_radix(digits, 16)`; on `#b` of `b` binary digits → `width = b`, `value = Integer::from_str_radix(digits, 2)`. Emit `ctx.mk_bv_const(width, value)`.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-parser parses_bv_sort_and_hex_binary_literals`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-parser/src/
git commit -m "feat(parser): parse (_ BitVec n) sorts and #x/#b literals"
```

---

## Task 5: Parser — indexed BV operators

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs`
- Test: `crates/shinri-parser/src/parser.rs`

**Interfaces:**
- Consumes: BV `BuiltinOp` variants (Task 3).
- Produces: the parser maps each BV symbol / indexed identifier to its `BuiltinOp`.

Symbol → op table (non-indexed): `bvnot→BvNot`, `bvand→BvAnd`, `bvor→BvOr`, `bvxor→BvXor`, `bvnand→BvNand`, `bvnor→BvNor`, `bvxnor→BvXnor`, `bvneg→BvNeg`, `bvadd→BvAdd`, `bvsub→BvSub`, `bvmul→BvMul`, `bvudiv→BvUdiv`, `bvurem→BvUrem`, `bvsdiv→BvSdiv`, `bvsrem→BvSrem`, `bvsmod→BvSmod`, `bvshl→BvShl`, `bvlshr→BvLshr`, `bvashr→BvAshr`, `bvult→BvUlt`, `bvule→BvUle`, `bvugt→BvUgt`, `bvuge→BvUge`, `bvslt→BvSlt`, `bvsle→BvSle`, `bvsgt→BvSgt`, `bvsge→BvSge`, `concat→BvConcat`.

Indexed identifiers `(_ <id> <args>)`: `extract i j→BvExtract{hi:i,lo:j}`, `zero_extend k→BvZeroExtend(k)`, `sign_extend k→BvSignExtend(k)`, `rotate_left k→BvRotateLeft(k)`, `rotate_right k→BvRotateRight(k)`, `repeat k→BvRepeat(k)`. Also `(_ bvK n)` (an indexed *term*, not op) → `ctx.mk_bv_const(n, Integer::from(K))`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn parses_indexed_bv_ops_and_bv_numeral() {
    let src = "(declare-const x (_ BitVec 8))\n\
               (assert (bvult (bvadd x (_ bv1 8)) ((_ zero_extend 4) ((_ extract 3 0) x))))\n";
    // wrong: widths differ (12 vs 8). Use a width-correct formula instead:
    let src = "(declare-const x (_ BitVec 8))\n\
               (assert (= (concat ((_ extract 7 4) x) ((_ extract 3 0) x)) (bvadd x (_ bv1 8))))\n";
    assert!(parse_all(src).is_ok());
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-parser parses_indexed_bv_ops_and_bv_numeral`
Expected: FAIL — unknown symbol `bvadd` / `concat`.

- [ ] **Step 3: Implement**

Add the non-indexed table to the function-symbol resolver (the `match name { ... }` that already maps `"and"`, `"select"`, etc. — see `builtin_name` handling). Add the indexed-identifier arms where `(_ extract ...)` etc. are dispatched. For `(_ bvK n)`, parse `K` from the symbol suffix after `bv` and emit `mk_bv_const(n, Integer::from(K))`.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-parser parses_indexed_bv_ops_and_bv_numeral`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(parser): BV operator symbols + indexed identifiers"
```

---

## Task 6: shinri-bv crate scaffold — Blaster, BitLit, CNF

**Files:**
- Create: `crates/shinri-bv/Cargo.toml`
- Create: `crates/shinri-bv/src/lib.rs`
- Create: `crates/shinri-bv/src/blast/mod.rs`
- Modify: `Cargo.toml` (workspace members)
- Test: `crates/shinri-bv/src/blast/mod.rs` (inline)

**Interfaces:**
- Produces:
  - `pub struct BitLit { pub var: u32, pub pos: bool }` with `fn negate(self) -> BitLit`.
  - `pub struct Cnf { pub num_vars: u32, pub clauses: Vec<Vec<BitLit>> }`.
  - `pub struct Blaster { /* private */ }` with:
    - `fn new() -> Blaster` (allocates var 0 as the pinned-true constant).
    - `fn one(&self) -> BitLit` / `fn zero(&self) -> BitLit` (const true / false).
    - `fn fresh(&mut self) -> BitLit` (new var).
    - `fn add_clause(&mut self, lits: &[BitLit])`.
    - `fn finish(self) -> Cnf`.
    - Gate helpers used by every gadget: `and2`, `or2`, `xor2`, `not1`, `mux2(sel, a, b)` (returns `sel ? a : b`), `full_adder(a,b,cin) -> (sum, cout)`.
  - `bits_eq(&mut self, a: &[BitLit], b: &[BitLit]) -> BitLit` deferred to compare.rs (Task 13).

- [ ] **Step 1: Write the failing test**

```rust
// in blast/mod.rs
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_bits_and_fresh_allocate_distinct_vars() {
        let mut b = Blaster::new();
        assert_eq!(b.one().var, 0);
        assert!(b.one().pos);
        assert_eq!(b.zero().var, 0);
        assert!(!b.zero().pos);
        let x = b.fresh();
        let y = b.fresh();
        assert_ne!(x.var, y.var);
        assert!(x.var >= 1 && y.var >= 1);
    }

    #[test]
    fn full_adder_truth_table() {
        // Verify the gate definition by solving with a tiny brute force over the
        // 3 inputs using the emitted clauses (helper `eval` assigns the input vars
        // and checks all clauses are satisfiable with exactly one completion).
        // For now assert structural: full_adder returns two distinct signal lits.
        let mut b = Blaster::new();
        let a = b.fresh(); let bb = b.fresh(); let c = b.fresh();
        let (s, co) = b.full_adder(a, bb, c);
        assert_ne!(s.var, co.var);
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv`
Expected: FAIL — crate/types do not exist.

- [ ] **Step 3: Implement**

`crates/shinri-bv/Cargo.toml`:

```toml
[package]
name = "shinri-bv"
version = "0.1.0"
edition = "2021"

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-num = { path = "../shinri-num" }
rustc-hash = "2"

[dev-dependencies]
shinri-sat = { path = "../shinri-sat" }
```

Add `"crates/shinri-bv"` to the workspace `members` in the root `Cargo.toml`.

`src/lib.rs`:

```rust
//! shinri-bv: eager bit-blasting of QF_BV to CNF over a private BitVar namespace.
//! See docs/superpowers/specs/2026-06-23-shinri-qfbv-design.md.
pub mod blast;
pub mod bitwise; // re-exported gate modules live under blast/, but keep lib flat for now
pub use blast::{BitLit, Blaster, Cnf};
```

(Adjust `pub mod` lines as later tasks add modules; keep `blast` the home of `Blaster`.)

`src/blast/mod.rs`:

```rust
use rustc_hash::FxHashMap;
use shinri_core::TermId;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BitLit { pub var: u32, pub pos: bool }
impl BitLit {
    pub fn negate(self) -> BitLit { BitLit { var: self.var, pos: !self.pos } }
}

#[derive(Default)]
pub struct Cnf { pub num_vars: u32, pub clauses: Vec<Vec<BitLit>> }

pub struct Blaster {
    next_var: u32,
    clauses: Vec<Vec<BitLit>>,
    /// Memoized blasted words: TermId -> LSB..MSB bit literals.
    pub(crate) cache: FxHashMap<TermId, Vec<BitLit>>,
}

impl Blaster {
    pub fn new() -> Blaster {
        // var 0 is the pinned-true constant.
        let mut b = Blaster { next_var: 1, clauses: Vec::new(), cache: FxHashMap::default() };
        let t = BitLit { var: 0, pos: true };
        b.add_clause(&[t]); // force var0 = true
        b
    }
    pub fn one(&self) -> BitLit { BitLit { var: 0, pos: true } }
    pub fn zero(&self) -> BitLit { BitLit { var: 0, pos: false } }
    pub fn fresh(&mut self) -> BitLit { let v = self.next_var; self.next_var += 1; BitLit { var: v, pos: true } }
    pub fn add_clause(&mut self, lits: &[BitLit]) { self.clauses.push(lits.to_vec()); }
    pub fn finish(self) -> Cnf { Cnf { num_vars: self.next_var, clauses: self.clauses } }

    pub fn not1(&self, a: BitLit) -> BitLit { a.negate() }

    pub fn and2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        self.add_clause(&[o.negate(), a]);
        self.add_clause(&[o.negate(), b]);
        self.add_clause(&[o, a.negate(), b.negate()]);
        o
    }
    pub fn or2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        self.add_clause(&[o, a.negate()]);
        self.add_clause(&[o, b.negate()]);
        self.add_clause(&[o.negate(), a, b]);
        o
    }
    pub fn xor2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        self.add_clause(&[o.negate(), a, b]);
        self.add_clause(&[o.negate(), a.negate(), b.negate()]);
        self.add_clause(&[o, a.negate(), b]);
        self.add_clause(&[o, a, b.negate()]);
        o
    }
    /// sel ? a : b
    pub fn mux2(&mut self, sel: BitLit, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // sel -> o<->a ; ¬sel -> o<->b
        self.add_clause(&[sel.negate(), o.negate(), a]);
        self.add_clause(&[sel.negate(), o, a.negate()]);
        self.add_clause(&[sel, o.negate(), b]);
        self.add_clause(&[sel, o, b.negate()]);
        o
    }
    pub fn full_adder(&mut self, a: BitLit, b: BitLit, cin: BitLit) -> (BitLit, BitLit) {
        let axb = self.xor2(a, b);
        let sum = self.xor2(axb, cin);
        let t1 = self.and2(a, b);
        let t2 = self.and2(axb, cin);
        let cout = self.or2(t1, t2);
        (sum, cout)
    }
}
```

Add a `#[cfg(test)] fn eval(...)` helper if you implement the truth-table solve; otherwise keep the structural assertion. (Exhaustive correctness is validated end-to-end in gadget tasks via `shinri-sat`.)

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/ Cargo.toml
git commit -m "feat(bv): shinri-bv scaffold — Blaster, BitLit, CNF, gate gadgets"
```

---

## Task 7: Structural gadgets (concat/extract/extend/repeat)

**Files:**
- Create: `crates/shinri-bv/src/blast/structural.rs`
- Modify: `crates/shinri-bv/src/blast/mod.rs` (`pub mod structural;` + dispatch stub)
- Test: `crates/shinri-bv/src/blast/structural.rs`

**Interfaces:**
- Consumes: `Blaster`, `BitLit` (Task 6).
- Produces (all pure slicing, no clauses):
  - `fn concat(hi: &[BitLit], lo: &[BitLit]) -> Vec<BitLit>` — result LSB..MSB is `lo` then `hi` (SMT-LIB `concat` puts the first arg in the high bits).
  - `fn extract(a: &[BitLit], hi: u32, lo: u32) -> Vec<BitLit>` — `a[lo..=hi]`.
  - `fn zero_extend(a: &[BitLit], k: u32, b: &Blaster) -> Vec<BitLit>` — append `k` zeros at MSB.
  - `fn sign_extend(a: &[BitLit], k: u32) -> Vec<BitLit>` — append `k` copies of the MSB.
  - `fn repeat(a: &[BitLit], k: u32) -> Vec<BitLit>` — `k` concatenated copies.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::Blaster;

    fn vars(b: &mut Blaster, n: usize) -> Vec<crate::blast::BitLit> {
        (0..n).map(|_| b.fresh()).collect()
    }

    #[test]
    fn concat_orders_first_arg_high() {
        let mut b = Blaster::new();
        let hi = vars(&mut b, 2); // [h0,h1]
        let lo = vars(&mut b, 3); // [l0,l1,l2]
        let c = concat(&hi, &lo); // width 5, LSB..MSB = l0,l1,l2,h0,h1
        assert_eq!(c.len(), 5);
        assert_eq!(c[0], lo[0]);
        assert_eq!(c[3], hi[0]);
    }

    #[test]
    fn extract_slices_inclusive() {
        let mut b = Blaster::new();
        let a = vars(&mut b, 8);
        let e = extract(&a, 3, 1); // bits 1,2,3
        assert_eq!(e, vec![a[1], a[2], a[3]]);
    }

    #[test]
    fn sign_extend_copies_msb() {
        let mut b = Blaster::new();
        let a = vars(&mut b, 4);
        let s = sign_extend(&a, 2);
        assert_eq!(s.len(), 6);
        assert_eq!(s[4], a[3]);
        assert_eq!(s[5], a[3]);
    }

    #[test]
    fn zero_extend_pads_zero() {
        let mut b = Blaster::new();
        let a = vars(&mut b, 4);
        let z = zero_extend(&a, 2, &b);
        assert_eq!(z.len(), 6);
        assert_eq!(z[4], b.zero());
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv structural`
Expected: FAIL — module/functions missing.

- [ ] **Step 3: Implement**

```rust
use crate::blast::{BitLit, Blaster};

pub fn concat(hi: &[BitLit], lo: &[BitLit]) -> Vec<BitLit> {
    let mut v = Vec::with_capacity(hi.len() + lo.len());
    v.extend_from_slice(lo);
    v.extend_from_slice(hi);
    v
}
pub fn extract(a: &[BitLit], hi: u32, lo: u32) -> Vec<BitLit> {
    a[lo as usize..=hi as usize].to_vec()
}
pub fn zero_extend(a: &[BitLit], k: u32, b: &Blaster) -> Vec<BitLit> {
    let mut v = a.to_vec();
    v.extend(std::iter::repeat(b.zero()).take(k as usize));
    v
}
pub fn sign_extend(a: &[BitLit], k: u32) -> Vec<BitLit> {
    let msb = *a.last().expect("nonzero width");
    let mut v = a.to_vec();
    v.extend(std::iter::repeat(msb).take(k as usize));
    v
}
pub fn repeat(a: &[BitLit], k: u32) -> Vec<BitLit> {
    let mut v = Vec::with_capacity(a.len() * k as usize);
    for _ in 0..k { v.extend_from_slice(a); }
    v
}
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv structural`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/
git commit -m "feat(bv): structural gadgets (concat/extract/extend/repeat)"
```

---

## Task 8: Bitwise gadgets

**Files:**
- Create: `crates/shinri-bv/src/blast/bitwise.rs`
- Modify: `crates/shinri-bv/src/blast/mod.rs`
- Test: `crates/shinri-bv/src/blast/bitwise.rs`

**Interfaces:**
- Consumes: `Blaster` gates (Task 6).
- Produces, each `(&mut Blaster, &[BitLit], &[BitLit]) -> Vec<BitLit>` (same width): `bvand, bvor, bvxor, bvnand, bvnor, bvxnor`; and `bvnot(&mut Blaster, &[BitLit]) -> Vec<BitLit>`.

- [ ] **Step 1: Write the failing test**

Use `shinri-sat` to *solve* a tiny instance and confirm semantics. Helper to pin a word to a constant and read it back:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::{Blaster, BitLit};
    use crate::testkit::{pin_const, solve_value}; // add a small test helper module

    #[test]
    fn bvand_truth() {
        for x in 0u8..=255 { for y in 0u8..=255u8.wrapping_add(0) {
            // sample a few to keep it fast:
        }}
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1100, 4);
        let y = pin_const(&mut b, 0b1010, 4);
        let r = bvand(&mut b, &x, &y);
        assert_eq!(solve_value(b, &r), 0b1000);
    }
}
```

Add `crates/shinri-bv/src/testkit.rs` (cfg(test)) providing:
- `pin_const(b: &mut Blaster, val: u64, width: u32) -> Vec<BitLit>`: fresh bits, add unit clauses fixing each bit to `val`'s bit.
- `solve_value(b: Blaster, bits: &[BitLit]) -> u64`: finish CNF, build a `shinri_sat::Solver` with `num_vars` vars, add every clause (map `BitLit{var,pos}` → `Lit`), solve, read the model bits of `bits`, pack LSB→MSB.

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv bitwise`
Expected: FAIL — module missing.

- [ ] **Step 3: Implement**

```rust
use crate::blast::{BitLit, Blaster};

fn zip_map(b: &mut Blaster, x: &[BitLit], y: &[BitLit], mut f: impl FnMut(&mut Blaster, BitLit, BitLit) -> BitLit) -> Vec<BitLit> {
    debug_assert_eq!(x.len(), y.len());
    x.iter().zip(y).map(|(&a, &c)| f(b, a, c)).collect()
}
pub fn bvand(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> { zip_map(b, x, y, Blaster::and2) }
pub fn bvor (b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> { zip_map(b, x, y, Blaster::or2) }
pub fn bvxor(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> { zip_map(b, x, y, Blaster::xor2) }
pub fn bvnot(b: &mut Blaster, x: &[BitLit]) -> Vec<BitLit> { x.iter().map(|&a| b.not1(a)).collect() }
pub fn bvnand(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> { let t = bvand(b,x,y); bvnot(b,&t) }
pub fn bvnor (b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> { let t = bvor (b,x,y); bvnot(b,&t) }
pub fn bvxnor(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> { let t = bvxor(b,x,y); bvnot(b,&t) }
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv bitwise`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/bitwise.rs crates/shinri-bv/src/testkit.rs crates/shinri-bv/src/blast/mod.rs
git commit -m "feat(bv): bitwise gadgets + test harness (pin_const/solve_value)"
```

---

## Task 9: Arithmetic — add/sub/neg

**Files:**
- Create: `crates/shinri-bv/src/blast/arith.rs`
- Modify: `crates/shinri-bv/src/blast/mod.rs`
- Test: `crates/shinri-bv/src/blast/arith.rs`

**Interfaces:**
- Consumes: `Blaster::full_adder`, bitwise `bvnot` (Task 8), `testkit`.
- Produces:
  - `fn adder(b, x, y, cin: BitLit) -> (Vec<BitLit> /*sum*/, BitLit /*cout*/)` — ripple-carry, width = `x.len()`.
  - `fn bvadd(b, x, y) -> Vec<BitLit>` — `adder(x,y,0).0`.
  - `fn bvneg(b, x) -> Vec<BitLit>` — `adder(not x, 1, 0).0` (two's complement).
  - `fn bvsub(b, x, y) -> Vec<BitLit>` — `adder(x, not y, 1).0`.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::Blaster;
    use crate::testkit::{pin_const, solve_value};

    #[test]
    fn bvadd_wraps_mod_2pow_w() {
        for (x, y) in [(0u64,0u64),(1,1),(255,1),(200,100),(123,77)] {
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x, 8);
            let yv = pin_const(&mut b, y, 8);
            let r = bvadd(&mut b, &xv, &yv);
            assert_eq!(solve_value(b, &r), (x + y) & 0xFF, "x={x} y={y}");
        }
    }

    #[test]
    fn bvsub_and_neg() {
        let mut b = Blaster::new();
        let xv = pin_const(&mut b, 5, 8);
        let yv = pin_const(&mut b, 9, 8);
        let r = bvsub(&mut b, &xv, &yv); // 5-9 = -4 = 252 mod 256
        assert_eq!(solve_value(b, &r), 252);
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv arith`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
use crate::blast::{BitLit, Blaster};
use crate::blast::bitwise::bvnot;

pub fn adder(b: &mut Blaster, x: &[BitLit], y: &[BitLit], cin: BitLit) -> (Vec<BitLit>, BitLit) {
    debug_assert_eq!(x.len(), y.len());
    let mut carry = cin;
    let mut sum = Vec::with_capacity(x.len());
    for i in 0..x.len() {
        let (s, c) = b.full_adder(x[i], y[i], carry);
        sum.push(s);
        carry = c;
    }
    (sum, carry)
}
pub fn bvadd(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let z = b.zero(); adder(b, x, y, z).0
}
pub fn bvneg(b: &mut Blaster, x: &[BitLit]) -> Vec<BitLit> {
    let nx = bvnot(b, x);
    let ones: Vec<BitLit> = (0..x.len()).map(|i| if i == 0 { b.one() } else { b.zero() }).collect();
    let z = b.zero(); adder(b, &nx, &ones, z).0
}
pub fn bvsub(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let ny = bvnot(b, y);
    let one = b.one(); adder(b, x, &ny, one).0
}
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv arith`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/arith.rs crates/shinri-bv/src/blast/mod.rs
git commit -m "feat(bv): ripple-carry add/sub/neg"
```

---

## Task 10: Multiplier

**Files:**
- Modify: `crates/shinri-bv/src/blast/arith.rs`
- Test: `crates/shinri-bv/src/blast/arith.rs`

**Interfaces:**
- Consumes: `adder`, `Blaster::and2`, `mux2`.
- Produces: `fn bvmul(b, x, y) -> Vec<BitLit>` — width = `x.len()`, low `n` bits of the product (mod 2^n).

Algorithm: shift-add. For each bit `y[i]`, form the partial product `pp_i = (x AND y[i]) << i` truncated to `n` bits, then sum all partials with `adder` (carry-out discarded — truncation is mod 2^n).

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn bvmul_mod_256() {
    for (x, y) in [(0u64,7u64),(1,1),(13,13),(255,255),(16,16),(200,3)] {
        let mut b = Blaster::new();
        let xv = pin_const(&mut b, x, 8);
        let yv = pin_const(&mut b, y, 8);
        let r = bvmul(&mut b, &xv, &yv);
        assert_eq!(solve_value(b, &r), (x * y) & 0xFF, "x={x} y={y}");
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv bvmul`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
pub fn bvmul(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let n = x.len();
    let zero = b.zero();
    let mut acc: Vec<BitLit> = vec![zero; n];
    for i in 0..n {
        // partial = (x AND y[i]) shifted left by i, truncated to n bits.
        let mut partial = vec![zero; n];
        for j in 0..(n - i) {
            partial[i + j] = b.and2(x[j], y[i]);
        }
        acc = adder(b, &acc, &partial, zero).0;
    }
    acc
}
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv bvmul`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/arith.rs
git commit -m "feat(bv): shift-add multiplier (mod 2^n)"
```

---

## Task 11: Divider family (udiv/urem/sdiv/srem/smod)

**Files:**
- Create: `crates/shinri-bv/src/blast/div.rs`
- Modify: `crates/shinri-bv/src/blast/mod.rs`
- Test: `crates/shinri-bv/src/blast/div.rs`

**Interfaces:**
- Consumes: `adder`, `bvsub`, `bvneg`, `mux2`, comparators are not needed (use the subtract-borrow directly).
- Produces:
  - `fn udivurem(b, x, y) -> (Vec<BitLit> /*quot*/, Vec<BitLit> /*rem*/)` — restoring division. SMT-LIB semantics: if `y == 0`, `bvudiv` returns all-ones and `bvurem` returns `x`.
  - `fn bvudiv(b,x,y)`, `fn bvurem(b,x,y)` — projections.
  - `fn bvsdiv`, `fn bvsrem`, `fn bvsmod` — signed, defined via the unsigned core and sign fixups (SMT-LIB definitions below).

**Restoring division (n-bit, unsigned):** maintain a `2n`-wide running remainder `R` (start 0), process dividend bits MSB→LSB. At each step: shift `R` left by 1, bring in dividend bit; trial-subtract divisor from the high half; if no borrow (R_high >= divisor) keep and set quotient bit 1, else restore and set quotient bit 0. Implement the conditional keep/restore with `mux2` on the borrow-out of the subtractor.

**`y == 0` handling:** compute `is_zero_y = NOR of all y bits`. Final `quot = mux(is_zero_y, all_ones, quot)`, `rem = mux(is_zero_y, x, rem)`.

**Signed definitions (SMT-LIB):**
- `bvsdiv x y`: let `sx = msb(x)`, `sy = msb(y)`; `ux = if sx then bvneg x else x`, `uy = if sy then bvneg y else y`; `u = bvudiv ux uy`; `bvsdiv = if sx xor sy then bvneg u else u`.
- `bvsrem x y`: `u = bvurem ux uy`; `bvsrem = if sx then bvneg u else u` (sign follows dividend).
- `bvsmod x y`: per SMT-LIB reference definition — compute `u = bvurem ux uy`; if `u == 0` → 0; else combine signs: result sign follows divisor. Implement the exact reference: 
  - if `sx==0 && sy==0` → `u`
  - if `sx==1 && sy==0` → `bvneg u + y` (i.e. `bvadd (bvneg u) y`), unless `u==0` → 0
  - if `sx==0 && sy==1` → `u + y`, unless `u==0` → 0
  - if `sx==1 && sy==1` → `bvneg u`
  Use `mux2` chains keyed on `sx`, `sy`, and `u==0`.

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::Blaster;
    use crate::testkit::{pin_const, solve_value};

    #[test]
    fn udiv_urem_including_zero_divisor() {
        let cases = [(17u64,5u64),(255,16),(0,3),(7,7),(10,0),(255,0)];
        for (x, y) in cases {
            let (eq, er) = if y == 0 { (0xFF, x) } else { (x / y, x % y) };
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x, 8);
            let yv = pin_const(&mut b, y, 8);
            let (q, r) = udivurem(&mut b, &xv, &yv);
            // solve once: pack a combined check by solving twice on clones is wasteful;
            // instead solve_value supports reading two slices. If not, split into two Blasters.
            assert_eq!(solve_value_pair(b, &q, &r), (eq, er), "x={x} y={y}");
        }
    }

    #[test]
    fn sdiv_srem_smod_signed() {
        // 8-bit signed: -7 / 2 = -3 (trunc), -7 srem 2 = -1, -7 smod 2 = 1
        let neg7 = 249u64; // 256-7
        let mut b = Blaster::new();
        let xv = pin_const(&mut b, neg7, 8);
        let yv = pin_const(&mut b, 2, 8);
        let d = bvsdiv(&mut b, &xv, &yv);
        assert_eq!(solve_value(b, &d) as i8, -3);
        // (repeat with fresh Blasters for srem/smod)
    }
}
```

Add `solve_value_pair(b, &[BitLit], &[BitLit]) -> (u64, u64)` to `testkit` (one solve, read two slices).

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv div`
Expected: FAIL.

- [ ] **Step 3: Implement**

Implement `udivurem` with the restoring algorithm described above, then the unsigned projections, then `is_zero` helper (`NOR` of bits), then the signed wrappers exactly per the SMT-LIB definitions listed. Key helper:

```rust
use crate::blast::{BitLit, Blaster};
use crate::blast::arith::{adder, bvadd, bvneg, bvsub};

fn is_zero(b: &mut Blaster, x: &[BitLit]) -> BitLit {
    // OR all bits, then negate.
    let mut acc = x[0];
    for &bit in &x[1..] { acc = b.or2(acc, bit); }
    b.not1(acc)
}

// trial-subtract: returns (diff, borrow_out). diff = a - d (n-bit), borrow_out=1 iff a < d.
fn sub_borrow(b: &mut Blaster, a: &[BitLit], d: &[BitLit]) -> (Vec<BitLit>, BitLit) {
    // a - d = a + (~d) + 1; carry_out==1 means no borrow. borrow = !carry_out.
    let nd: Vec<BitLit> = d.iter().map(|&x| b.not1(x)).collect();
    let one = b.one();
    let (diff, carry) = adder(b, a, &nd, one);
    (diff, b.not1(carry))
}

pub fn udivurem(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> (Vec<BitLit>, Vec<BitLit>) {
    let n = x.len();
    let zero = b.zero();
    let mut rem: Vec<BitLit> = vec![zero; n];     // current remainder (n bits suffice)
    let mut quot: Vec<BitLit> = vec![zero; n];
    for i in (0..n).rev() {
        // rem = (rem << 1) | x[i]
        let mut shifted = vec![x[i]];
        shifted.extend_from_slice(&rem[..n - 1]);
        rem = shifted;
        // trial subtract divisor
        let (diff, borrow) = sub_borrow(b, &rem, y);
        // if no borrow: rem = diff, quot[i] = 1 ; else keep rem, quot[i]=0
        let keep = b.not1(borrow);
        let new_rem: Vec<BitLit> = (0..n).map(|j| b.mux2(keep, diff[j], rem[j])).collect();
        rem = new_rem;
        quot[i] = keep;
    }
    // divisor == 0 fixups
    let yz = is_zero(b, y);
    let all_ones: Vec<BitLit> = (0..n).map(|_| b.one()).collect();
    let q = (0..n).map(|j| b.mux2(yz, all_ones[j], quot[j])).collect::<Vec<_>>();
    let r = (0..n).map(|j| b.mux2(yz, x[j], rem[j])).collect::<Vec<_>>();
    (q, r)
}
pub fn bvudiv(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> { udivurem(b,x,y).0 }
pub fn bvurem(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> { udivurem(b,x,y).1 }
```

Then signed wrappers (`bvsdiv`, `bvsrem`, `bvsmod`) using `msb = *x.last()`, `mux2` to conditionally negate, and `bvneg`/`bvadd` exactly per the definitions above.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv div`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/div.rs crates/shinri-bv/src/blast/mod.rs crates/shinri-bv/src/testkit.rs
git commit -m "feat(bv): restoring divider — udiv/urem + signed sdiv/srem/smod"
```

---

## Task 12: Shifts and rotates

**Files:**
- Create: `crates/shinri-bv/src/blast/shift.rs`
- Modify: `crates/shinri-bv/src/blast/mod.rs`
- Test: `crates/shinri-bv/src/blast/shift.rs`

**Interfaces:**
- Consumes: `mux2`.
- Produces (shift amount is a BV word, semantics: shift by `y mod 2^n` saturating to "all shifted out" when `y >= n`, per SMT-LIB where shift amounts >= width yield 0 for shl/lshr and sign/zero fill for ashr):
  - `fn bvshl(b, x, y) -> Vec<BitLit>`
  - `fn bvlshr(b, x, y) -> Vec<BitLit>`
  - `fn bvashr(b, x, y) -> Vec<BitLit>`
  - `fn rotate_left(b, x, k: u32) -> Vec<BitLit>` (k constant), `fn rotate_right(b, x, k: u32)`.

Barrel shifter: for stage `s` (0..ceil(log2 n)), shift by `2^s` iff `y[s]` is set, via `mux2` per bit. For `bvshl`, bit `j` of the stage output is `y[s] ? in[j - 2^s] : in[j]` (with 0 fill when `j - 2^s < 0`). For `bvlshr`, fill with 0 from the top; for `bvashr`, fill with the sign bit (`x`'s MSB). If `y` has bits at positions `>= ceil(log2 n)` that are set, the result is fully filled (handle by an extra `any_high_bit_set` mux to the fill value).

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn shifts_match_native() {
    let n = 8u32;
    for x in [0u64, 1, 0x80, 0xFF, 0x3C] {
        for sh in 0u64..=9 { // include sh >= width
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x, n);
            let yv = pin_const(&mut b, sh, n);
            let r = bvshl(&mut b, &xv, &yv);
            let expect = if sh >= 8 { 0 } else { (x << sh) & 0xFF };
            assert_eq!(solve_value(b, &r), expect, "shl x={x} sh={sh}");
        }
    }
}
#[test]
fn ashr_sign_fills() {
    let mut b = Blaster::new();
    let xv = pin_const(&mut b, 0x80, 8); // -128
    let yv = pin_const(&mut b, 3, 8);
    let r = bvashr(&mut b, &xv, &yv);
    assert_eq!(solve_value(b, &r), 0xF0); // arithmetic shift keeps sign
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv shift`
Expected: FAIL.

- [ ] **Step 3: Implement**

Implement the log-depth barrel shifter with explicit fill handling for out-of-range shift amounts (mux the whole word to the fill value when any `y` bit at index `>= log2_ceil(n)` is set). `rotate_left`/`rotate_right` are constant-amount index permutations (`k %= n`), pure slicing like structural gadgets.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv shift`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/shift.rs crates/shinri-bv/src/blast/mod.rs
git commit -m "feat(bv): barrel shifts (shl/lshr/ashr) + constant rotates"
```

---

## Task 13: Comparators (eq + unsigned/signed)

**Files:**
- Create: `crates/shinri-bv/src/blast/compare.rs`
- Modify: `crates/shinri-bv/src/blast/mod.rs`
- Test: `crates/shinri-bv/src/blast/compare.rs`

**Interfaces:**
- Consumes: `xor2`, `and2`, `or2`, `not1`, `sub_borrow` (re-export from div or reimplement locally).
- Produces single-bit outputs:
  - `fn eq(b, x, y) -> BitLit` — AND of bitwise XNOR.
  - `fn ult(b, x, y) -> BitLit` — borrow-out of `x - y`.
  - `fn ule, ugt, uge` — from `ult`/`eq`.
  - `fn slt(b, x, y) -> BitLit` — `ult` with the MSBs flipped (`(x ⊕ 2^{n-1}) <_u (y ⊕ 2^{n-1})`); equivalently classic `slt = (msb_x ∧ ¬msb_y) ∨ ((msb_x = msb_y) ∧ ult(x,y))`.
  - `fn sle, sgt, sge`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn unsigned_and_signed_compares() {
    let probe = |x:u64,y:u64| {
        let mut b = Blaster::new();
        let xv = pin_const(&mut b, x, 8);
        let yv = pin_const(&mut b, y, 8);
        let l = ult(&mut b, &xv, &yv);
        solve_value(b, std::slice::from_ref(&l))
    };
    assert_eq!(probe(3, 5), 1);
    assert_eq!(probe(5, 3), 0);
    assert_eq!(probe(5, 5), 0);

    let sprobe = |x:u64,y:u64| {
        let mut b = Blaster::new();
        let xv = pin_const(&mut b, x, 8);
        let yv = pin_const(&mut b, y, 8);
        let l = slt(&mut b, &xv, &yv);
        solve_value(b, std::slice::from_ref(&l))
    };
    assert_eq!(sprobe(0x80, 1), 1); // -128 < 1
    assert_eq!(sprobe(1, 0x80), 0);
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv compare`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
use crate::blast::{BitLit, Blaster};

pub fn eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    let mut acc = b.one();
    for i in 0..x.len() {
        let xn = b.xor2(x[i], y[i]);     // 1 if differ
        let same = b.not1(xn);
        acc = b.and2(acc, same);
    }
    acc
}
fn ult_core(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    // borrow-out of x - y  ==  x <_u y
    let ny: Vec<BitLit> = y.iter().map(|&v| b.not1(v)).collect();
    let one = b.one();
    let mut carry = one;
    for i in 0..x.len() {
        let (_, c) = b.full_adder(x[i], ny[i], carry);
        carry = c;
    }
    b.not1(carry) // borrow == !carry_out
}
pub fn ult(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { ult_core(b, x, y) }
pub fn ugt(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { ult(b, y, x) }
pub fn ule(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { let g = ugt(b,x,y); b.not1(g) }
pub fn uge(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { let l = ult(b,x,y); b.not1(l) }
pub fn slt(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    let n = x.len();
    let mx = x[n-1]; let my = y[n-1];
    let u = ult_core(b, x, y);
    // (mx ∧ ¬my) ∨ ((mx = my) ∧ u)
    let nmy = b.not1(my);
    let neg_only = b.and2(mx, nmy);
    let same_sign = { let d = b.xor2(mx, my); b.not1(d) };
    let same_and_u = b.and2(same_sign, u);
    b.or2(neg_only, same_and_u)
}
pub fn sgt(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { slt(b, y, x) }
pub fn sle(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { let g = sgt(b,x,y); b.not1(g) }
pub fn sge(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { let l = slt(b,x,y); b.not1(l) }
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv compare`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/compare.rs crates/shinri-bv/src/blast/mod.rs
git commit -m "feat(bv): comparators (eq + unsigned/signed)"
```

---

## Task 14: Blast dispatch — term → bits / term → atom literal

**Files:**
- Modify: `crates/shinri-bv/src/blast/mod.rs`
- Test: `crates/shinri-bv/src/blast/mod.rs`

**Interfaces:**
- Consumes: every gadget module (Tasks 7–13), `Context` term inspection.
- Produces on `Blaster`:
  - `fn blast_word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit>` — recursively bit-blast a BitVec-sorted term; memoized via `self.cache`. Dispatches by `term_node`: `Const::BitVec` → constant bits; `Uninterpreted(_)` nullary (a BV variable) → fresh bits (memoized so the same variable reuses bits); BV `BuiltinOp` apps → the matching gadget.
  - `fn blast_atom(&mut self, ctx: &Context, t: TermId) -> BitLit` — for a Bool-sorted BV predicate (`Eq`/`Distinct` over BV args, or `BvUlt..BvSge`), blast the operand words and return the predicate literal.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn blast_word_constant_and_var_and_add() {
    use shinri_core::{Context, Op, BuiltinOp};
    use shinri_num::Integer;
    let mut ctx = Context::new();
    let s8 = ctx.bv_sort(8);
    let xf = ctx.declare_fun("x", &[], s8);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let c = ctx.mk_bv_const(8, Integer::from(1u32));
    let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, c]).unwrap();

    let mut b = Blaster::new();
    let bits = b.blast_word(&ctx, add);
    assert_eq!(bits.len(), 8);
    // same variable term reuses cached bits
    let bx1 = b.blast_word(&ctx, x);
    let bx2 = b.blast_word(&ctx, x);
    assert_eq!(bx1, bx2);
}

#[test]
fn blast_atom_eq_is_solvable_true() {
    // (= (bvadd x 1) y) with x=1 => y must be 2 for the atom to be true; check SAT.
    // (full end-to-end SAT check lives in integration tests; here assert it returns a lit)
    use shinri_core::{Context, Op, BuiltinOp};
    use shinri_num::Integer;
    let mut ctx = Context::new();
    let s8 = ctx.bv_sort(8);
    let xf = ctx.declare_fun("x", &[], s8);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let one = ctx.mk_bv_const(8, Integer::from(1u32));
    let lhs = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, one]).unwrap();
    let yf = ctx.declare_fun("y", &[], s8);
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let atom = ctx.mk_eq(lhs, y).unwrap();
    let mut b = Blaster::new();
    let _l = b.blast_atom(&ctx, atom);
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv blast_word blast_atom`
Expected: FAIL.

- [ ] **Step 3: Implement**

`blast_word` matches `ctx.term_node(t)`:
- `TermNode::Const { val: ConstVal::BitVec(_), .. }` → read `(width, value)` via `ctx.bv_const_value`; produce `width` bit lits each `b.one()`/`b.zero()` per the value's bit.
- `TermNode::App { op: Op::Uninterpreted(_), args, .. }` with BV sort → fresh bits of width `ctx.bv_width(sort)` (cache by `TermId`). (Nullary = variable; non-nullary uninterpreted over BV is out of scope and must have been fenced earlier — debug_assert nullary.)
- `TermNode::App { op: Op::Builtin(bv_op), args, .. }` → recurse on children, call the gadget. Map every BV `BuiltinOp` to its gadget (structural ops use `concat/extract/...`; arith/bitwise/shift/div to their modules).

`blast_atom` matches the predicate op: `Eq`/`Distinct` over BV → `compare::eq` (negated for Distinct); `BvUlt..BvSge` → the corresponding comparator. Memoize atoms too if convenient. Insert into `self.cache` only for words (atoms return a single `BitLit`).

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv blast_word blast_atom`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/mod.rs
git commit -m "feat(bv): blast dispatch — term→bits and atom→literal"
```

---

## Task 15: Word-level rewrite pass

**Files:**
- Create: `crates/shinri-bv/src/rewrite.rs`
- Modify: `crates/shinri-bv/src/lib.rs`
- Test: `crates/shinri-bv/src/rewrite.rs`

**Interfaces:**
- Consumes: `Context` (mutates to build rewritten terms).
- Produces: `fn rewrite(ctx: &mut Context, t: TermId) -> TermId` — bottom-up simplification returning a semantically-equal BV (or Bool) term. Idempotent.

Rules (apply bottom-up; each rule is semantics-preserving):
- **Constant folding:** all-constant BV apps → a single `mk_bv_const` of the computed value (compute with `shinri_num::Integer`, reduce mod 2^width). Covers every op.
- **Identities:** `x bvadd 0 → x`, `x bvor 0 → x`, `x bvand ~0 → x`, `x bvand 0 → 0`, `x bvor ~0 → ~0`, `x bvxor 0 → x`, `x bvmul 1 → x`, `x bvmul 0 → 0`, `x bvsub 0 → x`, `bvsub x x → 0`, `x bvshl 0 → x`.
- **Lowering:** `bvsub x y → bvadd x (bvneg y)` is left to the blaster (already handled there); do NOT rewrite if it loses constant-folding chances.
- **Nested structural:** `extract i j (concat hi lo)` split across the boundary; `extract i j (extract k l a) → extract (i+l) (j+l) a`.

Keep the rule set small and provably sound; the blaster is the source of truth, so rewrite is purely an optimization. **Do not** add a rule you cannot test by equivalence.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn folds_constants_and_identities() {
    use shinri_core::{Context, Op, BuiltinOp};
    use shinri_num::Integer;
    let mut ctx = Context::new();
    let s8 = ctx.bv_sort(8);
    let a = ctx.mk_bv_const(8, Integer::from(20u32));
    let b = ctx.mk_bv_const(8, Integer::from(22u32));
    let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[a, b]).unwrap();
    let r = rewrite(&mut ctx, add);
    assert_eq!(ctx.bv_const_value(r).unwrap().1, &Integer::from(42u32));

    // x + 0 -> x
    let xf = ctx.declare_fun("x", &[], s8);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let zero = ctx.mk_bv_const(8, Integer::from(0u32));
    let add0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, zero]).unwrap();
    assert_eq!(rewrite(&mut ctx, add0), x);
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv rewrite`
Expected: FAIL.

- [ ] **Step 3: Implement**

Bottom-up: recurse on children first (rebuild the node via `mk_app` if any child changed), then apply the local rules. Constant folding evaluates the op over `Integer` operands. Cache results in an `FxHashMap<TermId, TermId>` to keep it linear.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv rewrite`
Expected: PASS.

- [ ] **Step 5: Add an equivalence (miter) test, then commit**

Add a test that, for a handful of random small formulas, blasts both `t` and `rewrite(t)` and asserts the miter `t != rewrite(t)` is UNSAT (using `testkit`). Then:

```bash
git add crates/shinri-bv/src/rewrite.rs crates/shinri-bv/src/lib.rs
git commit -m "feat(bv): word-level rewrite (const-fold + identities) with miter test"
```

---

## Task 16: `lower()` orchestration

**Files:**
- Modify: `crates/shinri-bv/src/lib.rs`
- Test: `crates/shinri-bv/src/lib.rs`

**Interfaces:**
- Consumes: `rewrite` (Task 15), `Blaster::blast_atom`/`blast_word` (Task 14).
- Produces:
  ```rust
  pub struct Lowered {
      pub cnf: Cnf,                              // num_vars + clauses over BitVar namespace
      pub atom_lit: FxHashMap<TermId, BitLit>,   // each Bool-sorted BV atom -> its literal
      pub var_bits: FxHashMap<TermId, Vec<BitLit>>, // BV variable term -> its bits (for model)
  }
  pub fn lower(ctx: &mut Context, bv_atoms: &[TermId]) -> Lowered;
  ```
  `bv_atoms` is the set of Bool-sorted atoms (from the assertion skeleton) whose top operator is a BV predicate or a (dis)equality over BV operands.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn lower_produces_atom_lits_and_var_bits() {
    use shinri_core::{Context, Op, BuiltinOp};
    use shinri_num::Integer;
    let mut ctx = Context::new();
    let s8 = ctx.bv_sort(8);
    let xf = ctx.declare_fun("x", &[], s8);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let c = ctx.mk_bv_const(8, Integer::from(5u32));
    let atom = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[x, c]).unwrap();

    let lo = lower(&mut ctx, &[atom]);
    assert!(lo.atom_lit.contains_key(&atom));
    assert!(lo.var_bits.contains_key(&x));
    assert!(lo.cnf.num_vars >= 1);
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-bv lower_produces`
Expected: FAIL.

- [ ] **Step 3: Implement**

```rust
pub fn lower(ctx: &mut Context, bv_atoms: &[TermId]) -> Lowered {
    let mut b = Blaster::new();
    let mut atom_lit = FxHashMap::default();
    for &a in bv_atoms {
        let a = rewrite(ctx, a);
        let lit = b.blast_atom(ctx, a);
        atom_lit.insert(a, lit);
    }
    // var_bits: pull every BV-variable term the blaster cached as fresh bits.
    let var_bits = b.exported_var_bits(); // method returning cache entries for nullary uninterpreted BV terms
    Lowered { cnf: b.finish(), atom_lit, var_bits }
}
```

Note: `rewrite` may change the atom TermId, so the key stored is the rewritten atom. The solver-side hook (Task 17) must rewrite the same way to look up — so expose the rewrite mapping too, OR have `lower` accept original atoms and return a `FxHashMap<TermId /*original*/, BitLit>`. **Choose the latter:** key `atom_lit` by the *original* atom id (rewrite internally, store under the original key). Update the test accordingly. Add `Blaster::exported_var_bits(&self) -> FxHashMap<TermId, Vec<BitLit>>` filtering the cache to nullary-uninterpreted BV terms.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-bv lower_produces`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/lib.rs crates/shinri-bv/src/blast/mod.rs
git commit -m "feat(bv): lower() orchestration — rewrite + blast → Lowered"
```

---

## Task 17: Solver integration — BV stage + surrogate wiring

**Files:**
- Create: `crates/shinri-solver/src/bv_stage.rs`
- Modify: `crates/shinri-solver/src/lib.rs`
- Modify: `crates/shinri-solver/src/tseitin.rs`
- Modify: `crates/shinri-solver/Cargo.toml` (add `shinri-bv` dep)
- Test: `crates/shinri-solver/src/lib.rs`

**Interfaces:**
- Consumes: `shinri_bv::{lower, Lowered, BitLit}`, the existing `Encoder`, the SAT solver `new_var`/`add_clause`.
- Produces:
  - `fn solver_uses_bv(ctx, assertions) -> bool` — any BV sort/op present.
  - `fn collect_bv_atoms(ctx, assertions) -> Vec<TermId>` — Bool-sorted subterms whose op is a BV predicate or (dis)equality over BV operands.
  - A `BvSurrogates { atom_to_lit: FxHashMap<TermId, Lit>, var_bits: FxHashMap<TermId, Vec<Var>> }` the `Encoder` consults: when it would call `self.atom(t)` for a BV atom, it instead returns the surrogate `Lit`.
  - Fence: if `solver_uses_bv` AND any non-BV theory atom is present → return `Unknown`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn bv_query_sat_and_unsat() {
    // SAT: exists x:8. x bvadd 1 = 2   (x = 1)
    let mut s = Solver::new();
    let s8 = s.bv_sort(8);
    let x = s.declare_const("x", s8);
    let one = s.bv_numeral(1, 8);
    let two = s.bv_numeral(2, 8);
    let lhs = s.app(Op::Builtin(BuiltinOp::BvAdd), &[x, one]);
    let eq = s.eq(lhs, two);
    s.assert(eq);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);

    // UNSAT: x bvadd 1 = x
    let mut s = Solver::new();
    let s8 = s.bv_sort(8);
    let x = s.declare_const("x", s8);
    let one = s.bv_numeral(1, 8);
    let lhs = s.app(Op::Builtin(BuiltinOp::BvAdd), &[x, one]);
    let eq = s.eq(lhs, x);
    s.assert(eq);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn bv_mixed_with_arith_is_unknown() {
    let mut s = Solver::new();
    let s8 = s.bv_sort(8);
    let x = s.declare_const("x", s8);
    let one = s.bv_numeral(1, 8);
    let bvatom = s.eq(s.app(Op::Builtin(BuiltinOp::BvAdd), &[x, one]), one);
    let r = s.real_sort();
    let y = s.declare_const("y", r);
    let pos = s.app(Op::Builtin(BuiltinOp::Gt), &[y, /* 0.0 */ s.numeral_zero(r)]);
    s.assert(bvatom);
    s.assert(pos);
    assert_eq!(s.check_sat(), SolveOutcome::Unknown);
}
```

Add thin `Solver` API helpers used here: `bv_sort(width)`, `bv_numeral(val, width)` (wrapping `ctx.mk_bv_const`). `numeral_zero` may already exist; if not use the existing numeral constructor.

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-solver bv_query_sat_and_unsat bv_mixed_with_arith_is_unknown`
Expected: FAIL.

- [ ] **Step 3: Implement**

In `check_sat`, before building the `Encoder`:
1. If `solver_uses_bv(&self.ctx, &assertions)`:
   - Compute `bv_atoms = collect_bv_atoms(...)`.
   - If a non-BV theory atom is also present, return `Unknown` (scan assertions; reuse `classify` to detect EUF/Arith/Arrays/Shared atoms outside the BV set).
   - `let lowered = shinri_bv::lower(&mut self.ctx, &bv_atoms);`
   - Allocate a contiguous block of SAT vars: call `sat.new_var()` exactly `lowered.cnf.num_vars` times, recording the first index `base`. Map `BitLit{var,pos}` → `Lit::new(Var(base+var), pos)`. (Var 0 of the blaster is the pinned-true const; its unit clause is in the CNF, so it gets forced true automatically.)
   - Add every clause in `lowered.cnf.clauses` to `sat` via `sat.add_clause(&mapped)`.
   - Build `atom_to_lit: FxHashMap<TermId, Lit>` from `lowered.atom_lit` (mapped) and `var_bits` mapped to `Var`s. Store on the `Encoder` (new field `bv_surrogates: Option<&BvSurrogates>`).
2. In `Encoder::atom` / `encode_uncached`: when `t` is in `bv_surrogates.atom_to_lit`, return that `Lit` instead of registering a theory atom. (Add an early check at the top of `encode_uncached` for Bool-sorted BV atoms.)
3. The Boolean skeleton (and/or/not over BV atoms and other Bool structure) encodes as today; `assert_top` forces each assertion.
4. Keep the existing `Combiner` path for non-BV queries unchanged. For a pure-BV query the `Combiner` is constructed but sees no atoms (fine), or skip building EUF/Arith state — minimal: still build the SAT solver (it is generic over the theory) but no theory atoms are registered.

Model bits: stash `var_bits` (mapped to `Var`) on the `Solver` for Task 18.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-solver bv_query_sat_and_unsat bv_mixed_with_arith_is_unknown`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/bv_stage.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/src/tseitin.rs crates/shinri-solver/Cargo.toml
git commit -m "feat(solver): BV lowering stage — replay CNF, surrogate atoms, mixed-theory fence"
```

---

## Task 18: BV model extraction & `get-value`

**Files:**
- Create: `crates/shinri-bv/src/model.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (model formatting)
- Modify: `crates/shinri-solver/src/model.rs`
- Test: `crates/shinri-solver/src/lib.rs`

**Interfaces:**
- Consumes: the SAT model (bit assignment) + `var_bits` from Task 17.
- Produces: `shinri_bv::model::pack(width, bits: &[bool]) -> shinri_num::Integer`, and solver-side formatting of a BV constant as SMT-LIB `#b…`/`#x…`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn bv_get_model_reports_value() {
    let mut s = Solver::new();
    let s8 = s.bv_sort(8);
    let x = s.declare_const("x", s8);
    let five = s.bv_numeral(5, 8);
    let eq = s.eq(x, five);
    s.assert(eq);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
    let m = s.get_model_string();
    assert!(m.contains("x"));
    assert!(m.contains("#b00000101") || m.contains("#x05"));
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-solver bv_get_model_reports_value`
Expected: FAIL.

- [ ] **Step 3: Implement**

`shinri_bv::model::pack` packs LSB→MSB bits into an `Integer`. Solver-side: for each declared BV constant with recorded `var_bits`, read each var's truth value from the SAT model, pack, and format as `#b` + width bits (MSB→LSB) — or `#x` when width % 4 == 0. Wire into the existing `get-model`/`get-value` formatting path (the same place `display_term` and value strings are produced).

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-solver bv_get_model_reports_value`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/model.rs crates/shinri-solver/src/
git commit -m "feat(bv): model extraction + #b/#x value formatting"
```

---

## Task 19: Differential oracle vs z3 + e2e witnesses

**Files:**
- Create: `crates/shinri-cli/tests/qfbv_oracle.rs` (match the existing oracle test location/pattern)
- Create: `crates/shinri-cli/tests/qfbv_witnesses.rs`
- Test: the two files above

**Interfaces:**
- Consumes: the CLI `solve` entry point on `.smt2` text (as existing oracle tests do).

- [ ] **Step 1: Write the tests**

Mirror the existing z3 differential oracle (e.g. the QF_AX/QF_UFLIA oracle tests). For QF_BV:
- Generate ~N random well-typed QF_BV formulas over a few widths (4, 8, 16) and the full op set; run shinri and z3; assert agreement (`sat`/`unsat`), skipping any shinri `unknown`.
- e2e witnesses: a handful of fixed `.smt2` files with known results, including: overflow wrap (`bvadd` UNSAT identity), `bvudiv` by zero = all-ones, `bvsdiv` sign cases, `concat`/`extract` round-trip, shift-by-width = 0.

```rust
// qfbv_witnesses.rs (sketch — adapt to the existing harness helpers)
#[test]
fn udiv_by_zero_is_all_ones() {
    let src = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
               (assert (= (bvudiv x #x00) #xff))\n(check-sat)\n";
    assert_eq!(run_smt2(src), "sat");
}
```

- [ ] **Step 2: Run to verify they fail (or are skipped if z3 absent)**

Run: `cargo test -p shinri-cli qfbv`
Expected: FAIL initially if helpers/wiring missing; the differential test must `skip` cleanly when `z3` is not on PATH (match existing oracle gating).

- [ ] **Step 3: Implement the harness glue**

Reuse the existing oracle helper module (random term generation + z3 invocation). Add a BV generator. Ensure `unknown` from shinri is treated as a skip, never a mismatch.

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test -p shinri-cli qfbv`
Expected: PASS (differential agrees on all non-`unknown` cases; witnesses match).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-cli/tests/qfbv_oracle.rs crates/shinri-cli/tests/qfbv_witnesses.rs
git commit -m "test(bv): QF_BV differential oracle vs z3 + e2e witnesses"
```

---

## Task 20: Workspace non-regression + full build

**Files:**
- No new source; a final integration gate.

- [ ] **Step 1: Run the whole suite**

Run: `cargo test --workspace`
Expected: PASS — no existing EUF/Arith/Arrays/UFLIA tests regress.

- [ ] **Step 2: Lints/format**

Run: `cargo fmt --all && cargo clippy --workspace --all-targets`
Expected: clean (or only pre-existing warnings).

- [ ] **Step 3: Commit any formatting**

```bash
git add -A
git commit -m "chore(bv): fmt + clippy clean; workspace non-regression green"
```

---

## Self-Review Notes

**Spec coverage:**
- Full operator set → Tasks 7–13 (structural/bitwise/arith/div/shift/compare). ✓
- Word-level rewrite front-end → Task 15. ✓
- Eager bit-blast → CNF, bypassing Combiner → Tasks 6, 14, 16, 17. ✓
- Standalone (no Combiner involvement), mixed-theory → `unknown` → Task 17 fence. ✓
- `#x`/`#b` literals, `(_ BitVec n)`, indexed ops → Tasks 4–5. ✓
- Width as part of sort, checked in core → Tasks 1, 3. ✓
- Model extraction → Task 18. ✓
- Differential vs z3 + non-regression → Tasks 19–20. ✓
- Non-goals (incremental, UFBV/ABV) → respected; re-blast per check (Task 17), mixed fenced (Task 17).

**Type consistency:** `BitLit`/`Cnf`/`Blaster` defined in Task 6 and used unchanged through Tasks 7–18; `Lowered`/`lower` signature fixed in Task 16 and consumed in Task 17; bit order (LSB→MSB) stated in Global Constraints and assumed by every gadget. `atom_lit` keyed by **original** atom TermId (Task 16 Step 3 note) — Task 17's hook looks up the original atom id.

**Open implementation choices deferred to the engineer (all sound):** exact restoring-division remainder width (n vs 2n) — n suffices since each step shifts in one dividend bit; Booth vs shift-add multiplier — plan uses shift-add for clarity (correctness-equivalent).
