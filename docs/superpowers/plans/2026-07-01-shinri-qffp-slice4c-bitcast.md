# QF_FP Slice 4c — BV→FP bitcast Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit the first BV↔FP crossing conversion — BV→FP bit reinterpretation via `FpFromBits` (`(fp sign exp sig)`) and the 1-arg `to_fp` bitcast — as pure bit-wiring through the unified `Lowerer`.

**Architecture:** Two new match arms in `blast_fp_word` consume the BV children's bit-lits (which already route to `blast_bv_word` via the sort-dispatched `Lowerer::word`) and present them as the FP word: `FpFromBits` concatenates `sig ++ exp ++ sign` LSB-first; 1-arg `to_fp` returns the source BV bits verbatim. The soundness fence in `fp_stage.rs` drops these two ops from the crossing set and admits them in the support check. No new circuit, no rounding, no special-value logic.

**Tech Stack:** Rust workspace (`shinri-*` crates), `shinri-bv` `Blaster`/`WordSink` seam, `shinri-num::Integer`, z3 via `easy_smt` for the differential oracle.

## Global Constraints

- **Soundness first:** anything out of scope returns `Unknown`, never a wrong SAT/UNSAT. The only crossing ops admitted this slice are `FpFromBits` and 1-arg `to_fp`. `FpToUbv` / `FpToSbv` / `ToFpUnsigned` / `FpToReal` / `to_fp`-2-arg-BV / symbolic-Real `to_fp` stay fenced.
- **FP word bit order is LSB-first:** bits `[0..sb-1)` significand, `[sb-1..sb-1+eb)` exponent, `[eb+sb-1]` sign — matching the FP-const path at `crates/shinri-fp/src/lib.rs:106-116`.
- **Crossing-canary cross-slice lesson:** after admitting the op, run the **whole** `fp_e2e` suite and grep-audit the crossing-canary array; repoint stale `Unknown`-canaries. Do not run a partial suite.
- **Long differential runs:** the z3 oracle test loops `N_ITERS` and shells out to z3 each iteration — run it in the background yourself, do not block.
- Follow existing file patterns; no unrelated refactoring.

---

### Task 1: Reference model for BV→FP bit packing

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (add `ref_fp_from_bits`; add one test in the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Produces: `pub fn ref_fp_from_bits(eb: u32, sb: u32, sign: u64, exp: &Integer, sig: &Integer) -> Integer` — the packed `(eb+sb)`-bit FP value. Used by Task 5's oracle as the trusted layout and to cross-check the gadget's field order.

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod tests` block at the bottom of `crates/shinri-fp/src/reference.rs`:

```rust
#[test]
fn ref_fp_from_bits_packs_one_float32() {
    // 1.0f32 = sign 0, biased exp 127 (0x7F), trailing sig 0 → 0x3F800000.
    let packed = ref_fp_from_bits(8, 24, 0, &Integer::from(127u64), &Integer::zero());
    assert_eq!(packed, Integer::from(0x3F80_0000u64));
    // Round-trips through decode() to a positive normal.
    assert_eq!(
        decode(8, 24, &packed),
        FpClass::Normal { sign: false, biased_exp: 127, sig: Integer::zero() }
    );
    // Sign bit is the MSB: flipping it yields -1.0's pattern (0xBF800000).
    let neg = ref_fp_from_bits(8, 24, 1, &Integer::from(127u64), &Integer::zero());
    assert_eq!(neg, Integer::from(0xBF80_0000u64));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp --lib ref_fp_from_bits_packs_one_float32`
Expected: FAIL — `cannot find function ref_fp_from_bits in this scope`.

- [ ] **Step 3: Write minimal implementation**

Add near the other `ref_*` decode helpers in `crates/shinri-fp/src/reference.rs` (e.g. just after `decode`):

```rust
/// Pack a (sign, exponent-field, trailing-significand) triple into the (eb, sb)
/// bit pattern. Inverse of `decode`'s field extraction: MSB is the sign, then
/// the eb-bit biased exponent, then the (sb-1)-bit trailing significand.
/// `packed = sign·2^(eb+sb-1) + exp·2^(sb-1) + sig`.
pub fn ref_fp_from_bits(eb: u32, sb: u32, sign: u64, exp: &Integer, sig: &Integer) -> Integer {
    let two = Integer::from(2u64);
    let pow = |k: u32| {
        let mut m = Integer::one();
        for _ in 0..k {
            m = m * two.clone();
        }
        m
    };
    Integer::from(sign) * pow(eb + sb - 1) + exp.clone() * pow(sb - 1) + sig.clone()
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp --lib ref_fp_from_bits_packs_one_float32`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): ref_fp_from_bits — exact BV→FP bit-packing golden (slice 4c)"
```

---

### Task 2: The bitcast gadget in `blast_fp_word`

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` — add an `FpFromBits` arm and branch the `ToFp` arm on arity in `blast_fp_word` (around lib.rs:192-204); add two tests in the existing `#[cfg(test)] mod lower_tests`.

**Interfaces:**
- Consumes: `WordSink::word` (routes BV-sorted children to `blast_bv_word` under a `Lowerer`), `crate::lower::Lowerer`.
- Produces: `blast_fp_word` now returns a wired FP word for `FpFromBits` (kids `[sign, exp, sig]`) and 1-arg `ToFp` (kids `[bv]`). Consumed end-to-end by Task 3's fence lift.

- [ ] **Step 1: Write the failing tests**

Add to `#[cfg(test)] mod lower_tests` in `crates/shinri-fp/src/lib.rs` (this module already has `use super::*;` and `use shinri_core::{BuiltinOp, Context, Op};`). Add `use shinri_bv::WordSink;` and `use crate::lower::Lowerer;` at the top of the module if not already present:

```rust
#[test]
fn fp_from_bits_wires_children_lsb_first() {
    let mut ctx = Context::new();
    let bv1 = ctx.bv_sort(1);
    let bv8 = ctx.bv_sort(8);
    let bv23 = ctx.bv_sort(23);
    let sf = ctx.declare_fun("s", &[], bv1);
    let ef = ctx.declare_fun("e", &[], bv8);
    let mf = ctx.declare_fun("m", &[], bv23);
    let s = ctx.mk_app(Op::Uninterpreted(sf), &[]).unwrap();
    let e = ctx.mk_app(Op::Uninterpreted(ef), &[]).unwrap();
    let m = ctx.mk_app(Op::Uninterpreted(mf), &[]).unwrap();
    let fp = ctx.mk_app(Op::Builtin(BuiltinOp::FpFromBits), &[s, e, m]).unwrap();

    let mut lw = Lowerer::new();
    let sw = lw.word(&ctx, s);
    let ew = lw.word(&ctx, e);
    let mw = lw.word(&ctx, m);
    let fw = lw.word(&ctx, fp);

    assert_eq!(fw.len(), 32, "FpFromBits result is eb+sb bits");
    // LSB-first packing: significand (23) ++ exponent (8) ++ sign (1).
    let expect: Vec<_> = mw.iter().chain(ew.iter()).chain(sw.iter()).copied().collect();
    assert_eq!(fw, expect, "children wired sig ++ exp ++ sign, LSB-first");
}

#[test]
fn to_fp_1arg_bitcast_is_identity() {
    let mut ctx = Context::new();
    let bv32 = ctx.bv_sort(32);
    let bf = ctx.declare_fun("b", &[], bv32);
    let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
    let cast = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b]).unwrap();

    let mut lw = Lowerer::new();
    let bw = lw.word(&ctx, b);
    let fw = lw.word(&ctx, cast);

    assert_eq!(fw, bw, "1-arg to_fp reinterprets the same bits verbatim");
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp --lib fp_from_bits_wires_children_lsb_first to_fp_1arg_bitcast_is_identity`
Expected: FAIL — `blast_fp_word` hits `unreachable!("blast_word: FP op FpFromBits …")` for the first, and the `ToFp` arm panics on the 1-arg case (`blast_rm` on the BV operand) for the second.

- [ ] **Step 3: Write the gadget**

In `crates/shinri-fp/src/lib.rs`, inside `blast_fp_word`'s `Op::Builtin(op)` match, add an `FpFromBits` arm and replace the existing `ToFp { .. }` arm. The current `ToFp` arm is:

```rust
                ToFp { .. } => {
                    // Non-BV faces only (fence guarantees this): 2 args (RM, X), X = Float | const Real.
                    // `eb`/`sb` here are the outer target widths (result sort); source is X's sort.
                    let rm = blast_rm(sink, ctx, kids[0]);
                    if let Some(q) = ctx.const_real_value(kids[1]) {
                        crate::convert::to_fp_real_const(sink.blaster(), &q, eb, sb, &rm)
                    } else {
                        let (eb_s, sb_s) = ctx.fp_widths(ctx.sort_of(kids[1])).expect("FP source operand");
                        let xw = sink.word(ctx, kids[1]);
                        crate::convert::to_fp_fp(sink.blaster(), &xw, eb_s, sb_s, eb, sb, &rm)
                    }
                }
```

Replace it with (and add the `FpFromBits` arm just before it):

```rust
                FpFromBits => {
                    // (fp sign exp sig): assemble the FP word from three BV children.
                    // Pure wiring — LSB-first significand ++ exponent ++ sign. Each
                    // child is BV-sorted and routes to `blast_bv_word` via the
                    // sort-dispatched sink (const children → constant bit-lits,
                    // symbolic → fresh vars). Widths (1, eb, sb-1) are guaranteed by
                    // the parser's FpFromBits sort check, so the concat is exactly
                    // eb+sb bits. Requires the unified `Lowerer` sink (the pure-FP
                    // `FpBlaster` cannot blast BV children — crossing ops are only
                    // reached via `lower_mixed`/`lower`, both `Lowerer`-backed).
                    let sign = sink.word(ctx, kids[0]);
                    let exp = sink.word(ctx, kids[1]);
                    let sig = sink.word(ctx, kids[2]);
                    let mut out = sig;
                    out.extend(exp);
                    out.extend(sign);
                    out
                }
                ToFp { .. } => {
                    if kids.len() == 1 {
                        // 1-arg bitcast: a single BV of width eb+sb reinterpreted as
                        // the IEEE bit pattern. Same LSB-first layout on both sides,
                        // so the BV word IS the FP word — passthrough.
                        sink.word(ctx, kids[0])
                    } else {
                        // 2-arg (RM, X), X = Float (FP→FP re-round) | const Real (fold).
                        // BV / symbolic-Real sources stay fenced (later slices).
                        let rm = blast_rm(sink, ctx, kids[0]);
                        if let Some(q) = ctx.const_real_value(kids[1]) {
                            crate::convert::to_fp_real_const(sink.blaster(), &q, eb, sb, &rm)
                        } else {
                            let (eb_s, sb_s) = ctx.fp_widths(ctx.sort_of(kids[1])).expect("FP source operand");
                            let xw = sink.word(ctx, kids[1]);
                            crate::convert::to_fp_fp(sink.blaster(), &xw, eb_s, sb_s, eb, sb, &rm)
                        }
                    }
                }
```

Note: `eb`/`sb` are already bound at the top of the `Op::Builtin(op)` arm (`let (eb, sb) = ctx.fp_widths(sort)…`); the `FpFromBits` arm does not use them but that is fine — `#[allow]` is unnecessary since they are used by other arms.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp --lib fp_from_bits_wires_children_lsb_first to_fp_1arg_bitcast_is_identity`
Expected: PASS.

- [ ] **Step 5: Confirm no pure-FP regression**

Run: `cargo test -p shinri-fp`
Expected: PASS (all existing FP unit tests green — the gadget only adds arms).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): blast_fp_word gadget for BV→FP bitcast (FpFromBits + 1-arg to_fp) (slice 4c)"
```

---

### Task 3: Lift the fence — admit the two bitcast ops

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` — `uses_crossing_conversion` (drop `FpFromBits` + `ToFp` 1-arg), `is_supported_fp_word` (add `FpFromBits` arm, extend `ToFp` arm); add tests in the existing `#[cfg(test)] mod tests`.

**Interfaces:**
- Consumes: `is_fp_sorted` semantics (BV children are not FP-sorted), the total BV blaster invariant.
- Produces: `uses_crossing_conversion` returns `false` for `FpFromBits`/1-arg `ToFp`; `fp_atoms_fully_supported` returns `true` for atoms nesting them. End-to-end bitcast solving now works.

- [ ] **Step 1: Write the failing tests**

Add to `#[cfg(test)] mod tests` in `crates/shinri-solver/src/fp_stage.rs` (helpers `fp_var` etc. exist; add BV helpers inline):

```rust
#[test]
fn bitcast_ops_are_not_crossing_but_others_still_are() {
    let mut ctx = Context::new();
    let bv1 = ctx.bv_sort(1);
    let bv8 = ctx.bv_sort(8);
    let bv23 = ctx.bv_sort(23);
    let bv32 = ctx.bv_sort(32);
    let mk = |ctx: &mut Context, s| {
        let f = ctx.declare_fun("v", &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    };
    let s = mk(&mut ctx, bv1);
    let e = mk(&mut ctx, bv8);
    let m = mk(&mut ctx, bv23);
    let fp_from_bits = ctx.mk_app(Op::Builtin(BuiltinOp::FpFromBits), &[s, e, m]).unwrap();
    let b32 = mk(&mut ctx, bv32);
    let bitcast = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b32]).unwrap();

    // Newly admitted — NOT crossing.
    assert!(!super::uses_crossing_conversion(&ctx, &[fp_from_bits]), "FpFromBits admitted");
    assert!(!super::uses_crossing_conversion(&ctx, &[bitcast]), "1-arg to_fp admitted");

    // Still crossing: fp.to_sbv over an FP var.
    let x = fp_var(&mut ctx, "x");
    let rm_s = ctx.rm_sort();
    let rmf = ctx.declare_fun("rm", &[], rm_s);
    let rm = ctx.mk_app(Op::Uninterpreted(rmf), &[]).unwrap();
    let to_sbv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToSbv(32)), &[rm, x]).unwrap();
    assert!(super::uses_crossing_conversion(&ctx, &[to_sbv]), "fp.to_sbv still crossing");
}

#[test]
fn is_supported_fp_word_admits_bitcast() {
    let mut ctx = Context::new();
    let bv1 = ctx.bv_sort(1);
    let bv8 = ctx.bv_sort(8);
    let bv23 = ctx.bv_sort(23);
    let bv32 = ctx.bv_sort(32);
    let mk = |ctx: &mut Context, s| {
        let f = ctx.declare_fun("v", &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    };
    let s = mk(&mut ctx, bv1);
    let e = mk(&mut ctx, bv8);
    let m = mk(&mut ctx, bv23);
    let fp_from_bits = ctx.mk_app(Op::Builtin(BuiltinOp::FpFromBits), &[s, e, m]).unwrap();
    let b32 = mk(&mut ctx, bv32);
    let bitcast = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b32]).unwrap();

    assert!(super::is_supported_fp_word(&ctx, fp_from_bits), "FpFromBits word supported");
    assert!(super::is_supported_fp_word(&ctx, bitcast), "1-arg to_fp word supported");
}
```

(`rm_sort()` is the RM-sort accessor, confirmed in `context.rs:123`.)

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-solver --lib fp_stage::tests::bitcast_ops_are_not_crossing_but_others_still_are fp_stage::tests::is_supported_fp_word_admits_bitcast`
Expected: FAIL — `uses_crossing_conversion` still returns `true` for both; `is_supported_fp_word` returns `false` for both.

- [ ] **Step 3: Drop the two ops from the crossing set**

In `crates/shinri-solver/src/fp_stage.rs`, `uses_crossing_conversion`, change the `is_crossing` match. Remove `FpFromBits` from the always-crossing list and change the `ToFp` `1 => true` arm to `1 => false`:

```rust
            let is_crossing = match op {
                Op::Builtin(BuiltinOp::FpToUbv(_))
                | Op::Builtin(BuiltinOp::FpToSbv(_))
                | Op::Builtin(BuiltinOp::ToFpUnsigned { .. })
                | Op::Builtin(BuiltinOp::FpToReal) => true,
                Op::Builtin(BuiltinOp::ToFp { .. }) => match kids.len() {
                    1 => false, // 1-arg BV bitcast — admitted in slice 4c
                    2 => match ctx.sort_node(ctx.sort_of(kids[1])) {
                        SortNode::BitVec(_) => true, // signed-BV → FP (later slice)
                        SortNode::Real => ctx.const_real_value(kids[1]).is_none(),
                        _ => false, // Float → FP (3a-supported)
                    },
                    _ => true, // defensive: unexpected arity
                },
                _ => false,
            };
```

Also update the doc comment above `uses_crossing_conversion` (lines ~50-62): remove `FpFromBits` from the "always crossing" bullet and note the 1-arg `to_fp` bitcast is now admitted; keep the others.

- [ ] **Step 4: Add the support arms**

In the same file, `is_supported_fp_word`, add an `FpFromBits` arm and extend the `ToFp` arm. Add before the final `_ => false`:

```rust
        // fp constructor (fp sign exp sig): three BV-sorted children. The BV
        // blaster is total, and any still-crossing op nested in a child is caught
        // by `uses_crossing_conversion` before lowering — so a BV-sort check on
        // the children suffices (no recursive FP-support call).
        TermNode::App { op: Op::Builtin(BuiltinOp::FpFromBits), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 3
                && kids.iter().all(|&k| matches!(ctx.sort_node(ctx.sort_of(k)), SortNode::BitVec(_)))
        }
```

And change the existing `ToFp { .. }` arm from:

```rust
        TermNode::App { op: Op::Builtin(BuiltinOp::ToFp { .. }), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_rounding_mode_term(ctx, kids[0])
                && (is_supported_fp_word(ctx, kids[1]) || ctx.const_real_value(kids[1]).is_some())
        }
```

to:

```rust
        TermNode::App { op: Op::Builtin(BuiltinOp::ToFp { .. }), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            match kids.len() {
                // 1-arg BV bitcast: single BV-sorted source (slice 4c).
                1 => matches!(ctx.sort_node(ctx.sort_of(kids[0])), SortNode::BitVec(_)),
                // 2-arg non-BV faces: FP→FP re-round or constant-Real fold (3a).
                2 => is_rounding_mode_term(ctx, kids[0])
                    && (is_supported_fp_word(ctx, kids[1]) || ctx.const_real_value(kids[1]).is_some()),
                _ => false,
            }
        }
```

- [ ] **Step 5: Run the fp_stage tests to verify they pass**

Run: `cargo test -p shinri-solver --lib fp_stage`
Expected: PASS (new tests green; existing `fp_stage` unit tests — arity rejections, `fp.min inside fp.eq`, etc. — still green).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): lift the fence for BV→FP bitcast (FpFromBits + 1-arg to_fp) (slice 4c)"
```

---

### Task 4: End-to-end SAT/UNSAT + get-model, and repoint the crossing canary

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` — add a slice-4c e2e test block; remove the now-solvable 1-arg-bitcast entry from `to_fp_bv_crossing_and_symbolic_real_are_unknown`.

**Interfaces:**
- Consumes: `run(src) -> (SolveOutcome, String)` (already in the file).

- [ ] **Step 1: Write the failing e2e tests**

Add a new block near the end of `crates/shinri-solver/tests/fp_e2e.rs`:

```rust
// ── Slice-4c end-to-end: BV→FP bitcast (FpFromBits + 1-arg to_fp) ───────────
#[test]
fn fp_from_bits_known_value_sat() {
    // (fp #b0 #b11111111 #b0…0) is +oo. Pins the field layout semantically:
    // sign=0 (MSB), exp=all-ones, sig=0. A wrong concat order would break this.
    let src = "\
(declare-fun z () (_ FloatingPoint 8 24))
(assert (fp.eq z (fp #b0 #b11111111 #b00000000000000000000000)))
(assert (fp.isInfinite z))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "(fp 0 all-ones 0) is +oo");
}

#[test]
fn fp_from_bits_sign_bit_is_msb_unsat() {
    // Same pattern but sign=1 → -oo, which is fp.eq-distinct from +oo → UNSAT.
    let src = "\
(assert (fp.eq (fp #b1 #b11111111 #b00000000000000000000000) (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat, "sign bit is the MSB: (fp 1 …) is -oo, not +oo");
}

#[test]
fn fp_from_bits_symbolic_child_sat_with_model() {
    // Symbolic BV sign feeding an FP atom; get-model surfaces both the BV child
    // and the resulting FP var.
    let src = "\
(declare-fun s () (_ BitVec 1))
(declare-fun z () (_ FloatingPoint 8 24))
(assert (fp.eq z (fp s #b11111111 #b00000000000000000000000)))
(assert (fp.isInfinite z))
(check-sat)
(get-model)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "∃ sign bit making (fp s all-ones 0) infinite");
    assert!(model.contains("s"), "model surfaces the symbolic BV child");
    assert!(model.contains("z"), "model surfaces the FP var");
}

#[test]
fn to_fp_1arg_bitcast_known_value_sat() {
    // 0x7f800000 is the IEEE-754 bit pattern for +oo (float32). The 1-arg
    // to_fp reinterprets it; isInfinite must hold.
    let src = "\
(declare-fun b () (_ BitVec 32))
(assert (= b #x7f800000))
(assert (fp.isInfinite ((_ to_fp 8 24) b)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "0x7f800000 bitcasts to +oo");
}
```

- [ ] **Step 2: Run to verify they pass** (the gadget + fence are already in place from Tasks 2–3)

Run: `cargo test -p shinri-solver --test fp_e2e fp_from_bits to_fp_1arg`
Expected: PASS. (If any FAIL as `Unknown`, the fence lift in Task 3 is incomplete; if a SAT/UNSAT is inverted, the concat order in Task 2 is wrong — fix there.)

- [ ] **Step 3: Repoint the stale crossing canary**

In `to_fp_bv_crossing_and_symbolic_real_are_unknown` (fp_e2e.rs ~621), **remove** the now-solvable 1-arg-bitcast entry:

```rust
        // bitcast from BV (1-arg to_fp)
        "(declare-fun b () (_ BitVec 32)) (declare-fun z () Float32) \
         (assert (fp.eq z ((_ to_fp 8 24) b))) (check-sat)",
```

Leave the other four entries (symbolic-Real `to_fp`, signed-int 2-arg BV→FP, `fp.to_sbv`, `fp.to_real`). Update the test's doc comment to note the bitcast is admitted as of slice 4c.

- [ ] **Step 4: Run the WHOLE fp_e2e suite + grep-audit** *(cross-slice lesson — no partial run)*

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS — every test, including all remaining crossing canaries still `Unknown`.

Run: `rg -n 'SolveOutcome::Unknown' crates/shinri-solver/tests/fp_e2e.rs`
Expected: the four remaining crossing entries plus any other legitimately-`Unknown` canaries; confirm none is a bitcast form.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): e2e BV→FP bitcast SAT/UNSAT + get-model; repoint the 1-arg-bitcast crossing canary (slice 4c)"
```

---

### Task 5: Differential z3 oracle for BV→FP bitcast

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` — add `gen_bitcast_script` and a `differential_qf_bvfp_bitcast` test, mirroring `gen_mixed_script` / `differential_qf_bvfp_mixed` (fp_oracle.rs:927-1019).

**Interfaces:**
- Consumes: `Lcg`, `FP32_SPECIALS`, `shinri_outcome`, `z3_outcome_mixed` (uses `QF_BVFP` logic), `N_ITERS` — all already in the file.

- [ ] **Step 1: Write the generator + differential test**

Add to `crates/shinri-solver/tests/fp_oracle.rs`:

```rust
/// One BV→FP bitcast script: constrain a 32-bit BV var to a value, bitcast it to
/// Float32 two ways — `(fp sign exp sig)` slicing the BV, and 1-arg `to_fp` of
/// the whole BV — and relate the results with a random FP relation. Exercises
/// both bitcast faces against z3 under QF_BVFP.
fn gen_bitcast_script(rng: &mut Lcg) -> String {
    // A concrete 32-bit pattern (favor special-adjacent values for coverage).
    let hi = (rng.next() & 0xffff) as u32;
    let lo = (rng.next() & 0xffff) as u32;
    let word = (hi << 16) | lo;
    const FP_RELS: &[&str] = &["fp.lt", "fp.leq", "fp.gt", "fp.geq", "fp.eq"];
    let fp_rel = FP_RELS[rng.below(FP_RELS.len() as u64) as usize];
    // Slice the 32-bit constant into sign(1) / exp(8) / sig(23) literal fields
    // so the (fp …) form and the 1-arg to_fp form describe the SAME value.
    let sign = (word >> 31) & 0x1;
    let exp = (word >> 23) & 0xff;
    let sig = word & 0x7f_ffff;
    format!(
        "(declare-fun b () (_ BitVec 32))\n\
         (declare-fun p () (_ FloatingPoint 8 24))\n\
         (declare-fun q () (_ FloatingPoint 8 24))\n\
         (assert (= b (_ bv{word} 32)))\n\
         (assert (= p (fp (_ bv{sign} 1) (_ bv{exp} 8) (_ bv{sig} 23))))\n\
         (assert (= q ((_ to_fp 8 24) b)))\n\
         (assert ({fp_rel} p q))\n\
         (check-sat)\n"
    )
}

#[test]
fn differential_qf_bvfp_bitcast() {
    let mut rng = Lcg(0x4C_B17_CA5);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_bitcast_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_mixed(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_BVFP BITCAST SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_bvfp_bitcast: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(n_z3_checked > 0, "z3 never returned a concrete verdict — check the logic/harness");
}
```

Note: the `(fp (_ bvN 1) …)` form uses `(_ bvN w)` decimal BV literals so both faces reference the identical 32-bit value; shinri parses `(fp …)` as `FpFromBits`, and `z3_outcome_mixed` forwards the lines verbatim under `QF_BVFP`.

- [ ] **Step 2: Run the oracle in the background** *(long-running — shells out to z3 per iteration)*

Run (background): `cargo test -p shinri-solver --test fp_oracle differential_qf_bvfp_bitcast -- --nocapture`
Expected: PASS with `sat>0 unsat>0 z3_checked>0` printed and no SOUNDNESS DISAGREEMENT panic. Poll for completion; do not block the session.

If z3 disagrees on a SAT/UNSAT: the concat order in Task 2 or the field slicing in `gen_bitcast_script` is off — the printed script isolates it. A field-order flip surfaces here first.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential z3 oracle for BV→FP bitcast (slice 4c)"
```

---

### Task 6: Full workspace green + doc landing note

**Files:**
- Modify: `docs/superpowers/specs/2026-07-01-shinri-qffp-slice4c-bitcast-design.md` (status → landed).

- [ ] **Step 1: Full workspace test**

Run: `cargo test --workspace`
Expected: PASS — no regressions in pure-BV, pure-FP, or mixed paths.

- [ ] **Step 2: Clippy**

Run: `cargo clippy --workspace --all-targets -- -D warnings`
Expected: no new warnings.

- [ ] **Step 3: Mark the design landed**

Change the design doc's `**Status:**` line to `Landed` and add a one-line note that both bitcast faces (`FpFromBits` + 1-arg `to_fp`) are admitted, with the crossing canary repointed.

- [ ] **Step 4: Commit**

```bash
git add docs/superpowers/specs/2026-07-01-shinri-qffp-slice4c-bitcast-design.md
git commit -m "docs(qffp): mark slice-4c landed — BV→FP bitcast admitted"
```

---

## Self-Review

**Spec coverage:**
- §3 gadget (FpFromBits concat + 1-arg to_fp passthrough) → Task 2. ✓
- §4 fence lift (`uses_crossing_conversion` drop + `is_supported_fp_word` arms) → Task 3. ✓
- §4 literal-args-not-special (const BV children blast to constant bit-lits) → Task 4's `fp_from_bits_known_value_sat` (all-literal `(fp …)`). ✓
- §5 reference model + golden → Task 1. ✓
- §5 differential z3 oracle → Task 5. ✓
- §5 canary repoint + whole-suite run → Task 4 Steps 3-4. ✓
- §5 get-model read-back on BV + FP var → Task 4 `fp_from_bits_symbolic_child_sat_with_model`. ✓
- §6 bit-order risk → pinned by Task 4 known-value tests + Task 5 oracle. ✓

**Placeholder scan:** no TBD/TODO; every code step shows complete code. The one conditional (`ctx.rounding_mode_sort()` accessor name in Task 3 Step 1) has an explicit fallback instruction.

**Type consistency:** `ref_fp_from_bits(eb, sb, sign: u64, exp: &Integer, sig: &Integer) -> Integer` defined in Task 1, used consistently. `blast_fp_word` arms return `Vec<BitLit>` matching the function signature. `gen_bitcast_script` / `z3_outcome_mixed` signatures match the existing `gen_mixed_script` pattern. Concat order `sig ++ exp ++ sign` is stated identically in Task 2's gadget and its test.
