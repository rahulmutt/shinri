# shinri QF_FP — Slice 2a: Rounder + `fp.add`/`fp.sub` Design

**Date:** 2026-06-25
**Status:** Approved design, pre-implementation
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (architecture, approved)
**Roadmap:** `docs/superpowers/specs/2026-06-25-shinri-qffp-vertical-slice-design.md` §3 (Plan 2 = "Rounder + arithmetic")
**Builds on:** Slice 1 (landed 2026-06-25 — rounding-free QF_FP end-to-end: `unpack`/`pack`/`classify`/`compare`/`structural`, `reference.rs` with a full round core, `fp_stage.rs`, model + printer)

This document decomposes the roadmap's **Plan 2** ("Rounder + arithmetic") and specifies its
**first sub-slice (2a)**: the shared rounder, the leading-zero counter, and the `fp.add`/`fp.sub`
datapath. It does **not** revise the parent architecture — the engine model (eager bit-blast to
the shared `Blaster`), the `unpack → align → operate → normalize → round → special-case → pack`
pipeline (parent §4), and the soundness contract are all unchanged. Plan 2's remaining datapaths
(`mul`, `div`, `sqrt`, `fma`, `rem`, `roundToIntegral`, `min`/`max`) are deferred to later
sub-slices that reuse the rounder built here.

## 1. Why slice it

Plan 2 as written bundles the rounder plus **nine** arithmetic datapaths into one line. That is
far more than one implementation plan should carry, and it cuts against the slice-1 discipline
(thin vertical slice, prove the seam, then expand). Slice 2a builds the **shared rounding
pipeline** and exercises it end-to-end through the single canonical arithmetic op — `fp.add`
(and `fp.sub`, which is a thin wrapper) — so every later datapath inherits a trusted,
op-agnostic rounder.

**Plan 2 sub-slice roadmap:**

| # | Sub-slice | Delivers |
|---|---|---|
| **2a** (this spec) | `lzc.rs`, `round.rs` (5-mode), `blast/add.rs`, `rm.rs`; `fp.add`/`fp.sub` end-to-end |
| 2b | `fp.mul` (reuses `bvmul` + rounder) |
| 2c | `fp.div`, `fp.sqrt` (restoring/Newton datapaths + rounder) |
| 2d | `fp.fma` (full-width multiply, single rounding) |
| 2e | `fp.rem` (exact, no rounding), `fp.roundToIntegral`, `fp.min`/`fp.max` |

Until each lands, the corresponding op stays fenced to `Unknown` (parent soundness contract).

## 2. The canonical intermediate form

A new `ExtFp` struct is the single currency between every arithmetic datapath and the rounder.
Every op's contract: produce a **normalized** `ExtFp` (leading significand bit at the fixed MSB
position) with correct guard/round/sticky, then call `round()`. The rounder never needs to know
which op produced the value.

```rust
struct ExtFp {
    sign: BitLit,                  // result sign
    exp:  Vec<BitLit>,             // signed, widened exponent: eb+2 bits
                                   //   (room for ±1 renormalize and over/underflow detection)
    sig:  Vec<BitLit>,            // sb significand bits, MSB = hidden/leading: [hidden | trailing(sb-1)]
    grs:  (BitLit, BitLit, BitLit) // Guard, Round, Sticky, just below sig's LSB
}
```

## 3. Module decomposition (new in `shinri-fp`)

| Module | Slice-2a responsibility |
|---|---|
| `lzc.rs` | Leading-zero counter over a significand → shift amount. Pure combinational, width-parameterized, reused by the normalize path. |
| `round.rs` | The shared rounder: `round(b, ext, eb, sb, rm_sel) -> Vec<BitLit>` (a packed W-bit word). Subnormal pre-shift, 5-mode increment mux, carry-renormalize, overflow→∞, underflow→subnormal/zero, then `pack` (NaN canonicalization inherited from slice 1). |
| `blast/add.rs` | The `fp.add` datapath (§5). Produces a normalized `ExtFp`, calls `round()`, then applies the IEEE special-case mux. |
| `rm.rs` | Blast a `RoundingMode` operand to a 3-bit selector word: literal → constant bits; symbolic variable → 3 fresh bits. Feeds `round()`. |

Files **still deferred** (NOT in 2a): `rewrite.rs`, `convert.rs`, and `blast/{mul,div,sqrt,fma,rem,roundint,minmax}.rs`.

`fp.sub` adds **no** datapath: `lib.rs` rewrites `fp.sub RM x y` → `fp.add RM x (fp.neg y)` at
blast time (`fp.neg` is the slice-1 `blast/structural.rs` gadget). This identity is exact in
IEEE 754, including the sign of a zero result.

## 4. The rounder (`round.rs`)

`round(b, ext, eb, sb, rm_sel)`:

1. **Subnormal pre-shift.** If `ext.exp < emin`, right-shift `sig` by `(emin − exp)` (barrel
   shift via `shinri-bv::bvlshr`), OR-ing every dropped bit into sticky; clamp `exp` to `emin`.
   After this the rounding position is **fixed**, so the rest of the rounder is position-static.
2. **Increment decision** = a mux over `rm_sel` of the five mode predicates, computed from
   `(lsb, G, R, S, sign)` exactly as the reference (`reference.rs:245-257`):
   - `RTZ` → `0`
   - `RTP` → `¬sign ∧ (G ∨ R ∨ S)`
   - `RTN` → `sign ∧ (G ∨ R ∨ S)`
   - `RNE` → `G ∧ (R ∨ S ∨ lsb)`
   - `RNA` → `G`
3. **Apply increment** to the significand; detect a significand carry (`1.11… → 10.0…`) →
   right-shift by 1, `exp += 1`.
4. **Overflow:** `exp > emax` → the ∞ bit pattern (sign preserved). **Underflow** needs no
   separate arm — a subnormal significand that rounds up into the hidden-bit position promotes
   to the smallest normal naturally (matches `round_rational`).
5. **Pack** `sign | biased_exp | trailing` via the slice-1 `pack.rs` (NaN canonicalization
   unchanged; no arithmetic path emits a non-canonical NaN).

**Validation anchor:** `round()` is asserted **bit-identical to `reference.rs::round_rational`**
across the full test matrix (§8). This is the single most important correctness gate in the slice.

## 5. The `fp.add` datapath (`blast/add.rs`)

1. **Unpack** x, y via slice-1 `unpack.rs` (sign, exponent, explicit significand, `isNaN`,
   `isInf`, `isZero` flags).
2. **Order operands** so `|x| ≥ |y|` by exponent (with significand tiebreak): a mux on the
   unpacked operands, so the alignment right-shift is always applied to the smaller operand.
3. **Align:** right-shift the smaller significand by `exp_x − exp_y` (capped at the datapath
   width) using `shinri-bv::bvlshr`; **sticky** = OR of all bits shifted out.
4. **Operate:** signs equal → effective add (`shinri-bv::adder`); signs differ → effective
   subtract (`shinri-bv::bvsub`), on the significands extended with the G/R/S columns.
5. **Normalize:** add path → at most a 1-bit right renormalize on carry-out; subtract path →
   `lzc.rs` + left-shift to reclaim leading zeros from cancellation, adjusting `exp`.
6. **Build `ExtFp`** and call `round()`.
7. **Special-case mux** (overrides the datapath result), a final mux tower keyed on the input
   flags, per the IEEE `fp.add` table:
   - either input `NaN`, or `(+∞) + (−∞)` → canonical `NaN`
   - either input `∞` (and not the NaN case) → `∞` with the surviving sign
   - exact-zero result sign rule: `x + (−x)` and `(±0) + (∓0)` → `+0` in every mode **except
     `RTN`, which yields `−0`**; `(+0)+(+0) → +0`, `(−0)+(−0) → −0`
   - `(±0) + y = y`, `x + (±0) = x` (identity, preserving the nonzero operand)

## 6. Solver wiring & boundaries (`fp_stage.rs`, `lib.rs`)

The slice-1 stage machinery carries over; slice 2a only changes *what is in scope*.

- **`collect_fp_atoms`** — unchanged in shape. `fp.add`/`fp.sub` are **word** ops, not atoms;
  they are reached transitively when an enclosing Bool-sorted atom is blasted (e.g.
  `(fp.eq (fp.add RM x y) z)` or `(= (fp.add …) c)`). No new atom kinds.
- **`solver_uses_fp`** — already fires on any FP builtin, `FpAdd`/`FpSub` included. No change.
- **`lib.rs::blast_word`** — gains two arms: `FpAdd` (the §5 datapath) and `FpSub`
  (rewrite-to-add). The existing `unreachable!`/`Unknown` backstop for out-of-scope ops stays
  as the fence.
- **RoundingMode operands** are never atoms and never surrogated; they are consumed inside the
  `FpAdd` arm via `rm.rs`. A standalone `RoundingMode`-typed value escaping into a non-FP
  context still trips `has_non_fp_theory_atom` → `Unknown` (the slice-1 safety net); in practice
  RM appears only as an op operand.
- **Still fenced to `Unknown`** (soundness contract unchanged): FP+BV mixing (Plan 4),
  FP+EUF/Arith/Arrays, every not-yet-built op (`mul`/`div`/`sqrt`/`fma`/`rem`/`roundToIntegral`/
  `min`/`max`), all conversions, and any Real bridge. Slice 2a only **removes** `fp.add`/`fp.sub`
  from the fenced set.

## 7. Model path — unchanged

`fp.add`/`fp.sub` introduce no new *variables*, so model extraction is untouched: it still reads
declared FP variable bit-vars (`exported_var_bits`) and renders via the slice-1 printer fix. A
`get-value` on an `fp.add` *term* reads that term's cached output word — the existing read-back
already handles any cached word. A witness test confirms this end-to-end.

## 8. Test plan

Extends the established slice-1 test layers; the reference oracle is `reference.rs` (decode →
`class_to_rational` → exact arithmetic → `round_rational`).

- **Rounder unit tests (`round.rs` vs `round_rational`) — the anchor.** Drive `round()` on
  concrete `(sign, exp, sig, GRS)` across **all five modes**; assert the packed word equals
  `round_rational` of the same exact value. **Exhaustive on `(3,5)`** (every value × every mode),
  randomized on Float16/Float32. Explicitly seed: exact values (no rounding), every tie
  (`G=1, R=0, S=0`), the overflow-to-∞ boundary, the subnormal pre-shift range, and the
  round-up-carries-into-the-exponent case.
- **`fp.add`/`fp.sub` gadget tests.** Blast the datapath; fix concrete `(x, y, RM)`; assert
  output bits equal `reference.rs`. Exhaustive on `(3,5)` over all mode/operand combinations
  (`256² × 5`, feasible); randomized on Float16/Float32. Seed every special pair: `∞ + (−∞)`,
  `∞ + finite`, `NaN + x`, `(±0) + (±0)` (verifying the **`RTN` → −0** sign rule), cancellation
  (`a + (−a)`), and massive-exponent-gap (sticky-only) cases.
- **Symbolic-RM test.** A query with a `RoundingMode` *variable* and an asserted `fp.add`
  result — confirm the solver finds a satisfying mode (proves the 5-mode mux is wired, not
  folded away).
- **Differential vs z3.** Extend `fp_oracle.rs` (feature-gated, mirrors `qfbv_oracle.rs`) to
  emit random `fp.add`/`fp.sub` over all five modes; agree on SAT/UNSAT.
- **End-to-end witness + non-regression.** A known SAT script (e.g.
  `(assert (fp.eq (fp.add RNE one one) two))`) with a `get-model` round-trip; the full
  `cargo test` workspace sweep stays green; the QF_BV path is untouched (FP keeps its own stage
  and `Blaster`).

## 9. Decisions locked for slice 2a

| Decision | Choice |
|---|---|
| Scope | Rounder + `lzc` + `fp.add`/`fp.sub` only; mul/div/sqrt/fma/rem/roundToIntegral/min/max deferred to 2b–2e |
| `fp.sub` | Rewrite to `fp.add RM x (fp.neg y)` — no second datapath (exact in IEEE incl. zero signs) |
| Rounder | Fixed-position guard/round/sticky (Approach A); shared and op-agnostic |
| Rounding modes | Full 5-mode mux from day one; literal modes fold via constant select bits |
| Intermediate form | `ExtFp { sign, exp, sig, grs }` — the contract every future datapath rounds through |
| `rewrite.rs` | Still deferred (constant-folding not required for correctness; the circuit computes constants) |
| Validation anchor | `round.rs` bit-identical to `round_rational`; the `fp.add` datapath bit-identical to `reference.rs` |
| Soundness | Everything outside scope returns `Unknown`, never a wrong verdict — unchanged from parent |
