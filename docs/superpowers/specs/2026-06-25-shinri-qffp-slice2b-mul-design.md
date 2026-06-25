# shinri QF_FP — Slice 2b: `fp.mul` Design

**Date:** 2026-06-25
**Status:** Approved design, pre-implementation
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (architecture, approved)
**Roadmap:** `docs/superpowers/specs/2026-06-25-shinri-qffp-slice2a-add-design.md` §1 (Plan 2 sub-slice table, row **2b**)
**Builds on:** Slice 2a (landed 2026-06-25 — the shared 5-mode rounder `round.rs` with the `ExtFp` contract, `lzc.rs`, `rm.rs`, and the `fp.add`/`fp.sub` datapath, all bit-identical to `reference.rs`)

This document specifies Plan 2's **second sub-slice (2b)**: the `fp.mul` datapath. It does **not**
revise the parent architecture — the engine model (eager bit-blast to the shared `Blaster`), the
`unpack → datapath → round → special-case → pack` pipeline, the `ExtFp` → `round()` contract, and
the soundness fence are all unchanged. Plan 2's remaining datapaths (`div`, `sqrt`, `fma`, `rem`,
`roundToIntegral`, `min`/`max`) stay fenced to `Unknown` and are deferred to sub-slices 2c–2e.

## 1. Why this slice

`fp.mul` is the smallest next step after 2a: it reuses the `shinri-bv` multiplier (`bvmul`) plus
the op-agnostic rounder built in 2a, and it is the **second exerciser of the `ExtFp` → `round()`
contract** — proving the rounder is genuinely op-agnostic and not accidentally `fp.add`-shaped.
Structurally `fp.mul` is *simpler* than `fp.add` in its datapath body (no operand ordering, no
alignment shift, no effective-add-vs-subtract split, no mode-dependent zero-sign rule), with the
new work concentrated in the full-width significand multiply and the renormalization of its product.

**Plan 2 sub-slice roadmap (from the 2a spec):**

| # | Sub-slice | Delivers |
|---|---|---|
| ~~2a~~ ✅ | `lzc.rs`, `round.rs` (5-mode), `blast/add.rs`, `rm.rs`; `fp.add`/`fp.sub` | landed |
| **2b** (this spec) | `blast/mul.rs`, `ref_mul`; `fp.mul` end-to-end |
| 2c | `fp.div`, `fp.sqrt` |
| 2d | `fp.fma` |
| 2e | `fp.rem`, `fp.roundToIntegral`, `fp.min`/`fp.max` |

Until each lands, the corresponding op stays fenced to `Unknown` (parent soundness contract).

## 2. Scope & what changes

One new datapath, one reference function, two one-line fence extensions. No architecture revision.

| File | Change |
|---|---|
| `crates/shinri-fp/src/blast/mul.rs` | **new** — the `fp.mul` datapath (§4) |
| `crates/shinri-fp/src/blast/mod.rs` | register the `mul` module; host the shared `Operand`/`to_operand` (§4) |
| `crates/shinri-fp/src/reference.rs` | **new** `ref_mul` — exact-rational product + IEEE special tables (§5) |
| `crates/shinri-fp/src/lib.rs` | `blast_word` gains an `FpMul` arm (§6) |
| `crates/shinri-solver/src/fp_stage.rs` | add `FpMul` to `is_supported_fp_word` + `fp_atom_is_supported` (§6) |

**Still fenced to `Unknown`** (soundness contract unchanged): `div`/`sqrt`/`fma`/`rem`/
`roundToIntegral`/`min`/`max`, all conversions, FP+BV mixing (Plan 4), FP+EUF/Arith/Arrays, and the
Real bridge. Slice 2b only **removes** `fp.mul` from the fenced set.

## 3. Shared operand helper

`blast/add.rs` already contains an `Operand` struct (signed unbiased exponent in `exp_w` bits, an
explicit `sb`-bit significand with the hidden bit materialized, and `is_nan`/`is_inf`/`is_zero`
flags) and a `to_operand` constructor that builds it from packed bits via the slice-1 `unpack`.
`fp.mul` needs exactly the same unpacked form. To avoid a duplicated copy, **lift `Operand` and
`to_operand` into a shared location** (`blast/mod.rs`, or a small `blast/operand.rs`) and have both
`add.rs` and `mul.rs` consume it. This is a targeted refactor of code 2b is already touching, not a
speculative one — it keeps the single source of truth for the unpacked operand contract.

## 4. The `fp.mul` datapath (`blast/mul.rs`)

```
fp_mul(b, x, y, rm, eb, sb):
  ox, oy = to_operand(x), to_operand(y)        // shared helper (§3)

  1. Sign:  res_sign = ox.sign XOR oy.sign      // always, including specials (IEEE)
  2. Exp:   prod_exp = ox.exp + oy.exp          // signed add in exp_w bits
  3. Sig:   zero-extend ox.sig, oy.sig to 2*sb bits;
            prod = bvmul(ext_x, ext_y)          // bvmul truncates to its input width,
                                                // so 2*sb-wide inputs yield the full
                                                // 2*sb-bit product in the low bits
  4. Normalize (uniform LZC):
            lz     = lzc(prod) over 2*sb width
            prod_n = prod << lz                 // leading 1 lands at the MSB
            norm_exp = prod_exp - lz + CORRECTION
            // CORRECTION is the fixed constant mapping an MSB-aligned 2*sb product
            // to the ExtFp [hidden|frac] weighting; folded at blast time.
  5. Build ExtFp:
            sig = top sb bits of prod_n
            G   = next bit below sig
            R   = next bit below G
            S   = OR of all remaining low bits of prod_n
            ext = ExtFp{ sign: res_sign, exp: norm_exp, sig, grs: (G, R, S) }
            rounded = round(b, ext, eb, sb, rm)  // 2a rounder, unchanged

  6. Special-case mux (overrides rounded), priority NaN > Inf > Zero > normal:
            want_nan = ox.is_nan OR oy.is_nan
                       OR (ox.is_zero AND oy.is_inf)
                       OR (ox.is_inf AND oy.is_zero)        // 0 * inf = NaN
            any_inf  = ox.is_inf OR oy.is_inf               // (and not want_nan)
            any_zero = ox.is_zero OR oy.is_zero             // finite * 0 = +/-0
            // inf and zero result patterns both carry res_sign (the XOR sign is
            // correct for both); NaN is the canonical pattern.
```

**Reuse vs. new.** Reused: `to_operand`/`unpack` (slice 1 + §3), `bvmul` (`shinri-bv`), `lzc`
(slice 2a), `round` (slice 2a, unchanged), the canonical-NaN / inf / signed-zero pattern builders
(present in `add.rs`, shareable). New: only the multiply-and-normalize body and the mul
special-case table.

**Three things to get right:**

- **No operand ordering, alignment, or add/sub split.** The datapath body is shorter than
  `fp.add`'s; the substance is the full-width multiply plus the uniform LZC renormalize.
- **Exponent headroom — explicit checkpoint, not an assumption.** `fp.add` keeps operands close;
  `fp.mul` *sums* exponents, so the intermediate range is larger (two subnormals:
  `exp ≈ 2·emin − lz`). The current `exp_w(eb) = eb + 6` must be re-validated for products. The
  exhaustive `(3,5)` gadget test (§7) is the gate: if any case mismatches, widen `exp_w` and
  document. Do **not** assume `eb + 6` suffices for mul without that test passing.
- **Zero sign is pure XOR.** `±0 · finite` and `±0 · ±0` yield a zero whose sign is exactly
  `res_sign = sign_x XOR sign_y`. Unlike `fp.add`, there is **no** mode-dependent (`RTN`)
  zero-sign rule — IEEE multiplication zero sign is pure XOR. This is strictly simpler than add.

## 5. Reference oracle (`ref_mul`)

Mirrors `ref_add` in `reference.rs`, with simpler special tables:

```
ref_mul(eb, sb, a, b, mode):
  ca, cb = decode(a), decode(b)
  1. NaN:  either NaN -> canonical_nan(eb, sb)
  2. 0*inf: (zero and inf) in either order -> canonical_nan          // BEFORE the inf arm
  3. Inf:  either inf (other finite-nonzero) -> inf_pattern(sign = sign_a XOR sign_b)
  4. Zero: either zero (other finite)        -> zero_pattern(sign = sign_a XOR sign_b)
  5. Finite*finite: ra * rb (exact Rational) -> round_rational(product, mode)
```

The exact-rational product is `0` only when an operand is `0` (handled in arm 4), so there is **no**
`sum == 0` cancellation arm of the kind `ref_add` carries — another way `mul` is cleaner than
`add`. `ref_mul` is the trusted golden semantics the datapath is asserted bit-identical against, and
is also available to a future `rewrite` constant-folding pass (not built in 2b).

## 6. Wiring & fence

- **`lib.rs::blast_word`** — new `FpMul` arm alongside `FpAdd`/`FpSub`: consume the RM operand via
  `rm.rs`, blast the two FP operand words, call `fp_mul(...)`. The existing `unreachable!`/`Unknown`
  backstop for still-out-of-scope ops stays as the fence.
- **`fp_stage.rs`** — add `BuiltinOp::FpMul` to the two recognizer arms (`is_supported_fp_word` and
  `fp_atom_is_supported`), reusing the same `(RM, F, F)` shape check applied to `FpAdd`/`FpSub`: the
  RM operand must be a `RoundingMode` term (literal const or nullary RM variable) and both FP
  operands must be recursively supported. `recognized_fp_op` already lists `FpMul`, so it needs no
  change.
- **Soundness unchanged.** Any not-yet-built op still defaults to unsupported → `Unknown`. The
  "a new FP op defaults to fenced" discipline is preserved; 2b flips exactly one op into scope.

## 7. Model path — unchanged

`fp.mul` introduces no new *variables*, so model extraction is untouched: it reads declared FP
variable bit-vars and renders via the slice-1 printer. A `get-value` on an `fp.mul` *term* reads
that term's cached output word — the existing read-back already handles any cached word. A witness
test confirms this end-to-end.

## 8. Test plan

Extends the established slice-2a layers; the oracle is `ref_mul` (decode → `class_to_rational` →
exact `Rational` product → `round_rational`, with the special tables).

- **`fp.mul` gadget tests — the anchor.** Blast the datapath; fix concrete `(x, y, RM)`; assert the
  output bits equal `ref_mul`. **Exhaustive on `(3,5)` over all operand/mode combinations**
  (`256² × 5`, the same budget `fp.add` already runs); randomized on Float16/Float32. Explicitly
  seed: `NaN · x`, `0 · ∞` (both orders → canonical NaN), `∞ · finite`, `±0 · ±finite` and
  `±0 · ±0` (verify the **XOR zero-sign**), subnormal × subnormal (deep underflow → flush; exercises
  the uniform LZC plus the rounder's subnormal denormalize), subnormal × normal, the
  round-up-carries-into-the-exponent case, and the overflow-to-∞ boundary.
- **Exponent-width gate.** The exhaustive `(3,5)` sweep is the explicit check that
  `exp_w(eb) = eb + 6` survives summed exponents. If any case mismatches, widen `exp_w` and document
  the new bound. (Checkpoint, not an assumption — see §4.)
- **Symbolic-RM test.** A query with a `RoundingMode` *variable* and an asserted `fp.mul` result —
  confirms the 5-mode mux is wired through `fp.mul`, not folded away.
- **Differential vs z3.** Extend `fp_oracle.rs` (feature-gated, mirrors `qfbv_oracle.rs`) to emit
  random `fp.mul` over all five modes; agree on SAT/UNSAT.
- **End-to-end witness + non-regression.** A known SAT script (e.g.
  `(assert (fp.eq (fp.mul RNE two two) four))`) with a `get-model` round-trip; the full `cargo test`
  workspace sweep stays green; the QF_BV path is untouched (FP keeps its own stage and `Blaster`).

## 9. Decisions locked for slice 2b

| Decision | Choice |
|---|---|
| Scope | `fp.mul` only; `div`/`sqrt`/`fma`/`rem`/`roundToIntegral`/`min`/`max` stay fenced (2c–2e) |
| Significand multiply | Zero-extend `sb` → `2·sb`, reuse `bvmul` (truncating), take the full low `2·sb` product |
| Normalize | **Uniform LZC** over the full `2·sb` product → canonical [1,2); no normal/subnormal fast-path split |
| `Operand`/`to_operand` | Lifted to a shared module so `add` and `mul` share one copy |
| Sign | `sign_x XOR sign_y` always (including specials); no mode-dependent zero-sign rule |
| Rounder | Reused unchanged — proves `round()` is op-agnostic (2b's secondary goal) |
| Exp width | `exp_w(eb) = eb + 6` provisional; the exhaustive `(3,5)` test is the gate, widen if it fails |
| Validation anchor | datapath bit-identical to `ref_mul`; `ref_mul` is the exact-rational golden oracle |
| Soundness | Everything outside scope returns `Unknown`, never a wrong verdict — unchanged from parent |
