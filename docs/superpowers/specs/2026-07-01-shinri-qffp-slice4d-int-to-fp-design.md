# shinri QF_FP — Slice 4d: int→FP (`to_fp` signed-BV + `to_fp_unsigned`)

**Date:** 2026-07-01
**Status:** Landed — both int→FP faces (`to_fp` 2-arg signed-BV + `to_fp_unsigned`) admitted
through the `to_fp_int` gadget (sign+magnitude → prenormalize → clamp → static split → shared
rounder → zero mux). MID-SLICE DISCOVERY: §2's "rounder's existing overflow→±∞/max-finite-by-mode
path" did not exist — `round()`/`round_rational` overflowed to ±∞ under EVERY mode (latent IEEE-754
deviation in all prior rounding ops); fixed centrally in both (RNE/RNA→±∞, RTZ→±max_finite,
RTP→+∞/−max_finite, RTN→+max_finite/−∞), all 10 sign×mode combos hard-pinned on golden and circuit.
Verification: workspace EXIT=0 (shinri-fp exhaustive 77/0 @2337s, solver lib 81/0, fp_e2e 57/0 incl
5 new int→FP e2e, shinri-bv 98/0, qfbv 26/0); full z3 oracle 13/13 ZERO disagreements (new
differential_qf_bvfp_int_to_fp sat=112 unsat=88 z3_checked=200/200; all pre-existing counts
byte-identical to the 4c baseline); 4 canaries repointed (fp_stage.rs ×3 incl. one the plan missed,
fp_e2e.rs ×1); remaining fence = fp.to_ubv / fp.to_sbv / fp.to_real / symbolic-Real to_fp.
**Plan:** 4 (BV↔FP crossing conversions), second admitted conversion
**Predecessors:** slice 4a (unified `Lowerer`/`WordSink`), slice 4b (mixed
pure-BV+pure-FP fence-lift), slice 4c (BV→FP bitcast)
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (§5 conversions)

## 1. Goal & Scope

Admit the two **integer→FP** faces of the conversion suite: the value (not bit)
reinterpretation of a BitVec as a signed or unsigned integer, rounded into the
target format. Unlike 4c's bitcast this is a real datapath — normalize + round —
but it reuses the shared rounder end to end.

**In scope (both faces, one slice):**
- `((_ to_fp eb sb) RM x)` with `x : (_ BitVec m)` — `ToFp{eb,sb}` 2-arg,
  BV-sorted second operand: round the **two's-complement signed** integer value
  of `x` into `(eb, sb)` under `RM`.
- `((_ to_fp_unsigned eb sb) RM x)` — `ToFpUnsigned{eb,sb}`: same, reading `x`
  **unsigned**.

**Explicitly NOT in scope (stay fenced to `Unknown`):**
- `fp.to_ubv` / `fp.to_sbv` (FP→BV value conversions) — the next slice, and
  after it Plan 4 is complete.
- `fp.to_real` (permanent v1 non-goal — the Real bridge).
- `to_fp` from a symbolic Real (later Real combination).

**Soundness contract (unchanged):** anything out of scope returns `unknown`,
never a wrong SAT/UNSAT verdict.

## 2. Semantics (the spec we encode)

SMT-LIB defines both ops via the real value of the source integer: form the
exact integer (signed or unsigned read of the BV) and round it into `(eb, sb)`
under `RM`. The golden anchor is the existing exact-rational rounder
`round_rational` (`crates/shinri-fp/src/reference.rs:253`) — every integer is
an exact `Rational`, so the reference needs **no new rounding machinery**:

- `ref_to_fp_sbv(eb, sb, m, x, mode)` / `ref_to_fp_ubv(eb, sb, m, x, mode)` are
  thin wrappers: read the `m`-bit pattern as a signed / unsigned `Integer`,
  lift to `Rational`, call `round_rational`.

Consequences of "input is a BV integer" (vs. FP→FP's operand flags):
- **No NaN/∞ input cases.** The special-case mux of `to_fp_fp` collapses to a
  single zero mux.
- **`x = 0` → `+0`** under every mode, matching `round_rational` on exact zero
  (already pinned by the 3a const-Real face). A negative integer is never zero,
  so the unsigned/signed faces agree here.
- **Overflow is real:** a wide integer into a small format (e.g. 8-bit values
  into `(3,5)`, max finite 15.5) must hit the rounder's existing
  overflow→±∞/max-finite-by-mode path.
- **Rounding is real:** any integer with more than `sb` significant bits rounds
  (guard/round/sticky), e.g. 64-bit ints into Float32.

## 3. The gadget (`crates/shinri-fp/src/convert.rs`)

One new function, `to_fp_int(b, x, m, signed, eb_t, sb_t, rm) -> Vec<BitLit>`,
mirroring the shape of `to_fp_fp` (convert.rs:26). `ToFp`-2-arg-BV calls it
with `signed = true`, `ToFpUnsigned` with `signed = false` — `signed` is a
blast-time constant, so the unsigned face pays nothing for the sign logic.

1. **Sign + magnitude.** `sign = x[m-1]` (signed) or `b.zero()` (unsigned);
   `mag = mux(sign, bvneg(x), x)`. The `m`-bit negate is safe: the only value
   whose negation doesn't fit signed is INT_MIN, and `|INT_MIN| = 2^(m-1)`
   fits **unsigned** in `m` bits — `mag` is read unsigned from here on.
2. **Prenormalize.** Treat `mag` as a significand with hidden bit at index
   `m-1` and constant exponent `m-1` (value = `mag/2^(m-1) · 2^(m-1)`). Feed it
   through the shared `prenormalize` (`crates/shinri-fp/src/blast/normalize.rs:23`
   — already width-generic: LZC + left shift, exponent decremented by the
   shift), exactly the call `to_fp_fp` makes at convert.rs:38. After it, the
   leading 1 sits at index `m-1` and the exponent is the true unbiased
   exponent of the value.
3. **Exponent width + clamp.** The working exponent must hold `[0, m-1]` before
   normalization and survive the target-range compares. Run it at
   `wc = max(exp_w(eb_t), bits_for(m)) + 1` (`bits_for(m)` = smallest width
   holding `m-1` as a signed value) and reuse the exact
   saturate-then-clamp block from `to_fp_fp` (convert.rs:42-66): `> emax_t + 1`
   saturates high (rounder → overflow), `< emin_t - (sb_t + 2)` saturates low
   (rounder → deep denormalize → zero; unreachable here since the source is an
   integer ≥ 1 at this point, but keeping the block identical costs nothing
   and keeps one shared shape). Low `exp_w(eb_t)` bits feed the rounder.
4. **Static significand split.** Identical widen/narrow split to
   `to_fp_fp` (convert.rs:69-84) with `m` in the role of `sb_s`: if
   `sb_t >= m` pad low zeros (exact, GRS = 0); else keep the top `sb_t` bits
   and fold the dropped low bits into guard/round/sticky.
5. **Round + zero mux.** `round(b, ExtFp{sign, exp, sig, grs}, eb_t, sb_t, rm)`
   (`crates/shinri-fp/src/round.rs:30`), then mux `is_zero = NOR(x)` to the
   `+0` pattern (`signed_zero_bits` with a constant positive sign).

**Dispatch** (`crates/shinri-fp/src/lib.rs`, `blast_fp_word`): extend the
2-arg `ToFp` arm — if the second child is BV-sorted, blast it via
`sink.word` (the sort-dispatched route through `blast_bv_word`, per 4c) and
call `to_fp_int(signed = true)`; the FP→FP and const-Real faces are untouched.
Add a new `ToFpUnsigned` arm calling `to_fp_int(signed = false)`.

**Constants are not special-cased** (4c decision carried forward): a literal BV
operand blasts to constant bit-lits and the circuit folds; no `rewrite` arm.

## 4. Fence lift (`crates/shinri-solver/src/fp_stage.rs`)

- **`uses_crossing_conversion`** (fp_stage.rs:65): remove `ToFpUnsigned` from
  the always-crossing set (line 76) and flip the `ToFp` 2-arg
  `SortNode::BitVec(_) => true` arm (line 81) to `false`. `FpToUbv` /
  `FpToSbv` / `FpToReal` and the symbolic-Real `ToFp` face stay crossing. The
  DAG-walk safety net still catches a still-crossing op nested inside the BV
  child (e.g. `(to_fp rm (fp.to_ubv …))`).
- **`is_supported_fp_word`** (fp_stage.rs:195): in the `ToFp` 2-arg arm
  (line 265), accept a BV-sorted second operand alongside the existing
  FP-word / const-Real cases; add a `ToFpUnsigned` arm (exactly 2 kids: a
  RoundingMode term + a BV-sorted operand). **No recursive support check on
  the BV child** — the BV blaster is total and nested crossings are fenced
  upstream, the same argument locked in 4c (fp_stage.rs:270-273).
- **`is_fp_op`** already lists `ToFp` and `ToFpUnsigned` (fp_stage.rs:19), so
  `solver_uses_fp` fires unchanged.

After this slice the only remaining crossing faces are `fp.to_ubv`/`fp.to_sbv`
and the permanent Real bridge.

## 5. Testing (the established slice pattern)

- **Per-gadget bit-identical gate** (in `convert.rs` tests): exhaustive — all
  2^8 8-bit patterns, **both** signed and unsigned reads, into `(3,5)` and
  `(5,11)`, all five modes, vs `ref_to_fp_sbv`/`ref_to_fp_ubv`. This covers
  overflow (255 ≫ 15.5), ties, INT_MIN negation, zero, and the widen branch
  (8-bit into `sb_t = 11`). Randomized: 32/64-bit ints into Float32 (deep
  sticky collapse, `m > sb_t` narrowing), seeded with `0`, `±1`, `INT_MIN`,
  `INT_MAX`, `u64::MAX`, and powers of two ± 1.
- **e2e (`fp_e2e.rs`)**: symbolic int→FP scripts flipping `Unknown → Sat` and
  `→ Unsat`, `get-model` read-back on both the BV source var and the FP result
  var in the same model; both faces exercised.
- **Differential z3 oracle**: random QF_BVFP formulas over `to_fp` and
  `to_fp_unsigned` from symbolic BVs, SAT/UNSAT agreement, zero disagreements.
- **Canary repoint** *(standing cross-slice lesson)*: pre-flight hunt BEFORE
  the fence edit — grep `fp_e2e` and the `fp_stage` unit tests for canaries
  pinned on the int→FP faces. Known flips: fp_stage.rs:593 (`to_fp from BV is
  crossing`) and fp_stage.rs:599 (`to_fp_unsigned is crossing`) assert the old
  verdict and must be repointed at `fp.to_ubv`/`fp.to_sbv`; audit the e2e
  crossing-canary array the same way. Then run the **whole** suites.
- **Regression is an oracle**: full `cargo test --workspace` green; pure-BV and
  prior-FP verdicts byte-identical. The multi-minute FP/SAT gates run in
  background in-session (not via subagents).

## 6. Risks

- **Exponent-width wrap on extreme narrowing.** The source exponent ranges over
  `[0, m-1]`; `exp_w(eb_t) = eb_t + 6` is comfortable for real formats but the
  design still pins the widened-compare-then-clamp (`wc = max(...) + 1`) so no
  compare can wrap regardless of `m`/`eb_t`. Mitigation: the exhaustive tiny
  gate plus a wide-int-into-`(3,5)` case.
- **INT_MIN negation.** `-INT_MIN` wraps in signed arithmetic; reading `mag`
  unsigned makes it correct by construction. Mitigation: INT_MIN is a seeded
  test vector in every per-gadget sweep.
- **Cross-slice canary breakage.** Admitting these faces flips prior
  `Unknown`-canaries (unit AND e2e). Mitigation: the front-loaded canary hunt
  and full-workspace net, per the standing lesson.
- **Circuit depth.** Shallow — LZC + one barrel shift + the shared rounder,
  comparable to `fp.add`; none of the `fp.div` recursion-depth risk.

## 7. Decisions locked for slice 4d

| Decision | Choice |
|---|---|
| Faces admitted | Both — `ToFp` 2-arg BV (signed) and `ToFpUnsigned` (unsigned), one slice |
| Gadget | One `to_fp_int` with blast-time `signed` flag; sign+magnitude → `prenormalize` → shared `round()` |
| Reference | `ref_to_fp_sbv`/`ref_to_fp_ubv` = thin wrappers over `round_rational` |
| Zero | Explicit `is_zero` mux to `+0` (matches `round_rational`, all modes) |
| INT_MIN | `mag` read unsigned after the m-bit negate — exact by construction |
| Exponent width | `wc = max(exp_w(eb_t), bits_for(m)) + 1`, reusing the `to_fp_fp` clamp |
| Constant folding | None — literal BV operands fold through constant bit-lits (4c decision) |
| BV-child support | Sort check only; no recursive FP-support call (4c argument) |
| Fence edit | Un-cross `ToFpUnsigned` + `ToFp`-2-arg-BV; extend the two `is_supported_fp_word` arms |
| Success criterion | Byte-identical existing verdicts + remaining crossing canaries still `Unknown` + both faces solve & agree with z3 |
| Next slice | FP→BV (`fp.to_ubv`/`fp.to_sbv`) — closes Plan 4 |
