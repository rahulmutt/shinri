# shinri QF_FP — Floating-Point Theory Design

**Date:** 2026-06-24
**Status:** Approved design, pre-implementation
**Scope:** Full QF_FP (SMT-LIB `FloatingPoint` theory), with full QF_BVFP
interop, via eager bit-blasting into the shared `shinri-bv` `Blaster`.

## 1. Goal & Scope

Add support for the SMT-LIB QF_FP logic to shinri: the `FloatingPoint` sort
family, `RoundingMode`, FP literals/constructors, the full operator set, the
conversion suite, and `(get-model)`/`(get-value)` over FP terms — with
floating-point and bit-vector terms freely mixed (QF_BVFP).

**In scope (v1):**
- **Sorts:** `(_ FloatingPoint eb sb)` and the aliases
  `Float16/32/64/128` = `(5,11)/(8,24)/(11,53)/(15,113)`; `RoundingMode`.
- **Literals/constructors:** `(fp s_sign s_exp s_sig)` (3 BV args of widths
  `1`, `eb`, `sb-1`); `(_ +oo eb sb)`, `(_ -oo eb sb)`, `(_ +zero eb sb)`,
  `(_ -zero eb sb)`, `(_ NaN eb sb)`; the five rounding-mode constants
  `RNE, RNA, RTP, RTN, RTZ`.
- **Arithmetic:** `fp.abs`, `fp.neg`, `fp.add`, `fp.sub`, `fp.mul`, `fp.div`,
  `fp.fma`, `fp.sqrt`, `fp.rem`, `fp.roundToIntegral`, `fp.min`, `fp.max`.
- **Comparisons:** `fp.leq`, `fp.lt`, `fp.geq`, `fp.gt`, `fp.eq`, and core `=`.
- **Classification:** `fp.isNormal`, `fp.isSubnormal`, `fp.isZero`,
  `fp.isInfinite`, `fp.isNaN`, `fp.isNegative`, `fp.isPositive`.
- **Conversions:** `to_fp` (BV bitcast / FP→FP / signed-int→FP),
  `to_fp_unsigned` (unsigned-int→FP), `fp.to_ubv`, `fp.to_sbv`, and `to_fp`
  from a **constant Real literal**.
- **QF_BVFP interop:** any BV operation may be freely mixed with FP; the whole
  formula blasts into one shared CNF.
- **Model extraction** for FP (and BV) constants.

**Deliberate non-goals (v1):**
- **Symbolic-Real bridge.** `fp.to_real`, and `to_fp` from a *symbolic/variable*
  Real, require an FP↔Reals combination (an eager-blasted value constrained in
  the lazy arith engine), which contradicts the Combiner-bypass architecture.
  Deferred to a later combination design → `unknown`. (Constant-Real
  conversions *are* supported — see §5.)
- **Theory combination** with EUF/Arith/Arrays. A query mixing FP/BV with those
  is refused as `unknown`, consistent with the existing `Unsupported` discipline
  in `shinri-theory::atom`.
- **Persistent incremental bit-blasting.** Each `check-sat` re-blasts the current
  assertion stack from scratch (matches QF_BV v1).

**Soundness contract:** anything out of scope returns `unknown`, never a wrong
SAT/UNSAT verdict.

## 2. Approach

**Eager bit-blasting to gate-level circuits**, reusing the `shinri-bv`
infrastructure. FP terms lower (SymFPU-style: unpack → operate → normalize →
round → special-case → pack) directly to Boolean clauses for the CDCL SAT core.

This is the same architecture as QF_BV: FP is a *lowering stage*, not a
`TheorySolver`. It **does not implement `TheorySolver` and never reaches the
`Combiner`.**

Alternatives considered and rejected:
- **Abstraction-refinement (lazy FP):** can dodge large circuits on easy
  benchmarks, but is a major departure from the eager-BV machinery, harder to
  make sound first, and needs a new refinement seam. High risk for a first cut.
- **Reduction to Real arithmetic + integer exponents:** correct rounding in
  reals is brutal, `div`/`sqrt` go nonlinear, and it discards the strong BV
  substrate. Not competitive.

## 3. Architecture & Pipeline Placement

`shinri-fp` is an eager bit-blasting front-end, exactly like `shinri-bv`. The one
structural change versus BV: because v1 is full **QF_BVFP**, FP and BV blast into
**one shared `Blaster`** so a value can cross the FP↔BV boundary as a slice of
the same `Vec<BitLit>`.

```
parse → assertions (term DAG: may contain BV and FP)
          │
          ▼  unified eager lowering (shinri-bv + shinri-fp, ONE Blaster)
   ┌──────────────────────────────────────────────┐
   │ 1. collect BV+FP atoms from assertions         │
   │ 2. word-level rewrite / simplify (BV and FP)   │
   │ 3. blast residual → CNF + bit-vars (shared)    │
   │ 4. map each Bool-sorted atom → a literal        │
   └──────────────────────────────────────────────┘
          │  (assertions with BV/FP atoms replaced by Bool surrogates;
          │   definitional clauses handed to SAT)
          ▼
   existing Tseitin + CDCL SAT core  →  SAT/UNSAT
          │
          ▼  model.rs: read bit assignments → BV values + FP values
   (get-model / get-value)
```

Consequences:
- `shinri-fp` depends on `shinri-bv` and reuses its `Blaster`, adders, shifters,
  and comparators.
- The solver's lowering stage is unified: when a `check-sat` query contains *any*
  BV or FP sort/op (and no EUF/Arith/Array — same exclusivity rule BV uses
  today), it runs **one** lowering pass that blasts both BV and FP atoms into a
  single CNF + surrogate map. Pure QF_BV keeps working via this same path.
- FP equality `(= x y)` is bit-blasted (NaN-aware, see §4), **not** sent to the
  equality engine.
- The SAT core and Tseitin encoder need **zero** FP/BV awareness.

## 4. The Circuit Model

Every FP arithmetic op follows the same pipeline, on an *unpacked*
representation rather than raw bits.

**Unpacked form.** For each operand, computed once at unpack:
- `sign` (1 bit),
- `exp` in a widened **signed** representation (room for intermediate
  over/underflow),
- `sig` with the **explicit** leading bit (`1.fff` normal, `0.fff` subnormal),
- flags `isNaN`, `isInf`, `isZero` derived from the bits.

**Pipeline** (e.g. `fp.add RM x y`):
1. **Unpack** x, y → signs/exps/sigs/flags.
2. **Align & operate:** barrel-shift the smaller-exponent significand right by
   the exponent difference, capturing a **sticky** bit of everything shifted
   out; add/subtract on the aligned, guard/round/sticky-extended significands.
3. **Normalize:** leading-zero-count + left-shift to canonical form, adjusting
   `exp`.
4. **Round:** the rounder decides "increment?" from `(guard, round, sticky, lsb,
   sign)` and the mode; a carry-out re-normalizes; exponent **overflow → ∞,
   underflow → subnormal/zero.**
5. **Special-case mux:** override the normal path with the op's IEEE table
   (`∞ + (−∞) = NaN`, `x/0 = ∞`, `0·∞ = NaN`, `sqrt(neg) = NaN`,
   `sqrt(−0) = −0`, …).
6. **Pack:** reassemble `sign | exp | sig` into `eb+sb` bits.

### 4.1 Correctness traps, handled explicitly

**NaN canonicalization.** The theory has *exactly one* NaN value, but the
`(fp …)` constructor can build NaN with any payload. Therefore:
- **Packing** a NaN result always emits the canonical NaN pattern.
- **Inputs** keep their literal bits (so a bitcast to BV is faithful).
- Core `=` over FP is blasted as
  `(isNaN x ∧ isNaN y) ∨ (¬isNaN x ∧ ¬isNaN y ∧ bits(x) = bits(y))` — **not**
  raw bit-equality.
- `+0` and `−0` are **distinct** under core `=` (separate theory values) but
  **equal** under `fp.eq`. These are two different gadgets.

**Symbolic rounding modes.** `RoundingMode` may be a variable, so it is encoded
as 3 bits; the rounder muxes the increment decision over all five modes. When
the mode is a literal (the common case), `rewrite` constant-folds the mux away.

**Single-rounding FMA.** `fp.fma RM x y z` computes `round(x·y + z)` with **one**
rounding: multiply to full width, add `z` aligned at full width, then round once.

### 4.2 Reuse vs. new gadgets

- **Reused from `shinri-bv`:** alignment/normalization barrel shifts, ripple
  adders, the multiplier, the restoring divider.
- **New in `shinri-fp`:** leading-zero-counter (`lzc.rs`), the rounder
  (`round.rs`), a square-root datapath (`fp.sqrt`), and the full-width
  single-rounding fused multiply-add (`fp.fma`).

## 5. Conversions & the Real Boundary

Conversions that stay inside the eager substrate:
- `to_fp` from a **BV of width `eb+sb`** → bitcast (pure wiring).
- `to_fp` **FP→FP** → unpack, re-round, pack.
- `to_fp` from a **signed BV** / `to_fp_unsigned` from an **unsigned BV** →
  integer→FP with rounding.
- `fp.to_ubv m` / `fp.to_sbv m` → FP→integer with rounding. **NaN/∞/out-of-range
  is "unspecified" in SMT-LIB**, so we emit *unconstrained* result bits (sound —
  any value is legal).

**The Real boundary** (the only scope line below "literally everything"), because
Reals live in the *lazy* arith engine, not the eager bit-blaster:
- `to_fp` from a **constant Real literal** → **supported**: round the exact
  `Rational` at blast time via `reference.rs`. (The common case.)
- `fp.to_real`, and `to_fp` from a **symbolic/variable Real** → **`unknown`**.
  These need an FP↔Reals combination that deliberately contradicts the
  Combiner-bypass architecture; deferred to a later design.

This keeps v1 fully eager and self-contained while still covering essentially
every real-world QF_FP benchmark (symbolic-Real conversions are rare).

## 6. Module Decomposition

### 6.1 `shinri-core` additions
- `SortNode::Float(eb, sb)` (sb includes the hidden bit; total width `eb+sb`),
  with the four `FloatNN` aliases resolving in the parser. Sort-checking
  computes result sorts and enforces width agreement on `(fp …)` args.
- `SortNode::RoundingMode`.
- FP literal values: the five specials per format, and the `(fp …)` constructor.
- Five `RoundingMode` constants.
- `BuiltinOp` variants for every FP op. Rounded ops take a `RoundingMode`
  operand (no index); indexed conversions carry params: `ToFp{eb,sb}`,
  `ToFpUnsigned{eb,sb}`, `FpToUbv(m)`, `FpToSbv(m)`.

### 6.2 `shinri-parser` additions
- `(_ FloatingPoint eb sb)` + `Float16/32/64/128` aliases; `RoundingMode`.
- Rounding-mode tokens (long and short: `roundNearestTiesToEven` / `RNE`, etc.).
- `(fp …)`, the `(_ ±oo/±zero/NaN eb sb)` family, indexed conversions via the
  existing `(_ … )` path.

### 6.3 `shinri-fp` crate

| Module | Responsibility |
|---|---|
| `lib.rs` | Public entry; orchestrates `rewrite → blast` for FP atoms; plugs into the unified lowering alongside BV (shared `Blaster`). |
| `rewrite.rs` | FP word-level simplification: constant-fold ops over literal FP values (via `reference.rs`), specialize literal rounding modes, `fp.neg/abs` identities, `to_fp`-bitcast collapse. |
| `unpack.rs` / `pack.rs` | bits ↔ unpacked form (sign/exp/explicit-sig/flags); `pack` applies NaN canonicalization. |
| `round.rs` | The rounder: 5-mode increment decision, carry re-normalize, overflow→∞, underflow→subnormal/zero. |
| `lzc.rs` | Leading-zero-counter (shared by normalize paths). |
| `blast/{add,mul,div,sqrt,fma,rem,roundint}.rs` | One datapath each. `fma` multiplies full-width and rounds once; `rem` is exact (no rounding). |
| `blast/{compare,classify,minmax}.rs` | `leq/lt/geq/gt/fp.eq` + NaN-aware core `=`; the 7 classification predicates; `fp.min/max`. |
| `convert.rs` | `to_fp` (bitcast / FP→FP / int→FP), `to_fp_unsigned`, `fp.to_ubv/to_sbv`. |
| `model.rs` | Reconstruct FP values from the SAT bit assignment for `get-model`/`get-value`. |
| `reference.rs` | The exact-rational golden oracle (also used by `rewrite` for constant folding). |

## 7. The Exact-Rational Oracle & Testing

**`reference.rs` — the golden semantics.** A scalar evaluator that, given an op
and concrete operand values, computes the result the way IEEE *defines* it: form
the **exact** result as a `shinri-num::Rational` (infinite precision), then
**round** it into the target `(eb, sb)` under the active mode, handling specials
by the same tables the circuits use. Because it is the literal spec definition,
it is the trusted reference for both correctness and `rewrite` constant-folding.
It covers every format and all five modes — no native-`f32`/`f64` blind spots.

**Test layers** (mirroring the established differential pattern):
- **Per-gadget bit-identical tests:** blast each datapath, fix concrete inputs,
  assert modeled output bits equal `reference.rs`. **Exhaustive on tiny formats**
  (e.g. `(3,5)`, `(5,11)`/Float16 where feasible), **randomized** on
  Float32/64/128. Sweep all five rounding modes; explicitly seed subnormals,
  `±0`, `±∞`, NaN, ties, and overflow/underflow boundaries.
- **Rewrite equivalence:** simplify, then miter original-vs-rewritten and assert
  UNSAT.
- **Differential-vs-z3** on random well-typed QF_FP/QF_BVFP formulas → agree on
  SAT/UNSAT; plus the workspace non-regression sweep.
- **End-to-end witness tests:** known SAT/UNSAT queries with `get-model` checks,
  and FP↔BV bitcast round-trips.

## 8. Error Handling, Incrementality & Models

- **Unsupported / out-of-scope** → `unknown`, never a wrong answer. Covers:
  FP/BV mixed with EUF/Arith/Arrays, and the symbolic-Real bridge.
- **Sort/width errors** (e.g. `(fp …)` arg widths not matching `eb`/`sb-1`,
  `to_fp` bitcast width ≠ `eb+sb`) caught at sort-check in `shinri-core`, before
  blasting.
- **Incrementality (push/pop):** v1 re-blasts on each `check-sat` over the
  current assertion stack, sharing the BV cache rebuild. Persistent incremental
  blasting is a v1 non-goal.
- **Model extraction:** `model.rs` reads each declared FP constant's bit-vars
  from the SAT assignment and formats them; NaN renders as the canonical pattern.

## 9. Summary of Decisions

| Decision | Choice |
|---|---|
| Engine model | Eager bit-blast (Approach 1), shared `Blaster` with BV |
| Operator coverage | Full QF_FP |
| FP/BV interop | Full QF_BVFP, one shared CNF |
| Combiner integration | None — eager front-end, bypasses the theory seam |
| Real conversions | Constant-Real supported; symbolic-Real → `unknown` (later combination) |
| Validation | Exact-rational golden oracle + differential-vs-z3 |
| Incrementality | Re-blast per `check-sat` |
| Combination (FP+EUF/Arith/Arrays) | Out of scope for v1 |
