# shinri QF_FP — Vertical Slice (Slice 1) Design

**Date:** 2026-06-25
**Status:** Approved roadmap + slice-1 spec, pre-implementation
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (architecture, approved)
**Foundation:** `docs/superpowers/plans/2026-06-24-shinri-qffp-foundation.md` (landed 2026-06-25 — term layer complete)

This document specifies **how** the approved QF_FP architecture gets built now that the
term layer (core sorts/ops + parser) has landed. It does **not** revise the parent
architecture — engine model, operator coverage, the eager-bit-blast approach, and the
two carry-forwards are all unchanged. It defines the implementation **roadmap** and the
**first vertical slice**, which is the only piece we cut an implementation plan for next.

## 1. Where things stand

- **Landed:** every QF_FP / QF_BVFP term parses and sort-checks into a well-sorted DAG
  (`shinri-core` sorts/ops/literal table; `shinri-parser` surface syntax). See foundation plan.
- **Unbuilt:** the entire `shinri-fp` crate (parent design §6.3) and all solver wiring.
- **Carry-forwards pinned in the parent design:**
  - **Printer placeholders** — `crates/shinri-parser/src/print.rs:51-52` render
    `ConstVal::Float`→`"<fp>"` and `ConstVal::Rm`→`"<rm>"`. Inert today (no model path
    exercises them); a wrong-output bug the moment a model path goes live.
  - **Symbolic-Real fence** — `fp.to_real` and `to_fp`-from-Real sort-check but must be
    fenced to `unknown` in the **solver stage** (never solved). Constant-Real conversions
    are supported via `reference.rs`.

## 2. The seam (what slice 1 must plug into)

The existing QF_BV path is the template. Slice 1 mirrors it exactly, with an FP-private
`Blaster` (BV+FP unification is deferred — see §3, Plan 4).

- **`shinri_bv::Blaster`** (`crates/shinri-bv/src/blast/mod.rs`) — the reusable gate-level
  builder over a private `BitLit` namespace. Public surface slice 1 reuses:
  `new`, `one`, `zero`, `fresh`, `add_clause`, `not1`, `and2`, `or2`, `xor2`, `mux2`,
  `full_adder`, `finish`, `exported_var_bits`. (`blast_word`/`blast_atom` are BV-specific
  dispatch; FP adds its own dispatch over the same primitives.)
- **`shinri_bv::lower()` → `Lowered { cnf, atom_lit, var_bits }`** — the BV collect-and-blast
  loop. `atom_lit` is keyed by the **original** (pre-rewrite) atom `TermId`. FP gets an
  analogous `shinri_fp::lower()`.
- **`crates/shinri-solver/src/bv_stage.rs`** — `solver_uses_bv`, `collect_bv_atoms`
  (soundness-critical: includes BV `=`/`distinct`), `has_non_bv_theory_atom` (mixed-theory
  fence), and `BvSurrogates { atom_to_lit, var_bits }`. FP gets a parallel `fp_stage.rs`.
- **`crates/shinri-solver/src/lib.rs`** (~line 343-360) — where `solver_uses_bv` →
  `collect_bv_atoms` → fence → `lower` → surrogate map is wired before the SAT skeleton.
  The FP stage slots in alongside, gated so a pure-QF_FP query routes through it.

**FP bit layout** (fixed by the foundation): MSB→LSB `[ sign(1) | exponent(eb) |
trailing-significand(sb-1) ]`, total width `W = eb + sb`, `sb` **includes** the hidden bit.

## 3. Roadmap (4 plans)

| # | Plan | Delivers | End-to-end answer? |
|---|---|---|---|
| **1** | **Vertical slice** (this spec) | `shinri-fp` skeleton, `reference.rs`, `unpack`/`pack`, a **rounding-free** op set, FP-only `fp_stage.rs`, `model.rs`, printer fix | **Yes** — SAT/UNSAT/get-model on Float formulas |
| **2** | **Rounder + arithmetic** | `round.rs`, `lzc.rs`, then `add/sub`, `mul`, `div`, `sqrt`, `fma`, `rem`, `roundToIntegral`, `min/max`; `rewrite.rs` folding grows alongside | yes, expanding op set |
| **3** | **Conversions + Real fence** | `convert.rs` (bitcast / FP↔FP / int→FP / `to_ubv`/`to_sbv` / constant-Real `to_fp`); the **symbolic-Real `unknown` fence** | yes |
| **4** | **QF_BVFP unification** | refactor lowering into one shared driver feeding a single `Blaster` across BV+FP | yes, mixed FP↔BV |

Until Plan 4, a query mixing FP and BV (or FP with EUF/Arith/Arrays) returns a **sound
`Unknown`**, never a wrong verdict. This is the existing `bv_stage` fence discipline,
extended to FP.

## 4. Slice 1 specification

**Goal:** a real end-to-end QF_FP answer — parse → blast → SAT → model — on the subset of
operators that need **no rounder and no arithmetic datapath**, proving the whole seam
(crate wiring, `Blaster` reuse, stage detect/collect/fence, model read-back, printer)
before any heavy circuit is built.

### 4.1 New crate: `crates/shinri-fp`

Depends on `shinri-bv` (for `Blaster`/`BitLit`), `shinri-core`, `shinri-num`, `rustc-hash`.
No new external dependencies. Slice-1 modules:

| Module | Slice-1 responsibility |
|---|---|
| `lib.rs` | `lower(ctx, fp_atoms) -> Lowered`-shaped entry; FP-private `Blaster`; collect-and-blast loop keyed by original atom `TermId`. |
| `reference.rs` | The exact-`Rational` golden oracle, **built in full** (round core included), so Plans 2–3 inherit a trusted reference. Slice-1 ops exercise its unpack/classify/pack paths; its rounding core is unit-tested here even though no slice-1 op rounds. |
| `unpack.rs` | bits → unpacked `(sign, exp, explicit-sig, isNaN, isInf, isZero)`. |
| `pack.rs` | unpacked → bits, applying **NaN canonicalization** on any NaN result. |
| `blast/classify.rs` | the 7 predicates: `isNormal`, `isSubnormal`, `isZero`, `isInfinite`, `isNaN`, `isNegative`, `isPositive`. |
| `blast/compare.rs` | `fp.eq` (`+0`==`−0`, NaN≠NaN) and **NaN-aware core `=`** (`(isNaN x ∧ isNaN y) ∨ (¬isNaN x ∧ ¬isNaN y ∧ bits=bits)`) — two distinct gadgets. |
| `blast/structural.rs` | `fp.abs` (clear sign), `fp.neg` (flip sign) — pure bit twiddling, no unpack needed. |
| `model.rs` | reconstruct FP constant values from the SAT bit assignment; NaN renders canonical. |

Deferred to later plans (NOT in slice 1): `round.rs`, `lzc.rs`, `rewrite.rs`, all
`blast/{add,mul,div,sqrt,fma,rem,roundint,minmax}.rs`, `convert.rs`.

### 4.2 Solver wiring: `crates/shinri-solver/src/fp_stage.rs`

Parallel to `bv_stage.rs`:
- `solver_uses_fp(ctx, assertions) -> bool` — any Float-sorted subterm or FP builtin op.
- `collect_fp_atoms(ctx, assertions) -> Vec<TermId>` — Bool-sorted FP atoms: the FP
  predicates **and** `Eq`/`Distinct` whose operands are Float-sorted. **Soundness-critical:**
  FP `=`/`distinct` MUST be surrogated (otherwise it routes to EUF as an uninterpreted
  function and can answer wrongly), exactly as `collect_bv_atoms` includes BV equalities.
- `has_non_fp_theory_atom(ctx, assertions, fp_atoms) -> bool` — conservative mixed-theory
  fence: any Bool-sorted atom outside `fp_atoms` that is not pure Boolean structure → fence
  to `Unknown`. In slice 1 this **includes BV atoms** (BV+FP mixing waits for Plan 4) and
  any `RoundingMode`-typed weirdness.
- `FpSurrogates { atom_to_lit, var_bits }`, wired into `lib.rs` alongside the BV stage:
  a query that `solver_uses_fp` and is not fenced routes through `shinri_fp::lower()`.
- **Slice-1 Real boundary:** no slice-1 op touches Reals, but `fp.to_real` /
  `to_fp`-from-Real are parseable today. The fence treats them as non-FP theory atoms →
  `Unknown` (the symbolic-Real fence's slice-1 stand-in; Plan 3 refines constant-Real to
  *supported*).

### 4.3 Carry-forward: printer (done in slice 1)

Replace `print.rs:51-52` placeholders with real SMT-LIB rendering, because slice 1's
`get-model`/`get-value` path makes them reachable:
- `ConstVal::Float(id)` → `(fp #b<sign> #b<exp> #b<trailing-sig>)` from the literal's
  `(eb, sb, bits)`, or the `(_ …)` special form for canonical specials.
- `ConstVal::Rm(rm)` → the `RNE`/`RNA`/`RTP`/`RTN`/`RTZ` token.

### 4.4 Validation

- **Per-gadget golden tests:** each slice-1 gadget asserted bit-identical to
  `reference.rs` — **exhaustive on a tiny format** (`(3,5)`: 256 values), **randomized**
  on Float16/Float32. Seed `±0`, `±∞`, NaN (canonical and non-canonical payloads),
  subnormals, and normals explicitly.
- **Equality-gadget tests:** prove `+0 == −0` under `fp.eq` but `+0 ≠ −0` under core `=`;
  prove NaN `≠` NaN under both; prove non-canonical-NaN inputs keep their bits (faithful
  bitcast) yet compare equal under `fp.eq`.
- **End-to-end:** known SAT/UNSAT scripts (e.g. `(assert (fp.isNaN x))` SAT with a NaN
  witness; `(assert (and (fp.isZero x) (fp.isInfinite x)))` UNSAT) with `get-model`
  round-trips through the fixed printer.
- **Differential vs z3:** a feature-gated `crates/shinri-fp/tests/fp_oracle.rs` (or under
  `shinri-solver`), mirroring `qfbv_oracle.rs` (`easy_smt` driving z3, deterministic LCG
  corpus, `#[cfg(feature = "oracle")]`), restricted to the slice-1 rounding-free op set.
  Extended each later plan.
- **Non-regression:** the full existing `cargo test` workspace sweep stays green; the
  QF_BV path is untouched (FP has its own stage and Blaster).

## 5. Soundness contract (unchanged from parent)

Anything outside slice-1 scope returns `Unknown`, never a wrong SAT/UNSAT: FP+BV mixing
(until Plan 4), FP+EUF/Arith/Arrays, every rounded/arithmetic op (until Plan 2), every
conversion and any Real bridge (until Plan 3). Sort/width errors are already caught at
sort-check in `shinri-core` before blasting.

## 6. Decisions locked for slice 1

| Decision | Choice |
|---|---|
| First-plan shape | Thin vertical slice — end-to-end on a rounding-free op set |
| Rounder in slice 1 | **No** — debuts with `fp.add` in Plan 2 |
| FP↔BV interop | FP-private `Blaster` now; unified shared `Blaster` in Plan 4 |
| Slice-1 ops | `fp.abs`, `fp.neg`, 7 classifications, `fp.eq`, NaN-aware core `=` |
| Oracle | `reference.rs` built in full in slice 1 (trusted reference for all later plans) |
| Printer carry-forward | Fixed in slice 1 (model path makes it reachable) |
| Symbolic-Real fence | Slice-1 stand-in: Real-FP conversions fence to `Unknown`; Plan 3 refines |
| Differential testing | z3 4.16.0 (+ cvc5 1.3.4 available), feature-gated, mirrors `qfbv_oracle.rs` |
