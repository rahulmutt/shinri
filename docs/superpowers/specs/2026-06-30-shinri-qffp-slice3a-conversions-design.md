# shinri QF_FP — Slice 3a Design: non-BV `to_fp` conversions + symbolic-Real fence

**Date:** 2026-06-30
**Status:** Approved design, pre-implementation
**Scope:** The first slice of **Plan 3 (conversions + Real fence)**. Admits the two
operand kinds of `to_fp` that stay entirely inside the FP substrate — **FP→FP**
(re-round) and **constant-Real→FP** (fold) — and refines the slice-1 stand-in fence
into the parent design's real **symbolic-Real → `Unknown`** boundary. All BV-crossing
conversions remain fenced (Plan 4+).
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (architecture, §5 the Real boundary)
**Roadmap:** `docs/superpowers/specs/2026-06-25-shinri-qffp-vertical-slice-design.md` (§3, Plan 3)

## 0. Where this slice sits

Plans 1 (vertical slice) and 2 (rounder + all arithmetic, slices 2a–2g) are landed;
Plan 2 closed with `fp.rem`. `crates/shinri-fp/src/convert.rs` **does not exist yet** —
the entire conversion suite is fenced to `Unknown` (`fp_stage.rs::is_supported_fp_word`
ends in an "anything else (… conversions …) → false" arm).

Plan 3's conversion suite splits by whether it crosses the FP↔BV boundary. The FP
`Blaster` is **private** until Plan 4, and the mixed-theory fence already trips on any
BV-alongside-FP query. This slice takes the **non-BV half** — the only conversions that
are fully eager and self-contained today:

| Form | Term shape (`shinri-core`) | This slice |
|---|---|---|
| **FP→FP** | `ToFp{eb,sb}` 2 args `(RM, x)`, `x` Float | **admit** — new circuit |
| **const-Real→FP** | `ToFp{eb,sb}` 2 args `(RM, r)`, `r` constant Real | **admit** — fold |
| signed-int→FP | `ToFp{eb,sb}` 2 args `(RM, bv)` | fenced (BV) → Plan 4 |
| bitcast | `ToFp{eb,sb}` 1 arg `(bv)`, width `eb+sb` | fenced (BV) → Plan 4 |
| unsigned-int→FP | `ToFpUnsigned{eb,sb}` `(RM, bv)` | fenced (BV) → Plan 4 |
| FP→int | `FpToUbv(m)` / `FpToSbv(m)` `(RM, x)` | fenced (BV) → Plan 4 |
| FP→Real | `FpToReal` `(x)` | fenced (Real bridge) → never in v1 |
| **symbolic-Real**→FP | `ToFp{eb,sb}` 2 args `(RM, r)`, `r` non-constant Real | fenced (Real bridge) → later combination |

The operand-kind disambiguation is fixed by core sort-checking
(`shinri-core/src/context.rs:560`): `ToFp` with **1 arg** is the BV bitcast; with **2
args** `(RM, X)`, `X` is Float / BV / Real. This slice recognizes the Float and
constant-Real cases of the 2-arg form and nothing else.

## 1. Semantics (the spec we encode)

`((_ to_fp eb sb) RM x)` produces the value of `x` **rounded** into the target format
`(eb, sb)` under `RM`, per SMT-LIB `FloatingPoint` / IEEE 754 §5.4.2.

**FP→FP.** Let `x` be a Float of source format `(eb_s, sb_s)`.
- `NaN → canonical NaN`; `±∞ → ±∞`; `±0 → ±0` (sign preserved) — independent of `RM`.
- Finite: the exact real value of `x` is representable-or-rounded into `(eb_t, sb_t)`
  under `RM`, with overflow→∞ and underflow→subnormal/zero exactly as the arithmetic
  rounder already handles. **Widening** (target can represent every source value) never
  rounds; **narrowing** rounds under `RM`. Both go through the same path (§2).

**constant-Real→FP.** Let `r` be a constant Real with exact value `q ∈ ℚ`. The result is
`round_rational(eb, sb, q, RM)` — the exact rational rounded into `(eb, sb)`. No specials
arise (a constant Real is always finite); overflow→∞ and underflow→subnormal/zero follow
from the rounder. This is the parent design's "round the exact `Rational` at blast time"
(§5), now realized.

**Symbolic `RM`.** `RM` may be a variable; the FP→FP path muxes the increment decision
over all five modes exactly as the arithmetic ops do. (For const-Real, a symbolic `RM`
means the folded result is itself a 5-way mux over the five `round_rational` values — see
§2.)

## 2. The two datapaths

### 2.1 FP→FP — `convert.rs` (the only new circuit)

Pipeline: **unpack → (re-)round → pack**, reusing existing, already-trusted gadgets.

1. **Unpack** the source operand at `(eb_s, sb_s)` → `(sign, signed exp, explicit sig,
   isNaN, isInf, isZero)` via the shared operand path.
2. **Round** the source significand + exponent into the target `(eb_t, sb_t)` through the
   **existing `round.rs` rounder**. One unified path covers both directions: widening
   produces guard/round/sticky all-zero, so the rounder provably never increments (exact
   re-encode); narrowing feeds real GRS bits and rounds under `RM`. Exponent overflow→∞,
   underflow→subnormal/zero are the rounder's existing behavior. Cancellation/normalization
   on widening of a subnormal source reuses `lzc`/`normalize`.
3. **Pack** `sign | exp | sig` at the target width, NaN-canonicalizing.
4. **Special-case mux:** `NaN → canonical NaN`, `±∞ → ±∞`, `±0 → ±0` override the datapath.

**Approach choice (locked): single unified-through-the-rounder path**, not a separate
exact-recode gadget for widening. It is less code and reuses the trusted rounder; widening
correctness is the rounder's existing "GRS all-zero ⇒ no increment" property, checked
bit-identically against the oracle.

**Same-format `to_fp` (`(eb_s,sb_s) == (eb_t,sb_t)`)** is **not** special-cased — it falls
through the rounder as a harmless exact re-round (identity on the value; NaN still
canonicalizes, which is the correct SMT-LIB behavior). A `rewrite.rs` identity fold can be
added later; it is out of scope here.

### 2.2 constant-Real→FP — fold, no circuit

Detect a constant-Real operand with a thin helper:

```
try_const_real(ctx, t) -> Option<Rational>
  = numeral_value(t)                       // literals + parser-folded (/ lit lit)
  | Neg/Sub-of-constant-Real, folded       // unary minus of a literal
  | else None                              // symbolic Real → fence
```

The parser already constant-folds `(/ lit lit)` into a single numeral
(`shinri-parser/src/parser.rs:674`) and lexes decimals straight to numerals, so the
breadth "literals + `(/ lit lit)` + `(- lit)`" reduces to `numeral_value` plus a unary-Neg
unwrap. A **symbolic** Real arrives as a variable or as `(* recip x)` (from `(/ … x)`) →
`numeral_value` is `None` → `try_const_real` returns `None` → the atom is unsupported → the
query fences to `Unknown`.

When `Some(q)`: emit the result **as a constant** — compute bits via
`reference::round_rational(eb, sb, &q, mode)` and intern a `ConstVal::Float` literal. No
gates. For a **literal** `RM` (the common case) this is a single constant; for a
**symbolic** `RM`, emit a 5-way `mux` over the five `round_rational(…, mode_i)` constants
selected by the 3 RM bits (cheap — five precomputed literals, no datapath).

### 2.3 Reference oracle (already built)

Both datapaths validate against composition of **existing, tested** `reference.rs`
functions — no new oracle code:
- FP→FP golden: `decode` source bits → `class_to_rational(eb_s, sb_s, …)` → `round_rational(eb_t, sb_t, q, mode)`.
- const-Real golden: `round_rational(eb, sb, q, mode)` directly.

`round_rational` and `class_to_rational` were built in full in slice 1 and are already
trusted by every arithmetic slice.

## 3. Dispatch + fence

- **`shinri-fp/src/convert.rs`** (new): `pub fn to_fp_fp(b: &mut Blaster, x: &[BitLit],
  eb_s, sb_s, eb_t, sb_t, rm: &RmSel) -> Vec<BitLit>` (the FP→FP circuit, mirroring the
  `fp_add`/`fp_rem` signature style) and a const-Real fold entry returning packed literal
  bits.
- **`shinri-fp/src/blast/mod.rs`** / **`lib.rs`:** declare `pub mod convert;` and add a
  `ToFp{..}` arm to `blast_word` dispatch that branches on operand kind (FP child → circuit;
  `try_const_real` → fold). The 1-arg bitcast and BV-operand 2-arg forms are **not**
  dispatched here — they never reach blast because the fence rejects them first.
- **`shinri-solver/src/fp_stage.rs`:** one new arm in `is_supported_fp_word`:

  ```
  ToFp{..} with kids.len() == 2
    && is_rounding_mode_term(kids[0])
    && ( is_supported_fp_word(kids[1])           // FP→FP
       || try_const_real(ctx, kids[1]).is_some() ) // const-Real
  ```

  `try_const_real` lives here (or a shared helper) so the fence and the folder agree
  exactly on what "constant Real" means. Every other `ToFp`/`ToFpUnsigned`/`FpToUbv`/
  `FpToSbv`/`FpToReal` shape — and a 2-arg `ToFp` whose operand is BV or symbolic-Real —
  stays in the "→ false" arm → `Unknown`. Update the slice-enumeration doc-comment to
  mention slice 3a.

**Fence ⇄ folder agreement is soundness-critical:** the fence must admit an atom **iff**
the folder can handle it. If the fence admitted a const-Real form the folder later choked
on, `blast_word`'s `unreachable!` becomes a user-triggered panic; if the fence is stricter
than the folder, we lose completeness but stay sound. They share `try_const_real` to make
the admit-set identical by construction.

## 4. Canary handling (verify; likely no repoint)

Slice 2g deliberately repointed the malformed/fail-closed canary to **`fp.to_real`**,
chosen because the FP→Real direction needs an FP↔Reals combination deferred for **all of
v1** — so it stays fenced through Plan 3. That choice was made *anticipating this slice*:
`to_fp`-from-Real is partially admitted here (constant Reals), but `fp.to_real` is not, so
**the standing canary remains valid and needs no repoint.**

Per the established cross-slice lesson (a self-contained new op looks clean in isolation;
the breakage is in *prior* slices' canaries), this slice still must:

1. Run the **whole** `cargo test -p shinri-solver --test fp_e2e`, not just the new tests.
2. `grep -n 'to_fp\|ToFp' crates/shinri-solver/tests/` for any canary that nested a
   `to_fp` **FP→FP** or **constant-Real** form as its out-of-scope trigger — those flip
   from `Unknown` to decidable and would break. Expected: none (canaries use `fp.to_real`),
   but verify rather than assume. Repoint any that surface to `fp.to_real`.

## 5. Validation

- **Bit-identical vs `reference.rs`** (FP→FP, `convert.rs`): assert modeled bits equal the
  `decode → class_to_rational → round_rational` composition. **Exhaustive** on
  `(3,5)↔(5,11)` both directions (widen + narrow); **randomized** on Float16↔Float32↔Float64.
  Sweep all five rounding modes. Seed `±0`, `±∞`, NaN (canonical + non-canonical payload —
  must canonicalize on output), subnormals (source and result), normals, exact ties on
  narrowing, and overflow/underflow boundaries (narrowing that rounds to ∞ / to subnormal /
  to zero).
- **const-Real goldens:** `(to_fp (/ 1 3))`, integer and decimal literals, negatives via
  `(- …)`, values exactly on a rounding tie, and magnitudes that overflow→∞ / underflow→0;
  assert the emitted literal bits equal `round_rational`. Cover a **symbolic `RM`** const-
  Real (the 5-way mux) and assert each mode selects the right literal.
- **Fence / `Unknown` tests:** each of `to_fp` from a **symbolic** Real (variable and
  `(* recip x)`), `fp.to_real`, `to_fp` from a BV (signed-int), the 1-arg bitcast,
  `to_fp_unsigned`, `fp.to_ubv`, `fp.to_sbv` → `Unknown`. Confirms the admit-set is exactly
  the two intended forms.
- **Differential vs z3:** extend the feature-gated `fp_oracle.rs` corpus with FP→FP and
  constant-Real `to_fp` over feasible formats and all modes; agree on SAT/UNSAT. BV-crossing
  forms stay out of the corpus until Plan 4.
- **End-to-end:** known SAT/UNSAT scripts with `get-model` round-trips (e.g.
  `(assert (fp.eq ((_ to_fp 11 53) RNE x) y))` widening a Float32 `x`;
  `(assert (fp.eq ((_ to_fp 8 24) RNE (/ 1.0 3.0)) z))`).
- **Non-regression:** full workspace `cargo test` stays green; the QF_BV path and the
  FP-private `Blaster` are untouched.

## 6. Soundness contract (unchanged from parent)

Anything outside this slice's scope returns `Unknown`, never a wrong verdict: FP+BV mixing
and **all BV-crossing conversions** (until Plan 4), FP+EUF/Arith/Arrays, `fp.to_real` and
symbolic-Real `to_fp` (later combination, never in v1). Sort/width errors are caught at
sort-check in `shinri-core` before blasting.

## 7. Decisions locked for slice 3a

| Decision | Choice |
|---|---|
| Slice scope | The two **non-BV** faces of `to_fp`: FP→FP + constant-Real; bundled |
| FP→FP circuit | Single unified path through the existing `round.rs` rounder (widen = no-increment round); no separate exact-recode gadget |
| Same-format `to_fp` | Not special-cased — falls through the rounder (harmless exact re-round); identity fold deferred to `rewrite.rs` |
| const-Real → FP | Fold to a `ConstVal::Float` via `reference::round_rational`; symbolic `RM` → 5-way mux over five precomputed literals |
| "Constant Real" breadth | `try_const_real` = `numeral_value` (literals + parser-folded `(/ lit lit)`) + unary-`Neg` unwrap; anything else (Real var, `(* recip x)`) → `Unknown` |
| Fence ⇄ folder | Share `try_const_real` so the admit-set is identical by construction (soundness) |
| Oracle | Reuse existing `decode`/`class_to_rational`/`round_rational`; no new oracle code |
| Canary | Standing `fp.to_real` canary stays valid (no repoint); still run full `fp_e2e` to verify no prior canary nested an admitted `to_fp` form |
| BV-crossing conversions | Out of scope — Plan 4 (shared Blaster) unblocks them |
