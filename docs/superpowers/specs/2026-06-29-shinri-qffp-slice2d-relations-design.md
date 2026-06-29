# shinri QF-FP slice 2d — ordering relations + fp.min/fp.max

**Date:** 2026-06-29
**Status:** Design (approved in brainstorming)
**Track:** QF-FP, follows slice 2c′ (fp.sqrt)

## Goal

Add the four IEEE/SMT-LIB floating-point ordering relations and the two
NaN-aware selectors to shinri's bit-blasted QF-FP path:

- Relations (Bool-producing): `fp.lt`, `fp.leq`, `fp.gt`, `fp.geq`
- Selectors (FP-word-producing): `fp.min`, `fp.max`

All six are **rounding-free** (no `RoundingMode` operand) and produce **shallow**
circuits — one unsigned comparator plus muxes, no recursion. This closes a
notable gap: `fp.eq` and core `=`/`distinct` over floats are already supported,
but the ordering relations are not.

## Background / current state

The FP crate already provides everything this slice builds on:

- `unpack(b, bits, eb, sb) -> Unpacked { sign, exp, sig, is_nan, is_inf, is_zero }`
- `blast/compare.rs`: `fp_eq` (IEEE equality: `+0 == -0`, NaN ⇒ false) and
  `core_eq` (NaN == NaN, `+0 != -0`)
- `reference.rs`: `decode`, `class_to_rational` (returns `None` for NaN **and**
  Inf), `ref_fp_eq`, `canonical_nan`, plus the `ref_*` differential references
  for every shipped op
- `Blaster` primitives: `not1`, `and2`, `or2`, `xor2`, `mux2`, `one`, `zero`
- The soundness fence in `shinri-solver/src/fp_stage.rs`
  (`is_supported_fp_word`, `fp_atom_is_supported`) that positively enumerates
  every op the blaster can handle, so an unhandled FP op fails closed rather
  than panicking.

## Semantics

### Ordering relations

NaN is unordered: any relation with a NaN operand is **false**. `+0` and `-0`
compare equal. Otherwise the usual extended-real order applies
(`-inf < negatives < ±0 < positives < +inf`).

One new primitive `fp_lt(x, y) -> BitLit` carries all four:

| op | definition |
|---|---|
| `fp.lt(x,y)`  | `fp_lt(x,y)` |
| `fp.gt(x,y)`  | `fp_lt(y,x)` |
| `fp.leq(x,y)` | `fp_lt(x,y) ∨ fp_eq(x,y)` |
| `fp.geq(x,y)` | `fp_lt(y,x) ∨ fp_eq(y,x)` |

NaN ⇒ false falls out for all four because both `fp_lt` and `fp_eq` already
force NaN to false.

### fp.min / fp.max

SMT-LIB follows IEEE-754 `minNum`/`maxNum`: **NaN passes through to the other
operand** (`min(NaN,y)=y`, `min(x,NaN)=x`, both-NaN ⇒ NaN). Otherwise the
smaller/larger by real order.

**`±0` decision (SMT-LIB-unspecified).** `fp.min(+0,-0)` may legally return
either zero. shinri commits to a **sign-canonical, order-independent** rule:

- `fp.min(+0,-0) = fp.min(-0,+0) = -0`
- `fp.max(+0,-0) = fp.max(-0,+0) = +0`

This is a legal SMT-LIB value, is commutative/clean, and is expected to match
Z3 — keeping the differential oracle unconstrained. It costs one extra
both-zero special-case mux over a naive order-dependent select.

## Reference functions (`reference.rs`)

```rust
// Extended order key: -∞ < every finite rational < +∞; NaN is incomparable.
enum Ord3 { NegInf, Fin(Rational), PosInf }

// None iff NaN. Inf{sign} -> NegInf/PosInf; else Fin(class_to_rational(..).unwrap()).
// ±0 both collapse to Fin(0), so they compare equal.
fn order_key(eb, sb, c: &FpClass) -> Option<Ord3>

pub fn ref_lt(eb, sb, a: &Integer, b: &Integer) -> bool   // either NaN -> false; else key(a) < key(b)
pub fn ref_leq(..) -> bool   // ref_lt(a,b) || ref_fp_eq(decode a, decode b)
pub fn ref_gt(..)  -> bool   // ref_lt(b,a)
pub fn ref_geq(..) -> bool   // ref_lt(b,a) || ref_fp_eq(decode b, decode a)

pub fn ref_min(eb, sb, a, b) -> Integer
//   isNaN(a) -> b ; isNaN(b) -> a ;
//   both-zero & opposite sign -> canonical -0 bits ;
//   else ref_lt(a,b) ? a : b
pub fn ref_max(eb, sb, a, b) -> Integer   // symmetric; canonical +0 on the ±0 tie
```

`ref_min`/`ref_max` encode the *same* sign-canonical `±0` rule the circuit uses,
so the in-crate unit tests are self-consistent. The Z3 oracle is the separate
cross-check that the rule is also a legal choice Z3 agrees with.

## Blast circuits

### Unsigned magnitude comparator

Less-than on the `[exp ++ sig]` field (width `eb + sb - 1`), rippled LSB→MSB so
the most-significant bit dominates:

```rust
fn ult(b, x, y) -> BitLit {            // x < y, same width, LSB→MSB
    let mut lt = b.zero();
    for i in 0..x.len() {
        let bit_lt = b.and2(b.not1(x[i]), y[i]);
        let bit_eq = b.not1(b.xor2(x[i], y[i]));
        lt = b.or2(bit_lt, b.and2(bit_eq, lt));   // higher bit wins
    }
    lt
}
```

### fp_lt (`blast/compare.rs`)

```rust
let (ux, uy) = (unpack(x), unpack(y));
let mag_x = [ux.exp, ux.sig].concat();   // exp more significant than sig
let mag_y = [uy.exp, uy.sig].concat();
let mlt = ult(&mag_x, &mag_y);           // |x| < |y|
let mgt = ult(&mag_y, &mag_x);           // |x| > |y|

let signs_diff = xor(ux.sign, uy.sign);
let diff_case  = and(signs_diff, ux.sign);                  // x<0, y≥0 ⇒ x<y
let same_case  = and(not(signs_diff),
                     or(and(not(ux.sign), mlt),             // both ≥0: |x|<|y|
                        and(ux.sign,      mgt)));           // both <0: |x|>|y|
let raw        = or(diff_case, same_case);

let both_zero   = and(ux.is_zero, uy.is_zero);              // equal ±0 ⇒ not lt
let neither_nan = and(not(ux.is_nan), not(uy.is_nan));      // NaN ⇒ not lt
and(and(raw, not(both_zero)), neither_nan)
```

Infinities need no special case: `[all-ones-exp ++ zero-sig]` is the maximum
magnitude, so `-inf < everything < +inf` and `inf == inf` order out correctly.

`fp_leq`/`fp_gt`/`fp_geq` are trivial combinators over `fp_lt` and the existing
`fp_eq`.

### fp.min / fp.max (`blast/minmax.rs`, new)

```rust
fn mux_word(b, sel, a, c) -> Vec<BitLit>     // per-bit b.mux2(sel, a[i], c[i])

// min (max: swap the first pick and use +0 for the tie):
let lt = fp_lt(x, y);
let mut pick = mux_word(lt, x, y);                       // lt ? x : y
let zero_tie = and(both_zero, xor(ux.sign, uy.sign));
pick = mux_word(zero_tie, neg_zero_word, pick);          // min→-0 ; reuse const_n
let r = mux_word(uy.is_nan, x, pick);
mux_word(ux.is_nan, y, r)                                 // NaN passthrough, outermost
```

If either operand is NaN, `both_zero` is false, so `zero_tie` cannot conflict
with the NaN passthrough. `neg_zero_word`/`pos_zero_word` are built with the
existing constant-word helper (`const_n` in `blast/normalize.rs`).

## Wiring

| File | Change |
|---|---|
| `shinri-fp/src/blast/compare.rs` | add `fp_lt` (+ `ult`); `fp_leq/gt/geq` combinators |
| `shinri-fp/src/blast/minmax.rs` *(new)* | `fp_min`, `fp_max`, `mux_word` |
| `shinri-fp/src/blast/mod.rs` | `pub mod minmax;` |
| `shinri-fp/src/lib.rs` `blast_atom` | arms for `FpLt \| FpLeq \| FpGt \| FpGeq` |
| `shinri-fp/src/lib.rs` `blast_word` | arms for `FpMin \| FpMax` |
| `shinri-fp/src/reference.rs` | `Ord3`, `order_key`, `ref_lt/leq/gt/geq`, `ref_min/max` |
| `shinri-solver/src/fp_stage.rs` `fp_atom_is_supported` | admit `FpLt \| FpLeq \| FpGt \| FpGeq` (two supported FP operands) |
| `shinri-solver/src/fp_stage.rs` `is_supported_fp_word` | admit `FpMin \| FpMax` (two supported FP operands, **no RM operand**) |

## Tests

Three layers, matching the established FP pattern.

1. **Unit tests** (`compare.rs`, `minmax.rs`): blast a constant pair → SAT-eval
   → compare to `ref_*`, over a corner matrix: `±0`, `±inf`, qNaN, sNaN,
   normals, subnormals, and equal-magnitude/opposite-sign (`+1` vs `−1`).
   min/max additionally cover the `±0` opposite-sign tie and NaN passthrough
   (both directions and both-NaN).

2. **Differential-vs-Z3 oracle** (`shinri-solver/tests/fp_oracle.rs`, behind the
   `oracle` feature): extend the rounding-free generator to emit
   `fp.lt/leq/gt/geq` atoms and `fp.min/max` words (the latter folded into
   `fp.eq`/classification atoms so their outputs are observable). Pure SAT/UNSAT
   differential against Z3; assert both SAT and UNSAT coverage. The `±0` rule is
   expected to agree with Z3; a disagreement there is a real signal, not noise.

3. **End-to-end** (`shinri-solver/tests`): SAT/UNSAT scripts per relation plus
   min/max, with a `get-model` check. Examples: `(fp.lt x y)` SAT;
   `(and (fp.lt x y) (fp.lt y x))` UNSAT; `(not (fp.leq x x))` SAT only via a
   NaN `x`.

## Implementation notes

- These circuits are **shallow** (one comparator + muxes, no recursion), so the
  deep-circuit SAT-recursion / stack-overflow issues that affected `fp.div` and
  `fp.sqrt` do not apply.
- The oracle suite is multi-minute and gated; run it in the background during
  implementation rather than blocking on it.

## Out of scope

- Rounding-bearing FP ops (`fp.fma`, `fp.roundToIntegral`, `fp.rem`) and the
  conversion family (`to_fp`, `to_ubv`, `to_sbv`, `to_real`, `fromBits`) — each
  is its own later slice.
