# shinri QF_FP — Slice 4c: BV→FP bitcast (`FpFromBits` + 1-arg `to_fp`)

**Date:** 2026-07-01
**Status:** Landed — both bitcast faces (`FpFromBits` + 1-arg `to_fp`) admitted as pure
BV→FP bit-wiring; the 1-arg-bitcast crossing canary repointed and all other crossing faces
still fenced to `Unknown`. Verified: full workspace green (shinri-fp exhaustive 69/0, fp_e2e
52/0), full z3 oracle 12/12 zero disagreements (new `differential_qf_bvfp_bitcast`
z3_checked=200/200), clippy net-new-zero.
**Plan:** 4 (BV↔FP crossing conversions), first admitted conversion
**Predecessors:** slice 4a (unified `Lowerer`/`WordSink`), slice 4b (mixed
pure-BV+pure-FP fence-lift)

## 1. Goal & Scope

Admit the first BV↔FP **crossing** conversion: BV→FP bit reinterpretation over
BV operands (constant or symbolic alike — see §4). Two faces, both pure
bit-wiring — no rounding, no
special-value (NaN/Inf/range) logic. The result FP word *is* the source bits.

**In scope:**
- `(fp sign exp sig)` — `FpFromBits`, three BV operands of widths `1`, `eb`,
  `sb-1`, assembled into the `(eb+sb)`-bit FP word.
- `((_ to_fp eb sb) bv)` — the 1-arg `to_fp` bitcast, one BV operand of width
  `eb+sb`, reinterpreted as the IEEE bit pattern.

**Explicitly NOT in scope (stay fenced to `Unknown`):**
- `to_fp` 2-arg from a signed BV (int→FP, needs a round-from-integer circuit).
- `to_fp_unsigned` (`ToFpUnsigned`, unsigned BV→FP).
- `fp.to_ubv` / `fp.to_sbv` (FP→BV value conversions).
- `fp.to_real` (permanent v1 non-goal — the Real bridge).
- `to_fp` from a symbolic Real (later Real combination).

Each remains its own later slice.

**Soundness contract (unchanged):** anything out of scope returns `unknown`,
never a wrong SAT/UNSAT verdict.

## 2. Why this is pure wiring

Slices 4a/4b already built the seam this slice needs:

- `Lowerer::word` (`crates/shinri-fp/src/lower.rs:34-53`) dispatches by sort: a
  BV-sorted node routes to `blast_bv_word`, an FP-sorted node to
  `blast_fp_word`, both through one shared `Blaster` and one shared bit cache.
- The BV blaster is **total** over pure-BV ops once crossing ops are fenced
  (`crates/shinri-solver/src/lib.rs:395-396`).

So a BV child of an FP op already blasts correctly and lands in the shared
cache. The only missing piece is the FP-side arm that *consumes* those BV
bit-lits and presents them as the FP word.

## 3. The gadget (`crates/shinri-fp/src/lib.rs`, `blast_fp_word`)

FP words are packed **LSB-first**, matching the FP-const path (lib.rs:106-116),
where the packed integer is `sign·2^(eb+sb-1) + exp·2^(sb-1) + sig`:

- bits `[0 .. sb-1)` = significand (`sb-1` bits),
- bits `[sb-1 .. sb-1+eb)` = exponent (`eb` bits),
- bit `[eb+sb-1]` = sign.

**`FpFromBits`** (kids `[sign, exp, sig]`):

```
out = sink.word(ctx, sig) ++ sink.word(ctx, exp) ++ sink.word(ctx, sign)
```

concatenated in LSB-first order, yielding exactly `eb+sb` bits. Each
`sink.word` on a BV-sorted child routes to `blast_bv_word` via the shared
cache — no new plumbing.

**`ToFp` 1-arg** (kids `[bv]`): branch the existing `ToFp` arm on arity.
`len()==1` returns `sink.word(ctx, bv)` verbatim (SMT-LIB defines
`to_fp`-from-BitVec as a straight IEEE reinterpret; both sides are LSB-first).
`len()==2` keeps today's RM-based FP→FP re-round and const-Real fold faces
unchanged.

## 4. Fence lift (`crates/shinri-solver/src/fp_stage.rs`)

- **`uses_crossing_conversion`:** delete the `FpFromBits` arm and the `ToFp`
  `1 => true` arm. `FpToUbv` / `FpToSbv` / `ToFpUnsigned` / `FpToReal` and
  `ToFp`-2-arg-BV / symbolic-Real stay crossing. A BV child that itself nests a
  still-crossing op (e.g. `(fp (fp.to_ubv …) e m)`) is still caught by the same
  DAG walk — the safety net holds.
- **`is_supported_fp_word`:** add an `FpFromBits` arm (exactly 3 BV-sorted
  children) and extend the `ToFp` arm for the 1-arg BV-source case
  (1 BV-sorted child). No recursive support check on the BV children — the BV
  blaster is total and nested crossings are already fenced; a BV-sort check on
  the children is sufficient.
- **`is_fp_op`** already lists `FpFromBits` and `ToFp`, so `solver_uses_fp`
  fires unchanged; no change to the top-level dispatch in `lib.rs`.

**Literal args are NOT a special case.** Unlike the five indexed special forms
(`(_ +oo eb sb)` etc.), the `(fp …)` triple does *not* fold to a
`ConstVal::Float` — the parser builds `FpFromBits` with const-BV children for
both literal and symbolic args (see fp_e2e.rs:51-57), so today *every* `(fp …)`
fences to `Unknown`. The gadget therefore handles both uniformly: a const-BV
child blasts to constant bit-lits through `blast_bv_word`, a symbolic child to
fresh vars. `(fp #b0 #b0111 #b000)` yields a fully-constant FP word — no
separate folding path, and previously-`Unknown` literal-triple queries now solve
(a strict expansion of the admit-set, not a regression).

## 5. Reference model & validation

- **`reference.rs`:** `ref_fp_from_bits(sign, exp, sig)` — concrete concat of
  the three BV values → expected packed FP value; golden test asserting the
  field layout matches the const packing.
- **`fp_oracle.rs`:** a `gen_*` script emitting `(fp b0 b1 b2)` and a 1-arg
  `to_fp` over independently-declared BV vars inside an FP predicate, wired into
  a `#[test]` mirroring `differential_qf_fp_add_sub`. Skip on shinri `Unknown`;
  `panic!` on a true Sat/Unsat disagreement with z3.
- **`fp_e2e.rs` canary repoint** *(standing cross-slice lesson)*: lifting the
  fence flips today's `FpFromBits` / 1-arg-bitcast `Unknown`-canaries to
  Sat/Unsat. Repoint the stale entries onto a still-crossing op (`fp.to_ubv`),
  then run the **whole** `fp_e2e` suite and grep-audit the crossing-canary
  array. New positive canaries: at least one symbolic `(fp …)` script flips
  `Unknown → Sat` and one `→ Unsat`, with `get-model` read-back checked on both
  a source BV var and the resulting FP var in the same model.
- **Regression is an oracle.** Full workspace green; pure-BV and pure-FP
  verdicts byte-identical.

## 6. Risks

- **Bit-order of the concat.** The one correctness-critical detail: the
  `sig ++ exp ++ sign` LSB-first order must match the FP-const packing. A
  flipped field is a wrong (but not silently unsound) value. Mitigation: the
  z3 differential oracle and `get-model` read-back surface any field flip
  immediately; the reference model pins the layout independently.
- **Under-lifting / over-lifting the fence.** If a crossing arm is deleted that
  shouldn't be, a genuinely-crossing query reaches a `blast_*_word`
  `unreachable!` → panic (a crash, not unsoundness). Mitigation: only the two
  bitcast arms are removed; the canary array exercises every remaining crossing
  face and they must all stay `Unknown`.
- **Cross-slice canary breakage.** Per the standing lesson, admitting a new op
  breaks prior slices' malformed/crossing canaries. Mitigation: run the full
  `fp_e2e` suite and repoint at `fp.to_ubv`, not a partial run.

## 7. Decisions locked for slice 4c

| Decision | Choice |
|---|---|
| Faces admitted | Both — `FpFromBits` (symbolic `(fp …)`) **and** 1-arg `to_fp` bitcast |
| Direction | BV→FP only — no FP→BV bitcast op exists in SMT-LIB |
| Gadget placement | `blast_fp_word` arms; BV children blast through the existing sort-dispatched `Lowerer::word` |
| BV-child support | None recursive — BV blaster is total; a BV-sort check suffices, nested crossings stay fenced |
| Literal `(fp …)` | Not special-cased — `FpFromBits` for both literal & symbolic args; const children blast to constant bit-lits (literal triples, `Unknown` today, now solve) |
| Bit order | LSB-first `sig ++ exp ++ sign`, matching the FP-const packing |
| Fence edit | Remove `FpFromBits` + `ToFp` `1 =>` from `uses_crossing_conversion`; add the two `is_supported_fp_word` arms |
| Success criterion | Byte-identical existing verdicts + remaining crossing canaries still `Unknown` + symbolic bitcast solves & agrees with z3 |
| Next slices | int→FP (`to_fp` signed-BV / `to_fp_unsigned`), then FP→BV (`fp.to_ubv`/`fp.to_sbv`), each its own slice |
