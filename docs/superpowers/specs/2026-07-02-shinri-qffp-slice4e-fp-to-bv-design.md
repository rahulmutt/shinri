# shinri QF_FP — Slice 4e: FP→BV (`fp.to_ubv` + `fp.to_sbv`)

**Date:** 2026-07-02
**Status:** Landed — both FP→BV faces (`fp.to_ubv` + `fp.to_sbv`) admitted through the
`fp_to_int` gadget (decode → one right-shift-with-sticky → shared `rounding_increment` →
round-FIRST-then-range-check → ok-mux over fresh unconstrained bits), with unspecified
results encoded as an uninterpreted function of `(RM, x)` per `(face, m, eb, sb)` via
Ackermann-style congruence clauses (`FpToBvApp` registry on the `Lowerer`). First BV-sorted
FP op: dispatched by a `blast_fp_to_bv` SIBLING of `blast_fp_word` (§6's "blast_fp_word
gains the two arms" was refined — its preamble asserts an FP-sorted result), and the first
BV-atom embedded-FP support walk (`bv_atoms_fp_supported`, mutually recursive with
`is_supported_fp_word`) fences unsupported FP shapes reachable through BV atoms.
Verification: workspace EXIT=0, all 61 suites 0-failed (shinri-fp exhaustive 84/0 @2615s,
solver lib 83/0, fp_e2e 62/0 incl 5 new FP→BV e2e, shinri-bv 98/0); full z3 oracle 14/14
ZERO disagreements (new differential_qf_bvfp_fp_to_bv sat=105 unsat=95 unknown=0
z3_checked=200/200 incl 1-in-4 congruence probes; all pre-existing counts byte-identical
to the 4d baseline); 4 canaries repointed (fp_stage.rs ×3, fp_e2e.rs ×1); clippy net-new
zero after one allow-attribute fold. Remaining fence (permanent v1 Real bridge):
`fp.to_real` / symbolic-Real `to_fp`. **Plan 4 complete.**
**Plan:** 4 (BV↔FP crossing conversions), third and FINAL admitted conversion — closes Plan 4
**Predecessors:** slice 4a (unified `Lowerer`/`WordSink`), slice 4b (mixed fence-lift),
slice 4c (BV→FP bitcast), slice 4d (int→FP)
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (§5 conversions)

## 1. Goal & Scope

Admit the two **FP→integer** faces: round the real value of an FP term into an
`m`-bit unsigned or signed (two's-complement) BitVec under `RM`. This is the
first slice where (a) an FP-op term is **BV-sorted** (reverse dispatch), and
(b) the result is **SMT-LIB-unspecified** on some inputs (NaN, ±∞,
out-of-range) — there is no single correct output bit-pattern.

**In scope (both faces, one slice — mirrors 4d):**
- `((_ fp.to_ubv m) RM x)` — `FpToUbv{m}`: unsigned read.
- `((_ fp.to_sbv m) RM x)` — `FpToSbv{m}`: two's-complement read.

**Explicitly NOT in scope (stay fenced to `Unknown`, durably):**
- `fp.to_real` (permanent v1 non-goal — the Real bridge).
- `to_fp` from a symbolic Real (later Real combination).

After this slice the crossing set is exactly those two permanent/deferred
faces; Plan 4 is complete.

**Soundness contract (unchanged):** anything out of scope returns `unknown`,
never a wrong SAT/UNSAT verdict.

## 2. Semantics (the spec we encode — empirically pinned against z3 4.16)

SMT-LIB: form the real value of `x`, round it to an integer `n` per `RM`, and
if `n` is representable in the target read, return it; otherwise the result is
**unspecified**. Probed against z3 on 2026-07-02 (7 probes, scratchpad):

- **Round FIRST, then range-check the rounded integer.** `fp.to_ubv 8 RNE
  -0.5` → rounds to `0` → in range → **specified** `#x00` (z3: distinct-from-0
  UNSAT). `fp.to_ubv 8 RTZ 255.5` → `255` → specified `#xFF`. `fp.to_ubv 8 RNE
  255.5` → `256` → out of range → **unspecified** (z3: `= a #x07` SAT).
- In-range: `n ∈ [0, 2^m−1]` (ubv), `n ∈ [−2^(m−1), 2^(m−1)−1]` (sbv). A
  negative FP value whose ROUNDED result is `0` is in range for ubv.
- Unspecified cases: `x` NaN, `x` ±∞, or `n` out of range.
- **The unspecified result is an uninterpreted function of `(RM, x)`** per
  face+signature, NOT a pinned constant and NOT a per-sort shared value:
  - unconstrained in value — `(= (fp.to_ubv RNE NaN) #x2A)` is SAT;
  - congruent — `x = y ∧ isNaN x ∧ distinct (to_ubv RNE x) (to_ubv RNE y)`
    is **UNSAT**;
  - free to differ across different inputs (`NaN` vs `+∞` results may be
    distinct: SAT) and across different modes (SAT).

Two encodings were rejected on these probes: **pinning a concrete value**
(e.g. IEEE-style saturation) makes `(= a #x2A)`-shaped scripts wrongly UNSAT;
**fresh value without congruence** makes the probe-2 shape wrongly SAT. Both
violate the soundness contract. The admitted encoding is **fresh result word +
congruence constraints** (§5).

Congruence trigger equality on `x` is SMT **value** equality: any-NaN equals
any-NaN regardless of payload bits. FP words in the blasted world are NOT
canonical-NaN-normalized (SMT `=` is blasted via the NaN-aware
`blast/compare.rs::core_eq`), so the trigger must reuse `core_eq`, not
bitwise equality.

## 3. Reference goldens (`crates/shinri-fp/src/reference.rs`)

- `round_rational_to_integer(q: &Rational, mode: RoundMode) -> Integer` — new
  small helper: exact integer rounding of a rational per the five modes (no FP
  format involved). RNE ties-to-even on the integer.
- `ref_to_ubv(eb, sb, m, bits, mode) -> Option<Integer>` and
  `ref_to_sbv(...) -> Option<Integer>`: decode → NaN/∞ → `None`; else
  `class_to_rational` → `round_rational_to_integer` → range check per face →
  `Some(n as m-bit pattern)` (two's complement for sbv) or `None`.

`None` means "unspecified": the circuit gate compares result bits only on
`Some`, and separately asserts the circuit's `ok` bit equals `is_some()`.

## 4. The gadget (`crates/shinri-fp/src/convert.rs`)

`fp_to_int(b, x, eb, sb, m, signed_face, rm) -> (Vec<BitLit> /* m bits */, BitLit /* ok */)`,
mirroring `to_fp_int`'s shape; `FpToUbv` calls with `signed_face = false`,
`FpToSbv` with `true` (blast-time constant).

1. **Decode** `x` via the existing operand decode (`blast/operand.rs`): sign,
   class flags (NaN/∞/zero), unbiased exponent `e`, significand with hidden
   bit (subnormals flow through the generic path — value < 1, rounds to 0/1).
2. **Magnitude datapath.** Value = `sig · 2^(e−(sb−1))`. Build the rounded
   integer magnitude in an `(m+1)`-bit register (the +1 catches rounding into
   `2^m`):
   - `e ≥ m` → out-of-range short-circuit (magnitude ≥ 2^m ≥ both faces'
     bounds); no shift needed.
   - `e ≥ sb−1` (and `< m`) → exact left shift by `e−(sb−1)`; GRS = 0.
   - `e < sb−1` (incl. all negative `e` and subnormals) → `shift_right_sticky`
     (`round.rs:185`) by the clamped amount `sb−1−e`, folding dropped bits
     into guard/round/sticky.
   - `rounding_increment` (`round.rs:162`, shared with `round()` and RTI) with
     the magnitude's lsb → +1 on the magnitude. Zero input needs no special
     mux: sig = 0 flows to magnitude 0, GRS = 0, ok.
   Exact register widths and the clamped-shift encoding are plan-level.
3. **Range check + sign application.**
   - ubv: `in_range = (mag ≤ 2^m − 1) ∧ (¬sign ∨ mag = 0)`; result = low `m`
     bits of `mag`.
   - sbv: `in_range = (¬sign ∧ mag ≤ 2^(m−1) − 1) ∨ (sign ∧ mag ≤ 2^(m−1))`;
     result = `mux(sign, −mag, mag)` in `m` bits (the negative bound admits
     INT_MIN exactly).
4. **ok / unspecified mux.** `ok = ¬NaN ∧ ¬∞ ∧ in_range`. Result word =
   per-bit `mux(ok, datapath, fresh)` where `fresh` = `m` × `Blaster::fresh()`
   (`blast/mod.rs:84`) — unconstrained. The gadget returns `(word, ok)`; the
   dispatch layer discards `ok` (it exists for the per-gadget gate, which
   asserts it against the golden's `is_some()`).

Circuit depth: one barrel shift + one increment + compares — `fp.add`-class,
none of the `fp.div` recursion-depth risk.

**Constants are not special-cased** (4c/4d decision carried forward).

## 5. Unspecified-value congruence (the new plumbing)

Per §2, distinct applications with equal `(RM, x)` must produce equal results.
Hash-consing makes syntactically identical terms share one word for free; the
constraint is only needed across **distinct TermIds** of the same signature.

- **Registry on the `Lowerer`** (`lower.rs`), exposed through a new `WordSink`
  accessor mirroring the `rm_cache()` precedent: a list of admitted FP→BV
  applications, keyed by `(face, m, eb, sb)`, each carrying the rm one-hot
  selectors, the operand word, and the result word.
- **Emission:** in the `blast_fp_word` arm, after blasting a new application,
  for each prior entry with the same key emit
  `(core_eq(x₁, x₂) ∧ rm₁ = rm₂) → result₁ = result₂` (bitwise over the full
  result word — when both are in-range the datapath already agrees, so the
  full-word form is correct and simpler than gating on the fresh branch).
  `rm` equality = pairwise equivalence of the 5 one-hot selector bits.
- O(k²) pairs in the number of FP→BV applications per formula — k is tiny in
  practice; no Ackermann-explosion mitigation needed at this scale.

Faces are independent functions: no constraints across `to_ubv`/`to_sbv`, nor
across different `m` or source formats (z3 probe 1 agrees).

## 6. Dispatch & fence lift

**Dispatch** — the reverse of 4c/4d, and the first BV-sorted FP-op:
- `Lowerer::word` (`lower.rs:35`) currently routes by sort alone; a BV-sorted
  `fp.to_ubv` would fall into `blast_bv_word` and hit its crossing
  `unreachable!` arm. Change: BV-sorted terms whose op is
  `FpToUbv`/`FpToSbv` route to `blast_fp_word` (the comment at lower.rs:41-43
  anticipates exactly this).
- `blast_fp_word` (`shinri-fp/src/lib.rs`) gains the two arms: blast RM via
  `blast_rm`, the FP operand via `sink.word` (FP-sorted → recurses through
  `blast_fp_word`), call `fp_to_int`, run the §5 congruence emission.

**Fence lift** (`crates/shinri-solver/src/fp_stage.rs`):
- `uses_crossing_conversion` (fp_stage.rs:68): remove `FpToUbv`/`FpToSbv` from
  the always-crossing set (line 77-78). Remaining crossing set — final for
  v1: `FpToReal` + symbolic-Real `ToFp`. The DAG-walk still nets a
  still-crossing op nested anywhere (e.g. `(fp.to_ubv rm ((_ to_fp 5 11) RNE
  r))` with symbolic Real `r` stays `Unknown`).
- `is_supported_fp_word`: add `FpToUbv`/`FpToSbv` arms — exactly 2 kids, a
  RoundingMode term + an FP-sorted operand, and **recursively support-check
  the FP operand** (unlike 4d's BV child: the FP blaster is NOT total over
  unfenced-but-unsupported shapes; the operand subtree is FP).
- **New fence surface — FP subterms under BV atoms.** Until 4e, BV atoms could
  never contain FP subterms (all crossings were fenced), so the support walk
  only visited FP atoms. Now `(bvult (fp.to_ubv rm x) c)` is legal: extend the
  support check to walk BV atoms too, applying `is_supported_fp_word` to any
  `FpToUbv`/`FpToSbv` subterm found there.
- Confirm `FpToUbv`/`FpToSbv` ∈ `is_fp_op` (fp_stage.rs:19) so
  `solver_uses_fp` routes a formula whose ONLY FP content is an FP→BV term
  into the FP stage at all; add if missing.
- Model read-back: the FP→BV term is not a variable; user BV/FP vars flow
  through the existing exported-bits path. No change expected — pinned by the
  get-model e2e.

## 7. Testing (the established slice pattern + the new unspecified dimension)

- **Per-gadget gate** (`convert.rs` tests): exhaustive — all 256 patterns of
  `(3,5)`, both faces, all five modes, `m ∈ {1, 4, 8}` (m=1 exercises the
  degenerate range `[0,1]` / `[−1,0]`), vs `ref_to_ubv`/`ref_to_sbv`:
  bit-exact on `Some`, and circuit `ok` ≡ `is_some()` on every pattern.
  Randomized `(5,11)` and Float32 into `m ∈ {8, 32, 64}`, seeded with ±0,
  ±min-subnormal, ±max-finite, ±∞, NaN, exact integers, halfway ties
  (x.5 patterns), and the range edges `2^m−1 ± ulp`, `±2^(m−1) ± ulp`.
- **Congruence unit pins** (spec-derived, per the standing lesson that
  circuit-vs-golden gates cannot see this dimension): the probe-2 shape
  (equal-forced NaN operands, distinct results → UNSAT), the probe-1 shape
  (NaN vs +∞ → SAT), the probe-3 shape (unspecified = 42 → SAT), and a
  payload-NaN pair (two different NaN bit-patterns, `= x y` holds at SMT
  level → results forced equal) to pin the `core_eq` trigger.
- **e2e (`fp_e2e.rs`)**: `Unknown → Sat` and `→ Unsat` flips for both faces;
  get-model read-back of the BV result var and the FP source var in one
  model; the probe-5/6/7 boundary trio as SAT/UNSAT pins; one mixed-atom
  script with `fp.to_ubv` nested under a BV atom.
- **Differential z3 oracle**: random QF_BVFP formulas over both faces from
  symbolic FP vars (naturally hitting NaN/∞/out-of-range), INCLUDING
  multi-application formulas — the §5 encoding matches z3's probed semantics,
  so zero disagreements is the bar, no generator restrictions.
- **Canary repoint** *(standing cross-slice lesson — pre-flight hunt BEFORE
  the fence edit)*: 4d repointed the crossing canaries AT
  `fp.to_ubv`/`fp.to_sbv` (fp_stage.rs ×3, fp_e2e.rs ×1); this slice flips
  them AGAIN. Repoint to `fp.to_real` / symbolic-Real `to_fp` — their FINAL
  resting place (both durably fenced for v1). Grep both files for the full
  set before touching the fence; then run the whole suites.
- **Regression is an oracle**: full `cargo test --workspace` green; pure-BV
  and prior-FP verdicts byte-identical. Multi-minute FP/SAT gates run in
  background in-session (not via subagents).

## 8. Risks

- **Congruence plumbing is new cross-cutting state** — the first constraints
  emitted ACROSS separate `word()` calls. Risk: a missed pair (wrong SAT) or
  an over-strong trigger (wrong UNSAT). Mitigation: the four spec-derived
  congruence pins + multi-application z3 differential.
- **First FP-op-under-BV-atom** — a support-fence gap could let an
  unsupported FP shape reach the blaster via a BV atom. Mitigation: the §6
  BV-atom support walk + a nested-crossing canary
  (`fp.to_ubv` over symbolic-Real `to_fp` stays `Unknown`).
- **Range/width off-by-ones** at the edges (rounding into `2^m`, sbv INT_MIN,
  m=1). Mitigation: the `(m+1)`-bit magnitude register pinned in §4 and the
  exhaustive small gate with `m ∈ {1, 4, 8}` + seeded edge vectors.
- **Cross-slice canary breakage** — the standing lesson; front-loaded hunt +
  full-workspace net.

## 9. Decisions locked for slice 4e

| Decision | Choice |
|---|---|
| Faces admitted | Both — `FpToUbv` + `FpToSbv`, one slice (4d precedent); closes Plan 4 |
| Unspecified semantics | Fresh result word + `(RM, x)`-congruence per `(face, m, eb, sb)` — matches z3-probed UF semantics; pinning and no-congruence both rejected as unsound |
| Congruence trigger | `core_eq` on the FP operand (value equality, any-NaN = any-NaN) ∧ one-hot rm equality → full-result-word equality |
| Congruence home | Registry on `Lowerer`, new `WordSink` accessor (rm_cache precedent), emitted in the `blast_fp_word` arm |
| Gadget | One `fp_to_int` with blast-time `signed_face` flag → `(word, ok)`; decode → clamped shift + GRS → shared `rounding_increment` → range check → ok-mux |
| Range semantics | Round FIRST, then range-check the rounded integer (z3 probes 5–7) |
| Reference | `ref_to_ubv`/`ref_to_sbv` → `Option<Integer>` over new `round_rational_to_integer`; `None` = unspecified |
| Dispatch | `Lowerer::word` routes BV-sorted `FpToUbv`/`FpToSbv` to `blast_fp_word` |
| FP-operand support | Recursive `is_supported_fp_word` check (FP blaster not total — unlike 4d's BV child) + new BV-atom support walk |
| Constant folding | None — folds through constant bit-lits (4c/4d decision) |
| Success criterion | Byte-identical existing verdicts + `fp.to_real`/symbolic-Real canaries still `Unknown` + both faces solve, congruence pins hold, z3 zero disagreements |
| Next | Plan 4 complete. Remaining fence = the permanent Real bridge; QF_FP/QF_BVFP v1 op coverage done |
