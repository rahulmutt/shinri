# shinri QF_FP slice 9 — the Real-bridge seam (`fp.to_real`)

**Date:** 2026-07-04
**Status:** Implemented (slice 9 landed). `fp.to_real` over Float16/32 (eb≤8) is
admitted and solved jointly with the resulting Real in the Combiner — mixed with
LRA **and EUF (QF_UFLRA + bridge)** — via constant + symbolic guarded-linear arms
+ NaN/±∞ functionality (three distinct per-format consts); symbolic `to_fp` and
`fp.to_real` over eb≥11 stay soundly fenced to `Unknown`. The §0 scope calls
(mechanism A, `fp.to_real`-only, Float16/32) were carried through as designed.
z3 differential: 200 constant-source finite/functionality cases + 200
QF_UFLRA-mixed cases (`differential_qf_fp_to_real_uflra`), 0 disagreements,
0 Unknown; full `cargo test --workspace` green. **FOLLOW-UP (closed by slice
10):** the Real-sorted recognizer admits Array-Real bridge operands but the
combined solve does not decide Real-valued arrays (sound Unknown), and Str-Real
EUF operands are fenced upstream by the string stage — the original
"structurally the same as the validated EUF path" assumption did not hold
end-to-end. Slice 10 pinned these fences (fp_e2e canaries) and added
unknown-tolerant z3 differential families (differential_qf_fp_to_real_array
/_str), and separately found+fixed a pre-existing non-string-path wrong-SAT for
ite over Int/Real/uninterpreted/Array sorts (see the slice-10 design doc).
**Scope:** First face of the permanent FP↔Reals bridge. Admit `fp.to_real` over
Float16/32, solved jointly with LRA in one solve, by establishing an
**eager-blast ⋈ lazy-LRA coexistence seam** that later bridge faces reuse.

---

## 0. Best-judgment calls pending user confirmation

The user selected **direction = Symbolic-Real bridge**, **slice-1 scope = thin
vertical seam**, then stepped away before confirming the mechanism. The
following were chosen on best judgment and are all trivially reversible at the
design stage:

1. **Mechanism = A (eager guarded-linear reduction, single combined solve).**
   Alternatives B (lazy CEGAR refinement) and C (FP as a first-class Combiner
   theory) are documented in §9 as the roadmap. A is recommended because it is
   sound **and** complete with the least new conceptual surface, and Float16
   keeps the exponent case-split trivially small (32 patterns).
2. **Direction = `fp.to_real` only.** Symbolic `to_fp(rm, real)` is deferred to a
   later face — it needs rounding-interval reasoning (the FP result is the value
   whose real interval contains `r` under the rounding mode), strictly harder
   than `to_real`'s exact-value equalities.
3. **Format scope = Float16/Float32 only** (`eb ≤ 8`). `fp.to_real` on
   Float64/128 (`eb ≥ 11`) stays **soundly fenced to `Unknown`**, to bound the
   `2^eb` eager case-split blow-up until the lazy path (B) exists.

If the user prefers a different mechanism, direction, or format line, this design
is re-scoped before any plan is written.

---

## 1. Goal & non-goals

**Goal.** Turn `fp.to_real(x)` from an unconditional `Unknown` fence into a
decided verdict for Float16/32, by letting the eagerly bit-blasted FP value and
the lazy LRA Real that names its exact value be solved in **one** solver. The
real deliverable is the **architecture seam** (blast into the Combiner's SAT
core + emit bridge rows as Arith atoms guarded by blasted bits) — every later
Real-bridge face reuses it.

**In scope (v1 of the bridge):**
- `fp.to_real(x)` where `x` is a Float16 or Float32 term, freely mixed with LRA
  constraints on the resulting Real (and with the existing eager FP/BV ops).
- Exact-finite semantics (normal/subnormal/zero) **and** the unspecified-but-
  functional NaN/±∞ semantics (§5).
- `(get-value)`/`(get-model)` over the bridged Real (it is an Arith model var —
  reuses the existing arith model channel).

**Deliberate non-goals (this slice):**
- **Symbolic `to_fp(rm, real)`** — stays fenced (§0.2, §9).
- **`fp.to_real` on Float64/128** — stays fenced (§0.3).
- **B (lazy CEGAR) and C (FP-as-theory)** — documented roadmap only (§9).
- No change to constant-Real `to_fp` (still folds via `reference.rs`), and no
  change to any purely-eager FP/BV path.

**Soundness contract (unchanged project invariant):** anything out of scope
returns `Unknown`, never a wrong SAT/UNSAT.

---

## 2.0 Pre-flight corrections (source-verified 2026-07-04, before planning)

A source pre-flight (per `shinri-spec-assumed-paths-semantic-preflight`) revised
the mechanism below — §2/§3 as originally written **overstated** the work:

- **The combined solver already exists.** `check_sat` builds
  `Sat = Solver::with_theory(cfg, Combiner::with_context(ctx.clone()))` and
  replays the BV/FP CNF into *that* (lib.rs ~481–533). The Combiner (with Arith)
  is present in every FP solve; it is simply never *fed* arith atoms because the
  query fences first. So there is **no "merge blast into the Combiner" work** —
  the seam is purely **additive**: mint arith vars/atoms and guard clauses.
- **The bridge Real is the `(fp.to_real x)` term itself.** `normalize_atom`
  treats an opaque Real leaf (like `str.len`) as a `problem_var`, so
  `(fp.to_real x)` becomes its own arith variable with no new symbol.
- **Arith has no guarded-row facility** — atoms are gated purely by the SAT
  layer. A bridge row is therefore a normal `Le`/`Ge` atom (registered via
  `Encoder::atom` → `Combiner::register_atom` → `Arith::new_var`) plus a raw
  **guard clause** `sat.add_clause([¬guard_bit_lits…, atom_lit])`, where the
  guard bits are the blasted FP bits in `fp_var_bits: FxHashMap<TermId,
  Vec<Var>>` (LSB→MSB: sig `[0..sb-1]`, exp `[sb-1..sb-1+eb]`, sign `[eb+sb-1]`).
- **Ordering constraint.** All bridge TermIds must be minted in `self.ctx`
  **before** the `ctx.clone()` into the Combiner (else out-of-range for
  `classify`/`normalize`); the guard *clauses* are added later, after replay
  populates `fp_var_bits`. This two-phase split structures the tasks.
- **TWO fences to narrow, not one:** `uses_crossing_conversion` (fp_stage.rs:88,
  `FpToReal => true`) **and** `has_non_bvfp_theory_atom` (fp_stage.rs:140–184,
  which fences the `(> (fp.to_real x) 1.5)` Real atom). The recognizer admits
  pure-LRA-Real atoms only in the bridge-admissible case.
- **Special-constant soundness sharpened.** The three NaN/±∞ constants must be
  **distinct** unconstrained vars: a single shared const would force
  `to_real(+∞) = to_real(−∞)` — a wrong-**UNSAT** (both are independently
  unspecified). Same-class→same-const still gives functionality (no wrong-SAT).
- **Channel vars must be Real** (0/1-valued Reals), not Int — an Int channel var
  beside the Real bridge var trips the `lira` gate (`saw_int_arith &&
  saw_real_arith` → Unknown, lib.rs:603/606).
- **No parser work** — `(fp.to_real x)` and `(> (fp.to_real x) 1.5)` already
  parse and sort-check to Real.

## 2. Why this is the hard slice — the dispatch wall

`shinri-solver::check_sat` dispatches a query to **exactly one** engine:

- the **eager blast path** (BV / FP / QF_BVFP + Boolean structure), replayed
  into a `NoTheory` SAT solver; or
- the **lazy Combiner path** (`Solver<Combiner<Euf, Arith, Arrays, Str>>`),
  Nelson–Oppen over a shared equality engine + interface set.

They never run in the same solve. `fp.to_real` (and symbolic `to_fp`) is caught
by `fp_stage::uses_crossing_conversion` and fenced to `Unknown` **before** any
lowering (`lib.rs` ~L406–413), and `has_non_bvfp_theory_atom` fences any FP
query that also carries a non-BVFP theory atom. The bridge is hard precisely
because its value — a Real — lives in the lazy LRA simplex, while the FP value is
a slice of blasted bits in the SAT core, and today those two engines are on
opposite sides of a mutually-exclusive branch.

Confirmed enabling facts:
- `shinri-fp::reference::class_to_rational` already pins the exact value:
  finite → `(−1)^sign · significand · 2^(exp − bias − (sb−1))`; NaN/∞ → `None`.
- `shinri-arith` is mixed Int/Real (`vars::problem_var_sorted(_, is_int)`,
  `DeltaRational`, integer branch-and-bound) — a significand-integer / bit→{0,1}
  encoding is representable.
- The blaster writes through a minimal `BvSink` (`new_var`/`add_clause`);
  `Solver<Combiner<…>>` is a SAT solver, so the sink is implementable over it.

---

## 3. Approach A — eager guarded-linear reduction, single combined solve

**Dispatch.** Add a `check_sat` branch for the shape *"FP query whose only
crossing is `fp.to_real` over an admitted format, mixed with LRA"*:

1. Recognize it: `uses_fp` ∧ the only crossing conversion is `fp.to_real`
   (no symbolic `to_fp`), every `fp.to_real` operand is Float16/32, and the
   remaining non-BVFP atoms are LRA-only (Arith). Anything else → keep fencing.
2. Blast FP (and any BV) into a `Solver<Combiner<…>>` via a `BvSink` adapter
   over that solver (reuse the `replay_bv_cnf` sink abstraction).
3. For each `fp.to_real(x)` term, allocate the bridge Real `r_x` as an Arith
   problem var and emit the guarded-linear rows (§4) as Arith assertions whose
   guards are blasted bits.
4. Any user LRA atoms over `r_x` route to Arith the normal way.
5. Solve the combined problem; on SAT, `r_x` reads out of the arith model.

**Why not keep FP in its own SAT solver and exchange values?** The bridge rows
must be **guarded by the blasted exponent/sign bits** — those guards have to be
literals in the *same* SAT core that hosts the Arith atoms. Sharing the core is
therefore necessary, and proving that coexistence works is the point of the
slice.

---

## 4. The bridge encoding (format-generic; exact per `class_to_rational`)

Let `x` have format `(eb, sb)`, `bias = 2^(eb−1) − 1`. Blasted fields: `sign`
(1 bit), `expf` (eb bits, value `e`), `sigf` (sb−1 bits). Introduce **bit→{0,1}
channel reals** `b_0..b_{sb−2}` for the significand, each tied to its blasted
literal `ℓ_i` by two guarded unit facts: `ℓ_i ⟹ b_i = 1` and `¬ℓ_i ⟹ b_i = 0`.
Write `SIG = Σ_i 2^i · b_i` (a linear term; the significand's integer value as a
real). The channel reals are **shared across all exponent guards** of `x`.

For each biased-exponent pattern `e ∈ 0..2^eb−1` and each `sign ∈ {0,1}`, emit
one guarded row. `guard(sign, e)` is the conjunction (a Tseitin aux literal) of
the sign bit = `sign` and the `eb` exponent bits matching `e`.

- **Normal** (`1 ≤ e ≤ 2^eb−2`), with `const_e = 2^(e − bias − (sb−1))` (a fixed
  rational):
  `guard(sign,e) ⟹ r_x = (−1)^sign · const_e · (2^(sb−1) + SIG)`
- **Subnormal / zero** (`e = 0`), with `sub = 2^(1 − bias − (sb−1))`:
  `guard(sign,0) ⟹ r_x = (−1)^sign · sub · SIG`
  (SIG = 0 gives `r_x = 0`, covering ±zero.)
- **NaN / ±∞** (`e = 2^eb−1`): point `r_x` at a **shared per-format unspecified
  constant** — see §5:
  - `guard(0, all-ones) ∧ SIG = 0 ⟹ r_x = POS_INF_c`
  - `guard(1, all-ones) ∧ SIG = 0 ⟹ r_x = NEG_INF_c`
  - `guard(_, all-ones) ∧ SIG ≠ 0 ⟹ r_x = NAN_c`

Every row is linear (the `const`/`sub`/`(−1)^sign` are constants once `e` and
`sign` are fixed by the guard). For **Float16** (`eb=5, sb=11`): 2 signs × 32
exponent patterns ≈ 62 rows + 10 channel reals + their 20 unit facts. Float32
(`eb=8`) ≈ 510 rows — still modest. The encoding is exactly `class_to_rational`,
so it is **sound and complete** to the extent SMT-LIB specifies `fp.to_real`.

---

## 5. Key soundness obligation — functionality over NaN/±∞

SMT-LIB leaves `fp.to_real` **unspecified** on NaN and ±∞, but it is still a
**function**: equal FP values must map to equal reals. If each `fp.to_real(NaN)`
were left independently unconstrained, the solver would accept
`x = y ∧ fp.to_real(x) ≠ fp.to_real(y)` — a **wrong SAT**. (The theory has a
single NaN value: `reference::ref_core_eq` treats `NaN == NaN`.)

This is the mutually-consistent-bug / wrong-SAT shape the project memory warns
about, and it is invisible to circuit-vs-golden gates. The encoding closes it by
tying the NaN/±∞ cases to **three shared per-format unconstrained constants**
(`POS_INF_c`, `NEG_INF_c`, `NAN_c` — fresh Arith vars, one triple per admitted
format, reused by *every* `fp.to_real` term of that format). Result: distinct
`fp.to_real` applications on equal FP values agree (functional), the value stays
unspecified (unconstrained), and no wrong SAT is possible.

- `POS_INF_c ≠ NEG_INF_c` is **not** required for soundness (both unspecified);
  leaving them independent is fine and simpler. Sharing per class per format is
  what matters.
- This obligation gets a dedicated **constant-source z3 differential** pin
  (§7) — the only gate that can catch it.

---

## 6. Scope fence — what stays `Unknown` (and stays sound)

The existing `uses_crossing_conversion` fence narrows, it does not vanish.
**Implemented (slice 9):** `fp.to_real` over Float16/32 (`eb ≤ 8`) is now
*admitted* (no longer crossing) and decided via the Real bridge. What still
stays `Unknown`:

- **Symbolic `to_fp(rm, real)`** — still crossing → `Unknown`.
- **`fp.to_real` on Float64/128** (`eb ≥ 11`) — still crossing → `Unknown`
  (bounds the `2^eb` blow-up; lifted by B or a smarter encoding later).

**Broadened scope (shipped):** `fp.to_real` (`eb ≤ 8`) is admitted mixed with
LRA **and with EUF over the resulting Real (QF_UFLRA + bridge)** — e.g.
`(= (fp.to_real x) (f a))` with `f: Real → Real`. The admissibility recognizer
`is_lra_real_atom` requires only that relation operands be **Real-sorted**; an
EUF application `(f a)`, an array `(select arr i)`, or a Str-Real term over Real
routes to the Combiner alongside Arith. Soundness rests on the Combiner's
**Nelson–Oppen EUF⋈Arith** combination deciding the shared-Real interface, and
is validated empirically by the `differential_qf_fp_to_real_uflra` z3 oracle
(`tests/fp_oracle.rs`): 200 decidable EUF+bridge cases + a NaN/EUF functionality
pin, **0 disagreements, 0 Unknown**.

- **EUF-over-Real coverage only.** The Real-sorted recognizer also admits
  **Array-over-Real** (`(select arr i)`) and **Str-Real** operands mixed with
  the bridge, but the `differential_qf_fp_to_real_uflra` oracle exercises only
  the EUF case (decidable Array/Str-Real bridge queries are harder to
  generate). **FOLLOW-UP: add Array/Str+bridge differential coverage.**
- **FP mixed with a genuinely non-Real-routed theory** (e.g. BV/Int-only lazy
  atoms) alongside the bridge remains out of the bridge's admitted scope.

Each remaining fence degrades to sound `Unknown`; none can flip a real
Sat↔Unsat. The broadened EUF⋈bridge scope is empirically z3-differentially
validated rather than fenced.

---

## 7. Testing

Following the project's soundness-first gate discipline:

1. **Exact-rational oracle.** Reuse `class_to_rational` as golden; assert the
   blasted+bridged model's `r_x` equals it for finite inputs across the F16/F32
   value classes (normal / subnormal / ±zero boundaries).
2. **Constant-source z3 differential.** *Decidable-verdict* scripts (not
   free-variable relations) — these are the only gate that catches
   mutually-consistent bugs (memory: `shinri-spec-assumed-paths-semantic-
   preflight`). Must include the §5 functionality pins:
   `x = y (both NaN) ∧ to_real(x) ≠ to_real(y)` ⟹ **UNSAT**; and finite pins
   like `to_real((fp …)) = <exact literal>`.
3. **e2e SAT/UNSAT pins** for F16/F32 mixing `fp.to_real` with LRA
   (e.g. `fp.to_real(x) > 1.5 ∧ fp.isNormal(x)` SAT with a witness; a
   contradiction UNSAT).
4. **Repointed fence canaries** (§8) assert the new verdicts.
5. **Full `cargo test --workspace`** as the closeout net for stale canaries in
   other crates (memory: `shinri-fence-canary-cross-slice`).

---

## 8. Cross-slice canary repoints (pre-flight already surfaced these)

Admitting `fp.to_real` flips existing assertions that pin it as crossing /
`Unknown`. Per the slice-4c idiom, **each repoint lands in the same task** that
lifts the fence (same file/fn), not at closeout:

- `crates/shinri-solver/src/fp_stage.rs:656–659` — `"fp.to_real still crossing"`:
  flip for the **admitted-format** face; keep asserting **crossing** for
  Float64/128 and for symbolic `to_fp` (the durable fence).
- `fp_stage.rs:836–838` — `"fp.to_real stays fenced"`: same split by format.
- `fp_stage.rs:824` `fp_to_bv_faces_admitted_real_bridge_still_crossing` and the
  `to_fp_faces_*` tests — re-express as "admitted for F16/F32 `fp.to_real`,
  still crossing for the deferred faces".
- Hunt e2e pins asserting *mixed FP+LRA → Unknown* or *`fp.to_real` → Unknown*
  and flip the F16/F32 ones (rename `*_is_unknown` → `*_solves_after_bridge`).

Pre-flight obligation (memory `shinri-fence-canary-cross-slice`): before
execution, `grep -rn` the whole workspace for any test pinning the old
crossing/Unknown classification of `fp.to_real`, and fold each into the
fence-lifting task.

---

## 9. Roadmap (documented, not built this slice)

- **Larger formats via B (lazy CEGAR refinement).** For Float64/128 the eager
  `2^eb` case-split is large; a model-driven definitional-lemma loop
  (read `x`'s bits from a candidate model → add a guarded exact-value lemma →
  re-solve) scales without the up-front blow-up. Built on top of this slice's
  seam.
- **Symbolic `to_fp(rm, real)`.** The next face: `y = to_fp(rm, r)` constrains
  the FP value `y` to `round_rm(r)` — rounding-interval rows per exponent
  (`r ∈ [lo_y, hi_y)` under the mode's tie rule), reusing `reference::
  round_rational` semantics.
- **C — FP as a first-class Combiner theory (north-star).** FP stops being a
  pure lowering stage and becomes a Nelson–Oppen `TheorySolver` exchanging
  equalities over shared interface Reals (internally still blasting). This
  eventually subsumes the §3 ad-hoc combined-dispatch branch; the seam built
  here is the incremental stepping stone toward it.

---

## 10. Risks

- **Integration surprise at the seam.** Merging the blaster into the Combiner's
  SAT core is new plumbing; expect an unplanned cross-cutting fix (cf. the
  slice-2c deep-circuit stack-overflow that the plan didn't anticipate). The
  thin vertical + full-workspace regression is the mitigation.
- **NaN/∞ functionality (§5)** — the one wrong-SAT trap; owned by a dedicated
  z3 pin.
- **Model channel for `r_x`.** `get-value` over the bridge Real must read the
  arith model, not the blast model — verify the combined-solve model path
  surfaces both.
