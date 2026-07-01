# shinri QF_FP — Slice 4b: Mixed BV+FP Fence-Lift Design

**Date:** 2026-07-01
**Status:** Landed 2026-07-01 — mixed BV+FP fence lifted; crossing conversions still fenced.
**Parent:** `2026-06-24-shinri-qffp-design.md` (Plan 4, "QF_BVFP unification")
**Predecessor:** `2026-07-01-shinri-qffp-slice4a-bvfp-unification-design.md` (slice 4a landed)

## 1. Goal & Scope

Slice 4a unified BV and FP bit-blasting onto **one** shared `Blaster` + `WordSink`
+ `Lowerer` driver, but kept the mixed BV+FP fence **closed**: the solver still
runs BV and FP as two mutually-exclusive `Option<Lowered>` blocks, and any query
mixing the two theories returns `Unknown`.

Slice 4b lands the **fence-lift only**: a query whose atoms are pure-BV and/or
pure-FP — with **no** BV↔FP crossing conversion — is lowered as **one** problem
through the 4a `Lowerer` and gets a real SAT/UNSAT verdict instead of `Unknown`.

**Zero new blasting gadgets.** This is the plumbing counterpart to 4a: it lifts a
fence that 4a's unified substrate already made safe to lift. It authors no
int↔float datapath and admits no conversion op.

**Explicitly still fenced (→ later slices, one conversion each):** the four
crossing conversions — 1-arg BV bitcast `to_fp`, signed-BV→FP `to_fp`,
`to_fp_unsigned` (unsigned-BV→FP), and `fp.to_ubv`/`fp.to_sbv` (FP→BV) — plus
`FpFromBits`. The permanent v1 non-goals are unchanged: `fp.to_real` and `to_fp`
from a *symbolic/variable* Real (both need an FP↔Reals combination).

## 2. Why this is safe — the disjointness invariant

The key soundness fact that makes a pure fence-lift correct:

> **Without a crossing conversion op, BV terms and FP terms are completely
> disjoint DAGs.** Every term has exactly one sort; `ite` and `=`/`distinct`
> branches must be same-sort; so a BV subterm and an FP subterm can meet **only**
> at the Boolean level (as two atoms combined by Boolean structure).

A mixed non-crossing query is therefore just **two independent bit-blasting
problems that share one `Blaster` variable namespace and one SAT instance**.
There is no shared bit word, no cross-theory constraint, nothing to blast that
4a's substrate cannot already blast. Consequently:

- **Detecting the crossing-op set is both necessary and sufficient** to preserve
  soundness. Fence exactly the crossing conversions and the symbolic-Real bridge;
  everything else in the BV+FP union is safe to lower.
- The two theories interact through the Boolean skeleton only, which the SAT
  layer already handles for single-theory queries.

## 3. Success criterion

1. **Every existing BV and FP verdict is byte-identical.** Full workspace
   `cargo test` stays green (98 `shinri-bv`, 26 `qfbv_witnesses`, the `shinri-fp`
   exhaustive gate, `fp_e2e`, and — feature-gated — `fp_oracle`).
2. **The crossing canaries still fence.** The 5-form array
   `to_fp_bv_crossing_and_symbolic_real_are_unknown` (`fp_e2e.rs`) stays all
   `Unknown` — 4b admits no crossing op.
3. **Mixed non-crossing now solves.** A formula like
   `(and (bvult x y) (fp.lt a b))` returns Sat/Unsat, agrees with z3, and its
   model reads back both a BV value and an FP value.

## 4. Architecture

### 4.1 The dispatch restructure (`shinri-solver/src/lib.rs`)

Today (`lib.rs:355-400`) there are two mutually-exclusive `Option<Lowered>`
blocks. The BV block fences if any FP is present (`|| solver_uses_fp`, `:367`);
the FP block runs only if `lowered_bv.is_none()` and fences if any non-FP atom is
present (`has_non_fp_theory_atom`, `:390`). New control flow:

```
collect bv_atoms and fp_atoms
if uses_crossing_conversion(ctx, assertions)          → Unknown   (fence, §4.2)
else if any Bool atom ∉ (bv_atoms ∪ fp_atoms)         → Unknown   (other theory: arrays/LIA/EUF)
else if uses_fp:  lower (fp_atoms ∪ bv_atoms) via the Lowerer     ← pure-FP (empty BV set) AND mixed
else if uses_bv:  shinri_bv::lower(bv_atoms)                      ← pure-BV, unchanged path
else:             (pure Boolean / existing handling)
```

- **Pure-FP** is unchanged: `bv_atoms` is empty, so the union equals today's
  `fp_atoms`, lowered by the same `Lowerer` (4a Task 4).
- **Pure-BV** is unchanged: it keeps `shinri_bv::lower` on its own `Blaster`
  path — byte-identical, zero numbering risk on the BV corpus (the deliberate
  "minimal entry-unification" decision; folding pure-BV into the `Lowerer` is a
  later cleanup, not this slice).
- **Mixed** is the only new behavior: the FP-involving branch now lowers
  `fp_atoms ∪ bv_atoms` instead of fencing on the presence of BV atoms.

The FP lowering entry (`shinri_fp::lower`) gains a `bv_atoms` parameter (or a
sibling `lower_mixed(ctx, fp_atoms, bv_atoms)`), so the `Lowerer` blasts both
atom sets through its existing sort-dispatching `Lowerer::atom` (BV-sorted first
operand → `blast_bv_atom`, else `blast_fp_atom`). No `Lowerer` internals change —
4a already made both `blast_bv_*` and `blast_fp_*` generic over `WordSink`, which
`Lowerer` implements.

### 4.2 The fence, redefined

Replace the two scattered guards ("FP present ⇒ Unknown in the BV block";
"non-FP atom ⇒ Unknown in the FP block") with **one** predicate:

```rust
fn uses_crossing_conversion(ctx: &Context, assertions: &[TermId]) -> bool
```

a DAG walk (memoized over `TermId`) that flags any use of the crossing/unsupported
conversion set:

- `FpFromBits`
- `FpToUbv(_)`, `FpToSbv(_)` — FP→BV
- `ToFpUnsigned { .. }` — unsigned-BV→FP
- `ToFp { .. }` in its **BV-source**, **1-arg-bitcast**, or **symbolic-Real**
  faces (i.e. exactly the faces `is_supported_fp_word` rejects today) — but
  **not** the 3a-supported FP→FP and constant-Real faces.
- `FpToReal`

**Why one predicate.** It is exhaustively verifiable in one place; it gives the
*next* slice one obvious spot to delete an entry as each conversion is admitted;
and it removes the fragile reliance on block ordering. In particular the FP→BV
ops (`fp.to_ubv/sbv`) are BV-sorted, so `collect_bv_atoms` would otherwise treat
them as pure-BV leaves and drive `blast_bv_word` into its `unreachable!`
(`blast/mod.rs:410`) — the crossing predicate is exactly what stops that before
lowering. With this predicate owning the fence, the positive-enumeration helper
`fp_atoms_fully_supported` / `is_supported_fp_word` can be simplified or retired.

The separate "other theory" guard (arrays/LIA/EUF) is retained but **generalized**
from the two single-theory predicates to one union test: a Boolean atom that is
neither in `bv_atoms` nor `fp_atoms` (and is not pure Boolean structure) still
fences to `Unknown`. This is the `has_non_fp_theory_atom` inversion called out in
§6 — we widen the allowed set to the union rather than deleting the guard.

### 4.3 Model read-back (the one non-mechanical spot)

The solver keeps two decode maps — `bv_var_bits` (`lib.rs:66`) and `fp_var_bits`
(`:69`) — filled today from two mutually-exclusive `Lowered`s and read by two
separate loops (BV width `:547`; FP `eb+sb` `:560`).

The mixed path produces **one** `shinri_bv::Lowered` (one CNF, one `atom_lit`
spanning both theories' atoms, one `var_bits`) and registers it **once** via the
existing `register_surrogate` (`:689`). The only new wiring:

- The mixed lower returns `var_bits = bv_vars ∪ fp_vars`, both obtained from 4a's
  `Lowerer::var_bits_split(ctx)` (already RM-filtered).
- The FP/mixed registration block (`:435-444`) **splits that union by sort**:
  entries where `ctx.bv_width(sort).is_some()` populate `bv_var_bits`; entries
  where `ctx.fp_widths(sort).is_some()` populate `fp_var_bits`.
- The two decode loops (`:547`, `:560`) are unchanged.

Pure-FP stays byte-identical: its union is FP-only, so `bv_var_bits` stays empty
exactly as today. No change to the `Lowered` type and no new struct — the split
lives where `ctx` is already in hand. (A cleaner-but-more-invasive alternative —
returning both maps from the lowering entry — is rejected for a fence-lift slice.)

## 5. Validation

- **Regression is an oracle.** Full workspace green; all pure-BV and pure-FP
  verdicts byte-identical. Assert `num_vars` parity on a representative pure-FP
  atom to catch any visit-order drift.
- **Crossing canaries hold.** The 5-form array in `fp_e2e.rs` stays all
  `Unknown`. Per the standing cross-slice lesson, run the **whole** `fp_e2e`
  suite and `grep`-audit the crossing canaries — 4b admits nothing new.
- **New positive canaries (`fp_e2e.rs`).** At least one mixed non-crossing script
  flips `Unknown → Sat` and one `→ Unsat`; `get-model` read-back is checked on
  both a BV var and an FP var in the same model (e.g.
  `(and (= x #b0011) (fp.eq a (fp #b0 #b0111 #b000)))`).
- **New differential oracle (`fp_oracle.rs`).** A `gen_mixed_script` emitting a BV
  predicate ∧ an FP predicate over independently-declared BV and FP vars, wired
  into a `#[test]` mirroring `differential_qf_fp_add_sub`. `z3_outcome_arith`
  already forwards `(declare-fun …)`/`(assert …)` lines verbatim, so declaring
  both a BV var and an FP var needs no harness change. Skip on shinri `Unknown`;
  `panic!` on a true Sat/Unsat disagreement.

## 6. Risks

- **Over-lifting the fence.** If `uses_crossing_conversion` misses a crossing
  face, a crossing query reaches `blast_bv_word`/`blast_fp_word`'s `unreachable!`
  → panic (a crash, not unsoundness). Mitigation: the predicate is the single
  source of truth, the canary array exercises all five faces, and the
  `unreachable!` arms stay as a backstop.
- **Var-numbering drift on pure paths.** Pure-BV is untouched (separate entry).
  Pure-FP: the union is FP-only and visit order is unchanged, so numbering is
  preserved — asserted via `num_vars` parity.
- **`has_non_fp_theory_atom` inversion.** That guard currently fences on BV
  atoms; 4b must stop it fencing the BV+FP union while **still** fencing genuine
  third theories (arrays/LIA/EUF). Mitigation: generalize to "atom ∉
  (`bv_atoms` ∪ `fp_atoms`) ⇒ `Unknown`", not delete.

## 7. Decisions locked for slice 4b

| Decision | Choice |
|---|---|
| Slice scope | Fence-lift only — mixed pure-BV+pure-FP solves; **zero new gadgets** |
| Crossing ops | **None admitted** — still fenced; each its own later slice |
| Entry unification | Minimal — FP path lowers `fp_atoms ∪ bv_atoms`; pure-BV path untouched |
| Fence shape | One `uses_crossing_conversion` DAG walk; generalize the non-theory guard to the BV+FP union |
| Model read-back | Reuse `var_bits_split`; split the one mixed `Lowered.var_bits` by sort into the two decode maps |
| Legacy `shinri_bv::lower` | Unchanged (own `Blaster` path); full fold into the `Lowerer` deferred |
| Success criterion | Byte-identical existing verdicts + crossing canaries still `Unknown` + mixed solves & agrees with z3 |
| Next slices | Admit the crossing conversions one at a time (bitcast first — pure wiring), each with its own gadget + `reference.rs` model + `fp_oracle` corpus + canary repoint |
