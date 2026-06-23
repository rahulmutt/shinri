# shinri QF_BV — Bitvector Theory Design

**Date:** 2026-06-23
**Status:** Approved design, pre-implementation
**Scope:** Full QF_BV (SMT-LIB `FixedSizeBitVectors` logic), standalone, eager bit-blasting with a word-level rewrite front-end.

## 1. Goal & Scope

Add support for the SMT-LIB QF_BV logic to shinri: fixed-width bitvector
constants, the full operator set, and `(get-model)`/`(get-value)` over BV terms.

**In scope (v1):**
- Full QF_BV operator coverage: `concat`, `extract`, all bitwise
  (`bvnot/bvand/bvor/bvxor/bvnand/bvnor/bvxnor`), `bvadd/bvsub/bvneg/bvmul`,
  the divider family (`bvudiv/bvurem/bvsdiv/bvsrem/bvsmod`), shifts
  (`bvshl/bvlshr/bvashr`), rotates (`rotate_left/rotate_right`),
  `zero_extend/sign_extend`, `repeat`, equality, and all unsigned + signed
  comparisons (`bvult/bvule/bvugt/bvuge/bvslt/bvsle/bvsgt/bvsge`).
- A word-level rewrite/simplify pass ahead of bit-blasting.
- Model extraction for BV constants.

**Deliberate non-goals (v1):**
- **Persistent incremental bit-blasting.** Each `check-sat` re-blasts the
  current assertion stack from scratch.
- **Theory combination.** No QF_UFBV / QF_ABV / BV+arith. A query mixing BV with
  EUF/Array/Arith is refused as `unknown` (consistent with the existing
  `Unsupported` discipline in `shinri-theory::atom`). Combination is a later,
  separate design.

**Soundness contract:** anything out of scope returns `unknown`, never a wrong
SAT/UNSAT verdict.

## 2. Approach

**Hybrid: word-level rewriting, then eager bit-blasting of the residual.**

BV is architecturally distinct from shinri's existing theories. EUF/Arith/Arrays
are *lazy* CDCL(T) solvers that share an equality engine through the `Combiner`
and the `TheorySolver` seam. Bit-blasting is *eager*: BV terms lower directly to
Boolean clauses for the CDCL SAT core, much like a richer Tseitin pass.

Therefore **BV does not implement `TheorySolver` and never reaches the
`Combiner`.** It is a lowering stage the `Solver` runs before its existing
Tseitin/SAT step.

## 3. Architecture & Pipeline Placement

```
parse → assertions (term DAG, may contain BV)
          │
          ▼   shinri-bv
   ┌──────────────────────────────────────────┐
   │ 1. collect BV subterms from assertions    │
   │ 2. word-level rewrite / simplify          │
   │ 3. bit-blast residual → CNF + bit-vars    │
   │ 4. map each Bool-sorted BV atom → a literal│
   └──────────────────────────────────────────┘
          │  (assertions with BV atoms replaced by Bool surrogates;
          │   definitional clauses handed to SAT)
          ▼
   existing Tseitin + CDCL SAT core  →  SAT/UNSAT
          │
          ▼  shinri-bv model.rs: read bit assignments → BV values
   (get-model / get-value)
```

Consequences:
- For pure QF_BV, EUF/Arith/Arrays are never constructed.
- BV equality `(= x y)` is bit-blasted (bitwise XNOR-and), **not** sent to the
  equality engine.
- The blaster emits **CNF clauses + fresh SAT variables**. Each Bool-sorted BV
  predicate atom maps to a single SAT literal. The Boolean skeleton over those
  atoms goes through the existing Tseitin encoder unchanged.

**Blast-to-CNF decision:** the blaster emits CNF directly (allocating fresh SAT
vars), rather than building core Bool *term* DAGs and letting Tseitin blast them.
This is how mature solvers do it and keeps the term DAG small. (Rejected
alternative: emit Bool terms — reuses more infra but builds huge term DAGs.)

## 4. Module Decomposition

### 4.1 `shinri-core` additions

The term layer must represent BV before anything else can use it.

- **BitVec sort** parameterized by width `n`: `SortNode::BitVec(u32)`. Width is
  part of the sort, so sort-checking enforces width agreement.
- **BV literal constant**: a value carrying `(width, bits)`, backing `#xNN`,
  `#b0101`, and `(_ bvK n)`.
- **BV builtin ops** in `BuiltinOp`. Fixed-arity ops (`bvadd`, `bvand`, …) are
  plain variants. Indexed ops carry their parameters: `Extract{hi,lo}`,
  `ZeroExtend(k)`, `SignExtend(k)`, `RotateLeft(k)`, `RotateRight(k)`,
  `Repeat(k)`. Sort-checking computes result widths (concat adds widths, extract
  is `hi-lo+1`, extends add `k`, repeat multiplies).

### 4.2 `shinri-parser` additions

- `(_ BitVec n)` sort syntax.
- BV literals `#x…` (hex) and `#b…` (binary).
- Indexed identifiers via the existing `(_ … )` path: `(_ extract i j)`,
  `(_ zero_extend k)`, `(_ sign_extend k)`, `(_ bvK n)`, `(_ rotate_left k)`,
  `(_ rotate_right k)`, `(_ repeat k)`.

### 4.3 `shinri-bv` crate

One module per concern, each independently testable. The split mirrors the
`shinri-arith` decomposition (simplex/cuts/bounds/… each in its own file).

| Module | Responsibility |
|---|---|
| `lib.rs` | Public entry: `lower(assertions) → LoweredBv { surrogate map, clauses, bit model plan }`. Orchestrates rewrite → blast. |
| `rewrite.rs` | Word-level simplification: constant folding, identities (`x bvand 0`, `x bvor ~0`, add/mul by 0/1), extract-over-concat, nested extract collapse, `bvsub`→`bvadd`+`bvneg`, etc. Pure term→term. |
| `blast/mod.rs` | Blaster driver + memoized `TermId → Vec<Lit>` (one literal per bit) cache; allocates fresh SAT vars; owns the clause sink. |
| `blast/bitwise.rs` | not/and/or/xor/nand/nor/xnor — gate-per-bit. |
| `blast/arith.rs` | ripple-carry add/sub, negate, multiplier (shift-add array). |
| `blast/div.rs` | restoring divider feeding udiv/urem and the signed family (sdiv/srem/smod). |
| `blast/shift.rs` | barrel shifters (shl/lshr/ashr) + rotates/repeat. |
| `blast/structural.rs` | concat/extract/(zero\|sign)_extend — pure wiring, **no clauses**. |
| `blast/compare.rs` | eq, unsigned + signed comparisons → single output literal. |
| `model.rs` | Reconstruct BV values from the SAT model's bit assignments for `get-model`/`get-value`. |

## 5. Data Flow & Solver Wiring

### 5.1 Surrogate mechanism

How BV atoms re-enter the Boolean skeleton:

1. The `Solver` scans assertions; if any BV sort/op appears, it runs the BV
   stage.
2. `rewrite` simplifies the BV term DAG.
3. `blast` walks each Bool-sorted BV atom (`bvult`, `=` over BV, etc.). Blasting
   an atom produces a single output literal `ℓ_atom` plus definitional CNF over
   fresh bit-vars.
4. The solver builds a **surrogate map** `BV-atom TermId → fresh Bool TermId`
   (a 0-ary Bool constant), and asserts the equivalence `surrogate ↔ ℓ_atom` by
   adding the definitional clauses to the SAT solver keyed on that literal.
5. The assertion DAG has each BV atom replaced by its Bool surrogate. The
   top-level formula is now pure Boolean → existing Tseitin + CDCL runs
   unchanged.

The SAT core and Tseitin encoder need **zero** BV awareness. They see Bool atoms
and clauses; all BV semantics live in the definitional clauses.

### 5.2 Word/bit boundary

Structural ops (`concat`/`extract`/`extend`) never emit clauses — they re-slice
the cached `Vec<Lit>`. Clause count stays tied to genuine arithmetic/logic, not
plumbing.

### 5.3 Solver-level placement

The BV stage sits in `check_sat` ahead of `Combiner` construction. It is
mutually exclusive with the theory path for v1 (pure QF_BV detected by a sort
scan). A query mixing BV with EUF/Arith/Arrays is refused → `unknown`.

## 6. Error Handling, Incrementality & Models

- **Unsupported / out-of-scope** → `unknown`, never a wrong answer (matches
  `shinri-theory::atom::Unsupported`). Mixed BV + other-theory queries fall here
  in v1.
- **Width mismatches** are caught at sort-check time in `shinri-core` (a
  parse/type error), before blasting.
- **Incrementality (push/pop):** v1 blasts on each `check-sat` over the current
  assertion stack; the blaster cache is rebuilt per check. Persistent
  incremental bit-blasting is a v1 non-goal.
- **Model extraction:** `model.rs` reads each declared BV constant's bit-vars
  from the SAT assignment, packs them LSB→MSB into a value, formats as
  `#x…`/`#b…`.

## 7. Testing

Mirrors the established differential-oracle-vs-z3 pattern.

- **Per-gadget unit tests** in each `blast/*.rs`: exhaustive for small widths
  (e.g. all 8×8-bit add/mul/udiv/shift pairs) against a Rust reference computed
  with native integers.
- **Rewrite tests:** simplify, then check semantic equivalence by blasting both
  sides and asserting the miter is UNSAT.
- **Differential oracle vs z3** on QF_BV: random well-typed BV formulas, assert
  agreement on SAT/UNSAT; plus the existing workspace non-regression sweep.
- **End-to-end witness tests:** known SAT/UNSAT QF_BV queries with model checks.

## 8. Summary of Decisions

| Decision | Choice |
|---|---|
| Engine model | Hybrid: word-level rewrite front-end + eager bit-blast |
| Operator coverage | Full QF_BV |
| Combiner integration | None — standalone eager front-end, bypasses the theory seam |
| Blaster output | CNF + fresh SAT vars (not Bool term DAGs) |
| Incrementality | Re-blast per `check-sat` (no persistent incremental) |
| Combination (UFBV/ABV) | Out of scope for v1 |
