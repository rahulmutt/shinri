# shinri QF_S Core — Strings + LIA (SLIA Core) Design

**Date:** 2026-06-24
**Status:** Approved design, pre-implementation
**Scope:** The **core** of the SMT-LIB `String` theory — the `String` sort,
concatenation, length, `str.at`, `str.substr`, and (dis)equality — combined with
the existing linear-integer-arithmetic solver (effectively **QF_SLIA core**),
decided by a length-aware DPLL(T) string calculus that plugs into the existing
lazy `Combiner` and Nelson–Oppen Int seam.

> **Roadmap context.** This is **Spec 1 of 4** in the decomposition of full
> SMT-LIB `QF_S`. The remaining slices, each its own spec → plan → implement
> cycle, are: **Spec 2 — Regular expressions** (`str.in_re` + `re.*`);
> **Spec 3 — Extended functions** (`str.contains`, `str.indexof`,
> `str.prefixof`, `str.suffixof`, `str.replace`, `str.replace_all`);
> **Spec 4 — Conversions** (`str.to_int`, `str.from_int`, `str.to_code`,
> `str.from_code`). Spec 1 establishes all structure (crate, theory solver,
> Combiner/N-O integration, calculus, model construction); Specs 2–4 are
> additive.

## 1. Goal & Scope

Add the **core** of the SMT-LIB `String` theory to shinri, combined with linear
integer arithmetic. Because `str.len` returns an `Int` and virtually every
interesting string constraint involves length reasoning, the realistic unit is
strings combined with LIA — **QF_SLIA core** — solved through theory combination
rather than as a standalone theory.

**In scope (v1):**
- The `String` sort; string literals and string variables.
- `str.++` (concat), `=` / `distinct` on strings.
- `str.len`, `str.at`, `str.substr`.
- All length reasoning delegated to the existing LIA solver via the
  Nelson–Oppen **Int** exchange (every `str.len t` is a shared Int term).
- Word-equation solving by normal-form alignment splitting, emitted as
  `TCheck::Split` lemmas.
- `(get-model)` / `(get-value)` over string and length terms (concrete string
  assignments).
- Alphabet = SMT-LIB Unicode scalar values `0x0..0x2FFFF` (196607), matching
  z3/cvc5 for differential parity.

**Deliberate non-goals (v1, deferred to later specs):**
- **Regex** (`str.in_re`, `re.*`) — Spec 2.
- **Extended functions** (`str.contains`, `str.indexof`, `str.prefixof`,
  `str.suffixof`, `str.replace`, `str.replace_all`) — Spec 3.
- **Conversions** (`str.to_int`, `str.from_int`, `str.to_code`,
  `str.from_code`) — Spec 4.
- Strings mixed with **EUF / arrays / BV / uninterpreted sorts** beyond the
  String+LIA combination → fenced to `unknown`.
- **Inter-`check-sat` persistence** of string state. (Intra-`check-sat`
  incrementality via the Combiner's `push`/`pop` is supported; see §9.)

**Soundness contract.** The calculus is **incomplete by design** — QF_S is
undecidable. A **fuel budget** caps total splits / derived-variable depth; on
exhaustion the query returns `unknown`, never a wrong SAT/UNSAT verdict.
Everything out of scope returns `unknown` via the established fence discipline.
This matches the soundness posture of the QF_BV / QF_ABV designs: anything not
decided is `unknown`, never an incorrect answer.

## 2. Approach

**Length-aware DPLL(T)** (the cvc5 / z3-seq family), implemented as a new
`TheorySolver` in crate `shinri-str`, a **congruence-only Nelson–Oppen
participant** in the mold of `shinri-arrays`:

- It **owns no equality state**; string (dis)equalities are read from and
  asserted through the shared `EqualityEngine`.
- Every `str.len t` term is registered as a **shared Int** term so the existing
  LIA solver owns all length arithmetic, via the trait's
  `shared_arith_terms` / `ensure_shared_var` / Int N-O seam.
- Word equations over concatenations are normalized and resolved by **alignment
  case-splits** emitted as `TCheck::Split` clauses of positive atoms — the exact
  mechanism `shinri-arrays` uses for ROW lemmas. Length-feasibility of each
  split is enforced by the shared Int constraints, so arith prunes infeasible
  alignments automatically.

The consequence is that strings introduce **no new solving path**: they reuse
the `Combiner`, the Nelson–Oppen Int exchange, and the `TCheck::Split`
lemmas-on-demand seam wholesale. (Contrast with QF_ABV, which had to fork a
separate eager path because BV is an eager pre-pass. Strings have no such
impedance mismatch — they are a lazy theory like EUF/arith/arrays.)

## 3. Architecture & Pipeline Placement

```
parse → assertions (term DAG; may contain str.* ops, String sort)
   │  shinri-solver routing
   ▼ contains String sort / str.* ops?
     │ no  → existing paths unchanged
     │ yes → mixed with EUF/arrays/BV/uninterpreted sorts? ── yes → unknown (fence)
     │          ▼ no  (String + LIA only)
   reduction pre-pass:  str.at / str.substr → concat + len + fresh vars + guards
   register String theory in Combiner; str.len terms → shared Int (N-O)
   CDCL(T) loop: Combiner drives SAT + theories;
        StrSolver.check() emits alignment splits via TCheck::Split;
        LIA owns all length arithmetic via the Int exchange
```

**Crate.** New crate **`shinri-str`**, mirroring `shinri-arrays`'s layout.
Depends on `shinri-theory` (the `TheorySolver` trait, `EqualityEngine`, N-O
seam, `ModelBuilder`), `shinri-core` (term DAG, sorts). It registers with the
`Combiner` alongside EUF / arith / arrays.

**Routing & fence (in `shinri-solver`).** Detect assertions containing the
`String` sort or `str.*` operators and admit the String+LIA combination. Refuse,
as `unknown`, any query mixing strings with EUF, arrays, BV, or uninterpreted
sorts — consistent with the mixed-theory fences in the BV/ABV designs.

**Reduction pre-pass.** `str.at` and `str.substr` are **desugared into the
core** (concat + length + fresh string variables + boundary guards) before
solving, so the `StrSolver` itself only ever sees `str.++`, `str.len`, and
`=`/`distinct`. (See §5.) This mirrors how the abv stage desugars n-ary `+` /
`distinct` array atoms into pairwise binary form.

**`StrSolver: TheorySolver` responsibilities.**
- `new_var` / `assert` — track string atoms and (dis)equalities through the
  shared `EqualityEngine`.
- `shared_arith_terms` / `ensure_shared_var` / `entailed_equalities` /
  `consume_interface_equality` — surface every `str.len t` as a shared Int so
  LIA reasons about lengths, and consume length equalities LIA entails (e.g.
  `len(s) = 0`).
- `check` — run the calculus (§4); return `TCheck::Split` for an alignment
  branch, `TCheck::Conflict` for a length/character contradiction, or
  `TCheck::Sat`.
- `explain` — resolve split/conflict justifications back to input literals.
- `model` — construct concrete string values (§6).
- `push` / `pop` — participate in the Combiner's scoped backtracking like every
  other theory.

## 4. The Core Calculus

### 4.1 Length skeleton (always asserted to LIA via the Int seam)

For every string term the solver registers the structural length facts so
arithmetic does the numeric work:

- `len(s) ≥ 0` for every string term `s`.
- `len("…") = literal-length` for every string constant.
- `len(x ++ y ++ …) = len(x) + len(y) + …`.
- **Empty link:** when LIA entails `len(s) = 0`, the solver adds `s = ""`; and
  `s = "" → len(s) = 0`.

### 4.2 Normal forms

Each string term has a flattened concatenation **normal form** — a sequence of
*atoms* (variables or string constants) modulo congruence read from the shared
`EqualityEngine`. An asserted equality `lhs = rhs` requires the two normal forms
to **unify**.

### 4.3 Word-equation alignment splitting (F-split)

To unify `a₁·a₂·… = b₁·b₂·…`, inspect the leading atoms `a₁, b₁`:

- **Same atom** → strip both, recurse on the tails.
- **Both constants** → compare characters: a prefix mismatch is a
  `TCheck::Conflict`; otherwise strip the shared prefix and recurse.
- **Otherwise (≥1 variable head)** → emit the **F-split** as `TCheck::Split`, a
  disjunction of positive atoms whose three cases are exhaustive and mutually
  exclusive over the integers:
  1. `len(a₁) = len(b₁)`  ⟶  `a₁ = b₁`            (heads align; recurse on tails)
  2. `len(a₁) > len(b₁)`  ⟶  fresh `z`: `a₁ = b₁ ++ z`  (b₁ a strict prefix of a₁)
  3. `len(a₁) < len(b₁)`  ⟶  fresh `z`: `b₁ = a₁ ++ z`  (a₁ a strict prefix of b₁)

  LIA evaluates the length atoms, so infeasible alignments are pruned by arith
  without the string solver guessing. A **variable-vs-constant** head is the same
  rule with the constant split character-by-character (including the
  empty-variable branch).

### 4.4 Disequalities `s ≠ t`

Discharged lazily: if the normal forms reduce to the **same** word →
`TCheck::Conflict`. Otherwise the disequality is satisfied by the split
`len(s) ≠ len(t)` ∨ (lengths equal ∧ a witnessed differing position),
introduced only when the rest of the model would otherwise force `s = t`.

### 4.5 Fuel budget (termination)

The only source of non-termination is unbounded fresh-remainder generation
(word equations are undecidable). A **fuel budget** caps total splits and
derived-variable depth; on exhaustion the solver signals `unknown` up through
the Combiner. This is sound: a genuine `Conflict` or a fully-unified `Sat` is
always honored; only true non-termination is cut.

## 5. `str.at` / `str.substr` Reduction (SMT-LIB semantics)

Desugared in the pre-pass into core constraints with boundary guards, so the
`StrSolver` never special-cases them:

- **`str.substr(s, i, l)`** → fresh `pre, mid, post` with
  `s = pre ++ mid ++ post`. When `0 ≤ i < len(s)` and `l > 0`:
  `len(pre) = i`, `len(mid) = min(l, len(s) − i)`, result `= mid`.
  Otherwise (out-of-range `i`, or `l ≤ 0`): result `= ""`.
  The guard disjunction and the `min` become length atoms / splits handed to
  LIA.
- **`str.at(s, i)`** → exactly `str.substr(s, i, 1)`.

All guards reduce to length arithmetic owned by LIA.

## 6. Model Construction (`get-model` / `get-value`)

After the Combiner reports SAT, LIA holds a concrete length for every string
atom. The solver builds concrete words:

1. Read `len(x)` for each free string variable from the arith model.
2. Walk each equality's unified normal form. Constant atoms pin specific
   characters; positions still free are filled with a **default character**
   (`U+0041 'A'`), respecting all length and alignment constraints.
3. Assemble compound term values (`str.++`, `str.at`, `str.substr`) by
   concatenation / slicing of their atoms' assigned words.
4. Render as SMT-LIB string literals, with standard `\u{…}` escaping for
   non-printable / non-ASCII scalar values.

The constructed assignment must satisfy the original assertions — enforced by
the E2E witness checks in §8.

## 7. Soundness & Termination

**Soundness.** String (dis)equalities flow through the shared `EqualityEngine`;
all length arithmetic is owned by LIA through the audited Nelson–Oppen Int seam.
Every `TCheck::Split` is a **valid** disjunction — the three F-split cases are
exhaustive and mutually exclusive over the integers, so adding the clause
removes no real model. A `Conflict` is raised only on a genuine character
mismatch or an unsatisfiable length system. A `Sat` verdict means every word
equation unified and every disequality is witnessed, so a total string model
exists. Therefore neither the SAT nor the UNSAT verdict can be wrong.

**Termination.** The only source of non-termination is unbounded
fresh-remainder generation. The fuel budget bounds total splits and
derived-variable depth; exhaustion yields `unknown`. Every fuel-respecting run
terminates because each non-splitting step strictly shrinks the pending equation
set.

## 8. Testing

Mirror the differential-oracle methodology that landed with QF_BV / QF_ABV:

- **Differential oracle vs z3:** randomly generate well-sorted QF_SLIA-core
  formulas (concat chains, shared variables, length constraints linking to LIA,
  `str.at` / `str.substr`, equalities and disequalities, mixed literal/variable
  heads) and compare SAT / UNSAT / `unknown` verdicts against z3. An `unknown`
  from fuel exhaustion is treated as a **non-disagreement** (z3 SAT/UNSAT vs
  shinri `unknown` is acceptable; a shinri SAT vs z3 UNSAT, or vice versa, is a
  hard failure).
- **E2E witness checks:** on SAT, validate that the constructed string model
  satisfies the original assertions.
- **Targeted unit tests** per calculus rule: prefix-mismatch conflict, the three
  F-split branches (§4.3), the empty-length link (§4.1), disequality witnessing
  (§4.4), `str.substr` in-range / out-of-range / clamped (§5), `str.at`, and the
  length↔LIA Int exchange.
- **Fuel tests:** an adversarial diverging word equation returns `unknown`
  (never hangs, never a wrong verdict).
- **Fence tests:** strings mixed with EUF / arrays / BV / uninterpreted sorts
  return `unknown`.

## 9. Open Sub-Decisions (resolved defaults)

- **Crate vs. module:** new crate `shinri-str` (parity with `shinri-arrays`,
  clean layering). *Chosen.*
- **Length ownership:** LIA via the Nelson–Oppen Int seam; the string solver
  never performs integer arithmetic itself. *Chosen.*
- **Reduction site:** `str.at` / `str.substr` desugared in a pre-pass, not
  inside the calculus. *Chosen.*
- **Default model character:** `U+0041 'A'`. *Chosen.*
- **Incrementality:** intra-`check-sat` via the Combiner's `push` / `pop`;
  inter-`check-sat` persistence is a non-goal (matches ABV). *Chosen.*
- **Fuel budget shape:** combined split-count + derived-variable-depth cap;
  exact constants tuned during implementation against the differential suite.
  *Chosen.*
