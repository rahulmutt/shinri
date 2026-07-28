# Slice 45 — Bool-result uninterpreted applications in the bit-blaster

**Status:** design
**Date:** 2026-07-28
**Area:** `shinri-bv` (`blast::blast_bv_atom`'s new `Op::Uninterpreted` arm),
`shinri-fp` (`Lowerer::atom`'s dispatch), `shinri-solver` (`bv_stage`'s
`collect_bv_atoms`, `uf_args_supported`, `uf_congruence_cost`; three oracle
generators). No new crate, no new theory slot, no parser surface change, no
`Combiner` change, no new gadget.
**Predecessors:** slice 44 gave BitVec-result uninterpreted applications
Ackermann congruence in the blaster and named Bool-result applications as
deliberately out of scope (slice 44 §2, "Out of scope, deliberately
unchanged"). This slice is that follow-on. It reuses slice 44's `blast_uf_app`,
`UfApp` registry, `shape_compatible` pairing predicate, `word_eq` hook, and
`UF_CONGRUENCE_BUDGET` **verbatim** — the only new code is one match arm, one
dispatch reorder, and three fence-guard widenings.

## 1. Summary

An uninterpreted application with **Bool result sort and non-empty arguments**
— `(p x)` where `p : (_ BitVec 8) → Bool` — is fenced to `unknown` whenever a
BitVec sort is in play. `has_non_bv_theory_atom`
(`crates/shinri-solver/src/bv_stage.rs:177`) exempts *nullary* Bool
uninterpreted symbols, because a nullary symbol has no arguments for congruence
to act on and Tseitin encodes it as a plain SAT variable. A non-nullary one
falls through to the conservative arm — "any other App node that is Bool-sorted
is a candidate atom" — and fences.

Measured on the pre-slice release binary (`main` @ `15149258`), every one of
these is `unknown`:

| # | Query (`QF_UFBV`, `p : (_ BitVec 8) → Bool`) | Truth | shinri |
|---|---|---|---|
| Q1 | `(= x y)`, `(p x)`, `(not (p y))` | `unsat` | `unknown` |
| Q2 | `(p x)` | `sat` | `unknown` |
| Q3 | `(p x)`, `(not (p y))` | `sat` | `unknown` |
| Q4 | `(p x)`, `(bvult x #x05)` | `sat` | `unknown` |
| Q5 | `(p x)`, `(not (p x))` — propositional, needs no theory | `unsat` | `unknown` |

Q5 is the sharpest illustration: the same hash-consed term asserted at both
polarities is refutable by the SAT skeleton alone, and the fence fires before
the skeleton ever runs.

**The gap is specifically BitVec-sorted arguments.** The same three shapes over
`Int`, `Bool`, or an uninterpreted sort all decide correctly today via the EUF
engine — measured, all `unsat`:

```
(set-logic QF_UF)  (declare-fun p (Bool) Bool)  … (= a b) (p a) (not (p b))  → unsat
(set-logic QF_UF)  (declare-sort U 0) (declare-fun p (U) Bool) …             → unsat
(set-logic QF_UFLIA) (declare-fun p (Int) Bool) …                            → unsat
```

BitVec arguments are what force the query onto the eager bit-blaster, which
cannot be combined with EUF. So the fence is not an oversight; it is the
standing "BV is not a combinable theory" decision showing through.

**This is a completeness slice, not a soundness slice.** Unlike slice 44 there
is no wrong answer to fix. That distinction drives two things: the invariant in
§2, which is strictly tighter than slice 44's, and the gate design in §6, which
cannot be a plain differential oracle because every existing harness treats
`Unknown` as a skip.

### 1.1 The hazard that turned out not to be one

A Bool-sorted term can nest inside a BitVec term only through `ite`:
`(bvult (ite (p x) #x01 #x00) c)`. Both `collect_bv_atoms` and
`has_non_bv_theory_atom` treat a collected atom as a **leaf** and do not
descend into it, so a `(p x)` buried there is invisible to the fence's walk. If
it then reached the blaster, congruence would be silently missing — slice 44's
failure mode exactly, with no crash and no visible symptom.

Measured on the pre-slice release binary, all three probes fence correctly:

```
(= x y), (= (ite (p x) #x01 #x00) #x01), (= (ite (p y) #x01 #x00) #x00)  → unknown  [truth: unsat]
(= (ite (p x) #x01 #x00) #x01), (= (ite (p x) #x01 #x00) #x00)           → unknown  [truth: unsat]
(= x y), (distinct (ite (p x) #x01 #x00) (ite (p y) #x01 #x00))          → unknown  [truth: unsat]
```

The reason is `word_norm.normalize` (`crates/shinri-solver/src/lib.rs:759`),
which runs **before** atom collection and eliminates BitVec `ite`s into a fresh
symbol plus a defining assertion — lifting `(p x)` to the assertion level where
the fence's walk does see it. Post-slice these same queries must **decide**,
and that is the test which proves the lifting works rather than assuming it.

## 2. Scope and the invariant

**In scope.** Uninterpreted applications with **Bool result sort and non-empty
arguments**, on all three paths that share `blast_bv_atom`
(`crates/shinri-bv/src/blast/mod.rs:609`):

- pure-BV — `Blaster::blast_atom` (`blast/mod.rs:330`), driven by
  `shinri_bv::lower` (`crates/shinri-bv/src/lib.rs:31`);
- FP/mixed — `Lowerer::atom` (`crates/shinri-fp/src/lower.rs:113`);
- ABV — the persistent blaster across refinement rounds
  (`crates/shinri-solver/src/abv_stage.rs:322`).

**Out of scope, deliberately unchanged.**

- **FP-result** applications. An uninterpreted FP-sorted word is still rejected
  by `is_supported_fp_word`, and `fp_atoms_fully_supported`
  (`fp_stage.rs:767`) still fences the query.
- Applications whose **arguments** are Int-, Bool-, Array-, String-,
  Datatype-, uninterpreted-, or RoundingMode-sorted. Fence 1 keeps fencing
  them. A Bool argument is worth calling out because it looks superficially
  blastable as a one-bit word: it is not, because a Bool child can be an
  arbitrary formula and the blaster has no Tseitin encoder. It stays fenced.
- **BV ⋈ Int/String/DT** combination. BV is still not a combinable theory.
- **`get-model` for arity > 0 symbols.** `p` itself remains omitted, so a model
  for a UF query stays incomplete (slice 43 §5, still open). Only argument
  values appear, by the same mechanism slice 44 §7.5 measured.

### 2.1 The invariant — strictly tighter than slice 44's

Slice 44 *had* to change verdicts; the defect's signature was a wrong `sat`.
This slice must change **none**.

- **Permitted:** `unknown` → decided. That is the whole point of the slice.
- **Regression:** any `sat` → `unsat`, any `unsat` → `sat`, any decided →
  `unknown`.

There is **no named-exception list** this time. Slice 44 needed one because its
two new fences legitimately withdrew completeness from queries that previously
decided. This slice adds no fence and withdraws nothing: it only widens which
atoms the blaster is allowed to own. Any decided → `unknown` flip is therefore
a defect in the widening, not a trade-off — most plausibly the §5 leaf-rule
hazard.

Gates: `qfbv_witnesses`, `script_e2e`, `qfdt_e2e`, `qfuf_e2e`, and the **full
unfiltered** oracle suite (slice 40's lesson: a filtered run skips
`qfs_differential`).

## 3. The gadget

`blast_bv_atom` gains one arm, ahead of its builtin dispatch:

```rust
TermNode::App { op: Op::Uninterpreted(sym), args, .. } => {
    // Bool-sorted, non-nullary. Fence 1 has already guaranteed every
    // argument is a blastable word.
    let child_ids = ctx.children(args).to_vec();
    blast_uf_app(sink, ctx, sym, &child_ids, /* width */ 1)[0]
}
```

`blast_bv_atom` is only ever called on a Bool-sorted term, so the arm needs no
result-sort test.

**Nullary applications stay out of collection (§4), and the reason is not
soundness.** It is worth being exact, because the obvious worry is wrong:
`encode_uncached` intercepts a collected atom by TermId *before* reaching
`atom()`, and memoizes (`tseitin.rs:112`), so a collected nullary Bool symbol
would get exactly one literal, not a blaster literal competing with a Tseitin
one. `blast_uf_app` also returns at its `child_ids.is_empty()` branch *before*
touching the registry, so nothing would enter the `UfApp` store either. Routing
a bare Bool constant through the blaster would simply be a pointless detour to
the same unconstrained variable.

Nullary applications are excluded because the existing Tseitin path for bare
Bool constants is the well-understood one and this slice has no reason to move
it, and because `nullary_applications_emit_no_congruence_clauses` pins that
arm's clause count — a constant this slice must leave undisturbed (§6.6).

Nothing inside the gadget changes. `blast_uf_app`
(`crates/shinri-bv/src/blast/mod.rs:358`) already:

- blasts the arguments **first** — the load-bearing step order, so that
  `p(f(x))` registers the inner BitVec-result application while lowering its
  own argument;
- filters priors through `shape_compatible`, not `sym ==` alone;
- emits the **implication only**, `(⋀ₖ argₖ equal) → (result equal)`, never the
  converse;
- registers the new application in the `UfApp` registry.

At `width = 1` the result word is a single fresh literal and the pairwise
clause degenerates to one clause — `cond → (v_prior ↔ v_new)` — rather than one
per result bit.

### 3.1 Why `shape_compatible` needs no change

`Context::declare_fun` interns by name and overwrites `fun_sigs`, and
`Command::DeclareFun` accepts a redeclaration silently, so one `SymbolId` can
carry applications of two different functions in a single assertion list. This
slice makes that sharper: the same name can now be Bool-result in one
declaration and BitVec-result in another, and pairing those would be unsound.

`shape_compatible` already discriminates them on `prior.result.len() ==
result_len` — 1 for a Bool result, `width` for a BitVec result. It is total
over arity, per-argument sort, per-argument word length, and result length, and
the arm carries no shape assertion precisely so that the guard is what holds in
the shipping profile. No change; a test pins the discrimination.

### 3.2 Two implementation details that are easy to get wrong

**(a) `Lowerer::atom` dispatches on the first operand's sort.**

```rust
// crates/shinri-fp/src/lower.rs:113-124
let first_operand_sort = /* sort of kids[0] */;
if ctx.bv_width(first_operand_sort).is_some() {
    blast_bv_atom(self, ctx, t)
} else {
    crate::blast_fp_atom(self, ctx, t)
}
```

For `(p x)` with a BitVec first argument this routes correctly. For `(p f)`
with an FP first argument it routes to `blast_fp_atom`, which has no
uninterpreted-application arm — a panic, not an `unknown`. The
`Op::Uninterpreted` case must be matched **before** the first-operand-sort
test. This is the one place in the slice where a mistake crashes rather than
degrades, and it is the same shape as the slice-43 panic.

**(b) `rewrite` can make two distinct original atoms converge.**
`shinri_bv::rewrite` (`crates/shinri-bv/src/rewrite.rs:19`) is generic and
structure-preserving — it rewrites children bottom-up and rebuilds — so a Bool
UF app passes through with its arguments simplified. Consequently
`(p (bvadd x #x00))` and `(p x)` rewrite to the **same** TermId, while `lower()`
blasts each rewritten atom separately and mints two independent result
literals for one term.

This is **correct but wasteful**: congruence relates them, the antecedent is
identically true because the argument words are the same, and the two literals
are forced equal. Memoizing the atom literal by *rewritten* TermId — while
keeping `atom_lit` keyed by the *original*, the contract `lower()` already
documents — removes the duplication. It is an efficiency and clarity choice,
**not** a soundness one, and the spec records it as such so a reviewer does not
mistake the memo for a correctness fix.

## 4. Collection and the fences

The load-bearing edit is to collection, because all three paths call it:

**`collect_bv_atoms`** (`bv_stage.rs:124`) additionally collects Bool-sorted
non-nullary `Op::Uninterpreted` applications.

That single change satisfies every path's foreign-theory fence at once, since a
collected atom is in `bv_set` and each fence's walk returns at it.

| Guard | Today | Change |
|---|---|---|
| `has_non_bv_theory_atom` (`bv_stage.rs:177`) | non-nullary Bool UF app → fence | **none** — the app is now in `bv_set`, so the walk returns at it |
| `has_non_bvfp_theory_atom` (`fp_stage.rs:303`) | delegates over `fp_atoms ∪ bv_atoms` | **none** — inherits the widened `bv_atoms` |
| `uf_args_supported` — Fence 1 (`bv_stage.rs:279`) | guards on `ctx.bv_width(*sort).is_some()` | widen to BitVec-**or-Bool** result sort; the argument-admissibility rule is unchanged |
| `uf_congruence_cost` → `collect_uf_apps` — Fence 2 (`bv_stage.rs:341`) | same `bv_width` guard | same widening, with `res_bits = 1`; `UfShapeKey` already keys on the result `SortId`, so Bool and BitVec results group separately, mirroring `shape_compatible` |

`UF_CONGRUENCE_BUDGET` stays at its slice-44 calibrated value and stays
**global**: `uf_congruence_cost` already sums `pairs(k) × (arg_bits +
res_bits)` across every shape group, so Bool-result applications simply join
the sum. No second budget, no per-family budget. The claim that the existing
budget still holds with predicates in the mix is measured (§6, T6), not
assumed — slice 42's lesson that a fully-implemented plan with green reviews
can still rest on a wrong premise until the measured gate runs.

### 4.1 The renaming question

After this change `collect_bv_atoms` no longer means "BitVec atoms". It means
"atoms the blaster owns". Its module doc currently calls out BV (dis)equality
inclusion as *the* soundness-critical subtlety
(`crates/shinri-solver/src/bv_stage.rs:11`); this adds a second one. The
function is renamed to `collect_blastable_atoms`, or — if the churn across
`bv_stage`, `fp_stage`, `abv_stage`, and `lib.rs` is judged worse than the
imprecision — kept and re-documented with both subtleties stated. The
implementer picks one and records which; what is **not** acceptable is leaving
the doc comment describing the pre-slice meaning.

## 5. The one new risk

A collected atom is a **leaf** in `has_non_bv_theory_atom`'s walk — it returns
without descending. Making Bool UF apps collectible therefore hides their
argument subtrees from the foreign-theory fence, which previously saw them.

Fence 1 is the backstop: an admitted application's arguments must be BitVec-
(or, on the FP path, FP-) sorted, so nothing Int-, Array-, String-, or
DT-sorted can hide there. But **Fence 1 checks argument sorts, not
blastability**. A BitVec-sorted `(select a i)` passes by sort while the pure-BV
blaster has no arm for it.

The expected resolution is that `uses_arrays` routes any such query to
`abv_stage` before the pure-BV path is reached, and that `abv_stage`'s
abstraction replaces `select`/`store` with fresh BitVec symbols *before*
`collect_bv_atoms` runs on `abs.assertions` — making the shape unreachable.
That is a plausible argument, not a measurement, and slice 38 is this project's
standing lesson that "provably unreachable" claims must be measured. It gets
its own task.

Two things to note about its blast radius. First, it applies **equally to slice
44's already-shipped BitVec-result arm** — `(f (select a i))` has the same
shape — so whatever the audit finds is a pre-existing condition this slice
surfaces, not one it introduces. Second, if the routing argument does not hold,
the fix is a fence (reject an application whose argument is not a blastable
word, not merely a well-sorted one), which costs completeness on a shape
nobody has yet demonstrated.

## 6. Testing

### 6.1 T1 — the gate, and why it cannot be a plain differential oracle

Every existing oracle harness treats our `Unknown` as a skip:

```rust
// crates/shinri-solver/tests/qfbv_oracle.rs:483
(SolveOutcome::Unknown, _) => {
    // Our Unknown is never a failure — skip.
    n_unknown += 1;
}
```

For slice 44 that was fine: the generator failed on pre-slice `main` with a
wrong `sat`. Here it cannot fail at all — pre-slice, every instance containing
a UF predicate is `unknown`, which the harness counts as a skip. A generator
extension alone would be green on pre-slice `main`, i.e. would prove nothing.
This is the `oracle-generator-blind-spots` failure mode in a new costume.

The mechanism that gives a completeness slice teeth is a **family-scoped
decidedness assertion**. Each generator is extended with Bool-result
predicates, counts the instances that contain one, and asserts a minimum
decided fraction among exactly those — alongside the existing
zero-disagreement panic, which stays unconditional.

- **`qfbv_oracle`** — add `p` (1-ary) and `q` (2-ary), Bool-result, over the
  existing width-parameterized BitVec term pool, beside the `f`/`g` slice 44
  added.
- **`qfabv_oracle`** — the same, beside the `f`/`g` it already declares at
  `qfabv_oracle.rs:137`. It already emits `set-logic QF_AUFBV` rather than
  `QF_ABV` so z3 accepts a non-nullary `declare-fun`.
- **`fp_oracle`** — `(declare-fun p ((_ FloatingPoint 8 24)) Bool)`. This is
  the instance that exercises §3.2(a)'s dispatch and `core_eq`-based
  congruence; it is the highest-value single test in the slice because its
  failure mode is a panic.

**The threshold.** Mirror the existing global guard: among instances containing
a UF predicate, more than half must decide (`decided > family_total / 2`),
plus `family_total > 0` so an empty family cannot pass vacuously — the
0-tests-read-as-green failure mode at the assertion level. Half is chosen
because it fails unambiguously at the pre-slice 0% while leaving room for
instances that fence for unrelated reasons (an Int argument the generator also
emitted, a budget trip). If the measured post-slice fraction lands close enough
to 50% that the assertion would be flaky, raise or lower the threshold to sit
clearly below the measured value and **record both the measurement and the
chosen number** in §8.2 — never tune it upward to whatever the run happened to
produce.

Pre-slice the decided fraction is **0%** and each assertion fails. Both the
pre-slice failure and the post-slice pass are recorded as measurements in §8.
The existing global `ran > total / 2` unknown-rate guard stays as it is; the
new assertion is family-scoped, so a healthy overall rate cannot mask a
predicate family that never decides.

### 6.2 T2 — direction tests

The tests that catch the likely bug, in the order a wrong implementation fails
them:

1. `x ≠ y`, `(p x)`, `(not (p y))` must stay **sat**. Congruence is an
   implication; encoding a biconditional would wrongly force distinct arguments
   to distinct results. This is the Bool-result mirror of slice 44's
   `congruence_is_an_implication_not_a_biconditional`.
2. `(= x y)`, `(p x)`, `(not (p y))` must be **unsat** — congruence fires.
3. `(p (f x))` with `f : BV → BV` — a Bool application over a BitVec-result
   application, exercising the blast-arguments-first order across both arms.
4. **Redeclaration discrimination:** one symbol name declared Bool-result and
   then BitVec-result within one assertion list must not be paired. Asserts the
   `shape_compatible` `result.len()` guard directly, at the unit level, since
   the guard must hold in the shipping profile where an assertion would vanish.
5. **FP-argument congruence:** `(p a)`, `(not (p b))`, `(= a b)` with `a`, `b`
   FP-sorted must be **unsat**, and the NaN case — two distinct NaN bit
   patterns — must also be congruent, which only `core_eq` gets right.

### 6.3 T3 — the `ite`-lifting pins

The three §1.1 probes, each measured `unknown` pre-slice, must decide `unsat`
post-slice. They are what proves `word_norm`'s `ite` elimination lifts the
condition to where collection sees it, rather than leaving a Bool term inside a
blasted word.

### 6.4 T4 — fence pins

- Bool argument (`p : Bool → Bool`) with a BitVec sort in play → still
  `unknown` (Fence 1).
- Int argument → still `unknown` (Fence 1), the Bool-result sibling of slice
  44's `int_argument_to_a_bv_uf_fences_to_unknown`.
- A predicate population past the budget → `unknown` (Fence 2), with the cost
  accounted at `res_bits = 1`. A unit test pins that
  `uf_congruence_cost` counts a Bool-result application at
  `pairs(k) × (arg_bits + 1)`.

### 6.5 T5 — the model channel, measured not assumed

`display_term` (`crates/shinri-solver/src/tseitin.rs:483`) already renders
non-nullary `Op::Uninterpreted` applications structurally, so
`(get-value ((p x)))` will now emit the label `(p x)`. Whether it emits a
**value** is unmeasured today because the query never got past the fence.

Measure it on the built binary and pin whatever it does. `get-model` is
unchanged and still omits `p`. Argument variables gain values by the same
mechanism slice 44 §7.5 measured — congruence forces the arguments to be
blasted, so they enter `Blaster.cache` and become visible to
`exported_var_bits`. Slice 43's lesson stands: absence of a value must not be
rendered as a confident default.

### 6.6 T6 — non-regression

- Full **unfiltered** oracle suite: `cargo nextest run -p shinri-solver
  --features oracle`. Without the feature it silently runs 0 tests; a 0-test
  run reads as green and is not coverage.
- `qfbv_witnesses`, `script_e2e`, `qfdt_e2e`, `qfuf_e2e`. Use the nextest
  expression form — `-E 'binary(script_e2e)'`, not a positional filter — and
  confirm a non-zero discovered count.
- PR-tier wall clock against the 10–15 min budget (CI hard cap 20 min), with
  `UF_CONGRUENCE_BUDGET` at its unchanged slice-44 value.
- `nullary_applications_emit_no_congruence_clauses` still passes at its
  constant: a nullary Bool symbol must remain a plain Tseitin SAT variable and
  must not enter the registry.

## 7. Success criteria

1. Every §1 probe query (Q1–Q5) and every §1.1 `ite` probe decides, agreeing
   with **both** z3 and cvc5.
2. The three extended generators **fail on pre-slice `main`** and pass after;
   both results recorded as measurements in §8.
3. **Zero verdict changes and zero decided → `unknown` flips** across every §2.1
   gate. There is no named-exception list: `unknown` → decided is the only
   permitted flip, and anything else is a defect.
4. The `Lowerer::atom` FP-argument path is exercised by a passing test, so
   `blast_fp_atom`'s unsupported arm stays an internal invariant rather than a
   user-triggered panic.
5. The §5 Fence-1 argument-blastability audit reaches a **measured**
   conclusion — either a demonstrated routing that makes the shape unreachable,
   or a fence. A reasoned argument alone does not close it.
6. The PR tier stays inside its budget with `UF_CONGRUENCE_BUDGET` unchanged,
   and the shared-budget claim is measured rather than assumed.
7. `collect_bv_atoms` is either renamed or re-documented (§4.1); no committed
   doc comment describes the pre-slice meaning.

## 8. Measured outcomes

To be filled in during implementation. Every row must cite the binary profile
(debug or release) and the commit it was measured at, so a later slice can
reproduce it.

- 8.1 — T1: the pre-slice generator failures (three, one per oracle), with the
  measured decided fraction of 0%.
- 8.2 — T1: the post-slice decided fractions and the thresholds chosen.
- 8.3 — T5: `get-value` and `get-model` behaviour on a Bool UF app.
- 8.4 — §5: the Fence-1 blastability audit's conclusion and its evidence.
- 8.5 — T6: the full unfiltered oracle summary and the PR-tier wall clock.
