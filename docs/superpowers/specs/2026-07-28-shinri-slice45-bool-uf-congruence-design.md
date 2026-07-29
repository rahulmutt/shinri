# Slice 45 — Bool-result uninterpreted applications in the bit-blaster

**Status:** implemented
**Date:** 2026-07-28 (design); implemented 2026-07-29 on branch
`slice45-bool-uf-congruence`, seven tasks over base `main` @ `e1baa3bb`
**Area:** `shinri-bv` (`blast::blast_bv_atom`'s new `Op::Uninterpreted` arm;
`UfApp::result_sort` and its `shape_compatible` conjunct), `shinri-fp`
(`Lowerer::atom`'s dispatch), `shinri-solver` (`bv_stage`'s `collect_bv_atoms`,
`uf_args_supported` + the new `arg_term_blastable`, `uf_congruence_cost`;
`abv_stage::fenced`; three oracle generators). No new crate, no new theory slot,
no parser surface change, no `Combiner` change, no new gadget, and no new
dependency.
**Predecessors:** slice 44 gave BitVec-result uninterpreted applications
Ackermann congruence in the blaster and named Bool-result applications as
deliberately out of scope (slice 44 §2, "Out of scope, deliberately
unchanged"). This slice is that follow-on. It reuses slice 44's `blast_uf_app`,
`UfApp` registry, `word_eq` hook, and `UF_CONGRUENCE_BUDGET` **verbatim** (the
budget confirmed byte-identical to `main` at `9_271_680`).

> **As-built delta from the design, three items — each measured, each written up
> where the original prose lived.** The design said "the only new code is one
> match arm, one dispatch reorder, and three fence-guard widenings", and reused
> `shape_compatible` verbatim. All four of those claims moved:
>
> 1. **`shape_compatible` DID change** — the design's argument that it needed no
>    change is false at result width 1 (§3.1).
> 2. **A FOURTH fence needed its own widening** — `abv_stage::fenced`, which
>    takes raw assertions and so inherited nothing from the collector (§4).
> 3. **A new fence predicate was added** — `bv_stage::arg_term_blastable`,
>    because Fence 1 checked argument *sorts*, not argument *blastability*
>    (§5, §8.4).
>
> None of the three widened scope beyond §2; items 1 and 3 are guards, i.e.
> they narrow. §2.1's invariant held, and needed no exception list: every
> measured flip across the slice was `unknown` → decided or panic → `unknown`.

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

### 3.1 `shape_compatible` DID need a change — this section's original claim was false

> **CORRECTED during implementation (Task 2), with the human partner's
> authorization.** As designed, this section was titled "Why `shape_compatible`
> needs no change" and argued the following, which is **FALSE**:
>
> > `shape_compatible` already discriminates them on `prior.result.len() ==
> > result_len` — 1 for a Bool result, `width` for a BitVec result.
>
> The premise "1 for a Bool result, `width` for a BitVec result" silently
> assumes `width ≠ 1`. At **result width 1** it collapses: this slice records a
> Bool result as a ONE-BIT word, so a Bool-result application and a
> `(_ BitVec 1)`-result application of one redeclared symbol have
> `result.len() == 1` alike. The length check does not tell them apart, the
> pairing predicate would relate two different functions, and congruence would
> emit a clause that is not entailed — a **wrong `unsat`, silently**.
>
> Task 2 did not reason this out on paper; it built the probe, measured the
> wrong `unsat`, and fixed it. The claim below is the corrected one.

`Context::declare_fun` interns by name and overwrites `fun_sigs`, and
`Command::DeclareFun` accepts a redeclaration silently, so one `SymbolId` can
carry applications of two different functions in a single assertion list. This
slice makes that sharper: the same name can now be Bool-result in one
declaration and BitVec-result in another, and pairing those would be unsound.

Slice 44 could infer the result sort from `result.len()`, because the only arm
recording a `UfApp` recorded BitVec results and BitVec sorts intern by width —
equal length therefore meant equal sort. Slice 45 breaks that inference, so the
sort is recorded and compared **directly**:

- `UfApp` gains a `result_sort: SortId` field
  (`crates/shinri-bv/src/blast/mod.rs:87`), the result-side twin of the
  `arg_sorts` field slice 44 added for exactly the same redeclaration hazard on
  the argument side;
- `shape_compatible` gains `&& prior.result_sort == result_sort`
  (`blast/mod.rs:136`), alongside — not instead of — the existing
  `result.len()` check, which stays because it is what the congruence clauses'
  `zip` actually walks.

With that added conjunct the predicate is total over arity, per-argument sort,
per-argument word length, **result sort**, and result word length. The arm
carries no shape assertion precisely so that the guard is what holds in the
shipping profile. `bool_and_bv_results_of_one_symbol_are_never_paired` pins the
discrimination at the unit level, at width 1 where the length check alone fails.

The general lesson, and the reason this correction is written out rather than
quietly patched: a discriminator that works "because the values differ" is not
a discriminator until you check the boundary where they coincide.

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

> **CORRECTED during implementation (Task 5), after measurement, with the human
> partner's authorization.** As designed, this section continued:
>
> > That single change satisfies every path's foreign-theory fence at once,
> > since a collected atom is in `bv_set` and each fence's walk returns at it.
>
> **That premise is measured-false for the third of §2's three paths.** It holds
> for two of them and for exactly the reason given: `bv_stage`'s
> `has_non_bv_theory_atom` and `fp_stage`'s `has_non_bvfp_theory_atom` each
> consume a **collected atom set**, so widening the collector widened them for
> free. The ABV path has a fourth fence, `abv_stage::fenced`, which the table
> below never listed — and it consumes **no atom set at all**. It walks the RAW
> assertions, and it runs at `lib.rs:903`, *before* `shinri_abv::abstract_arrays`
> builds the abstraction that `collect_bv_atoms` is later called on
> (`abv_stage.rs:373`). A query fenced at `:903` never constructs a
> `RealBridge`, so the collector never runs on that path at all and Task 3's
> widening was **invisible to it**.
>
> Task 5 measured this rather than inferring it: after Tasks 1–4, an ABV probe
> containing a Bool-result predicate still answered `unknown`, and the
> `qfabv_oracle` family-scoped decidedness gate still failed at **0/94** — a
> `0/94` that would otherwise have read as "the widening does not work",
> when in fact the widening was correct and simply never reached.
>
> **What replaced it.** A separate, minimal widening of `abv_stage::fenced`'s
> Bool-sorted-uninterpreted-application arm (`abv_stage.rs:194-196`), from
> `return false` for the nullary case only to
> `return kids.iter().any(walk_fence)`. Two properties make it minimal rather
> than a second design:
>
> - it is **bit-identical to the code it replaced for nullary applications** —
>   `Iterator::any` over an empty child list is `false` by definition — so it
>   withdraws nothing and admits nothing new in the nullary case;
> - it does **not** duplicate Fence 1's argument-admissibility check.
>   `uf_args_supported` runs unconditionally on the same raw assertions
>   immediately after, at `lib.rs:910`. `fenced` is explicitly **not sufficient
>   on its own**, and its doc-comment now states that caller obligation.
>
> After it, the same probe decides (`unknown` → `sat`, z3 and cvc5 agreeing —
> the one authorized verdict flip in this slice) and the gate reads 94/94.
>
> The general lesson: "one change satisfies all N consumers" is a claim about
> the consumer list being complete. Here it was not — a fence that takes raw
> assertions instead of an atom set does not appear in a table organized by
> atom sets.

For the two paths where it does hold, a collected atom is in `bv_set` and each
fence's walk returns at it.

| Guard | Today | Change |
|---|---|---|
| `has_non_bv_theory_atom` (`bv_stage.rs:177`) | non-nullary Bool UF app → fence | **none** — the app is now in `bv_set`, so the walk returns at it |
| `has_non_bvfp_theory_atom` (`fp_stage.rs:303`) | delegates over `fp_atoms ∪ bv_atoms` | **none** — inherits the widened `bv_atoms` |
| `abv_stage::fenced` (`abv_stage.rs:194`), called at `lib.rs:903` | non-nullary Bool UF app → fence | **its own widening** — *added by the correction above*; this fence walks RAW assertions and runs before the abstraction, so it inherits nothing from the collector |
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

**Decision (Task 7): the name is KEPT and the docs rewritten.** Rationale, in
order of weight:

1. **Diff hygiene at the one moment it matters most.** The rename is 9 call
   sites (6 of them outside `bv_stage`) but **28** total occurrences
   (`grep -rn collect_bv_atoms --include=*.rs`, counted at this commit:
   `bv_stage.rs`, `fp_stage.rs`, `abv_stage.rs`, `lib.rs`, `qfufbv_e2e.rs`,
   plus cross-crate prose in `shinri-bv/src/lib.rs` and
   `shinri-bv/src/blast/mod.rs`). Slice 45's final commit lands immediately
   before a fresh-eyes whole-branch review whose job is to spot a pairing or
   fence defect in a soundness path — the failure mode that slice 43 and slice
   44 each shipped past every per-task review. A ~28-site mechanical rename in
   that same diff buys nothing and costs the reviewer signal-to-noise.
2. **The name is defensible; the doc was the actual defect.** "BV atoms" reads
   correctly as "the BV stage's atoms" — the set the bit-blaster owns — and
   that is exactly what the function returns. What was genuinely wrong was the
   module doc, which named BV (dis)equality inclusion as *the* subtlety.
3. **It would strand the committed record.** The slice-44 spec on `main` and
   several cross-crate comments cite the function by name as the soundness
   anchor; renaming either invalidates those citations or drags them into this
   diff.

**What was written instead**, since three subtleties now exist and the brief's
"both" undercounts. The module doc (`bv_stage.rs:1`) states each with its
direction of load-bearing-ness:

1. BV (dis)equalities are **included**, for soundness — the pre-existing
   `classify_equality`/EUF argument;
2. non-nullary Bool-result uninterpreted applications are **included**, for
   completeness — this slice;
3. nullary Bool applications are **excluded**, for soundness *on the ABV path*
   — live as of Task 5, and easy to misread as tidiness (full argument at the
   arm).

Plus the consequence that motivates `arg_term_blastable`: a collected atom is a
**leaf** to `has_non_bv_theory_atom`, so collecting a Bool UF application also
hides its argument subtrees from the foreign-theory fence. The function's own
doc-comment leads with "collect the Bool-sorted atoms the BIT-BLASTER OWNS —
despite the name, this is no longer 'atoms with a BV operator on top'", so a
reader who arrives at the call site rather than the module header still gets
the correction. Success criterion 7 is met by re-documentation, the second of
the two permitted branches.

*A future slice that touches this area for other reasons should do the rename
then, when it can land alone.*

## 5. The one new risk

A collected atom is a **leaf** in `has_non_bv_theory_atom`'s walk — it returns
without descending. Making Bool UF apps collectible therefore hides their
argument subtrees from the foreign-theory fence, which previously saw them.

Fence 1 is the backstop: an admitted application's arguments must be BitVec-
(or, on the FP path, FP-) sorted, so nothing Int-, Array-, String-, or
DT-sorted can hide there. But **Fence 1 checks argument sorts, not
blastability**. A BitVec-sorted `(select a i)` passes by sort while the pure-BV
blaster has no arm for it.

> **CORRECTED during implementation (Task 6), after measurement.** As designed,
> this section predicted:
>
> > The expected resolution is that `uses_arrays` routes any such query to
> > `abv_stage` before the pure-BV path is reached, and that `abv_stage`'s
> > abstraction replaces `select`/`store` with fresh BitVec symbols *before*
> > `collect_bv_atoms` runs on `abs.assertions` — making the shape unreachable.
>
> **That prediction is false, and the audit took the code-change branch.** The
> error is the routing predicate's name. There is no general `uses_arrays`. The
> real predicate is `abv_stage::uses_arrays_over_bv` (`lib.rs:902`), and via
> `is_bv_array` (`abv_stage.rs:30-35`) it claims a query only when the array is
> BV-indexed **and** BV-valued. For that shape the prediction is exactly right,
> and the mechanism is as described. But `(Array Int (_ BitVec 8))` makes
> `uses_arrays_over_bv` **false**, so the query escapes to the pure-BV path
> (`lib.rs:1007`), where nothing abstracts anything — while `(select a i)` is
> still BitVec-8-**sorted** and so passed Fence 1's sort check.
>
> Measurement (four probes, both profiles, cross-checked against z3 4.16.0 and
> cvc5 1.3.4) found two things, of different provenance:
>
> - `(f (select a i))` over an Int-indexed array **panicked on `main`** —
>   pre-existing, and exactly what this section predicted for slice 44's
>   already-shipped BitVec-result arm;
> - `(p (select a i))` over the same array answered a sound `unknown` on `main`
>   and **panicked at the slice-45 branch tip** — a regression this slice
>   introduced, and precisely this section's "one new risk" realised: Task 3's
>   widening made the application a collected atom, hence a leaf the
>   foreign-theory fence no longer descends into.
>
> So the second branch below — "the fix is a fence" — is what shipped:
> `bv_stage::arg_term_blastable`, called from `walk_uf_args`. It rejects a UF
> argument whose subtree contains a `select`/`store` over a **non-BV** array,
> and (round 1) an `fp.to_ubv`/`fp.to_sbv` where the path's sink has no arm for
> it. Both exemptions are **conditional in both directions**: an unconditional
> rejection would have flipped shapes that decide today to `unknown`, the one
> thing §2.1 forbids with no exception list. Full evidence in §8.4.
>
> The general lesson, and why slice 38's rule earned its keep again: a
> reachability argument that names the wrong predicate reads exactly like one
> that names the right predicate. Only the measurement told them apart.

Two things to note about its blast radius. First, it applies **equally to slice
44's already-shipped BitVec-result arm** — `(f (select a i))` has the same
shape — so part of what the audit finds is a pre-existing condition this slice
surfaces rather than introduces. *(Measured: only part. `(f (select a i))` is
pre-existing; the Bool-result twin `(p (select a i))` is a regression slice 45
introduced, because only slice 45 makes it a collected atom. The audit had to
tell the two apart — see the correction above and §8.4.)* Second, if the
routing argument does not hold, the fix is a fence (reject an application whose
argument is not a blastable word, not merely a well-sorted one), which costs
completeness on a shape ~~nobody has yet demonstrated~~ *(demonstrated by Task
6: four probes, both profiles; the cost is bounded to shapes that previously
**panicked**, so no verdict was lost — §8.4's verdict-flip audit)*.

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

  **`qfbv_oracle.rs` / `differential_qf_bv_small`** — measured at commit
  `e1baa3bb` (pre-fix tree: `slice45-bool-uf-congruence` branch tip before
  this task's commit), debug profile (nextest default), via:

  ```
  cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_bv_small)' --no-capture
  ```

  Discovered test count: 1 (confirmed non-zero — not a 0-test skip). Result:
  **FAIL**, on the family-scoped decidedness assertion, exactly as predicted
  by the task brief (not on the `pred_total > 0` line). Verbatim panic:

  ```
  thread 'differential_qf_bv_small' (1686222) panicked at crates/shinri-solver/tests/qfbv_oracle.rs:596:5:
  Bool-result predicate family decided 0/89 — more than half must decide. Pre-slice this is 0/N by construction (the bv_stage foreign-theory fence); post-slice a low rate means the collection widening or a fence is rejecting instances it should admit
  ```

  `pred_decided`/`pred_total` = **0/89** (out of 200 total generator
  iterations; 89 of them happened to emit at least one Bool-result predicate
  application). Run summary: `sat=78 unsat=33 unknown=89`, width breakdown
  `w4=68 w8=60 w16=72`. The zero-disagreement soundness check never fires —
  every predicate-bearing instance is `Unknown` pre-slice (the `bv_stage`
  foreign-theory fence rejects the new `p`/`q` uninterpreted-Bool-result
  applications), which is exactly why a plain differential extension alone
  would have been green: `Unknown` is a harness skip, not a failure. The
  `fp_oracle.rs` and `qfabv_oracle.rs` pre-slice measurements are recorded by
  Tasks 4 and 5, which mirror this same shape.

  **`fp_oracle.rs` / `differential_qf_fp_add_sub`** — measured at commit
  `f4079ec5` (Task 3's tip) with this task's Step-1 and Step-6 TEST changes
  applied but the Step-3 `Lowerer::atom` dispatch fix REVERTED (`git
  checkout -- crates/shinri-fp/src/lower.rs`), debug profile (nextest
  default), via:

  ```
  cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_fp_add_sub)' --no-capture
  ```

  Discovered test count: 1 (confirmed non-zero). Result: **FAIL** — and,
  unlike the `qfbv_oracle` row above, NOT on the decidedness assertion. It is
  a **PANIC**, which is exactly the §3.2(a) claim this task exists to test:

  ```
  thread 'differential_qf_fp_add_sub' (4051127) panicked at crates/shinri-fp/src/lib.rs:432:18:
  internal error: entered unreachable code: blast_atom: FP atom Uninterpreted(SymbolId(3)) out of slice-1 scope
  ```

  The run dies at 1.47s, before any counter is printed, so no pre-fix
  `pred_decided`/`pred_total` fraction exists for this family — the process
  never reaches the assertion. `Lowerer::atom` (`crates/shinri-fp/src/lower.rs`)
  dispatched on the FIRST OPERAND's sort, so `(p <fp-term>)` routed to
  `blast_fp_atom`, which has no uninterpreted-application arm. The same panic,
  same line, same message (with `SymbolId(0)`) is what the two `qfufbv_e2e`
  probes below produce pre-fix. **This is the one slice-45 path that panics
  rather than degrading to `unknown`, and the measurement confirms it.**

  **`qfabv_oracle.rs` / `qfabv_matches_z3`** — measured by Task 5 at commit
  `b5b7ffa3` (Task 4's tip) with Task 5's Step-3 tests in place but the
  `abv_stage::fenced` widening REVERTED, debug profile (nextest default), via:

  ```
  cargo nextest run -p shinri-solver --features oracle -E 'test(qfabv_matches_z3)' --no-capture
  ```

  Discovered test count: 1 (confirmed non-zero). Result: **FAIL** on the
  family-scoped decidedness assertion. Verbatim panic:

  ```
  thread 'qfabv_matches_z3' panicked at crates/shinri-solver/tests/qfabv_oracle.rs:544:5:
  Bool-result predicate family decided 0/94 — more than half must decide. Pre-slice this is 0/N by construction (the abv_stage foreign-theory fence); post-slice a low rate means the collection widening or a fence is rejecting instances it should admit
       Summary [   3.223s] 1 test run: 0 passed, 1 failed, 0 skipped
  ```

  `pred_decided`/`pred_total` = **0/94** — not "a low rate" but *every*
  predicate-bearing instance fencing, because `abv_stage::fenced` rejected the
  whole query at `lib.rs:903`. Note what this row measures that the other two
  do not: it was taken with Tasks 1–4 **already applied**, so its `0/94` is not
  a pre-slice baseline but the evidence that Task 3's collector widening never
  reached this path at all — the §4 premise correction above.
- 8.2 — T1: the post-slice decided fractions and the thresholds chosen.

  **All three, re-measured together at the slice tip (Task 7).** Debug profile
  (nextest default), on the finished branch — `7b69df2f` plus Task 7's
  doc-and-test-only edits, which cannot move a solver verdict. One command, so
  the three numbers come from one tree:

  ```
  $ cargo nextest run -p shinri-solver --features oracle --no-capture \
      -E 'test(differential_qf_bv_small) + test(qfabv_matches_z3) + test(differential_qf_fp_add_sub)'

      Starting 3 tests across 27 binaries (627 tests skipped)
  differential_qf_fp_add_sub: sat=193 unsat=7 unknown=0 pred_total=83 pred_decided=83
          PASS [  27.022s] (1/3) shinri-solver::fp_oracle differential_qf_fp_add_sub
    slice-45 Bool-result predicate family: decided=94/94
          PASS [   3.497s] (2/3) shinri-solver::qfabv_oracle qfabv_matches_z3
    slice-45 Bool-result predicate family: decided=89/89
          PASS [   5.529s] (3/3) shinri-solver::qfbv_oracle differential_qf_bv_small
       Summary [  36.050s] 3 tests run: 3 passed, 627 skipped
  ```

  Discovered count **3** — confirmed non-zero, and `--no-capture` is what makes
  the counter lines visible at all (nextest swallows stdout on a passing test,
  so without it the run is green and says nothing).

  | oracle | gate test | pre-slice | post-slice | threshold |
  | --- | --- | --- | --- | --- |
  | `qfbv_oracle` | `differential_qf_bv_small` | **0/89** (§8.1) | **89/89 = 100%** | `pred_decided > pred_total / 2` |
  | `qfabv_oracle` | `qfabv_matches_z3` | **0/94** (§8.1) | **94/94 = 100%** | `pred_decided > pred_total / 2` |
  | `fp_oracle` | `differential_qf_fp_add_sub` | **PANIC**, no fraction exists (§8.1) | **83/83 = 100%** | `pred_decided > pred_total / 2` |

  **No threshold moved off `> total / 2`,** and that is deliberate rather than
  incidental. §6.1 authorized moving it only to keep the assertion off a flaky
  boundary; all three families measured at 100%, which is nowhere near the
  boundary, so the mirror-the-global-guard default stands unmodified in every
  case. §6.1's other instruction — "never tune it upward to whatever the run
  happened to produce" — is why these stay at half rather than being ratcheted
  to 100%: the gate exists to catch a family that *silently stops deciding*,
  and a 100% gate would additionally fail on any unrelated instance that fences
  for a legitimate reason (a budget trip, a generator-emitted Int argument),
  making it a flakiness source rather than a signal. The distance between the
  threshold (>50%) and the measurement (100%) is headroom, not slack.

  Each of the three was independently shown to FAIL on the tree that lacked its
  fix (§8.1) — so none is green-by-omission, the
  `oracle-generator-blind-spots` failure mode this gate design exists to close.

  **`fp_oracle.rs` / `differential_qf_fp_add_sub`** — measured at Task 4's
  commit, debug profile, same command as above. Result: **PASS** in 29.13s
  (31.40s in the full-binary parallel run). Summary line:

  ```
  differential_qf_fp_add_sub: sat=193 unsat=7 unknown=0 pred_total=83 pred_decided=83
  ```

  Decided fraction for the Bool-result predicate family: **83/83 = 100%**
  (up from an unmeasurable pre-fix panic). Threshold chosen: `pred_decided >
  pred_total / 2`, identical to the `qfbv_oracle` gate — the point is to catch
  a family that silently stops deciding, not to pin 100%. `unknown=0` across
  all 200 iterations also shows the unconditional `(declare-fun p ...)` added
  to the preamble fences nothing when no application of `p` appears.

  **Two `qfufbv_e2e` probes** (debug profile, this task's commit):
  `fp_argument_predicate_congruence` and
  `nan_arguments_are_congruent_for_a_predicate`, 2 discovered, both **PASS**
  (`unsat`); both **panicked** at `crates/shinri-fp/src/lib.rs:432:18` before
  the fix.

  **Oracle caveat — z3 4.16.0 is WRONG on the NaN probe; cvc5 is right.**
  Three-way cross-check of the second probe
  (`fp.isNaN a ∧ fp.isNaN b ∧ p(a) ∧ ¬p(b)`):

  | solver | verdict |
  | --- | --- |
  | shinri (post-fix) | `unsat` |
  | cvc5 1.3.4 | `unsat` |
  | z3 4.16.0 | `sat` ← **defective** |

  z3's `sat` is refuted by z3 itself: asked for its own model it returns
  `p := λx. true` and then evaluates `(p b) = true` — while the query asserts
  `(not (p b))`. The model does not satisfy the input. z3 also agrees the two
  arguments are equal (`fp.isNaN a ∧ fp.isNaN b ∧ a ≠ b` is `unsat` for z3)
  and returns `unsat` once `(= a b)` is asserted SYNTACTICALLY — so the defect
  is z3's FP+UF congruence closure failing on an ENTAILED rather than stated
  equality. Ground truth is `unsat` (SMT-LIB `FloatingPoint` has exactly one
  NaN value), so the pinned expectation is correct and shinri matches cvc5.
  The first probe is unanimous: shinri / z3 / cvc5 all `unsat`.

  This matters beyond the probe, because `fp_oracle` uses **z3** as its
  differential oracle: a generated instance that makes two FP arguments
  NaN-equal but bitwise-distinct under one predicate could produce a spurious
  "DISAGREEMENT" panic that is z3's fault, not ours. It did NOT occur at the
  `differential_qf_fp_add_sub` seed (200 iterations, zero disagreements), but
  the exposure is real and should be revisited if that oracle ever reports a
  shinri-`unsat`/z3-`sat` split on a predicate-bearing instance.
- 8.3 — T5: `get-value` and `get-model` behaviour on a Bool UF app.

  **Measured, not predicted.** RELEASE profile (`cargo build --release`), at
  commit `7b69df2f` (the branch tip before this task; the doc-only edits in
  this task's commit cannot change it, and the pinning test passes identically
  in the DEBUG profile). Query and verbatim output:

  ```
  (set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)
  (declare-fun x () (_ BitVec 8))(assert (p x))(check-sat)
  (get-value ((p x)))(get-model)

  success
  success
  success
  success
  sat
  (((p x) ?))
  ((define-fun x () (_ BitVec 8) #x00))
  ```

  Three separate facts, and the second is the one §6.5 existed to catch:

  1. **The query now decides `sat`.** Pre-slice it was `unknown` (§1, Q2), so
     `get-value` returned the `model is not available` error (`lib.rs:438`) and
     neither channel was observable at all. That is why this had to be measured
     after the slice, not predicted before it.

  2. **The label renders; the value channel does NOTHING, and says so.**
     `display_term` (`tseitin.rs:483`) renders the application structurally, so
     the label is `(p x)` as §6.5 predicted. `format_value` (`lib.rs:585`) then
     returns `None` — it resolves a **0-arity** symbol through `last_model`,
     and `(p x)` is not one — and `get-value` prints `?` (`lib.rs:453`).

     `?` is the established visible placeholder for "no value", the same one
     slice 43 §5 introduced for a symbol whose value no channel holds. This is
     the **correct** outcome by slice 43's rule, and it is pinned as such: the
     failure mode that rule guards against is rendering absence as a confident
     default, which would here mean printing `true` because `(p x)` is
     asserted. `(p x)` being asserted is exactly why a default would look
     plausible and exactly why it must not be synthesized here — the blaster
     knows the literal's polarity, but nothing plumbs a blaster literal back to
     `format_value`, and inventing the answer from the assertion text would be
     answering from the question. Slice 45 leaves the value channel alone; the
     test pins that it does nothing, plainly.

  3. **`get-model` still omits `p`.** `format_model` filters `d.arity == 0`
     (`lib.rs:540`), so an arity-1 symbol is structurally absent no matter what
     the blaster learned — unchanged by this slice, and §2 records it as
     deliberately out of scope. A function graph needs congruence-class
     enumeration (slice 43 §5, still open). The **argument** `x` does get a
     value, by the mechanism slice 44 §7.5 measured: congruence forces the
     argument word to be blasted, so it enters `Blaster.cache` and reaches
     `exported_var_bits`.

  Pinned by `qfufbv_e2e::get_value_on_a_predicate_application` (debug profile,
  1 discovered, PASS). The test pins the `get-value` string exactly and the
  `get-model` **shape** — that `p` is absent and that `x` has some 8-bit value
  — but not the witness `#x00`: `(p x)` constrains nothing about `x`, so every
  8-bit value is a legitimate model and pinning the solver's current pick would
  pin an implementation detail rather than a contract.
- 8.4 — §5: the Fence-1 blastability audit's conclusion and its evidence.

  **Conclusion: §5's expected resolution is FALSE. Step 4's second branch was
  taken — a blastability check was added to `walk_uf_args`.** The routing
  argument holds only for the array shape the router actually claims, and the
  audit additionally found that slice 45 had itself turned a sound `unknown`
  into a panic. Both are measured below.

  **The routing predicate, verified at HEAD.** It is
  `abv_stage::uses_arrays_over_bv` (`crates/shinri-solver/src/lib.rs:902`), not
  a general `uses_arrays`. Its `walk_uses` helper (`abv_stage.rs:44-63`) fires
  only when a `select`/`store`/array-(dis)equality has an array operand that
  `is_bv_array` accepts — **BV-indexed AND BV-valued** (`abv_stage.rs:30-35`).
  When it fires, `shinri_abv::abstract_arrays`
  (`crates/shinri-abv/src/abstraction.rs:38`) mints one fresh BV symbol per
  distinct `select` and `subst` (`:72-107`) rewrites it throughout — and both
  `shinri-abv`'s `collect` (`collect.rs:65-67`) and `subst` (`abstraction.rs:95-98`)
  recurse into children **generically**, so a `select` buried in a UF
  application's arguments is substituted like any other. `collect_bv_atoms`
  then runs on `abs.assertions` (`abv_stage.rs:370`), by which point the
  argument is a plain word. So for BV arrays §5's argument is CORRECT.

  It fails for every other array shape. `(Array Int (_ BitVec 8))` makes
  `uses_arrays_over_bv` false, so the query takes the pure-BV path
  (`lib.rs:1007`) where nothing abstracts anything — and `(select a i)` is
  still BitVec-8-**sorted**, so Fence 1's sort check admitted it.

  **Measurement.** Four probes, run on BOTH profiles. Pre-slice column measured
  at commit `e1baa3bb` (`main`) in a separate worktree; HEAD column at commit
  `99b282af` (branch tip before this task); post-fix at this task's commit.
  Commands:

  ```
  cargo build --release && cargo build
  ./target/{release,debug}/shinri /tmp/claude-1000/-workspace/<probe>.smt2
  mise exec -- z3 <probe>.smt2 ; mise exec -- cvc5 <probe>.smt2
  ```

  | probe | array sort | result sort | `main` e1baa3bb | HEAD 99b282af | post-fix | z3 4.16.0 | cvc5 1.3.4 |
  | --- | --- | --- | --- | --- | --- | --- | --- |
  | `audit-bv`   | `(Array (_ BitVec 4) (_ BitVec 8))` | BitVec | `sat` | `sat` | `sat` | `sat` | `sat` |
  | `audit-bool` | `(Array (_ BitVec 4) (_ BitVec 8))` | Bool | `unknown` | `sat` | `sat` | `sat` | `sat` |
  | `escape-bv`  | `(Array Int (_ BitVec 8))` | BitVec | **PANIC** | **PANIC** | `unknown` | `sat` | `sat` |
  | `escape-bool`| `(Array Int (_ BitVec 8))` | Bool | `unknown` | **PANIC** | `unknown` | `sat` | `sat` |

  Release and debug agreed on every cell — the panic is an `unreachable!`, not
  a `debug_assert!`, so it fires in the shipping profile too. Verbatim, on both
  profiles at HEAD:

  ```
  thread 'main' panicked at crates/shinri-bv/src/blast/mod.rs:624:22:
  internal error: entered unreachable code: non-BV builtin reached blast_word
  ```

  (At `e1baa3bb` the identical message is reported at `mod.rs:599:22` — the same
  arm, before slice 45 Task 2 added lines to that file.)

  Two findings, of different provenance:

  1. **`escape-bv` is pre-existing**, exactly as §5 predicted for slice 44's
     shipped BitVec-result arm: it panicked identically on `main`. The fix
     upgrades it from a panic to a sound `unknown`.
  2. **`escape-bool` is a regression slice 45 introduced.** `main` answered a
     sound `unknown`; HEAD panics. The mechanism is precisely §5's "one new
     risk", realised: pre-slice, the Bool-result application was not a
     collected BV atom, so `has_non_bv_theory_atom` saw a foreign Bool-sorted
     atom and fenced. Task 3's widening of `collect_bv_atoms` makes it a
     collected atom — hence a **leaf** the fence no longer descends into — so
     the foreign `select` in its arguments stopped being seen, and Fence 1's
     sort check was, as §5 warned, not a sufficient backstop.

  **The fix.** `bv_stage::arg_term_blastable` (called from `walk_uf_args`)
  rejects a UF argument whose subtree contains a `select`/`store` over a
  non-BV array. The exemption for BV arrays is load-bearing in the opposite
  direction: an unconditional rejection would fence `audit-bv` and `audit-bool`
  to `unknown`, a **decided → unknown** regression forbidden by §2.1 and a
  regression against slice 44's shipped behaviour. It is safe because Fence 1
  runs on RAW assertions at `lib.rs:910` (still containing the `select`) only
  on the ABV path, where the abstraction removes it before blasting; on the
  pure-BV (`:1007`) and FP/mixed (`:1095`) paths `uses_arrays_over_bv` was
  false, so no BV-array `select` can be present and the predicate rejects every
  array access there.

  **Completeness of the check (CORRECTED in review round 1).** Enumerating
  `BuiltinOp` (`crates/shinri-core/src/term.rs`) against `blast_bv_word`'s
  dispatch (`crates/shinri-bv/src/blast/mod.rs:448-628`), the BV-**sorted**
  heads with no arm are exactly four: `Select`, `Ite`, `FpToUbv`, `FpToSbv`.

  - `Ite` is excluded upstream and unconditionally — `word_norm.normalize`
    (`lib.rs:759`) eliminates every BV-sorted `ite` BEFORE any fence or routing
    decision runs.
  - `Select`/`Store` is gated by array sort, as above.
  - **`FpToUbv`/`FpToSbv` is gated by `allow_fp_args`.** The first version of
    this section claimed they "force `solver_uses_fp`, routing to the FP path
    where `Lowerer::word` has arms for them", and concluded `Select` was the
    only reachable shape. **That claim is FALSE and the conclusion with it.**
    It holds for the pure-BV path (`lib.rs:1007` is guarded by
    `uses_bv && !uses_fp`) but NOT for the ABV path: the ABV gate at
    `lib.rs:902` runs BEFORE any FP routing and `return`s in every arm, and
    `abv_stage` blasts with a bare `shinri_bv::Blaster` that has no FP sink —
    as the Fence-1 comment at `lib.rs:905-908` already stated. Measured at
    commit `4a3701e8` (this task's first commit), release AND debug:

    ```
    (set-logic ALL)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
    (declare-fun i () (_ BitVec 4))(declare-fun x () Float32)
    (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
    (assert (= (select a i) (f ((_ fp.to_ubv 8) RNE x))))(check-sat)

    thread 'main' panicked at crates/shinri-bv/src/blast/mod.rs:624:22:
    internal error: entered unreachable code: non-BV builtin reached blast_word
    ```

    The argument is BitVec-8-sorted (passes the sort check) and contains no
    `select` (passes the array half). `abv_stage::fenced` cannot help either:
    `(fp.to_ubv rm x)` is not Bool-sorted, so `walk_fence` reaches only its
    descend-into-a-non-Bool-term arm (`abv_stage.rs:201-203`) and its kids —
    `rm` and `x` — are themselves non-Bool-sorted, so each takes that same arm
    over an EMPTY child list, and `Iterator::any` on an empty iterator is
    `false`.

    *(Citation corrected in Task 7. This sentence originally cited
    `abv_stage.rs:198-200`, which is the WRONG ARM — `:198-200` is the "any
    other Bool-sorted application → `true`" arm, which `(fp.to_ubv rm x)` never
    reaches because it is not Bool-sorted; the descend arm is `:201-203`. The
    same wording originally said "the kids bottom out at constants", which is
    loose: a nullary uninterpreted symbol such as `rm` or `x` is an `App` node
    with an empty child list, NOT a `TermNode::Const`, so it returns `false`
    via the empty-`kids` `any` rather than via the `Const` arm. The substantive
    conclusion — that `fenced` cannot substitute for the blastability check —
    was independently traced and confirmed and is unaffected; this is a
    citation fix, not an argument change.)*

    The gate must be conditional in both directions. `Lowerer::word`
    (`crates/shinri-fp/src/lower.rs:52-73`) intercepts exactly these two ops and
    routes them to `blast_fp_to_bv`, so on the FP/mixed path the shape decides:
    `(= (f ((_ fp.to_ubv 8) RNE x)) #x2a)` is `sat` on both profiles, z3 4.16.0
    and cvc5 1.3.4 agreeing. Rejecting unconditionally would flip that to
    `unknown` — the same decided → unknown trap the `select` exemption avoids.
    `allow_fp_args` is already precisely "an FP sink exists", so it is the
    correct discriminator rather than a proxy for one. Post-fix, both profiles:
    the ABV variant is `unknown` (a completeness cost on a shape that
    previously crashed — z3 and cvc5 say `sat`, so no verdict was lost), the FP
    variant stays `sat`.

    Provenance: **pre-existing, not slice-45-introduced** — the no-UF variant
    panics identically, so it belongs to the same class as the out-of-scope
    hole below. Unlike that hole, however, it sits squarely inside Fence 1's
    jurisdiction and inside what the fence's own doc-comment asserts it covers,
    so it is fixed here rather than deferred.

  **Verdict-flip audit.** The only flips are `escape-bv` panic → `unknown` and
  `escape-bool` panic → `unknown`. No `sat`/`unsat` flip, and no decided →
  `unknown`: `escape-bool`'s `unknown` restores `main`'s answer, and
  `escape-bv` had no verdict to lose. Pinned as four `qfufbv_e2e` tests plus
  four `bv_stage` unit tests.

  **One Task-5 unit test needed updating.**
  `abv_stage::tests::fence_descends_into_predicate_arguments_to_find_a_foreign_select`
  asserted as a *precondition* that Fence 1 ADMITS its shape, to show the test
  exercised `walk_fence`'s recursion rather than Fence 1. Fence 1 now rejects
  that shape too, so the assertion was inverted with a comment: the test is
  still non-vacuous because it calls `fenced` directly, independently of Fence
  1. The two fences are now independent lines of defence over one shape, which
  is what `fenced`'s doc-comment ("NOT sufficient on its own") already declared.

  **OUT OF SCOPE, REPORTED NOT FIXED — a broader pre-existing hole.** The same
  panic reproduces with **no uninterpreted application anywhere**:

  ```
  (set-logic ALL)(declare-fun a () (Array Int (_ BitVec 8)))(declare-fun i () Int)
  (assert (= (select a i) #x2a))(check-sat)     → PANIC (mod.rs:624)
  (assert (bvult (select a i) #x2a))(check-sat) → PANIC (mod.rs:624)
  ```

  Measured at `main` (`e1baa3bb`) and at this task's commit, both profiles:
  panics in all four cells. Fence 1 has no jurisdiction — `walk_uf_args` only
  inspects UF *arguments*. The cause is one level up: `has_non_bv_theory_atom`
  treats a collected BV-sorted `Eq`/predicate atom as an opaque leaf, so a
  foreign `select` inside it is never fenced. This predates slice 44 and is a
  general "the pure-BV path admits an unblastable BV-sorted term" hole; where
  the general blastability fence belongs (`collect_bv_atoms`,
  `has_non_bv_theory_atom`, or a new pre-lowering check) is an architectural
  decision this slice did not take.
- 8.5 — T6: the full unfiltered oracle summary and the PR-tier wall clock.

  Both measured at the slice tip (`7b69df2f` + Task 7's doc-and-test-only
  edits), debug profile (nextest default), foreground, output captured.

  **Full UNFILTERED oracle suite.** No `-E` filter at all — slice 40's lesson
  is that a filtered run silently skips `qfs_differential` and nearly shipped a
  string `Sat`→`Unknown` regression.

  ```
  $ time cargo nextest run -p shinri-solver --features oracle

       Summary [1084.012s] 627 tests run: 627 passed (6 slow), 3 skipped

  real  18m6.828s
  user  38m48.059s
  sys   3m14.224s
  ```

  **627 passed, 0 failed, 0 disagreements.** The 3 skipped are the `#[ignore]`d
  nightly-tier tests. Every oracle binary is represented — `qfs_differential`
  90, `fp_oracle` 43, `qfdt_oracle` 16, `oracle` 13, `ite_oracle` 3,
  `qfax_oracle` 2, `nary_oracle` 2, `qfbv_oracle` 1, `qfabv_oracle` 1,
  `nary_arith_oracle` 1.

  **The feature flag was verified to have taken effect, not assumed.** Without
  `--features oracle` these binaries are `#![cfg]`-compiled away and the run is
  green while testing none of them:

  ```
  $ cargo nextest list -p shinri-solver                     → 483 tests
  $ cargo nextest list -p shinri-solver --features oracle   → 630 tests
  ```

  **147 tests** exist only under the flag; 627 ran + 3 `#[ignore]`d = 630. A
  483-test run would have read as green and been no coverage at all.

  **PR tier (blocking) wall clock.**

  ```
  $ time cargo nextest run --all

       Summary [ 238.555s] 1369 tests run: 1369 passed (5 slow), 7 skipped

  real  4m0.694s
  user  18m21.243s
  sys   0m47.526s
  ```

  **4m00.7s against a 10–15 min budget and a 20 min CI hard cap** — comfortably
  inside, with the slice's new tests included. `mise run test` is exactly this
  command, so this is the blocking tier and not a proxy for it. The §2.1 gates
  all discovered non-zero counts inside it: `qfbv_witnesses` 33, `script_e2e`
  73, `qfdt_e2e` 21, `qfuf_e2e` 2, and `qfufbv_e2e` 37 (the slice's own file).

  Slowest blocking-tier test: `shinri-fp blast::rem::tests::
  rem_float32_specials_and_random` at **238.2s = 3.97 min**, inside the
  5-minute `#[ignore]` rule. Nothing on this tier exceeds it.

  **`UF_CONGRUENCE_BUDGET` unchanged, and the shared-budget claim is now
  measured rather than assumed** — §4's open question. Confirmed by grep:

  ```
  $ grep -rn "UF_CONGRUENCE_BUDGET" --include=*.rs .
  crates/shinri-solver/src/bv_stage.rs:690:/// UF_CONGRUENCE_BUDGET = pairs(440) * 96 = 96,580 * 96 = 9_271_680.
  crates/shinri-solver/src/bv_stage.rs:691:pub const UF_CONGRUENCE_BUDGET: u64 = 9_271_680;
  crates/shinri-solver/tests/qfufbv_e2e.rs:53:                  // the calibrated UF_CONGRUENCE_BUDGET (9_271_680, k=440 --
  crates/shinri-solver/src/lib.rs:916:                > crate::bv_stage::UF_CONGRUENCE_BUDGET
  crates/shinri-solver/src/lib.rs:1021:                > crate::bv_stage::UF_CONGRUENCE_BUDGET
  crates/shinri-solver/src/lib.rs:1100:                > crate::bv_stage::UF_CONGRUENCE_BUDGET

  $ git show main:crates/shinri-solver/src/bv_stage.rs | grep -n "pub const UF_CONGRUENCE_BUDGET"
  444:pub const UF_CONGRUENCE_BUDGET: u64 = 9_271_680;
  ```

  Exactly one definition, three consumers (the three routing paths' Fence 2),
  and one test-comment citation. The three `lib.rs` sites are the pure-BV, ABV
  and FP/mixed gates — the same three §2 names as the slice's scope, which is
  what makes "global, shared" a checked statement rather than a description.

  Byte-identical to `main`'s slice-44 calibrated value: still ONE global
  budget, still `9_271_680`, no second budget and no per-family budget. With
  Bool-result applications now joining the same `pairs(k) × (arg_bits +
  res_bits)` sum at `res_bits = 1`, the three predicate families measured
  **89/89, 94/94 and 83/83 decided** (§8.2) — i.e. the added population does
  not trip Fence 2 — and the tier came in at 4m00.7s. This is slice 42's
  lesson answered: the claim that the existing budget still holds with
  predicates in the mix rested on a plausible premise until a measured gate
  ran, and the gate has now run.

  **Verdict-flip audit across both tiers: no forbidden flip.** 627/627 and
  1369/1369 passed with no test expectation altered by this task, so no
  `sat`→`unsat`, no `unsat`→`sat`, and no decided→`unknown` anywhere in either
  suite. §2.1's "no named-exception list" survives the sweep intact.
