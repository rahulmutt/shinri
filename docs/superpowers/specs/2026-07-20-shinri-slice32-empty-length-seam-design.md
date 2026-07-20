# Slice 32 design — the empty-length seam: `len(x)=0 ⇒ x=""` as a leaf-variable tautology

**Date:** 2026-07-20
**Status:** Approved design, pre-implementation
**Scope:** `shinri-str` — emit a two-literal emptiness tautology per bare
string variable so an arith-derived `len(x)=0` grounds `x=""` in the string
theory's EUF.

## 1. Problem — arith knows the length is zero; the string theory never hears it

The string theory reasons over word equations in EUF; lengths live in arith,
exchanged across the Nelson–Oppen Int seam. The seam is one-way in the place
that matters: when arith derives `len(x) = 0`, nothing tells the string
theory that `x = ""`.

There is deliberately **no** `len=0 ⇒ empty` rule in `cx.eq`. `length.rs`
documents the omission twice (`length.rs:157`, `length.rs:254`): emitting an
empty-link for every `str.len` term — including every fresh F-split skolem's
length — floods the shared-Int MBTC / N-O exchange and livelocks concat+length
queries. What exists instead is narrower:

- an on-demand guarded lemma `(s≠"") → len(s)≥1`, emitted only for `s ≠ ""`
  disequalities (`lib.rs:976` and the `≥1` separation channel), and
- `len_class_zero`, a *read* of the shared engine inside the disequality loop
  (`lib.rs:506-508`) — never an emitted lemma, precisely so it cannot flood
  the seam.

Neither closes the direction we need. `len_class_zero` only fires where the
disequality loop already looks; the guarded lemma runs the other way
(non-empty ⇒ length ≥ 1). Nothing converts an arith fact into an EUF merge.

This was diagnosed independently as **wall 3** of the slice-31 four-wall
analysis (slice-31 spec §11): "Grounding the recursion needs `|tail|=0 ⇒
tail=""`, but that fact lives only in arith and never reaches the string
theory's EUF in time … *This wall is fixable* — emitting the tautology
`(or (= x "") (>= (str.len x) 1))` per skolem lets arith's `len(x)=0`
propagate `x=""` into EUF, and it worked in the spike."

Slice 31 banked it. This slice cashes it, and widens it from the spike's
skolem-only shape to all bare string variables, so the win is user-visible
rather than dormant behind the still-standing order fence.

### 1.1 Emission mechanism

One clause per qualifying term, through the existing axiom pump in
`StrSolver::check` (`lib.rs:462-504`) — the same loop that already walks
`self.len_terms` and returns `TCheck::Split` one axiom at a time:

```
(or (= x "") (>= (str.len x) 1))
```

Both disjuncts are theory-visible in the right places: `(= x "")` is a string
equality that routes to EUF, and `(>= (str.len x) 1)` is an arith atom that
routes to Arith. Under an arith-derived `len(x) ≤ 0` the second disjunct is
false, so unit propagation forces `x = ""` into EUF — which is exactly the
grounding the word-equation engine is missing.

**Qualifier — bare leaf variables, once each.** A term qualifies iff it is
`str.len(a)` where `a` is a bare uninterpreted nullary string symbol
(`TermNode::App { op: Op::Uninterpreted(_), .. }` with no children, and
`string_const_value(a).is_none()`). This is the same "genuine string
VARIABLE" predicate the empty-residual lemma already uses at `lib.rs:577-586`;
it reuses that shape rather than inventing a second notion of leafness.
Explicitly excluded: concat-length terms, literal lengths, and any compound.
Engine-minted skolems qualify — they *are* bare uninterpreted symbols — which
is how the slice-31 prerequisite gets cashed without a second mechanism.

Emission is deduplicated through the existing `emitted_len_axioms` set, so
each qualifying variable produces the clause at most once per solve. No
preprocessing changes; no new mint-site hooks; nothing outside `shinri-str`.

The clause carries a per-atom phase hint preferring **TRUE** on the
`(>= (str.len x) 1)` disjunct, via the `phases` field on `TCheck::Split`
(`solver_trait.rs:31-36`). Rationale in §2.

## 2. Soundness, flood control, and termination

**Soundness is structural, not argued.** `(or (= x "") (>= (str.len x) 1))`
is valid in the SMT-LIB `String` theory for every string term `x`: a string is
either empty or has length at least one. It is a **tautology**, so it is
entailed at level 0 unconditionally and needs no guard —
`guard: None`, like the other structural axioms in the same loop. This
sidesteps the whole class of hazards that dominates the surrounding code
(`E1` iters 1–3, the `side_clean` guard, the `leaves_all_dl0` antecedent
check): every one of those exists because a *conditional* fact was pinned
unconditionally. A tautology has no antecedents to get wrong, and no branch on
which it fails. There is no new wrong-UNSAT surface.

Verdict-monotonicity follows: adding valid clauses can turn `Unknown` into
`sat`/`unsat` but can never flip `sat ↔ unsat`.

**Flood control is the real risk, and the qualifier is the control.** The
`length.rs:254-259` note is a warning earned by experiment: an empty-link on
*every* `str.len` term livelocks concat+length queries. Two properties keep
this slice on the safe side of that line.

*Volume.* Restricting to bare leaf variables means the clause count is bounded
by the number of distinct string variables (input plus minted), not by the
number of `str.len` terms — concat lengths, the terms that multiply as the
word-equation engine rewrites, contribute nothing. Combined with
`emitted_len_axioms` dedup, total emission is linear in the variable count and
strictly one clause per variable.

*Shape.* The livelock the note describes came from pushing emptiness *into*
the N-O Int exchange as a fact the seam had to carry. This clause is a
disjunction handed to the SAT layer; the `x = ""` merge lands in EUF only when
propagation forces it. Nothing is added to the shared-Int exchange.

**The phase hint makes it on-demand in practice.** Preferring TRUE on
`(>= (str.len x) 1)` means the SAT layer's default guess is "non-empty",
leaving the clause satisfied and dormant. The `x = ""` branch is entered only
when arith's `len(x) ≤ 0` actually refutes the preferred disjunct — so the
clause behaves like a demand-driven rule without needing a value-view seam
into arith. This also cashes the slice-31b phase-hint channel
(`shinri-sat`/`shinri-theory`, task 7.1), which landed reviewed-sound but has
been dormant since — its first load-bearing consumer.

**Termination.** Emission is finite by construction: one clause per variable,
dedup'd, and each emission spends fuel through the existing
`self.fuel.spend()` path before the split is delivered, so the established
budget still bounds the round count. The clause introduces no fresh terms —
`x` and `str.len(x)` both already exist when the term is in `len_terms` — so
it cannot feed the axiom-chain growth that `collect::collect` exists to track.
No new recursion, no fresh skolems, no new measure needed.

**Empirical gate.** Because the flood hazard is empirical rather than
structural, the acceptance bar is empirical too: the concat+length queries the
`length.rs` note was written about must be timed before and after, and the
`script_e2e` suite plus the oracle differential suite (`--features oracle` —
without it the suite compiles to zero tests) must show `Unknown → decided`
flips only, with zero `decided → Unknown` and zero `sat ↔ unsat`.

## 3. Completeness boundary and non-goals (banked)

Stays `Unknown`, by design:

- **Two-symbolic-variable `str.< / str.<=`.** This slice removes wall 3 of
  four. Walls 1, 2, and 4 (total-assignment CDCL, no relevance signal, and
  the intractable code-point arithmetic that is the actual blocker) are
  untouched, and the preprocessing fence stays down. Slice-31 §11's
  prerequisite list is unchanged except that its one "cheap, reusable win"
  is now cashed.
- **Non-leaf emptiness.** `len(x ++ y) = 0 ⇒ x = "" ∧ y = ""` is not
  derived directly; it follows only where the concat-sum axiom plus the leaf
  clauses happen to compose. Compound-term emptiness is banked.
- **Demand-driven emission.** Emitting only when arith has actually derived
  `len(x) ≤ 0` would need a value-view extension to `TheoryCtx` — the same
  seam wall 2 of slice 31 wants. Banked; the phase hint approximates it.
- Standing bank unchanged: slice-28 §8 (conflict-core minimization,
  cross-term / eq-class-aware aggregation, cap-raising), the slice-27
  typed-antecedent refactor, slice-29's approach-C fuel-free constant-length
  propagation, distinct-length sets, and co-finite memberships.

## 4. Testing

- **Unit (`shinri-str`).** The clause is emitted exactly once for a bare
  string variable; it is *not* emitted for a concat-length term, for a
  literal's length, or a second time for the same variable. The `phases`
  payload carries the preferred-TRUE hint on the `≥ 1` disjunct.
- **Integration.** A pin where an arith-derived zero length must ground the
  variable — e.g. `(<= (str.len x) 0) ∧ (= (str.++ x "a") "b")` — decides
  `unsat`, where today it returns `Unknown`.
- **Regression (the load-bearing one).** The concat+length queries behind the
  `length.rs` livelock note, timed before and after; no wall-clock regression
  beyond noise, and the blocking tier stays inside its 10–15 min budget.
- **Oracle differential.** `cargo nextest run -p shinri-solver --features
  oracle`, run in the foreground with captured output. Dump-and-diff needs
  `--nocapture`; confirm a non-zero line count before trusting the diff, and
  confirm test discovery (a 0-test run reads as green).
- **`script_e2e`** run locally pre-push — this slice shifts completeness, and
  z3-confirmed `Unknown → decided` pin flips are adjudicated flips, not
  blockers.
