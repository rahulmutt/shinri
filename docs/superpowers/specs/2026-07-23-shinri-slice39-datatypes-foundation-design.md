# Slice 39 — Datatypes theory foundation (spine + definitional rules)

**Status:** design
**Date:** 2026-07-23
**Area:** new crate `shinri-dt`; `shinri-core` (sorts, datatype registry),
`shinri-parser` (`declare-datatypes`), `shinri-theory` (Combiner 5th slot),
`shinri-solver` (instantiation)
**Predecessors:** none in the datatype line — this is the first slice of a new
theory. Reuses the Nelson–Oppen seam built for EUF⋈Arith and the `TCheck`
fence discipline established by the string slices.

## 1. Summary

shinri covers EUF, arithmetic, arrays, bit-vectors, floating-point, and
strings, but has **no datatype support anywhere** — `SortNode` has no datatype
variant, the parser does not recognize `declare-datatypes`, and the Combiner is
a fixed four-theory tuple. This spec introduces the theory of algebraic
datatypes.

The north star is **full recursive QF_DT combined into QF_UFDTLIA**: the
complete Barrett–Shikanian–Tinelli procedure — constructors, selectors,
testers, case-splitting, acyclicity, and cardinality — combined with
uninterpreted functions and arithmetic. That is far more than one slice, so
this document fixes the architecture for the whole theory (§2–§6) and specifies
**slice 39** in implementable detail: the representational spine plus the rules
that need no case splitting. §8 sequences the remainder.

Slice 39 lands a sound, self-contained increment that decides real QF_DT
problems end to end, behind an explicit completeness fence (§5.2) that slice 40
lifts.

## 2. Representation — datatypes as tagged uninterpreted symbols

Constructors, selectors, and testers need **no new `Op` variants**. They are
declared as ordinary `Op::Uninterpreted(SymbolId)` functions with proper
signatures:

- `cons : (Elem, List) List`, `nil : () List` — constructors
- `head : (List) Elem`, `tail : (List) List` — selectors
- `is-cons : (List) Bool`, `is-nil : (List) Bool` — testers

Because they are plain uninterpreted applications, **EUF congruence-closes them
for free**: `a = c ∧ b = d ⇒ cons(a,b) = cons(c,d)` requires no datatype code.
The datatype solver supplies only what congruence cannot derive — the converse
(injectivity) direction, constructor disjointness, and selector-collapse.

Two additions to `shinri-core`:

1. **`SortNode::Datatype(SymbolId)`** — one new variant. It behaves exactly
   like `Uninterpreted(SymbolId)` under sort-checking, but is distinguishable
   so `classify` can route atoms (§6) and so later slices can ask cardinality
   questions about the sort (§8, slice 42).

2. **`DatatypeRegistry`, a side-table on `Context`** — for each datatype sort,
   its constructor list; for each constructor, its selector symbols, argument
   sorts, and tester symbol; plus reverse maps `SymbolId → role` (constructor
   of *D* / *i*-th selector of *C* / tester of *C*). `Context` already derives
   `Clone`, so the registry survives the `check_sat` clone of the context into
   the Combiner, which the codebase relies on elsewhere.

`shinri-dt` therefore never parses or rebuilds terms. It asks the registry
whether a symbol is a constructor, selector, or tester and of what, then
reasons over e-nodes the shared engine already holds.

## 3. Parser — `declare-datatypes` as new untrusted surface

Per [docs/threat-model.md](../../threat-model.md), SMT-LIB text entering the
lexer/parser is shinri's **only** untrusted edge, and the governing controls
are "no panics on hostile input" plus fuzz coverage. `declare-datatypes` is
genuinely new attack surface and is designed accordingly.

Add `Command::DeclareDatatypes`, handling both SMT-LIB 2.6 forms —
`(declare-datatype T (...))` and the plural
`(declare-datatypes ((T 0) ...) ((...) ...))` with mutual recursion across the
declared group. Parsing desugars into existing machinery: mint a
`SortNode::Datatype` sort per declared name, `declare_fun` each constructor,
selector, and tester into `Env`, and record the shape in the
`DatatypeRegistry`.

Every malformed shape is **rejected with a `Diagnostic`, never a panic**:

| Input | Required behavior |
|---|---|
| Arity ≠ 0 (parametric `(T 1)`) | `Diagnostic` — polymorphic datatypes are out of scope |
| Duplicate constructor, selector, or sort name | `Diagnostic`; never silently overwrite an existing symbol |
| Zero-constructor datatype | `Diagnostic` — an empty sort is not well-formed |
| Non-well-founded datatype, e.g. `(declare-datatype T ((c (f T))))` | `Diagnostic` — no finite ground term exists, so the sort is empty; accepting it would be unsound downstream |
| Deeply nested / mutually recursive sort references | Resolved **iteratively**; no stack overflow |
| Selector applied to the wrong sort | Existing `SortError` path |

**Well-foundedness** is a fixpoint over the declared group: mark a datatype
inhabited as soon as some constructor has all argument sorts inhabited;
iterate to saturation; reject anything still unmarked. Both this check and the
sort-reference resolution use an explicit worklist rather than recursive
descent over the type graph, so a hostile deeply-nested declaration cannot
overflow the stack. The same inhabitance computation is what slice 42 needs for
cardinality, so it is built once, here.

Datatype declarations are added to the `parse_script` fuzz corpus seeds so the
nightly fuzz budget actually exercises this surface.

## 4. Architecture — `shinri-dt` shares the EUF congruence substrate

The datatype decision procedure is congruence closure plus extra semantic
rules, so DT and EUF reason about the very same e-nodes. `shinri-dt` is a new
crate with its own `Owner` and Combiner slot, but it holds **no union-find of
its own**: it layers datatype rules on the shared `EqualityEngine` that every
theory's `TheoryCtx` already exposes.

Alternatives considered:

- **Extend `shinri-euf` in place.** Least seam friction — literally one engine
  — but it bloats the EUF crate, mixes two theories' concerns, and makes both
  harder to test in isolation.
- **A fully independent fifth theory with its own union-find.** Cleanest
  boundary on paper, but constructor and selector congruence would then have to
  be coordinated *across* the N-O seam with EUF, since both theories register
  the same applications — a double-reasoning and missed-congruence hazard.

The chosen middle path gives a clean crate boundary and isolated tests (the
`shinri-arrays` pattern) while congruence over constructors and selectors comes
free from the shared substrate. It also matches how cvc5 and z3 keep DT tightly
coupled to congruence closure.

`DtSolver` implements `TheorySolver` with `THEORY_ID = 5` (the next free id;
1–4 are EUF, arith, arrays, string).

## 5. The rule set

`DtSolver` keeps an index of the DT-relevant applications it has registered —
constructor applications, selector applications, and testers. On `check` it
canonicalizes them through the shared engine (`eq.find()`) and buckets them by
class representative; rules then fire per class. Polling on `check` rather than
subscribing to merge notifications keeps the seam small, and the cost is
O(#DT-apps) per check — negligible beside congruence itself.

### 5.1 Slice-39 rules (no case splitting)

- **Selector-collapse.** If the class of `t` contains `C(a₁…aₙ)` and also
  contains `selᵢ(t)` where `selᵢ` is `C`'s *i*-th selector, emit the lemma
  **`selᵢ(C(a₁…aₙ)) = aᵢ`**. Written over the constructor application itself
  this is an *unconditional* T-tautology, so it needs no guard; congruence
  supplies `selᵢ(t) ≡ selᵢ(C(a₁…aₙ))`. This is the workhorse rule, and it is
  the ROW-1 pattern of `shinri-arrays` (`crates/shinri-arrays/src/lib.rs:94`).
  If `selᵢ` belongs to a **different** constructor `D ≠ C`, the SMT-LIB
  semantics leave the value **unspecified** and the rule must **not** fire —
  collapsing there would be unsound.
- **Injectivity (downward).** `C(a₁…aₙ) ≡ C(b₁…bₙ)` ⇒ `aᵢ = bᵢ` pairwise
  requires **no dedicated code**: it is a consequence of selector-collapse plus
  congruence. From `C(a…) ≡ C(b…)`, congruence gives
  `selᵢ(C(a…)) ≡ selᵢ(C(b…))`; the two collapse lemmas give
  `aᵢ ≡ selᵢ(C(a…))` and `bᵢ ≡ selᵢ(C(b…))`; hence `aᵢ ≡ bᵢ`. EUF already
  supplies the upward direction. Tests pin this consequence (§7).
- **Constructor clash.** A class containing both `C(…)` and `D(…)` with
  `C ≠ D` ⇒ conflict.
- **Tester consistency (at-most-one only).** `t ≡ C(…)` ⇒ propagate `is-C(t)`
  true and every `is-D(t)` (`D ≠ C`) false. An asserted `is-C(t)` contradicted
  by a `D`-application in `t`'s class ⇒ conflict.

### 5.2 The completeness fence

The *at-least-one* direction — exhaustiveness, that every datatype term is
*some* constructor — is precisely what requires a case split, and it lands in
slice 40. Slice 39 is therefore **sound but deliberately incomplete**:

- `unsat` is decided fully; every rule above is conflict- or
  equality-producing and sound on its own.
- `Sat` is returned **only** when every datatype e-class is
  constructor-determined — that is, its class contains a constructor
  application, or its constructor is pinned by an asserted tester.
- Any datatype class whose constructor is undetermined yields
  **`TCheck::Unknown`**, never a possibly-wrong `sat`.

Without this fence a query such as `¬is-nil(t) ∧ ¬is-cons(t)` — unsat by
exhaustiveness — would be answered `sat`. The fence mirrors the project's
existing discipline (string budget fences, `TCheck::Unknown` on exhaustion).
Slice 40 *lifts* the fence; it does not fix a bug.

## 6. Wiring — equality seam, Combiner, models

**`DtSolver` owns no equality state and never merges.** The hazard this section
originally guarded against — DT merging classes directly in the shared
`EqualityEngine`, leaving EUF's use-lists un-triggered and congruence
consequences silently missed — is designed out rather than mitigated.
`DtSolver` is a **pure lemma-on-demand theory, structurally identical to
`shinri-arrays`**: it derives nothing into the equality engine and instead
emits axiom instances as positive-atom clauses via `TCheck::Split`, letting the
SAT search and EUF congruence do all merging.

> **Plan-time correction (2026-07-23).** This section originally routed DT's
> derived equalities through the Combiner's `consume_interface_equality` seam,
> with a guarded `TCheck::Split` as fallback. Both are unnecessary: writing
> selector-collapse over the constructor application (§5.1) makes the lemma an
> *unconditional* tautology, so no guard and no merge channel are needed, and
> injectivity ceases to require code at all. The N-O extension is dropped from
> this slice.

The three channels DT actually uses, all pre-existing:

| Rule | Channel |
|---|---|
| Selector-collapse `selᵢ(C(a…)) = aᵢ` (⇒ injectivity) | `TCheck::Split { guard: None }` — unconditional tautology |
| Tester positive `is-C(C(a…))` | `TCheck::Split { guard: None }` — unit tautology |
| Constructor clash `C(…) ≡ D(…)` | `TCheck::Conflict`, leaves from `cx.eq.explain(a, b, &mut out)` |
| Tester disjointness: asserted `is-D(t)`, class holds `C(…)`, `C ≠ D` | `TheorySolver::assert` returns conflict leaves |

Tester disjointness lives in `assert` rather than `check` because its
consequence `¬is-D(t)` is a *negative* literal, and `TCheck::Split` carries
only positive atoms. Catching it at assertion time is both sound and cheaper.

Consequently `DtSolver::explain` handles only tags it mints for its own
conflicts, and it implements none of the N-O exchange hooks
(`consume_interface_equality`, `mint_eq_tag`, `entailed_equalities`) — their
trait defaults stand. Slice 43 revisits this when arithmetic-sorted fields
require genuine equality exchange.

**Combiner.** `Combiner<E, A, R, S>` gains a fifth slot,
`Combiner<E, A, R, S, D>`, with a `dt_mut()` accessor and a new
`Owner::Datatypes`. `classify` routes an atom to `Datatypes` when it is a
tester application, or an equality/disequality whose operands are
datatype-sorted. The concrete instantiation in `shinri-solver` becomes
`Combiner<Euf, Arith, Arrays, StrSolver, DtSolver>`. The eager BV, FP, ABV, and
string stages are untouched: they detect their own fragments, DT atoms never
appear there, and datatype problems take the Combiner path.

**Models.** `DtSolver::model` assigns each datatype class a ground constructor
term. When the class contains a constructor application, the value is that
application with children resolved recursively through the model. Otherwise —
under the §5.2 fence the class is constructor-determined by a tester — selector
children are filled from the model where present, falling back to a canonical
inhabitant of the field sort. Well-foundedness (§3) guarantees such an
inhabitant exists and that the recursion terminates.

## 7. Testing

- **Unit tests in `shinri-dt`**, against a hand-built
  `EqualityEngine`/`TheoryCtx`: one per rule in §5.1 — selector-collapse emits
  the tautology for the matching constructor and *provably does not* for a
  foreign selector; constructor clash conflict; tester tautology and
  tester/constructor conflict at assert time. Injectivity is tested as an
  **emergent consequence** (collapse lemmas + congruence yield `aᵢ ≡ bᵢ`), not
  as a dedicated rule. Plus fence tests asserting `Unknown` rather than `Sat` on
  a constructor-undetermined class.
- **Parser tests**: one per row of §3's rejection table, each asserting a
  `Diagnostic` rather than a panic — including the non-well-founded case and a
  deeply nested mutually recursive declaration. Datatype declarations seeded
  into the `parse_script` fuzz corpus.
- **End-to-end script tests in `shinri-solver`**: small `.smt2` scripts with
  pinned `sat` / `unsat` / `unknown` outcomes, including at least one pinned
  `unknown` that documents the §5.2 fence.
- **Oracle differential tests** against z3 and cvc5, both of which support
  QF_DT. These are feature-gated: the plan must bake in
  `cargo nextest run -p shinri-solver --features oracle`, because **without the
  flag the suite silently runs zero tests** and reads as green.

All of this is small and fast; no exhaustive suites are added, so the blocking
PR tier budget is unaffected. Because the slice shifts completeness, the local
`script_e2e` gate runs pre-push, and `cargo fmt --all` runs before pushing (CI
gates on `fmt --check` and fails fast).

## 8. Slice roadmap

| Slice | Content |
|---|---|
| **39 (this spec)** | Spine + definitional rules: representation, parser, Combiner wiring, selector-collapse, injectivity, disjointness, tester consistency; completeness fence |
| 40 | Tester case-splitting — constructor instantiation `t = C(sel₁(t), …)`, lazily so recursive types terminate; lifts the §5.2 fence |
| 41 | Acyclicity — occurs-check over the constructor graph; `x = cons(h, x)` unsat |
| 42 | Finiteness / cardinality reasoning over finite datatype domains, for combination completeness |
| 43 | Nelson–Oppen with arithmetic — Int/Real datatype fields ⋈ arith; completes QF_UFDTLIA |

## 9. Success criteria

1. `(declare-datatype …)` and `(declare-datatypes …)` parse, including mutual
   recursion; every §3 malformed shape produces a `Diagnostic` and no panic.
2. Selector-collapse, injectivity, constructor clash, and tester consistency
   each decide their unit test, and the foreign-selector case provably does not
   collapse.
3. End-to-end QF_DT scripts return correct `unsat` and `sat` results, and the
   pinned fence script returns `unknown`.
4. Oracle differential tests agree with z3/cvc5 on every non-`unknown` outcome,
   run with `--features oracle` and with a non-zero test count confirmed.
5. `mise run lint` and `cargo fmt --check` clean; blocking tier wall-clock
   unchanged.
