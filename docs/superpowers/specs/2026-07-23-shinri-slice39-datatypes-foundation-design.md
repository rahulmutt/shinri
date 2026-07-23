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
- **Injectivity (downward).** `C(a₁…aₙ) ≡ C(b₁…bₙ)` ⇒ `aᵢ = bᵢ` pairwise is
  the *consequence* of selector-collapse plus congruence: from `C(a…) ≡
  C(b…)`, congruence gives `selᵢ(C(a…)) ≡ selᵢ(C(b…))`; the two collapse
  lemmas give `aᵢ ≡ selᵢ(C(a…))` and `bᵢ ≡ selᵢ(C(b…))`; hence `aᵢ ≡ bᵢ`. EUF
  already supplies the upward direction.
  > **Implementation correction (Task 10, human-approved deviation).** This
  > consequence does **not** fall out for free: `selᵢ(C(a…))` and
  > `selᵢ(C(b…))` only exist as watched applications, and hence only feed
  > `collapse_lemma`, if something has *instantiated* those selector terms.
  > When neither side of the equated constructor pair already has its
  > selectors mentioned in the input, no lemma ever fires and the
  > consequence is silently missed. Slice 39 therefore ships a **dedicated
  > rule**, `DtSolver::instantiate_injectivity_selectors` (on-demand selector
  > instantiation): for every pair of same-constructor applications found
  > equal in the same class, it mints and watches every field selector
  > applied to *both* applications, which then feeds selector-collapse as
  > above. This is planted code, not an emergent property — see §10.
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
  tester/constructor conflict at assert time. Injectivity is tested as the
  consequence of the dedicated `instantiate_injectivity_selectors` rule
  feeding collapse lemmas + congruence to yield `aᵢ ≡ bᵢ` (see §5.1's
  implementation correction) — not as a rule-free emergent property, which
  was the original (incorrect) plan-time assumption. Plus fence tests
  asserting `Unknown` rather than `Sat` on a constructor-undetermined class.
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

## 10. Measured outcomes

Recorded 2026-07-23, Task 11, on the `slice39-datatypes-foundation` branch.
Every number below is from a command actually run in this session; none are
aspirational.

**Rules exercised (via `crates/shinri-dt/src/lib.rs` unit tests, `cargo
nextest run -p shinri-dt`, 14/14 pass):**

| Rule | Test(s) |
|---|---|
| Selector-collapse (fires) | `selector_collapse_emits_tautology_for_matching_constructor`, `collapse_reaches_fixpoint_after_lemma_is_installed` |
| Selector-collapse (does NOT fire on a foreign selector) | `selector_collapse_does_not_fire_for_foreign_selector` |
| Injectivity, via the dedicated `instantiate_injectivity_selectors` rule (§5.1 correction) | `injectivity_is_a_consequence_of_collapse_and_congruence` |
| Constructor clash | `constructor_clash_is_a_conflict` |
| Tester consistency (unit tautology + assert-time conflict) | `tester_over_constructor_emits_unit_tautology`, `tester_lemma_over_class_member_rewrites_onto_constructor_app`, `asserted_tester_conflicting_with_constructor_is_rejected_at_assert`, `asserted_tester_agreeing_with_constructor_is_fine` |
| §5.2 completeness fence | `undetermined_datatype_class_yields_unknown_not_sat`, `determined_datatype_class_is_sat` |
| Model construction | `model_assigns_ground_constructor_term` |
| Watch-set indexing / linearity | `new_var_indexes_constructor_selector_and_tester_apps`, `collect_seen_guard_keeps_shared_subterm_walk_linear` |

**End-to-end** (`cargo nextest run -p shinri-solver --test qfdt_e2e`,
confirmed 10/10 pass in the full run below): selector-over-constructor unsat,
constructor disjointness unsat, injectivity unsat (direct and transitive),
injectivity branch-local stays sat, tester/constructor agreement and
contradiction, UF-over-datatype congruence unsat, mixed datatype+arith unsat,
and the pinned fence case (`undetermined_constructor_fences_to_unknown`)
returning `unknown` rather than a possibly-wrong `sat`.

**Oracle differential** — command actually run:

```
cargo nextest run -p shinri-solver --features oracle -E 'binary(qfdt_oracle)'
```

z3 4.16.0 (via `mise`) was on `PATH` in this environment, so the suite was
**executed, not merely compiled**. Result:

```
Starting 6 tests across 1 binary (24 binaries skipped)
    PASS [   0.031s] (1/6) shinri-solver::qfdt_oracle qfdt_oracle_selector_collapse
    PASS [   0.032s] (2/6) shinri-solver::qfdt_oracle qfdt_oracle_nested_constructors
    PASS [   0.033s] (3/6) shinri-solver::qfdt_oracle qfdt_oracle_tester_agreement
    PASS [   0.033s] (4/6) shinri-solver::qfdt_oracle qfdt_oracle_disjointness
    PASS [   0.033s] (5/6) shinri-solver::qfdt_oracle qfdt_oracle_injectivity
    PASS [   0.033s] (6/6) shinri-solver::qfdt_oracle qfdt_oracle_uf_over_datatype
Summary [   0.034s] 6 tests run: 6 passed, 0 skipped
```

**Confirmed non-`unknown` on both sides for every case** (checked directly,
outside the assertion, by instrumenting and by running each query's script
through `z3 -smt2 -in -T:120 -memory:4096` standalone): shinri and z3 agree
`unsat`/`unsat`/`unsat`/`sat`/`unsat`/`unsat` for
selector-collapse/injectivity/disjointness/tester-agreement/nested-constructors/uf-over-datatype
respectively. No case was a silent `unknown`-skip on either side, so all six
comparisons genuinely exercised the differential, not a vacuous pass.

Only z3 was run — **cvc5 was not wired into this suite** even though it is on
`PATH` via `mise` (`cvc5 1.3.4`) and §7/§9-criterion-4 as originally written
name both oracles. This is a real gap against the spec's own criterion 4 —
see the criterion-4 verdict below.

**Fuzz corpus seeds.** The 5 seed bodies from the task brief were added to
`crates/shinri-parser/fuzz/corpus/parse_script/`, named by the sha1 hex of
their content (matching the existing seed-naming convention in that
directory). `ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run parse_script
-- -runs=20000` was run locally and completed 20000 runs with no crash
(`corp: 2245/226Kb` at completion). **The `corpus/` directory itself is
git-ignored repository-wide** (`.gitignore`: `crates/*/fuzz/corpus/`,
comment "Local cargo-fuzz state (nightly CI fuzzes from a fresh corpus)") —
this is true for every fuzz target in the repo, none of which have a
committed corpus. The 5 seed files exist on disk and were exercised by the
local run; they are intentionally **not** part of the git commit, consistent
with how every other fuzz crate in this repo is set up.

**Blocking-tier wall-clock** — command actually run:

```
cargo nextest run --all
```

Result: `1218 tests run: 1218 passed (5 slow), 7 skipped` in **262.1s**
nextest-reported (`4m22.7s` wall via `time`), comfortably inside the 10–15
min blocking-PR budget. The slowest individual test in the run was
`shinri-parser parser::tests::declare_datatypes_deep_nesting_does_not_overflow`
at **22.0s** (the 5000-deep nested datatype declaration named in the task
brief); the next-slowest DT-adjacent test was `qfbv_witnesses
bvmul_commutativity_unsat` at 16.1s (pre-existing, unrelated to this slice).
No DT test required an `#[ignore]` exhaustive tier. Wall-clock is effectively
unchanged from pre-slice-39 baselines (the added DT suites total well under a
second).

**Lint.** `cargo fmt --all --check` and `cargo clippy --workspace
--all-targets -- -D warnings` (i.e. `mise run lint`) are both clean.
`cargo clippy -p shinri-solver --test qfdt_oracle --features oracle -- -D
warnings` (the new file, isolated) is also clean. However,
`cargo clippy -p shinri-solver --all-targets --features oracle -- -D
warnings` (every oracle test compiled together) currently fails with 36
pre-existing `clippy::wrong_self_convention` errors in
`tests/qfs_differential.rs`, `tests/qfbv_oracle.rs`, `tests/fp_oracle.rs`, and
`tests/nary_arith_oracle.rs` — none of them touched by this task, and none in
`qfdt_oracle.rs`. This looks like latent drift (nobody previously ran clippy
`--all-targets --features oracle` together) rather than anything introduced
here; it is flagged, not fixed, since fixing it means editing unrelated
oracle suites outside this task's scope ("tests, seeds, and docs only" for
QF_DT).

**§9 success criteria — verified one by one:**

1. **MET.** Parser accepts `declare-datatype`/`declare-datatypes` including
   mutual recursion, and rejects every malformed shape with a `Diagnostic`
   (no panic) — 20+ dedicated tests in
   `crates/shinri-parser/src/parser.rs` (e.g.
   `declare_datatypes_rejects_non_well_founded`,
   `declare_datatypes_rejects_duplicate_selector`,
   `declare_datatypes_deep_nesting_does_not_overflow`), all green in the
   1218-test run above.
2. **MET.** Selector-collapse, injectivity (via the dedicated instantiation
   rule — see §5.1 correction), constructor clash, and tester consistency
   each have a passing unit test in `shinri-dt` (14/14, table above),
   including the foreign-selector negative case
   (`selector_collapse_does_not_fire_for_foreign_selector`).
3. **MET.** `qfdt_e2e` (10/10) covers correct `sat`/`unsat`, and
   `undetermined_constructor_fences_to_unknown` pins the §5.2 fence returning
   `unknown`.
4. **PARTIALLY MET.** Oracle differential agrees with z3 on all 6 non-`unknown`
   cases, run with `--features oracle -E 'binary(qfdt_oracle)'`, confirmed
   non-zero (6) test count, all passing. The criterion as originally written
   also names cvc5; **cvc5 was not exercised by this suite** (Task 11's brief
   scoped the oracle helper to z3 only, mirroring `qfs_differential.rs`).
   This is a real, acknowledged shortfall against the letter of criterion 4,
   not a silent claim of full compliance — a cvc5 leg is future work, not
   landed here.
5. **MET.** `mise run lint` (fmt --check + workspace clippy, no oracle
   feature) is clean. Blocking-tier wall-clock is 262.1s / 4m22.7s,
   unchanged in substance from pre-slice-39 (the added suites are
   sub-second). The one caveat is the pre-existing, unrelated
   `--features oracle --all-targets` clippy failure noted above, which this
   task did not introduce and does not fix.
