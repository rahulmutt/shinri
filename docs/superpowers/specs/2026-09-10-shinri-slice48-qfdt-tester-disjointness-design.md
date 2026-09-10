# Slice 48 — QF_DT wrong-`sat`: tester disjointness is checked once, at the wrong moment

**Status:** design
**Date:** 2026-09-10
**Area:** `shinri-dt` (`DtSolver::check`, `assert`, `push`/`pop`, the
`asserted_testers` record), `shinri-solver` tests (`qfdt_oracle` gains a
randomized generator; `qfdt_e2e` gains the repro fences). No new crate, no new
theory slot, no parser surface change, no `Combiner` change, no shared-primitive
change.
**Predecessors:** slice 46 measured the defect
(`docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md § Next slices`,
rank 2). The datatype theory was built by slices 39–41
(`2026-07-23-shinri-slice39-datatypes-foundation-design.md`,
`2026-07-24-shinri-slice40-tester-case-split-design.md`,
`2026-07-24-shinri-slice41-datatype-acyclicity-design.md`); this slice repairs a
rule slice 39 placed and slice 40 built on. Slice 47 closed rank 1 (QF_ABV
wrong-`sat`).

## 1. Summary

The first full SMT-LIB 2024 run reports **328 wrong answers in QF_DT**, every
one `:status unsat` answered `sat`. Families: `20172804-Barrett` 166 and
`20230720-blocksworld` 162. The cluster is independently confirmed rather than
`:status`-only — 327 of the 328 rows carry a decided oracle `unsat`. Bucket key:
`docs/superpowers/research/2026-09-09-smtlib-2024-baseline-report.md
› ## Wrong answers` (the QF_DT rows).

**The two families are two different bugs.** This slice fixes Barrett, whose
cause is diagnosed below, and *measures* blocksworld without touching it.

### The Barrett cause

Tester disjointness — "an asserted `is-D(t)` whose class holds a `C(..)` with
`C ≠ D` is a conflict" — is enforced in exactly one place, `DtSolver::assert`
(`crates/shinri-dt/src/lib.rs:788-810`), against whatever constructor is in the
class **at that instant**. Any merge that later brings a conflicting constructor
into the class is never re-checked:

* `constructor_clash` (`lib.rs:251`) compares constructor applications only to
  *other constructor applications*, never to a tester;
* `tester_lemma` (`lib.rs:292`) handles only the **agreeing** direction, emitting
  `is-C(C(..))` when the symbols match, and its own doc comment records that the
  disagreeing direction "is handled at assert time instead";
* `instantiate_constructor` (`lib.rs:402`) skips a class that already holds a
  constructor by testing *presence*, never comparing symbols.

So the answer depends on the order in which SAT asserts the literals. The
minimal reproducer is three lines:

```smt2
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
((cons (car tree) (cdr list)) (null))
((node (children list)) (leaf (data nat)))))
(declare-fun x2 () list)
(assert (and ((_ is cons) x2) (= x2 null)))
(check-sat)
```

`sat` on `7abe84ca`; it must be `unsat`. Swapping the two conjuncts yields the
correct `unsat` — the equality merge then precedes the tester assertion, so
`assert`'s one-shot check sees `null` in the class and fires. Since both
conjuncts are inside a single `and`, the order is SAT's to choose, not the
file's.

The corpus reproducer is the same hole reached through a *check-time* merge.
`QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30072.cvc.smt2` (966 B) reduces
to

```smt2
(assert ((_ is cons) (children (node null))))   ; → sat, must be unsat
```

Here the class of `(children (node null))` gains its constructor `null` from
`collapse_lemma` (`lib.rs:113`), which runs inside `check` and installs the
selector-collapse tautology `children(node null) = null` as a level-0 unit. That
merge arrives through the shared `EqualityEngine`, not as a DT-owned literal, so
`assert` is never re-entered and the clash is never seen. Each half alone is
answered correctly:

| probe | shinri on `7abe84ca` | correct |
| --- | --- | --- |
| `(not (= (children (node null)) null))` | `unsat` | `unsat` |
| `((_ is cons) null)` | `unsat` | `unsat` |
| `((_ is cons) (children (node null)))` | **`sat`** | `unsat` |
| `(= x2 null) ∧ is-cons(x2)` | `unsat` | `unsat` |
| `is-cons(x2) ∧ (= x2 null)` | **`sat`** | `unsat` |
| `is-cons(x2) ∧ (= x2 y2) ∧ (= y2 null)` | **`sat`** | `unsat` |

### Why blocksworld is not this bug

The 162 `20230720-blocksworld` files contain **zero testers** — the shape is deep
ground `stack` chains, three-field records, and 21-constructor enums, with
equalities and selectors but no `(_ is C)` anywhere. A rule about asserted
testers cannot be their cause. Five hand-built probes over that shape (enum
constructor clash, same-constructor injectivity conflict, nested-chain clash,
record selector round-trip, selector-through-equality) all answer `unsat`
correctly on `7abe84ca`, so the cause is not one of the obvious candidates and
needs a real bisect on a 21–53 KB instance. It is measured here and queued
(§9), not fixed.

## 2. Scope

**In:** the tester-disjointness rule and the assertion record it reads; a
randomized QF_DT oracle generator; fences; a QF_DT corpus re-run.

**Out, and reported unchanged:**

* the 162 blocksworld wrong rows (different bug, §1);
* QF_DT's 507 `timeout`, 11 `unknown` and 5 `unverified` rows;
* the completeness fence `has_undetermined_class` (`lib.rs:612`) and the
  acyclicity walk (`lib.rs:507`) — untouched;
* every other logic. This slice changes no shared primitive: the edits are
  confined to `crates/shinri-dt/src/lib.rs` and test files.

## 3. The fix

### 3.1 `tester_clash` — the same rule, at the right trigger point

A new rule in `DtSolver::check`, placed immediately after `constructor_clash`:

```
for each currently-asserted tester is-D(t):
    let (C, capp) = ctor_of_class(t)?          // no constructor → nothing to clash with
    if C == D { continue }                     // agrees
    return Conflict([Asserted(is-D(t))] ++ eq.explain(intern(t), intern(capp)))
```

The body is `assert`'s (`lib.rs:801-809`) verbatim. What changes is *when* it
runs: `check` is re-entered after every merge, so a constructor that reaches the
class later — from `collapse_lemma`, from `instantiate_constructor`, or from any
EUF congruence closure — is now compared against the branch's asserted testers.

`assert` **keeps its copy.** The two are one rule at two trigger points:
catching the clash at assert time is strictly cheaper when the constructor is
already present, and removing it would regress the existing fence
`asserted_tester_conflicting_with_constructor_is_rejected_at_assert`
(`lib.rs:1367`). This duplication is deliberate and is recorded here so a later
reader does not "simplify" one of them away.

**Placement is load-bearing.** `tester_clash` must precede
`has_undetermined_class`'s `Unknown` fence and `constructor_graph_find_cycle`,
on exactly the principle `check` already documents for
`instantiate_injectivity_selectors`: a rule that returns `Sat` or `Unknown`
must not short-circuit a pending conflict. Putting it adjacent to
`constructor_clash` at the top of `check` satisfies this and groups the two
conflict rules together.

**Why not a `Split`.** The consequence in the disagreeing direction is the
negative literal `¬is-D(t)`, and `TCheck::Split` carries only positive atoms
(`shinri-theory/src/solver_trait.rs:28-36`) — the reason slice 39 put this rule
in `assert` in the first place. `TCheck::Conflict` carries `EqLeaf`s and has no
such restriction, so the conflict channel is the one that fits.

### 3.2 `asserted_testers` becomes level-indexed

> **Superseded by §11 ("What actually shipped").** This section is the
> design as originally proposed and as Task 2 (`e5cc3eea`) built it: ONE
> levelled record shared by both `tester_clash` and `instantiate_constructor`.
> The `slice48` corpus re-measure found that sharing silently retracted
> `instantiate_constructor`'s guarded lemmas on every `pop`, turning an
> `unsat` blocksworld instance into a wrong `sat` (+28 wrong rows across the
> family) — read §11's "What actually shipped" subsection before trusting
> anything below as the shipped behaviour. The code ships **two** records,
> split by consumer, not the single record this section describes; treat this
> section as historical design intent, not current fact. `crates/shinri-dt/src/lib.rs`'s
> field docs on `instantiation_testers_monotone` / `conflict_testers_per_level`
> are the authority on what the running solver actually does.

This retires a documented invariant, and it is the substantive risk of the
slice.

Today `asserted_testers` (`lib.rs:36-40`) is monotone and never popped. Slice 40
justified that explicitly: a stale entry from a backtracked branch "only
re-emits a GUARDED (hence inert) lemma, never an unsound one, so retraction is
unnecessary and `push`/`pop` stay no-ops". Feeding that set into a **conflict**
voids the justification. A stale tester would yield a `Conflict` citing
`EqLeaf::Asserted(lit)` for a literal the trail no longer holds. The resulting
clause is still a valid theory lemma — `is-D(t) ∧ t = C(..)` is unsatisfiable
regardless of branch — but handing conflict analysis a clause that is not
falsified by the current assignment is a defect in its own right: the backjump
level is computed from literals assumed false, and none of the SAT seam's
invariants survive that.

`TheoryCtx` exposes `terms`, `eq` and `atoms` and **no trail**
(`solver_trait.rs:14-18`), so `check` cannot ask "is this tester still true?".
The record must therefore be backtrack-accurate by construction.

Shape, mirroring `shinri-str`'s trail (`crates/shinri-str/src/trail.rs`), whose
`pop_to` semantics are already proven and tested in this repo:

* `asserted_testers: Vec<TermId>` in insertion order, paired with the existing
  `FxHashSet<TermId>` so the dedup that `assert` relies on is preserved;
* `tester_marks: Vec<usize>`;
* `push()` → `tester_marks.push(asserted_testers.len())`;
* `pop(target)` → `while tester_marks.len() > target { last = tester_marks.pop() }`,
  then truncate the vec to `last` and remove the dropped terms from the set.

`pop` takes **absolute** target levels (`solver_trait.rs:43`) and `combiner.rs:505`
already hands DT that target, so no plumbing changes. `push`/`pop` stop being
no-ops for DT.

Everything else stays monotone and untouched: `ctor_apps`, `sel_apps`,
`testers`, `dt_terms`, `emitted`, `split_done` are assignment-independent watch
sets, and only the assertion record is levelled. The doc comment at `lib.rs:36`
is rewritten to say why this one field is different from its neighbours.

The off-by-one in `pop_to` is the sharpest edge in this slice and gets dedicated
fences (§5.2).

### 3.3 `instantiate_constructor`'s presence test

> **Superseded by §11 ("What actually shipped").** This section's premise —
> that `tester_clash` and `instantiate_constructor` read the SAME record, so a
> disagreeing constructor reaching this line is unreachable — is false of the
> shipped code. The two consumers now read different records
> (`instantiation_testers_monotone` for this function,
> `conflict_testers_per_level` for `tester_clash`), so a tester retracted from
> the per-level record but still present in the monotone one CAN legitimately
> reach this line with a disagreeing constructor; that state is normal, not a
> bug. The `debug_assert` this section prescribes below was **removed** in the
> fix wave for exactly that reason — see §11.

`lib.rs:402` reads `if self.ctor_of_class(cx, t).is_some() { continue; }` — it
skips on *any* constructor in the class and never compares symbols. Today that
is a live gap. Once `tester_clash` runs earlier in the same `check` call, a
class holding a constructor that disagrees with an asserted tester can no longer
reach that line, so the control flow becomes correct as written.

**No behavioural change is made here.** The line gains a `debug_assert` that the
symbols agree and a comment naming `tester_clash` as the reason — the slice-38
pattern: a defensive fence that is end-to-end unreachable, kept because it is
zero-cost, with unit tests rather than a live branch as its proof. Converting it
into a second conflict site would duplicate `tester_clash` for no measured gain.
**(Superseded — see the marker above: this `debug_assert` was removed.)**

## 4. Tasks

1. **Randomized QF_DT oracle generator** (§5.1). Must FAIL on pre-slice `main`,
   with the failing instance quoted verbatim in the task report. Lands before
   any fix.
2. **`tester_clash` in `check`** (§3.1), with its unit fences.
3. **Level-indexed `asserted_testers`** (§3.2), with its backtracking fences
   (§5.2). **As shipped, this became a split into two records by consumer,
   not one shared levelled record — see §11.**
4. **`instantiate_constructor` defensive fence** (§3.3).
5. **e2e repro fences** (§5.3), including the negative over-fire guard.
6. **QF_DT corpus re-run and report** (§6), including the blocksworld
   measurement.
7. **Whole-branch review** before the PR — not per-task review only. Slice 44's
   final review caught a Critical that all seven task reviews missed, and this
   slice touches identity/keying (which tester belongs to which level) inside a
   soundness path.

## 5. Testing

### 5.1 Oracle

`crates/shinri-solver/tests/qfdt_oracle.rs` is 267 lines of hand-written fixed
shapes. `qfdt_oracle_disjointness` (`:155`) exists and **passes today** — it
happens to use the conjunct order that works. That is precisely the blind spot
that let 166 wrong answers ship, and the slice-44 lesson repeated: a green
oracle is not coverage when the generator cannot emit the failing shape.

Task 1 adds a randomized generator to that file:

* **Families:** a Barrett-shaped mutually-recursive `nat`/`list`/`tree` group and
  a flat enum.
* **Assertions drawn from:** testers (positive and negated), equalities between
  variables and constructor applications, selector applications *including
  selectors applied to the wrong constructor* (where `v1l30072` lives), and
  nested constructor terms.
* **The dimension the fixed list lacks: randomized conjunct order.** The defect
  is order-dependent — the same formula answers `sat` or `unsat` depending on
  which conjunct is asserted first — so a generator that always emits one order
  cannot find it.
* Differential against z3, in the established `agree` / `agree_decided` style so
  the completeness fence fails loudly rather than silently.

The file is feature-gated. **Every command carries `--features oracle`**; without
it the suite silently runs 0 tests, which reads as green. A filtered run must
report a non-zero discovered count before it is believed, and filters use the
expression form `-E 'test(<name>)'` — a positional `mod::name` filter matches
nothing on the pinned nextest 0.9.140.

The closing run is the **full unfiltered** `cargo nextest run -p shinri-solver
--features oracle`, not a `-E 'test(qfdt)'` filter.

### 5.2 Backtracking fences (`shinri-dt` unit tests)

* An asserted tester recorded at level 2 is **gone** after `pop(1)`, and `check`
  no longer reports a conflict for it.
* An asserted tester recorded at level 0 **survives** `pop(0)`.
* A stale tester cannot produce a conflict: assert `is-D(t)` at level 2, pop to
  level 1, merge `t` with a `C(..)`, and confirm `check` returns no conflict
  citing the popped literal.

### 5.3 e2e repro fences (`qfdt_e2e.rs`)

Every one of these reproduces on `7abe84ca`:

* `is-cons(x2) ∧ (x2 = null)` → `unsat`, asserted in **both conjunct orders**;
* `is-cons(x2) ∧ (x2 = y2) ∧ (y2 = null)` → `unsat` (transitive merge);
* `is-cons(children(node null))` → `unsat` (the check-time merge from
  `collapse_lemma` — the corpus shape);
* the `v1l30072.cvc.smt2` body inline → `unsat`.

And one **negative** fence the fix must not break:

* `is-cons(children(t3))` with `t3` free stays **`sat`**.

A disjointness rule that over-fires — conflicting on a class whose constructor is
merely a candidate rather than established — turns that query into a wrong
`unsat`. It is the cheapest available guard against trading a wrong-`sat`
cluster for a wrong-`unsat` one.

### 5.4 Tiers and hygiene

No test in this slice is expected to exceed the 5-minute exhaustive threshold,
so nothing here is `#[ignore]`d and no `shinri-fp` `#[ignore]` is touched.
Pre-push: `cargo fmt --all` (CI gates on `fmt --check` and fails fast),
`mise run lint`, `mise run test`.

Because this slice shifts completeness on QF_DT — queries that answered `sat`
now answer `unsat` — `script_e2e` runs locally before the push, via
`-E 'binary(script_e2e)'` (`test(script_e2e)` finds 0 tests: it is a binary
name, not a test name). A pinned-answer flip that z3 confirms is an adjudicated
flip to be re-pinned, not a blocker.

## 6. Measurement

Single-logic QF_DT re-run, run-id `slice48`, all 8,700 QF_DT paths from the
baseline run, reported to
`docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md` with
the transition matrix and family breakdowns the slice-47 report established.

### Success criteria

| # | criterion | baseline | gate |
| --- | --- | ---: | --- |
| 1 | `20172804-Barrett` wrong rows | 166 | **0** — hard gate |
| 2 | `correct → timeout` / `correct → unknown` / `correct → oom` transitions | — | **0** — hard gate |
| 3 | QF_DT `correct` | 7,849 | ≥ 7,849 |
| 4 | the randomized generator failed pre-slice and passes now | — | yes |
| 5 | `20230720-blocksworld` wrong rows | 162 | **measured and reported, not gated** |

**Criterion 2 is deliberately a transition count, not a bucket cap.** Slice 47
capped the `timeout` bucket, missed the cap, and then had to decompose the
number to show that the rise was overwhelmingly `wrong → timeout` — a wrong
answer becoming an honest timeout, which is the point of a soundness slice —
with only 62 of 163 being the actual `correct → timeout` regression. A bucket
total cannot distinguish the slice's purpose from its cost; the transition can,
so it says the intended thing directly.

**Criterion 5 is measured, not gated,** because the premise is that blocksworld
is a different bug (§1). If those rows move, the premise was wrong and the
report says so — the slice-42 lesson that a fully implemented plan with green
reviews can still deliver zero, and only the measured end-to-end gate catches a
bad premise. Either outcome is a result; neither blocks the merge.

## 7. Named reproducers

| path / query | expects | shinri on `7abe84ca` |
| --- | --- | --- |
| `bench/corpus/QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30072.cvc.smt2` | `unsat` | `sat` |
| `is-cons(x2) ∧ (x2 = null)` (inline, §1) | `unsat` | `sat` |
| `is-cons(children(node null))` (inline, §1) | `unsat` | `sat` |
| `bench/corpus/QF_DT/20230720-blocksworld/blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_5.smt2` | `unsat` | `sat` (out of scope, §2) |

The blocksworld instance is listed for the §6 measurement, not as something this
slice fixes.

## 8. Banked, not built

**Approach B — propagating `¬is-D(t)`.** Implementing `DtSolver::propagate` to
emit the negative literal whenever a class holds `C(..)` and a watched
`is-D(t)` has `D ≠ C` would let SAT *learn* the negation instead of
rediscovering the same conflict on each branch, and it would sidestep §3.2
entirely, since SAT owns retraction of its own propagations. It is the more
faithful rendering of the Barrett–Shikanian–Tinelli procedure.

It is banked because its payoff is efficiency, not soundness, and it is not
free: DT's `propagate` and `explain` are both no-ops today, and only EUF
implements `mint_eq_tag` (`crates/shinri-euf/src/solver.rs:313`), so DT would be
the first non-EUF theory here to open the justification-tag channel — new
machinery in a soundness path, bought against an unmeasured benefit.

**Un-bank it only on a measured thrash signal** in the §6 re-run: a
`correct → timeout` transition (criterion 2) or a material rise in QF_DT
`timeout` attributable to repeated rediscovery of the same tester clash. QF_DT
already carries 507 `timeout` rows at baseline, so that bucket is the one to
watch.

## 9. Queued for the next slice

> **Updated by §11's re-measure (run-id `slice48b`, fixed code).** The bullets
> below are as written before any measurement; see §11's "Re-measured after
> the fix wave" subsection for the current, measured queue, including two
> items §11 adds: the pre-existing `shinri-euf` congruence-loss defect that
> now explains blocksworld's one clean `correct → wrong` regression, and
> `qfdt_oracle` generator's blind spot for it.

* **`20230720-blocksworld`, 162 wrong rows (baseline).** No testers anywhere in
  the family, so §3's rule cannot be the cause; the five obvious candidate
  shapes all answer correctly. Needs a genuine bisect on a 21–53 KB instance —
  the cheapest is `blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_5.smt2`
  (21,247 B, answers in 0.95 s). Whatever §6/§11 measures about these rows is
  the starting evidence — as measured, this family's premise (that it is
  fully untouched by this slice) is false; see §11.
* **QF_DT's 507 `timeout`, 11 `unknown`, 5 `unverified` rows** — unchanged in kind from
  baseline, out of scope per §2, still in the slice-46 queue.

## 10. References

* Baseline — `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Next slices, rank 2) and
  `2026-09-09-smtlib-2024-baseline-report.md` (`## Wrong answers`, the QF_DT
  rows).
* The datatype theory — slices 39
  (`2026-07-23-shinri-slice39-datatypes-foundation-design.md`), 40
  (`2026-07-24-shinri-slice40-tester-case-split-design.md`, which introduced
  `asserted_testers` and the monotone justification §3.2 retires — slice 48's
  fix wave then reinstated a monotone record for `instantiate_constructor`
  alongside a new per-level one for `tester_clash`; see §11) and 41
  (`2026-07-24-shinri-slice41-datatype-acyclicity-design.md`).
* The preceding queue item —
  `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md`
  and its report, whose success-criteria post-mortem shaped §6.
* The trail pattern §3.2 mirrors — `crates/shinri-str/src/trail.rs`.

## 11. Measured outcomes

**This section records THREE states, in order: the pre-fix measurement below
(commit `17f2ac31092a`, run-id `slice48`), which found that Task 2's
level-indexed `asserted_testers` (§3.2 as originally written) had itself
introduced a wrong-`sat` regression; "What actually shipped", the fix wave
that followed; and the fixed-code re-measure (commit `f27a340ceb77`, run-id
`slice48b`) that closes this section. Do not read the "pre-fix" subsection
below as a description of the shipped code — §3.2 and §3.3 carry their own
superseded-by-§11 markers for the same reason.**

### Pre-fix measurement (run-id `slice48`, commit `17f2ac31092a`) — SUPERSEDED, kept for history

Closing QF_DT re-run, run-id `slice48`, measured at commit `17f2ac31092a`
(same 8,700 paths as the baseline). Full narrative, transition matrix and
family breakdowns:
`docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md`.

#### Success criteria (pre-fix)

| criterion | baseline | slice48 | verdict |
| --- | ---: | ---: | --- |
| 1. `20172804-Barrett` wrong = 0 | 166 | **32** | **MISS** |
| 2. `correct → {timeout,unknown,oom}` = 0 | — | **6** | **MISS** |
| 3. QF_DT `correct` ≥ 7,849 | 7849 | **7978** (+129) | **PASS** |
| 4. randomized generator failed pre-slice, passes now | — | yes | **PASS** |
| 5. `20230720-blocksworld` wrong (measured, not gated) | 162 | **190** (+28) | measured — premise contradicted |

**Criterion 1 was missed, and decomposed rather than relaxed.** The 166
baseline Barrett wrong rows split cleanly on a directory boundary: all 37
`barrett-jsat/tests/` rows (non-`ite`-encoded, including the spec's own named
corpus reproducer `v1l30072.cvc.smt2`) are fixed 100%. All 32 residual/new
wrong rows are in `barrett-jsat/typed/` (nested-`ite`-encoded assertions):
97 of 129 `typed/` baseline-wrong rows were fixed, 1 became an honest
timeout, 31 remain wrong, and 1 previously-`correct` `typed/` row newly
regressed to `wrong` — 31 + 1 = 32. Two candidate mechanisms were
investigated (word_norm's ite-elimination structurally routing a `typed/`
tester's truth value away from `asserted_testers`, and `DtSolver::assert`'s
unconditional `if !lit.is_positive() { return None; }` at `lib.rs:888`,
unchanged since slice 39, which never records or checks a negative tester)
but **neither was confirmed**: a hand-built minimal negative-tester case
answers correctly in both assertion orders. The real mechanism needs a
targeted bisect on one of the 31 residual `typed/` files — queued, not
solved here.

**Criterion 2 was missed, and decomposed rather than relaxed.** All 6
`correct → timeout` rows are Barrett `typed/` instances, all small
(1,293–2,828 B) and fast at baseline (4–14 ms). None overlap the
`wrong → timeout` set, so unlike slice 47's criterion-3 miss there is no
"wrong answer became an honest timeout" component here — all 6 are a
genuine performance cost: re-running `tester_clash` on every `check()` call
adds enough case-split churn on these particular shapes to blow the 20 s
budget on formulas that solved in single-digit milliseconds before. Beyond
this criterion's literal scope, 2 `correct → wrong` rows were also found
(1 Barrett, 1 blocksworld) — a more severe regression than a timeout; both
were bisected (below).

**Criterion 4's evidence.** `qfdt_random_matches_z3` failed on pre-slice code
(task 1's report, commit `90a061b8`, verbatim): `QF_DT SOUNDNESS
DISAGREEMENT (iter 44): shinri=sat z3=unsat` on an instance combining a
positive tester, two negated testers and a selector-collapse equality.
`cargo nextest run -p shinri-solver --features oracle -E
'binary(qfdt_oracle)'` now discovers 17 tests, all 17 pass, including
`qfdt_random_matches_z3: 300 iters, 144 sat / 152 unsat / 4 skipped, 0
mismatches`. The full unfiltered oracle gate (`cargo nextest run -p
shinri-solver --features oracle`) ran 651 discovered, 651 passed, 0 failed,
3 skipped at the same HEAD.

**Criterion 5 — the premise was wrong, and this run says so plainly.** §1
and §9 claimed blocksworld is untouched by this slice because its corpus
files contain zero `(_ is C)` syntax. That is true of the *source*, but
`DtSolver::exhaustiveness_split` (`lib.rs:416`) mints tester atoms
**internally** for every multi-constructor datatype term whose class isn't
yet determined — exactly the machinery blocksworld's 21-constructor
enums/records exercise — and those internally-minted testers flow through
the same `assert`/`asserted_testers` bookkeeping Task 2 changed from a
monotone `HashSet` to a level-indexed `Vec`. Measured effect: blocksworld
wrong rows rose 162 → 190 (+28, mostly previously-`timeout` rows now
completing), and one instance
(`blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2`) flipped
deterministically from a fast correct `unsat` (47 ms) to a fast wrong `sat`
(27 ms) — reproduced identically across 3 reruns. Bisecting in isolated git
worktrees (no source modified) pins this flip to **`e5cc3eea`, Task 2**,
*before* `tester_clash` (Task 3) exists — so the family is not immune to
this slice's changes even though Task 3's new rule never fires on it. A
second `correct → wrong` row, Barrett's `typed/v3l70051.cvc.smt2`, bisects
to a **different** commit, `c0957d4b` (Task 3 itself). Per spec §6 this
criterion is measured, not gated, so neither finding blocks the merge — but
the premise that this slice's blast radius excludes blocksworld is
discarded as stated; the shared `asserted_testers` record is live for that
family too.

### Approach B's un-banking trigger fired (pre-fix)

§8 named its un-banking condition precisely: "a `correct → timeout`
transition (criterion 2) or a material rise in QF_DT `timeout`." This run
produced the first half of that condition directly (6 `correct → timeout`
rows), and the second half is at least suggestive: QF_DT's overall `timeout`
count only fell modestly (507 → 489, -18) despite 137 Barrett rows leaving
`wrong`/`timeout` for `correct`. The next slice should treat Approach B
(propagating `¬is-D(t)` instead of rediscovering the same conflict on every
branch) as a live candidate rather than a deferred efficiency nice-to-have.

### Hypotheses this run discarded (pre-fix)

| hypothesis | verdict |
| --- | --- |
| §1/§9 — blocksworld's 162 wrong rows are a bug fully independent of this slice's changes, since the family has zero tester syntax | **DISCARDED as stated.** The family's *source* has no testers, but `exhaustiveness_split` mints them internally, and Task 2's `asserted_testers` refactor measurably flipped one blocksworld row (bisected to `e5cc3eea`). The 162/190-row bug itself is still unexplained and still queued, but the "fully independent" framing is wrong. |
| word_norm's ite-elimination hides a `typed/`-family tester from `asserted_testers` | **NOT CONFIRMED.** Plausible structurally (a DT-sorted `ite` becomes a fresh symbol plus a Boolean-`ite` defining assertion, routing the tester through ordinary Tseitin clauses rather than a direct assert), but not reproduced by a hand-built minimal case. |
| `DtSolver::assert`'s negative-tester no-op (`lib.rs:888`, unchanged since slice 39) is exploitable on 2-constructor datatypes | **NOT CONFIRMED.** A hand-built `¬is-cons(x) ∧ x = cons(...)` case (both assertion orders) answers `unsat` correctly — the exhaustiveness split's sibling-constructor literal appears to close this gap in the simple case. The `typed/` family's actual mechanism remains unidentified. |

### What actually shipped (supersedes §3.2, §3.3)

The fix wave (commit `f27a340ceb77`) did **not** implement §3.2 as written.
Instead of one levelled `asserted_testers` record shared by both consumers,
`crates/shinri-dt/src/lib.rs` now carries **two** records, split by consumer,
with deliberately opposite retraction disciplines:

* `instantiation_testers_monotone: FxHashSet<TermId>` — the trigger set for
  `instantiate_constructor` ALONE. Never popped. This restores exactly
  slice 40's original monotone semantics (same type, same insertion order),
  because that consumer's lemma is GUARDED (`is-C(t) ⇒ t = C(sel..(t))`, valid
  at level 0 on every branch), so a stale entry can only re-offer an inert
  tautology — never an unsound one — while a *missing* entry costs a lost
  instantiation, which is exactly how the blocksworld regression happened
  (§11's "Re-measured after the fix wave", "root cause of the pre-fix
  regression").
* `conflict_testers_per_level: Vec<(TermId, Lit)>` + `conflict_tester_set` +
  `tester_marks` — the trigger set for `tester_clash` ALONE, backtrack-accurate
  by construction (§3.2's original reasoning for why a conflict-citing record
  must be levelled). `push`/`pop` retract this one only.

Both fields carry doc comments naming their single consumer, the discipline
that consumer requires and why, the commit that briefly merged them
(`e5cc3eea`), the corpus regression that merging caused, and the fences that
pin the split (`crates/shinri-dt/src/lib.rs:36-98`, roughly). The struct-level
doc says explicitly: "Do NOT merge this with `conflict_testers_per_level`."

§3.3's prescribed `debug_assert_eq!(csym, ctor)` was **removed**, not kept: with
the records split, `instantiate_constructor` can legitimately observe a class
whose constructor disagrees with a tester that is still in the monotone record
but has been retracted from the per-level one — `tester_clash` (reading the
per-level record) has correctly gone silent about it, and `instantiate_constructor`
(reading the monotone record) correctly still sees the stale entry and skips.
That is normal operation, not the unreachable state §3.3 assumed, so asserting
the constructors agree there is no longer a valid invariant; the removal is
documented in place with a comment naming this reasoning.

### Re-measured after the fix wave (run-id `slice48b`, commit `f27a340ceb77`)

Full narrative, three-way transition matrix and per-family closure arithmetic:
`docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md`,
"Re-measure after the fix wave" section. HEAD advanced once more after this
run, to `f8b605e957e0` ("final-review fix wave — comments and test strength");
that commit's message states no executable logic changed outside two test
bodies, so this measurement remains representative of current HEAD.

#### Success criteria — baseline / pre-fix / fixed

| # | criterion | baseline | pre-fix (`slice48`) | fixed (`slice48b`) | gate | verdict |
| --- | --- | ---: | ---: | ---: | --- | --- |
| 1 | `20172804-Barrett` wrong rows | 166 | 32 | **31** | 0 (hard gate) | **MISS** |
| 2 | `correct → {timeout,unknown,oom}` | — | 6 | **7** | 0 (hard gate) | **MISS** |
| 3 | QF_DT `correct` | 7,849 | 7,978 | **7,978** | ≥ 7,849 | **PASS** |
| 4 | generator failed pre-slice, passes now | — | yes | yes (carried forward, not re-run) | yes | **PASS** |
| 5 | `20230720-blocksworld` wrong rows | 162 | 190 | **169** | measured, not gated | measured |

**Both hard gates are still missed, and are decomposed here rather than
relaxed.**

**Criterion 1 (31, not 0).** The fix wave repairs exactly one of the 32
pre-fix Barrett wrong rows: `barrett-jsat/typed/v3/typed_v3l70051.cvc.smt2`
(the pre-fix `correct → wrong` regression bisected to `c0957d4b`, Task 3
itself) is `correct` again in `slice48b`, at the same 9 ms it took at
baseline. The other 31 residual `typed/` wrong rows are byte-for-byte the
same 31 files, unchanged in verdict — this fix wave does not touch whatever
mechanism produces them; that bisect is still open and still queued (§9).

**Criterion 2 (7, not 6) — the trigger fired in an unexpected direction.**
Comparing `slice48` → `slice48b` directly on the 6 pre-fix `correct → timeout`
rows: one of them, `barrett-jsat/typed/v3/typed_v3l90023.cvc.smt2`, is
**cured** by the split — 14 ms at baseline, timed out at 20,004 ms pre-fix,
back to 18 ms fixed (the record split removed the redundant `tester_clash`
churn that caused the pre-fix timeout on this specific file). But the fix wave
also **introduces two new** `correct → timeout` rows that were fine at both
baseline and pre-fix: `barrett-jsat/tests/v1/v1l60099.cvc.smt2` (37 ms
baseline, 39 ms pre-fix, 20,006 ms fixed — the first timeout ever recorded in
the `tests/` subfamily, previously believed 100% clean) and
`20230720-blocksworld/blocksworld_from_3_5_0_to_8_0_0_negated_goal_bmc_14.smt2`
(4,368 ms baseline, already a slow 18,315 ms pre-fix, now 20,006 ms fixed — an
already-marginal file pushed over the cap). Net: 6 − 1 (cured) + 2 (new) = 7.
Both new rows are a genuine, if small, performance cost of the split, not a
correctness trade — no wrong answer became either of these timeouts.

**Criterion 2, beyond its literal scope — the `correct → wrong` count.**
Baseline → fixed has exactly **one** `correct → wrong` row (down from 2
pre-fix): `20230720-blocksworld/blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2`
(`unsat` at 47 ms baseline → `sat` at 27 ms pre-fix → `sat` at 30 ms fixed,
deterministic, unchanged by the fix wave). This is the SAME file the pre-fix
report bisected to `e5cc3eea` (Task 2's levelling, before `tester_clash`
existed) — the fix wave's record split does not touch it because its cause is
a **different, pre-existing defect in `shinri-euf`**, not in `shinri-dt`'s
tester bookkeeping: `EGraph::add_term` (`crates/shinri-euf/src/egraph.rs:137`)
records its signature-table insert on the undo log, so a term first
registered above decision level 0 loses its congruence registration on the
next backtrack, and the `seen_terms` guard blocks re-registration forever
after. The selector applications `instantiate_injectivity_selectors` mints
mid-search (e.g. `top(stack C empty)` / `top(stack H empty)`) are bound this
way at level ≥ 1, so two `stack` applications can be merged into one class
while their `top` selector applications are never merged by congruence —
injectivity never derives the resulting equality, and `constructor_clash`
never fires. `Euf::new_var` already documents this exact class of bug ("the
I1 soundness bug") for the ⊤/⊥ sentinels and works around it by registering at
level 0; the general case was never fixed. It reproduces on `main` via a
9-line reduced query (`docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md`
carries it in full). **`blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2`
still answers `sat` because of this `shinri-euf` defect, not because of
anything slice 48 changed** — Task 2's levelling only happened to steer the
search into it (five-variant isolation, same report, proves the levelling
change ALONE is sufficient to flip this file, independent of `tester_clash`).
This is a shared-core defect needing its own slice with the full unfiltered
oracle, not a `shinri-dt` fix; see §9 and the report's "Queued for the next
slice".

**Criterion 3 — 7,978, unchanged from pre-fix, PASS.** The fix wave neither
gains nor loses a `correct` verdict at the QF_DT-total level relative to
pre-fix (individual files move between `correct` and other verdicts as
described above, but they net to zero at this granularity).

**Criterion 4 — carried forward, not re-run.** No `shinri-dt` production
logic changed between the `slice48b` run's binary (`f27a340ceb77`) and the
original evidence (commit `90a061b8`'s pre-slice failure, `c0957d4b`'s fixed
pass); re-running the same oracle binary would show the same result at
non-trivial cost, so the pre-fix report's verbatim failing instance and the
17/17-passing `qfdt_oracle` run (300 iters, 0 mismatches) are cited, not
reproduced. **Its 0 mismatches is not coverage of the `shinri-euf` defect
above** — see §9.

**Criterion 5 — 169, still measured not gated; the §1/§9 premise remains
discarded as stated.** Blocksworld wrong rows moved 162 (baseline) → 190
(pre-fix) → **169** (fixed): the fix wave's record split shifts 28 pre-fix
`wrong` rows to an honest `timeout` and 7 pre-fix `timeout` rows newly
complete as `wrong`, netting −21 from the pre-fix count, but still +7 over
baseline. The family remains perturbed relative to baseline by the shared
`asserted_testers`/instantiation-tester bookkeeping this slice touches, via
internal `exhaustiveness_split` minting rather than any corpus-file syntax —
exactly as the pre-fix measurement found. The family's own 162/190/169-row
bug is still unexplained and still queued (§9); only the one clean
`correct → wrong` regression (above) has an identified cause, and that cause
is `shinri-euf`, not this family's pre-existing bug.

#### Full transition matrix, baseline → fixed (`slice48b`), changed cells only

| baseline | fixed | count | families |
| --- | --- | ---: | --- |
| `wrong` | `correct` | 134 | 20172804-Barrett 134 |
| `timeout` | `wrong` | 17 | 20230720-blocksworld 17 |
| `wrong` | `timeout` | 12 | 20230720-blocksworld 11, 20172804-Barrett 1 |
| `correct` | `timeout` | 7 | 20172804-Barrett 6, 20230720-blocksworld 1 |
| `unverified` | `timeout` | 5 | 20230720-blocksworld 5 |
| `timeout` | `correct` | 3 | 20172804-Barrett 3 |
| `correct` | `wrong` | 1 | 20230720-blocksworld 1 |
| `timeout` | `unverified` | 1 | 20230720-blocksworld 1 |

Unchanged: 8,520 of 8,700. Every verdict count above closes exactly against
the per-family before/after totals (arithmetic shown in the research report).

### Queued for the next slice (fixed-code state — supersedes §9 above)

* **The pre-existing `shinri-euf` congruence-loss defect** —
  `EGraph::add_term` (`crates/shinri-euf/src/egraph.rs:137`), described in full
  above and in the research report. Reproduces on `main`. Needs its own slice
  with the full unfiltered oracle (shared-core change).
* **`qfdt_oracle`'s generator blind spot.** `gen_instance` only emits
  top-level ground conjuncts, so every literal lands at decision level 0 and
  the generator structurally cannot produce the shape either live defect
  needs (a selector-app equality, or a tester, derived above level 0). Extend
  it to emit disjunction-/`ite`-guarded testers and record-shaped datatypes;
  the next slice's generator work must FAIL on this branch's HEAD for the
  `shinri-euf` defect before it is believed to cover it.
* **The 32 (now 31) residual `20172804-Barrett/.../typed/` wrong rows** — the
  fix wave did not move this bisect forward; still needs a targeted bisect on
  one of the 31 files (unchanged from the pre-fix queue).
* **The 6 (now 7) `correct → timeout` Barrett/blocksworld rows and Approach B**
  — the fix wave's own churn added 2 more `correct → timeout` rows rather than
  resolving the un-banking trigger; Approach B (§8) remains a live candidate,
  now with a slightly stronger signal.
* **`20230720-blocksworld`'s own 162/190/169-row bug** — still unexplained,
  still needs a genuine bisect on a 21–53 KB instance (unchanged from §9).
* **QF_DT's remaining `timeout`/`unknown` rows** — out of scope per §2, still
  in the slice-46 queue.
