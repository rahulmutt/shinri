# Slice 49 — EUF congruence lost for terms registered mid-search

**Status:** design
**Date:** 2026-09-11
**Area:** `shinri-euf` (`EGraph` indexing — `add_term`, `pop`, the undo log;
`Euf::propagate` and `Euf::check`), `shinri-euf` tests (a unit regression, an
index-invariant checker, a differential property test), `shinri-solver` tests
(`qfdt_oracle` generator extension, `qfdt_e2e` repro pin). No `EqualityEngine`
change, no `Combiner` change, no `shinri-dt` change, no parser surface change.
**This is a shared-core change:** every logic that routes atoms through EUF
depends on `EGraph`, so the full unfiltered oracle suite is a gate (§6.5).
**Predecessors:** slice 48
(`2026-09-10-shinri-slice48-qfdt-tester-disjointness-design.md`) found this
defect while root-causing its one `correct → wrong` row and queued it as its
own slice (`docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md
› ### Queued for the next slice (current, fixed-code state …)`, first bullet).
Slices 47 and 48 closed ranks 1 and 2 of the slice-46 queue.

## 1. Summary

A term that `EGraph::add_term` registers **above decision level 0**, while an
argument's class is the product of a merge made at that level, is left on the
wrong use-list once the search backtracks. When the classes later re-merge,
congruence over that term is never re-detected. The result is a wrong `sat`.
Datatype injectivity is the path the corpus hits: `shinri-dt` mints selector
applications mid-search (`instantiate_injectivity_selectors`,
`crates/shinri-dt/src/lib.rs:255`), and they reach `add_term` through
`bind_fresh` (`crates/shinri-sat/src/solver.rs:743` →
`crates/shinri-theory/src/combiner.rs:374` → `Euf::new_var`).

Reduced reproducer (from slice 48's delta-debugging; re-run on `main` at
`ee30ad7793c4` for this spec):

```smt2
(set-logic QF_DT)
(declare-datatypes ((E 0)) (((A) (C) (H))))
(declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))
(declare-datatypes ((R 0)) (((R (right T)))))
(declare-fun p () R)(declare-fun q () R)(declare-fun u () R)(declare-fun c () E)
(assert (= (right p) (stack C empty)))
(assert (= q p))
(assert (ite (= c A) (= (right u) (right q)) (= (right u) (right q))))
(assert (= (right u) (stack H empty)))
(check-sat)
```

shinri `sat`; z3 `unsat`; cvc5 `unsat`. Replacing the `ite` with the plain unit
`(assert (= (right u) (right q)))` makes shinri answer `unsat`.

### 1.1 The slice-48 root-cause text is wrong

The slice-48 report attributes the defect to `add_term` recording
`Undo::LookupInsert` for its signature entry, so that the registration is
"undone by the next backtrack" while `seen_terms` blocks re-registration.
**`add_term` records no undo entry at all.** `Undo::LookupInsert` is recorded
only by `recanonicalize_use_list` (`crates/shinri-euf/src/egraph.rs:345`).
`add_term`'s registration is permanent, so the described mechanism cannot occur.
The actual mechanism (§1.2) was confirmed in this spec's brainstorming by a unit
probe and by an instrumented run of the repro above (§1.3). The slice-49 report
records the correction. The historical slice-48 report is not rewritten.

### 1.2 The confirmed mechanism

The congruence index rests on one invariant:

> **(I-use)** At every decision level, every app is on the use-list of the
> **current representative** of each of its arguments.

`recanonicalize_use_list` keeps (I-use) across merges by draining the loser's
use-list into the winner's and re-signing each moved app. `add_term` keeps it at
registration time by pushing the new app onto `use_list[find(arg)]`
(`egraph.rs:172`). It installs the signature with `lookup.insert`
(`egraph.rs:187`). **Neither write is logged.** When `find(arg)` is a
representative only because of a merge at the current level:

1. **Level L ≥ 1.** Classes W and X merge, with W the winner. `add_term(f(x))`
   runs for an `x` in X's class. The app goes onto `use_list[W]`, and signature
   `(f, [W])` goes into `lookup`, both unlogged.
2. **Pop below L.** The equality engine undoes the W/X merge. `UseSplice`
   moves X's original apps back. `f(x)` stays on `use_list[W]`, although `x`'s
   representative is X again. (I-use) is now false.
3. **Re-merge.** Union-by-size breaks ties deterministically
   (`crates/shinri-theory/src/eq_engine.rs:209`), so W wins again.
   `recanonicalize_use_list` walks only the **loser's** list. X's list holds
   nothing for `f(x)`, so `f(x)` is never re-signed, no collision is found, and
   no congruence is enqueued.

The `pending` entry `add_term` may have enqueued at step 1 is stale after
step 2, and `drain_pending`'s guard correctly skips it. So nothing re-derives
`f(x) ≡ f(w)`.

### 1.3 Evidence

**Unit probe.** It was a throwaway edit, reverted; Task 1 reinstates it as a
permanent test. Constants `a` and `b` are merged at level 1, `f(a)` and `f(b)`
are registered, the solver pops to level 0, and `a = b` is re-merged:

```
PROBE level1 f(a)==f(b): true
PROBE after pop f(a)==f(b): false use_list[a]=[2, 3] use_list[b]=[]
PROBE remerge rep(a)=ENodeId(0) rep(b)=ENodeId(0) f(a)==f(b): false
panicked: congruence lost after mid-search add_term + backtrack
```

**Instrumented repro** (throwaway `eprintln!` in `add_term`,
`recanonicalize_use_list` and `pop`, reverted). Node 11 joins class 8 by a
level-0 merge. At level 1, classes 0 and 8 merge, and the four selector apps
(`top` and `rest` on both `stack` applications, apps 13–16) are registered.
Apps 14 and 16, whose argument is node 11, are keyed onto node 0:

```
PROBE49 merge level=0 winner=ENodeId(8) loser=ENodeId(11) moved=[] winner_list=[]
PROBE49 merge level=1 winner=ENodeId(0) loser=ENodeId(8) moved=[] winner_list=[13]
PROBE49 add_term level=1 app_term=TermId(23) op=Uninterpreted(SymbolId(9)) arg=ENodeId(11) keyed_on_rep=ENodeId(0)
PROBE49 pop 1 -> 0
…
PROBE49 merge level=2 winner=ENodeId(0) loser=ENodeId(8) moved=[] winner_list=[13, 14, 15, 16]
```

Every later re-merge of 0 and 8 moves nothing (`moved=[]`), because the apps
are on the winner's list. `top(stack C empty) ≡ top(stack H empty)` is never
re-derived, and the answer is `sat`.

### 1.4 Blast radius

Any theory that causes a term to be registered with EUF mid-search can reach
this: the datatype injectivity path above, and the string F-split skolems and
empty-length-link disjuncts named in `add_term`'s own comment
(`egraph.rs:159–169`). Registration at level 0 is safe, because level-0 merges
never unwind.

## 2. Scope

**In scope:**

* Restoring (I-use), and the matching `lookup` invariant, across backtracking
  for every term registered above level 0.
* Draining congruences enqueued outside `merge_eq`, meaning at registration or
  re-index time, at `Euf::propagate` and `Euf::check`.
* Tests that fail on pre-slice `main` at three layers: `EGraph` unit and
  property, QF_DT oracle, and e2e.
* Re-measuring QF_DT, QF_UF, QF_UFLIA, QF_UFLRA and QF_S (§7).

**Out of scope** (queued in §10, not fixed here):

* The `Owner::Shared` definitional merge that bypasses EUF
  (`combiner.rs:185`).
* Slice 48's other QF_DT residuals, which are re-measured but not claimed.
* Any `shinri-dt` change.
* Any `EqualityEngine` change.

## 3. The fix

All production changes are in `crates/shinri-euf/src/egraph.rs`, plus two
call-site lines in `crates/shinri-euf/src/solver.rs`.

### 3.1 Registration versus indexing

`add_term` does two different things today. The fix gives them different
lifetimes:

| | state | across backtrack |
| --- | --- | --- |
| **Registration** | `apps`, `is_app`, `terms`, `seen_terms` | **permanent**, unchanged. The atom's SAT variable is permanent, so the theory's knowledge of the term must be too. |
| **Indexing** | the use-list push per argument, the `lookup` insert | **undoable**, re-applied after pop (§3.3) |

Undoing *registration* would be wrong. The SAT variable for an atom such as
`sel(p) = a` outlives the level, so a later `assert` of it would reach
`cx.eq.intern` with no app structure behind it.

### 3.2 `index_app` and `Undo::AppIndexed`

Extract the tail of `add_term`, everything after the argument recursion and the
`apps.push`, into `fn index_app(&mut self, eq: &EqualityEngine, app: AppId)`:

1. For each argument node `an`, in order, push `app` onto
   `use_list[find(an)]` and remember `find(an)` in `reps`.
2. Compute the signature. If `lookup` has it with another app, enqueue a
   congruence (unchanged behaviour) and set `inserted_sig = None`. Otherwise
   insert it and set `inserted_sig = Some(sig)`.
3. If `self.undo.level() > 0`, record
   `Undo::AppIndexed { app, reps, inserted_sig }`. At level 0 record nothing,
   because `UndoLog` never unwinds entries recorded before the first
   `push_level`.

`add_term` calls `index_app` where it currently does steps 1–2 inline.

In `EGraph::pop`, undoing `AppIndexed { app, reps, inserted_sig }`:

* For `rep` in `reps` **reversed**, pop the tail of `use_list[rep]`, with
  `debug_assert_eq!(popped, app)`.
* If `inserted_sig` is `Some(sig)`, `debug_assert_eq!(lookup.get(&sig), Some(&app))`
  and remove it.
* Push `app` onto a new field, `reindex: Vec<AppId>`.

**Why the tail pops are exact.** Once every use-list write is logged, LIFO
unwinding restores list contents exactly. Any `UseSplice` recorded after the
push, which moved this list into a winner, is undone first, and that returns
the app to this list's tail. The same argument makes the existing
`UseSplice` undo's `split_off(total - count)` tail assumption (`egraph.rs:115`)
true by construction. Today it is violated by exactly the unlogged pushes this
slice removes. It is pinned under `cfg(debug_assertions)`: `UseSplice` also
carries the moved `Vec<AppId>` (debug builds only), and its undo
`debug_assert_eq!`s the split-off block against it.

### 3.3 Lazy re-index

`TheorySolver::pop` has no `TheoryCtx`, and the combiner pops `eq` before `euf`
(`combiner.rs:500–501`). So `EGraph::pop` can only queue, and re-indexing
happens at the next entry point that holds the equality engine:

```text
fn flush_reindex(&mut self, eq: &EqualityEngine)
    // registration order: reindex was filled in LIFO order, so walk it reversed
    for app in reindex.drain(..).rev() { self.index_app(eq, app) }
```

`index_app` records a fresh `AppIndexed` at whatever level is current at flush
time, so an app follows the unwinding until it is indexed at level 0.

**Flush points.** At the very start of `add_term` (before the `seen_terms`
guard), `merge_eq`, `assert_diseq`, and `close` (§3.4). No merge, collision
check or drain can then observe a half-indexed graph. `flush_reindex` is O(1)
when the queue is empty.

### 3.4 `close` — drain congruences at propagate and check

Congruences enqueued by `index_app` sit in `pending` until something calls
`drain_pending`, and today only `merge_eq` does. A collision found at
registration or re-index time with no later merge would never close. Add:

```text
pub fn close(&mut self, eq: &mut EqualityEngine) -> Option<Vec<EqLeaf>>
    self.flush_reindex(eq); self.drain_pending(eq)
```

* `Euf::propagate` (`solver.rs:156`) calls `close` first and returns its
  conflict through the existing `Option<Vec<EqLeaf>>`. The combiner already
  returns `euf.propagate`'s conflict (`combiner.rs:862`).
* `Euf::check` (`solver.rs:174`) calls `close` and returns
  `TCheck::Conflict(leaves)` on a conflict. The combiner already maps it
  (`combiner.rs:614`).

Merges produced by `close` go through `eq.merge_congruence`, the same path as
`merge_eq`'s congruence merges, so they reach the combiner's merge-event
consumers unchanged.

### 3.5 What does not change

* `pending`'s staleness guard (`egraph.rs:286`) and its sole-consumer note.
  `close` consumes it only through `drain_pending`.
* `recanonicalize_use_list`, `LookupInsert`, `LookupOverwrite` and `UseSplice`
  semantics.
* The ⊤/⊥ sentinels, `eq_atoms`, `propagated`, `prop_records`, `model` and
  `explain`.
* Any other crate's production code.

## 4. Index invariant checker and edge cases

### 4.1 `check_index` (test-only)

`#[cfg(test)] fn check_index(&self, eq: &EqualityEngine) -> Result<(), String>`
checks:

* **(I-use)** For every app not in `reindex` and every argument position `i`,
  `use_list[find(args[i])]` holds `app` exactly as many times as `find(args[i])`
  occurs among `find(args[..])`.
* **(I-lookup)** For every app not in `reindex`, `lookup[sig(app)]` exists and
  names an app whose node is in the same class as `app`'s node, or is connected
  to it by a live, non-stale `pending` entry.
* **(I-queue)** No app in `reindex` is on any use-list or named by any `lookup`
  entry.

It is called after every operation in the unit and property tests. It is not
wired into debug solver builds, because an O(apps) scan per operation would
slow the blocking test tier.

### 4.2 Edge cases (each a unit test calling `check_index`)

1. **Duplicate arguments**, e.g. `f(a, a)` registered at level 1: two pushes,
   then two tail pops in LIFO order on undo.
2. **Nested registration**, e.g. `g(f(a))` at level 1: `f(a)` is indexed
   before `g`, each with its own `AppIndexed`. Undo runs `g` then `f`; the
   flush re-indexes `f` then `g`.
3. **Loser of a later merge.** An app is indexed onto R at level L, then R
   loses a merge at level ≥ L. Undo reverses the splice first, then the
   `AppIndexed` tail pop finds the app on R.
4. **`lookup` overwritten after the insert.** A later `LookupOverwrite` on the
   same signature is undone first, so the `debug_assert` that
   `lookup[sig] == app` holds.
5. **Multi-level pop, then a push, then the first flush.** The flush records
   `AppIndexed` at the higher level; a pop below that level re-queues the app.
6. **The `seen_terms` early return while an app is queued.** The flush runs
   before the guard, so the app is indexed on return.
7. **A congruence discovered during the flush.** It is enqueued only. The next
   `close` or `merge_eq` drains it, and a pop in between leaves it stale, which
   the guard skips.
8. **The §1.3 regression.** Register at level 1 over a level-1 merge, pop to 0,
   re-merge with `merge_eq`, which drains; `f(a) ≡ f(b)` must hold. It uses
   only APIs that exist on `main`, so it compiles and fails there. The throwaway
   probe did exactly this.
9. **A registration-time collision with no later merge** (§3.4), at the `Euf`
   level. At level 1, merge `a = b`. Then `new_var` registers the atom
   `(= f(a) f(b))`, so `add_term` enqueues the `f(a)`/`f(b)` collision, and its
   negation is asserted (`assert_diseq` succeeds, because `pending` is
   undrained). `Euf::propagate` or `Euf::check` must now return a conflict. By
   reading, on `main` both return nothing and `check` returns `Sat`: nothing
   drains `pending`, and `collect_eq_propagations` sees `f(a)`, `f(b)` unequal.
   This has not been run; Task 5 records the actual failure.

## 5. Tasks

Every test task must record, in its task report, the test **failing on
pre-slice `main`** (the exact failure output). It lands before the fix it
covers.

1. **Unit regression and `check_index`** (§4.1, §4.2 case 8). Must fail on
   `main`.
2. **Differential property test** (§6.2). Must fail on `main`; the minimized
   failing trace is quoted.
3. **`qfdt_oracle` generator extension** (§6.3). Must fail on `main` with a
   quoted z3 disagreement, run with `--features oracle` and a non-zero
   discovered count confirmed.
4. **`index_app`, `Undo::AppIndexed` and the lazy re-index** (§3.2, §3.3),
   with edge-case unit tests 1–7 (§4.2). Tasks 1 and 2 go green. Task 3 is
   expected green; if it is not, Task 5 must turn it green, and the task report
   says which.
5. **`close` at `Euf::propagate` and `Euf::check`** (§3.4), with §4.2 case 9,
   which must fail on `main` before this task's code lands. A separate commit,
   so its search-trajectory effect is reviewable and bisectable apart from
   Task 4.
6. **e2e pin** of the §1 repro in `crates/shinri-solver/tests/qfdt_e2e.rs`,
   expecting `unsat`.
7. **Gates** (§6.5).
8. **Bench re-run and report** (§7), including the slice-48 root-cause
   correction (§1.1).
9. **Whole-branch review** before the PR. This slice changes identity and
   keying (which use-list an app lives on, and which `lookup` entry it owns)
   inside a soundness path. That is the class slice 44's final review caught
   after all seven task reviews missed it.

## 6. Testing

### 6.1 Unit (`crates/shinri-euf/src/egraph.rs` tests)

§4.2 cases 1–8, each asserting both the observable congruence result and
`check_index`. Case 9 lives in `crates/shinri-euf/src/solver.rs` tests,
because it exercises `Euf::new_var`, `assert`, `propagate` and `check`.

### 6.2 Differential property test

`EGraph` lives in a private module (`crates/shinri-euf/src/lib.rs`:
`mod egraph;`), so the test is in-crate, using the existing `proptest`
dev-dependency (`crates/shinri-euf/Cargo.toml:15`).

* **Signature.** One uninterpreted sort, 4–6 constants, unary `f` and binary
  `g`, and a pool of candidate apps up to depth 2.
* **Operations** (weighted): `push`; `pop(k)` to a random lower level;
  `merge_eq(x, y)`; `assert_diseq(x, y)`; `add_term(t)` for an unregistered
  pool term; `drain`. Registration is biased to land right after a merge at
  the current level. That is the defect's shape; without the bias, a random
  trace almost never reaches it.
* **`drain`** is a test-local helper, `merge_eq(k, k)` for a fixed registered
  constant `k`. It is the drain idiom of
  `stale_pending_congruence_not_drained_after_backtrack`, and it exists on
  `main`, so the test compiles and fails there. After Task 4, `merge_eq`
  flushes first, so `drain` behaves like `close`.
* **Conflicts.** On a returned conflict the trace pops one level, or ends if
  at level 0, as the SAT solver would.
* **Reference.** After each `drain`, recompute from scratch a naive congruence
  closure over the live asserted equalities (a per-level stack) and all
  registered terms. Then assert:
  * for every pair of registered terms, `eq.are_equal` matches the reference;
  * the engine reported a conflict iff some live disequality's sides are equal
    in the reference;
  * `check_index` is `Ok`.
* **Budget.** The case count and trace length are bounded so the test runs in
  seconds on the blocking tier. It must find the §1.2 defect on `main` within
  that budget; if not, the generator is re-tuned before Task 4 starts.

### 6.3 `qfdt_oracle` generator (`crates/shinri-solver/tests/qfdt_oracle.rs`)

`gen_instance` (`qfdt_oracle.rs:373`) emits only top-level ground conjuncts, so
every literal lands at level 0 and the §1.2 shape is unreachable. That is why
slice 48's 300 iterations with 0 mismatches did not cover this defect. Extend
it (as a new generator or a mode of the existing one) with:

* a record-shaped datatype whose field is itself a constructor-bearing
  datatype, the `R`/`T`/`E` shape of §1;
* equalities between selector applications and constructor terms wrapped in
  `ite` or `or` guards over a free discriminant, so they are derived only
  under a decision.

Pass criterion: 0 mismatches against z3 after the fix. Required pre-fix: at
least one mismatch on `main`.

### 6.4 e2e (`crates/shinri-solver/tests/qfdt_e2e.rs`)

The §1 repro, expecting `unsat`. Also the unit-equality variant, expecting
`unsat`, as a guard that the fix does not depend on the `ite`.

### 6.5 Gates

* `mise run test` (the blocking tier).
* `cargo nextest run -p shinri-solver --features oracle`, **unfiltered**.
  This is a shared-core change, and a filtered run nearly shipped slice 40's
  string regression.
* `script_e2e` locally before pushing
  (`cargo nextest run -p shinri-solver -E 'binary(script_e2e)'`, discovered
  count confirmed non-zero).
* `mise run lint` and `cargo fmt --all`.

## 7. Measurement

Run-id `slice49`, same limits as the baseline (20 s / 3072 MB / 6 jobs):

```
BENCH_LOGICS=QF_DT,QF_UF,QF_UFLIA,QF_UFLRA,QF_S BENCH_RUN_ID=slice49 mise run bench-run
```

It is reported to
`docs/superpowers/research/2026-09-11-smtlib-2024-slice49-euf-report.md`, with
per-logic transition matrices against the most recent committed run covering
that logic:

* QF_DT: `slice48b`;
* QF_UF, QF_UFLIA, QF_UFLRA, QF_S: `baseline-8de004d44944`. The
  `rerun-0fca46476479` re-classification assigns these logics' re-run rows the
  same verdicts as the baseline: QF_UF parse-error 34; QF_UFLIA oom 5; QF_UFLRA
  parse-error 1,229 and oom 10; QF_S has no re-run rows. So the baseline row
  stands unmodified.

### Comparison baselines

| logic | total | correct | wrong | timeout | other |
| --- | ---: | ---: | ---: | ---: | --- |
| QF_DT (`slice48b`) | 8,700 | 7,978 | 200 (blocksworld 169, Barrett 31) | 510 | unknown 11, unverified 1 |
| QF_UF | 7,503 | 7,106 | 0 | 363 | parse-error 34 |
| QF_UFLIA | 659 | 103 | 11 | 523 | oom 5, unknown 17 |
| QF_UFLRA | 1,284 | 44 | 0 | 1 | parse-error 1,229, oom 10 |
| QF_S | 18,940 | 16,025 | 2 | 8 | unknown 2,809, unverified 96 |

### Success criteria

| # | criterion | gate |
| --- | --- | --- |
| 1 | Tasks 1–3's tests and Task 5's §4.2 case 9 each failed on pre-slice `main` (recorded) and pass now | **hard** |
| 2 | §1 repro answers `unsat` | **hard** |
| 2b | `blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` answers `unsat` | **measured**; if still `sat`, the report traces it to a named cause before merge. Delta-debugging reduced it to the §1 repro, but that does not prove §1.2 is its only cause. |
| 3 | `correct → wrong` transitions, all five logics | **0 — hard** |
| 4 | QF_DT `wrong` | **≤ 200 — hard**; the actual delta is reported per family |
| 5 | per-logic `correct` | **≥ comparison run — hard**, excluding only rows that an A/B re-run shows flip identically on pre-slice `main` (boundary noise); every excluded row is listed |
| 6 | `correct → {timeout, unknown, oom}` transitions | **measured**; each row A/B-timed on pre-slice `main` against `slice49`, and those confirmed slower are reported as the slice's cost |
| 7 | `* → wrong` from a non-`correct` verdict (e.g. `timeout → wrong`) | **measured**; each row checked for whether pre-slice `main` answers the same wrong answer given a longer timeout |
| 8 | QF_UFLIA 11 and QF_S 2 wrong rows | **measured, not gated** |

**Criterion 4 claims no specific number.** Only one of slice 48's 200 wrong
rows, `bmc_2`, is traced to §1.2. The report must say which rows moved, and
must make no causal claim about any row without a trace. A slice that is fully
implemented and reviewed can still deliver nothing on the corpus (slice 42);
only the measured result says whether this one did.

**Criterion 5 replaces slice 48's "0 `correct → timeout`" hard gate,** which was
missed on 7 boundary rows. A per-logic `correct` floor with an explicit,
evidenced noise exclusion gates what matters, a real loss of answers, without
being defeated by 20-second-boundary jitter. Criterion 6 keeps the individual
rows visible.

## 8. Named reproducers

| path / query | expects | shinri on `ee30ad7793c4` |
| --- | --- | --- |
| §1 inline query (`ite`-guarded) | `unsat` | `sat` |
| §1 inline query with the `ite` replaced by its unit equality | `unsat` | `unsat` |
| `bench/corpus/QF_DT/20230720-blocksworld/blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` (9,814 B) | `unsat` (`:status`, z3) | `sat` |

## 9. Banked, not built

**Approach B — mint DT selector applications at level 0.** Registering
`sel_i(c)` for every constructor application and field during DT registration
would keep the injectivity path from minting mid-search. It is banked because it
closes only one caller: the string F-split skolems, interface atoms, and any
future minter would still reach §1.2. Slice 48 already ruled out a DT-only fix
for a shared-core defect. **Un-bank only** as a perf measure, if §7 criterion 6
attributes QF_DT `correct → timeout` rows to re-index churn on selector apps.

**Approach C — use-lists keyed by raw argument node, with a class-member walk
on merge.** This removes the whole class structurally, because apps never move.
It is banked because it rewrites the congruence core over a new undoable
class-member ring in `EqualityEngine` (`shinri-theory`), which every logic
uses, for a defect that §3 fixes locally. **Un-bank** if a second, independent
(I-use) violation class turns up that `AppIndexed` does not cover. The first
candidate is §10's `combiner.rs:185`, if it proves live.

## 10. Queued for the next slice

* **`Owner::Shared` definitional merge bypasses EUF** (`combiner.rs:185`). The
  purification path merges `w = def` directly in the shared `EqualityEngine`
  with `EqJust::Definitional`. It skips EUF's `recanonicalize_use_list`, and
  the merge is logged at the current level. If `bind_fresh` reaches this arm
  mid-search, a "holds unconditionally (level 0)" equality would be undone on
  backtrack, and EUF's use-lists would not reflect the merge while it holds.
  **Unverified:** it needs a named repro reaching the arm above level 0 before
  it is a diagnosis.
* **Slice 48's other QF_DT residuals** — the 31 Barrett `typed/` wrong rows,
  the rest of blocksworld's wrong rows, and the 7 `correct → timeout` rows —
  unless §7 shows this slice moved them. The report states what moved.
* **The rest of the slice-46 queue:** rank 3 (the 55 small wrong-answer
  clusters, including the QF_S wrong `unsat`), then the `blast_word` panic
  bucket.

## 11. References

* Slice 48 spec and report —
  `docs/superpowers/specs/2026-09-10-shinri-slice48-qfdt-tester-disjointness-design.md`,
  `docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md`
  (`#### Root cause of blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2`,
  corrected by §1.1).
* Baseline — `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Next slices) and `2026-09-09-smtlib-2024-baseline-report.md`.
* The prior use-list keying fix this slice completes — the comment at
  `crates/shinri-euf/src/egraph.rs:159–169` (keying by representative to avoid
  the "loser use-list not empty on undo" panic). That fix chose the right list
  at registration time but left the write unlogged.
* The prior backtracking-staleness fix §3.4 relies on —
  `EGraph.pending`'s slice-8 cluster-C invariant (`egraph.rs:51–60`) and
  `stale_pending_congruence_not_drained_after_backtrack`.
* The ⊤/⊥ precedent for "registration must survive backtracking" —
  `Euf::new_var`'s I1 note (`crates/shinri-euf/src/solver.rs:92–99`).
