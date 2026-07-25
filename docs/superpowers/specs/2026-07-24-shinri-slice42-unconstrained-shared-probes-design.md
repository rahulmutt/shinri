# Slice 42 — Pruning Nelson–Oppen probes over unconstrained shared vars

**Status:** design
**Date:** 2026-07-24
**Area:** `shinri-arith` (`entailed_equalities`, `model_equal_shared_pairs`, and
the entry points that constrain a problem var). No `Combiner` change, no
`shinri-dt` change, no new crates, no `shinri-core`/`shinri-parser` surface, no
new theory slot.
**Predecessors:** slice 40 (tester case-splitting) minted the selector
applications that expose this; slice 41 (acyclicity) left `DtSolver` in its
current shape. Neither is modified here.

## 1. Summary

A datatype whose constructor has an `Int` field makes every QF_DT query
quadratically expensive in the number of datatype terms, **even when the formula
contains no arithmetic atom at all**.

`DtSolver::instantiate_constructor` mints one selector application `head(t)` per
constructor instantiation. Those are `Int`-sorted uninterpreted applications, so
`Euf::shared_arith_terms` (`shinri-euf/src/solver.rs:235`) — which filters
registered terms by **sort alone** — sweeps every one of them into the
Nelson–Oppen shared set `S`. Arith is then asked, once per exchange round, which
equalities over `S` it entails. Every one of those terms is an unconstrained
fresh problem var sitting at β = 0, so `entailed_equalities`' same-β pre-filter
(`shinri-arith/src/lib.rs:704`) admits **every pair**, and each pair costs a
slack definition plus two simplex probes. None can ever succeed.

Measured on a chain of `n` nested `((_ is nil) (tail …))` constraints:

| n | 12 | 16 | 20 | 24 |
|---|---|---|---|---|
| `(cons (head Int) (tail List))` | 0.76 s | 3.1 s | 9.4 s | 24.1 s |
| `(cons (head U) (tail List))`, `U` uninterpreted | — | — | 6 ms | — |
| `(cons (tail List))`, no field | — | — | 5 ms | — |

**A ≈1600× slowdown at n = 20 attributable solely to the field's sort** (9.4 s
vs 6 ms against the uninterpreted-field baseline — same term count, same
structure, same number of DT lemmas).
Instrumentation confirms the location: 100 % of wall-clock is inside
`Combiner::check` at `Effort::Full` across only 123 calls (≈76 ms each), with
`|S| = 40`, 143 exchange rounds total and **0** round-cap hits. The round cap
(`combiner.rs:605`) is not implicated; the per-round pairwise probing is.

Slice 42 adds one guard, applied at two sites (§3.B, §3.C): **arith never probes
or splits on a pair whose var it has received no constraint about.** No `sat` or
`unsat` verdict changes — the slice removes no deduction. It is not, however,
strictly verdict-neutral in one direction: see §4.A.

## 2. Why not fix the shared set instead

The conceptually correct fix is to stop over-approximating `S`. Nelson–Oppen
defines the shared set as terms occurring in *both* theories' constraints;
`shared_arith_terms`' sort-only filter admits terms that occur in no arith
constraint whatsoever. Narrowing `S` to `Int`/`Real` terms appearing in
`Arith`- or `Shared`-owned atoms would eliminate the probing *and* the
downstream per-round bookkeeping.

It is deferred (§6) for two reasons:

1. **Blast radius.** `S` is consumed by the exchange in both directions and by
   MBTC; changing it changes the `Combiner`, the highest-risk surface in the
   codebase. Under-approximating `S` costs completeness — a missed arith→EUF
   equality lets EUF miss a contradiction, i.e. wrong `sat`.
2. **The soundness argument is global.** It must show that no chain of
   EUF-derived equalities can carry information between two arith-constrained
   terms via an excluded one. That argument is available — selector-collapse
   produces `head(x) = 1` as an `Int`-sorted equality *atom*, which classifies
   as `Shared` and so stays in `S` — but it depends on the classification of
   every equality shape the DT and string layers can emit.

This slice's guard rests instead on a **local** invariant internal to
`shinri-arith` (§4), and leaves `S` and both exchange directions byte-for-byte
as they are.

## 3. The rule

### 3.A Constrainedness tracking

`Arith` gains a union-find over problem vars. Three entry points mark a var as
carrying a **real** constraint; the fourth **joins** two vars into one class
without marking either:

| Entry point | Site | Effect |
|---|---|---|
| Atom registration | `new_var`, `lib.rs:1303` | **marks** — the var occurs in a registered arith atom (including B&B branch/cut atoms routed via `Combiner::bind_fresh`) |
| Assertion | `assert`, `lib.rs:1349` | **marks** — the atom's bound is on the trail |
| Numeral pin | `ensure_shared_var`, `lib.rs:659` | **marks** — a numeral pinned to its value *is* a constraint |
| Interface equality | `assert_interface_equality`, `lib.rs:944` (via `consume_interface_equality`, `lib.rs:1438`) | **joins only** — the EUF→arith equality pins `av - bv = 0`, a real constraint on the *difference* that carries no information about either value |

`is_constrained(v)` reads the flag at `v`'s class root, so a class counts as
constrained iff **some** member carries a real constraint. The last row was a
marking site until task 4b: marking both sides let `DtSolver`'s collapse lemma
`head(cons(h,t)) = h` — a congruence-only equality between two `Int`-sorted
terms — mark every selector application, so the guard fired on nothing and the
measured n = 24 chain still took 22 s. A class of mutually-equal free vars is
still free; §4.B (L3) proves it.

The asymmetry in the numeral row is the other half of the point:
`ensure_shared_var` marks **only** on the numeral-pin branch. A shared term arith
was merely told exists — no numeral value, no atom — stays unconstrained. That is
exactly the `head(t)` population.

**Both components are monotone: a mark is never cleared and a union is never
undone, including on `pop`.** After backtracking, a var constrained only by a
since-retracted assertion stays marked, and a class joined by a since-retracted
interface equality stays joined, so both are still probed. This
over-approximates constrainedness, which errs toward *more* probing — the sound
direction. Making either backtrack-exact would prune more and is not worth the
pop-ordering hazard.

### 3.B The guard

In `entailed_equalities`, at candidate construction (`lib.rs:722`–`735`), skip a
pair when **either** var is unconstrained — after task 4b, when either var's
interface-equality class is (§3.A).

The guard MUST sit at candidate construction, before the `define_slack` loop at
`lib.rs:742`–`746`. Slacks minted for a candidate pair **persist across calls**:
the snapshot at `lib.rs:751` is taken *after* `define_slack`, the final `restore`
(`lib.rs:801`) restores to that post-definition snapshot, and
`Vars::slack_var` memoizes the combination. A guard placed later would leave the
`u − v` rows behind on the first call and pay for them forever.

That persistence is also why the predicate cannot be inferred from the tableau.
The natural reading — "no bounds and appears in no row" — is correct on the
first call and wrong on every subsequent one, because the probe slacks put every
previously-probed var into a row. Constrainedness must be tracked explicitly.

### 3.C MBTC

The same guard applies in `model_equal_shared_pairs` (`lib.rs:809`), which feeds
the MBTC trichotomy split at `combiner.rs:813`. It runs the identical same-β
pairwise sweep over `S` and hands the `Combiner` the first model-equal pair,
which becomes a 3-way `(= u v) ∨ (< u v) ∨ (> u v)` split. With 40 unconstrained
vars at β = 0 those splits are pure waste — arith constrains neither side, so
any arrangement EUF chooses is arith-satisfiable. *(As a general claim about
free vars that is false; §4.B refutes it and proves the pair-local version the
guard actually needs.)*

This is a **distinct soundness sub-claim** from §3.B (arrangement agreement
rather than equality entailment) and gets its own test (§5). It is included
because it is the same invariant over the same var set in the same file, and
omitting it leaves a second, smaller source of the same waste in place.

## 4. Soundness

> **Superseded in part.** The var-level invariant stated immediately below, and
> its §3.C consequence, are the pre-implementation sketch. §4.B is the audit of
> record: it refutes the general §3.C reading, and task 4b restates the whole
> invariant at **class** granularity, which is what the shipped guards rest on.
> Read §4.B for the authoritative statement.

**Invariant.** *A problem var that arith has received no constraint about is
free: for any assignment satisfying arith's constraints there is another,
differing only in that var, that also satisfies them.*

Two consequences:

- **§3.B.** `u = v` is not entailed by arith for any `v` when `u` is free —
  shift `u`. Skipping the probe therefore cannot drop an entailed equality,
  which is the only way this change could cost completeness.
- **§3.C.** Any arrangement of a free var is arith-satisfiable, so arith has
  nothing to contribute to deciding it and MBTC's split is not needed for
  agreement.

Vars are deduped to distinct problem vars before pairing (`lib.rs:697`–`704`), so the
degenerate `u = u` case does not arise.

**The invariant is only as strong as the exhaustiveness of §3.A's four entry
points.** Establishing that no other path can constrain a var — and that the
monotone set is genuinely conservative under `push`/`pop` — is the substantive
work of this slice; the guards themselves are a handful of lines. The
implementation plan
must carry that audit as an explicit task with its findings recorded, not fold
it into the coding task.

### 4.A One permitted verdict change: `unknown` → decided

The slice removes no deduction, so no `sat` can become `unsat` or vice versa,
and nothing decided can become `unknown` on that account. There is one
asymmetric exception, and it is an improvement rather than a regression.

`Arith::STRING_PATH_PIVOT_BUDGET` and `STRING_PATH_BRANCH_BUDGET`
(`lib.rs:214`, `lib.rs:205`) exist precisely because the String↔Arith length
seam feeds `entailed_equalities` / `model_equal_shared_pairs` a degenerate
system whose probing re-solves simplex unboundedly; on exhaustion `check_full`
returns a **sound `Unknown`**. Those budgets are cumulative over a solve. Pruning
hopeless probes consumes fewer pivots, so a query that previously exhausted its
budget and bailed to `Unknown` may now finish and decide.

That is `unknown` → `sat`/`unsat`: sound, an improvement, and an **adjudicated
flip** in the sense slices 40 and 41 used the term. It must still be
z3/cvc5-confirmed before any pin is updated. Every other flip direction remains
a regression (§5).

This also means the string path — not just QF_DT — is in this slice's blast
radius, which is a further reason the oracle run must be unfiltered (§5).

### 4.B Entry-point audit (recorded during implementation)

Method: every non-test writer of `bounds` in `shinri-arith` (`apply_bound` at
`lib.rs:433` is the funnel; `Bounds::tighten` at `bounds.rs:73` the primitive),
every non-test writer of the tableau (`Tableau::define_slack`,
`Tableau::pivot`), and every emitter of a fresh atom. Line numbers are against
`crates/shinri-arith/src/lib.rs` after task 4b landed.

**Invariant (class-level — this is what the guards rest on).** *A class carrying
no real constraint is free **as a class**: for any assignment satisfying arith's
live constraints there is another that differs from it exactly by shifting one
live interface-component of that class by the same `±1`.*

This replaces the var-level statement in §4's preamble, which task 4b made too
weak: once interface equalities only *join*, a var in a free class is no longer
independently shiftable — it is pinned to its class-mates — so the argument has
to move the whole component at once. Lemma L3 proves the invariant, and C2
covers the one case the shift cannot separate.

**Vocabulary.** A var is **really marked** iff one of the three marking sites in
§3.A's table fired for it. `class(u)` is `u`'s union-find class and
`real(class(u))` the OR stored at its root, so
`is_constrained(u) = real(class(u))`. Write `K(u)` for the **live interface
component** of `u`: the vars reachable from `u` along interface-equality bounds
that are currently installed (not undone by `pop`). Every such bound's site also
unions, and unions are never undone, so

> **(†)** `K(u) ⊆ class(u)` — hence `real(class(u)) = false` implies that no
> member of `K(u)` is really marked.

The class is the over-approximation the guards read; the component is what the
shift moves. Over-approximating (a class wider than the live component, a mark
that outlived its assertion) can only make `is_constrained` return `true` more
often, i.e. probe more — the sound direction.

| Site | Marks? | Why that is correct |
|---|---|---|
| `new_var` atom registration (`lib.rs:1303`) | yes | dominant site; marks every problem var of the normalized comb, so it covers multi-var atoms whose encoding is over a slack |
| `assert` → `apply_bound` (`lib.rs:1349`, `1350`) | yes | the atom's bound goes on the trail. Unreachable without `new_var` (it indexes `self.enc`, sized there), so this is belt-and-braces over the row above |
| `ensure_shared_var` numeral pin (`lib.rs:659` mark, `667`/`668` tighten) | yes | a numeral is fixed to its value. This is what keeps a DT collapse to a *constant* (`head(cons(5,t)) = 5`) probeable, and with it the QF_DT⋈arith anchors |
| `ensure_shared_var` non-numeral path (`lib.rs:648`–`674`) | **no** | installs no bound and no row. It is not quite "nothing": `problem_var_sorted` (`lib.rs:652` → `vars.rs:46`) stamps Int-sortedness, which restricts the var to ℤ and makes it eligible for the a-priori box. Harmless — the shift step below is integral. The population this slice prunes |
| `assert_interface_equality` (`lib.rs:944` **join**, `962`/`965` bound, `947` row) | **no — joins instead** | it pins `av - bv = 0`, which is a real constraint on the *difference* and carries no information about either value, so it is a class edge and not a mark (task 4b). L1 below still carries it as a primitive bound. Marking here was the pre-4b rule and it made the guard fire on nothing: DT's collapse lemma emits `head(cons(h,t)) = h` for every constructor instantiation, so every selector app got marked through a congruence-only equality |
| `seed_apriori_if_needed` (`lib.rs:1255`, `1256`) | **no** | seeds a UNIFORM `[-M, M]` box on every non-slack Int var. `lo`/`hi` are computed once (`lib.rs:1244`–`1245`) outside the loop and nothing on this path narrows per var. `apriori_bound` (`lib.rs:1206`) gives `M = (n+1)·((n+m)a+1)^(n+m)` with `a = apriori_coeff_max ≥ 0` and `n ≥ 1` whenever the loop bounds anything, so `M ≥ 2`: the box always admits ≥ 5 integer values. Two vars in a box of width ≥ 2 are not entailed equal. Marking here would mark every Int var and defeat the slice |
| `run_fbbt` (`lib.rs:1277`) | **no** | a *derived* site: it emits only consequences of the bounds and rows already present (Lemma L2). Note it CAN bound a slack — `propagate.rs:111`–`133` sweeps every var, slacks included, and `bounds.upper(v).is_none_or(…)` makes any finite derived interval on a bound-free slack count as strictly tighter, so it is emitted and installed permanently at level 0. L1 below is therefore stated over *primitive* bounds only, and this row is discharged by L2 instead |
| `probe` (`lib.rs:882`) | **no** | the probe's own synthetic strict bound. Undone by `restore` (`lib.rs:766`–`780`) after every probe and once more before `entailed_equalities` returns (`lib.rs:801`), so nothing survives the call. *(Site the plan's draft table omitted.)* |
| `atom_var_and_rhs` slack row (`lib.rs:331`) | n/a | the comb is the registered atom's, whose vars `new_var` marked |
| `entailed_equalities` probe slack rows (`lib.rs:745`) | **no** | the one row family whose *defining comb* can span an unmarked var. Persists across calls (the snapshot at `lib.rs:751` is taken *after* the rows exist, and `pop` does not restore the tableau) — but carries no surviving primitive bound, and by L1 acquires one only together with a mark or a live class edge |
| `Tableau::pivot` (`lib.rs:545`) | n/a | basis change; the row space, hence the constraint set, is unchanged |
| `integer_check` B&B split atoms (`lib.rs:1039`+) | n/a | emits `TCheck::Split`, writes no bound. Routed back through `crates/shinri-sat/src/solver.rs:734` → `Combiner::bind_fresh` (`crates/shinri-theory/src/combiner.rs:374`, `Owner::Arith`/`Shared` arms at `combiner.rs:411`/`423`) → `Arith::new_var`, which marks. `branch.rs` itself holds only the pure helpers `floor_ceil`/`round_int_bound` — it emits nothing |
| `try_gmi_cut` / `cuts::derive_gmi` (`lib.rs:1124`, `cuts.rs:38`) | n/a | derived from existing rows and bounds; emits a `TCheck::Split` atom on the same `bind_fresh` → `new_var` route, and writes no bound directly |

The sites split into **primitive** ones (they assert something arith was told)
and **derived** ones (`run_fbbt`, GMI cuts — they restate what the primitive
ones already imply). L1 and L2 handle one class each; L3 assembles them into the
class-level invariant and C2 covers same-component pairs.

**L1 (primitive slack-bound closure).** *If a slack carries a **primitive**
bound that survives the call that installed it, then either (a) every problem
var in its **defining comb** is really marked, or (b) the bound is an
interface-equality pin, its defining comb is `av - bv`, and `av` and `bv` lie in
the same live interface component.* Only three primitive sites bound a slack:

- `assert` on an atom slack — case (a), because `new_var` (`lib.rs:1303`) marks
  exactly the comb that `atom_var_and_rhs` (`lib.rs:330`) interned that slack
  from;
- `assert_interface_equality` — case (b): a bound that is installed and not yet
  undone *is* a live interface edge, so its two endpoints are in one component
  by the definition of `K`;
- `probe`, which does not survive.

`VarStore::slack_var` interns by comb (`vars.rs:55`), so a probe slack that a
later atom or interface equality reuses is the *same* `ArithVar`, and it lands
in (a) or (b) at the moment it acquires a bound. Two scope notes a maintainer
will otherwise trip on:

- *Primitive* excludes `run_fbbt`, which does bound bound-free slacks (see its
  table row). It is a derived site and is discharged by L2, not by L1.
- *Defining comb*, not *row*. `Tableau::define_slack` substitutes any basic comb
  var by its own row (`tableau.rs:132`–`152`), and `pivot` rewrites rows freely,
  so once `u` is basic it can appear **textually** in the row of a bounded slack
  whose defining comb never mentioned it. That is a change of basis, not a new
  constraint (`Tableau::pivot` row in the table); L1 is about combs.

**L2 (derivation vacuity).** FBBT and GMI cuts emit only consequences of the
constraints already present, so they cannot constrain a var the primitive sites
left free. `tighten_to_fixpoint` (`propagate.rs:21`) is monotone interval
propagation seeded from the live bounds; it relaxes its inputs (δ dropped) and
rounds only for Int vars, so everything it emits is implied. `run_fbbt` runs
only from `seed_apriori_if_needed` (`lib.rs:1259`), gated on
`bounds.marks_len() == 0` (`lib.rs:1239`) — level 0, so its premises are
permanent and its output stays valid under every backtrack. (This is the same
soundness property `sanitize_conflict` already relies on when it drops
`apriori_lits` as level-0-entailed; a defect here would be a pre-existing
wrong-UNSAT bug, not one this slice introduces.) Because a derived bound is
implied, it is preserved by any shift that preserves the primitive constraints —
so L2 lets the argument below ignore derivation entirely.

**L3 (free-class shift).** *Let `u` be a problem var with
`real(class(u)) = false`. For any assignment satisfying arith's live constraints
and any **integer** `δ` that keeps every boxed member of `K(u)` inside its box,
adding `δ` to every member of `K(u)` — and re-deriving each slack from its row —
yields another satisfying assignment.*

By L4 below no member of a free component is boxed at all, so `δ` ranges over
all of ℤ; the box proviso is kept because it makes the lemma independent of L4's
call-order premise, and because §3.B needs no more than a single `δ = ±1` step,
which a box can never take away (`M ≥ 2`, see part 2).

1. *All of `K(u)` shares one value.* Each live interface edge pins its slack to
   the fixed δ-rational `(0, 0)` (`lib.rs:962`/`965`) and that slack's defining
   comb is exactly `av - bv`, so `av` and `bv` agree in **both** the rational and
   the δ component. Transitively every member of `K(u)` holds the identical
   value. The shift is therefore well defined and one choice of `δ` serves the
   whole component.
   *(One state does not satisfy that description: `apply_bound` can conflict on
   the `Lower` pin and return before installing `Upper` (`lib.rs:962`–`967`),
   leaving `s ≥ 0` rather than `s = 0`. It is vacuous here — the bound set is
   infeasible, so "for any satisfying assignment" quantifies over nothing, and
   the `Combiner` turns that conflict into `FinalCheck::Conflict`
   (`combiner.rs:779`–`783`) without reaching either guard.)*
2. *Bounds on problem vars.* For `x ∈ K(u)`, `x` is not really marked by (†), so
   by the table the only primitive bound it can carry is the a-priori box — and
   only if it is Int and already existed when the box was seeded; a Real var, or
   one minted later (`lib.rs:1232` runs once), carries none. The box is uniform
   and `M ≥ 2` (see its table row), so *some* `δ ≠ 0` always exists even for a
   boxed component: with common rational part `r`, `|r| ≥ 1` admits the unit step
   toward zero (`|r| - 1 < M`) and `|r| < 1` admits either unit step
   (`|r ± 1| < 2 ≤ M`); both land **strictly** inside `(-M, M)`, so the bound
   holds whatever the δ-rational component is. Vars outside `K(u)` do not move.
   *Mixed Int/Real components are harmless.* By (1) every member holds the same
   value and the shift moves them all by the same integer, so every member's
   integrality is whatever it was before, every Int member stays inside its box
   by the paragraph above, and a Real member has no box at all. Whether the
   shared engine can actually put an `Int`-sorted and a `Real`-sorted term in one
   class is left open here — the shift does not need it to be impossible.
3. *Bounds on slacks.* Take any slack `s` with a surviving primitive bound. By
   L1 either (a) every var of its defining comb is really marked, so by (†) none
   is in `K(u)` and `s` does not move; or (b) `s` is an interface pin `av - bv`
   with both endpoints in one component — if that component is `K(u)` both move
   by `δ` and the difference is unchanged, and if it is another component
   neither moves. **Every primitively-bounded slack keeps its exact value**,
   whatever `δ` is, so every primitive slack bound still holds. Cross-component
   slacks *do* move, and they are exactly the ones L1 leaves bound-free: the
   probe slacks of `entailed_equalities` (`lib.rs:745`), which persist across
   calls but never carry a surviving primitive bound.
   This is also why shifting **several** free components at once, each by its own
   `δ_i`, is no harder than shifting one: case (a) is immobile under all of them
   and case (b) is intra-component, so neither case can see two different `δ`s.
   L5 uses that.
4. *Rows, derived bounds, integrality.* Rows hold by construction (slack values
   are re-derived from them). Every derived bound is a consequence of the
   primitive constraints (L2), which (2)–(3) preserve, so the derived bounds
   hold too. Integrality survives because `δ` is an integer. ∎

**L4 (no free var carries an a-priori box).** *Every var the box is seeded on is
really marked, so no member of a free component is boxed.* The box is seeded
exactly once, on the **first** `Arith::propagate` call:
`Solver::solve_under` backtracks to level 0 and calls `propagate()` at the head
of its loop (`shinri-sat/src/solver.rs:515`, `528`); `Solver::propagate` always
calls `theory.propagate` after BCP (`solver.rs:1155`); `Combiner::propagate`
runs `drive_propagation`, which calls `arith.propagate` unconditionally
(`combiner.rs:865`); and `Arith::propagate` calls `seed_apriori_if_needed`
(`lib.rs:1375`). At that first call `marks_len() == 0` — `bounds.mark()` happens
only in `Arith::push`, driven by `trail.new_level()` at a decision
(`solver.rs:617`, `625`) — so the seeding really does fire, and
`apriori_seeded` (`lib.rs:1233`–`1235`) makes every later call a no-op.

At that moment the only site that has interned a problem var is `new_var`. The
only site that interns a *free* one is `ensure_shared_var`, whose sole non-test
callers are `combiner.rs:582` and `Arith::assert_interface_equality`
(`lib.rs:929`–`930`), both inside `drive_final_check`, which is reachable only
from `theory.check(Effort::Full)` (`solver.rs:629`) — strictly after the first
`propagate`. So every shared var is minted after seeding.

It does **not** follow that every var present at seeding is really marked, and
the lemma must not claim it. `linearize` interns a problem var for every leaf it
walks (`normalize.rs:169`, `190`) while `canonicalize` drops zero-coefficient
entries (`normalize.rs:217`), so an atom like `(<= (+ x y) (+ x 3))` interns `x`
before seeding and `new_var`'s marking loop, which walks the *canonicalized* comb
(`lib.rs:1302`–`1304`), never marks it.

The step that carries the lemma is `is_int`, not the mark: the box loop only
touches non-slack vars with `is_int` set (`lib.rs:1248`), and before seeding the
only site that stamps `is_int` is `new_var`'s `mark_int` loop (`lib.rs:1291`–
`1297`) — which walks **the same canonicalized comb** as the marking loop. So
pre-seeding `is_int(v)` implies `v` occurs in a registered atom's comb, which
implies `v` is really marked. Every boxed var is therefore really marked, and no
member of a free component is boxed. ∎

*(A maintainer who widened Int-stamping — say by stamping every leaf `linearize`
walks — would break this lemma even though the marking sites were untouched. The
`is_int` step is the load-bearing one.)*

*(This is a premise about call order, not about arith alone. If a future change
interned a shared var before the first `propagate`, L4 fails and L5's free choice
of target narrows to the box; L3 and §3.B are unaffected.)*

**C2 (a same-component pair is already known to the shared engine).** *If
`v ∈ K(u)` then arith does entail `u = v` — and skipping the pair still drops no
deduction.* Every live interface bound was installed by
`Arith::consume_interface_equality` (`lib.rs:1438`), whose only non-test caller
is the Combiner's EUF→arith step (`combiner.rs:780`); that step asserts
`rep = m` only for shared terms the congruence engine `cx.eq` holds in **one
class** (`combiner.rs:745`–`757`). So each edge of the chain from `u` to `v` was
`cx.eq`-equal when it was installed, at some level `ℓ' ≤ ℓ`, where `ℓ` is the
level the arith bound went in at. `Combiner::pop` rewinds `cx.eq` and every
theory to the same absolute target (`combiner.rs:500`–`505`) and `Arith::pop`
undoes bounds by that target (`lib.rs:1461`), so a *live* arith bound means the
current level is `≥ ℓ ≥ ℓ'` and the merge is live too. Hence
`cx.eq.are_equal(u, v)` holds, and both guard sites would discard the pair
anyway:

- the arith→EUF exchange `continue`s on exactly that test (`combiner.rs:718`)
  **before** setting `progressed`, so reporting the pair changes nothing, not
  even the round count;
- MBTC filters its candidate pairs by the same test (`combiner.rs:814`–`818`)
  before building a split.

The merge target is the single shared engine `cx.eq` that every theory reads, so
this is not an EUF-only argument: no third theory loses the equality either. ∎

**C2b (the converse).** *A `cx.eq`-merged pair of shared terms lies in ONE live
component.* The EUF→arith step asserts `rep = m` for every non-representative
member of every `cx.eq` class of shared terms (`combiner.rs:735`–`787`), and
MBTC is reached only after a whole round added nothing (`progressed == false`,
`combiner.rs:797`), so by then every merged shared pair has been asserted at some
point during this check — `iface_asserted` (`combiner.rs:763`) suppresses only
*re*-assertion, and no `pop` runs inside `drive_final_check`, so every one of
those bounds is still live. Chaining through the representative puts the whole
class in one component. Together with C2: **merged ⟺ same live component**, for
shared terms at the MBTC decision point. ∎

**L5 (joint arrangement, over MBTC's candidate set).** *When `drive_final_check`
returns `Sat` (`combiner.rs:844`) there is a single arith model realizing the
`cx.eq` arrangement over the shared vars **MBTC is responsible for** — the
non-slack problem vars carrying the `is_int` stamp, which is exactly the set
`model_equal_shared_pairs` draws its candidates from (`lib.rs:813`).*

**Why that scope, and not "the shared terms".** `Euf::shared_arith_terms` admits
Real-sorted terms as well as Int (`shinri-euf/src/solver.rs:235`–`247`), and
`model_equal_shared_pairs` filters them out (`lib.rs:813`). A pair outside the
`is_int` set is therefore never an MBTC candidate — **before or after this
slice** — so the guard cannot have changed anything about it, and claiming a
joint arrangement over it would be claiming something this slice neither owes
nor establishes. Two consequences worth stating plainly:

- *The Real fragment.* Its agreement rests on the pre-existing design decision
  that MBTC is Int-only ("convex exchange handles those; splitting them would
  regress QF_UFLRA" — `model_equal_shared_pairs`' own doc comment). That
  justification takes complete entailed-equality propagation as its input, and
  **this slice preserves that input exactly**: for every skipped pair, either the
  equality is not entailed (Conclusion case 1) or it is entailed and `cx.eq`
  already holds it, so the Combiner discards the report at `combiner.rs:718`
  (C2). The set of equalities reaching `euf.consume_interface_equality` is
  therefore byte-for-byte what it was pre-slice, and the Real fragment's standing
  is unchanged. I deliberately do **not** discharge it here with the usual LRA
  convexity argument (if no individual equality is entailed then their
  disjunction is not, so one model falsifies all of them at once): that argument
  is about a *pure*-LRA system, `Arith` is mixed Int/Real, and invoking it in a
  mixed setting would overclaim.
- *The stamp, not the sort.* The scope is the `is_int`-**stamped** vars, not the
  Int-**sorted** terms. `problem_var_sorted` returns an already-interned var
  without stamping (`vars.rs:46`–`49`), so an Int-sorted term first interned by a
  cancelling atom can reach MBTC unstamped and be filtered out. That gap is
  pre-existing and out of scope for slice 42; stating L5 over the stamped set
  keeps the lemma true regardless of it, and it is the honest scope anyway —
  MBTC's remit *is* its candidate set.

L3 is not enough on its own, and it is worth being explicit about why. L3 moves
**one** component **one** step, which is exactly what one skipped pair needs —
that is all §3.B asks for. The `Sat` exit asserts something stronger: that every
non-merged candidate pair is *simultaneously* distinct in one model. `k`
independent `±1` steps do not compose into that — two free components both
sitting at β = 0 and both shifted by `+1` are still equal to each other, and a
shift can even collide a free component with a constrained var it was distinct
from. The construction below is what bridges the gap.

Let β be the model arith is sitting on. Call a live component **in scope** if it
contains a stamped shared var; group the shared problem vars by live component.

1. *What has to hold.* By C2/C2b, merged ⟺ same live component, and by L3 part 1
   every member of a component holds one common value. So realizing the
   arrangement means exactly: **distinct in-scope components get distinct
   values.**
2. *Constrained components already agree.* Two constrained stamped shared vars
   that were β-equal and unmerged would be returned by
   `model_equal_shared_pairs` (neither side is skipped) and picked as `undecided`
   (`combiner.rs:814`–`818`), so the `Sat` exit would not have been taken. They
   are pairwise distinct at β already; leave them there.
3. *Free components move freely and independently.* By (†) no member of a free
   component is really marked and by L4 none is boxed, so no member carries any
   bound at all; by L3 parts 3–4 a rigid integer shift preserves every
   primitively-bounded slack exactly, every row, every derived bound, and
   integrality — and per-component shifts compose (L3 part 3). A pin can never
   join a free component to a constrained one: that would make them one
   component and hence one class.
4. *Assign.* Let `D = 1 + ⌈max |c(β(w))|⌉` over **all** shared problem vars `w`,
   where `c(·)` is the rational part of the δ-rational. The ceiling is load
   bearing: an out-of-scope Real shared var may sit at a fraction, and a
   non-integral `D` would make the shift non-integral and break L3 part 4. Taking
   the max over *all* shared vars — not just the in-scope ones — is what keeps a
   move from colliding with an out-of-scope var.
   Enumerate the in-scope free components as `K_1, …, K_k`. Each holds a common
   value `(c_i, 0)` with `c_i ∈ ℤ`, because it contains a stamped var and `check`
   returns `Sat` only after `integer_check` finds every stamped non-slack var
   integral with a zero δ-part (`lib.rs:1043`–`1047`). Move `K_i` rigidly by
   `δ_i = D + i - c_i`, an integer. Out-of-scope components are left where they
   are.
   Every target `(D + i, 0)` is distinct from every other target and exceeds
   every unmoved shared var's value in the rational part (`|c| ≤ D - 1`),
   whatever δ-part that var carries. So each moved component is distinct from
   everything else, in scope or out, while no relation among the unmoved vars
   changes. That is the arrangement of (1). ∎

The construction moves a component whole, Real members included; that is sound
for the same reason (an unmarked Real var carries no bound either), and it
disturbs no out-of-scope pair either, since step 4's `D` is taken over every
shared var and the targets clear all of them.

**Conclusion.** Let `(u, v)` be a pair a guard skips, so (WLOG)
`real(class(u)) = false`. Vars are deduped to distinct problem vars before
pairing (`lib.rs:697`–`704`), so `u ≠ v`.

1. **`v ∉ K(u)`.** L3 shifts `K(u)` and leaves `v` where it is, so the shifted
   assignment satisfies arith with `u ≠ v`. Note this covers `v` in a *different*
   class and `v ∈ class(u) \ K(u)` — a pair whose join has since been popped —
   alike.
2. **`v ∈ K(u)`.** `u = v` is entailed, and by C2 the shared engine already has
   the two terms merged.

Its two consequences, stated at the strength the argument actually proves:

- **§3.B.** In case 1, `u = v` is not entailed, so skipping the probe drops no
  deduction. In case 2 it is entailed, but the Combiner discards the report at
  `combiner.rs:718` before it can make progress — so skipping still drops
  nothing. This is the one place the class rule could have cost a real
  deduction, and C2 is why it does not.
- **§3.C.** Two things are owed here, and the pair-local one alone is *not*
  enough.
  *Pair-locally:* `model_equal_shared_pairs` returns only β-equal pairs
  (`lib.rs:809`), so at the split point `u = v` already holds in the current
  satisfying assignment; in case 1 the L3 shift gives a satisfying assignment
  with `u ≠ v`, so both cells are arith-satisfiable and arith has nothing to
  contribute to deciding that pair, and in case 2 the pair is already merged and
  MBTC drops it at `combiner.rs:814` regardless.
  *Jointly:* skipping pairs is only sound if the `Sat` the Combiner eventually
  returns is backed by a model realizing the **whole** arrangement, over all `k`
  skipped pairs at once. Pair-local satisfiability does not give that — `k`
  independent `±1` steps do not compose — and L5 is what supplies it, over
  exactly the candidate set MBTC draws from. Pairs outside that set (Real-sorted,
  or Int-sorted but unstamped) are not MBTC's business before or after this
  slice; what the guard could have disturbed for them is §3.B, and the bullet
  above shows it does not.
  What is still NOT claimed: "every arrangement of `u` is arith-satisfiable" is
  false in general, since a boxed `u` cannot be made equal to a var minted after
  seeding whose value exceeds `M`. L4 is what keeps that from biting here — a
  *free* var is never boxed, so L5's targets are unconstrained.

## 5. Testing

### Unit — `shinri-arith`

- `entailed_equalities` over two unconstrained shared vars returns empty **and
  mints no slack**. Assert on the tableau/`Vars` state, not only on the return
  value: slack persistence is what defeated the tableau-based predicate, so it
  needs a direct fence.
- Each **marking** path individually restores probing — a var constrained only by
  a numeral pin, only by a registered atom, and only by an assertion each still
  yields the entailed equality it yielded before.
- A consumed interface equality does **not**: after task 4b it joins a class
  instead of marking, so free⋈free stays unprobed while free⋈really-constrained
  becomes probed. Pin both directions, and pin the OR-on-union ordering both
  ways round (mark then join, join then mark) — that is the easiest part of the
  union-find to get wrong.
- An entailed pair between two constrained vars is still reported: the
  anti-regression anchor for the rule itself.
- `model_equal_shared_pairs` omits pairs with an unconstrained var and still
  returns model-equal pairs of constrained vars (§3.C).
- Monotonicity: a var constrained at level *n* is still probed after `pop` below
  *n*.

### End-to-end — `shinri-solver`

The existing DT⋈arith set is the regression anchor and must stay green with
verdicts unchanged: `mixed_datatype_and_arith_unsat`,
`arith_{lt,le,gt,ge}_over_selector_*`, `arith_wrapped_selector_unsat`
(`qfdt_e2e.rs:146–231`).

### Performance gate

Check the `deep` family in as a test: assert a **decided** verdict at n = 24
under a generous wall-clock bound (5 s against a pre-fix 24.1 s). Wall-clock
assertions are normally a flakiness smell; a ≈1600× fault carries enough margin
to justify one, and without it a silent regression quietly consumes the
10–15 min blocking-tier budget.

### Oracle

The **full unfiltered** run: `cargo nextest run -p shinri-solver --features
oracle`, no `-E` filter, and **confirm a non-zero discovered test count** (a
flagless run compiles to zero tests and proves nothing). Non-negotiable here —
this change sits in the shared arith/N-O path, and a filtered run on slice 40
skipped `qfs_differential` and nearly shipped a Sat→Unknown regression. QF_UFLIA
coverage matters as much as QF_DT; the exchange is shared.

### `script_e2e`

Run locally pre-push. The change removes no deduction, so the expected outcome
is **no flips at all**. Adjudicate any that appear by direction:

| Flip | Reading |
|---|---|
| `unknown` → `sat`/`unsat` | **Permitted** (§4.A): a budget-limited query now finishes. Confirm against z3/cvc5 before updating the pin. |
| `sat` ↔ `unsat` | Regression. Stop. |
| decided → `unknown` | Regression. Stop. |

The permitted direction is expected on the **string** path, not QF_DT, since
that is where the cumulative pivot/branch budgets actually bind.

### Standing gates

`cargo fmt --all` before pushing (CI `fmt --check` fails fast); `mise run lint`
clean (clippy `-D warnings`).

## 6. Scope — explicitly out of slice 42

| Deferred | Owner |
|---|---|
| Correcting `Euf::shared_arith_terms`' sort-only filter so `S` is not over-approximated (§2) | 43 |
| Finiteness predicate + demand-driven splitting + leaving infinite-sort terms free (the original slice-42 roadmap entry) | 43 |
| Nelson–Oppen exchange for `Int`/`Real` datatype fields, completing QF_UFDTLIA | 43 |
| `?` placeholders for non-datatype fields in rendered models (`DtSolver::render_value_inner`) | 43 |

The roadmap entry this slice displaces — finiteness/cardinality — was
re-examined and reduced before deferral. Its cardinality half is **not** needed
for completeness: because every finite-sorted term is split exhaustively, every
finite-sort class becomes constructor-determined and the arrangement over those
classes is settled by congruence plus constructor clash. `(distinct a b c d)`
over a three-constructor enum already returns `unsat` with no counting rule.
Slice 43 should build the finiteness **predicate** only; an explicit pigeonhole
rule stays speculative until a query demands it.

## 7. Success criteria

- The n = 24 `deep` query decides `sat` in well under a second, against a
  measured 24.1 s baseline; the n = 20 Int-field query matches the
  uninterpreted-field query's order of magnitude (6 ms), closing the
  sort-attributable gap.
- **No regressive verdict changes**: `qfdt_e2e`, `script_e2e`, and the full
  unfiltered oracle run agree with pre-slice results, except that an
  `unknown` → decided flip on the string path is permitted once
  z3/cvc5-confirmed (§4.A). Any `sat` ↔ `unsat` or decided → `unknown` flip is a
  regression.
- The §3.A entry-point audit is recorded, establishing that no path can
  constrain a problem var without marking it.
- Unit tests pin both the skip (no slack minted) and each marking path's
  restoration of probing.
