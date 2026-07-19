# Slice 31 design — two-variable lexicographic order in the word-equation engine

Date: 2026-07-19
Status: DESIGN

**Delivered across two slices** (decomposed at planning, 2026-07-19, once the
encoding size became concrete — see §2a):
- **Slice 31 (the spine):** ownership routing + assert path + the
  code-handle bridge primitive (with congruence) + the head-peel spine that
  cashes the bare pin (Sat) and the shallow Unsat idioms, fuel-bounded; the
  symbolic-pair oracle family. This is what the plan
  `docs/superpowers/plans/2026-07-19-shinri-slice31-str-order-symbolic-pair.md`
  implements.
- **Slice 32 (the deepening):** deep recursion / length-coupling to full
  order-reduction completeness, fuel tuning, and the exhaustive oracle sweep.

Predecessor: slice 30 (constant-word lexicographic order, landed 2026-07-18).
Slice 30 took the last *pure-rewrite* step adjacent to the string-order
fence — generalizing the constant side to any-length words — and, per its
§6, banked the two-free-variable case as engine work. That banked item,
`targeted_str_order_symbolic_pair_known_gap`
(`crates/shinri-solver/tests/qfs_differential.rs:4035`): `(str.< s u)` over
two free variables returns a sound `Unknown`; z3 answers `Sat`. It is now
**the oldest live known gap**. This slice cashes it.

The fix is not a new engine — `crates/shinri-str/src/wordeq.rs` is already a
real online, backtracking Nielsen/Levi word-equation resolver running inside
the DPLL(T) `Combiner` as the string theory. What is missing is that
**lexicographic order is handled only by the preprocessing rewriter**
(`order.rs`), which fences to `Unknown` the moment both sides are free
variables — the order atom never reaches the online engine. The doc at
`order.rs:479` names the missing piece: "the existential first-differing-
position split, banked." This slice supplies that split and routes order
into the engine.

## 1. Problem — order over two symbolic sides is fenced at preprocessing

`order.rs` (slices 23/24/30) rewrites `str.<`/`str.<=` to regex membership
when **one** side is a constant, and folds the empty/reflexive/literal
idioms. When **both** sides are free variables none of the `try_order_atom`
arms fire, the atom survives unchanged
(`symbolic_pair_survives_to_fence`, `order.rs:308`), and
`has_unreduced_str_order` (`order.rs:229`) reports it, so the solver returns
`SolveOutcome::Unknown` (`crates/shinri-solver/src/lib.rs:483`).

The reason it is fenced is **not** undecidability of the rewrite fragment —
it is that comparing two *symbolic* characters' order fundamentally needs
arithmetic on their code points. A regex `Range` can express "char <
constant" but cannot relate two unknowns; and `str.to_code` is a
preprocessing-only pre-pass with a presence fence
(`crates/shinri-str/src/code_conv.rs`, "Slice 18 pre-pass … exact rewriting
+ fence") — a `to_code` term minted mid-solve would be uninterpreted. So the
two-variable case requires a new online capability, which is why every
string slice since 19 held it as a standing non-goal.

## 2. Scope — order-reduction completeness, not literal totality

Deciding *every* two-variable `str.<` conjoined with arbitrary
length/word-equation constraints is not a finite target: word equations
**with length** is a well-known open problem, and this engine is
deliberately sound-but-incomplete (fuel-bounded to a sound `Unknown`). The
achievable, honest goal is **order-reduction completeness**: reduce
`str.<`/`str.<=` faithfully into the engine so that *order itself introduces
no incompleteness* — any residual `Unknown` comes only from the engine's
fundamental fuel bound, shared with all word-equation reasoning, not from a
special order fence. This strictly *shrinks* the incomplete region and lifts
the two-variable order fence.

**Where slice 31 lands within that goal.** Slice 31 builds the *spine* of the
reduction — the ownership/assert wiring, the congruent code-handle bridge,
and the head-peel clause family — and validates it end-to-end on the bare
pin (Sat via the empty-prefix base case) and the shallow Unsat idioms
(`s<u ∧ u<s`, `s<u ∧ s=u`, `s<u ∧ u<=s`). Deep recursion and tight
length-coupling — pushing to full order-reduction completeness — are
slice 32. Everything slice 31 does is *sound at every depth*; slice 32 only
*decides more* (fewer fuel-bounded `Unknown`s), never changes an answer.

## 2a. Two encoding realities that shaped the split (surfaced at planning)

1. **`TCheck::Split` atoms must be flat theory atoms.** `classify`
   (`crates/shinri-theory/src/atom.rs:16–103`) routes a compound
   `(and …)`/`(or …)` atom to `Err(Unsupported)`. So the nested head-peel
   formula below cannot be one atom — it is hand-Tseitin'd into a **family of
   flat guarded CNF clauses emitted incrementally across solver rounds**,
   the exact pattern the membership pass already uses (`memb.rs`, the keyed
   S1..S4 witnesses). This is the intricate, soundness-critical core, and the
   reason the completeness push is its own slice.
2. **The code handle needs congruence *and* on-demand constant folding *and*
   range — all three for soundness, not completeness.** Two concrete
   spurious-SAT scenarios (found while deriving the clause family) pin this
   down: `s<u ∧ u<s ∧ |s|=1 ∧ |u|=1` needs **congruence** (each atom mints
   its own head-skolem for `s`, so only `hs=hs' ⇒ code(hs)=code(hs')` yields
   the conflict); `s<u ∧ s="b" ∧ u="a"` needs **on-demand folding** (pin
   `code(head)` to the real value of a constant-forced head, else the solver
   picks a bogus code order). §4 gives the mechanism. This is a *bounded*
   online `str.to_code` capability (constant-fold + congruence + range on
   single-char heads), deliberately short of general online `to_code` (still
   a non-goal). It is more than the abstract-code sketch the first spec draft
   assumed — the correction that most shaped the spine.

## 3. Fix — four wiring changes plus one new capability

All four wiring changes reuse existing infrastructure (the generic
`TCheck::Split` seam, the Combiner lift, the SAT split-on-demand loop, the
`fresh_str` skolem mint, the `emitted` dedup set, and the `Fuel` budget).

1. **Fence lift (narrowed, not removed).** `has_unreduced_str_order`
   (`order.rs:229`) stops firing *only* for the two-symbolic-side case (a
   surviving `StrLt`/`StrLeq` where **neither** operand is a string
   constant). It **still fences** a surviving order atom with a constant
   operand — those are the over-cap / above-alphabet constant words
   `try_order_atom` rejected (`word_codes → None`), which stay `Unknown` by
   design (§9 non-goal). `order.rs`'s constant-side rewrites (slices 23/24/30)
   are untouched and still fire first in `try_order_atom`; only the surviving
   *symbolic-pair* atom now flows through to the theory layer instead of
   `→ Unknown` at `lib.rs:483`.
2. **Ownership routing.** Extend `classify`
   (`crates/shinri-theory/src/atom.rs:16–103`) to return `Owner::String`
   for a surviving `StrLt`/`StrLeq` atom — a `str.in_re`-style early return
   alongside the existing string-routing blocks (today such an atom falls to
   `_ => Err(Unsupported)` at `atom.rs:98`). The `Owner::String` enum variant
   and its dual EUF+String dispatch (`combiner.rs:173–181` / `256–260` /
   `354–357`) already exist, so no Combiner or `Owner`-enum change is needed.
   Today no owner ever sees the atom because it never survives preprocessing.
3. **Assert path.** `StrSolver.assert` (`crates/shinri-str/src/lib.rs:100`)
   records order literals into a new `order_true: Vec<(atom, lit,
   polarity)>` list with decision levels — parallel to the existing
   `eq_true` / `diseq_true` / `memb_true` handling (`lib.rs:114–145`).
4. **`check` handler.** A new order-lemma generator processes `order_true`,
   emitting the guarded head-peel split (§5), recursing via fresh `StrLt` /
   `StrLeq` atoms, `self.fuel.spend()` per unfold.

The one genuinely new capability is the **symbolic-character ↔ code-point
bridge** (§4), which makes the char comparison expressible online.

**Guardrails.** Binary `str.<`/`str.<=` only (matches the existing arms).
Constant-side and empty/reflexive idioms stay in the preprocessing rewriter;
this slice adds *only* the symbolic–symbolic path. No change to the regex
core, arrays/BV/FP, or the `str.at`/`substr` fence (`lib.rs:507–512`).

## 4. The symbolic-character ↔ code-point bridge

The head-peel (§5) must assert `code(hs) < code(hu)` where `hs`, `hu` are
symbolic single characters. `code(·)` is a **congruent, range-bounded integer
handle** on a single-char string, realized as a **dedicated uninterpreted
`String→Int` function** (declared once, e.g. `!strcode`). It must be
uninterpreted, *not* `str.to_code`: EUF congruence-closes only
`Op::Uninterpreted` applications (`crates/shinri-euf/src/solver.rs:41,294`,
`register_arith_uf_terms`), so a `str.to_code` (Builtin) handle would get no
congruence. When `code(h)` appears in the emitted arith comparison, the
`Owner::Arith` bind path calls `euf.register_arith_uf_terms` (`combiner.rs`)
which interns the `code(h)` application into EUF for congruence. It needs
**three** sound-making properties, established at planning by the
failing-scenario analysis:

- **(a) Congruence** — `hs = hu ⇒ code(hs) = code(hu)`. Load-bearing for
  soundness, *not merely completeness*: because each order atom mints its
  *own* fresh head-skolems, `s<u ∧ u<s ∧ |s|=1 ∧ |u|=1` mints two distinct
  heads for `s`; only congruence (via the word equation `hs = hs'`) forces
  their codes equal and yields the arith conflict. Without it the abstract
  codes satisfy both comparisons → spurious SAT.
- **(b) Range** — `0 ≤ code(h) ≤ MAX_CODE`, `code(h) ∉ [0xD800,0xDFFF]`.
- **(c) On-demand constant folding** — when a head `h` is forced EUF-equal to
  a **single-character constant** `c`, emit `code(h) = eval_to_code(c)`
  (reusing `code_conv::eval_to_code`) as `Ge`/`Le` companions. Also a
  soundness requirement, *not* completeness: `s<u ∧ s="b" ∧ u="a"` would
  otherwise let the solver pick `code("b") < code("a")` → spurious SAT;
  folding pins `98 < 97 → false → UNSAT`. A head can only ever equal a
  *single-char* constant (its `|h|=1` companion refutes any longer literal),
  so folding is well-defined and bounded.

Congruence + range + folding is exactly sufficient: a head's real order is
pinned only by equalling a constant (c) or another head (a); an otherwise-free
head is genuinely unconstrained and any in-range code realizes a real char.

Whenever the head-peel mints a single-char head `h`, it emits (once per `h`,
deduped) these bridge axioms (each guarded by `¬L`, as flat arith/length
atoms — never a bare `Eq`, which routes to EUF not arith; `|h|=1` and the
range are emitted as their `Ge`/`Le` companions per
`length::arith_eq_companions`):

```
|h| = 1                          → (>= len(h) 1), (<= len(h) 1)
0 ≤ code(h) ≤ MAX_CODE           → (>= code(h) 0), (<= code(h) MAX_CODE),  MAX_CODE = 0x2FFFF
code(h) ∉ [0xD800, 0xDFFF]       → (<= code(h) 0xD7FF) ∨ (>= code(h) 0xE000)   [a 2-atom clause]
```

`code(h)` enters the **shared String↔Arith set** — the same channel `str.len`
skolems use: it lands in `len_terms`/a sibling set exposed by
`shared_arith_terms` (`lib.rs:1181–1207`), which the Combiner pulls into arith
via `ensure_shared_var` (`combiner.rs:475–489`). The comparison `code(hs) <
code(hu)` is a `BuiltinOp::Lt` atom, which `classify` routes unconditionally
to `Owner::Arith` (`atom.rs:89–91`) — the LIA solver decides it.

**Soundness.** Each emitted clause is a **valid** implication `L → (…)`
entailed by string theory under the interpretation `code = real code-point
function` (everything asserted about `code(·)` — functionality, range, and
the constant folds — holds of the real code-point function), so adding it
preserves both SAT and UNSAT. On a SAT verdict the arith model gives each
`code(h)` a concrete value in the representable, non-surrogate range;
assigning `h = char(code(h))` (order-consistent with the `<` constraints arith
found satisfiable, and equal to the pinned constant wherever folding fired)
realizes a genuine model — SMT-LIB `str.<` agrees with code-point `<` (UTF-8
is byte-wise code-point-order-preserving, slices 23/30). Surrogate/`MAX_CODE`
edges are excluded exactly as `code_conv`/`order.rs` already do.

## 5. The order head-peel lemma, recursion, and fuel

When `StrLt(s, u)` is asserted **true** (literal `L`), `check` drives the
following **logical** target — guard `¬L` throughout, so every emitted clause
is the valid implication `L → (…)`, the same posture the wordeq F-split uses
(`wordeq.rs:730`, the sole `guard = Some(…)` user):

```
L →  (s = "" ∧ u ≠ "")                                        [base: empty s < nonempty u]
   ∨ ( s = hs·ss ∧ u = hu·su ∧ bridge(hs) ∧ bridge(hu)        [heads exist, |hs|=|hu|=1]
       ∧ ( code(hs) < code(hu)  ∨  (hs = hu ∧ StrLt(ss, su)) ) )  [differ here, or recurse]
```

Per §2a this nested formula is **not** one atom — it is realized as a
**family of flat guarded CNF clauses emitted incrementally across rounds**
(disjuncts are positive theory atoms; a "≠"/negation is expressed as its own
`distinct`/`not` atom), keyed and deduped like the membership pass's S1..S4.
The plan pins the exact clause set and its per-clause validity.

`hs, ss, hu, su` are fresh (`fresh_str`, `wordeq.rs:27`); `bridge(·)` is §4.
The tail `StrLt(ss, su)` is a **fresh order atom** — it flows back through
assert → `order_true` → `check` on the next round, so recursion is driven by
the SAT case-split loop, not by Rust recursion. Emission is deduped through
an `emitted`-style set keyed on `(s, u)` (mirroring `wordeq.rs`),
guaranteeing termination of *emission*.

**`str.<=`** is the sibling: base case `s = ""` alone (empty ≤ anything,
including empty), recurse-tail `StrLeq(ss, su)`.

**Both polarities, no fence.** `L` false means
`¬StrLt(s, u) ≡ StrLeq(u, s)` (and `¬StrLeq(s, u) ≡ StrLt(u, s)`). The
handler maps a negated order literal to the sibling relation with swapped
operands and emits *that* lemma — so negative occurrences are complete too,
no polarity fence (the slice 23/24/30 invariant).

**Fuel.** Each unfold calls `self.fuel.spend()` before emitting (as
`wordeq.rs:735` does); exhaustion → `TCheck::Unknown`, sound. The bare pin
decides at **depth 0** — the `s = ""` base disjunct is immediately Sat — so
it costs one unfold. Deep length-coupled cases consume fuel and fall to
sound `Unknown` (the fundamental residual, §2). **Fuel-budget question for
the plan:** two-variable order recursion is deeper than constant-side work;
measure whether the default 40 (`fuel.rs:21`) needs a bump or an
order-specific sub-budget, tuned against the oracle family — flagged, not
pre-decided.

**Conflict citation.** The bounded Unsat idioms (§7) resolve through the
normal SAT/arith conflict path: the head-peel drives both sides to comparable
heads, the `code` comparisons (plus congruence and folding, §4) and
word-equation tails contradict, and the existing conflict-citation machinery
(`nf_equal_explain`, `lib.rs:1101`; arith conflicts) produces the refutation —
no new order-specific conflict logic. *Unbounded* antisymmetry (`s<u ∧ u<s`
with free lengths) instead exhausts fuel to a sound `Unknown` in the spine
(the all-heads-equal branch has no length floor) — that is the slice-32
deepening target, not a spine regression.

## 6. Soundness (summary)

- **Reduction faithfulness.** The head-peel disjunction is the standard
  two-way characterization of lexicographic order on code-point sequences:
  `s < u` iff `s` is empty and `u` nonempty, or they share equal heads and
  recurse, or the heads differ with `code(hs) < code(hu)`. Each emitted
  clause is a **guarded implication** `L → (…)`, valid at any
  polarity/nesting/occurrence — no eager (unguarded) order clause is ever
  learnt, so no spurious UNSAT (the hazard `wordeq.rs:700` guards against).
- **Bridge soundness.** §4 — `code(·)` congruent + ranged into
  `[0, MAX_CODE]` minus surrogates; each clause valid under `code = real
  code-point function`; code-point `<` agrees with SMT-LIB `str.<`.
- **Termination.** Emission deduped per `(s, u)`; recursion depth
  fuel-bounded to a sound `Unknown`. The engine stays **sound, terminating,
  incomplete**; this slice strictly shrinks the incomplete region without
  touching the soundness envelope.

## 7. Testing

**Unit (`order.rs` + `lib.rs` / wordeq seam).**

- Fence-lift regression: `symbolic_pair_survives_to_fence` (`order.rs:308`)
  flips to a *now-routed* assertion — the atom reaches `StrSolver`, no
  longer `Unknown` at preprocessing.
- Bridge unit: a minted single-char head emits `|h| = 1` (Ge/Le companions)
  and the `code(h)` range/surrogate-exclusion atoms.
- **Congruence unit (T-2 crux):** a small solver-level test that forcing two
  head-skolems equal forces their codes equal — i.e. `code(hs) < code(hu) ∧
  hs = hu` is refuted. This validates the code-handle mechanism choice
  (uninterpreted symbol vs `str.to_code`).
- Head-peel shape: assert the exact guarded flat CNF clauses for `StrLt` and
  `StrLeq`, both polarities (negated maps to the swapped sibling).
- All constant-side slice 23/24/30 tests pass **unchanged** — the
  constant path is untouched (regression guard).

**e2e pins (`qfs_differential.rs`, z3-cross-checked via `expect`).**

- Headline flip: `targeted_str_order_symbolic_pair_known_gap` → **decides
  Sat** (renamed off `_known_gap`, z3-confirmed witness — the empty-prefix
  base case).
- Unsat idioms the **spine** decides at bounded depth:
  - `(str.< s u) ∧ (= s u)` → Unsat (the `A≠B` clause, depth 0).
  - `(str.< s u) ∧ (= s "b") ∧ (= u "a")` → Unsat (on-demand folding:
    `98 < 97` is false).
  - `(str.< s u) ∧ (str.< u s) ∧ (= (str.len s) 1) ∧ (= (str.len u) 1)` →
    Unsat (bounded antisymmetry via congruence on the equal single-char
    heads).
  - `(str.< s u) ∧ (= (str.len u) 0)` → Unsat (nothing is `< ""`).
- Decided Sat with a length coupling:
  `(str.< s u) ∧ (= (str.len s) 1)` → Sat.
- **New residual pin (slice-32 target, sound `Unknown`):** the *unbounded*
  antisymmetry `(str.< s u) ∧ (str.< u s)` stays `Unknown` in the spine — the
  all-heads-equal branch recurses without a length bound and fuel-exhausts.
  Pinned `Unknown` (z3 says Unsat) so the slice-32 deepening trips a test
  when it flips.

**Differential oracle** (house cadence: `--features oracle`, run foreground
with captured output — see AGENTS.md / oracle-gate memory). New family
`qfs_str_order_symbolic_pair_matches_z3`: two-free-var `str.<`/`str.<=`
(both polarities), a fraction conjoined with length/equality constraints to
force decided verdicts on both sides. Expect: **shinri-unknowns down**,
**0 shinri-vs-z3 disagreements**, both `n_sat > 0` and `n_unsat > 0`. The
other string/regex families re-run with tallies **unchanged** — any movement
is a finding to adjudicate. (Slice 31's family exercises the *spine* — the
bare/shallow shapes; the exhaustive deep-recursion sweep that would prove
order-reduction completeness is slice 32.)

Per-iteration verdict monotonicity via the printed-tally comparison
(base vs fix): this repo's `qfs_differential.rs` has **no** `DIFFDUMP`
per-iteration recipe (slice 29/30 precedent), so the soundness invariant is
checked by comparing family tallies — every flip `Unknown → decided`, zero
`decided → Unknown`, zero `sat ↔ unsat`.

**Tier note.** If the new oracle family's fuel-depth sweep exceeds the 5-min
blocking budget, it gets
`#[ignore = "exhaustive: nightly tier (~N min in CI)"]` with a fast smoke
companion covering the same operation on the blocking tier (AGENTS.md
test-tier rules).

**Gate list** (run locally pre-push): `shinri-str`,
`qfs_differential --features oracle`, `script_e2e` — a completeness-shifting
string change can flip string-side e2e pins; any z3-confirmed
`Unknown → decided` flip is an adjudicated flip, not a blocker
(slice 25/26/28/29/30 precedent). Plus
`cargo clippy --workspace --all-targets -- -D warnings` and
`cargo fmt --check`.

## 8. Alternatives considered

- **(B) Preprocessing bounded unfold** (slice 30 §5-B): unfold order to a
  fixed depth `D` at preprocessing, where `to_code` *is* handled by the
  pre-pass; fence the tail beyond `D`. Simpler, no online bridge — but
  **bounded ⇒ incomplete**, directly against the order-reduction-
  completeness goal, and emits eager skolems even when unneeded. Rejected as
  the slice-31 shape; usable only as a smaller fallback.
- **(C) First-diff index via `str.at`/`substr`:** introduce integer `k` =
  first-differing index and axiomatize `s[k] < u[k] ∧ s[0..k] = u[0..k]`.
  But `str.at`/`substr` is currently **fenced** (`lib.rs:507–512`) — this
  drags in a whole separate banked seam and a far larger surface. Rejected.

## 9. Non-goals (banked)

- **n-ary / chained `str.<` / `str.<=`** — binary only, matching the
  existing arms.
- **Deep length-coupled order + word-equation conjunctions** beyond fuel
  depth — the fundamental residual (word equations with length is open);
  sound `Unknown`, not an order-specific gap.
- **`str.at` / `substr` seam** — stays fenced; the bridge deliberately
  avoids it.
- **General online `to_code`** — the bridge pins single-char heads only;
  general `to_code` stays preprocessing-only.
- Slice 27/28/29 standing bank unchanged (approach-C fuel-free
  constant-length propagation, distinct-length sets, co-finite memberships,
  slice-28 §8 conflict-core work, slice-27 typed-antecedent refactor).

## 10. Addendum (2026-07-19) — base-case decision-phase preference

**Surfaced at the Task 7 integration gate.** Tasks 1–6 landed sound and
unit-reviewed: ownership routing, the congruent `!strcode` bridge,
`order_true` recording, the head-peel clause families, polarity mapping, and
on-demand constant folding (including a `side_clean(input_cond_roots)` guard
added to close a conditional-merge spurious-UNSAT hazard). But when Task 7
lifted the fence and ran the acceptance pins end-to-end for the first time,
**4 of 5 intended-decidable pins returned `Unknown`, including both soundness
gates** — no *wrong* verdict, but the slice did not decide the idioms it
claims. This section specifies the missing piece.

### 10.1 Root cause — the recursion is forced, not chosen

`§5`'s claim "the bare pin decides at depth 0 — the `s=""` base disjunct is
immediately Sat" is **false as built**. In `CMP2 = [a_eps, clt, r_tail]`
(where `a_eps = (= A "")`, `clt = (< code(hA) code(hB))`, `r_tail = (str.< tA
tB)`), every fresh atom takes the SAT solver's **default-FALSE** decision
phase (`shinri-sat` `Assignment::new_var` pushes `phase = false`, and the vec
order of `atoms` is *inert* — clause literal order does not bias decisions).
So `a_eps=false ∧ clt=false` **unit-propagates `r_tail=true`**: the recursion
tail is *forced*, never chosen. `order_true` grows unboundedly (instrumented:
1→2 for the bare pin, 2→3 for the antisymmetry gate), the shallow model /
bounded refutation is never reached, and the pass fuel-exhausts to sound
`Unknown`. This is **not** a fuel bug — bumping fuel *diverges* (>60s /
timeout, per-round N-O cost × unbounded rounds) — and **not** a wiring bug
(`code(h)` reaches shared arith; congruence interning is present).

Why the other candidate fixes fail: a **finite depth/length measure alone**
cannot decide the *Sat* cases — when the theory returns `Unknown`, DPLL(T)
returns `Unknown`; it does not backtrack to hunt the base-case model — and
dropping `r_tail` at a depth cap is unsound (spuriously refutes `s="aa",
u="ab"`). **`propagate`** forces only *entailed* literals; `s=""` is a
preference, not a consequence, so forcing it is unsound. The `str.<`/`str.<=`
recursion also lacks the finite measure `memb.rs` (Brzozowski-derivative state
space) and `wordeq.rs` (repeatable head-pair dedup) use to converge — it mints
a fresh clause family per fresh tail pair, so its dedup key never repeats and
fuel is its only bound.

### 10.2 Fix — an optional preferred decision phase on emitted split atoms

Add a **decision-phase preference** channel so a theory can mark specific
atoms of an emitted `Split` as preferred-TRUE (or preferred-FALSE):

1. **`shinri-sat`:** extend the `Split`/`SplitAtoms` payload (and the
   `bind_fresh` / fresh-var path) to carry, per atom, an optional preferred
   phase. When a fresh variable is minted for such an atom, **seed
   `Assignment::phase[v]`** with the preferred value so `pick_branch` decides
   it in that direction first. Absent a preference, behaviour is unchanged
   (default FALSE + phase-saving). This is a small, reusable SAT capability;
   nothing else about the decision heuristic changes.
2. **`shinri-theory` combiner:** thread the per-atom phase preference through
   the `TCheck::Split → TheoryResult::SplitAtoms` lift (`combiner.rs`),
   carrying no other change.
3. **`shinri-str` order engine (first client):** when `build_order_family`
   emits `CMP1`/`CMP2` (and the `DEC/LEN` clauses that gate on `a_eps`), mark
   **`a_eps` and `clt` as preferred-TRUE**. Then:
   - **Bare pin** (`s<u`): `a_eps` tried TRUE → `s=""` model → **Sat at depth
     0**, no recursion.
   - **Antisymmetry with `|s|=|u|=1`** (`s<u ∧ u<s`): `a_eps` tried TRUE then
     refuted by `|s|=1`; `clt` preferred TRUE satisfies `CMP2` **without
     forcing `r_tail`**, landing both atoms on the code-compare disjunct →
     congruence (`hs=hs'` via the word equations) forces
     `code(hs)<code(hu)<code(hs)` → arith **UNSAT**.
   - **Constant pins** (`s<u ∧ s="b" ∧ u="a"`): same `clt` path; folding pins
     `98 < 97` → **UNSAT**.
   - **`len(u)=0`**, `s=u`, and the deep/unbounded shapes decide or stay sound
     `Unknown` exactly as before.

### 10.3 Soundness

A decision-phase preference **only reorders the search** — it changes which
branch the solver explores first, never which assignments are legal, never a
learnt clause, never a verdict. Every model found is still a real model; every
refutation is still a real conflict. So the preference is **unconditionally
sound** and cannot regress any of Tasks 1–6. It strictly changes *when* (and
whether, within fuel) a decidable case is decided — completeness, not
soundness.

### 10.4 Validation and residual caveat

The phase preference is *necessary*; sufficiency rests additionally on the
length coupling (`|s|=1 → |hA|=1 → tA=""`) reaching arith/EUF — machinery
Tasks 4/6 already built. Therefore the **acceptance criterion is the 5-pin
gate itself**, run end-to-end after the hint lands:
`bare_symbolic_lt_is_sat` (Sat), `lt_and_eq_is_unsat` /
`lt_and_lt_swapped_bounded_len_is_unsat` (congruence) /
`lt_with_constant_pins_is_unsat_via_folding` (folding) /
`(str.< s u) ∧ (= (str.len u) 0)` (Unsat), `lt_with_len1_is_sat` (Sat), plus
the `qfs_str_order_symbolic_pair_matches_z3` oracle family with **0
disagreements** and acceptable wall-clock. If a gate is still `Unknown` after
the hint, it is a second-order length-coupling defect (diagnosable via
systematic-debugging), **not** a reason to weaken a gate. The
unbounded-antisymmetry pin (`s<u ∧ u<s`, free lengths) remains the recorded
sound-`Unknown` slice-32 residual.

### 10.5 Scope delta

This inserts, before the fence-lift/acceptance task, the phase-preference
capability (`shinri-sat` + `shinri-theory`) and its order-engine client
wiring. Non-goals unchanged. The general phase-hint is deliberately minimal —
one optional field, seeded once at fresh-var creation — not a full
decision-strategy framework (YAGNI); other theories may adopt it later but
none is required to.

## 11. Status: DEFERRED (2026-07-19) — the online spine cannot decide the pins; four-wall analysis

**Outcome.** Slice 31's infrastructure landed and is reviewed sound (Tasks
1–6 = ownership routing, the congruent `!strcode` bridge, `order_true`
recording, head-peel clause families, polarity mapping, on-demand folding with
the `side_clean` guard; slice-31b Tasks 7.1–7.2 = the SAT phase-hint channel
and the order-engine `a_eps`/`clt` tagging). But the **acceptance bar was
never met**: end-to-end, four of the five order pins return `Unknown` (only
`lt_and_eq_is_unsat` decides, via the EUF `NEQ` singleton — it never enters the
recursion). The two-symbolic-variable order capability is therefore **deferred**
and the gap re-banked. This section records *why*, so a future attempt starts
from the real obstacle, not from §10's (disproven) premise.

**The §10 premise was wrong.** §10 claimed a base-case decision-phase
preference would make the bare pin "decide at depth 0." It does not. Four
*independent* walls block the online spine, found in order by
experiment/spike:

1. **Total-assignment CDCL.** `pick_branch` stops only when every var is
   assigned, so the recursion-tail atom `r_tail = (str.< tA tB)` is always
   assigned (either polarity), `assert` records it as an order atom, and
   `order_check` *unconditionally* emits its child family → an unbounded tower
   cut off only by fuel → `Unknown`. The phase hint (7.1/7.2) provably fires
   (`a_eps` is decided TRUE) but cannot help: the tower forms regardless of
   decision *order*, because it is driven by decision *existence*.
2. **No relevance signal.** The clean fix — expand `r_tail` only when its
   parent `CMP2` clause is not already satisfied by `a_eps`/`clt` — is
   **not implementable**: a theory sees only `TheoryCtx = {terms, eq, atoms}`,
   with no view of the SAT assignment or of sibling literals' truth values.
   Membership avoids the tower not by relevance but by a *finite measure*
   (Brzozowski-derivative dedup) that order lacks (fresh tails, no repeating
   key).
3. **The N–O length seam.** Grounding the recursion needs `|tail|=0 ⇒
   tail=""`, but that fact lives only in arith and never reaches the string
   theory's EUF in time — there is no `len=0 ⇒ empty` rule in `cx.eq`
   (deliberately absent, `length.rs:157/254`). A spike confirmed the emptiness
   is invisible at expansion time. *This wall is fixable* — emitting the
   tautology `(or (= x "") (>= (str.len x) 1))` per skolem lets arith's
   `len(x)=0` propagate `x=""` into EUF, and it worked in the spike.
4. **Code-point arithmetic is intractable (the blocker).** Once the len seam
   is fixed and the tail grounds, the wall moves to the `!strcode` semantics:
   the range + surrogate-hole constraints over the 196,607-wide domain
   `[0, 0x2FFFF]` (×2 heads ×recursion) exhaust arith's string-path simplex
   pivot budget (2000) → `Unknown` (`shinri-arith/src/lib.rs:386`); raising the
   budget makes even a single bare `(str.< s u)` livelock (>3 min). The
   code comparison, as a full-alphabet LIA constraint on an uninterpreted
   handle, is simply too heavy on the string arith path.

**What a real attempt needs (prerequisites, not a slice).** The decisive
missing piece is a **tractable symbolic-character order comparison** — one of:
a bounded/bit-vector encoding of the code point; a dedicated non-string-path
arith budget (or lazy range instantiation) for `!strcode`; or an EUF-level
total order on the `!strcode` handle that avoids materializing the full LIA
range. Plus a **finite measure or relevance discipline** for the recursion
(wall 1/2) — which, per wall 2, likely requires extending the DPLL(T)
`TheoryCtx` seam with an assignment/value view, or giving order a
membership-style finite dedup measure. The len-seam tautology (wall 3) is the
one cheap, reusable win and can be lifted out independently. Until the
code-comparison prerequisite exists, two-symbolic-variable `str.<`/`str.<=`
stays a sound `Unknown` and remains the oldest live known gap.

**Disposition.** Tasks 1–6 + 7.1–7.2 are committed and reviewed sound but
**dormant** — the preprocessing fence was never lifted, so no symbolic-pair
atom reaches the engine; behaviour is unchanged from before the slice
(symbolic pairs → `Unknown` at preprocessing). The phase-hint channel
(`shinri-sat`/`shinri-theory`, 7.1) is a general, independently-useful
capability. The banked non-goals (§9) are unchanged.
