# Slice 31 design — two-variable lexicographic order in the word-equation engine

Date: 2026-07-19
Status: DESIGN

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

## 3. Fix — four wiring changes plus one new capability

All four wiring changes reuse existing infrastructure (the generic
`TCheck::Split` seam, the Combiner lift, the SAT split-on-demand loop, the
`fresh_str` skolem mint, the `emitted` dedup set, and the `Fuel` budget).

1. **Fence lift.** `has_unreduced_str_order` (`order.rs:229`) stops fencing
   the two-symbolic-side case. `order.rs`'s constant-side rewrites (slices
   23/24/30) are untouched and still fire first in `try_order_atom`; only
   the surviving *symbolic-pair* atom now flows through to the theory layer
   instead of `→ Unknown` at `lib.rs:483`.
2. **Ownership routing.** Extend `classify` / `theory_of`
   (`crates/shinri-theory/src/combiner.rs:100`,
   `crates/shinri-theory/src/interface.rs:43`) so a surviving
   `StrLt`/`StrLeq` atom is owned by `StrSolver`. Today no owner claims it
   because it never survives preprocessing.
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
symbolic single characters. Because `str.to_code` is preprocessing-only and
fenced, the bridge **replaces** `to_code` with a pinned integer at mint
time rather than emitting a `to_code` application that would survive to a
fence.

Whenever the head-peel mints a single-char head `h`, it emits (once per `h`,
deduped) a bridge axiom binding a fresh integer `k_h`:

```
|h| = 1                          (h is exactly one character)
0 ≤ k_h ≤ MAX_CODE               (MAX_CODE = 0x2FFFF)
k_h ∉ [0xD800, 0xDFFF]           (surrogate block — unrepresentable, code_conv policy)
k_h  is the code point of  h     (the single-char ↔ code binding)
```

`k_h` enters the **shared String↔Arith set** — the same channel `str.len`
skolems already use (`crates/shinri-str/src/fuel.rs` docs). The order
comparison then becomes an ordinary arith atom `k_hs < k_hu`, decided by the
LIA solver. Character equality `hs = hu` in the recurse-branch is an ordinary
string equation the engine already handles (and is entailed by `k_hs = k_hu`
plus single-char, giving the string-view and arith-view a consistent join).

**Soundness.** Every `k_h` is pinned to a representable, non-surrogate code
point, so any satisfying arith assignment induces a genuine single-char
string whose SMT-LIB `str.<` agrees with code-point `<` (UTF-8 is byte-wise
code-point-order-preserving, as slices 23/30 established). Surrogate and
`MAX_CODE` edges are excluded exactly as `code_conv` / `order.rs` already do,
so no interior-surrogate endpoint arises. No `to_code` term ever survives to
a fence because the bridge pins an integer instead of emitting a `to_code`
application.

**Open detail for the plan (implementation, not architecture).** The exact
call path that injects `k_h` and its bounds into the shared arith set —
whether to reuse the precise machinery that lifts `str.len(skolem)` into
shared arith, or add a small sibling emitter — is nailed during planning.
The reuse target (the `str.len` skolem channel) is fixed.

## 5. The order head-peel lemma, recursion, and fuel

When `StrLt(s, u)` is asserted **true** (literal `L`), `check` emits the
guarded disjunction — guard `¬L`, so the learnt clause is the valid
implication `L → (…)`, the same posture the existing wordeq F-split uses
(`wordeq.rs:730`, the sole `guard = Some(…)` user):

```
L →  (s = "" ∧ u ≠ "")                                        [base: empty s < nonempty u]
   ∨ ( s = hs·ss ∧ u = hu·su ∧ bridge(hs) ∧ bridge(hu)        [heads exist, |hs|=|hu|=1]
       ∧ ( k_hs < k_hu  ∨  (hs = hu ∧ StrLt(ss, su)) ) )       [differ here, or recurse]
```

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

**Conflict citation.** Unsat idioms (`s<u ∧ u<s`, `s<u ∧ s=u`,
`s<u ∧ u<=s`) resolve through the normal SAT/arith conflict path: the
head-peel drives both sides to comparable heads, the `k` comparisons plus
word-equation tails contradict, and the existing conflict-citation machinery
(`nf_equal_explain`, `lib.rs:1101`; arith conflicts) produces the
refutation — no new order-specific conflict logic.

## 6. Soundness (summary)

- **Reduction faithfulness.** The head-peel disjunction is the standard
  two-way characterization of lexicographic order on code-point sequences:
  `s < u` iff `s` is empty and `u` nonempty, or they share equal heads and
  recurse, or the heads differ with `code(hs) < code(hu)`. Each emitted
  clause is a **guarded implication** `L → (…)`, valid at any
  polarity/nesting/occurrence — no eager (unguarded) order clause is ever
  learnt, so no spurious UNSAT (the hazard `wordeq.rs:700` guards against).
- **Bridge soundness.** §4 — `k_h` pinned into `[0, MAX_CODE]` minus
  surrogates; code-point `<` agrees with SMT-LIB `str.<`.
- **Termination.** Emission deduped per `(s, u)`; recursion depth
  fuel-bounded to a sound `Unknown`. The engine stays **sound, terminating,
  incomplete**; this slice strictly shrinks the incomplete region without
  touching the soundness envelope.

## 7. Testing

**Unit (`order.rs` + `lib.rs` / wordeq seam).**

- Fence-lift regression: `symbolic_pair_survives_to_fence` (`order.rs:308`)
  flips to a *now-routed* assertion — the atom reaches `StrSolver`, no
  longer `Unknown` at preprocessing.
- Bridge unit: a minted single-char head pins `|h| = 1` and the `k_h`
  bounds including surrogate exclusion.
- Head-peel shape: assert the exact guarded disjunction for `StrLt` and
  `StrLeq`, both polarities (negated maps to the swapped sibling).
- All constant-side slice 23/24/30 tests pass **unchanged** — the
  constant path is untouched (regression guard).

**e2e pins (`qfs_differential.rs`, z3-cross-checked via `expect`).**

- Headline flip: `targeted_str_order_symbolic_pair_known_gap` → **decides
  Sat** (renamed off `_known_gap`, z3-confirmed witness).
- Unsat idioms: `(str.< s u) ∧ (str.< u s)`; `(str.< s u) ∧ (= s u)`;
  `(str.< s u) ∧ (str.<= u s)` → Unsat.
- Decided Sat with a length coupling:
  `(str.< s u) ∧ (= (str.len s) 1)` → Sat.

**Differential oracle** (house cadence: `--features oracle`, run foreground
with captured output — see AGENTS.md / oracle-gate memory). New family
`qfs_str_order_symbolic_pair_matches_z3`: two-free-var `str.<`/`str.<=`
(both polarities), a fraction conjoined with length/equality constraints to
force decided verdicts on both sides. Expect: **shinri-unknowns down**,
**0 shinri-vs-z3 disagreements**, both `n_sat > 0` and `n_unsat > 0`. The
other string/regex families re-run with tallies **unchanged** — any movement
is a finding to adjudicate.

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
