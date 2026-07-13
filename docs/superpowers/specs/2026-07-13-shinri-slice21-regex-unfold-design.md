# Slice 21 design — derivative unfolding of symbolic `str.in_re` in the string engine

Date: 2026-07-13
Status: Designed (implementation pending; plan to follow).

Predecessor: slice 20 (finite / co-finite symbolic `str.in_re` by pre-pass
enumeration rewrite, landed 2026-07-13). This is the third slice of roadmap
**Spec 2 — Regular expressions**
(`docs/superpowers/specs/2026-06-24-shinri-qfs-core-design.md`, Spec 2 of 4).
Slice 19 decided the ground fragment and built the `Rex` machinery
(smart constructors, nullability, per-code-point Brzozowski `deriv`) as the
designated seed; slice 20 decided the finite / co-finite sub-fragment with
zero engine changes. This slice cashes the banked item both specs named:
**derivative unfolding inside the string engine** — membership of symbolic
strings in infinite / co-infinite constant languages (`x ∈ [a-z]*` and
friends).

User-selected envelope (option A of three): **lazy guarded unfolding at
final check** — membership atoms become first-class string-theory
constraints and make progress via guarded lemmas through the existing
`TCheck::Split` channel. No automata module, no length-set lemmas into the
arith seam (option C, banked), no length-driven eager expansion (option B,
rejected as deciding too little). The `str.to_code` inequality
character-range gadget stays banked (natural slice 22). Scope confirmations:
membership only; any String-sorted term on the string side; both
polarities.

## Goal

Decide, at **any polarity, any position, any occurrence count**,
`str.in_re(t, R)` whenever:

- `t` is **any** String-sorted term (variable, concat, literal — anything),
  and
- `R` is a **constant regex** (slice-19 sense: every `str.to_re` argument
  and every `re.range` endpoint a literal, no RegLan variables),

with no restriction on the shape of `L(R)` — the slice-19 ground fold and
slice-20 finite / co-finite rewrite still run first and take the cheap
exits; what survives them (languages neither finite nor co-finite against
a symbolic string side: `[a-z]*`, `(re.+ (re.range "0" "9"))`,
`re.comp((re.range "a" "z")*)`, `(re.++ re.all (str.to_re "x"))`, …)
now routes into the engine instead of the presence fence.

The procedure is a fuel-bounded semi-decision procedure, per house
posture: every emitted lemma is a valid implication or equivalence, so a
**Sat / Unsat verdict is always sound**; fuel or cap exhaustion — and any
model the repair step cannot realise — yields `Unknown`, never a wrong
verdict. Termination comes from fuel and dedup, not from an appeal to
finiteness of the derivative state space.

Decided idioms this unlocks (all previously `Unknown`):

- `x ∈ (re.range "a" "z")*` — sat, with a get-value witness.
- `x ∈ (re.+ (re.range "a" "z")) ∧ len(x) = 3` — sat with a length-3
  witness.
- `x ∈ (str.to_re "a")* ∧ x = y·"b"` — unsat via unfolding against the
  word equation.
- `x ∈ (str.to_re "a")* ∧ x ∈ (str.to_re "b")* ∧ len(x) ≥ 1` — unsat.
- `¬(x ∈ (re.range "a" "z")*)` — sat via `Rex::Comp`, with a witness.
- `str.in_re s re.allchar` for symbolic `s` — the slice-20 `Unknown` pin
  flips to decided (Σ is ONE class here, not `0x30000` enumerated words).

## Lowering — narrowing the presence fence

The slice-19/20 rewrite pass (`rewrite_ground_in_re`) runs first,
unchanged. After it, the solver seam (`shinri-solver/src/lib.rs`, the
`has_unreduced_regex` check) no longer returns `Unknown` merely because a
`str.in_re` application survives. Instead:

- A surviving `str.in_re(t, R)` atom is **engine-eligible** iff
  `extract_const_regex` succeeds on `R` AND the string side `t` mentions
  no above-alphabet literal (`str_term_mentions_above_alphabet`).
  Engine-eligible atoms flow into the SAT core as ordinary Bool atoms.
- Everything else keeps fencing exactly as today: symbolic regex sides,
  any other RegLan-sorted subterm (RegLan equality etc.), RegLan-sorted
  declarations (`any_fun_sig_mentions`), above-alphabet literals on
  either side.

No new fences. The membership atoms in the lowered assertion set are
SMT-LIB terms throughout — lemmas minted during unfolding build new
`str.in_re` applications via a new `rex_to_term` reverse translation
(`Rex` → RegLan term over the existing `Re*` builtins), so `get-value`,
Tseitin, and the self-check all see ordinary terms and no new internal
atom kind exists.

## Atom intake

`StrSolver::assert` gets a `StrInRe` case alongside the existing
`Eq`/`Distinct` intake: it records `(atom TermId, Lit, polarity, level)`
in a new `memb_true` vector with level tracking mirroring
`eq_levels`/`diseq_levels`, so pop/retraction (slice-11 discipline) works
identically. A per-solver cache maps regex `TermId → Rex` (extraction runs
once per regex term). A **negative** membership literal is tracked as
membership in `comp(Rex)` — `Rex::Comp` is native to nullability and
`deriv`, so one code path serves both polarities; the atom term itself is
never rewritten.

## Engine rules

At `Effort::Full`, after the existing word-equation pass, `check` steps
each active membership `(t, R)`. The string side's normal form under the
equality engine is computed with the existing NF machinery, and rules
fire **only when the NF derivation is antecedent-clean** (the existing
`side_clean` discipline) so the emitted clause needs no equality
antecedent literals beyond the membership guard — the same gating
F-splits use today. A membership whose NF is not clean this round is
simply skipped (sound; it is revisited on later rounds).

Progress is by three rules, tried in order. Every emitted lemma spends
one unit of the existing per-solve `Fuel` (40, `fuel.rs`) and is
deduplicated by a `(string-side TermId, regex TermId)` set analogous to
`emitted_splits`; a dedup hit with no other progress leaves the
membership unresolved, and the round ends in the `Saturated` posture —
the solver must not conclude Sat from it (the self-check backstop
below enforces this).

**Rule G — ground consumption (no lemma).** While the NF head is a
string literal, consume it code point by code point with the existing
`deriv`, under `FUEL_NODE_CAP` (blow-up → this membership fences →
`Unknown`). If the NF grounds out completely, `nullable` of the residual
decides the atom: a violated membership is a `Conflict` whose
explanation is the membership literal (plus nothing else — the NF was
antecedent-clean); a satisfied one is discharged for this round. This
subsumes the slice-19 evaluator and handles literal heads introduced by
equality merges mid-search.

**Rule E — class expansion.** The residual regex `R'` (after Rule G) is
not head-forced and the residual NF head is a variable. Partition Σ
(`0..=0x2FFFF` as `u32` code points) into **next-character classes**:
maximal ranges on which `deriv` is uniform, computed from the boundary
set of all `Range` nodes occurring in `R'` (a superset of the
head-reachable boundaries — a finer partition is still correct). If the
class count exceeds a new `CLASS_SPLIT_CAP` (64), this membership fences
(→ `Unknown`). Otherwise emit, through `TCheck::Split` with guard
`¬M(t, R)`:

    M(t, R) → [residual = ""]?ν  ∨  ⋁_C M(residual, C · d_C)

where `d_C = deriv(rep(C), R')` for a representative code point of class
`C` (uniform by construction), the `ε` disjunct is present iff
`nullable(R')`, `residual` is the concat term for the residual NF, and
each disjunct is a **single atom** — an equality or a freshly minted
membership over `rex_to_term(concat(C, d_C))` — as the split channel
requires. Validity: this is the fundamental expansion
`L(R') = [ε]?ν ∪ ⋃_C C·L(d_C)`, an equivalence, not a heuristic. Fresh
membership terms are registered with `collect::collect` exactly as
F-split length terms are.

**Rule S — head split.** The residual regex is head-forced (`C · R''`
with a single non-nullable range head — the shape Rule E's disjuncts
have) and the residual NF head is a variable `x` with tail `γ`. Emit,
with fresh `h`, `z` minted by `fresh_str`:

    M(t, R) → x = "" ∨ x = h·z            (split clause, guard ¬M)
    (x = h·z) → len(h) = 1                 (witness canonicalization)
    M(t, R) ∧ (x = h·z) → M(h, C)          (head class)
    M(t, R) ∧ (x = h·z) → M(z·γ, R'')      (tail membership)

Soundness of the witness clauses is the F-split argument verbatim:
`h`, `z` occur nowhere else in the formula, so constraining them only
canonicalizes the existential witness of the chosen branch; no model of
the original formula is excluded. The `x = ""` branch feeds back into
Rule G on the shortened NF; the `x = h·z` branch grounds out once search
or the model pins `h` (a `M(h, C)` atom with `len(h) = 1` is decided by
Rule G the moment `h`'s class acquires a literal, and is realised by
model repair otherwise).

No changes to the word-equation stepper (`resolve_equation`), the arith
seam, the SAT `step_budget`, or the `Fuel` allotment value — the new
lemmas ride the existing channels and budgets.

## Model repair and the self-check backstop

`model.rs` currently builds each string class's value from the arith
model's `str.len`. New final step: for a class carrying active
memberships, ground-evaluate every membership against the candidate
value (Rule G machinery). On failure, search for a replacement word **of
the same model length** in the intersection of the active `Rex`
languages: BFS over product derivatives, one class-representative
character per position, skipping the surrogate block `0xD800..=0xDFFF`,
under a new `MEMB_SEARCH_STEP_CAP` (10 000) on visited states. Success
replaces
the value; failure is **not** a verdict — it falls through to the
backstop.

`string_model_satisfies` (the post-solve witness self-check that already
guards the `(B′)` premature-Sat hazard) is extended to evaluate every
lowered `str.in_re` atom with `eval_membership` in addition to the
(dis)equalities it checks today. Any atom the model does not realise —
including memberships repair could not satisfy, and negative literals
the repair step broke — downgrades Sat to `Unknown`. Unsat verdicts come
only from guarded conflicts and valid lemmas. Wrong verdicts are thereby
structurally excluded; budgets and repair failures only ever cost
completeness.

## Soundness corners

- **Surrogates.** Class analysis runs in `u32` code-point space, where
  `deriv` already operates — exact, surrogates included. A class lying
  entirely inside `0xD800..=0xDFFF` can arise (user range endpoints
  adjacent to the block) and its expansion disjunct is **kept**
  (omitting a class would invalidate the equivalence); only witness
  minting skips surrogates, so a branch whose every witness needs a
  surrogate code point ends in the self-check downgrading to `Unknown` —
  sound. This mirrors the slice-20 surrogate-range enumeration guard at
  the engine level.
- **Above-alphabet.** Rust literals in `0x30000..=0x10FFFF` keep fencing
  at the lowering seam (both sides), as in slices 19/20. Terms minted
  mid-search are engine-made and in-alphabet by construction.
- **Antecedents.** Rules fire only on `side_clean` NF derivations, so
  clause guards stay single-literal; this matches the E1 gating of
  merge-derived lemmas and keeps every learnt clause valid at level 0.
- **Saturation.** A round in which every active membership is either
  discharged, skipped (unclean NF), or dedup-blocked without grounding
  out must not report Sat on its own authority; the model build + the
  extended self-check are the only path to Sat, exactly the existing
  `Saturated` posture for word equations.

## Non-goals (banked for future slices)

- The `str.to_code` inequality character-range gadget (banked since
  slice 18) — natural slice 22 on top of this machinery. Fences.
- Symbolic regex sides, RegLan equality/containment/emptiness. Fences.
- Automata construction, derivative-state memoization as a DFA, or
  per-state length-set (Parikh) lemmas into the arith seam (envelope
  option C). Fuel-bounded unfolding only.
- `str.<` / `str.<=` lexicographic ordering — still unparsed.
- Any change to the word-equation stepper, arith seam, SAT budgets, or
  the `Fuel` allotment value.

## Testing

- **Unit tests** (`regex.rs` + the new engine module): class
  partitioning — boundary math from `Range` nodes, the Σ single-class
  case, a pure-surrogate-block class, the `CLASS_SPLIT_CAP` abort;
  `rex_to_term` ∘ `extract_const_regex` round-trip (Rex-level equality);
  per-class derivative uniformity (`deriv(rep(C))` = `deriv(c)` for
  sampled `c ∈ C`); expansion-clause shape (ε disjunct iff nullable,
  single-atom disjuncts); head-split clause set shape; BFS witness
  search — finds a word of a given length, respects the surrogate skip,
  and the `MEMB_SEARCH_STEP_CAP` abort; dedup keys; TermId stability of
  untouched subtrees.
- **E2e pins** (`shinri-solver` tests): the decided idioms above —
  sat + get-value for `x ∈ [a-z]*`, `x ∈ [a-z]+ ∧ len(x) = 3`, negative
  polarity `¬(x ∈ [a-z]*)`, memberships under `not`/`or`/`ite`; unsat
  pins for `x ∈ a* ∧ x = y·"b"` (`y ∈ a*` optional), `x ∈ a* ∧ x ∈ b*
  ∧ len(x) ≥ 1`, and a literal-head mismatch via equality merge;
  `Unknown` pins for fuel exhaustion (deep nesting) and a
  `CLASS_SPLIT_CAP` overflow shape. Two slice-20 pins **flip** and are
  re-pinned as decided: the `str.in_re s re.allchar` `Unknown` pin
  (now sat) and the `(re.* (re.range "a" "b"))` neither-finite-nor-
  co-finite `Unknown` pin (now sat); the slice-19
  `non_ground_shapes_survive_to_fence` sub-case that used a `re.*` shape
  swaps to a **symbolic-regex-side** shape so it keeps testing a genuine
  fence (the slice-20 deviation lesson, applied proactively).
- **Differential oracle**: new family `qfs_regex_unfold_matches_z3`
  (`--features oracle`, fresh seed, 200 iters): random constant regexes
  over the ASCII `{a,b,c}` alphabet (slice-18/19 harness lesson: scripts
  shared with z3 stay ASCII) **including** `re.*`/`re.+`/`re.loop`/
  `re.comp` shapes with infinite languages, one symbolic string variable
  with random equality/disequality/concat/length side constraints, ~25%
  negation wrapping, unknown-tolerant, **0 disagreements required**.
  Existing families re-run; tallies expected identical except
  `qfs_regex_symbolic_matches_z3`, whose shinri-unknown count may only
  **decrease** (the solver decides strictly more; generator and seed
  untouched) — any other tally movement is a stop-the-line signal.
- **Gates**: `cargo test -p shinri-core -p shinri-parser -p shinri-str
  -p shinri-solver --features oracle` (oracle families foreground with
  captured output), `cargo fmt --check`, `cargo clippy --workspace
  --all-targets` clean; the ~50-min full workspace run stays CI-side.
