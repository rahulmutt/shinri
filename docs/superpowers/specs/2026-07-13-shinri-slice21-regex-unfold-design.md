# Slice 21 design — derivative unfolding of symbolic `str.in_re` in the string engine

Date: 2026-07-13
Status: IMPLEMENTED (slice 21 landed 2026-07-14).

Oracle (new family, fresh seed `0x53_00_0000_0001`):
`qfs_regex_unfold_matches_z3: 200 iters — 95 sat / 88 unsat /
17 shinri-unknown (tolerated) / 0 z3-unknown / 0 guard-bailout
(tolerated); 93 witnesses; 0 disagreements`. The two pre-existing regex
families moved across this slice as sanctioned (generators and seeds
untouched — the solver decides strictly more):
`qfs_regex_symbolic_matches_z3` improved from 101 sat / 68 unsat /
31 shinri-unknown / 96 witnesses at slice-20 close to 113 sat / 76 unsat /
11 shinri-unknown / 108 witnesses; `qfs_regex_ground_matches_z3` improved
from 66 sat / 107 unsat / 27 shinri-unknown / 31 witnesses at slice-20
close to 71 sat / 113 unsat / 16 shinri-unknown / 36 witnesses. The final
ground tally includes ONE controller-adjudicated sat → sound-Unknown
trade (iter 74, seed 92126202705094: `s1 ∈ Σ+` with `s1` free and no
length bound — the D-wordeq-skip deferral removed the wordeq F-split's
`len_eq` shortcut over the pass-minted `s1 = h·z`, so full-alphabet
Rule-E unfolding now exhausts the shared fuel and the unchanged length
loop hard-Unknowns; z3 cross-check clean, and the same change bought
−4 unknown on regex_symbolic in the same run, so net movement is
strongly unknown-decreasing — the pre-priced completeness cost of the
owner's freeze lift, see Deviations D-wordeq-skip). All other families
re-ran with tallies identical to their committed values; **0
disagreements everywhere**.

**Deviations from the spec.**
This slice accumulated six owner/controller-adjudicated design
deviations (A1–A6: D-gate, D-pins-unknown, D-leaf, D-lenlink,
D-satfuel, D-wordeq-skip — the last two owner-authorized, D-wordeq-skip
under a spec-freeze lift by the slice owner, 2026-07-14), plus a
controller-sanctioned plan-gap fix (D1), two sanctioned transcription
deviations (D-pin-idiom, D-harness), and several prediction
corrections. Full traces live in the task reports
(`.superpowers/sdd/task-{2..6}-report.md`).

1. **D1 — `atom.rs` classify routing (plan gap, Task 2,
   controller-sanctioned).** The spec assumed engine-eligible
   `str.in_re` atoms would reach `StrSolver::assert`, but
   `shinri_theory::atom::classify` had no route for
   `BuiltinOp::StrInRe` (fell through to `Err(Unsupported)` → SAT
   refused the atom → `Unknown` before the string solver ever saw it).
   `classify()` now routes `StrInRe` → `Owner::String` unconditionally;
   eligibility stays guaranteed upstream by the solver-seam fence, and
   the combiner's `Owner::String` path needed no change.
2. **D-pin-idiom (Tasks 2–5, sanctioned).** The plan's e2e pin snippets
   used an `expect`/`Verdict` helper that does not exist in
   `script_e2e.rs`; all pins were transcribed via that file's
   `run_script` idiom, scripts and verdicts unchanged.
3. **D-gate (Task 3, authorized; spec-over-plan).** The plan's
   `memb_check` gated guarded splits on the strict `all_cond_roots`,
   which self-blocked (the engine's own first split taints the
   variable's class; no membership is ever revisited). The spec's own
   words — "the same gating F-splits use today" — govern: guarded split
   emission gates on `side_clean(input_cond_roots)` (byte-for-byte the
   F-split emission gate), while ground-NF conflicts stay fully cited
   and ungated. The E1 soundness argument transfers verbatim (guarded
   implication + fresh lone skolems + model-gate backstop).
4. **D-pins-unknown (Task 3, adjudicated).** Two of the spec's own
   claimed unsat idioms are CALCULUS-COMPLETENESS gaps in the G/E/S
   rule set: `disjoint_stars` (`x ∈ a* ∧ x ∈ b* ∧ len ≥ 1` — needs an
   intersection-aware rule citing two membership literals; the
   single-guard Split channel cannot; saturated fixpoint with 3961/4000
   fuel remaining in the decisive experiment) and `concat_context`
   (`x ∈ a* ∧ x = y·"b"` — inductive suffix refutation; forward
   unfolding left-peels unboundedly; needs reverse derivatives). Both
   are pinned at the sound observed verdict `unknown` with KNOWN GAP
   comments; the calculus extension is deferred to a future slice.
5. **D-harness (Task 3, sanctioned).** The plan's verbatim test helper
   `harness(ctx: …)` had an unused parameter; renamed `_ctx`.
6. **D-leaf (Task 4, adjudicated; spec §Rule S ground-out sentence).**
   Rule S does not fire on a bare `Rex::Range` residual — a bare
   single-class membership is the ground-out LEAF of the unfolding
   ("realised by model repair otherwise"), decided by Rule G when the
   class grounds and realised by `memb_seeds` otherwise; unfolding it
   minted repair-ineligible concats into witness classes.
7. **D-lenlink (Task 4, adjudicated).** The membership pass emits its
   own per-equation length-link companions for its minted equalities
   (`x = h·z` link; Rule-E ε-equality link; S2's `len(h) = 1` re-routed
   through `(>=)`/`(<=)` arith companions — the bare Int equality routed
   to EUF and never reached the arith model, starving `memb_seeds` of a
   length). Unguarded `[distinct, companion]` tautology clauses, deduped
   via `emitted_len_axioms`; `minted_eqs` marking is RETAINED (the
   cond-roots machinery requires it). This does not contradict the
   banked option C: these are per-equation links (the seam's existing
   posture), not Parikh length-set lemmas.
8. **D-satfuel (Task 4, owner-authorized).** Membership-pass exhaustion
   of the shared `Fuel` SATURATES — `memb_check` returns `None` and
   `check()` falls through to the model build + repair + self-check —
   instead of a hard `Unknown`. Spec basis: the Saturation paragraph
   (Sat only ever comes from the model build + extended self-check, so
   this can only cost decisiveness, never soundness). Implemented as a
   single fuel peek at the top of the per-atom loop before any dedup
   key is minted; `emit_split`'s fuel guard became a `debug_assert!`.
   `Fuel` allotment (40) unchanged; the unit test
   `fuel_exhaustion_yields_unknown` became
   `fuel_exhaustion_saturates_to_model_path`.
9. **D-wordeq-skip (Task 4, owner-authorized FREEZE LIFT, 2026-07-14).**
   The spec froze the word-equation stepper; the owner lifted that
   freeze for exactly this: the wordeq loop DEFERS its F-split/char-peel
   emission over string equalities the membership pass minted (new
   monotone `memb_minted_eqs` set, populated in `memb.rs::register_atom`,
   consulted only at the wordeq loop's `StepResult::Split` arm). These
   equalities are definitional — the S-rules are their resolution; EUF
   merges, NF participation, ground resolution and conflict derivation
   are untouched, and `resolve_equation` itself is unchanged. This
   landed the nonnullable-sat and negative-polarity-sat idioms, at ONE
   adjudicated completeness trade: `qfs_regex_ground` iter 74
   (`s1 ∈ Σ+` free, no length bound) moved sat → sound-Unknown — the
   pre-named cost class the freeze lift priced in (net movement
   strongly unknown-decreasing; see the Oracle paragraph).
10. **Task-5 prediction corrections.** (i) The slice-20 star-range pin
    (`(re.* (re.range "a" "b"))`) had ALREADY flipped to Sat at Task 2
    (commit 1274398) — Task 5 only confirmed it; the `re.allchar`
    sibling pin in `qfs_differential.rs` carried a stale slice-20-era
    comment, reconciled in this truth-up commit (the pin's verdict —
    `Unknown` — is unchanged and re-verified; only the comment now
    names the slice-21 cause). (ii) Bare `re.allchar` did NOT flip
    (KNOWN GAP: bare-range repair leaf + Σ > `ENUM_WORD_CAP` + no
    pinned length; decides Sat once a length is pinned — companion pin
    in `script_e2e.rs`). (iii) The brief's get-value pin shape
    (`[a-z]+ ∧ len = 2`) hits the intersection gap; get-value is pinned
    on the bare `[a-z]+` shape instead, and the len-2 shape is pinned
    Unknown. (iv) Open observation: the `CLASS_SPLIT_CAP` pin's
    union-of-singleton-ranges family yields Unknown already from N = 4
    (9 cuts, well below the cap of 64) for a reason that was NOT
    isolated; the pin uses N = 33 so the cap fence provably fires
    regardless of which limit trips first.

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

Decided idioms this unlocks (all previously `Unknown`) — **as-landed
scoreboard** (see the Deviations section for the adjudications; the
original claims are annotated, not deleted):

- `x ∈ (re.range "a" "z")*` — sat, with a get-value witness.
  **DELIVERED** (the slice-20 star-range pin flipped to Sat at Task 2).
- `x ∈ (re.+ (re.range "a" "z")) ∧ len(x) = 3` — sat with a length-3
  witness. **NOT DELIVERED — KNOWN GAP** (intersection gap: the SAT
  layer decides pass-minted membership atoms at polarities jointly
  unsatisfiable over one witness leaf; refuting that needs an
  intersection-aware conflict rule citing TWO membership literals, which
  the single-guard `TCheck::Split` channel cannot express). The
  length-FREE `x ∈ (re.+ (re.range "a" "z"))` IS delivered — sat with a
  witness via model repair (D-wordeq-skip).
- `x ∈ (str.to_re "a")* ∧ x = y·"b"` — unsat via unfolding against the
  word equation. **NOT DELIVERED — KNOWN GAP** (concat-context: the
  refutation "every a\*-word ends in 'a'" is inductive over the suffix;
  forward derivative unfolding left-peels unboundedly — needs reverse
  derivatives / suffix-aware handling).
- `x ∈ (str.to_re "a")* ∧ x ∈ (str.to_re "b")* ∧ len(x) ≥ 1` — unsat.
  **NOT DELIVERED — KNOWN GAP** (disjoint-stars: deciding a\* ∩ b\*
  above ε needs intersection-awareness, inexpressible in the
  single-guard Split channel; the G/E/S unfolding saturates → sound
  Unknown).
- `¬(x ∈ (re.range "a" "z")*)` — sat via `Rex::Comp`, with a witness.
  **DELIVERED** (negative-polarity sat, witness "BBBBB").
- `str.in_re s re.allchar` for symbolic `s` — the slice-20 `Unknown` pin
  flips to decided (Σ is ONE class here, not `0x30000` enumerated words).
  **NOT DELIVERED bare — KNOWN GAP** (a bare `Rex::Range` residual is a
  repair LEAF (D-leaf), Σ is far over `ENUM_WORD_CAP`, and with no
  pinned length the model has no length to search a repair word at);
  **DELIVERED with a pinned length** (`re.allchar ∧ len(s) = 1` decides
  Sat — see the `script_e2e.rs` companion pin).

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
F-splits use today. (As landed, "the same gating F-splits use today"
means exactly that: guarded split emission gates on
`side_clean(input_cond_roots)` — the F-split emission gate — while
fully-cited conflicts stay ungated; the plan's stricter `all_cond_roots`
reading self-blocked and was overruled, see Deviations, D-gate.) A
membership whose NF is not clean this round is
simply skipped (sound; it is revisited on later rounds).

Progress is by three rules, tried in order. Every emitted lemma spends
one unit of the existing per-solve `Fuel` (40, `fuel.rs`) and is
deduplicated by a `(string-side TermId, regex TermId)` set analogous to
`emitted_splits`; a dedup hit with no other progress leaves the
membership unresolved, and the round ends in the `Saturated` posture —
the solver must not conclude Sat from it (the self-check backstop
below enforces this). (As landed, shared-`Fuel` exhaustion in this pass
takes the SAME saturation posture — it falls through to the model
build + repair + self-check instead of a hard `Unknown` — an
owner-authorized change, see Deviations, D-satfuel. The per-atom
soundness fences — extraction failure, non-convergent NF,
`FUEL_NODE_CAP`, `CLASS_SPLIT_CAP` — still hard-`Unknown`.)

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
model repair otherwise). (As landed: a bare `Rex::Range` residual is
exactly that ground-out leaf, so Rule S does NOT recurse on it — see
Deviations, D-leaf; and the S2 witness clause plus the minted
equalities' length links are emitted through `(>=)`/`(<=)` arith
companions rather than bare Int equalities — see Deviations,
D-lenlink.)

No changes to the word-equation stepper (`resolve_equation`), the arith
seam, the SAT `step_budget`, or the `Fuel` allotment value — the new
lemmas ride the existing channels and budgets. (As landed, this freeze
was PARTIALLY lifted by the slice owner (2026-07-14): the wordeq loop
now DEFERS its F-split emission over equalities the membership pass
minted (`resolve_equation` itself unchanged) — see Deviations,
D-wordeq-skip; and the pass emits its own per-equation length-link
companions for its minted equalities — see Deviations, D-lenlink. The
arith seam, SAT `step_budget`, and the `Fuel` allotment value (40) are
unchanged as written.)

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
  the `Fuel` allotment value. (Freeze partially lifted by the slice
  owner mid-slice, 2026-07-14 — see Deviations, D-wordeq-skip and
  D-satfuel; arith seam / SAT budgets / `Fuel` value stand.)

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
  (As landed: only the star-range pin flipped (Sat, at Task 2); bare
  `re.allchar` did NOT flip — it is a KNOWN GAP, see the idiom list
  above and Deviations; and `non_ground_shapes_survive_to_fence`
  needed no swap — it exercises only `rewrite_ground_in_re` /
  `has_unreduced_regex`, never the solver, so it cannot pin solver
  semantics.)
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
  (As landed: `qfs_regex_ground_matches_z3` also moved — strongly
  unknown-decreasing overall, but including one adjudicated sat →
  sound-Unknown instance at iter 74; see the Oracle paragraph at the
  top and Deviations, D-wordeq-skip.)
- **Gates**: `cargo test -p shinri-core -p shinri-parser -p shinri-str
  -p shinri-solver --features oracle` (oracle families foreground with
  captured output), `cargo fmt --check`, `cargo clippy --workspace
  --all-targets` clean; the ~50-min full workspace run stays CI-side.
