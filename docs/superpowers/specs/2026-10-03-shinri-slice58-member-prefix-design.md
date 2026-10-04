# Slice 58 — Membership Rule G over class concat members

Status: design approved in chat 2026-10-03. Picks up the slice-57 report's
queue item 1 (`docs/superpowers/research/2026-10-03-smtlib-2024-slice57-str-model-reconcile-report.md`,
§ Queued for the next slice): "engine-side reconciliation (approach 2)",
whose reproducers are `translate-rotate-fuzz` and `translate-graft-translate`.
Scope ruling (owner, in chat): trace-driven minimum — trace the two `unsat`
reproducers first and fix only what they need. The trace (§1.2) showed that
neither needs any of the three queued parts; this slice adds one
membership-pass rule and re-scopes the rest of the queue (§9).

**Area:** `shinri-str` (`memb.rs`, `memb_check` only). Tests in `shinri-str`
(unit, `memb.rs`), `shinri-solver` (new `slice58_probes`, a new oracle family
in `qfs_differential.rs`, the two `slice57_probes` known-unknown pins moved).
No parser, SAT, Combiner, `wordeq.rs`, `normalize.rs`, `lower`, length-seam,
model-builder or gate change.

## 1. Summary

### 1.1 The rows

| input (QF_SLIA, `x`, `y` String) | HEAD (`f515c00`) | z3 |
| --- | --- | --- |
| `(= (str.len x) 3)`, `(= x y)`, `(str.in_re y (re.+ (re.range "a" "b")))`, `(str.prefixof "\\" x)` | `unknown fence=str-model-rejected` | `unsat` |
| `(= 2 (str.len x))`, `(= x y)`, `(str.in_re y (re.* (re.range "a" "b")))`, `(str.prefixof "1" x)` | `unknown fence=str-model-rejected` | `unsat` |

These are `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-translate-rotate-fuzz.smt2`
and `regex-050-translate-graft-translate.smt2`, pinned `unknown` today by
`slice57_probes::k1_stringfuzz_translate_rotate_stays_unknown` and
`k2_stringfuzz_translate_graft_stays_unknown`.

### 1.2 Mechanism (traced with throwaway debug output, not committed)

1. The `prefixof` reduction asserts `x = "1" ++ !pfx0` at level 0, and
   `x = y` merges `x`, `y` and that concat into one EUF class. The search
   later adds minted members such as `"1" ++ !strk0` (char-peel) and
   `!strk1 ++ !strk2` (membership unfolding).
2. `normalize::rep_rank` deliberately never picks a concat as a class
   representative (constant > anything else; a concat rep corrupts
   normalization). So the class rep is the variable `y` (or `x`), and both
   the single-level and the deep normal form of `y` are `["y"]`.
3. `memb_check`'s Rule G consumes the ground prefix of `t`'s deep NF through
   the regex derivative. With `nf = ["y"]` it consumes nothing; the atom goes
   to Rule S/E unfolding, which never sees the `"1"` either.
4. The word-equation loop resolves `x = "1" ++ !pfx0` against `["y"]` and
   only splits or saturates; there is no constant clash for it to find.
5. The model builder cannot satisfy both the prefix and the membership, so
   the gate rejects: `unknown fence=str-model-rejected`.

`∂_"1"([a-b]*) = ∅` (and `∂_"\\"([a-b]+) = ∅`): a conflict citing only the
membership literal and the merges `y ≈ "1" ++ …` exists at every point of
the search; the membership pass never looks at the class member that
carries it.

### 1.3 Throwaway probe (not kept)

Trying every concat member of `t`'s class in Rule G (cited `explain(t, k)` +
the member's cited deep NF, conflict on an empty derivative):

| row | HEAD | probe |
| --- | --- | --- |
| `translate-rotate-fuzz` | `unknown` | **`unsat`** (via `"\\" ++ !pfx0`, < 1 ms) |
| `translate-graft-translate` | `unknown` | **`unsat`** (via the minted `"1" ++ !strk0`, < 1 ms) |
| `multiply-reverse-fuzz` | `sat` | `sat` |

## 2. Scope

In:

- Rule G′ in `memb_check` (§4).
- Tests (§7) and a bench measurement over QF_S and QF_SLIA (§8).

Out (re-queued, §9):

- The slice-57 queue item 1 parts: the partial constant-head strip in
  `resolve_inner` (`wordeq.rs:1056`), a cited deep normal form on the
  word-equation conflict/split path, and length links for minted equations.
  No current reproducer needs them.
- A suffix (reverse-derivative) analogue of G′.
- Bare-E and the `Not(Eq)` arm removal; the axiom memory measurement.

## 3. Approaches considered

1. **Rule G over class concat members (chosen).** Local to `memb_check`,
   adds only fully-cited conflicts, mints nothing, spends no fuel.
2. **Concats eligible as normal-form representatives** (prefer a
   constant-headed concat in `rep_rank`). Fixes every consumer at once, but
   `rep_rank`'s documented hazard is exactly this, and it changes every
   word-equation conflict/split — the E1 wrong-UNSAT area. Rejected.
3. **A cited deep NF through variable reps on both the word-equation and
   membership paths** (the broad slice-57 queue item). Covers more shapes,
   none of which a current reproducer needs. Stays queued, behind the
   population classification (§9 item 1).

## 4. Design

### 4.1 Placement

In `memb_check` (`crates/shinri-str/src/memb.rs`), per membership atom
`t ∈ R` (`R` already complemented for negative polarity):

1. Rule G as today: consume `t`'s cited deep NF; a fully ground NF
   discharges (nullable) or conflicts.
2. **Rule G′ (new)**, only when step 1 neither discharged nor conflicted.
3. The existing arms, unchanged: the bare-range leaf, the slice-26 lone-leaf
   carve-out, Rule S, Rule E.

G′ sits before the leaf arms because they `continue` past the atom.

### 4.2 Rule G′

1. **Candidates.** The distinct terms `k` in `known` with
   `k` a `str.++` application, `find(k) == find(t)`, and `k ≠ t`, in `known`
   order. At most `MEMBER_CAP = 64` are examined per atom; the rest are
   skipped (decisiveness only, never a verdict).
2. **Per candidate**, with a fresh `ante: Vec<EqLeaf>`:
   - `eq.explain(t, k, &mut ante)`;
   - `normalize::deep_normal_form_cited(terms, eq, known, k, &mut ante)`;
     `None` (non-convergent) ⟹ skip this candidate. Not `Unknown`: G′ is
     additive, so a fence on it would lose verdicts the existing arms reach.
   - Starting from `R`, apply `regex::deriv` for every char of the NF's
     leading string-constant atoms, stopping at the first non-constant atom.
     If `regex::node_count` exceeds `regex::FUEL_NODE_CAP`, skip this
     candidate.
   - If the result is `Rex::Empty` (the syntactic test Rule E uses), return
     `TCheck::Conflict([EqLeaf::Asserted(lit)] ++ ante)`.
3. No candidate conflicts ⟹ fall through to step 3 of §4.1 with no state
   change.

G′ emits no split or lemma, mints no term, records no dedup key and spends
no fuel.

### 4.3 Soundness

The learnt clause is `¬lit ∨ ¬A`, where `A` is the conjunction of the cited
antecedents: the merges proving `t ≈ k` and the merges the deep NF
substituted. Under `A`, `t = w · u` for the consumed constant prefix `w` and
some string `u`.

- Positive polarity: `∂_w R = ∅` means no word with prefix `w` is in `R`,
  so `t ∉ R`, contradicting `lit`.
- Negative polarity (`R = comp(R₀)`): `∂_w comp(R₀) = ∅` means every word
  with prefix `w` is in `R₀`, contradicting `t ∉ R₀`.

Every substituted merge is cited, so the clause is valid at any decision
level and needs no `side_clean` gate — the same argument as Rule G's
existing ungated ground conflict (`expand_ante`). A minted member is only a
premise: its equation literal reaches the clause through `explain`, so a
branch where it is false is untouched (§7.3 `g2`, `g3`).

### 4.4 Cost

Per membership atom per Full check: one scan of `known` plus at most 64
cited deep NFs and derivative prefixes. `build_node_of` already scans
`known` on every normal-form call, so this is the same order; §8
criterion 5 measures it.

## 5. What this does not change

The SAT core, the Combiner, `wordeq.rs`, `normalize.rs`, the length seam,
`lower`, the parser, the model builder, the gates, and every non-string
path. Within `memb_check`, Rule G, the leaf arms and Rule S/E behave exactly
as before whenever G′ finds no conflict.

## 6. Tasks

1. **Base run.** `slice58-base` at the branch point over QF_S and QF_SLIA
   (§8), built first and run detached (slice-53 ruling R1).
2. **Failing tests first.** `slice58_probes.rs` (§7.3) and the oracle
   family (§7.4). Record that `m1`–`m4` fail at HEAD and the oracle's
   `unknown`-where-z3-`unsat` count as "before" evidence. Move
   `slice57_probes::k1`/`k2` (§7.3).
3. **Rule G′** (§4), with the §7.1 unit tests first.
4. **Gates and re-run.** `mise run ci`, the oracle suite, then `slice58`
   over the same logics, the report, and a *Measured outcomes* section
   appended to this spec.

## 7. Testing

### 7.1 Unit (`shinri-str`, `memb.rs` tests)

- A G′ conflict's justification contains the membership literal and the
  `t ≈ k` merge antecedents.
- A member whose derivative is non-empty leaves the atom to the existing
  arms: Rule E emits the same split as without G′.
- At decision level > 0 the conflict cites the decision literal that merged
  the member (it is not a level-0 fact).
- A class with more than `MEMBER_CAP` concat members: no G′ effect past the
  cap, never `Unknown`.

### 7.2 Unit (`shinri-solver`)

None: no solver-crate code changes.

### 7.3 End to end (`crates/shinri-solver/tests/slice58_probes.rs`, blocking tier)

Targets (fail at HEAD):

| probe | input shape | expect |
| --- | --- | --- |
| `m1_translate_rotate` | `len x = 3`, `x = y`, `y ∈ [a-b]+`, `prefixof "\\" x` | `unsat` |
| `m2_translate_graft` | `2 = len x`, `x = y`, `y ∈ [a-b]*`, `prefixof "1" x` | `unsat` |
| `m3_deep_nf_prefix` | `x = "a" ++ z`, `z = "b" ++ w`, `y = x`, `y ∈ "ac" · Σ*` | `unsat` |
| `m4_negative_polarity` | `x = y`, `prefixof "a" x`, `¬(y ∈ "a" · Σ*)` | `unsat` |

Sound-direction guards (`sat`; the witness satisfies every assertion):

| probe | input shape | guards |
| --- | --- | --- |
| `g1_compatible_prefix` | `prefixof "a" x`, `x = y`, `y ∈ [a-b]+` | non-empty derivative ⟹ no conflict |
| `g2_conditional_member` | `(or (= x (str.++ "1" z)) (= x "ab"))`, `x ∈ [a-b]*` | the `"1"` branch's conflict cites its disjunct; the `"ab"` branch survives (the E1 ce2 shape) |
| `g3_minted_member_other_branch` | as `m2` with `y ∈ ([a-b] ∪ "1")*` | a consistent minted `"1" ++ !strk` member ⟹ no conflict |

`m1` and `m2` are measured to fail at HEAD (§1.3). If `m3` or `m4` already
passes at HEAD, Task 2 records that and keeps it as a regression guard. If
`m4` stays `unknown` after G′ because `regex::deriv` over `comp` does not
reduce to `Rex::Empty` syntactically, that is recorded as a deviation and
queued, not fixed here (the emptiness test stays Rule E's).

`slice57_probes::k1`/`k2` are removed; `m1`/`m2` replace them with the
`unsat` expectation, and a one-line comment in `slice57_probes.rs` points to
`slice58_probes`.

### 7.4 Oracle (feature `oracle`, `qfs_differential.rs`)

`differential_qfs_member_prefix`, fresh seed, 300 iterations. Scripts: one
or two String variables; `x = y` and `x = lit ++ v` equations;
`prefixof`/`suffixof` with literals; one membership, positive or negative,
over a pool of `[a-b]`, `[a-d]`, literal-headed concats, `*`/`+` and
`comp`; an optional length pin; about one in three wraps one equation in an
`or` with an alternative to force conditional merges.

Asserted: 0 disagreements with z3; every `sat` model z3-verified; non-zero
`sat` and `unsat` counts; the `unknown`-where-z3-`unsat` count at HEAD is
recorded as a `const` (as slice 57's `MR_BEFORE_UNKNOWN_Z3_SAT`) and the
after count is strictly lower.

### 7.5 Unchanged suites

`slice57_probes` (minus `k1`/`k2`), `qfs_fuzz_corpus` and every existing
`qfs_differential` family pass unchanged.

## 8. Measurement

Two `mise run bench-run` runs at default limits (20 s, 3072 MB, 6 jobs):
`slice58-base` at the branch point and `slice58` at the slice head, over
QF_S and QF_SLIA. QF_LIA is not run: only string logics reach the
membership pass.

Every changed row that starts or ends in `correct` is re-run 3× per binary,
interleaved, with the bench's command line (slice-53 triage method). Large
groups may use a stratified sample, stated with its size. The report counts
the changed rows G′ itself decided (a `--stats` or probe check per row
group), which sizes the population beyond the two reproducers.

### Success criteria

| # | criterion | kind |
| --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | hard; any hit stops the slice for a ruling |
| 2 | `translate-rotate-fuzz` and `translate-graft-translate` answer `unsat` (`correct`) | hard |
| 3 | credited `unknown:str-model-rejected` (QF_S + QF_SLIA) does not increase; a row whose base binary also gives that fence in triage counts in the base (slice-57 ruling) | hard |
| 4 | every `correct → *` row triaged; no reproducible `correct → *` loss | hard |
| 5 | serial, interleaved timing on sampled both-`correct` QF_S and QF_SLIA rows: summed wall time within ±5% of base | hard |
| 6 | §7 gates: `mise run ci` green; oracle suite passes with a non-zero discovered count; §7.4 count strictly falls with 0 disagreements | hard |

## 9. Queued for the next slice

1. **Classify the `str-model-rejected` population** (4,089 rows at slice 57,
   minus this slice's movement), for example by the first violated
   assertion and the class shape. This absorbs slice-57 queue items 1 and 6:
   the remaining approach-2 parts (constant-head strip, cited deep NF on the
   word-equation path, minted length links) have no current reproducer and
   wait for one from the classification.
2. **Bare-E and `Not(Eq)` arm removal — possibly unblocked.**
   `translate-rotate-fuzz` was the smallest reproducer of the order
   sensitivity that blocked it. Re-run the R6 probes
   (`slice33_probes::probe_c_len_zero_var`,
   `script_e2e::user_pfx_name_declared_before_any_mint_still_works`) with
   bare-E applied, in that slice.
3. **Suffix analogue of G′** (reverse derivative over a member's constant
   tail), only if the classification shows suffix shapes.
4. Every other item of the slice-57 report's queue (3–5 and the carried
   lists), unchanged.

## 10. References

- Slice-57 report, § Queued for the next slice (item 1); slice-57 spec
  `docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md`
  (§1.2, §3, §9).
- Code:
  - `crates/shinri-str/src/memb.rs:146` (`memb_check`), `:185` (Rule G),
    `:494` (Rule E's `Rex::Empty` test)
  - `crates/shinri-str/src/normalize.rs:46` (`rep_rank`), `:97`
    (`normal_form_cited`), `:211` (`deep_normal_form_cited`)
  - `crates/shinri-solver/tests/slice57_probes.rs:181`, `:194` (`k1`, `k2`)

## 11. Measured outcomes

Full evidence:
`docs/superpowers/research/2026-10-04-smtlib-2024-slice58-member-prefix-report.md`.

| # | criterion | result |
| --- | --- | --- |
| 1 | 0 `* → wrong`; 0 wrong answers in triage | PASS: 0 `wrong` rows in either run (103,335 rows each), 0 wrong answers in 306 triage runs; no changed row ends `unverified`, so the z3 check has 0 rows and 0 disagreements |
| 2 | `translate-rotate-fuzz`, `translate-graft-translate` answer `unsat` | PASS: both `str-model-rejected → correct`, base `unknown` 3/3, after `unsat` 3/3 |
| 3 | credited `str-model-rejected` does not increase | PASS on the combined count: QF_S 966 → 970 (+4), QF_SLIA 3,122 → 3,114 (−8), combined 4,088 → 4,084 (−4); raw = credited (no row credited) |
| 4 | no reproducible `correct → *` loss | PASS: 0 `correct → *` rows; net `correct` QF_S +3, QF_SLIA +36 |
| 5 | serial timing within ±5% | PASS: QF_S 0.974 (1.07 s vs 1.04 s), QF_SLIA 1.017 (1.59 s vs 1.62 s), 150 rows each |
| 6 | `ci` green; oracle suite non-zero, passing; §7.4 count falls | PASS: `ci` exit 0, 1735/1735 passed (6 skipped); oracle suite 808/808 passed (2 skipped); §7.4 count 69 → 47, 0 disagreements |

Rows decided by G′: 8, all QF_SLIA stringfuzz `transformed/z3str2/regex-050-*`
(`unknown:str-model-rejected → correct`; base `unknown` 3/3, after `unsat` 3/3).

### Deviations from this spec

- Guards `g1`, `g3`, `rf2`, `rf3` (`unknown fence=str-model-rejected` at
  HEAD) and `rf4` (`unknown fence=sat-budget`) only forbid `unsat` and
  witness-check any `sat`; z3 answers `sat` for all five, and conflict-only
  G′ cannot change them. The shapes are queued (§9 item 1).
- `m4` already passed at HEAD (regression guard); before-count 7 PASS / 4 FAIL.
- `differential_qfs_member_prefix` takes about 669 s and is not `#[ignore]`d:
  it runs only in the nightly-only `oracle` CI job.
- Unit test `g_prime_reads_member_deep_nf` reorders `known` (`cb` before `z`)
  because `build_node_of` picks the first non-constant term as the
  representative.
- Oracle `sat` fell 73 → 71 (two `sat → unknown`, decisiveness only, 0
  disagreements).
- QF_S `str-model-rejected` rose by 4 (8 rows from `sat-budget`, 4
  rows back to `sat-budget`, all reproducible 3/3 and none `correct`); the
  criterion is on the combined count, which fell by 4.
- 31 `unverified → correct` rows are base-run z3 oracle timeouts with
  identical shinri answers; not credited to the slice.
