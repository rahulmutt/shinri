# Slice 29 design — enumeration↔length seam: exact-length companion

Date: 2026-07-18
Status: IMPLEMENTED (2026-07-18). See "Implementation notes (truth-up)" at
the end.

Predecessor: slice 28 (Rex intersection-emptiness refutation, landed
2026-07-17). Slice 28's truth-up banked nothing new; the oldest live
known-gap pin is slice 22's enumeration-length seam gap,
`targeted_to_code_range_length_seam_known_gap`
(`crates/shinri-solver/tests/qfs_differential.rs:3431`): both
`(>= (str.to_code s) 48) ∧ (<= (str.to_code s) 57) ∧ len(s) = 2` and its
`to_code`-free control `s ∈ (re.range "0" "9") ∧ len(s) = 2` return a
sound `Unknown`; z3 answers unsat. This slice cashes that item.

## 1. Problem — enumeration discards length information

Root cause, established empirically (2026-07-18):

- **Non-enumerable memberships already close this seam.** The slice-25/26
  arms of `memb::memb_check` emit guarded `min_len`/`max_len` axioms
  (`crates/shinri-str/src/memb.rs:247` bare-`Range` arm, memb.rs:289–360
  lone-leaf carve-out). Probes confirm both the finite-but-wide
  (`"ab"·Σ·Σ ∧ len = 7`) and infinite (`a·Σ* ∧ len = 0`) shapes decide
  Unsat today.
- **A structurally finite language within the enumeration caps never
  reaches `memb_check`.** The slice-20 preprocessing rewrite
  (`try_rewrite_symbolic_in_re`, `crates/shinri-str/src/regex.rs:1194`)
  replaces `t ∈ R` with `⋁ᵢ t = wᵢ` — a full equivalence, but one that
  drops the length fact the regex carried. Refutation against an
  independent `str.len` constraint then degrades to the SAT layer trying
  disjuncts one at a time, each refutation spending several length-axiom
  emissions from the shared string fuel (`Fuel::default() = 40`,
  `crates/shinri-str/src/fuel.rs:21`).
- **Bisection:** the hand-written `(or (= s "0") …) ∧ len(s) = 2`
  disjunction decides Unsat up to 8 disjuncts and goes Unknown at exactly
  9. `re.range "0" "9"` enumerates to 10 — past the fuel cliff.

## 2. Fix — exact-length companion at the rewrite

When the **finite** branch of `try_rewrite_symbolic_in_re` fires
(regex.rs:1199, `enum_lang` recognized `L(R)`), rewrite `t ∈ R` to

```
(and (⋁ᵢ (= t wᵢ))  (⋁ⱼ (= (str.len t) ℓⱼ)))
```

where `{ℓⱼ}` is the set of **distinct** word lengths of the enumerated
set, counted in code points (`w.chars().count()` — every enumerated
character is in-alphabet by the `enum_lang` surrogate/`MAX_CODE` fences,
so Rust `char` count equals SMT-LIB code-point count). For
`re.range "0" "9"` the companion is the single unit fact `len(t) = 1`,
which arith refutes against an asserted `len(t) = 2` instantly — no fuel
spent, no SAT case split.

Details:

- **Cap:** emit the companion only when the number of distinct lengths is
  ≤ `LEN_FACT_DISTINCT_CAP = 4`; otherwise skip it entirely. The
  companion is an implied fact, so skipping is always sound and merely
  preserves today's behavior. This bounds the added SAT burden.
- **Co-finite branch unchanged** (regex.rs:1202): a complement has min
  length 0 and no finite max — no derivable companion.
- **Degenerate cases:** an empty word set already folds to `false` in
  `mk_eq_disjunction` (no companion); a singleton length set emits a bare
  equality, not a 1-ary `or` (same folding discipline as
  `mk_eq_disjunction`).
- **Polarity:** the rewrite replaces the atom inside the assertion tree
  at any polarity (memoized bottom-up `rewrite`). Because the companion
  is entailed by the disjunction, the replacement is a genuine
  equivalence and stays correct under negation, in `ite` conditions,
  everywhere.

*Alternatives considered:* (B) min/max bounds companion — rejected:
strictly weaker (a gappy length set `{1,3}` cannot refute `len = 2`) for
barely less code. (C) fuel-free ground-constant length propagation in the
wordeq/length seam — more general (also fixes hand-written wide
disjunctions) but touches the core fuel discipline; **banked**, not
rejected (§4).

## 3. Soundness

For any finite word set `W = {w₁…wₙ}`, `t ∈ W` entails
`len(t) ∈ {|w₁|,…,|wₙ|}`. Conjoining an entailed formula preserves
logical equivalence, so the rewrite remains the full equivalence slice 20
established, at every polarity. The rewrite itself decides nothing; the
companion only adds a fact arith previously lacked — the same posture as
the slice-25/26 guarded axioms, but unguarded here because it is conjoined
into an equivalence rather than emitted as a theory lemma.

Verdict-monotonicity is expected but not syntactically guaranteed: the
companion mints a `str.len t` term per enumerated membership, which enters
the string↔arith shared set even when no length constraint exists and
could in principle shift fuel behavior elsewhere. The oracle
dump-and-diff gate enforces it empirically: every flip must be
`Unknown → decided`, zero `decided → Unknown`, zero `sat ↔ unsat`.

## 4. Completeness boundary and non-goals (banked)

Stays `Unknown`, by design:

- **Hand-written wide equality disjunctions** (the n ≥ 9 bisection repro):
  only enumeration-derived disjunctions get the companion. The general
  fix is approach C (fuel-free constant-length propagation) — banked.
- **Distinct-length sets > `LEN_FACT_DISTINCT_CAP`** — companion skipped.
- **Co-finite memberships** — no derivable length fact.
- Standing bank unchanged: slice-28 §8 (conflict-core minimization,
  cross-term/eq-class-aware aggregation, cap-raising) and the slice-27
  typed-antecedent refactor.

## 5. Testing

**Targeted e2e pins (`qfs_differential.rs`).**

- **Flip:** retire `targeted_to_code_range_length_seam_known_gap` into a
  `_now_decides` pin — both the `to_code` form and the `to_code`-free
  control → Unsat, z3 re-confirmed.
- **New positive pin:** gappy length set — `s ∈ ("a" ∪ "abc") ∧
  len(s) = 2` → Unsat. Pins the *exact*-length strength over min/max
  bounds (the anti-alternative-B pin: bounds alone cannot decide this).
- **New negative guards:**
  - `s ∈ [0-9] ∧ len(s) = 1` stays Sat (companion must not over-fire);
  - negative polarity: `s ∉ [0-9] ∧ s = "3"` → Unsat (equivalence
    preserved under negation);
  - `s ∉ [0-9] ∧ len(s) = 2` stays Sat (co-finite side untouched).
- **Re-examine** `targeted_regex_bare_range_multi_atom_residual_stays_unknown`
  (qfs_differential.rs:3408, `s·"a" ∈ [x-z]`): the companion gives
  `len(s·"a") = 1` and may cascade to Unsat. If it flips z3-confirmed,
  retitle to `_now_decides`; otherwise it stays pinned as observed —
  either outcome is acceptable, not promised.

**Unit (`regex.rs`).** Companion emitted with deduped distinct lengths;
code-point counting on an astral-character word; cap fence (5 distinct
lengths → no companion, disjunction unchanged); empty-set `false` fold
unchanged; singleton length emits a bare equality.

**Differential oracle** (house cadence: `--features oracle`, run
foreground with captured output). Expect 0 shinri-vs-z3 disagreements;
unknowns down. Per-iteration dump-and-diff (base vs fix): every flip
`Unknown → decided`; zero `decided → Unknown`, zero `sat ↔ unsat`.

**Gate list.** Run locally pre-push: `shinri-str`,
`qfs_differential --features oracle`, and `script_e2e` — a
completeness-shifting string change can flip string-side e2e pins; any
z3-confirmed `Unknown → decided` flip is an adjudicated flip, not a
blocker (slice-25/26/28 precedent). Plus
`cargo clippy --workspace --all-targets -- -D warnings` and
`cargo fmt --check`.

## Implementation notes (truth-up)

Implemented 2026-07-18 on branch `slice29-enum-length-companion`
(base `8a6dc95b` = plan commit; spec `fc9ef303`).

**Landed as designed:**

- `6cab388f` — §2 companion: private `fn conjoin_len_fact(ctx: &mut
  Context, t: TermId, ws: &Words, disj: TermId) -> TermId` and `const
  LEN_FACT_DISTINCT_CAP: usize = 4` in `regex.rs`, called from the finite
  branch of `try_rewrite_symbolic_in_re` (regex.rs:1199). Distinct lengths
  via `BTreeSet<usize>` of `w.chars().count()` (code points, ascending);
  `> CAP` → companion skipped; empty word set → untouched `false` fold;
  singleton length set → bare `(= (str.len t) ℓ)`, no 1-ary `or`;
  co-finite branch untouched. 3 new unit tests (gappy `{1,3}` → `(or …)`
  in ascending order; astral `"\u{2FFFF}b"` → `len = 2`, not the 5-byte
  count; 5-distinct-length cap fence → bare disjunction) plus
  `symbolic_finite_atom_rewrites_to_eq_disjunction` updated to unwrap the
  companion `And`. `symbolic_cofinite_atom_rewrites_to_negated_disjunction`
  and `symbolic_zero_word_languages_fold_to_bool_consts` pass unchanged.
  Code verbatim from plan.
- `459d7a6e` — §5 pins: `targeted_to_code_range_length_seam_known_gap`
  (slice 22) flipped to `targeted_to_code_range_length_seam_now_decides` —
  both the `to_code` gadget form and the `to_code`-free control decide
  Unsat, z3 cross-checked inline by `expect`. New
  `targeted_enum_gappy_length_set_unsat` (the anti-alternative-B pin:
  `s ∈ {"a","abc"} ∧ len(s) = 2` → Unsat despite 1 ≤ 2 ≤ 3, which a
  bounds-only companion could not decide) and
  `targeted_enum_length_companion_guards` (consistent length stays Sat;
  negative polarity `s ∉ [0-9] ∧ s = "3"` → Unsat; co-finite
  `s ∉ [0-9] ∧ len(s) = 2` stays Sat). Code verbatim from plan.
- `1e05649b` — comment-only follow-ups from the final whole-branch review
  (no code, query-string, assertion, or test-name changes; verified every
  changed line begins `//`/`///`). See "Deviations" item 4 and the
  companion doc-comment fence attribution below.

**§5 re-examination outcome:** the negative-polarity guard decided
**Unsat** on the primary branch — the plan's sound-but-weaker `Unknown`
fallback was not taken.
`targeted_regex_bare_range_multi_atom_residual_stays_unknown`
(qfs_differential.rs:3408) **stayed Unknown** — no cascade — and was left
untouched, which §5 admits as an acceptable outcome (not promised).

**Deviations:** none in behavior (both code diffs verbatim from the plan,
modulo rustfmt; `1e05649b` is comment-only). Four plan-text defects, all
corrected in execution, none affecting what was measured or shipped:

1. Task 2 Step 5 expects `grep -c
   "targeted_to_code_range_length_seam_known_gap"` to return `0`, but the
   Step-1 doc comment the plan itself mandates quotes the retired name in
   prose ("was `…_known_gap`, slice 22"). Corrected expectation: exactly
   1 hit, in that doc-comment cross-reference, with the `fn` definition
   gone — verified.
2. Task 3 Steps 3/4 omit `--nocapture`. Rust's harness captures
   `eprintln!` from passing tests, so the first fix-side dump produced
   **0** DIFFDUMP lines despite the run passing 81/0. Both sides rerun
   with `--nocapture` (matching Step 1, which already carried it).
   Anyone re-running this dump-and-diff recipe needs the flag.
3. Task 3's scratchpad path carried a stale session id (substituted at
   dispatch).
4. **Plan factual error** (also this spec's §5 third guard bullet, and the
   plan's Task-2 Step-2 comment text, both of which label the query
   "co-finite side untouched"). The final whole-branch review established
   that `¬(s ∈ [0-9]) ∧ len(s) = 2` never reaches the co-finite branch:
   `enum_comp` fires only on `Rex::Comp`, `Σ*`, or `Inter`/`Union` of
   co-finite parts (regex.rs:978-1005), while a bare `re.range` is matched
   by `enum_lang` first (regex.rs:1199). The query is the **finite** branch
   under negative polarity, and what it actually pins is that the companion
   causes no spurious Unsat under `Not` (`¬(disj ∧ fact)` is Sat at length
   2) — still a worthwhile guard, but not the co-finite one. The real
   co-finite no-companion guarantee is structural and is pinned by the
   unchanged unit test
   `symbolic_cofinite_atom_rewrites_to_negated_disjunction`. Adjudicated as
   a plan factual error (unambiguous intent = accurate comment; slice-28
   `332dc00c` / devkit-alignment-2 unsafe-claim precedent) and corrected in
   `1e05649b`; the assertion and its expected verdict are unchanged.

**Oracle dump-and-diff (base `8a6dc95b` vs fix `459d7a6e`):** fix side
**81 passed / 0 failed / 0 shinri-vs-z3 disagreements / 0 guard-bailouts**
across all 13 fuzz families (z3 4.16.0); base side 79/0/0/0. Per-iteration
diff (3685 base vs 3690 fix dump lines, src-hash-keyed, `--test-threads=1`
so the fixed LCG seeds make query text identical across branches):
**8 flips, ALL `unknown → decided`** — 7 `→ unsat` (`0589e304`,
`7027067c`, `746e3282`, `9073bbc3`, `91fdd091`, `d67cac5e`, `da88fe2a`)
and 1 `→ sat` (`2ad53bcc`); `bail=0` on both sides of every flip. Zero
`decided → unknown`, zero `sat ↔ unsat`, zero bailout increases — §3's
empirical verdict-monotonicity gate satisfied. The 5 fix-only hashes
(0 base-only) are Task 2's new pin queries, which have no baseline
counterpart.

**Full gate at `459d7a6e`:** `shinri-str` 200/200; oracle differential as
above; `script_e2e` 67/67 (no pin flips — nothing to adjudicate);
`cargo clippy --workspace --all-targets -- -D warnings` 0 warnings;
`cargo fmt --check` clean.

**Final whole-branch review:** READY TO MERGE — 0 Critical, 0 Important,
3 Minor. The reviewer re-derived §3's soundness argument from the code
rather than the doc comment, confirming both premises it rests on: every
word reaching `conjoin_len_fact` is an in-alphabet non-surrogate Rust
`char` sequence (the split `enum_lang` / `lit_to_rex` fences), and the
solver counts `str.len` of a constant as `chars().count()` everywhere
(length.rs:58, shinri-solver/src/lib.rs:1089), so the companion cannot
disagree with the length theory about what a length is. It also sharpened
§2's cap rationale: because `(⋁ len(t)=ℓⱼ)` is entailed by `(⋁ t=wᵢ)`
alone, `disj ∧ fact ≡ disj`, so skipping above the cap is not merely
weakening but exactly equivalence-preserving at both polarities. Named
cross-cutting risk checked and not materialized: the finite branch's shape
change from bare `Or` to `And` breaks no downstream consumer — all recurse
generically over `App` with no top-level shape assumption. Minor 1 fixed
in `1e05649b` (deviation 4 above); Minor 2 (fence attribution) fixed in
the same commit; Minor 3 (the negative-polarity guard is a non-regression
pin — `¬(s ∈ [0-9]) ∧ s = "3"` was already Unsat pre-slice-29 via `¬disj`
alone, so the companion is not load-bearing there) needs no action, noted
so it is not mistaken for evidence that the companion works under `Not`.
Two Minors carried from the Task-1 review were triaged **defer**: the
untested exact-cap boundary (4 distinct lengths) cannot produce a wrong
verdict in either direction — firing at 5 is sound and skipping at 4 is
equivalent — so it is a completeness-tuning risk only; and the
same-length-collapse path is in fact already covered by
`symbolic_finite_atom_rewrites_to_eq_disjunction` (`{"a","b"}` → bare
`(= (str.len s) 1)`, no `Or`) and at scale by the headline
`_now_decides` pin (10 words → 1 length).

**Newly banked:** nothing new. Standing bank unchanged: hand-written wide
equality disjunctions / approach C (fuel-free constant-length
propagation), distinct-length sets > `LEN_FACT_DISTINCT_CAP`, co-finite
memberships, slice-28 §8 (conflict-core minimization, cross-term/
eq-class-aware aggregation, cap-raising), and the slice-27
typed-antecedent refactor.
