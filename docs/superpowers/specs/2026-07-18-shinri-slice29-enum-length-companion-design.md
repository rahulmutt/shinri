# Slice 29 design — enumeration↔length seam: exact-length companion

Date: 2026-07-18
Status: APPROVED (design), not yet implemented.

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
