# Slice 22 design — `str.to_code` inequality atoms via a character-range gadget

Date: 2026-07-14
Status: IMPLEMENTED (slice 22 landed 2026-07-14).

Oracle (new family, fresh seed `0x53_00_0000_0002`):
`qfs_to_code_range_matches_z3: 200 iters — 28 sat / 105 unsat / 67
shinri-unknown (tolerated) / 0 z3-unknown / 0 guard-bailout (tolerated);
26 witnesses; 0 disagreements`. The three pre-existing regex families
(`qfs_regex_ground_matches_z3`, `qfs_regex_symbolic_matches_z3`,
`qfs_regex_unfold_matches_z3`) are **UNCHANGED** — bit-for-bit identical
to their slice-21 close values: ground `71 sat / 113 unsat / 16
shinri-unknown / 36 witnesses`; symbolic `113 sat / 76 unsat / 11
shinri-unknown / 108 witnesses`; unfold `95 sat / 88 unsat / 17
shinri-unknown / 93 witnesses`. All 11 differential families in the
same run: **0 disagreements**. The 67 shinri-unknowns in the new family
are fully accounted for: an independent replay of the generator's LCG
proved they are *exactly* the 67 of 200 iterations that draw a single,
un-fused `to_code` bound — i.e. precisely the instances that hit the
wide-arm known gap below (§1.4). Nothing new leaks into Unknown from
the 133 multi-bound draws.

**Deviations from the spec.**
Implementation surfaced two major spec corrections (the headline §1.4
routing claim and the §4 split-bounds mechanism), a plan-shape
deviation (the gadget is a second pass, not new arms on pass 1), a
completeness closure not anticipated by the plan (the gadget recurses
into its own output), an additional known gap (a `str.len` pin does not
rescue a fused range), and a testing-only constraint (non-ASCII string
literals are not comparable between shinri and the z3 CLI). Full traces
live in the task reports (`.superpowers/sdd/task-{1..4}-report.md`,
including the fix rounds appended to Tasks 2 and 3) and the
`## Deviations from the spec` section below.

Predecessor: slice 21 (derivative unfolding of symbolic `str.in_re` in the
string engine, landed 2026-07-14). This slice cashes the item banked since
**slice 18** and named by slice 21's non-goals as "the natural slice 22":
inequality atoms over `str.to_code` — character-range constraints — which
were banked *precisely* because they are not expressible as word equations
without a range gadget, and the range machinery did not exist until
slices 19–21 built it (`Rex`, `re.range` construction, class partitioning,
first-class membership atoms at both polarities).

It is a **pure rewrite slice**, in the shape of slice 20: every rule is a
full equivalence, there are no fresh variables, no model repair, no polarity
tracking, and **zero changes to the string engine, the regex core, the arith
seam, `Fuel`, or the SAT budgets**.

## Goal

Decide, at any polarity and any nesting depth, atoms of the form

```
(⋈ (str.to_code s) k)      ⋈ ∈ {>=, >, <=, <}, either orientation
```

where `s` is **any** String-sorted term and `k` is an Int constant — by
rewriting them into `str.in_re` memberships over constant character ranges,
which slices 19–21 already own.

**As-landed:** the rewrite itself is delivered exactly as designed — every
constant-RHS `to_code` inequality, at any polarity and nesting depth, becomes
a range membership, soundly, with no exceptions. But "decide" oversells the
downstream outcome for one idiom this Goal implies is central. The flagship
**fused, narrow** idiom genuinely decides: `48 ≤ to_code(s) ≤ 57` routes
through slice-20 enumeration and produces a real `get-value` witness. The
**lone, wide** bound over a free string variable — `(>= (str.to_code s) 48)`,
the slice's own canary idiom — does **not** decide: it builds
`Range(48, MAX_CODE)` and returns sound `Unknown` (z3: Sat). This is a
pre-existing slice-21 gap in the regex engine, not a defect in this slice's
rewrite (see §1.4's as-landed annotation and the Deviations section below).

Today these atoms are a documented sound-Unknown hole: `rewrite_code_conv`
(`crates/shinri-str/src/code_conv.rs:77`) dispatches only on `Eq` (via
`try_code_atom`, `code_conv.rs:222`) and has no arm for `Le`/`Lt`/`Ge`/`Gt`.
The `StrToCode` application survives, the presence fence
`has_unreduced_code_conv` (`code_conv.rs:313`) sees it, and the solver returns
`Unknown` (`crates/shinri-solver/src/lib.rs:474`). The hole is pinned by
`targeted_code_conv_fences_unknown`
(`crates/shinri-solver/tests/qfs_differential.rs:2641`), whose inequality
case (`:2681`) is the flip-marker this slice cashes.

## Deviations from the spec

1. **★ §1.4's routing claim is FALSE — the headline deviation.** §1.4 claims
   a wide fused range "declines enumeration and reaches slice 21's
   derivative engine as a single character class, which is exactly what its
   class partitioning was built for." It does not: `(>= (str.to_code s) 48)`
   over a free string variable — this slice's own canary idiom, the very
   atom `targeted_code_conv_fences_unknown`'s deleted case was meant to flip
   — builds `Range(48, MAX_CODE)` and returns **Unknown** (z3: Sat). This is
   a **pre-existing slice-21 gap, not a slice-22 defect**: a hand-written
   `str.in_re` over an equally wide range, with zero `to_code` in the
   formula, is equally Unknown, and the `ENUM_WORD_CAP = 256` cliff
   reproduces exactly (200 words → Sat; 300 words → Unknown; 977 words →
   Unknown) — matching a pin that already existed before slice 22
   (`in_re_unfold_slice20_allchar_stays_unknown`, `script_e2e.rs`). The
   **rewrite itself is correct** — sound but incomplete, never a wrong
   verdict: grounding the same wide range decides correctly in every
   direction, z3-agreeing (`s = "0"` → sat; `s = "!"` → unsat; `s = "ab"` →
   unsat, the `-1` escape correctly killed by the lower bound; `(>= tc 0) ∧
   s = ""` → unsat). The operative condition for the gap is **"no pinned
   length,"** not "over the word cap": `memb_seeds`' capped word search
   under an already-pinned length is a third closure route, and it closes
   over-cap ranges fine (`(>= tc 48) ∧ (<= tc 1000) ∧ (= (str.len s) 1)` →
   sat, at 953 words). But `Range(48, MAX_CODE)` spans the surrogate block,
   so `range_term` emits an `re.union`/`re.diff` composite rather than a
   bare `Rex::Range` leaf, and `memb_seeds` only engages bare-leaf shapes —
   so even a pinned length does not rescue *this* range. Consequence for the
   Goal and §5: the flagship **fused, narrow** idiom (the digit range) DOES
   decide — genuinely enumerated by slice 20, with a real `get-value`
   witness — but the **lone wide bound** does not. Task 1's deletion of the
   inequality case from `targeted_code_conv_fences_unknown` passed
   **vacuously**: the atom is no longer fenced by `has_unreduced_code_conv`
   (the rewrite works), but the query is still Unknown — now from the regex
   engine instead of the presence fence. Re-pinned as
   `targeted_to_code_range_wide_arm_known_gap`. See §1.4, the Goal section,
   and §5 for the inline annotations. (Task 3 report + fix report;
   `progress.md` D1/(w1)-(w3).)
2. **§4's split-bounds mechanism is UNCONFIRMED, not vindicated.** §4 claims
   that with bounds split across a disjunction, "two memberships land on `s`
   and the slice-21 intersection gap yields sound Unknown." The query IS
   Unknown, but the stated mechanism cannot be isolated by that test: two
   memberships on one variable do not by themselves trigger an intersection
   gap (`(str.in_re s (re.range "0" "9")) ∧ (or (str.in_re s (re.range "5"
   "z")) p)` → Sat), and both halves of the pinned query are independently
   Unknown (`>= 48` alone → Unknown; `<= 57` alone → Unknown) — so the
   observed Unknown is fully explained by the wide-arm gap (item 1) on the
   un-fused half. The pin is right; the explanation was wrong. Demoted to
   an unconfirmed hypothesis in `targeted_to_code_range_split_bounds_known_gap`'s
   comment. (Task 3 fix report, Finding 4.)
3. **The gadget is a second pass, not new arms on the existing pass.** §2
   says "`rewrite`'s `special` match gains arms for `Op::Builtin(Le | Lt |
   Ge | Gt)`, mirroring the existing `Eq → try_code_atom` arm." What landed
   is a separate, memoized pass-2 traversal (`gadget`, `code_conv.rs:610`)
   running after the slice-18 pass, so it only ever sees genuinely symbolic
   `to_code` applications. Equivalent in effect (bottom-up + memoized still
   handles nesting/negation for free); different in shape. (Task 1 report.)
4. **`gadget` recurses into the term it produces on a match** — not in the
   original plan. `Some(r) => gadget(ctx, r, memo)` (`code_conv.rs:628`):
   without it, a `to_code` inequality nested inside the **string argument**
   of another one (reachable via a String-sorted `ite` whose condition holds
   one) was left un-canonicalized and fenced to Unknown. With it, such
   queries decide. This is an Unknown→decisive transition, pinned by
   `gadget_recurses_into_a_nested_to_code_inside_the_matched_string_arg`
   (verified to fail if the recursion is reverted — Task 2 fix report,
   Finding 1). This adjudication ("A2") also means `elim_term_ite` — which
   runs *after* `code_conv` in the pipeline (`lib.rs:471` vs `:506`) —
   never lifts these memberships before they reach the regex stage: a new
   pipeline surface, flagged for the whole-branch review but not owned by
   this slice. (`progress.md`, Task 2 log, w1.)
5. **Fusion does not flatten.** It is per-syntactic-conjunction: one `And`
   node's direct children, or the top-level list. A nested `And`, a bound
   split across conjunction levels, and a double negation each escape
   fusion and yield two memberships on the same string term → sound
   Unknown. Not stated explicitly in §1.3/§1.4 as originally written; now
   documented directly in `fuse_bounds`'s doc comment. (Task 2 fix report,
   Finding 2.)
6. **A `str.len` pin does not rescue a fused range** — a gap not predicted
   by §4. `(>= tc 48) ∧ (<= tc 57) ∧ (= (str.len s) 2)` is Unknown (z3:
   unsat); a `to_code`-free control (`(str.in_re s (re.range "0" "9")) ∧
   (str.len s) = 2`) shows the identical gap, so it is a pre-existing
   slice-20/21 enumeration↔length seam issue, not a `to_code` artifact.
   Pinned as `targeted_to_code_range_length_seam_known_gap`. (Task 3 fix
   report, Finding 3.)
7. **Differential-oracle divergence on non-ASCII literals — a testing
   constraint, not a bug.** The z3 CLI parses a raw, non-escaped multi-byte
   UTF-8 string literal **byte-wise** (`(str.len "<raw U+D7FF>")` reads back
   as 3 in z3, not 1); shinri decodes it as one Rust `char`. Conversely
   shinri's parser does not decode `\u{...}` escapes (documented in
   `code_conv.rs`'s module header). So non-ASCII string **literals** are not
   comparable between the two engines in either form. `str.from_code`
   sidesteps it — no literal is involved, both engines agree — and the
   surrogate-boundary pins were rewritten onto it, now carrying a genuine
   z3 cross-check (`(= s (str.from_code 55295)) ∧ (>= tc 55296)` → both
   unsat; `(= s (str.from_code 57344)) ∧ (>= tc 55296)` → both sat: shinri
   is correct that `0xD800` is a genuine expressible endpoint). Worth
   carrying forward so the next slice does not rediscover it. (Task 3
   report + fix report, D2/Finding 1.)
8. **Unit tests use a distinct string variable per atom** in
   `canonicalization_table` and `degenerate_thresholds_fold_to_constants`
   (`code_conv.rs`), where they pin the per-atom canonicalization table
   (§1.1) and degenerate folds (§1.2) — not stated in §5's testing plan as
   written. Fusion (§1.3) groups bounds by string term, so a shared variable
   across the brief's original multi-bound lists would collapse each list
   into one fused result and lose the per-atom assertions the tests are
   meant to pin. Per-atom variables (`s_gt`/`s_lt`/`s_le`,
   `s_taut`/`s_unsat`/`s_neg_taut`/`s_neg_unsat`) keep each atom's intent
   exact and survive fusion unchanged. Purely a test-shape adjustment; no
   production-code or semantic consequence. (Pre-flight adjudication A1,
   `progress.md`.)

None of these deviations weaken soundness: every declined atom still leaves
its `StrToCode` application in place, the presence fence still catches it,
and every decided verdict cross-checks against z3 with zero disagreements
across all 11 differential families (200/200/200/200 iters where
applicable). What changed, in every case, is *how much* decides and *why* —
never whether a decided verdict can be wrong.

## 1. The calculus

`str.to_code` is **total**: it returns the code point of `s` when `|s| = 1`
and the sentinel `-1` otherwise. Its range is therefore
`{-1} ∪ [0, MAX_CODE]`, with `MAX_CODE = 0x2FFFF` (`code_conv.rs:30`,
`regex.rs:36` — the two agree).

That `-1` sentinel is the only thing that makes these atoms awkward, and it
collapses cleanly.

### 1.1 Canonicalization

Every matched atom reduces to a single **lower-bound threshold**, possibly
negated. `k` is recovered by `int_const_value`, exactly as `try_code_atom`
already does, and both orientations (`(>= (str.to_code s) k)` and
`(>= k (str.to_code s))`) map through the same table:

| atom | canonical | polarity |
| --- | --- | --- |
| `to_code(s) ≥ k` | `≥ k` | positive |
| `to_code(s) > k` | `≥ k+1` | positive |
| `to_code(s) ≤ k` | `≥ k+1` | **negated** |
| `to_code(s) < k` | `≥ k` | **negated** |

The strict/non-strict shifts are exact because `to_code` is Int-valued.

### 1.2 The master equivalence

For `0 ≤ k ≤ MAX_CODE`:

> **`to_code(s) ≥ k`  ⟺  `s ∈ Range(k, MAX_CODE)`**

with the two degenerate thresholds folding to constants:

- `k ≤ -1`  ⇒  `true`  (`to_code(s) ≥ -1` holds for every `s`)
- `k > MAX_CODE`  ⇒  `false`

A negated canonical atom wraps the membership in `not` — which needs no
special handling, because slice 21 made membership a first-class theory atom
at **both polarities**. A negated atom whose threshold is *degenerate* folds
to the negation of the constant above: a negated `k ≤ -1` is `false`, and a
negated `k > MAX_CODE` is `true`.

**Soundness.** Both directions follow from totality:

- (→) If `to_code(s) ≥ k ≥ 0`, then `to_code(s) ≠ -1`, so `|s| = 1` and its
  character *is* `to_code(s)`, which lies in `[k, MAX_CODE]`. Hence
  `s ∈ Range(k, MAX_CODE)`.
- (←) If `s ∈ Range(k, MAX_CODE)`, then `|s| = 1` and its character `c`
  satisfies `k ≤ c ≤ MAX_CODE`, so `to_code(s) = c ≥ k`.

`k = 0` is not a special case: `Range(0, MAX_CODE)` is exactly `re.allchar`,
the language of length-1 strings, and `to_code(s) ≥ 0 ⟺ |s| = 1`. The
formula is uniform across the whole in-alphabet range.

So **every** constant-RHS `to_code` inequality becomes a *single* range
membership — no disjunctions, no length side-conditions, no fresh variables.

### 1.3 Fusion — and why it is load-bearing

The flagship idiom for a character-range gadget is a **two-sided** bound:
`48 ≤ to_code(s) ≤ 57` ("is a digit"), `97 ≤ to_code(s) ≤ 122` ("is
lowercase"). Rewritten atom-by-atom, that yields **two membership atoms over
the same string term**:

```
s ∈ Range(48, MAX)  ∧  ¬(s ∈ Range(58, MAX))
```

which is precisely slice 21's pinned **intersection gap** — refuting or
realising two membership literals jointly requires a conflict rule citing
both, and the single-guard `TCheck::Split` channel cannot express one. Left
unfused, the headline use case of this slice would return `Unknown`.

The gadget therefore **fuses the bounds before they reach the engine**.
Fusion is a sound, polarity-free, purely syntactic equivalence.

At each conjunction — every `And` node, plus the top-level assertion list,
which is an implicit conjunction — group the canonical thresholds by string
term `s`. Write `P` for the positive thresholds on `s` and `N` for the
negated ones (degenerate thresholds having already folded to constants per
§1.2):

- **`P ≠ ∅`.** The lower bound `lo = max(P) ≥ 0` forces `len(s) = 1`, which
  kills the `-1` escape and turns every upper bound into a clean interval
  cap. Emit one membership `s ∈ Range(lo, hi)`, where `hi = min(N) - 1` if
  `N ≠ ∅` and `MAX_CODE` otherwise. If `lo > hi`, emit `false`.
- **`P = ∅`.** Upper bounds only, so the `len ≠ 1` escape survives and the
  constraint is genuinely a complement. Emit one negated membership
  `¬(s ∈ Range(min(N), MAX_CODE))`.

The algebra is just monotonicity of `≥`: several lower bounds meet to their
maximum (`≥a ∧ ≥b ⟺ ≥ max(a,b)`), several upper bounds to their minimum
(`¬(≥a) ∧ ¬(≥b) ⟺ ¬(≥ min(a,b))`), and a lower bound against an upper bound
gives the interval (`≥lo ∧ ¬(≥m) ⟺ len = 1 ∧ code ∈ [lo, m-1]`).

**The invariant that matters:** at most **one** membership atom per string
term per conjunction. The slice-21 intersection gap is never reached.

`Or` nodes are deliberately **not** fused. A disjunction of memberships is
harmless — SAT selects a branch, so only one membership is ever asserted on
`s` — and union-fusion would be YAGNI.

### 1.4 Downstream routing (why fusion pays twice)

`rewrite_code_conv` already runs immediately before the regex passes
(`lib.rs:470` → `lib.rs:483`), so the memberships it emits flow straight into
the slice-19/20/21 machinery with no re-ordering. The fused range then takes
whichever route fits it, and both routes are good:

- A **narrow** range — `Range(48, 57)` is 10 words, well under
  `ENUM_WORD_CAP = 256` (`regex.rs:523`) — is enumerated by slice 20's
  finite rewrite into `⋁ s = "0" … "9"`: plain word equations, on the
  most battle-tested path in the string solver.
- A **wide** range — `Range(97, MAX_CODE)` is ~196k words, far over the cap —
  declines enumeration and reaches slice 21's derivative engine as a
  **single character class**, which is exactly what its class partitioning
  was built for.

  **As-landed: this claim is FALSE.** A lone `to_code` bound over a free
  string variable — `(>= (str.to_code s) 48)`, this slice's own canary idiom,
  the very atom `targeted_code_conv_fences_unknown`'s deleted case was meant
  to flip — builds exactly this wide range and returns **Unknown** (z3:
  Sat), not Sat. This is a **pre-existing slice-21 gap**, not a slice-22
  defect: slice 21's membership engine only closes a language via (a) the
  trivial nullable/empty-string default, (b) capped enumeration under
  `ENUM_WORD_CAP` (256 words — irrelevant here, this route is for narrow
  ranges), or (c) `memb_seeds`' capped word search under an
  *already-pinned length* — and none of the three applies to a bare wide
  range over a free variable with no length pin. The gap is decisive, not
  speculative: a hand-written `str.in_re` over an equally wide range, with
  **zero `to_code` in the formula**, is equally Unknown, and the
  `ENUM_WORD_CAP` cliff reproduces exactly (200 words → Sat, 300 words →
  Unknown, 977 words → Unknown). The tree already carried a pin documenting
  this class of gap before slice 22 existed
  (`in_re_unfold_slice20_allchar_stays_unknown`, `script_e2e.rs`). The
  operative condition is **"no pinned length,"** not "over the word cap":
  `(>= tc 48) ∧ (<= tc 1000) ∧ (= (str.len s) 1)` decides **Sat** at 953
  words — far over the cap — via route (c) above. But `Range(48, MAX_CODE)`
  specifically spans the surrogate block, so `range_term` emits an
  `re.union`/`re.diff` **composite** rather than a bare `Rex::Range` leaf,
  and `memb_seeds` only engages bare-leaf shapes — so even a pinned length
  would not rescue *this* range. The rewrite itself is sound but incomplete,
  never a wrong verdict: grounding the same wide range decides correctly in
  every direction, z3-agreeing (`s = "0"` → sat, `s = "!"` → unsat, `s =
  "ab"` → unsat — the `-1` escape correctly killed by the lower bound,
  `(>= tc 0) ∧ s = ""` → unsat). Pinned as
  `targeted_to_code_range_wide_arm_known_gap`
  (`qfs_differential.rs`). See the Deviations section for the full account.

## 2. Architecture

All of it lands in `crates/shinri-str/src/code_conv.rs`, inside the existing
bottom-up memoized pass `rewrite_code_conv` (`code_conv.rs:77`). No new
module, no new fence, no engine change.

**Atom dispatch.** `rewrite`'s `special` match gains arms for
`Op::Builtin(Le | Lt | Ge | Gt)`, mirroring the existing `Eq → try_code_atom`
arm. Because the pass is a bottom-up DAG rewrite, nesting and negation are
handled for free — an atom buried under `not`/`or`/`ite` is rewritten exactly
like a top-level one.

**As-landed:** the gadget is a **second pass**, not new arms on pass 1. What
landed is a separate, memoized post-pass-1 traversal (`gadget`,
`code_conv.rs:610`), run by `rewrite_code_conv` (`code_conv.rs:84`) strictly
*after* the slice-18 fold, so it only ever sees genuinely symbolic `to_code`
applications — every foldable one is already gone by the time it runs.
Equivalent in effect (nesting and negation are still handled for free, by the
same bottom-up-memoized argument), different in shape. `gadget` also
**recurses into the term it produces on a match**
(`Some(r) => gadget(ctx, r, memo)`, `code_conv.rs:628`) — this was *not* in
the original plan and closes a real completeness gap: without it, a `to_code`
inequality nested inside the **string argument** of another one (reachable
via a String-sorted `ite` whose condition holds one) was left
un-canonicalized and fenced to Unknown. With it, such queries decide. This is
an Unknown → decisive transition, pinned by
`gadget_recurses_into_a_nested_to_code_inside_the_matched_string_arg`
(`code_conv.rs:1300`), independently verified to fail if the recursion is
reverted. Note `elim_term_ite` runs *after* `code_conv` in the pipeline
(`lib.rs:471` vs `:506`), so these memberships reach the regex stage
un-lifted — a new pipeline surface, flagged for the whole-branch review.

**Fusion placement.** One subtlety dictates the shape. `range_term`
(`regex.rs:350`) encodes a range that *spans the surrogate block* as a union
containing an `re.diff`, **not** as a bare `re.range` — and every range
reaching `MAX_CODE` spans the block, which is the common case. So fusion must
**not** be implemented by pattern-matching already-emitted membership terms;
it has to fuse *before* term construction.

Therefore the `And` arm scans its children for `to_code` inequality atoms
first, computes the fused interval per string term `s` (§1.3), and then
materializes **one** membership for each group, replacing the group's
remaining atoms with `true`. The top-level assertion list is treated as a
virtual `And` for the same purpose. Atoms that no fusion group claims — a
lone assertion, or an atom under an `Or` — materialize directly via the
master equivalence (§1.2).

String terms are keyed by `TermId`; the context is hash-consed, so identity
is the right grouping key and `s` may be any String-sorted term
(`(str.++ x y)`, a literal, a variable) — slice 21 accepts any of them on the
membership side.

**Term construction** reuses `rex_to_term` / `range_term`
(`regex.rs:393` / `:350`) verbatim, so the surrogate-block encoding is
inherited rather than reinvented. Both are `pub(crate)` within `shinri-str`,
so no visibility change is needed.

## 3. Fences

Every declined atom simply **leaves its `StrToCode` application in place**;
the existing presence fence `has_unreduced_code_conv` (`code_conv.rs:313`)
catches it and the solver returns sound `Unknown` (`lib.rs:474`). No new fence
machinery, and the house posture is preserved: never guess, never a wrong
verdict.

Three cases decline:

1. **Interior-surrogate thresholds.** `re.range` endpoints must be `Box<str>`
   literals, and a lone surrogate is not a valid Rust `str`. `range_term` can
   express the **full** surrogate block (its boundaries `D7FF`/`E000` are not
   surrogates, hence the `re.diff` trick) but *not* an endpoint inside it —
   its `debug_assert`s forbid interior-surrogate endpoints, and no `re.diff`
   workaround exists, since every alternative encoding needs another surrogate
   endpoint. So a canonical threshold `k ∈ [0xD801, 0xDFFF]` fences. This is a
   representational limit of the term layer, not an oversight, and it mirrors
   exactly the surrogate fence the **equality** rule already carries
   (`code_conv.rs:40`). Note `k = 0xD800` *is* expressible (`lo == SURR_LO`),
   so the check is a single range test on the canonicalized threshold.
2. **Nested arithmetic** — `(= (+ (str.to_code s) 1) 98)`,
   `(>= (+ (str.to_code s) 1) 98)`. Unchanged from slice 18; still a
   flip-marker.
3. **Symbolic linking** — `to_code(x) ⋈ to_code(y)`, or any symbolic Int side.
   The gadget structurally cannot apply: with no constant threshold there is
   no regex to build. Needs a char/code seam or a lazy propagator, as slice 18
   said.

## 4. Completeness limits (never soundness)

- **Bounds split across boolean structure.** Fusion sees a conjunction; it
  cannot see across one. Given `(assert (>= (str.to_code s) 48))` alongside
  `(assert (or (<= (str.to_code s) 57) p))`, if SAT selects the first
  disjunct then two memberships land on `s` and the slice-21 intersection gap
  yields sound `Unknown`. This is honest and pinned, not a bug: fusion is
  best-effort within a conjunction, and unfused residuals fall back on the
  engine.

  **As-landed: the query IS Unknown, but the stated mechanism is UNCONFIRMED,
  not vindicated.** Two memberships on one variable do **not** by themselves
  trigger an intersection gap: `(str.in_re s (re.range "0" "9")) ∧ (or
  (str.in_re s (re.range "5" "z")) p)` decides **Sat**. And both halves of
  the pinned split-bounds query are *independently* Unknown on their own
  (`>= 48` alone → Unknown; `<= 57` alone → Unknown), so the observed Unknown
  is fully explained by the wide-arm gap (above) on the un-fused half — the
  intersection gap is confounded in this construction and cannot be isolated
  by it. The pin (`targeted_to_code_range_split_bounds_known_gap`,
  `qfs_differential.rs`) is right; the explanation was wrong. The
  intersection-gap claim now lives in the test's comment as an explicitly
  unconfirmed hypothesis, not a demonstrated mechanism.
- **Wide fused ranges** reach the derivative engine, so they inherit its fuel
  and cap behaviour: a hard case may saturate to `Unknown`. Sound by the
  slice-21 posture.
- **As-landed, an additional gap found during e2e pinning:** a `str.len` pin
  does not rescue a fused range either. `(>= tc 48) ∧ (<= tc 57) ∧ (=
  (str.len s) 2)` is Unknown (z3: unsat), and a `to_code`-free control
  (`(str.in_re s (re.range "0" "9")) ∧ (= (str.len s) 2)`) shows the identical
  gap — a pre-existing slice-20/21 enumeration↔length seam issue, not a
  `to_code` artifact. Pinned as `targeted_to_code_range_length_seam_known_gap`
  (`qfs_differential.rs`).
- This slice **routes around** the intersection gap; it does not close it.
  Closing it (an intersection-aware conflict rule citing two membership
  literals) remains banked.

## 5. Testing

**Unit tests** (`code_conv.rs`):

- the canonicalization table (§1.1) — all four ops × both orientations;
- degenerate thresholds: `k ≤ -1` ⇒ `true`, `k > MAX_CODE` ⇒ `false`;
- `k = 0` ⟺ `len(s) = 1` (the `re.allchar` identity);
- the surrogate fence at all four boundaries — `0xD7FF` and `0xD800` express,
  `0xD801` and `0xDFFF` fence;
- the fusion algebra: two-sided ⇒ `Range(lo, hi)`; several lower bounds ⇒
  max; several upper bounds ⇒ min; crossed bounds ⇒ `false`; upper-only ⇒
  negated suffix range; fusion across *separate top-level assertions*.

**E2E pins** (`qfs_differential.rs`, `script_e2e.rs`):

- **The flip — as-landed.** `targeted_code_conv_fences_unknown`
  (`qfs_differential.rs:2641`) had its inequality case (`(>= (str.to_code s)
  48)` at `Unknown`, `:2681`) **deleted** rather than flipped to a decided
  pin. That deletion passed **vacuously**: the atom is no longer fenced by
  `has_unreduced_code_conv` (the rewrite genuinely fires — this much of the
  spec's prediction holds), but the query is *still* `Unknown` — now
  produced by the regex engine's wide-arm gap instead of the presence fence
  (see §1.4's as-landed annotation). It is now correctly re-pinned, at its
  true observed verdict, as `targeted_to_code_range_wide_arm_known_gap`. This
  atom is **not** the house canary idiom that decides; the genuinely decided
  flagship idiom is the **fused, narrow** range below. The nested-arith case
  (`:2673`) stays pinned `Unknown`, unchanged.
- The digit idiom `48 ≤ to_code(s) ≤ 57`: sat with a get-value witness
  (`to_code_digit_range_get_value_witness`, `script_e2e.rs`); unsat when
  conjoined with `s = "x"`. **Confirmed as-landed** — this is the pin that
  actually demonstrates decided-ness end to end, and `get-value` reads back a
  concrete digit character (`((s "9"))`), which is strong evidence the
  narrow range genuinely routes through slice-20 enumeration into a word
  equation rather than the regex engine.
- One pin on **each** downstream route — a narrow fused range (slice-20
  enumeration, decides) and a wide one (slice-21 engine, **as-landed: does
  NOT decide** — see §1.4) — so a future change that silently reroutes them
  trips a test. `targeted_to_code_range_decided` covers the narrow route;
  `targeted_to_code_range_wide_arm_known_gap` covers the wide one, now
  correctly named for what it actually is (a known gap, not a decided case).
- A pin on the boolean-structure completeness limit (§4), at its sound
  observed verdict with a KNOWN GAP comment
  (`targeted_to_code_range_split_bounds_known_gap`) — as-landed, its doc
  comment now leads with the wide-arm explanation and demotes the
  intersection-gap claim to an unconfirmed hypothesis (see §4's as-landed
  annotation). A further gap found only during e2e pinning, not predicted by
  this section, is also pinned: `targeted_to_code_range_length_seam_known_gap`
  (a `str.len` pin does not rescue a fused range; see §4).

**Differential oracle**, per house cadence: a new family
`qfs_to_code_range_matches_z3` on a fresh seed, generating random
constant-RHS `to_code` inequality conjunctions over symbolic strings, checked
against z3.

The three existing regex families (`qfs_regex_ground`, `qfs_regex_symbolic`,
`qfs_regex_unfold`) re-run with tallies expected **unchanged** — this slice
only adds decided idioms and does not touch the regex path. Any movement is a
finding to adjudicate, not to wave through.

**As-landed, a testing-only constraint discovered during e2e pinning:** the
z3 CLI parses a raw, non-escaped multi-byte UTF-8 string literal
**byte-wise** (`(str.len "<raw U+D7FF>")` reads back as 3 in z3, not 1),
while shinri decodes it as one Rust `char`; conversely shinri's own parser
does not decode `\u{...}` escapes (documented in `code_conv.rs`'s module
header). So a non-ASCII string **literal**, in either form, is not
comparable between the two engines — this is a pre-existing z3-CLI artifact
unrelated to `to_code`/regex semantics, not a disagreement. The surrogate
boundary pins (`targeted_to_code_range_surrogate_fences_unknown`) were
rewritten onto `str.from_code`, which sidesteps it entirely — no literal is
involved, so both engines agree — and now carry a genuine z3 cross-check:
`(= s (str.from_code 55295)) ∧ (>= tc 55296)` → both unsat; `(= s
(str.from_code 57344)) ∧ (>= tc 55296)` → both sat, confirming shinri is
correct that `0xD800` is a genuine expressible endpoint. Worth carrying
forward so the next slice does not rediscover it.

## 6. Non-goals (banked)

- Nested-arithmetic shapes and symbolic linking (§3) — still flip-markers.
- `str.<` / `str.<=` lexicographic ordering — still unparsed; separate slice.
- Interior-surrogate thresholds — a representational limit of the term layer.
- Symbolic regex sides, RegLan variables, RegLan equality/containment.
- Slice 21's intersection and concat-context gaps — untouched (§4).
- **`str.is_digit` stays exactly as it is.** Its current expansion
  (`code_conv.rs:205`) is a 10-way disjunction of string equalities — which is
  byte-for-byte what the fused gadget would produce anyway, once slice 20
  enumerates `Range(48, 57)`. Rerouting it through the regex engine would be
  pure churn.
- Any change to the word-equation engine, the regex core, the arith seam,
  `Fuel`, or the SAT budgets.
