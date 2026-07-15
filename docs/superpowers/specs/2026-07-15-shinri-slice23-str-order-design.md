# Slice 23 design — `str.<` / `str.<=` lexicographic ordering

Date: 2026-07-15
Status: DESIGN (not yet implemented).

Predecessor: slice 22 (`str.to_code` inequality atoms via a character-range
gadget, landed 2026-07-14). Slice 22's non-goals bank `str.<` / `str.<=`
lexicographic ordering as "still unparsed; separate slice." This slice cashes
that item.

It is a **pure rewrite slice**, in the shape of slices 20 and 22: every rule
is a full equivalence, there are no fresh variables, no model repair, no
polarity tracking, and **zero changes to the word-equation engine, the regex
core, the arith seam, `Fuel`, or the SAT budgets**.

## Goal

Parse and decide the tractable fragment of the SMT-LIB lexicographic string
predicates

```
(str.<  s t)      strict lexicographic order over code points
(str.<= s t)      reflexive closure: s < t ∨ s = t
```

Today `(str.< a b)` is rejected at parse time as `unknown operator str.<`
(`crates/shinri-parser/src/parser.rs:686`) — the head appears nowhere in
`Parser::builtin_for` (`parser.rs:274`), there is no `StrLt`/`StrLeq`
`BuiltinOp`, and no ordering machinery exists anywhere in the tree.

**Decided fragment (this slice):** literal–literal comparisons (complete),
empty-string boundary idioms, and syntactic reflexivity — all by
equivalence-preserving rewrite. **Fenced (sound Unknown):** every genuinely
symbolic comparison that is not one of those idioms (e.g. two free string
variables of general length). **Banked:** full symbolic lexicographic
decision, and single-character/leading-code-point comparison (see §6).

Lexicographic order here is over the Unicode code-point alphabet, per the
SMT-LIB Unicode strings theory: `s < t` iff `s` is a proper prefix of `t`, or
at the first position where they differ `s`'s code point is strictly less than
`t`'s. `str.<=` is `str.< ∨ =`.

## 1. Surface wiring (net-new operators)

- **`crates/shinri-core/src/term.rs:90-92`** — add `BuiltinOp::StrLt` and
  `BuiltinOp::StrLeq` alongside the existing binary string predicates
  (`StrPrefixOf` / `StrSuffixOf` / `StrContains`).
- **`crates/shinri-parser/src/parser.rs:~326`** — two arms in `builtin_for`:
  `"str.<" => StrLt`, `"str.<=" => StrLeq`.
- **`crates/shinri-parser/src/print.rs:~193`** — two print arms (`StrLt =>
  "str.<"`, `StrLeq => "str.<="`); the `BuiltinOp` match is exhaustive, so this
  is required to compile.
- **`crates/shinri-core/src/context.rs:512-517`** — extend the String×String→Bool
  sort arm (currently `StrPrefixOf | StrSuffixOf | StrContains`) to include
  `StrLt | StrLeq`: arity 2, both args `string_sort()`, result `bool_sort()`.
- **New module `crates/shinri-str/src/order.rs`**, exported from
  `shinri-str/src/lib.rs`, wired into the solver's string pipeline in
  `crates/shinri-solver/src/lib.rs` at the `code_conv` seam (`lib.rs:~471`):
  `order::rewrite_str_order` followed by an `order::has_unreduced_str_order`
  fence, running before `predicates::rewrite_str_predicates` and
  `reduce::reduce_assertions` (`lib.rs:~505-506`).

## 2. Decision mechanism

A single bottom-up, memoized rewrite pass (`rewrite_str_order`, modeled on
`code_conv::rewrite_code_conv` and `predicates::fold_str_predicates`) matches
these arms on `StrLt`/`StrLeq` applications. **Every arm is a full
equivalence**, so it fires at any polarity and any nesting depth (bottom-up +
memoized handles negation and nesting for free):

**a. Literal–literal fold** (both args string constants) → Bool constant:

- `(str.<  "a" "b")` → `true`   |  `(str.<  "b" "a")` → `false`
- `(str.<= "a" "a")` → `true`   |  `(str.<= "b" "a")` → `false`

Computed with Rust's `&str` `<` / `<=` (see §3 for why this is exactly
SMT-LIB code-point order). Complete for the ground fragment.

**b. Empty-string boundaries** (one arg is the empty-string literal `""`):

- `(str.<= "" s)` → `true`            (empty ≤ everything)
- `(str.<  s "")` → `false`           (nothing is strictly < empty)
- `(str.<= s "")` → `(= s "")`        (s ≤ "" iff s = "")
- `(str.<  "" s)` → `(not (= s ""))`  ("" < s iff s ≠ "")

The last two emit a word (dis)equation over `s` — already owned by the
word-equation engine (`wordeq.rs`) — so they decide without new machinery.
When *both* args are `""`, arm (a) fires first (`(str.< "" "")` → `false`,
`(str.<= "" "")` → `true`).

**c. Reflexivity** (the two args are the *same* hash-consed `TermId`, hence
syntactically identical):

- `(str.<= s s)` → `true`
- `(str.<  s s)` → `false`

Distinct `TermId`s that happen to be semantically equal are **not** caught
here — they fall through to the fence (sound: Unknown, never wrong).

**No polarity fence.** Unlike slice 12's predicate rewrite — whose existential
concat decomposition is only equisatisfiable for *positive* occurrences, hence
its `has_unrewritable_str_predicate` polarity fence — every arm above is a
two-way equivalence. So this slice needs no polarity tracking; it is a pure
rewrite in the slice-20/22 mold.

**The fence.** After the pass, `has_unreduced_str_order` scans for any
surviving `StrLt`/`StrLeq` application. If one remains — a symbolic comparison
that matched no arm above — the query fences to `SolveOutcome::Unknown`,
mirroring `has_unreduced_code_conv` (`code_conv.rs`, wired `lib.rs:473`). Sound
by construction: the fence only ever weakens a would-be answer to Unknown.

## 3. Soundness

**Folding is exactly code-point order.** UTF-8 is a code-point-order-preserving
encoding: for valid UTF-8, byte-wise lexicographic comparison equals
code-point-wise lexicographic comparison. Rust's `Ord for str` is byte-wise, so
Rust `s < t` / `s <= t` on `&str` coincides with SMT-LIB `str.<` / `str.<=`.
This is the same soundness argument slice 12's module header
(`predicates.rs:13-16`) already makes for `starts_with`/`ends_with`/`contains`.

**Every rewrite arm is a two-way equivalence**, so the pass preserves
satisfiability of the whole formula regardless of the polarity or context of
the atom:

- (a) folds a closed Boolean fact.
- (b) `s ≤ ""  ⟺  s = ""` and `"" < s  ⟺  s ≠ ""` are theorems of the
  lexicographic order; `"" ≤ s` and `¬(s < "")` are valid.
- (c) `s ≤ s` is valid and `s < s` is unsatisfiable (irreflexivity of `<`).

The fence only replaces a decided verdict with Unknown, never flips one.
Therefore the slice is sound: it never returns a wrong Sat/Unsat.

## 4. Non-goals justification — why the hard core is banked

Full symbolic `str.<`/`str.<=` between two free variables requires deciding, at
the first position where `s` and `t` differ, that `s`'s code point is smaller —
an **existential over the split point**: `∃ p, a, b, s', t'. s = p·a·s' ∧
t = p·b·t' ∧ code(a) < code(b)`, disjoined with the proper-prefix case
`s = p ∧ t = p·b·t'`. That is a disjunctive, fresh-variable decomposition fed
into the word-equation engine, interacting with `Fuel` and model repair —
squarely against this slice's standing non-goal of touching the word-equation
engine, and realistically more than one slice of work. Banking it keeps
slice 23 a tight, sound, pure-rewrite slice consistent with slices 19–22.

## 5. Testing

**Differential oracle** (house cadence): a new family
`qfs_str_order_matches_z3` on a fresh seed, generating random conjunctions of
`str.<` / `str.<=` atoms — a mix of literal–literal, empty-string boundary,
and free-variable comparisons — checked against the z3 CLI. Expectation: a
tolerated slice of shinri-unknowns (precisely the fenced free-variable
comparisons), **0 disagreements**. As with slice 22, non-ASCII string
*literals* are not byte-comparable between shinri and the z3 CLI (a pre-existing
z3-CLI artifact, not an ordering-semantics disagreement); the generator stays on
ASCII literals to sidestep it.

The existing string/regex oracle families (`qfs_regex_ground`,
`qfs_regex_symbolic`, `qfs_regex_unfold`, `qfs_to_code_range`, and any existing
string-predicate families) re-run with tallies expected **unchanged** — this
slice adds a new operator and touches no existing path. Any movement is a
finding to adjudicate, not to wave through.

**e2e pins** (`qfs_differential.rs` / `script_e2e.rs`), one per route so a
future change that silently reroutes them trips a test:

- **Fold**: `(str.< "a" "b")` sat; `(str.< "b" "a")` unsat; `(str.<= "a" "a")`
  sat — ground comparisons decided.
- **Boundary — decided**: `(str.<= "" s)` sat; `(str.< s "")` unsat;
  `(str.<= s "") ∧ (= s "x")` unsat, while `(str.<= s "") ∧ (= s "")` sat;
  `(str.< "" s) ∧ (= s "")` unsat (the `s ≠ ""` rewrite bites).
- **Reflexivity**: `(str.< s s)` unsat; `(str.<= s s)` sat.
- **Fenced — KNOWN GAP**: a free-variable comparison `(str.< s t)` over two
  distinct symbolic strings pinned at sound `Unknown` (z3: Sat) with a
  `KNOWN GAP` comment naming §4's banked existential-split decision, so the
  future symbolic-decision slice flips this pin when it lands.

## 6. Non-goals (banked)

- **Full symbolic lexicographic decision** — the existential first-differing-
  position split (§4). The natural next slice; explicitly requires
  word-equation-engine work.
- **Single-character / leading-code-point comparison** — e.g.
  `(str.< s "b")` → `s = "" ∨ first-char(s) < 'b'`. Reducible via the slice-22
  `to_code` range gadget, but pulls in `str.at` / `str.substr`; banked to keep
  this slice tight. A candidate follow-up before the full existential split.
- **`str.<` / `str.<=` chained/n-ary forms**, if the frontend ever admits
  them — binary only, matching the existing predicate arms.
- Any change to the word-equation engine, the regex core, the arith seam,
  `Fuel`, or the SAT budgets.
