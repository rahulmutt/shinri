# Slice 24 design — single-character `str.<` / `str.<=` vs. a constant

Date: 2026-07-16
Status: DESIGN (not yet implemented).

Predecessor: slice 23 (`str.<` / `str.<=` literal–literal folds, empty-string
boundaries, and syntactic reflexivity, landed 2026-07-15). Slice 23's non-goals
(§6) bank **single-character / leading-code-point comparison** as "a candidate
follow-up before the full existential split." This slice cashes exactly that
item — and nothing more.

It is a **pure rewrite slice**, in the shape of slices 20, 22, and 23: every
rule is a full equivalence, there are no fresh variables, no model repair, no
polarity tracking, and **zero changes to the word-equation engine, the regex
core, the arith seam, `Fuel`, or the SAT budgets**. The operators, their parse
arms, their sort rule, and the `order.rs` pass + fence already exist (slice 23);
this slice adds *rewrite arms only*.

## Goal

Decide `(str.< a b)` / `(str.<= a b)` whenever **exactly one side is a length-1
string constant** and the other is a symbolic String term — at any polarity,
nesting, or occurrence count. Today every such atom is symbolic-not-an-idiom,
so slice 23's presence fence (`has_unreduced_str_order`) turns it into a sound
`Unknown`. This slice flips that fenced sub-fragment to *decided*.

Concretely, for a single character `c` (code point `m`) and symbolic `s`:

```
(str.<  s "c")   (str.<= s "c")     -- constant on the right
(str.<  "c" s)   (str.<= "c" s)     -- constant on the left
```

Everything outside this shape is untouched: literal–literal and empty-string
and reflexive atoms are already decided by slice 23; two symbolic sides, and a
**multi-character** constant, stay fenced (banked — see §5).

## Design premise — why a regex reduction, not `str.at`

Slice 23 §6 sketched this follow-up as "reducible via the slice-22 `to_code`
range gadget, but pulls in `str.at` / `str.substr`." That route is a **dead
end**: the solver's `str.at`/`str.substr` seam is fenced. `lib.rs:497-512`
returns `Unknown` for *any* `str.at`/`str.substr` over a non-constant base (the
documented `(str.at s 2) = s` spurious-UNSAT flaw), and it runs *before*
`reduce_assertions`. So a reduction phrased as `to_code(str.at s 0) < m` would
fence to `Unknown` and decide nothing.

The viable mechanism is a **pure regex reduction**: rewrite the comparison
directly to a `str.in_re s R` membership, where `R` is a constant regex built
from `c`. No `str.at`, no `to_code`, no fresh variables. This is sound and —
critically — *decided*: the minted membership is a constant-regex-over-symbolic-
string atom, exactly the engine-eligible shape slice 21's derivative unfolding
owns (`lib.rs:487-490`).

**Placement makes it free.** `order::rewrite_str_order` runs at `lib.rs:481`,
*immediately before* the regex passes (`rewrite_ground_in_re` / the
`has_unsupported_regex` fence, `lib.rs:493-496`, then slice 21's engine
downstream). A membership minted in `order.rs` flows straight into that
machinery with no new wiring. Because the atom is rewritten away, the
`StrLt`/`StrLeq` node is gone and `has_unreduced_str_order` (`lib.rs:482`) no
longer fences it.

### Empirical de-risking (pre-spec spike)

The slice's entire value rests on the engine *deciding* these memberships
rather than fencing. Confirmed against the built `shinri` CLI and cross-checked
against z3 4.16.0:

- `s ∈ (re.++ (re.range "a" "c") re.all)` — the `Range·Σ*` shape — decides
  **correctly** on `s="b"` (sat), `s="bxy"` (sat), `s="z"` (unsat), `s=""`
  (unsat), free `s` (sat), and negated `¬(…)` with `s="z"` (sat). All six agree
  with z3; none return `unknown`.
- The `Σ*` sits **rightmost** (a suffix), which sidesteps slice 21's known
  left-peel gap (`Σ*` on the *left* — `concat_context` in the slice-21 spec,
  "forward derivative unfolding left-peels unboundedly; needs reverse
  derivatives"). Forward derivatives peel the fixed prefix + the one range
  char, then reach `Σ*`, whose self-loop the engine already decides (slice 21:
  bare `re.allchar` / `re.all` over symbolic `s` is decided).

## 1. Surface wiring

**None net-new.** `BuiltinOp::StrLt` / `StrLeq`, their `builtin_for` parse arms,
their `print.rs` arms, the String×String→Bool sort rule, and the `order.rs`
module + pipeline seam + presence fence all landed in slice 23. This slice edits
`order.rs` only.

## 2. Decision mechanism

Two new arms in `order::try_order_atom`, placed **after** the existing
empty-string boundary arms (b) and **before** the `None` fall-through. Each arm
matches "one side is a length-1 string constant, the other is not a string
constant," extracts the char's code point `m`, builds a constant regex `R`, and
returns `str.in_re other R`. Everything the pass already does — bottom-up
memoized traversal, so any polarity / nesting is handled for free — is
unchanged.

Notation: `Σ = re.allchar = Range(0, MAX)`, `Σ* = re.all = star(Range(0, MAX))`,
`MAX = MAX_CODE = 0x2FFFF`, `word(c) = Range(m, m)` (a single-char literal is one
range class), `Eps = {ε}`. All are `shinri_str::regex::Rex` nodes built with the
existing `pub(crate)` constructors (`concat`, `union`, `star`, `Rex::Range`,
`Rex::Eps`) and lowered to a term with `rex_to_term`.

The four form-families (`other` is the symbolic side `s`):

| Atom | Membership language `s ∈ …` | Reading |
|------|------------------------------|---------|
| `s < c`  | `Eps ∪ Range(0, m-1)·Σ*` | empty, or first char `< m` |
| `s <= c` | `Eps ∪ Range(0, m-1)·Σ* ∪ word(c)` | `< c`, or `= c` |
| `c < s`  | `Range(m+1, MAX)·Σ* ∪ word(c)·Σ·Σ*` | first char `> m`, or `c` a **proper** prefix |
| `c <= s` | `Range(m+1, MAX)·Σ* ∪ word(c)·Σ*` | first char `> m`, or `c` a prefix (incl. `= c`) |

Each family is emitted as **one** `str.in_re s (union …)` term (one membership,
one regex), matching the shape verified in the spike.

**Degenerate endpoints fold out of the same formulas — no special cases:**

- `m = 0` (`c` is the null char, the least character): `Range(0, -1)` is the
  empty interval, so `s < c` collapses to `s ∈ Eps` ≡ `s = ""` and `s <= c`
  to `s ∈ Eps ∪ word(c)`.
- `m = MAX` (`c` is the greatest character): `Range(MAX+1, MAX)` is empty, so
  the `c < s` / `c <= s` languages drop their range branch, leaving only the
  proper-prefix / prefix branch.

The empty-interval fold is exactly slice-22 `range_membership`'s "`lo > hi ⇒
false`" rule; reusing that policy keeps it single-sourced (see §3).

## 3. Reuse & the surrogate boundary

The range branches reuse slice-22's endpoint *policy* rather than re-deriving
it. Because §2 emits one `str.in_re s (rex_to_term R)` per atom, the branches
must compose as `Rex` nodes — so the shared piece is a **`Rex`-level** helper
`range_rex(lo: i128, hi: i128) -> Option<Rex>`, extracted from the endpoint
check inside `code_conv::range_membership` (`code_conv.rs:416-429`) and called by
both slice 22 (wrapping its result in a term) and this slice (composing it into
the union). (`range_membership` itself returns a *term* — `str.in_re …` or the
Bool `false` — so it cannot be reused verbatim inside a single-`Rex` emission;
`range_rex` is the term-free core it and this slice share.) Its contract:

- `lo > hi` ⇒ `Some(Rex::Empty)` — the empty interval. It is built **before** any
  `Rex::Range(u32, u32)` construction, so the `m=0` case (`hi = m-1 = -1`) never
  constructs a `Range` with an out-of-range bound. `union`/`concat` then drop the
  `Empty` branch (`regex.rs:73,90`), collapsing the `m=0` / `m=MAX` folds of §2.
- an endpoint **strictly inside** the surrogate block (`0xD801..=0xDFFE` as a
  bound other than the block edges `0xD800` / `0xDFFF`) ⇒ `None`, whereupon the
  arm returns `None` so the atom survives to `has_unreduced_str_order` → sound
  `Unknown`.
- otherwise ⇒ `Some(Rex::Range(lo as u32, hi as u32))`.

**For a single-character `c` this fence provably never fires.** The parser
cannot produce a surrogate literal, so `m` is a valid non-surrogate code point.
The only endpoints this slice forms are `m-1` and `m+1`, and a lone
surrogate-*interior* endpoint would require `m ∈ {0xD802..0xDFFF}` (for `m-1`)
or `m ∈ {0xD800..0xDFFD}` (for `m+1`) — all of which are surrogates, so no valid
`m` reaches them. The block *edges* `0xD800` / `0xDFFF` (reachable via
`m = 0xD7FF` / `m = 0xE000`) are expressible ranges. The guard is retained for
uniformity and the sound-Unknown fallback, not because it is load-bearing here —
a fact worth a pinned test (§5).

## 4. Soundness

Each membership language is the exact set `{ s : s ⋈ c }` for its operator `⋈`,
by the lexicographic definition (slice 23 §on order: `s < t` iff `s` is a proper
prefix of `t`, or at the first differing position `s`'s code point is smaller):

- **`s < c`** (`c` length 1). If `s = ""`: `"" < c` (empty is a proper prefix of
  any nonempty word) — captured by `Eps`. If `s` nonempty with first char code
  `f`: `f < m` ⇒ they differ at position 0 with `s` smaller ⇒ `s < c` regardless
  of `s`'s tail — captured by `Range(0,m-1)·Σ*`. `f = m` ⇒ `c` (length 1) is a
  prefix of `s` ⇒ `c ≤ s` ⇒ `s < c` false. `f > m` ⇒ `s > c` ⇒ false. So the
  language is exactly `Eps ∪ Range(0,m-1)·Σ*`. ∎
- **`s <= c`** = `s < c ∨ s = c`; `s = c` is the singleton `word(c)`. ∎
- **`c < s`**. `c < s` iff at position 0 `c`'s char is smaller (`f > m`,
  `Range(m+1,MAX)·Σ*`) or `c` is a **proper** prefix of `s` (`s` starts with `c`
  and is strictly longer: `word(c)·Σ·Σ*`, the `Σ` forcing ≥1 further char). No
  other case yields `c < s`. ∎
- **`c <= s`** = `c < s ∨ c = s`; folding `c = s` (`s` is exactly `c`) into the
  proper-prefix branch turns `word(c)·Σ·Σ*` into `word(c)·Σ*` (`c` a prefix,
  possibly equal). ∎

Every arm is a two-way equivalence, so rewriting preserves satisfiability at any
polarity or context — the bottom-up memoized pass needs no polarity tracking
(same argument as slice 23 §3). The surrogate/empty guard only ever weakens a
verdict to Unknown. Therefore the slice never returns a wrong Sat/Unsat.

Downstream, the minted `str.in_re` is decided soundly by the existing regex
engine (Sat/Unsat always sound; fuel/cap exhaustion ⇒ sound Unknown, per the
slice-21 contract). This slice adds no new obligation to that engine.

## 5. Non-goals (banked)

- **Multi-character constant** (`(str.< s "bc")`). The same regex reduction
  generalizes — a `⋁` over prefix-agreement positions `k`,
  `⋁ₖ str.to_re(c[0:k])·Range(0, c[k]-1)·Σ*` plus the proper-prefix literals —
  but it multiplies the branch count (and thus fuel pressure) and reintroduces
  per-position surrogate/null-char endpoint fences. Banked to keep this slice
  length-1-tight; a clean follow-up on the identical machinery.
- **Full symbolic lexicographic decision** (two free string variables). Still
  the natural end state; still requires the existential first-differing-position
  split and word-equation-engine work (slice 23 §4). Untouched.
- **Chained / n-ary `str.<` / `str.<=`**, if the frontend ever admits them —
  binary only, matching the existing arms.
- Any change to the word-equation engine, the regex core, the arith seam,
  `Fuel`, or the SAT budgets.

## 6. Testing

**Unit tests (`order.rs`).** For each of the 8 forms (`<` / `<=` × constant-left
/ constant-right, with a symbolic partner), assert the rewrite produces the
exact expected membership term. As in slice 22/23 these compare `TermId`s
directly — sound because the `Context` is hash-consed and `rex_to_term` is
deterministic — building the `want` regex with the same constructors. Plus:
the `m=0` fold (`s < c` ⇒ `s = ""`), the `m=MAX` fold (range branch dropped),
and a `m=0xE000` / `m=0xD7FF` block-edge case pinned to *not* fence (the guard
is non-load-bearing here — pin it so a future change that breaks that reasoning
trips a test).

**Differential oracle** (house cadence, **`--features oracle`**, run
**foreground with captured output** — the z3 cross-check is this slice's real
acceptance gate, since everything hinges on the engine deciding the minted
memberships). A new family `qfs_str_order_single_char_matches_z3` on a fresh
seed, generating random conjunctions of single-char-vs-symbolic `str.<` /
`str.<=` atoms (both orientations), mixed with equality/length constraints on
the symbolic side to force both Sat and Unsat. Checked against the z3 CLI.
Expectation: **0 disagreements**, and — unlike slice 23 — a substantially
*lower* shinri-unknown tally than the pre-slice baseline, because this fragment
now decides. ASCII literals only (the pre-existing non-ASCII z3-CLI byte-compare
artifact, slice 22/23 §5).

The existing string/regex oracle families (`qfs_regex_ground`,
`qfs_regex_symbolic`, `qfs_regex_unfold`, `qfs_to_code_range`,
`qfs_str_order_matches_z3`) re-run with tallies expected **unchanged** — this
slice adds rewrite arms and touches no existing path. In particular
`qfs_str_order_matches_z3`'s fenced free-variable comparisons must stay fenced;
any movement is a finding to adjudicate, not to wave through.

**e2e pins** (`qfs_differential.rs` / `script_e2e.rs`), one per route so a future
change that silently reroutes them trips a test:

- **`< c`, right**: `(str.< s "b") ∧ (= s "a")` sat; `∧ (= s "b")` unsat;
  `∧ (= s "c")` unsat; `∧ (= s "")` sat.
- **`<= c`, right**: `(str.<= s "b") ∧ (= s "b")` sat.
- **`c <`, left**: `(str.< "b" s) ∧ (= s "c")` sat; `∧ (= s "ba")` sat
  (proper prefix); `∧ (= s "b")` unsat.
- **`c <=`, left**: `(str.<= "b" s) ∧ (= s "b")` sat.
- **degenerate**: `(str.< s "\u{0}")` decided as `s = ""` (via the built
  `Rex`, not a parsed escape — assert through the term API or a construction
  test, since the CLI text frontend does not decode `\u{...}`).
- **negation**: `(not (str.< s "b")) ∧ (= s "a")` unsat.
