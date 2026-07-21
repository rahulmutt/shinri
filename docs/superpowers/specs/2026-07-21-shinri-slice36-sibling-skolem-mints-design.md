# Slice 36 — sibling skolem-mint hardening (`!pfx`/`!sfx`/`!ctnl`/`!ctnr`, `!pre`/`!mid`/`!post`, `!ite`)

Date: 2026-07-21. Base: `3a8da692` (slice-35 merge).

## 1. Problem

The slice-35 final review banked this as an explicit future-slice
candidate (slice-35 §2): every skolem mint in `shinri-str` **other than**
`fresh_str` bare-`declare_fun`s its name with neither collision direction
handled — no lookup-skip, no `reserve_symbol`. The sites:

- `fresh_str_var` (`crates/shinri-str/src/predicates.rs:176-181`), minting
  `!pfx{n}` / `!sfx{n}` / `!ctnl{n}` / `!ctnr{n}` for the
  prefixof/suffixof/contains concat decompositions
  (`predicates.rs:218-237`);
- `encode_substr` (`crates/shinri-str/src/reduce.rs:218-220`), minting the
  `!pre{n}` / `!mid{n}` / `!post{n}` trio off a **single** draw of the
  global `FRESH_CTR` (`reduce.rs:64-71`);
- the non-Boolean ITE lift (`reduce.rs:437-438`), minting `!ite{n}` at an
  arbitrary sort.

Unlike `fresh_str` — whose mints run inside the theory Combiner's
**discarded context clone** (`crates/shinri-solver/src/lib.rs:711`) and
are therefore parser-invisible — these mints run on the **live**
`self.ctx`, pre-clone (`lib.rs:515-516`). That is exactly the
parser-visible position where hash-cons aliasing persists across
check-sats, so both collision directions are user-reachable:

- **Pre-mint**: a user `(declare-const !pfx0 String)` that predates the
  mint hash-conses with the decomposition skolem — the skolem *is* the
  user's term, and the decomposition equation silently constrains it.
- **Post-mint**: a later user `declare-fun` of a minted name inherits the
  skolem's internal identity — the wrong-verdict shape word_norm's
  slice-5 final review found for `ite!` and fixed with `reserve_symbol`
  (`word_norm.rs:99-117`). Worse, `Context::declare_fun` silently
  overwrites `fun_sigs` (`context.rs:166-170`), so even a
  **differently-sorted** user redeclaration is accepted.

Both are wrong-verdict shapes. This is the "more exposed sibling" of the
hazard slice 35 closed for `fresh_str`.

> **Plan-time correction (reachability).** The `reduce.rs` mint families
> are currently **solver-path-dead**: `encode_substr` fires only for
> *unfoldable* substr/at, but the substr soundness fence
> (`lib.rs:507-512`) returns `Unknown` for exactly those queries
> *before* `reduce_assertions` runs — and `elim_term_ite`'s `!ite`
> mints only trigger on the ITEs the substr guards introduce (user
> non-Boolean ITEs are lifted earlier by word_norm on `self.ctx`,
> `lib.rs:384`). So today only the `predicates.rs` family
> (`!pfx/!sfx/!ctnl/!ctnr`, via `rewrite_str_predicates` at
> `lib.rs:515`) mints live-context skolems reachable from a script.
> The `reduce.rs` hardening is defense-in-depth that becomes load-
> bearing the day the substr fence lifts; its collision behavior is
> pinned at unit level (§4), not e2e. The pre-declared-alias hazard for
> `!pfx` is script-reachable and produces a measured **wrong unsat**
> today (a user `(declare-const !pfx0 String)` + `(= !pfx0 "z")` +
> `(str.prefixof "ab" s)` + `(= (str.len s) 2)`: the decomposition
> skolem hash-conses onto the user constant, forcing `s = "abz"` —
> z3: sat). This upgrades the slice from prophylactic to a live
> soundness fix.

## 2. Scope

**In scope.**

- One group-aware mint helper in `reduce.rs`, adopted by all four mint
  families above (§3).
- Unit + e2e pins for both collision directions (§4).

**Out of scope (banked / untouched).**

- **`Context::declare_fun` silent-overwrite hardening for user→user
  redeclarations** (context.rs:166-170). Adjudicated out: it is a
  parser-facing behavior question (SMT-LIB mandates an error on
  redeclaration) with a blast radius over every declare path, not a
  skolem hazard. The solver-side faces are fully closed by §3; bank the
  user→user face for its own look if it ever bites.
- `fresh_str` and word_norm `ite!` regimes: already hardened
  (slice 35 T2, slice 5); untouched.
- Standing bank unchanged: approach B (cite the strips — trigger fired,
  logged, not un-banked), tracked skolem-TermId set, multi-atom
  propagation (slice-34 §10), `Split` passthrough audit, slice-28 §8,
  slice-27 typed-antecedent refactor, slice-29 approach-C, slice-31 §11
  walls 1/2/4, the retracted wall-3 seam.

## 3. Mechanism — group-aware reserved mint

One `pub(crate)` helper in `reduce.rs`, next to `FRESH_CTR` so
`predicates.rs` keeps importing from the module it already uses:

```rust
/// Mint a GROUP of fresh reserved skolems sharing one counter suffix.
/// Loops the global counter until every `{prefix}{n}` is free, then
/// declares + reserves all of them. Group atomicity: if any name in the
/// group is user-owned, the whole group skips — no member of a group is
/// ever minted at an `n` another member couldn't use.
pub(crate) fn fresh_reserved_group(
    ctx: &mut Context,
    group: &[(&str, SortId)],
) -> Vec<TermId> {
    loop {
        let n = next_fresh();
        if group
            .iter()
            .any(|(p, _)| ctx.lookup_symbol(&format!("{p}{n}")).is_some())
        {
            continue; // user (or an earlier check) owns a name at this n
        }
        return group
            .iter()
            .map(|(p, sort)| {
                let sym = ctx.declare_fun(&format!("{p}{n}"), &[], *sort);
                ctx.reserve_symbol(sym);
                ctx.mk_app(Op::Uninterpreted(sym), &[])
                    .expect("nullary app of a declared symbol is well-sorted")
            })
            .collect();
    }
}
```

Call sites:

- `encode_substr`: one call with the `[("!pre", str), ("!mid", str),
  ("!post", str)]` trio, replacing the three bare `declare_fun`s and the
  local `next_fresh()` draw.
- `rewrite_pred` contains-arm: one call with `[("!ctnl", str),
  ("!ctnr", str)]`.
- `rewrite_pred` prefixof/suffixof arms and the ITE lift: 1-element
  groups (`!pfx` / `!sfx` at String; `!ite` at the lifted sort).
- `fresh_str_var` (predicates.rs) and the callers' separate
  `next_fresh()` draws are deleted — the helper owns the draw.

Properties:

- The `lookup_symbol` skip closes the pre-mint direction; `reserve_symbol`
  closes the post-mint direction — and here the reservation **actually
  reaches the parser**, because these mints run on `self.ctx` pre-clone
  (`lib.rs:515-516`), the same regime as word_norm's `ite!`
  (`lib.rs:384`). This is the exact asymmetry slice-35 §6 measured for
  `!strk` (whose in-clone reservation is discarded); no such correction
  is expected here, and the e2e pins in §4 verify the rejection is real.
- **No-collision naming is byte-identical to today** (`!pre0/!mid0/!post0`,
  one suffix per group): the group draws exactly one counter value where
  the old code drew one. This is the argument §4 leans on to skip the
  dump-and-diff.
- The `rewrite_pred` memo (one fresh-var set per repeated atom) is
  unaffected — the helper changes how names are chosen, not when mints
  happen.

**Alternatives rejected.** Per-name helper with independent draws
(simplest, but renames `!mid0` → `!mid1` even with zero collisions —
breaks the byte-identical argument and grouped-suffix debuggability);
in-place loops at each of the four sites (four copies of a
soundness-relevant pattern — the divergence hazard this slice exists to
close).

## 4. Testing

**Unit (`shinri-str`).**

- Pre-declared `!pfx0`: the prefixof decomposition mints `!pfx1`,
  TermIds distinct from the user term.
- Group atomicity: with only `!mid0` pre-declared, the substr trio lands
  entirely on suffix 1 — `!pre0` is never claimed.
- Reservation: minted symbols report `is_reserved`.
- Control: with no collisions, the substr trio shares one suffix
  (`!pre{n}/!mid{n}/!post{n}` for a single `n`) — today's grouped naming
  pinned *relatively*, not at an absolute `n` (the global counter is
  shared across parallel tests, per §5).

**e2e (`script_e2e`).** Mirror the two `ite!` reservation cases
(`script_e2e.rs:118-166`) for the script-reachable `predicates.rs`
family, plus one documentation pin for the fence-dead `reduce.rs`
family:

- Post-mint: a script whose first `(check-sat)` mints `!pfx0`, then
  `(declare-const !pfx0 String)` — **rejected** with the
  "reserved for solver-internal use" error. (A true parse-time
  rejection here, unlike the `!strk` pins — see §3.)
- Pre-declared: `(declare-const !pfx0 String)` + `(= !pfx0 "z")` before
  a prefixof assertion — stays a usable free constant, the mint skips
  past it, and the script keeps its z3-agreeing `sat` (pre-fix: wrong
  unsat via aliasing — the §1 correction's measured hazard).
- Fence documentation pin (`reduce.rs` family): an unfoldable-substr
  script fences to `unknown` *before* any `!pre` mint, so a later
  `(declare-const !pre0 String)` is **accepted** — pinning why the
  `reduce.rs` family has no e2e rejection case (spec §1 plan-time
  correction; the collision regime is pinned at unit level instead).

**Gates** (in order):

- `cargo nextest run -p shinri-solver --features oracle` with a
  **confirmed non-zero test count** (baseline 499 + this slice's new e2e
  pins; the invocation is package-wide, per the slice-35 correction).
- `script_e2e` locally, filtered with `-E 'binary(script_e2e)'` (the
  positional filter finds 0 tests on nextest 0.9.140).
- `cargo fmt --all -- --check`, `cargo clippy --workspace --all-targets
  -- -D warnings`, `cargo nextest run --workspace`.

**Dump-and-diff: adjudicated SKIP.** The change is behavior-identical on
any input that declares none of the eight prefixes at a colliding
suffix — which is the entire oracle corpus. Off-collision, the helper
draws the same counter values, mints the same names at the same TermIds,
and differs only in reservation bits no read path consults outside the
parser's declare check. Collision inputs get dedicated unit + e2e pins
instead. Recorded here so the omission is an explicit decision.

## 5. Risks

- **Counter now skips past user-owned names**: skolem names are internal;
  no test may pin a `!preN`-style spelling against a query that also
  declares one. The workspace gate catches accidental pins.
- **Parse-time rejection is new user-visible behavior**: a script that
  declares a minted name after solving has begun now errors instead of
  silently aliasing a skolem. This is the fix, identical to the `ite!`
  regime, and such inputs are outside any documented contract. Unlike
  slice-35's falsified §5 bullet, the rejection is real here (pre-clone
  mints); the e2e pins measure it rather than assume it.
- **Global `FRESH_CTR` is process-wide** (AtomicU32): parallel tests
  interleave draws, so unit pins on exact suffixes must construct their
  own `Context` and tolerate counter offsets — pin *relative* naming
  (skip behavior, group alignment), not absolute values, except where the
  test controls the counter. (The existing control test shape at
  `reduce.rs:481` already lives with this.)

## 6. Outcome

Implementation landed as three commits on `slice36-sibling-skolem-mints`:

- `3f0bc909` — T1: `fresh_reserved_group` helper (§3), adopted by
  `encode_substr` and the `!ite` lift in `reduce.rs`.
- `69e6dc7e` — T2: `predicates.rs` (`!pfx/!sfx/!ctnl/!ctnr`) adopts the
  helper; closes the measured live `!pfx0` aliasing wrong-unsat from §1.
- `740f10f1` — T3: three `script_e2e` pins (post-mint rejection,
  pre-declared-alias sat, fence-dead `!pre` documentation pin).
- this commit (truth-up) — gates run and this section appended.

**Gate results (all measured, foreground, captured output).**

1. Oracle differential gate —
   `cargo nextest run -p shinri-solver --features oracle`:
   **502 tests run: 502 passed (9 slow), 3 skipped**, 0 failed, wall
   1236.451s (~20.6 min). Matches the plan's ~502 exactly (499 at
   slice-35 close + 3 new e2e pins). No sat/unsat disagreement with z3
   in any test in the run — no BLOCKER.
2. Dump-and-diff — skipped as adjudicated in §4 (not run; this is the
   deliberate omission, not an oversight).
3. Workspace gates:
   - `cargo fmt --all -- --check` — clean (exit 0).
   - `cargo clippy --workspace --all-targets -- -D warnings` — 0
     warnings (exit 0).
   - `cargo nextest run --workspace` — **1146 tests run: 1146 passed (5
     slow), 7 skipped**, 0 failed, wall 281.508s. The plan predicted
     ~1143 (1138 at slice-35 close + 2 reduce + 2 predicates + 3 e2e);
     measured is **1146, a delta of +3** over the stated estimate (and
     +1 over the arithmetic sum 1138+2+2+3=1145) — recorded as-measured,
     not adjusted to match. 0 failed either way; the 7 skipped are
     exactly the `#[ignore]`d fp exhaustives (untouched, per policy).
4. Fence-pin confirmation — re-ran
   `post_fence_declaration_of_pre_name_is_accepted_no_mint_occurred` in
   isolation (`cargo nextest run -p shinri-solver -E
   'test(post_fence_declaration_of_pre_name_is_accepted_no_mint_occurred)'`):
   **1 passed**, asserting `out == vec!["unknown", "unknown"]` at
   `script_e2e.rs:339-343`. Confirms §1's plan-time correction: the
   `reduce.rs` family's fence-dead status holds — the substr fence fires
   before any `!pre` mint, so both check-sats in that script answer
   `unknown` and the later `!pre0` declaration is silently accepted, as
   documented.
5. Wrong-unsat repro (§1's measured hazard) — re-ran exactly:

   ```
   printf '(set-logic QF_S)(declare-const !pfx0 String)(declare-fun s () String)(assert (= !pfx0 "z"))(assert (str.prefixof "ab" s))(assert (= (str.len s) 2))(check-sat)\n' > /tmp/pfx-alias.smt2
   cargo run -q -p shinri-cli -- /tmp/pfx-alias.smt2
   ```

   Output's final line: **`sat`** (six `success` lines from the prior
   `assert`/`declare` commands precede it). Pre-fix this answered
   `unsat` against z3's `sat` — a live wrong-unsat. Post-fix (T2,
   `69e6dc7e`) it answers `sat`, agreeing with z3. The hazard is closed.

**Summary.** All gates green, all measured counts non-zero and in the
expected ballpark (one workspace-count delta noted above, no failures
either side of it), the fence-pin behavior measured exactly as `§1`/`§4`
predicted, and the plan-time wrong-unsat repro now answers `sat`. No
soundness regressions observed. Ready for PR.

## 7. Final-review correction — `!ite` is live, not fence-dead

The final whole-branch review (z3 cross-checked) found §1's fence-dead
claim over-broad. It is **correct for `!pre`/`!mid`/`!post`** — those
mint only inside `encode_substr`, which fires only on unfoldable
substr/at, and the substr soundness fence (`lib.rs:507-512`) returns
`Unknown` for exactly those queries before `reduce_assertions` ever runs
(confirmed by gate 4 in §6). It is **falsified for `!ite`**.

**(a) Why `!ite` is live.** §1's plan-time correction reasoned that "user
non-Boolean ITEs are lifted earlier by word_norm on `self.ctx`
(`lib.rs:384`)", implying no user `ite` could reach `reduce.rs`'s
`elim_term_ite` outside the substr-guard path. This misses that
word_norm's ite lift explicitly **excludes String-sorted ites**
(`crates/shinri-solver/src/word_norm.rs:80-82`,
`eliminates_ite_sort`: `!matches!(ctx.sort_node(s), SortNode::Bool |
SortNode::String)`). A String-sorted user `ite` therefore survives
word_norm untouched and reaches three later passes that mint `!ite` via
`elim_term_ite` on the **live**, pre-clone `self.ctx`
(`lib.rs:516`)  —  not the discarded Combiner clone:

- indexof with a symbolic start position → bounded Int-ite chain
  (`lib.rs:429-430`);
- `str.to_int(str.from_int(n))` roundtrip → `ite(n≥0,n,-1)`
  (`lib.rs:446-447`);
- the `str.to_code`/`str.from_code` roundtrip rewrites
  (`lib.rs:464-467`).

None of these require the substr fence to have fired, so `!ite` mints
are reachable on ordinary scripts that never touch `str.substr`/`str.at`
— including the simplest case, a bare user `(ite b "x" "yy")` assigned
to a string variable, which trivially exercises `elim_term_ite` once
word_norm has declined to touch it.

**(b) Measured repro.** At base `32739ef0` (pre-slice-36):

```
(set-logic QF_S)(declare-const !ite0 String)(declare-fun s () String)(declare-fun b () Bool)
(assert (= !ite0 "zzz"))
(assert (= s (ite b "x" "yy")))
(check-sat)
```

answered **`unsat`** — wrong; z3 confirms **`sat`** (`!ite0 = "zzz"`,
`b = true`, `s = "x"`, or symmetric). The pre-declared, constrained
`!ite0` was adopted by the mint via hash-consing (same genus as the
`!pfx0` hazard in §1), forcing `s` to equal both ite branches through
the aliased skolem. At `HEAD` (post-T1, `fresh_reserved_group`'s
lookup-skip) the same script answers **`sat`**, re-measured foreground
during this final-review fix wave. So slice 36's Task 1 closed a
**second** live wrong-unsat beyond the one §1 documented for `!pfx0` —
Task 1's `!ite` adoption was defense-in-depth only in the sense that it
predated recognizing this route; the fix itself was already load-bearing
at the time it landed.

**(c) New coverage.** `crates/shinri-solver/tests/script_e2e.rs` gains
`user_str_ite_name_declared_before_any_mint_still_works`, pinning the
repro in (b): asserts the script answers `["sat"]`. The slice-36 banner
comment and the `post_fence_declaration_of_pre_name_is_accepted_no_mint_occurred`
doc comment are rescoped to name only `!pre`/`!mid`/`!post` as
fence-dead, with `!ite`'s live routes cited and cross-referenced to the
new pin.

**(d) Bank entries for future slices.**

- (i) `order_engine.rs:20-24`'s `!strcode` is a fixed-name
  declare-or-fetch uninterpreted function, never reserved — currently
  dormant behind the slice-31 fence (`shinri-slice31-str-order-deferred`
  memory: two-free-var `str.<` order is banked, infra dormant). If the
  order engine goes live, a user pre-declaring `!strcode` is silently
  adopted into EUF congruence via the same `declare_fun`-overwrites-
  `fun_sigs` mechanism (`context.rs:166-170`) — same hazard genus as
  this slice, unaddressed. Worth a look the day that fence lifts.
- (ii) Unchanged reminder (spec §2, out of scope): user→user
  `declare_fun` silent overwrite remains adjudicated-out — a
  parser-facing SMT-LIB-conformance question with a blast radius over
  every declare path, not a skolem-specific hazard. Still banked, not
  fixed here.
