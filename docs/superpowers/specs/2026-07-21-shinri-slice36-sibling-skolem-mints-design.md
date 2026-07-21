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
(`script_e2e.rs:118-166`) for two families (one `predicates.rs` family,
one `reduce.rs` family):

- Post-mint: a script whose first `(check-sat)` triggers the mint, then
  `(declare-const !pfx0 String)` — **rejected** with the
  "reserved for solver-internal use" error. Same shape for `!pre0` via a
  substr script. (Expected to be a true parse-time rejection here,
  unlike the `!strk` pins — see §3.)
- Pre-declared: `(declare-const !pfx0 String)` before any use — stays a
  usable free constant, the mint skips past it, and the script keeps its
  verdict.

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
