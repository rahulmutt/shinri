# Slice 36 — Sibling Skolem-Mint Hardening Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close both skolem-name collision directions (pre-mint user
adoption, post-mint user redeclaration) for every non-`fresh_str` skolem
mint in `shinri-str` (`!pfx/!sfx/!ctnl/!ctnr`, `!pre/!mid/!post`, `!ite`)
via one group-aware lookup-skip + `reserve_symbol` helper — fixing a
**measured live wrong-unsat** (pre-declared `!pfx0` aliasing, shinri
`unsat` vs z3 `sat`, reproduced at plan time).

**Architecture:** One `pub(crate)` helper `fresh_reserved_group` in
`crates/shinri-str/src/reduce.rs` next to the global `FRESH_CTR`. It
draws one counter value per mint GROUP, skips any `n` where any
`{prefix}{n}` is user-owned (`lookup_symbol`), then declares + reserves
all names in the group. All four mint sites adopt it. No-collision
naming stays byte-identical (one shared suffix per group), which is the
spec's recorded argument for skipping the oracle dump-and-diff.

**Tech Stack:** Rust workspace, `cargo nextest` (0.9.140 — positional
filters silently find 0 tests; use `-E` expressions), z3 via mise for
oracle checks.

**Spec:** `docs/superpowers/specs/2026-07-21-shinri-slice36-sibling-skolem-mints-design.md`
(read it first — especially the §1 plan-time reachability correction:
the `reduce.rs` families are solver-path-dead behind the substr fence at
`crates/shinri-solver/src/lib.rs:507-512`, so only the `predicates.rs`
family gets e2e rejection pins).

## Global Constraints

- `cargo fmt --all` before every push; CI gates on `fmt --check` and fails fast.
- `cargo clippy --workspace --all-targets -- -D warnings` must be clean.
- Never remove `#[ignore]` from the exhaustive `shinri-fp` suites.
- Oracle differential tests need `--features oracle` — without it they
  silently run 0 tests; always confirm a non-zero test count.
- nextest filter for the e2e binary: `-E 'binary(script_e2e)'`.
- Pure-Rust mandate: no new dependencies.
- Skolem naming: no test may pin an absolute `!preN`-style suffix except
  via the relative `next_fresh()`-base pattern shown in Task 1 (the
  counter is process-global; nextest's process-per-test isolation makes
  the relative pattern deterministic).

---

### Task 1: `fresh_reserved_group` helper + `reduce.rs` adoption

**Files:**
- Modify: `crates/shinri-str/src/reduce.rs` (helper after `next_fresh`
  at `reduce.rs:70-72`; adoption in `encode_substr` `reduce.rs:212-230`
  and `elim_term_ite` `reduce.rs:436-441`; tests in the existing
  `mod tests` at `reduce.rs:474`)

**Interfaces:**
- Consumes: `Context::{lookup_symbol, declare_fun, reserve_symbol,
  is_reserved, symbol_name, mk_app, string_sort}` (all exist,
  `crates/shinri-core/src/context.rs:153-197`), `next_fresh()`.
- Produces: `pub(crate) fn fresh_reserved_group(ctx: &mut Context,
  group: &[(&str, SortId)]) -> Vec<TermId>` — Task 2 calls this from
  `predicates.rs`. Returned TermIds are nullary uninterpreted apps, one
  per group entry, in order; all symbols reserved; all names share one
  numeric suffix.

- [ ] **Step 1: Write the failing helper tests**

In `mod tests` in `crates/shinri-str/src/reduce.rs`, add (alongside the
existing imports `use shinri_core::{BuiltinOp, Context, Op};` — extend
with `TermId, TermNode` as needed):

```rust
    use shinri_core::{TermId, TermNode};

    /// Name of the uninterpreted symbol a minted nullary app points at.
    fn sym_name(ctx: &Context, t: TermId) -> String {
        match ctx.term_node(t) {
            TermNode::App {
                op: Op::Uninterpreted(sym),
                ..
            } => ctx.symbol_name(*sym).to_string(),
            other => panic!("expected nullary uninterpreted app, got {other:?}"),
        }
    }

    fn sym_id(ctx: &Context, t: TermId) -> shinri_core::SymbolId {
        match ctx.term_node(t) {
            TermNode::App {
                op: Op::Uninterpreted(sym),
                ..
            } => *sym,
            other => panic!("expected nullary uninterpreted app, got {other:?}"),
        }
    }

    #[test]
    fn fresh_reserved_group_mints_shared_suffix_and_reserves() {
        // Relative-suffix pattern (spec §5): `base + 1` is the next value
        // the helper will draw. Deterministic single-threaded; nextest's
        // process-per-test isolation keeps it deterministic in CI.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let base = crate::reduce::next_fresh();
        let minted = crate::reduce::fresh_reserved_group(
            &mut ctx,
            &[("!pre", str_s), ("!mid", str_s), ("!post", str_s)],
        );
        assert_eq!(minted.len(), 3);
        let n = base + 1;
        assert_eq!(sym_name(&ctx, minted[0]), format!("!pre{n}"));
        assert_eq!(sym_name(&ctx, minted[1]), format!("!mid{n}"));
        assert_eq!(sym_name(&ctx, minted[2]), format!("!post{n}"));
        for &t in &minted {
            assert!(
                ctx.is_reserved(sym_id(&ctx, t)),
                "minted skolems must be reserved"
            );
        }
    }

    #[test]
    fn fresh_reserved_group_skips_user_owned_names_atomically() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let base = crate::reduce::next_fresh();
        // User owns !mid{base+1}: the WHOLE trio must skip to base+2 —
        // no member may be minted at a suffix another member couldn't use.
        let user_name = format!("!mid{}", base + 1);
        let user_sym = ctx.declare_fun(&user_name, &[], str_s);
        let user = ctx.mk_app(Op::Uninterpreted(user_sym), &[]).unwrap();
        let minted = crate::reduce::fresh_reserved_group(
            &mut ctx,
            &[("!pre", str_s), ("!mid", str_s), ("!post", str_s)],
        );
        let n = base + 2;
        assert_eq!(sym_name(&ctx, minted[0]), format!("!pre{n}"));
        assert_eq!(sym_name(&ctx, minted[1]), format!("!mid{n}"));
        assert_eq!(sym_name(&ctx, minted[2]), format!("!post{n}"));
        // The user's term is untouched: distinct TermId, not reserved.
        assert!(minted.iter().all(|&t| t != user));
        assert!(!ctx.is_reserved(user_sym), "user symbol must stay usable");
        // Group atomicity: !pre{base+1} was never claimed by the failed round.
        assert!(
            ctx.lookup_symbol(&format!("!pre{}", base + 1)).is_none(),
            "skipped round must not declare partial groups"
        );
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

Run:
```bash
cargo nextest run -p shinri-str -E 'test(fresh_reserved_group)'
```
Expected: COMPILE ERROR — `fresh_reserved_group` not found. (A compile
failure is the red state here.)

- [ ] **Step 3: Implement the helper**

In `crates/shinri-str/src/reduce.rs`, extend the `shinri_core` import at
`reduce.rs:27` to include `SortId`:

```rust
use shinri_core::{BuiltinOp, Context, Op, SortId, TermId, TermNode};
```

Add directly below `next_fresh` (`reduce.rs:70-72`):

```rust
/// Mint a GROUP of fresh reserved skolems sharing one counter suffix.
///
/// Slice 36: every skolem mint outside `fresh_str` routes through here.
/// The `lookup_symbol` skip closes the pre-mint collision direction (a
/// user-declared `!pfx0` is never adopted as a skolem — pre-fix this was
/// a measured wrong-unsat); `reserve_symbol` closes the post-mint
/// direction (a later user declaration of the minted name is rejected at
/// parse time, the `ite!` regime). Group atomicity: if any name in the
/// group is taken at `n`, the whole group skips — no member is minted at
/// a suffix another member couldn't use, so no-collision naming stays
/// byte-identical to the pre-slice-36 one-draw-per-group scheme.
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

- [ ] **Step 4: Run the tests to verify they pass**

Run:
```bash
cargo nextest run -p shinri-str -E 'test(fresh_reserved_group)'
```
Expected: 2 passed.

- [ ] **Step 5: Write the failing adoption tests**

Add to the same `mod tests`. These walk the reduced output to find the
minted symbols (suffix unknown at this level), asserting the reserved
bit and shared suffix — red until Step 6 adopts the helper:

```rust
    /// Collect every nullary uninterpreted symbol in `t` whose name starts
    /// with `prefix`.
    fn collect_minted(
        ctx: &Context,
        t: TermId,
        prefix: &str,
        out: &mut Vec<(String, shinri_core::SymbolId)>,
    ) {
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            if let Op::Uninterpreted(sym) = op {
                let name = ctx.symbol_name(*sym).to_string();
                if name.starts_with(prefix) && !out.iter().any(|(n, _)| *n == name) {
                    out.push((name, *sym));
                }
            }
            let children = ctx.children(*args).to_vec();
            for c in children {
                collect_minted(ctx, c, prefix, out);
            }
        }
    }

    #[test]
    fn substr_and_ite_mints_are_reserved_with_shared_substr_suffix() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = {
            let f = ctx.declare_fun("s_res", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let i = ctx.mk_numeral(
            shinri_core::Rational::from_int(1i128.into()),
            ctx.int_sort(),
        );
        let one = ctx.mk_numeral(
            shinri_core::Rational::from_int(1i128.into()),
            ctx.int_sort(),
        );
        let ss = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrSubstr), &[s, i, one])
            .unwrap();
        let lit = ctx.mk_string_const("b");
        let atom = ctx.mk_eq(ss, lit).unwrap();
        let out = reduce_assertions(&mut ctx, &[atom]);
        let mut minted = Vec::new();
        for &a in &out {
            for p in ["!pre", "!mid", "!post", "!ite"] {
                collect_minted(&ctx, a, p, &mut minted);
            }
        }
        // One substr encoding mints the trio; its guards' ITEs mint !ite vars.
        assert!(
            minted.iter().any(|(n, _)| n.starts_with("!pre"))
                && minted.iter().any(|(n, _)| n.starts_with("!mid"))
                && minted.iter().any(|(n, _)| n.starts_with("!post"))
                && minted.iter().any(|(n, _)| n.starts_with("!ite")),
            "expected pre/mid/post + ite mints, got {minted:?}"
        );
        for (name, sym) in &minted {
            assert!(ctx.is_reserved(*sym), "{name} must be reserved");
        }
        // The trio shares ONE suffix (today's grouped naming, pinned
        // relatively per spec §4/§5).
        let suffix = |n: &str, p: &str| n[p.len()..].to_string();
        let pre_sfx = minted
            .iter()
            .find(|(n, _)| n.starts_with("!pre"))
            .map(|(n, _)| suffix(n, "!pre"))
            .unwrap();
        for p in ["!mid", "!post"] {
            let s = minted
                .iter()
                .find(|(n, _)| n.starts_with(p))
                .map(|(n, _)| suffix(n, p))
                .unwrap();
            assert_eq!(s, pre_sfx, "substr trio must share one suffix");
        }
    }
```

- [ ] **Step 6: Run to verify red, then adopt the helper at both sites**

Run:
```bash
cargo nextest run -p shinri-str -E 'test(substr_and_ite_mints_are_reserved)'
```
Expected: FAIL on `"!pre0 must be reserved"`-style assertion (mints
exist but carry no reserved bit).

Then replace the mint block in `encode_substr` (`reduce.rs:212-230` —
delete `let n = next_fresh();`, the three `declare_fun` lines, and the
three `mk_app` blocks):

```rust
    // Declare fresh reserved String skolems (slice 36: lookup-skip +
    // reserve_symbol via the shared group mint — one suffix per trio).
    let str_s = ctx.string_sort();
    let int_s = ctx.int_sort();

    let minted = fresh_reserved_group(
        ctx,
        &[("!pre", str_s), ("!mid", str_s), ("!post", str_s)],
    );
    let (pre, mid, post) = (minted[0], minted[1], minted[2]);
```

And the `!ite` mint in `elim_term_ite` (`reduce.rs:436-441` — delete
`let n = next_fresh();`, the `declare_fun`, and the `mk_app` block):

```rust
                let sort = ctx.sort_of(t);
                let w = fresh_reserved_group(ctx, &[("!ite", sort)])[0];
```

- [ ] **Step 7: Run the full `shinri-str` suite to verify green**

Run:
```bash
cargo nextest run -p shinri-str
```
Expected: all pass (existing reduce/predicates tests pin no absolute
skolem names). If any test fails on a name pin, fix the TEST to the
relative pattern — not the helper.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/reduce.rs
git commit -m "feat(str): slice36 T1 — group-aware reserved skolem mint, adopted by substr/ite reduction"
```

---

### Task 2: `predicates.rs` adoption (fixes the measured wrong-unsat aliasing)

**Files:**
- Modify: `crates/shinri-str/src/predicates.rs` (delete `fresh_str_var`
  at `predicates.rs:176-181`; rework the three mint arms in
  `rewrite_pred` at `predicates.rs:215-242`; tests in `mod tests` at
  `predicates.rs:263`)

**Interfaces:**
- Consumes: `crate::reduce::fresh_reserved_group(ctx, &[(&str, SortId)])
  -> Vec<TermId>` (Task 1), `crate::reduce::next_fresh()` (tests only).
- Produces: no API change — `rewrite_str_predicates` signature
  unchanged; minted `!pfx/!sfx/!ctnl/!ctnr` symbols are now reserved and
  never alias user terms.

- [ ] **Step 1: Write the failing tests**

Add to `mod tests` in `crates/shinri-str/src/predicates.rs` (the module
already has `str_var` and `pred` helpers, `predicates.rs:263-275`):

```rust
    /// Destructure `(= s (str.++ a b))` and return the concat's LAST child
    /// (the minted skolem for prefixof).
    fn last_concat_child(ctx: &Context, eq: TermId) -> TermId {
        let TermNode::App { args, .. } = ctx.term_node(eq) else {
            panic!("expected eq app");
        };
        let eq_children = ctx.children(*args).to_vec();
        let concat = eq_children[1];
        let TermNode::App { args, .. } = ctx.term_node(concat) else {
            panic!("expected concat app");
        };
        *ctx.children(*args).last().expect("concat has children")
    }

    fn sym_of(ctx: &Context, t: TermId) -> shinri_core::SymbolId {
        let TermNode::App {
            op: Op::Uninterpreted(sym),
            ..
        } = ctx.term_node(t)
        else {
            panic!("expected nullary uninterpreted app");
        };
        *sym
    }

    #[test]
    fn pre_declared_pfx_name_is_never_adopted_as_skolem() {
        // The measured wrong-unsat shape (spec §1 plan-time correction):
        // pre-fix, the mint's declare_fun re-interned the user's `!pfx{n}`
        // and the skolem hash-consed onto the user's constrained constant.
        let mut ctx = Context::new();
        let base = crate::reduce::next_fresh();
        let user = str_var(&mut ctx, &format!("!pfx{}", base + 1));
        let ab = ctx.mk_string_const("ab");
        let s = str_var(&mut ctx, "s");
        let atom = pred(&mut ctx, BuiltinOp::StrPrefixOf, ab, s);
        let out = rewrite_str_predicates(&mut ctx, &[atom]);
        let k = last_concat_child(&ctx, out[0]);
        assert_ne!(k, user, "skolem must not alias the user's !pfx term");
        assert_eq!(
            ctx.symbol_name(sym_of(&ctx, k)),
            format!("!pfx{}", base + 2),
            "mint must skip the user-owned suffix"
        );
        assert!(ctx.is_reserved(sym_of(&ctx, k)));
        assert!(!ctx.is_reserved(sym_of(&ctx, user)));
    }

    #[test]
    fn contains_pair_shares_one_suffix_and_is_reserved() {
        let mut ctx = Context::new();
        let abc = ctx.mk_string_const("b");
        let s = str_var(&mut ctx, "s");
        let atom = pred(&mut ctx, BuiltinOp::StrContains, s, abc);
        let out = rewrite_str_predicates(&mut ctx, &[atom]);
        // out[0] is (= s (str.++ kl sub kr)).
        let TermNode::App { args, .. } = ctx.term_node(out[0]) else {
            panic!("expected eq app");
        };
        let eq_children = ctx.children(*args).to_vec();
        let TermNode::App { args, .. } = ctx.term_node(eq_children[1]) else {
            panic!("expected concat app");
        };
        let cat = ctx.children(*args).to_vec();
        let (kl, kr) = (cat[0], cat[2]);
        let (nl, nr) = (
            ctx.symbol_name(sym_of(&ctx, kl)).to_string(),
            ctx.symbol_name(sym_of(&ctx, kr)).to_string(),
        );
        assert!(nl.starts_with("!ctnl") && nr.starts_with("!ctnr"));
        assert_eq!(
            nl["!ctnl".len()..],
            nr["!ctnr".len()..],
            "ctnl/ctnr must share one suffix"
        );
        assert!(ctx.is_reserved(sym_of(&ctx, kl)));
        assert!(ctx.is_reserved(sym_of(&ctx, kr)));
    }
```

Extend the test module's imports if needed:
`use shinri_core::{TermNode};` (Context/Op/BuiltinOp/TermId come via
`use super::*;`).

- [ ] **Step 2: Run the tests to verify they fail**

Run:
```bash
cargo nextest run -p shinri-str -E 'test(pre_declared_pfx) + test(contains_pair_shares)'
```
Expected: FAIL — `pre_declared_pfx_name_is_never_adopted_as_skolem`
fails on `assert_ne!(k, user)` (the aliasing bug, red);
`contains_pair_shares_one_suffix_and_is_reserved` fails on
`is_reserved`.

- [ ] **Step 3: Adopt the helper**

In `crates/shinri-str/src/predicates.rs`:

Delete `fresh_str_var` (`predicates.rs:176-181`).

Rework the three arms in `rewrite_pred` (each currently draws
`crate::reduce::next_fresh()` and calls `fresh_str_var`,
`predicates.rs:215-242`):

```rust
                Op::Builtin(BuiltinOp::StrPrefixOf) => {
                    let (p, s) = (new_children[0], new_children[1]);
                    let str_s = ctx.string_sort();
                    let k = crate::reduce::fresh_reserved_group(ctx, &[("!pfx", str_s)])[0];
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[p, k])
                        .expect("p ++ k");
                    ctx.mk_eq(s, cat).expect("s = p ++ k")
                }
                Op::Builtin(BuiltinOp::StrSuffixOf) => {
                    let (p, s) = (new_children[0], new_children[1]);
                    let str_s = ctx.string_sort();
                    let k = crate::reduce::fresh_reserved_group(ctx, &[("!sfx", str_s)])[0];
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[k, p])
                        .expect("k ++ p");
                    ctx.mk_eq(s, cat).expect("s = k ++ p")
                }
                Op::Builtin(BuiltinOp::StrContains) => {
                    let (s, sub) = (new_children[0], new_children[1]);
                    let str_s = ctx.string_sort();
                    let minted = crate::reduce::fresh_reserved_group(
                        ctx,
                        &[("!ctnl", str_s), ("!ctnr", str_s)],
                    );
                    let (kl, kr) = (minted[0], minted[1]);
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[kl, sub, kr])
                        .expect("kl ++ sub ++ kr");
                    ctx.mk_eq(s, cat).expect("s = kl ++ sub ++ kr")
                }
```

- [ ] **Step 4: Run the crate suite to verify green**

Run:
```bash
cargo nextest run -p shinri-str
```
Expected: all pass, including the two new tests. Same fix-the-test rule
as Task 1 Step 7 if any existing test pinned an absolute name.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/predicates.rs
git commit -m "fix(str): slice36 T2 — predicate skolems mint via fresh_reserved_group (closes measured !pfx aliasing wrong-unsat)"
```

---

### Task 3: e2e pins (`script_e2e`)

**Files:**
- Modify: `crates/shinri-solver/tests/script_e2e.rs` (append after the
  slice-35 `!strk` pins; mirror the `ite!` cases at
  `script_e2e.rs:110-163`)

**Interfaces:**
- Consumes: the file's existing `run_script` harness (returns one output
  `String` per producing command; successful `declare-const` produces no
  output, a rejected one produces an `(error …)` string).
- Produces: three `#[test]`s pinning the slice-36 e2e contract.

- [ ] **Step 1: Write the three pins**

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 36 — sibling skolem mints (spec §4): the predicates.rs family
// (!pfx/!sfx/!ctnl/!ctnr) mints on the LIVE parser-visible ctx
// (crates/shinri-solver/src/lib.rs:515, pre-clone), so BOTH collision
// directions are script-reachable — unlike !strk (clone-isolated, slice 35)
// and unlike !pre/!mid/!post/!ite (fence-dead, third pin below).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn post_mint_declaration_of_pfx_name_is_rejected() {
    // First check-sat rewrites prefixof → (= s (str.++ "ab" !pfx0)), minting
    // and reserving !pfx0 on the live ctx (the global FRESH_CTR starts at 0
    // in this test's process — nextest runs one process per test). The
    // user's later declaration of the minted name must be REJECTED (ite!
    // regime), the aliased use is an undeclared-symbol error, and the final
    // check-sat re-mints at a fresh suffix and stays sat. No wrong verdict.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (str.prefixof "ab" s))(assert (= (str.len s) 2))
           (check-sat)
           (declare-const !pfx0 String)
           (assert (= !pfx0 "z"))
           (check-sat)"#,
    );
    assert_eq!(out.len(), 4, "sat / declare-error / aliased-use-error / sat");
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("reserved for solver-internal use"),
        "declaration of the minted name must be rejected, got {:?}",
        out[1]
    );
    assert!(
        out[2].starts_with("(error"),
        "aliased use is undeclared, got {:?}",
        out[2]
    );
    assert_eq!(out[3], "sat", "must NOT be a wrong verdict");
}

#[test]
fn user_pfx_name_declared_before_any_mint_still_works() {
    // The measured plan-time wrong-unsat (spec §1 correction), now fixed:
    // pre-fix, the mint adopted the user's !pfx0 (= "z"), forcing
    // s = "ab" ++ "z" against len(s) = 2 → shinri unsat vs z3 sat. The
    // lookup-skip mints !pfx1 instead; the user constant stays free and
    // the script is SAT with s = "ab".
    let out = run_script(
        r#"(set-logic QF_S)(declare-const !pfx0 String)(declare-fun s () String)
           (assert (= !pfx0 "z"))
           (assert (str.prefixof "ab" s))(assert (= (str.len s) 2))
           (check-sat)(get-value (s))"#,
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"), "was a wrong unsat pre-fix");
    assert!(
        out.get(1).is_some_and(|v| v.contains("\"ab\"")),
        "s must be \"ab\", got {out:?}"
    );
}

#[test]
fn post_fence_declaration_of_pre_name_is_accepted_no_mint_occurred() {
    // Documentation pin (spec §1 plan-time correction): an unfoldable
    // substr fences to `unknown` at lib.rs:507-512 BEFORE reduce_assertions
    // runs, so no !pre/!mid/!post/!ite skolem is ever minted on the live
    // ctx — a later user `declare-const !pre0` is ACCEPTED (nothing to
    // collide with). This pins WHY the reduce.rs family has no e2e
    // rejection case; its collision regime is unit-pinned (reduce.rs
    // tests, slice 36 T1) as defense-in-depth for a future fence lift.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)(declare-fun i () Int)
           (assert (= (str.at s i) "a"))
           (check-sat)
           (declare-const !pre0 String)
           (assert (= !pre0 "z"))
           (check-sat)"#,
    );
    assert_eq!(
        out,
        vec!["unknown", "unknown"],
        "fence fires pre-mint both times; the declaration is silently accepted"
    );
}
```

- [ ] **Step 2: Run the e2e binary**

Run:
```bash
cargo nextest run -p shinri-solver -E 'binary(script_e2e)'
```
Expected: all pass (72 tests: 69 prior + 3 new; 1 pre-existing skip).
The two `!pfx` pins are green because Tasks 1–2 landed; the fence pin
documents current behavior. If `post_fence_…` reports outputs other than
`["unknown", "unknown"]`, STOP — the fence assumption is wrong; re-read
spec §1's plan-time correction and report the measured outputs rather
than adjusting the assertion silently.

- [ ] **Step 3: Slice-33/34/35 probe regression check**

The same run covers the slice-33 probes (C/E/G/F/H), slice-34 probes
(A1–A4, B1), and the slice-35 `!strk` pins — all must read unchanged
(B1 stays `unknown`). Confirm zero failures before committing.

- [ ] **Step 4: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/script_e2e.rs
git commit -m "test(str): slice36 T3 — e2e pins: !pfx reservation both directions, fence-dead !pre documentation"
```

---

### Task 4: Gates + spec truth-up

**Files:**
- Modify: `docs/superpowers/specs/2026-07-21-shinri-slice36-sibling-skolem-mints-design.md`
  (append `## 6. Outcome`)

**Interfaces:**
- Consumes: Tasks 1–3 landed and committed.
- Produces: gate-green branch ready for PR; spec Outcome section with
  measured numbers.

- [ ] **Step 1: Oracle gate (FOREGROUND, captured output)**

Run in the foreground and capture the summary (do NOT background it;
verify the count is non-zero — without `--features oracle` the
differential suites silently run 0 tests):

```bash
cargo nextest run -p shinri-solver --features oracle 2>&1 | tail -20
```
Expected: **~502 passed** (499 at slice-35 close + 3 new e2e pins; the
invocation is package-wide so script_e2e is included), 0 failed,
~20 min. Any `sat`/`unsat` disagreement with z3 is a BLOCKER — stop and
report with the failing test's output; do not rationalize it away.

- [ ] **Step 2: No dump-and-diff (adjudicated skip)**

Per spec §4: off-collision the helper draws the same counter values and
mints the same names; reservation bits are consulted only by the
parser's declare check. Do not run the dump-and-diff; the skip is
recorded in the spec.

- [ ] **Step 3: Full workspace gates**

```bash
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo nextest run --workspace
```
Expected: fmt clean; clippy 0 warnings; workspace **~1143 passed**
(1138 at slice-35 close + 2 reduce tests + 2 predicates tests + 3 e2e
pins, minus any counting drift — record the actual number), 0 failed,
7 skipped (the `#[ignore]`d fp exhaustives).

- [ ] **Step 4: Spec truth-up**

Append `## 6. Outcome` to the spec: task commits, measured test counts
per gate, confirmation (or correction) of the fence-pin behavior, and
an explicit line that the pre-fix wrong-unsat repro
(`scratchpad pfx-alias.smt2` shape, shinri `unsat` vs z3 `sat`) now
answers `sat`. Re-run the plan-time repro to confirm:

```bash
printf '(set-logic QF_S)(declare-const !pfx0 String)(declare-fun s () String)(assert (= !pfx0 "z"))(assert (str.prefixof "ab" s))(assert (= (str.len s) 2))(check-sat)\n' > /tmp/pfx-alias.smt2
cargo run -q -p shinri-cli -- /tmp/pfx-alias.smt2
```
Expected: final line `sat` (was `unsat` pre-fix).

- [ ] **Step 5: Commit**

```bash
git add docs/superpowers/specs/2026-07-21-shinri-slice36-sibling-skolem-mints-design.md
git commit -m "docs(str): slice36 truth-up — measured gate outcomes"
```
