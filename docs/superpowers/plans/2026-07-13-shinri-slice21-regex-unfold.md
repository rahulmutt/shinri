# Slice 21 — Derivative Unfolding of Symbolic str.in_re Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decide `str.in_re(t, R)` for any String-sorted term `t` and constant regex `R` — infinite/co-infinite languages included (`x ∈ [a-z]*`) — at both polarities, by lazy guarded Brzozowski-derivative unfolding inside the string theory's final check, with membership-aware model repair; fuel/cap exhaustion and unrealisable models yield sound `Unknown`, never a wrong verdict.

**Architecture:** Membership atoms with constant regex sides pass a narrowed presence fence into the SAT core as ordinary `str.in_re` atoms. `StrSolver` records them at `assert` (negative polarity → `Rex::Comp` internally) and, at `Effort::Full` check, makes progress per atom against the string side's deep normal form: **Rule G** consumes ground prefixes with the existing per-code-point `deriv` (fully-cited Conflict on violation), **Rule E** emits the fundamental class-expansion equivalence over next-character classes, and **Rule S** peels a head character with fresh `h`/`z` witnesses — all through the existing single-clause `TCheck::Split{atoms, guard}` channel, `Fuel`-bounded and deduplicated. The model builder seeds free membership variables with words found by capped derivative search; the post-solve `string_model_satisfies` self-check learns to evaluate `str.in_re` and downgrades any unrealised Sat to `Unknown`.

**Tech Stack:** Rust workspace (crates `shinri-str`, `shinri-solver`; `shinri-str/src/trail.rs` grows a third mark). Differential testing against z3 (installed via mise) behind `--features oracle`.

**Spec:** `docs/superpowers/specs/2026-07-13-shinri-slice21-regex-unfold-design.md`.

## Global Constraints

- Soundness posture: every emitted clause is a valid implication/equivalence or a fresh-witness canonicalization; Sat additionally passes the post-solve self-check. Budget exhaustion → `Unknown`, NEVER a wrong verdict.
- New caps: `CLASS_SPLIT_CAP: usize = 64` (max next-character classes per expansion) and `MEMB_SEARCH_STEP_CAP: usize = 10_000` (max derivative states visited by the model-repair word search). Existing caps unchanged: `FUEL_NODE_CAP = 10_000`, `Fuel { remaining: 40 }`, `ENUM_WORD_CAP`/`ENUM_TOTAL_BYTES_CAP`, SAT `step_budget`, arith budgets.
- The slice-19 ground fold and slice-20 finite/co-finite rewrite run FIRST and unchanged; the engine only sees what survives them.
- Fences that REMAIN: symbolic regex sides (`extract_const_regex` → `None`), RegLan-sorted subterms outside supported membership position, RegLan declarations, above-alphabet literals on either side.
- **Surrogates:** class analysis runs in `u32` code-point space (exact, surrogates included — no class is ever dropped from an expansion). Only witness minting skips `0xD800..=0xDFFF`. The only surrogate class boundaries that can arise are `lo = 0xD800` / `hi = 0xDFFF` (boundaries come from user chars ±1; user chars are never surrogates) — `range_term` relies on this.
- Guarded lemmas fire only when the string side is `side_clean(all_cond_roots)`; ground-NF Conflicts are fully cited (trigger literal + `deep_normal_form_cited` antecedents) and ungated — the diseq Case-2 pattern.
- **ASCII-only differential scripts** (slice-18/19 harness lesson). Non-ASCII coverage lives in unit tests and shinri-only pins.
- Never perturb existing differential-oracle families or their seeds. New family seed: `0x53_00_0000_0001` (grep `tests/qfs_differential.rs` for seed collisions before use).
- `cargo fmt` before EVERY commit (CI hard-fails on `cargo fmt --check`; subagents do not auto-format).
- Run oracle tests FOREGROUND with captured output — never claim a tally you didn't see.
- Commit messages: `feat(str): … (slice 21)`, `test(str): … (slice 21)`, `docs: …`.
- Do NOT run `cargo test --workspace` locally (~50 min); test per-crate as instructed. CI runs the full workspace.
- No new dependencies.
- Branch `slice21-regex-unfold` already exists with the spec committed — do NOT create a new branch; work on it.

---

### Task 1: Rex machinery extensions — classes, reverse translation, word search

Pure additions to `crates/shinri-str/src/regex.rs`, unit-tested, not yet called by the solver (transient `#[allow(dead_code)]` where clippy demands, removed in Task 3 — the slice-19/20 pattern).

**Files:**
- Modify: `crates/shinri-str/src/regex.rs`

**Interfaces:**
- Consumes (already in `regex.rs`): `enum Rex`, smart constructors `concat/union/inter/star/comp/loop_`, `nullable`, `deriv(c: u32, r: &Rex) -> Rex`, `node_count`, `eval_membership`, `extract_const_regex(ctx: &Context, t: TermId) -> Option<Rex>`, `str_term_mentions_above_alphabet`, `MAX_CODE: u32 = 0x2FFFF`, `FUEL_NODE_CAP: usize = 10_000`, test helpers `chr`, `lit`.
- Produces (Tasks 2–4 depend on these EXACT names):
  - Visibility lifts (same names, now `pub(crate)`): `Rex`, `concat`, `union`, `inter`, `comp`, `nullable`, `deriv`, `node_count`, `extract_const_regex`, `eval_membership`, `str_term_mentions_above_alphabet`, `MAX_CODE`, `FUEL_NODE_CAP`. Add `Hash` to Rex's derive list: `#[derive(Clone, PartialEq, Eq, Hash, Debug)]`.
  - `pub(crate) const CLASS_SPLIT_CAP: usize = 64;`
  - `pub(crate) const MEMB_SEARCH_STEP_CAP: usize = 10_000;`
  - `pub(crate) fn next_classes(r: &Rex) -> Option<Vec<(u32, u32)>>`
  - `pub(crate) fn head_forced(r: &Rex) -> Option<((u32, u32), Rex)>`
  - `pub(crate) fn rex_to_term(ctx: &mut Context, r: &Rex) -> TermId`
  - `pub(crate) fn search_word(r: &Rex, n: usize) -> Option<String>`
  - `pub fn eval_str_in_re(ctx: &Context, s: &str, re_t: TermId) -> Option<bool>` (pub: the solver crate's self-check calls it)

- [ ] **Step 1: Write the failing tests**

Append inside `mod tests` in `crates/shinri-str/src/regex.rs`:

```rust
    // ── Task 1 (slice 21): classes, reverse translation, word search ────────

    #[test]
    fn next_classes_partition_sigma() {
        // [a-z]* → boundaries {0, 'a', 'z'+1} → 3 classes covering Σ exactly.
        let r = star(Rex::Range('a' as u32, 'z' as u32));
        let cls = next_classes(&r).unwrap();
        assert_eq!(
            cls,
            vec![
                (0, 'a' as u32 - 1),
                ('a' as u32, 'z' as u32),
                ('z' as u32 + 1, MAX_CODE)
            ]
        );
        // Σ itself (re.allchar): ONE class.
        assert_eq!(next_classes(&Rex::Range(0, MAX_CODE)), Some(vec![(0, MAX_CODE)]));
        // No ranges at all (∅, ε): one class covering Σ.
        assert_eq!(next_classes(&Rex::Eps), Some(vec![(0, MAX_CODE)]));
        // Cap abort: 40 disjoint single-char ranges → 81 boundaries > 64.
        let many = union((0..40u32).map(|i| Rex::Range(3 * i, 3 * i)).collect());
        assert_eq!(next_classes(&many), None);
    }

    #[test]
    fn next_classes_derivative_uniform() {
        // Inside each class the derivative is identical to the representative's.
        let r = concat(vec![
            union(vec![Rex::Range('a' as u32, 'm' as u32), lit("xy")]),
            star(Rex::Range('0' as u32, '9' as u32)),
        ]);
        for (lo, hi) in next_classes(&r).unwrap() {
            let d0 = deriv(lo, &r);
            for c in [lo, (lo + hi) / 2, hi] {
                assert_eq!(deriv(c, &r), d0, "class [{lo},{hi}] not uniform at {c}");
            }
        }
    }

    #[test]
    fn head_forced_shapes() {
        // Bare range: forced head, ε residual.
        assert_eq!(
            head_forced(&Rex::Range('a' as u32, 'z' as u32)),
            Some((('a' as u32, 'z' as u32), Rex::Eps))
        );
        // Range-headed concat: forced head, concat residual.
        let r = concat(vec![Rex::Range('a' as u32, 'a' as u32), star(lit("b"))]);
        let (c, rest) = head_forced(&r).unwrap();
        assert_eq!(c, ('a' as u32, 'a' as u32));
        assert_eq!(rest, star(lit("b")));
        // Not head-forced: star, union, eps, empty, comp.
        assert_eq!(head_forced(&star(lit("a"))), None);
        assert_eq!(head_forced(&Rex::Eps), None);
        assert_eq!(head_forced(&Rex::Empty), None);
        assert_eq!(head_forced(&comp(lit("a"))), None);
    }

    #[test]
    fn rex_to_term_roundtrips_language() {
        // Round-trip is SEMANTIC (same language), not syntactic — the
        // surrogate-block encoding extracts back as Inter/Comp shapes.
        let mut ctx = Context::new();
        let samples = ["", "a", "z", "ab", "ba", "0", "abc", "zzz"];
        let cases = vec![
            Rex::Empty,
            Rex::Eps,
            Rex::Range('a' as u32, 'z' as u32),
            star(Rex::Range('a' as u32, 'z' as u32)),
            comp(star(Rex::Range('a' as u32, 'z' as u32))),
            concat(vec![lit("a"), star(union(vec![lit("b"), lit("c")]))]),
            loop_(Rex::Range('a' as u32, 'b' as u32), 1, 3),
            inter(vec![star(lit("a")), comp(lit("aa"))]),
        ];
        for r in cases {
            let t = rex_to_term(&mut ctx, &r);
            let back = extract_const_regex(&ctx, t).expect("minted term must extract");
            for s in samples {
                assert_eq!(
                    eval_membership(s, &back),
                    eval_membership(s, &r),
                    "language mismatch on {s:?} for {r:?}"
                );
            }
        }
    }

    #[test]
    fn rex_to_term_surrogate_block_range() {
        // A class ending at 0xDFFF and one starting at 0xD800 — the only
        // surrogate endpoints that can arise. The minted term must extract to
        // a Rex with the same membership on representative code points.
        let mut ctx = Context::new();
        for (lo, hi) in [(0xD800u32, 0xDFFFu32), ('a' as u32, 0xDFFF), (0xD800, 0x2FFFF)] {
            let t = rex_to_term(&mut ctx, &Rex::Range(lo, hi));
            let back = extract_const_regex(&ctx, t).expect("surrogate range term extracts");
            // Membership decided per code point via deriv (u32-exact — works
            // for surrogates even though no Rust literal can hold them).
            for c in [0u32, 'a' as u32, 0xD7FF, 0xD800, 0xDBBB, 0xDFFF, 0xE000, 0x2FFFF] {
                let want = lo <= c && c <= hi;
                assert_eq!(
                    nullable(&deriv(c, &back)),
                    want,
                    "code point {c:#x} in [{lo:#x},{hi:#x}]"
                );
            }
        }
    }

    #[test]
    fn search_word_finds_and_bounds() {
        let az_star = star(Rex::Range('a' as u32, 'z' as u32));
        // Word of exact length, all lengths realizable.
        assert_eq!(search_word(&az_star, 0), Some(String::new()));
        let w = search_word(&az_star, 3).unwrap();
        assert_eq!(w.chars().count(), 3);
        assert_eq!(eval_membership(&w, &az_star), Some(true));
        // Intersection via the smart constructor: a* ∩ [a-z]{2}.
        let two = loop_(Rex::Range('a' as u32, 'z' as u32), 2, 2);
        let w2 = search_word(&inter(vec![star(lit("a")), two]), 2).unwrap();
        assert_eq!(w2, "aa");
        // No word of that length: a* has no length-1 word other than "a";
        // a* ∩ b* has none at length ≥ 1.
        assert_eq!(search_word(&inter(vec![star(lit("a")), star(lit("b"))]), 1), None);
        // Surrogate-only language: L = the surrogate block — no Rust witness.
        assert_eq!(search_word(&Rex::Range(0xD800, 0xDFFF), 1), None);
        // Witness skips the block: [0xD7FF-0xE001] at length 1 minted as 0xD7FF.
        let w3 = search_word(&Rex::Range(0xD7FF, 0xE001), 1).unwrap();
        assert_eq!(w3.chars().next().unwrap() as u32, 0xD7FF);
        // Step-cap abort returns None (sound): a comp-heavy state space at a
        // length the cap cannot cover. comp(a*) words of length 40 over Σ force
        // one derivative state per prefix — cap trips before depth 40 × classes.
        let hard = inter((0..12).map(|i| comp(loop_(Rex::Range(0, MAX_CODE), i, i))).collect());
        let _ = search_word(&hard, 40); // must terminate (None or Some) without hanging
    }

    #[test]
    fn eval_str_in_re_term_level() {
        let mut ctx = Context::new();
        let r = star(Rex::Range('a' as u32, 'z' as u32));
        let t = rex_to_term(&mut ctx, &r);
        assert_eq!(eval_str_in_re(&ctx, "abc", t), Some(true));
        assert_eq!(eval_str_in_re(&ctx, "aBc", t), Some(false));
        // Symbolic regex term → None (cannot evaluate).
        let v = {
            let s = ctx.declare_fun("L", &[], ctx.reglan_sort());
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        assert_eq!(eval_str_in_re(&ctx, "a", v), None);
        // Above-alphabet string → None.
        assert_eq!(eval_str_in_re(&ctx, "\u{30000}", t), None);
    }
```

- [ ] **Step 2: Run tests to verify they fail to compile**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -20`
Expected: compile error — `next_classes`, `head_forced`, `rex_to_term`, `search_word`, `eval_str_in_re`, `CLASS_SPLIT_CAP` not found.

- [ ] **Step 3: Implement**

In `crates/shinri-str/src/regex.rs`:

(a) Lift visibilities listed in **Interfaces** (`enum Rex` → `pub(crate) enum Rex`, etc.) and add `Hash` to Rex's derive. Add `use rustc_hash::FxHashSet;` to the imports.

(b) Insert after `lit_to_rex` (before the slice-20 enumeration section):

```rust
// ─── Slice 21: derivative unfolding support ──────────────────────────────

/// Max next-character classes per Rule-E expansion; more ⇒ fence (Unknown).
pub(crate) const CLASS_SPLIT_CAP: usize = 64;
/// Max derivative states visited by the model-repair word search.
pub(crate) const MEMB_SEARCH_STEP_CAP: usize = 10_000;

const SURR_LO: u32 = 0xD800;
const SURR_HI: u32 = 0xDFFF;

/// Collect the class boundaries contributed by every `Range` node in `r`:
/// each range [lo, hi] cuts Σ at lo and hi+1.
fn range_bounds(r: &Rex, out: &mut BTreeSet<u32>) {
    match r {
        Rex::Empty | Rex::Eps => {}
        Rex::Range(lo, hi) => {
            out.insert(*lo);
            if *hi < MAX_CODE {
                out.insert(hi + 1);
            }
        }
        Rex::Concat(ps) | Rex::Union(ps) | Rex::Inter(ps) => {
            for p in ps {
                range_bounds(p, out);
            }
        }
        Rex::Star(i) | Rex::Comp(i) | Rex::Loop(i, ..) => range_bounds(i, out),
    }
}

/// Next-character classes: a partition of Σ = [0, MAX_CODE] into maximal
/// ranges on which `deriv` is uniform. `deriv` branches only on `Range`
/// membership tests, and no `Range` boundary of `r` falls strictly inside a
/// class, so every test answers identically across the class. Using ALL
/// ranges in `r` (not just head-reachable ones) yields a finer-than-needed
/// partition — still correct. `None` iff the partition exceeds
/// `CLASS_SPLIT_CAP` (→ caller fences).
pub(crate) fn next_classes(r: &Rex) -> Option<Vec<(u32, u32)>> {
    let mut bounds = BTreeSet::new();
    bounds.insert(0u32);
    range_bounds(r, &mut bounds);
    let cuts: Vec<u32> = bounds.into_iter().collect();
    if cuts.len() > CLASS_SPLIT_CAP {
        return None;
    }
    let mut classes = Vec::with_capacity(cuts.len());
    for (i, &lo) in cuts.iter().enumerate() {
        let hi = if i + 1 < cuts.len() { cuts[i + 1] - 1 } else { MAX_CODE };
        classes.push((lo, hi));
    }
    Some(classes)
}

/// The syntactic shape `Range · R''` (Rule-E disjunct shape): a bare `Range`
/// (residual ε) or a `Concat` whose head is a `Range`. Rule S peels exactly
/// this shape; everything else goes through Rule E first.
pub(crate) fn head_forced(r: &Rex) -> Option<((u32, u32), Rex)> {
    match r {
        Rex::Range(lo, hi) => Some(((*lo, *hi), Rex::Eps)),
        Rex::Concat(ps) => match &ps[0] {
            Rex::Range(lo, hi) => Some(((*lo, *hi), concat(ps[1..].to_vec()))),
            _ => None,
        },
        _ => None,
    }
}

/// `(re.range c c')` for NON-surrogate endpoints.
fn range_term_raw(ctx: &mut Context, lo: u32, hi: u32) -> TermId {
    let l = ctx.mk_string_const(&char::from_u32(lo).expect("non-surrogate lo").to_string());
    let h = ctx.mk_string_const(&char::from_u32(hi).expect("non-surrogate hi").to_string());
    ctx.mk_app(Op::Builtin(BuiltinOp::ReRange), &[l, h])
        .expect("re.range well-sorted")
}

/// A RegLan term denoting exactly the char set [lo, hi] ⊆ Σ. Surrogate
/// endpoints — only `lo = 0xD800` / `hi = 0xDFFF` can arise, because class
/// boundaries are user chars ±1 and user chars are never surrogates — are
/// handled by splitting at the block and encoding the FULL block as
/// `(re.diff (re.range \u{D7FF} \u{E000}) (re.union (re.range \u{D7FF} \u{D7FF})
/// (re.range \u{E000} \u{E000})))`, whose endpoints are all expressible.
fn range_term(ctx: &mut Context, lo: u32, hi: u32) -> TermId {
    debug_assert!(lo <= hi && hi <= MAX_CODE);
    debug_assert!(lo == SURR_LO || !(SURR_LO..=SURR_HI).contains(&lo), "interior surrogate lo");
    debug_assert!(hi == SURR_HI || !(SURR_LO..=SURR_HI).contains(&hi), "interior surrogate hi");
    let mut parts: Vec<TermId> = Vec::new();
    if lo < SURR_LO {
        parts.push(range_term_raw(ctx, lo, hi.min(SURR_LO - 1)));
    }
    if lo <= SURR_LO && hi >= SURR_HI {
        let outer = range_term_raw(ctx, SURR_LO - 1, SURR_HI + 1);
        let a = range_term_raw(ctx, SURR_LO - 1, SURR_LO - 1);
        let b = range_term_raw(ctx, SURR_HI + 1, SURR_HI + 1);
        let u = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[a, b])
            .expect("re.union well-sorted");
        parts.push(
            ctx.mk_app(Op::Builtin(BuiltinOp::ReDiff), &[outer, u])
                .expect("re.diff well-sorted"),
        );
    }
    if hi > SURR_HI {
        parts.push(range_term_raw(ctx, lo.max(SURR_HI + 1), hi));
    }
    match parts.len() {
        1 => parts[0],
        _ => ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &parts)
            .expect("re.union well-sorted"),
    }
}

/// Reverse translation Rex → RegLan term over the existing Re* builtins.
/// Total (surrogate-endpoint ranges included). Guarantee: the minted term
/// re-extracts (`extract_const_regex` succeeds) to a Rex with the SAME
/// LANGUAGE — not always the same shape (the surrogate-block diff extracts
/// as Inter/Comp). Deterministic, so hash-consing gives TermId identity for
/// equal Rex inputs (the engine's dedup keys rely on this).
pub(crate) fn rex_to_term(ctx: &mut Context, r: &Rex) -> TermId {
    let kids = |ctx: &mut Context, ps: &[Rex]| -> Vec<TermId> {
        ps.iter().map(|p| rex_to_term(ctx, p)).collect()
    };
    match r {
        Rex::Empty => ctx
            .mk_app(Op::Builtin(BuiltinOp::ReNone), &[])
            .expect("re.none well-sorted"),
        Rex::Eps => {
            let e = ctx.mk_string_const("");
            ctx.mk_app(Op::Builtin(BuiltinOp::StrToRe), &[e])
                .expect("str.to_re well-sorted")
        }
        Rex::Range(lo, hi) => range_term(ctx, *lo, *hi),
        Rex::Concat(ps) => {
            let ks = kids(ctx, ps);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReConcat), &ks)
                .expect("re.++ well-sorted")
        }
        Rex::Union(ps) => {
            let ks = kids(ctx, ps);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReUnion), &ks)
                .expect("re.union well-sorted")
        }
        Rex::Inter(ps) => {
            let ks = kids(ctx, ps);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReInter), &ks)
                .expect("re.inter well-sorted")
        }
        Rex::Star(i) => {
            let k = rex_to_term(ctx, i);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReStar), &[k])
                .expect("re.* well-sorted")
        }
        Rex::Comp(i) => {
            let k = rex_to_term(ctx, i);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReComp), &[k])
                .expect("re.comp well-sorted")
        }
        Rex::Loop(i, lo, hi) => {
            let k = rex_to_term(ctx, i);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: *lo, hi: *hi }), &[k])
                .expect("re.loop well-sorted")
        }
    }
}

/// A word of length EXACTLY `n` in L(r), or None if none exists within
/// `MEMB_SEARCH_STEP_CAP` visited states (an abort is NOT a verdict — the
/// caller leaves the value untouched and the self-check backstops). DFS over
/// next-character classes; per class the witness char is the smallest
/// NON-SURROGATE code point (a pure-surrogate class has no Rust witness and
/// is skipped — sound: skipping loses completeness only). `dead` memoizes
/// (remaining, Rex) states with no word, preventing exponential re-search.
pub(crate) fn search_word(r: &Rex, n: usize) -> Option<String> {
    fn go(
        r: &Rex,
        n: usize,
        steps: &mut usize,
        dead: &mut FxHashSet<(usize, Rex)>,
        out: &mut String,
    ) -> bool {
        if *steps >= MEMB_SEARCH_STEP_CAP {
            return false;
        }
        *steps += 1;
        if n == 0 {
            return nullable(r);
        }
        if matches!(r, Rex::Empty) {
            return false;
        }
        let key = (n, r.clone());
        if dead.contains(&key) {
            return false;
        }
        if let Some(classes) = next_classes(r) {
            for (lo, hi) in classes {
                // Smallest non-surrogate witness in the class (boundaries can
                // only be 0xD800 / 0xDFFF, so lo either avoids the block or
                // the block ends inside the class at 0xDFFF).
                let c = if (SURR_LO..=SURR_HI).contains(&lo) {
                    if hi > SURR_HI {
                        SURR_HI + 1
                    } else {
                        continue; // pure-surrogate class: no Rust witness
                    }
                } else {
                    lo
                };
                let d = deriv(c, r);
                if node_count(&d) > FUEL_NODE_CAP {
                    continue;
                }
                out.push(char::from_u32(c).expect("non-surrogate in-alphabet"));
                if go(&d, n - 1, steps, dead, out) {
                    return true;
                }
                out.pop();
            }
        }
        dead.insert(key);
        false
    }
    let mut out = String::new();
    let mut steps = 0usize;
    let mut dead = FxHashSet::default();
    if go(r, n, &mut steps, &mut dead, &mut out) {
        Some(out)
    } else {
        None
    }
}

/// Ground membership of a CONCRETE string in the regex TERM `re_t`.
/// 3-valued for the post-solve witness self-check: `Some(verdict)` iff `s`
/// is in-alphabet, `re_t` extracts as a constant regex, and evaluation stays
/// within fuel; `None` = cannot evaluate (treated as satisfied — can only
/// MISS a violation, never fabricate one).
pub fn eval_str_in_re(ctx: &Context, s: &str, re_t: TermId) -> Option<bool> {
    if s.chars().any(|c| c as u32 > MAX_CODE) {
        return None;
    }
    let rex = extract_const_regex(ctx, re_t)?;
    eval_membership(s, &rex)
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -20`
Expected: PASS (all new tests + all pre-existing regex tests unchanged).

- [ ] **Step 5: fmt, clippy, commit**

```bash
cargo fmt
cargo clippy -p shinri-str --all-targets 2>&1 | tail -5   # expect: clean (transient #[allow(dead_code)] on not-yet-called items is acceptable, removed by Task 3)
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): next-character classes, Rex reverse translation, capped word search (slice 21)"
```

---

### Task 2: Membership intake, fence narrowing, self-check extension

After this task, engine-eligible memberships flow to SAT and `StrSolver` records them; there are NO engine rules yet, so verdicts are: Sat only when the (unrepaired) model genuinely satisfies every membership (validated by the extended self-check), otherwise `Unknown`. Everything stays sound at every commit.

**Files:**
- Modify: `crates/shinri-str/src/trail.rs` (third mark)
- Modify: `crates/shinri-str/src/lib.rs` (fields, assert intake, pop, cited_lits, test helper)
- Modify: `crates/shinri-str/src/regex.rs` (`has_unsupported_regex` + tests)
- Modify: `crates/shinri-solver/src/lib.rs` (fence swap ~line 485; `eval_bool` StrInRe arm)
- Test: `crates/shinri-solver/tests/script_e2e.rs` (sanity pins)

**Interfaces:**
- Consumes: Task 1's `extract_const_regex`, `str_term_mentions_above_alphabet`, `eval_str_in_re`.
- Produces (Task 3 depends on these EXACT names):
  - `StrSolver` fields: `memb_true: Vec<(TermId, Lit, bool)>` (atom, literal, polarity), `memb_levels: Vec<u32>`
  - `Trail::push(eq_len: usize, diseq_len: usize, memb_len: usize)`, `Trail::pop_to(target) -> Option<(usize, usize, usize)>`
  - `pub fn has_unsupported_regex(ctx: &Context, assertions: &[TermId]) -> bool` in `regex.rs`
  - `#[cfg(test)] pub fn test_force_memb_true(&mut self, atom: TermId, positive: bool)`

- [ ] **Step 1: Write the failing tests**

(a) In `crates/shinri-str/src/regex.rs` `mod tests`:

```rust
    // ── Task 2 (slice 21): narrowed fence ────────────────────────────────

    #[test]
    fn unsupported_regex_fence_narrowed() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        // Engine-eligible: symbolic string × constant infinite regex → NOT fenced.
        let az_star = rex_to_term(&mut ctx, &star(Rex::Range('a' as u32, 'z' as u32)));
        let ok = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, az_star])
            .unwrap();
        assert!(!has_unsupported_regex(&ctx, &[ok]));
        // Symbolic REGEX side → fenced.
        let lvar = {
            let s = ctx.declare_fun("L", &[], ctx.reglan_sort());
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let sym = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, lvar])
            .unwrap();
        assert!(has_unsupported_regex(&ctx, &[sym]));
        // Above-alphabet string side → fenced.
        let hi = ctx.mk_string_const("\u{30000}");
        let bad = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[hi, az_star])
            .unwrap();
        assert!(has_unsupported_regex(&ctx, &[bad]));
        // Bare RegLan term outside membership position (RegLan equality) → fenced.
        let two = rex_to_term(&mut ctx, &lit("q"));
        let re_eq = ctx.mk_eq(lvar, two).unwrap();
        assert!(has_unsupported_regex(&ctx, &[re_eq]));
        // The eligible atom under Boolean structure stays unfenced.
        let notok = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[ok]).unwrap();
        assert!(!has_unsupported_regex(&ctx, &[notok]));
    }
```

(b) In `crates/shinri-str/src/lib.rs` `mod tests`:

```rust
    // ── Task 2 (slice 21): membership intake + retraction bookkeeping ───────

    #[test]
    fn memb_intake_and_pop_truncate_together() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let re_t = crate::regex::test_az_star_term(&mut ctx);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut s = StrSolver::default();
        s.test_force_memb_true(atom, true);
        assert_eq!(s.memb_true.len(), 1);
        assert_eq!(s.memb_levels, vec![0]);
        // push/pop keep memb_true in lock-step with eq_true/diseq_true.
        s.push();
        s.test_force_memb_true(atom, false);
        assert_eq!(s.memb_true.len(), 2);
        s.pop(0);
        assert_eq!(s.memb_true.len(), 1);
        assert_eq!(s.memb_levels.len(), 1);
    }
```

This needs a tiny test-only term builder in `regex.rs` (add next to the existing test helpers, OUTSIDE `mod tests` so `lib.rs` tests reach it):

```rust
/// Test-only: `(re.* (re.range "a" "z"))` as a term.
#[cfg(test)]
pub(crate) fn test_az_star_term(ctx: &mut Context) -> TermId {
    rex_to_term(ctx, &star(Rex::Range('a' as u32, 'z' as u32)))
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str 2>&1 | tail -10`
Expected: compile errors — `has_unsupported_regex`, `test_force_memb_true`, `memb_true` not found.

- [ ] **Step 3: Implement**

(a) `crates/shinri-str/src/trail.rs` — third mark, same shape:

```rust
#[derive(Default)]
pub struct Trail {
    marks: Vec<(usize, usize, usize)>, // (eq_true_len, diseq_true_len, memb_true_len)
}

impl Trail {
    pub fn push(&mut self, eq_len: usize, diseq_len: usize, memb_len: usize) {
        self.marks.push((eq_len, diseq_len, memb_len));
    }

    /// Current absolute decision level = number of open scopes. (Unchanged
    /// semantics — see the original doc comment.)
    pub fn level(&self) -> u32 {
        self.marks.len() as u32
    }

    /// Returns the (eq, diseq, memb) lengths to truncate to for absolute `target`.
    pub fn pop_to(&mut self, target: usize) -> Option<(usize, usize, usize)> {
        let mut last = None;
        while self.marks.len() > target {
            last = self.marks.pop();
        }
        last
    }
}
```

(b) `crates/shinri-str/src/lib.rs`:

- Fields (after `diseq_levels`):

```rust
    /// Asserted str.in_re atoms: (atom, literal, polarity). Polarity false ⟹
    /// the membership is asserted NEGATIVELY (t ∉ R ≡ t ∈ comp(R) internally).
    memb_true: Vec<(TermId, Lit, bool)>,
    /// SAT decision level per memb_true entry (lock-step; truncated on pop).
    memb_levels: Vec<u32>,
```

- `assert` (after the `is_str_eq` block, inside the same `if let TermNode::App`):

```rust
            // Slice 21: record membership atoms at both polarities. The regex
            // side is constant by the solver fence (input atoms) or by
            // construction (engine-minted atoms).
            if matches!(op, Op::Builtin(BuiltinOp::StrInRe)) {
                self.memb_true.push((atom, lit, lit.is_positive()));
                self.memb_levels.push(lvl);
            }
```

- `push`: `self.trail.push(self.eq_true.len(), self.diseq_true.len(), self.memb_true.len());`
- `pop`: destructure `Some((e, d, mb))`; add `self.memb_true.truncate(mb); self.memb_levels.truncate(mb);`
- `cited_lits` (debug audit): `out.extend(self.memb_true.iter().map(|&(_, l, _)| (l, "str.memb_true")));`
- Test helper (in the existing `#[cfg(test)] impl StrSolver` block):

```rust
    /// Push a membership atom directly onto `memb_true` (dummy Lit, level 0),
    /// simulating the SAT layer asserting `str.in_re` at the given polarity.
    pub fn test_force_memb_true(&mut self, atom: TermId, positive: bool) {
        self.memb_true.push((atom, Lit::new(Var::new(0), true), positive));
        self.memb_levels.push(0);
    }
```

(c) `crates/shinri-str/src/regex.rs` — the narrowed fence (after `has_unreduced_regex`, which stays for its existing unit tests):

```rust
/// Slice-21 fence (replaces the slice-19/20 blanket presence fence at the
/// solver seam): true iff anything regex-shaped survives that the ENGINE
/// cannot own — a `str.in_re` whose regex side fails constant extraction or
/// whose string side mentions an above-alphabet literal, or any
/// RegLan-sorted subterm OUTSIDE the regex position of a supported
/// membership (RegLan equality, bare RegLan terms). Engine-eligible
/// memberships are NOT fenced — they flow to StrSolver as ordinary atoms.
pub fn has_unsupported_regex(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        if ctx.sort_of(t) == ctx.reglan_sort() {
            return true; // RegLan term outside a supported membership position
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids: Vec<TermId> = ctx.children(*args).to_vec();
                if matches!(op, Op::Builtin(BuiltinOp::StrInRe)) {
                    return extract_const_regex(ctx, kids[1]).is_none()
                        || str_term_mentions_above_alphabet(ctx, kids[0])
                        || walk(ctx, kids[0]);
                }
                kids.iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}
```

(d) `crates/shinri-solver/src/lib.rs`:

- Fence swap (~line 485): replace `has_unreduced_regex` with `has_unsupported_regex` and update the comment:

```rust
            // ── Slices 19–21: RegLan + str.in_re ─────────────────────────────
            // Ground folds (19) and finite/co-finite equivalence rewrites (20)
            // run in the pass; what survives is either ENGINE-ELIGIBLE — a
            // constant-regex membership over an in-alphabet string side, which
            // slice 21's derivative unfolding owns as an ordinary theory atom —
            // or unsupported (symbolic regex side, RegLan equality,
            // above-alphabet literals) and fences to sound Unknown. Queries
            // DECLARING RegLan symbols were already fenced after word_norm.
            assertions = shinri_str::regex::rewrite_ground_in_re(&mut self.ctx, &assertions);
            if shinri_str::regex::has_unsupported_regex(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

- `eval_bool` — add an arm next to the existing string-atom cases (before the fallthrough `_ => None`):

```rust
            Op::Builtin(BuiltinOp::StrInRe) => {
                // 3-valued: None (symbolic regex / un-valued string / fuel)
                // is NOT a verdict — the gate treats it as satisfied.
                let s = self.eval_str_val(model, kids[0])?;
                shinri_str::regex::eval_str_in_re(&self.ctx, &s, kids[1])
            }
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str 2>&1 | tail -10` — expected: PASS.
Run: `cargo test -p shinri-solver --test script_e2e 2>&1 | tail -10` — expected: PASS. One pre-existing pin needs attention: the slice-20 `Unknown` pin for `(re.* (re.range "a" "b"))` shapes and the `str.in_re s re.allchar` pin may ALREADY flip to `sat` at this task (a free variable's default model can genuinely satisfy a nullable membership, and the extended self-check validates it). If a pin fails BY IMPROVING (unknown → sat with a verified witness), update that pin now with a comment `slice 21: decided (was fenced Unknown)`; any other change is a stop-the-line bug.

- [ ] **Step 5: Add sanity e2e pins**

Append to the slice-organized pin section of `crates/shinri-solver/tests/script_e2e.rs`:

```rust
// Slice 21 (Task 2): fence narrowed, engine rules not yet wired. Sound
// verdicts only — Sat must carry a genuine witness (self-check), everything
// else Unknown. These pins tighten in Tasks 3–5.
#[test]
fn in_re_symbolic_nullable_sat_via_selfcheck() {
    // x ∈ [a-z]* is satisfied by the default model (x = "" — nullable), and
    // the extended self-check verifies it: sat with witness even pre-engine.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (str.in_re x (re.* (re.range \"a\" \"z\"))))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn in_re_symbolic_nonnullable_unknown_pre_engine() {
    // x ∈ [a-z]+ : the default model (x = "") violates the membership; no
    // engine rules yet, so the self-check downgrades to Unknown — NOT a wrong
    // verdict. Task 4 flips this pin to Sat.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (str.in_re x (re.+ (re.range \"a\" \"z\"))))(check-sat)",
        Verdict::Unknown,
    );
}

#[test]
fn in_re_symbolic_regex_side_still_fenced() {
    expect(
        "(set-logic QF_S)(declare-fun x () String)(declare-fun L () RegLan)\
         (assert (str.in_re x L))(check-sat)",
        Verdict::Unknown,
    );
}
```

Run: `cargo test -p shinri-solver --test script_e2e in_re_symbolic 2>&1 | tail -10`
Expected: PASS (if `in_re_symbolic_nonnullable_unknown_pre_engine` returns Sat instead, verify the witness is genuine — then it is an improvement; adjust the pin and its comment).

- [ ] **Step 6: fmt, clippy, commit**

```bash
cargo fmt
cargo clippy -p shinri-str -p shinri-solver --all-targets 2>&1 | tail -5
git add -A
git commit -m "feat(str): str.in_re intake + narrowed regex fence + membership-aware model self-check (slice 21)"
```

---

### Task 3: Engine rules G/E/S — the membership pass

The heart of the slice: a new module `memb.rs` with the per-round membership pass, called from `StrSolver::check` right before the final `TCheck::Sat`.

**Files:**
- Create: `crates/shinri-str/src/memb.rs`
- Modify: `crates/shinri-str/src/lib.rs` (module decl, new fields, the call site)
- Test: unit tests in `memb.rs`; e2e unsat pins in `crates/shinri-solver/tests/script_e2e.rs`

**Interfaces:**
- Consumes: Task 1's `next_classes`, `head_forced`, `rex_to_term`, `deriv`, `nullable`, `node_count`, `comp`, `concat`, `extract_const_regex`, `Rex`, `FUEL_NODE_CAP`; Task 2's `memb_true`; existing `normalize::deep_normal_form_cited`, `side_clean`, `wordeq::fresh_str`, `wordeq::len_of`, `collect::collect`, `Fuel`.
- Produces:
  - `StrSolver` fields: `emitted_memb: FxHashSet<(TermId, TermId, u8)>` (string-side term, regex term of the residual Rex, rule tag), `memb_wits: FxHashMap<(TermId, TermId), (TermId, TermId)>` (per head-split (x, regex term) → the fresh (h, z)) — both monotone (never popped), like `emitted_splits`.
  - `pub(crate) fn memb_check(s: &mut StrSolver, cx: &mut TheoryCtx, known: &[TermId], all_cond_roots: &FxHashSet<ENodeId>) -> Option<TCheck>` in `memb.rs`.
  - `pub(crate) fn memb_sides(terms: &Context, atom: TermId) -> (TermId, TermId)` in `memb.rs` (Task 4 uses it).

**Rule tags (dedup key third component):** `0` = Rule E expansion; `1..=4` = head-split clauses S1..S4.

**The four head-split clauses** (S = the membership literal `lit`, `x` = the variable head of the residual NF, `γ` = the rest of the residual, fresh `h`, `z`):

| # | Clause | `TCheck::Split` encoding |
|---|--------|--------------------------|
| S1 | `lit → x = "" ∨ x = h·z` | `atoms: [x_eps, x_hz]`, `guard: Some(¬lit)` |
| S2 | `x = h·z → len(h) = 1` | `atoms: [distinct(x, h·z), len(h)=1]`, `guard: None` |
| S3 | `lit ∧ x = h·z → h ∈ C` | `atoms: [distinct(x, h·z), str.in_re(h, C)]`, `guard: Some(¬lit)` |
| S4 | `lit ∧ x = h·z → z·γ ∈ R''` | `atoms: [distinct(x, h·z), str.in_re(z·γ, R'')]`, `guard: Some(¬lit)` |

The second guard literal of S2–S4 is expressed as the POSITIVE `Distinct` atom (the codebase already treats `(distinct s t)` atoms and negative `(= s t)` literals as interchangeable disequality forms — `diseq_sides` handles both; the diseq conflict machinery catches a SAT assignment that sets both `x = h·z` and `distinct(x, h·z)` true). S2 is unguarded: it is a fresh-witness canonicalization, sound exactly like the F-split's `z1`/`z2` (`h`, `z` occur nowhere else, so any model extends to satisfy it).

- [ ] **Step 1: Write the failing unit tests**

Create `crates/shinri-str/src/memb.rs` with the tests first (implementation in Step 3):

```rust
//! Slice 21: the membership pass — lazy guarded derivative unfolding of
//! `str.in_re` atoms into word equations, run at the end of every Full check.

#[cfg(test)]
mod tests {
    use crate::regex::{self, Rex};
    use crate::StrSolver;
    use shinri_core::{BuiltinOp, Context, Op, TermId};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    fn var(ctx: &mut Context, n: &str) -> TermId {
        let str_s = ctx.string_sort();
        let s = ctx.declare_fun(n, &[], str_s);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    fn memb_atom(ctx: &mut Context, t: TermId, r: &Rex) -> TermId {
        let re_t = regex::rex_to_term_test(ctx, r);
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[t, re_t])
            .unwrap()
    }

    fn harness(ctx: &mut Context) -> (StrSolver, EqualityEngine, AtomRegistry) {
        (StrSolver::default(), EqualityEngine::default(), AtomRegistry::default())
    }

    /// Drive check() to a fixpoint, collecting every emitted Split; panics on
    /// Unknown. Returns the terminal TCheck (Sat or Conflict).
    fn run_rounds(
        s: &mut StrSolver,
        cx: &mut TheoryCtx,
        max: usize,
    ) -> (Vec<(Vec<TermId>, bool)>, TCheck) {
        let mut splits = Vec::new();
        for _ in 0..max {
            match s.check(cx, Effort::Full) {
                TCheck::Split { atoms, guard } => splits.push((atoms, guard.is_some())),
                other => return (splits, other),
            }
        }
        panic!("no fixpoint within {max} rounds");
    }

    #[test]
    fn rule_g_ground_conflict_and_discharge() {
        // x = "ab" merged, x ∈ a*  ⇒ Conflict (ground eval false).
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let ab = ctx.mk_string_const("ab");
        let eq = ctx.mk_eq(x, ab).unwrap();
        let m = memb_atom(&mut ctx, x, &regex::star_lit_test("a"));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &atoms };
        s.new_var(&mut cx, shinri_core::Var::new(0), eq);
        s.new_var(&mut cx, shinri_core::Var::new(1), m);
        s.test_force_eq_true(eq);
        // Unit tests drive the eq engine EXPLICITLY (the Combiner does this
        // in production) — same incantation as the wordeq.rs tests.
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(ab));
        let _ = cx.eq.merge(xn, cn, shinri_theory::types::EqJust::Definitional);
        s.test_force_memb_true(m, true);
        let (_, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(terminal, TCheck::Conflict(_)), "ground violation must conflict");

        // Same shape, x ∈ (str.to_re "ab") ⇒ discharged, Sat fixpoint.
        let mut ctx2 = Context::new();
        let x2 = var(&mut ctx2, "x");
        let ab2 = ctx2.mk_string_const("ab");
        let eq2 = ctx2.mk_eq(x2, ab2).unwrap();
        let m2 = memb_atom(&mut ctx2, x2, &regex::lit_test("ab"));
        let (mut s2, mut eq_e2, atoms2) = harness(&mut ctx2);
        let mut cx2 = TheoryCtx { terms: &mut ctx2, eq: &mut eq_e2, atoms: &atoms2 };
        s2.new_var(&mut cx2, shinri_core::Var::new(0), eq2);
        s2.new_var(&mut cx2, shinri_core::Var::new(1), m2);
        s2.test_force_eq_true(eq2);
        let (xn2, cn2) = (cx2.eq.intern(x2), cx2.eq.intern(ab2));
        let _ = cx2.eq.merge(xn2, cn2, shinri_theory::types::EqJust::Definitional);
        s2.test_force_memb_true(m2, true);
        let (_, terminal2) = run_rounds(&mut s2, &mut cx2, 16);
        assert!(matches!(terminal2, TCheck::Sat), "satisfied ground membership discharges");
    }

    #[test]
    fn negative_polarity_uses_complement() {
        // x = "ab" merged, ¬(x ∈ a*) ⇒ discharged (comp semantics); and
        // ¬(x ∈ (str.to_re "ab")) ⇒ Conflict.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let ab = ctx.mk_string_const("ab");
        let eq = ctx.mk_eq(x, ab).unwrap();
        let m_astar = memb_atom(&mut ctx, x, &regex::star_lit_test("a"));
        let m_ab = memb_atom(&mut ctx, x, &regex::lit_test("ab"));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &atoms };
        s.new_var(&mut cx, shinri_core::Var::new(0), eq);
        s.test_force_eq_true(eq);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(ab));
        let _ = cx.eq.merge(xn, cn, shinri_theory::types::EqJust::Definitional);
        s.test_force_memb_true(m_astar, false); // "ab" ∉ a* — true, discharges
        let (_, t1) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(t1, TCheck::Sat));
        s.test_force_memb_true(m_ab, false); // "ab" ∉ {ab} — false, conflicts
        let (_, t2) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(t2, TCheck::Conflict(_)));
    }

    #[test]
    fn rule_e_expansion_shape() {
        // x ∈ [a-c]* (not head-forced, nullable): ONE guarded clause whose
        // atoms are the ε equality + one membership per class with a
        // non-empty derivative (here exactly one: [a-c]·[a-c]*).
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let r = regex::star_range_test('a', 'c');
        let m = memb_atom(&mut ctx, x, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &atoms };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        // Rounds may interleave length axioms; find the ONE expansion split
        // (the guarded split containing a str.in_re disjunct). Terminal Sat
        // proves the expansion dedups (no re-emission).
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(terminal, TCheck::Sat), "expansion must dedup to a fixpoint");
        let is_memb = |t: &TermId| {
            matches!(
                cx.terms.term_node(*t),
                shinri_core::TermNode::App { op: Op::Builtin(BuiltinOp::StrInRe), .. }
            )
        };
        let expansions: Vec<_> = splits
            .iter()
            .filter(|(atoms, _)| atoms.iter().any(is_memb))
            .collect();
        assert_eq!(expansions.len(), 1, "exactly one Rule-E expansion for [a-c]*");
        let (disj, guarded) = expansions[0];
        assert!(*guarded, "expansion must be guarded by ¬lit");
        assert_eq!(disj.len(), 2, "ε disjunct + one live class disjunct");
        // One disjunct is x = "" and the other a str.in_re atom on x.
        let memb_disj = disj.iter().find(|t| is_memb(t)).unwrap();
        let (mt, _) = super::memb_sides(cx.terms, *memb_disj);
        assert_eq!(mt, x);
        let eq_disj = disj.iter().find(|t| !is_memb(t)).unwrap();
        let (l, rr) = crate::wordeq::sides(cx.terms, *eq_disj);
        assert!(cx.terms.string_const_value(l) == Some("") || cx.terms.string_const_value(rr) == Some(""));
    }

    #[test]
    fn rule_s_head_split_clause_sequence() {
        // x ∈ [a-c]·(str.to_re "") — head-forced: S1..S4 in order, then fixpoint.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let r = Rex::Range('a' as u32, 'c' as u32);
        let m = memb_atom(&mut ctx, x, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &atoms };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 24);
        assert!(matches!(terminal, TCheck::Sat));
        // Rounds may interleave length axioms (len(h) enters the length seam).
        // Identify the S-clauses by SHAPE, order-independent:
        let is_memb = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App { op: Op::Builtin(BuiltinOp::StrInRe), .. }
            )
        };
        let is_dist = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App { op: Op::Builtin(BuiltinOp::Distinct), .. }
            )
        };
        // S1: guarded, two string EQUALITIES on x (one against "").
        let s1 = splits.iter().filter(|(a, g)| {
            *g && a.len() == 2 && a.iter().all(|&t| !is_memb(cx.terms, t) && !is_dist(cx.terms, t))
        });
        assert_eq!(s1.count(), 1, "exactly one S1 head split");
        // S2: the ONLY unguarded clause — [distinct(x,h·z), len(h)=1].
        let s2: Vec<_> = splits.iter().filter(|(a, g)| !*g && a.iter().any(|&t| is_dist(cx.terms, t))).collect();
        assert_eq!(s2.len(), 1, "exactly one unguarded witness canonicalization (S2)");
        // S3 + S4: guarded [distinct, str.in_re] clauses.
        let s34: Vec<_> = splits
            .iter()
            .filter(|(a, g)| *g && a.iter().any(|&t| is_dist(cx.terms, t)) && a.iter().any(|&t| is_memb(cx.terms, t)))
            .collect();
        assert_eq!(s34.len(), 2, "head-class (S3) + tail-membership (S4) clauses");
        // Their membership atoms sit on fresh terms (h resp. z·γ), not on x,
        // and their regex sides re-extract as constant regexes.
        for (atoms, _) in &s34 {
            let mt = atoms.iter().copied().find(|&t| is_memb(cx.terms, t)).unwrap();
            let (side, re_side) = super::memb_sides(cx.terms, mt);
            assert_ne!(side, x, "S3/S4 memberships are on fresh witnesses");
            assert!(crate::regex::extract_const_regex(cx.terms, re_side).is_some());
        }
    }

    #[test]
    fn empty_language_residual_conflicts() {
        // x ∈ re.none survives the pre-pass only when minted mid-search, but
        // the rule must still conflict on it directly.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let m = memb_atom(&mut ctx, x, &Rex::Empty);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &atoms };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (_, terminal) = run_rounds(&mut s, &mut cx, 8);
        assert!(matches!(terminal, TCheck::Conflict(_)));
    }

    #[test]
    fn fuel_exhaustion_yields_unknown() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let m = memb_atom(&mut ctx, x, &regex::star_range_test('a', 'c'));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &atoms };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        s.test_set_fuel(0);
        assert!(matches!(s.check(&mut cx, Effort::Full), TCheck::Unknown));
    }
}
```

Add the three tiny test-only Rex builders next to `test_az_star_term` in `regex.rs`:

```rust
#[cfg(test)]
pub(crate) fn rex_to_term_test(ctx: &mut Context, r: &Rex) -> TermId {
    rex_to_term(ctx, r)
}
#[cfg(test)]
pub(crate) fn lit_test(s: &str) -> Rex {
    lit_to_rex(s).expect("ascii test literal")
}
#[cfg(test)]
pub(crate) fn star_lit_test(s: &str) -> Rex {
    star(lit_test(s))
}
#[cfg(test)]
pub(crate) fn star_range_test(lo: char, hi: char) -> Rex {
    star(Rex::Range(lo as u32, hi as u32))
}
```

- [ ] **Step 2: Run tests to verify they fail to compile**

Run: `cargo test -p shinri-str memb:: 2>&1 | tail -10`
Expected: compile error — module `memb` has tests but no `memb_sides`/`memb_check`; `lib.rs` lacks `mod memb;`.

- [ ] **Step 3: Implement the pass**

(a) `crates/shinri-str/src/lib.rs`: add `mod memb;` to the module list; add the two fields after `emitted_splits`:

```rust
    /// Dedup for membership lemmas (slice 21): (string-side term, RegLan term
    /// of the residual Rex, rule tag 0=E / 1..=4=S1..S4). Monotone, like
    /// `emitted_splits` — a dedup hit means the clause is already learnt.
    emitted_memb: FxHashSet<(TermId, TermId, u8)>,
    /// Fresh witnesses minted by head splits, keyed by (x, residual regex
    /// term) so clauses S2..S4 reuse S1's h/z across rounds. Monotone.
    memb_wits: FxHashMap<(TermId, TermId), (TermId, TermId)>,
```

and the call site in `check`, immediately BEFORE the final `TCheck::Sat`:

```rust
        // ── Slice 21: membership pass (derivative unfolding) ─────────────────
        // Runs after word equations and disequalities so ground substitutions
        // are already merged. Returns Some on any emission/verdict; None ⟹
        // every membership is discharged, deduped, or skipped (unclean NF) —
        // the Sat fixpoint below is then backstopped by the model self-check.
        if let Some(res) = memb::memb_check(self, cx, &known, &all_cond_roots) {
            return res;
        }

        TCheck::Sat
```

(NOTE: `known` and `all_cond_roots` are the locals already computed at the top of `check`; the membership pass borrows them unchanged.)

(b) `crates/shinri-str/src/memb.rs` implementation (above the tests):

```rust
use crate::regex::{self, Rex};
use crate::{collect, normalize, side_clean, wordeq, StrSolver};
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::{ENodeId, EqLeaf};
use shinri_theory::{TCheck, TheoryCtx};

const RULE_E: u8 = 0;
const RULE_S1: u8 = 1;
const RULE_S2: u8 = 2;
const RULE_S3: u8 = 3;
const RULE_S4: u8 = 4;

/// The two children of a `str.in_re` atom: (string side, regex side).
pub(crate) fn memb_sides(terms: &Context, atom: TermId) -> (TermId, TermId) {
    match terms.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrInRe),
            args,
            ..
        } => {
            let ch = terms.children(*args);
            (ch[0], ch[1])
        }
        _ => panic!("memb_sides: expected str.in_re atom"),
    }
}

/// `str.++` of `atoms` (1 atom → itself; 0 → the empty literal).
fn mk_concat(terms: &mut Context, atoms: &[TermId]) -> TermId {
    match atoms.len() {
        0 => terms.mk_string_const(""),
        1 => atoms[0],
        _ => terms
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), atoms)
            .expect("str.++ well-sorted"),
    }
}

/// Register a freshly-minted split atom exactly like the F-split path does:
/// collect its len/str terms and mark any string equality as minted so the
/// length seam skips it.
fn register_atom(s: &mut StrSolver, terms: &mut Context, atom: TermId) {
    let mut seen = FxHashSet::default();
    collect::collect(terms, atom, &mut s.len_terms, &mut s.str_terms, &mut seen);
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
        args,
        ..
    } = terms.term_node(atom)
    {
        let kids = terms.children(*args).to_vec();
        if !kids.is_empty() && terms.sort_of(kids[0]) == terms.string_sort() {
            s.minted_eqs.insert(atom);
        }
    }
}

/// Spend fuel and emit one guarded/unguarded split, registering every atom.
fn emit_split(
    s: &mut StrSolver,
    terms: &mut Context,
    atoms: Vec<TermId>,
    guard: Option<shinri_core::Lit>,
) -> TCheck {
    for &a in &atoms {
        register_atom(s, terms, a);
    }
    if !s.fuel.spend() {
        return TCheck::Unknown;
    }
    TCheck::Split { atoms, guard }
}

/// The slice-21 membership pass. `Some(tcheck)` = a verdict or an emission
/// this round; `None` = nothing to do (all memberships discharged, deduped,
/// or skipped as unclean — the caller falls through to Sat, backstopped by
/// the post-solve self-check).
pub(crate) fn memb_check(
    s: &mut StrSolver,
    cx: &mut TheoryCtx,
    known: &[TermId],
    all_cond_roots: &FxHashSet<ENodeId>,
) -> Option<TCheck> {
    let membs: Vec<(TermId, shinri_core::Lit, bool)> = s.memb_true.clone();
    for (atom, lit, pos) in membs {
        let (t, re_t) = memb_sides(cx.terms, atom);
        // Constant by the solver fence (input) or by construction (minted);
        // a failure here is a seam break — fence to Unknown, never guess.
        let Some(mut rex) = regex::extract_const_regex(cx.terms, re_t) else {
            return Some(TCheck::Unknown);
        };
        if !pos {
            rex = regex::comp(rex); // t ∉ R ≡ t ∈ comp(R)
        }

        // ── Rule G: consume the ground NF prefix ─────────────────────────
        // Fully-cited NF (the diseq Case-2 pattern): expansion antecedents
        // are collected so a ground Conflict can cite them and stay UNGATED.
        let mut expand_ante: Vec<EqLeaf> = Vec::new();
        let Some(nf) =
            normalize::deep_normal_form_cited(cx.terms, cx.eq, known, t, &mut expand_ante)
        else {
            return Some(TCheck::Unknown); // non-convergent merge — sound bail
        };
        let mut cur = rex;
        let mut i = 0usize;
        let mut fenced = false;
        while i < nf.len() {
            let Some(w) = cx.terms.string_const_value(nf[i]).map(str::to_owned) else {
                break;
            };
            for c in w.chars() {
                cur = regex::deriv(c as u32, &cur);
                if regex::node_count(&cur) > regex::FUEL_NODE_CAP {
                    fenced = true;
                    break;
                }
            }
            if fenced {
                break;
            }
            i += 1;
        }
        if fenced {
            return Some(TCheck::Unknown);
        }
        if i == nf.len() {
            // Fully ground: nullability decides the atom.
            if regex::nullable(&cur) {
                continue; // discharged this round
            }
            let mut just = vec![EqLeaf::Asserted(lit)];
            just.extend(expand_ante.iter().copied());
            return Some(TCheck::Conflict(just));
        }

        // Residual: nf[i..] with a variable head. Guarded lemmas read the
        // NF, so they fire only over branch-independent substitutions —
        // the strictest gate (all_cond_roots), mirroring the global-lemma
        // posture. Skipped ⟹ revisited when clean; never a verdict.
        if !side_clean(cx.eq, cx.terms, t, all_cond_roots) {
            continue;
        }
        let residual_atoms: Vec<TermId> = nf[i..].to_vec();
        let residual = mk_concat(cx.terms, &residual_atoms);
        let x = residual_atoms[0];
        let cur_t = regex::rex_to_term(cx.terms, &cur);
        let guard = Some(lit.negate());

        // ── Rule S: head-forced `C · R''` — peel one char off `x` ────────
        if let Some(((lo, hi), tail_rex)) = regex::head_forced(&cur) {
            // S1: lit → x = "" ∨ x = h·z (fresh h, z; the F-split argument).
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S1)) {
                s.emitted_memb.insert((x, cur_t, RULE_S1));
                let h = wordeq::fresh_str(cx.terms, &mut s.fresh_ctr);
                let z = wordeq::fresh_str(cx.terms, &mut s.fresh_ctr);
                s.memb_wits.insert((x, cur_t), (h, z));
                let hz = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[h, z])
                    .expect("str.++ well-sorted");
                let e = cx.terms.mk_string_const("");
                let x_eps = cx.terms.mk_eq(x, e).expect("eq well-sorted");
                let x_hz = cx.terms.mk_eq(x, hz).expect("eq well-sorted");
                return Some(emit_split(s, cx.terms, vec![x_eps, x_hz], guard));
            }
            let &(h, z) = s
                .memb_wits
                .get(&(x, cur_t))
                .expect("S1 emitted ⟹ witnesses recorded");
            let hz = cx
                .terms
                .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[h, z])
                .expect("str.++ well-sorted");
            let dist = cx
                .terms
                .mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, hz])
                .expect("distinct well-sorted");
            // S2 (unguarded fresh-witness canonicalization): x=h·z → len(h)=1.
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S2)) {
                s.emitted_memb.insert((x, cur_t, RULE_S2));
                let lh = wordeq::len_of(cx.terms, h);
                let one = cx.terms.mk_numeral(
                    shinri_core::Rational::from_int(1i128.into()),
                    cx.terms.int_sort(),
                );
                let len1 = cx.terms.mk_eq(lh, one).expect("eq well-sorted");
                return Some(emit_split(s, cx.terms, vec![dist, len1], None));
            }
            // S3: lit ∧ x=h·z → h ∈ C.
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S3)) {
                s.emitted_memb.insert((x, cur_t, RULE_S3));
                let c_t = regex::rex_to_term(cx.terms, &Rex::Range(lo, hi));
                let m_h = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[h, c_t])
                    .expect("str.in_re well-sorted");
                return Some(emit_split(s, cx.terms, vec![dist, m_h], guard));
            }
            // S4: lit ∧ x=h·z → z·γ ∈ R''.
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S4)) {
                s.emitted_memb.insert((x, cur_t, RULE_S4));
                let mut tail_atoms = vec![z];
                tail_atoms.extend_from_slice(&residual_atoms[1..]);
                let tail_t = mk_concat(cx.terms, &tail_atoms);
                let tail_re = regex::rex_to_term(cx.terms, &tail_rex);
                let m_tail = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[tail_t, tail_re])
                    .expect("str.in_re well-sorted");
                return Some(emit_split(s, cx.terms, vec![dist, m_tail], guard));
            }
            continue; // fully unfolded at this level — wait for SAT/merges
        }

        // ── Rule E: class expansion (fundamental derivative equivalence)
        //    L(cur) = [ε if ν] ∪ ⋃_C C·L(∂_C cur) — single-atom disjuncts. ──
        if !s.emitted_memb.contains(&(residual, cur_t, RULE_E)) {
            s.emitted_memb.insert((residual, cur_t, RULE_E));
            let Some(classes) = regex::next_classes(&cur) else {
                return Some(TCheck::Unknown); // CLASS_SPLIT_CAP — fence
            };
            let mut disj: Vec<TermId> = Vec::new();
            if regex::nullable(&cur) {
                let e = cx.terms.mk_string_const("");
                disj.push(cx.terms.mk_eq(residual, e).expect("eq well-sorted"));
            }
            for (lo, hi) in classes {
                // ∂ at the class representative — exact across the class
                // (u32 space: surrogate classes included, never dropped).
                let d = regex::deriv(lo, &cur);
                if regex::node_count(&d) > regex::FUEL_NODE_CAP {
                    return Some(TCheck::Unknown);
                }
                if matches!(d, Rex::Empty) {
                    continue; // C·∅ = ∅ — a dead disjunct, dropping is exact
                }
                let shape = regex::concat(vec![Rex::Range(lo, hi), d]);
                let shape_t = regex::rex_to_term(cx.terms, &shape);
                disj.push(
                    cx.terms
                        .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[residual, shape_t])
                        .expect("str.in_re well-sorted"),
                );
            }
            if disj.is_empty() {
                // No ε, no live class: L(cur) = ∅ — the membership is
                // unsatisfiable. Fully-cited conflict (trigger + NF merges).
                let mut just = vec![EqLeaf::Asserted(lit)];
                just.extend(expand_ante.iter().copied());
                return Some(TCheck::Conflict(just));
            }
            return Some(emit_split(s, cx.terms, disj, guard));
        }
    }
    None
}
```

(c) Remove any transient `#[allow(dead_code)]` left on Task-1 items now that everything is called.

- [ ] **Step 4: Run the unit tests**

Run: `cargo test -p shinri-str 2>&1 | tail -15`
Expected: PASS — including all pre-existing wordeq/normalize/regex tests (the pass runs only when `memb_true` is non-empty, so existing string behavior is unperturbed).

- [ ] **Step 5: Add e2e unsat pins (the engine's first end-to-end wins)**

Append to `crates/shinri-solver/tests/script_e2e.rs`:

```rust
// Slice 21 (Task 3): derivative unfolding — unsat verdicts through the full
// solver. Sat-with-witness shapes need Task 4's model repair.
#[test]
fn in_re_unfold_unsat_disjoint_stars() {
    // x ∈ a* ∧ x ∈ b* ∧ len(x) ≥ 1 — the intersection above length 0 is empty.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (str.in_re x (re.* (str.to_re \"a\"))))\
         (assert (str.in_re x (re.* (str.to_re \"b\"))))\
         (assert (>= (str.len x) 1))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn in_re_unfold_unsat_concat_context() {
    // x = y·"b" ∧ x ∈ a* — every word of a* ends in 'a' (or is empty).
    expect(
        "(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)\
         (assert (= x (str.++ y \"b\")))\
         (assert (str.in_re x (re.* (str.to_re \"a\"))))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn in_re_unfold_unsat_literal_by_merge() {
    // x = "b0" via equality, x ∈ [a-z]+ — ground consumption over the merge.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (= x \"b0\"))\
         (assert (str.in_re x (re.+ (re.range \"a\" \"z\"))))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn in_re_unfold_negative_polarity_unsat() {
    // ¬(x ∈ Σ*) is unsatisfiable — comp(Σ*) = ∅.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (not (str.in_re x re.all)))(check-sat)",
        Verdict::Unsat,
    );
}
```

Run: `cargo test -p shinri-solver --test script_e2e in_re_unfold 2>&1 | tail -10`
Expected: PASS. If `in_re_unfold_unsat_disjoint_stars` returns Unknown instead of Unsat, the likely cause is fuel exhaustion before the conflicting expansions meet — check the round trace before touching budgets (budget values are frozen by the spec; the fix must be in rule efficiency, e.g. dedup keys or dead-disjunct dropping).

- [ ] **Step 6: Run the full string-side suites**

Run: `cargo test -p shinri-str -p shinri-solver 2>&1 | tail -15`
Expected: PASS everywhere. Watch specifically for regressions in `qfs_fuzz_corpus.rs` (the wrong-verdict corpus) — any change there is stop-the-line.

- [ ] **Step 7: fmt, clippy, commit**

```bash
cargo fmt
cargo clippy -p shinri-str -p shinri-solver --all-targets 2>&1 | tail -5
git add -A
git commit -m "feat(str): derivative-unfolding membership pass — rules G/E/S (slice 21)"
```

---

### Task 4: Membership-aware model repair

Free string variables carrying memberships get their model values from the capped word search instead of the default fill, BEFORE concat assembly (seeding), so assembled values stay consistent.

**Files:**
- Modify: `crates/shinri-str/src/model.rs` (`assign` seed parameter + seed builder)
- Modify: `crates/shinri-str/src/lib.rs` (`model_with` computes seeds)
- Test: unit test in `model.rs` tests; e2e sat pins in `script_e2e.rs`

**Interfaces:**
- Consumes: Task 1's `search_word`, `extract_const_regex`, `comp`, `inter`, `eval_membership`; Task 3's `memb_sides`; existing `class_len_in_model`, `class_member`, `assign`.
- Produces:
  - `pub fn assign(terms, eq, known, str_terms, m, seed: &FxHashMap<TermId, String>)` — extra final parameter; existing callers pass `&FxHashMap::default()`.
  - `pub(crate) fn memb_seeds(terms: &mut Context, eq: &mut EqualityEngine, known: &[TermId], membs: &[(TermId, bool)], m: &ModelBuilder) -> FxHashMap<TermId, String>` in `model.rs` (`membs` = (atom, polarity) pairs).

- [ ] **Step 1: Write the failing test**

In `crates/shinri-str/src/model.rs` `mod tests` (mirror the existing test setup there — the tests seed a `ModelBuilder` with arith lengths):

```rust
    // ── Task 4 (slice 21): membership-aware seeding ──────────────────────

    #[test]
    fn memb_seed_replaces_free_fill() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let re_t = crate::regex::test_az_star_term(&mut ctx);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let mut m = ModelBuilder::default();
        // Arith pinned len(x) = 3.
        let len_x = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        m.assign(len_x, ModelVal::Num(shinri_core::Rational::from_int(3i128.into())));
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        let w = seeds.get(&x).expect("free membership var must be seeded");
        assert_eq!(w.chars().count(), 3);
        assert!(w.chars().all(|c| c.is_ascii_lowercase()));
        // A var pinned by a class CONSTANT must NOT be seeded (not free).
        let ab = ctx.mk_string_const("ab");
        let xa = eq.intern(x);
        let ca = eq.intern(ab);
        let _ = eq.merge(xa, ca, shinri_theory::types::EqJust::Definitional);
        let seeds2 = memb_seeds(&mut ctx, &mut eq, &[x, ab], &[(atom, true)], &m);
        assert!(seeds2.is_empty(), "constant-pinned var is not repaired");
    }
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-str model:: 2>&1 | tail -10`
Expected: compile error — `memb_seeds` not found / `assign` arity.

- [ ] **Step 3: Implement**

(a) `model.rs` — extend `assign` with the seed parameter; seed the memo before valuing concats:

```rust
pub fn assign(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    str_terms: &[TermId],
    m: &mut ModelBuilder,
    seed: &FxHashMap<TermId, String>,
) {
    let mut memo: FxHashMap<TermId, String> = seed.clone();
    ...
```

(everything else in `assign` is unchanged — the memo pre-load means `value_of` returns the seeded word for those vars, and concat assembly composes it).

(b) `model.rs` — the seed builder:

```rust
/// Slice 21: words for FREE string variables carrying membership atoms.
/// A variable is repair-eligible iff it is a leaf (nullary uninterpreted)
/// whose class holds no constant and no concat (the `value_of` free path) —
/// anything else has its value dictated elsewhere and repair would fight it.
/// The word: `search_word` over the intersection of all its (polarity-
/// adjusted) Rex constraints at the class's model length. No word / cap hit
/// / extraction failure ⇒ no seed (the post-solve self-check backstops).
pub(crate) fn memb_seeds(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    membs: &[(TermId, bool)],
    m: &ModelBuilder,
) -> FxHashMap<TermId, String> {
    use crate::regex;
    let mut per_var: FxHashMap<TermId, Vec<regex::Rex>> = FxHashMap::default();
    for &(atom, pos) in membs {
        let (t, re_t) = crate::memb::memb_sides(terms, atom);
        let is_leaf = matches!(
            terms.term_node(t),
            TermNode::App { op: Op::Uninterpreted(_), args, .. }
                if terms.children(*args).is_empty()
        );
        if !is_leaf {
            continue;
        }
        let Some(mut rex) = regex::extract_const_regex(terms, re_t) else {
            continue;
        };
        if !pos {
            rex = regex::comp(rex);
        }
        per_var.entry(t).or_default().push(rex);
    }
    let mut out = FxHashMap::default();
    for (v, rexes) in per_var {
        // Free check: no constant and no concat in v's class.
        let pinned = class_member(terms, eq, known, v, |terms, mm| {
            (terms.string_const_value(mm).is_some() || is_concat(terms, mm)) && mm != v
        });
        if pinned.is_some() {
            continue;
        }
        let n = class_len_in_model(terms, eq, known, m, v);
        let goal = regex::inter(rexes);
        if let Some(w) = regex::search_word(&goal, n) {
            out.insert(v, w);
        }
    }
    out
}
```

(c) `lib.rs` `model_with` — compute seeds and thread them:

```rust
    pub(crate) fn model_with(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        let str_terms: Vec<TermId> = self.str_terms.iter().copied().collect();
        let mut known: Vec<TermId> = str_terms.clone();
        for &(atom, _) in &self.eq_true {
            let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);
            known.push(l);
            known.push(r);
        }
        // Slice 21: seed free membership variables with searched words so
        // concat assembly composes REPAIRED values, not default fills.
        let membs: Vec<(TermId, bool)> =
            self.memb_true.iter().map(|&(a, _, p)| (a, p)).collect();
        let seeds = model::memb_seeds(cx.terms, cx.eq, &known, &membs, m);
        model::assign(cx.terms, cx.eq, &known, &str_terms, m, &seeds);
    }
```

(d) Fix the other `assign` call sites (grep `model::assign` / `assign(` in `model.rs` tests) to pass `&FxHashMap::default()`.

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-str 2>&1 | tail -10`
Expected: PASS.

- [ ] **Step 5: e2e sat pins — the decided idioms**

Append to `script_e2e.rs`, and FLIP the Task-2 pin:

```rust
// Slice 21 (Task 4): sat with witnesses via membership-aware model repair.
#[test]
fn in_re_unfold_sat_plus_with_length() {
    // x ∈ [a-z]+ ∧ len(x) = 3: repair searches a length-3 word.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (str.in_re x (re.+ (re.range \"a\" \"z\"))))\
         (assert (= (str.len x) 3))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn in_re_unfold_sat_negative_polarity() {
    // ¬(x ∈ [a-z]*): comp is co-infinite; a witness like "0" exists.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (not (str.in_re x (re.* (re.range \"a\" \"z\")))))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn in_re_unfold_sat_under_boolean_structure() {
    // Memberships under or/not/ite — the atom is decided at whatever polarity
    // the SAT layer picks.
    expect(
        "(set-logic QF_S)(declare-fun x () String)(declare-fun b () Bool)\
         (assert (or (str.in_re x (re.+ (str.to_re \"q\"))) (= x \"zz\")))\
         (assert (ite b (= x \"zz\") (= x \"qq\")))(check-sat)",
        Verdict::Sat,
    );
}
```

Also update `in_re_symbolic_nonnullable_unknown_pre_engine` (Task 2): rename to `in_re_symbolic_nonnullable_sat` with `Verdict::Sat` and a comment `slice 21 Task 4: repair finds a [a-z]+ witness (was Unknown pre-repair)`.

Run: `cargo test -p shinri-solver --test script_e2e in_re 2>&1 | tail -10`
Expected: PASS. `get-value` on these witnesses is exercised by the oracle family's witness cross-check in Task 6.

- [ ] **Step 6: fmt, clippy, commit**

```bash
cargo fmt
cargo clippy -p shinri-str -p shinri-solver --all-targets 2>&1 | tail -5
git add -A
git commit -m "feat(str): membership-aware model repair via capped derivative word search (slice 21)"
```

---

### Task 5: Full e2e pin matrix + slice-20 pin flips

**Files:**
- Modify: `crates/shinri-solver/tests/script_e2e.rs`
- Modify: `crates/shinri-str/src/regex.rs` (ONE slice-19 module-test sub-case swap, see Step 2)

- [ ] **Step 1: Locate and flip the two slice-20 `Unknown` pins**

Grep `script_e2e.rs` for the slice-20 pins on `(re.* (re.range "a" "b"))` (neither-finite-nor-co-finite) and `str.in_re s re.allchar` (over-cap Σ). Both now decide:

- `(re.* (re.range "a" "b"))` membership for symbolic `s` → `Verdict::Sat` (nullable — even the pre-repair self-check accepts `s = ""`). Update the pin verdict and rewrite its comment: `slice 21: decided by derivative unfolding (was fenced → Unknown in slices 19–20)`.
- `str.in_re s re.allchar` → `Verdict::Sat` (Σ is ONE next-character class; S1..S4 + repair mint a length-1 witness). Same comment treatment.

Run each BEFORE editing to confirm the flip is real:
`cargo test -p shinri-solver --test script_e2e -- <pin_test_name> 2>&1 | tail -5` — expected: FAIL with `expected Unknown, got Sat` (the improvement), then edit, then PASS.

- [ ] **Step 2: Keep the slice-19 fence test testing a genuine fence**

`crates/shinri-str/src/regex.rs::non_ground_shapes_survive_to_fence` has a sub-case using a `re.*` shape that slice 21 now decides at the SOLVER level — but this unit test exercises `has_unreduced_regex` (the slice-19/20 REWRITE-pass fence predicate), which is unchanged, so it should still pass. Verify; if any sub-case instead asserts end-to-end fencing semantics, swap that sub-case to a symbolic-REGEX-side shape (`(str.in_re x L)` for a declared RegLan `L`) with a comment naming the slice-21 reason — the slice-20 deviation lesson applied proactively.

- [ ] **Step 3: Add the remaining matrix pins**

```rust
// Slice 21 (Task 5): completion of the verdict matrix.
#[test]
fn in_re_unfold_sat_getvalue_witness() {
    // get-value returns a genuine member of [a-z]+ of the pinned length.
    // (Exact expected output format: copy the get-value pin pattern used by
    // the slice-15/18 pins in this file.)
    expect_get_value_satisfies(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (str.in_re x (re.+ (re.range \"a\" \"z\"))))\
         (assert (= (str.len x) 2))(check-sat)(get-value (x))",
        |v| v.len() == 2 && v.chars().all(|c| c.is_ascii_lowercase()),
    );
}

#[test]
fn in_re_unfold_unknown_class_cap() {
    // > 64 classes: 33 disjoint single-char printable-ASCII ranges at
    // codepoints 33, 35, …, 97 → 66 range boundaries + the 0 cut = 67 > 64.
    let ranges: String = (0..33)
        .map(|i| {
            let a = char::from(b'!' + 2 * i as u8); // '!'(33) … 'a'(97), printable
            format!("(re.range \"{a}\" \"{a}\")")
        })
        .collect::<Vec<_>>()
        .join(" ");
    expect(
        &format!(
            "(set-logic QF_S)(declare-fun x () String)\
             (assert (str.in_re x (re.* (re.union {ranges}))))\
             (assert (>= (str.len x) 1))(check-sat)"
        ),
        Verdict::Unknown,
    );
}

#[test]
fn in_re_unfold_unknown_fuel_depth() {
    // A shape whose unfolding needs more than the 40-unit fuel budget:
    // a long forced-prefix language against an unconstrained variable
    // (each level costs E + S1..S4). ~10 levels exhausts fuel → Unknown.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (str.in_re x ((_ re.loop 12 12) (re.range \"a\" \"b\"))))\
         (assert (str.in_re x (re.+ (re.range \"a\" \"a\"))))(check-sat)",
        Verdict::Unknown,
    );
}

#[test]
fn in_re_unfold_interplay_diseq() {
    // Memberships and disequalities cooperate: x ∈ a{1,1} ⇒ x = "a";
    // x ≠ "a" contradicts.
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (str.in_re x ((_ re.loop 1 1) (str.to_re \"a\"))))\
         (assert (not (= x \"a\")))(check-sat)",
        Verdict::Unsat,
    );
}
```

Notes: `expect_get_value_satisfies` — if no such helper exists, write the pin with this file's existing get-value pin mechanism (grep `get-value` in the file; slices 15/18 added witness pins) rather than inventing a new helper. `in_re_unfold_unknown_fuel_depth`: if this decides within fuel (verdict Sat — both memberships are satisfiable together only if... `a^12` vs `a+` over `re.loop 12 12 (re.range "a" "b")` IS satisfiable by "aaaaaaaaaaaa"), the pin's PURPOSE is an `Unknown`-on-fuel shape: verify the observed verdict, and if the engine decides it, deepen the loop bound until fuel genuinely trips, keeping the comment accurate. Never pin a wrong verdict.

- [ ] **Step 4: Run the whole e2e suite**

Run: `cargo test -p shinri-solver --test script_e2e 2>&1 | tail -10`
Expected: PASS, no unrelated pin changed.

- [ ] **Step 5: fmt, commit**

```bash
cargo fmt
git add -A
git commit -m "test(str): slice-21 e2e verdict pins — unfolding matrix + slice-20 pin flips (slice 21)"
```

---

### Task 6: Differential oracle family `qfs_regex_unfold_matches_z3`

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs`

- [ ] **Step 1: Study the slice-20 family**

Read `qfs_regex_symbolic_matches_z3` (~line 1865) and its generator (the regex sexpr sampler ~line 700–870). The new family reuses the same harness conventions: `--features oracle` gate, unknown-tolerant comparison, witness cross-check on Sat, tally print, 0 disagreements assertion.

- [ ] **Step 2: Write the family**

Key differences from the slice-20 family (copy its body, then adjust):

- Seed: `const RU_SEED: u64 = 0x53_00_0000_0001;` — FIRST grep the file for `0x53` to confirm no collision; if taken, use the next free `0x5N_00_0000_0001`.
- Iterations: `const RU_N_ITERS: usize = 200;`
- Regex sampler: bias toward INFINITE/CO-INFINITE languages over the ASCII `{a,b,c}` alphabet — with depth ≤ 3, draw uniformly from: `(re.* X)`, `(re.+ X)`, `((_ re.loop lo hi) X)` with `lo ≤ hi ≤ 4`, `(re.comp X)`, `(re.union X Y)`, `(re.++ X Y)`, `(re.inter X Y)`, `(re.range "a" "c")`, `(str.to_re w)` for `w` a random word of length ≤ 2 over {a,b,c}.
- One symbolic string variable `x`; per iteration add 0–2 random side constraints drawn from: `(= x w)`, `(not (= x w))`, `(= x (str.++ w x2))` for a second variable `x2`, `(= (str.len x) n)` / `(>= (str.len x) n)` with `n ≤ 4`.
- The membership atom `(str.in_re x R)`, negation-wrapped with probability ~25%.
- Tally names: `n_sat / n_unsat / n_shinri_unknown / n_z3_unknown / n_guard_bailouts / n_witness`.
- Assertion: **0 disagreements**; print the tally line `qfs_regex_unfold_matches_z3: {RU_N_ITERS} iters — …` (exactly the slice-20 format with the new family name).

- [ ] **Step 3: Run the new family FOREGROUND**

Run: `cargo test -p shinri-solver --features oracle qfs_regex_unfold_matches_z3 -- --nocapture 2>&1 | tail -10`
Expected: PASS with a printed tally, 0 disagreements. Record the tally verbatim — it goes into the spec truth-up. Any disagreement is stop-the-line: minimize the failing script, reproduce with `z3` directly, and diagnose (systematic-debugging) before ANY further work.

- [ ] **Step 4: Re-run all pre-existing string oracle families FOREGROUND**

Run: `cargo test -p shinri-solver --features oracle qfs_ -- --nocapture 2>&1 | tail -40`
Expected: every family passes. Tallies identical to their committed values, with ONE sanctioned exception: `qfs_regex_symbolic_matches_z3`'s shinri-unknown count may DECREASE (the engine now decides more; generator and seed untouched). Any other movement is stop-the-line.

- [ ] **Step 5: fmt, commit**

```bash
cargo fmt
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_regex_unfold_matches_z3 differential oracle family (slice 21)"
```

---

### Task 7: Spec truth-up, final gates, PR

- [ ] **Step 1: Final local gates**

```bash
cargo fmt --check
cargo clippy --workspace --all-targets 2>&1 | tail -5
cargo test -p shinri-core -p shinri-parser -p shinri-str -p shinri-solver --features oracle 2>&1 | tail -15
```
Expected: all clean/PASS. (Do NOT run `cargo test --workspace` — CI covers it.)

- [ ] **Step 2: Spec truth-up**

Edit `docs/superpowers/specs/2026-07-13-shinri-slice21-regex-unfold-design.md`:
- `Status: IMPLEMENTED (slice 21 landed <date>).`
- Insert the oracle tally paragraph (slice-20 format): the new family's numbers verbatim from Task 6 Step 3, plus the `qfs_regex_symbolic_matches_z3` movement if any.
- Add a **Deviations from the spec** section listing every place the implementation diverged (clause encodings, cap values, pin adjustments, helper renames) — write "none" only if literally true.

```bash
git add docs/superpowers/specs/2026-07-13-shinri-slice21-regex-unfold-design.md
git commit -m "docs: slice-21 spec truth-up — IMPLEMENTED + oracle tally"
```

- [ ] **Step 3: Push and open the PR**

```bash
git push -u origin slice21-regex-unfold
gh pr create --title "Slice 21: derivative unfolding of symbolic str.in_re" \
  --body "$(cat <<'EOF'
## Summary
- Decide str.in_re(t, R) for symbolic strings against infinite/co-infinite constant regexes by lazy guarded Brzozowski-derivative unfolding in the string engine (rules G/E/S over the existing TCheck::Split channel)
- Membership-aware model repair (capped derivative word search) + extended post-solve self-check
- Narrowed regex presence fence; symbolic regex sides / RegLan relations still fence

## Testing
- Unit: classes/reverse-translation/word-search + engine-rule round tests
- E2e: verdict pin matrix incl. two slice-20 Unknown pins flipped to Sat
- Oracle: new family qfs_regex_unfold_matches_z3 (200 iters, 0 disagreements); all existing families unperturbed

Spec: docs/superpowers/specs/2026-07-13-shinri-slice21-regex-unfold-design.md
EOF
)"
```

Wait for CI (includes the ~50-min full workspace run and `cargo fmt --check`). Merge per repo convention once green.
