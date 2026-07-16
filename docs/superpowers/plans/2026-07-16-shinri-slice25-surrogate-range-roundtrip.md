# Slice 25 — Surrogate-Straddling Range Round-Trip Canonicalization: Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `extract_const_regex(rex_to_term(r)) == r` for every canonical `Rex` — so surrogate-straddling ranges (which `rex_to_term` must encode as a `re.diff` block gadget) survive the term↔Rex round-trip shape-intact, and the order-rewrite memberships that stall to Unknown today decide.

**Architecture:** Two exact interval-arithmetic normalizations in `crates/shinri-str/src/regex.rs` and nothing else: (a) the `union` smart constructor coalesces `Rex::Range` members; (b) `extract_const_regex`'s `ReDiff` arm computes interval differences directly when every operand is a character class, folding the minted surrogate-block gadget back to `Rex::Range(0xD800, 0xDFFF)`. No changes to `memb.rs`, `order.rs`, `model.rs`, `wordeq.rs`, `Fuel`, fences, or SAT budgets.

**Tech Stack:** Rust workspace (`cargo`); differential oracle vs z3 (`--features oracle`, z3 on PATH via mise).

**Spec:** `docs/superpowers/specs/2026-07-16-shinri-slice25-surrogate-range-roundtrip-design.md` — read it first; the corrected diagnosis and probe table there are the context for every task.

## Global Constraints

- Source changes live in `crates/shinri-str/src/regex.rs` ONLY (plus its in-file `mod tests`). Test additions also go in `crates/shinri-solver/tests/qfs_differential.rs`. Docs edits: the two spec files named in Task 5.
- `qfs_differential.rs` is `#![cfg(feature = "oracle")]` — without `--features oracle` it silently runs 0 tests. Every oracle command below carries the flag. Run oracle tests FOREGROUND with captured output; never claim a tally you didn't see printed.
- Oracle invocation shape: `cargo test -p shinri-solver --features oracle --test qfs_differential <test_name> -- --nocapture --exact`
- Run `cargo fmt --all -- --check` before EVERY commit (CI gates on it and fails fast; fix with `cargo fmt --all`).
- Do NOT run `cargo test --workspace` (~50 min; shinri-fp exhaustive). Iterate per-crate: `cargo test -p shinri-str`, `cargo test -p shinri-solver`, plus the oracle file.
- Alphabet constants (already in `regex.rs`): `MAX_CODE = 0x2FFFF`, surrogate block `SURR_LO = 0xD800` / `SURR_HI = 0xDFFF`. Endpoint policy (`range_rex`): a surrogate endpoint is legal only as `lo == 0xD800` or `hi == 0xDFFF`.
- Work on a branch (suggested: `slice25-surrogate-range-roundtrip`), commits per task, PR to `main` at the end.

---

### Task 1: Union range coalescing

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` — the `union` smart constructor (currently lines 86–110) and a new module-level `coalesce` helper next to it; tests in the existing `mod tests` (starts line 1024).

**Interfaces:**
- Produces: `fn coalesce(iv: Vec<(u32, u32)>) -> Vec<(u32, u32)>` (module-private) — sorts inclusive intervals by `lo` and merges overlapping/adjacent ones. Task 2's `class_intervals` calls it.
- Produces: `union(parts: Vec<Rex>) -> Rex` (signature unchanged) with the NEW output contract: coalesced `Range` members first, sorted by `lo`, then non-range members in first-appearance order, deduped.

- [ ] **Step 1: Write the failing test**

Add to `mod tests` in `regex.rs` (after `smart_constructors_canonicalize`):

```rust
#[test]
fn union_coalesces_ranges() {
    // Adjacent intervals merge ([a,b] ∪ [b+1,c] = [a,c]).
    assert_eq!(
        union(vec![Rex::Range(97, 99), Rex::Range(100, 105)]),
        Rex::Range(97, 105)
    );
    // Overlapping intervals merge.
    assert_eq!(
        union(vec![Rex::Range(97, 103), Rex::Range(100, 105)]),
        Rex::Range(97, 105)
    );
    // Contained interval collapses.
    assert_eq!(
        union(vec![Rex::Range(97, 120), Rex::Range(100, 105)]),
        Rex::Range(97, 120)
    );
    // Disjoint (gap > 1) stays split, sorted by lo regardless of input order.
    assert_eq!(
        union(vec![Rex::Range(110, 120), Rex::Range(97, 99)]),
        Rex::Union(vec![Rex::Range(97, 99), Rex::Range(110, 120)])
    );
    // The slice's motivating fold: lo..D7FF ∪ block ∪ E000..hi = lo..hi.
    assert_eq!(
        union(vec![
            Rex::Range(99, 0xD7FF),
            Rex::Range(0xD800, 0xDFFF),
            Rex::Range(0xE000, MAX_CODE)
        ]),
        Rex::Range(99, MAX_CODE)
    );
    // Mixed members: coalesced ranges FIRST (sorted), then non-range
    // members in first-appearance order. Deterministic under permutation
    // of the range members.
    let st = star(Rex::Range(0, MAX_CODE));
    assert_eq!(
        union(vec![st.clone(), Rex::Range(100, 105), Rex::Eps, Rex::Range(97, 99)]),
        Rex::Union(vec![Rex::Range(97, 105), st.clone(), Rex::Eps])
    );
    assert_eq!(
        union(vec![Rex::Range(97, 99), st.clone(), Rex::Range(100, 105), Rex::Eps]),
        Rex::Union(vec![Rex::Range(97, 105), st, Rex::Eps])
    );
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str union_coalesces_ranges -- --exact`
Expected: FAIL — first assertion gets `Rex::Union([Range(97,99), Range(100,105)])`, not `Range(97,105)`.

- [ ] **Step 3: Implement**

Add `coalesce` above `union` and replace `union`'s body:

```rust
/// Sort inclusive intervals by `lo` and merge overlapping or ADJACENT ones
/// (`[a,b] ∪ [b+1,c] → [a,c]`). Exact set arithmetic on character classes.
fn coalesce(mut iv: Vec<(u32, u32)>) -> Vec<(u32, u32)> {
    iv.sort_unstable();
    let mut out: Vec<(u32, u32)> = Vec::new();
    for (lo, hi) in iv {
        match out.last_mut() {
            Some((_, phi)) if lo <= phi.saturating_add(1) => *phi = (*phi).max(hi),
            _ => out.push((lo, hi)),
        }
    }
    out
}

pub(crate) fn union(parts: Vec<Rex>) -> Rex {
    // Slice 25: Range members are coalesced (sorted by lo, overlapping/
    // adjacent merged) and emitted FIRST; non-range members follow in
    // first-appearance order, deduped. Deterministic output — hash-consing
    // and the engine's dedup keys rely on `rex_to_term` determinism per Rex.
    fn add(p: Rex, ranges: &mut Vec<(u32, u32)>, others: &mut Vec<Rex>) {
        match p {
            Rex::Empty => {}
            Rex::Range(lo, hi) => ranges.push((lo, hi)),
            Rex::Union(inner) => {
                for q in inner {
                    add(q, ranges, others);
                }
            }
            other => {
                if !others.contains(&other) {
                    others.push(other);
                }
            }
        }
    }
    let mut ranges = Vec::new();
    let mut others = Vec::new();
    for p in parts {
        add(p, &mut ranges, &mut others);
    }
    let mut out: Vec<Rex> = coalesce(ranges)
        .into_iter()
        .map(|(lo, hi)| Rex::Range(lo, hi))
        .collect();
    out.extend(others);
    match out.len() {
        0 => Rex::Empty,
        1 => out.pop().expect("len 1"),
        _ => Rex::Union(out),
    }
}
```

- [ ] **Step 4: Run the new test, then the whole crate**

Run: `cargo test -p shinri-str union_coalesces_ranges -- --exact` — expected: PASS.
Run: `cargo test -p shinri-str` — expected: PASS. If any existing test pins the *shape* of a union of character classes that now coalesces (language-equal by construction), update that pin to the coalesced form and say so in the commit message. Do NOT weaken any language-level or verdict-level assertion.

- [ ] **Step 5: Run the solver crate's non-oracle tests**

Run: `cargo test -p shinri-solver` — expected: PASS (minted regex TermIds shift where unions coalesce; solver unit tests build expectations via the same constructors, so both sides move together).

- [ ] **Step 6: Format and commit**

```bash
cargo fmt --all -- --check
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): coalesce Range members in the union smart constructor (slice 25)"
```

---

### Task 2: Character-class interval algebra on the ReDiff extraction arm

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` — new helpers `class_intervals` and `interval_diff` (place them directly above `extract_const_regex`, currently line 759), and the `BuiltinOp::ReDiff` arm inside `extract_const_regex` (currently lines 778–787); tests in `mod tests`.

**Interfaces:**
- Consumes: `coalesce(Vec<(u32, u32)>) -> Vec<(u32, u32)>` from Task 1.
- Produces: `fn class_intervals(r: &Rex) -> Option<Vec<(u32, u32)>>` — `Some(sorted, coalesced intervals)` iff `r` is a character class (`Empty`, `Range`, or `Union` whose members are classes); `None` otherwise.
- Produces: `fn interval_diff(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)>` — `a \ b`, both inputs sorted+coalesced, output sorted+coalesced.

- [ ] **Step 1: Write the failing tests**

Add to `mod tests` in `regex.rs`:

```rust
#[test]
fn rediff_block_gadget_folds_to_range() {
    let mut ctx = Context::new();
    // rex_to_term encodes the surrogate block Range(D800,DFFF) as the
    // re.diff gadget (range_term); extraction must fold it back to the
    // Range it encodes — shape, not just language.
    let block = Rex::Range(0xD800, 0xDFFF);
    let t = rex_to_term(&mut ctx, &block);
    assert_eq!(extract_const_regex(&ctx, t), Some(block));
    // A full straddling range round-trips whole (gadget fold + Task 1's
    // union coalescing).
    let straddle = Rex::Range('c' as u32, 0xE000);
    let t = rex_to_term(&mut ctx, &straddle);
    assert_eq!(extract_const_regex(&ctx, t), Some(straddle));
    let full = Rex::Range('c' as u32, MAX_CODE);
    let t = rex_to_term(&mut ctx, &full);
    assert_eq!(extract_const_regex(&ctx, t), Some(full));
}

#[test]
fn rediff_ascii_interval_algebra() {
    let mut ctx = Context::new();
    // [a-z] \ [d-f] = [a-c] ∪ [g-z].
    let az = range_term_raw(&mut ctx, 'a' as u32, 'z' as u32);
    let df = range_term_raw(&mut ctx, 'd' as u32, 'f' as u32);
    let d = ctx
        .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[az, df])
        .unwrap();
    assert_eq!(
        extract_const_regex(&ctx, d),
        Some(Rex::Union(vec![
            Rex::Range('a' as u32, 'c' as u32),
            Rex::Range('g' as u32, 'z' as u32)
        ]))
    );
    // Subtracting a superset → Empty.
    let d2 = ctx
        .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[df, az])
        .unwrap();
    assert_eq!(extract_const_regex(&ctx, d2), Some(Rex::Empty));
}

#[test]
fn rediff_non_class_operand_keeps_inter_comp_shape() {
    let mut ctx = Context::new();
    // A non-class operand (Star) must keep today's inter/comp construction
    // bit-for-bit — the fast path fires ONLY when all operands are classes.
    let az = range_term_raw(&mut ctx, 'a' as u32, 'z' as u32);
    let inner = range_term_raw(&mut ctx, 'a' as u32, 'z' as u32);
    let star_t = ctx
        .mk_app(Op::Builtin(BuiltinOp::ReStar), &[inner])
        .unwrap();
    let d = ctx
        .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[az, star_t])
        .unwrap();
    assert_eq!(
        extract_const_regex(&ctx, d),
        Some(inter(vec![
            Rex::Range('a' as u32, 'z' as u32),
            comp(star(Rex::Range('a' as u32, 'z' as u32)))
        ]))
    );
}

#[test]
fn interval_diff_edges() {
    // b covers a's head; a's tail survives.
    assert_eq!(interval_diff(&[(5, 20)], &[(0, 9)]), vec![(10, 20)]);
    // b splits a in two.
    assert_eq!(interval_diff(&[(5, 20)], &[(8, 12)]), vec![(5, 7), (13, 20)]);
    // Multiple b intervals carve multiple holes.
    assert_eq!(
        interval_diff(&[(0, 30)], &[(5, 6), (10, 12), (28, 40)]),
        vec![(0, 4), (7, 9), (13, 27)]
    );
    // Disjoint b: a unchanged.
    assert_eq!(interval_diff(&[(5, 9)], &[(20, 30)]), vec![(5, 9)]);
    // Exact cover → empty.
    assert_eq!(interval_diff(&[(5, 9)], &[(5, 9)]), Vec::<(u32, u32)>::new());
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str rediff -- --nocapture` and `cargo test -p shinri-str interval_diff_edges -- --exact`
Expected: `interval_diff_edges` and the first two rediff tests FAIL TO COMPILE (`interval_diff`/fast path don't exist yet) or fail on shape (`rediff_block_gadget_folds_to_range` gets the `Inter/Comp` form). `rediff_non_class_operand_keeps_inter_comp_shape` pins current behavior and will pass once it compiles.

- [ ] **Step 3: Implement**

Add above `extract_const_regex`:

```rust
/// `Some(sorted, coalesced intervals)` iff `r` is a pure character class:
/// `Empty`, a `Range`, or a `Union` whose members are themselves classes.
/// `None` for anything else (the caller falls back to the generic path).
fn class_intervals(r: &Rex) -> Option<Vec<(u32, u32)>> {
    fn go(r: &Rex, out: &mut Vec<(u32, u32)>) -> Option<()> {
        match r {
            Rex::Empty => Some(()),
            Rex::Range(lo, hi) => {
                out.push((*lo, *hi));
                Some(())
            }
            Rex::Union(ps) => ps.iter().try_for_each(|p| go(p, out)),
            _ => None,
        }
    }
    let mut out = Vec::new();
    go(r, &mut out)?;
    Some(coalesce(out))
}

/// `a \ b` over sorted, coalesced inclusive interval sets; output sorted,
/// coalesced. Exact set arithmetic — the ReDiff fast path's core.
fn interval_diff(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    for &(alo, ahi) in a {
        let mut lo = alo;
        let mut live = true;
        for &(blo, bhi) in b {
            if bhi < lo {
                continue;
            }
            if blo > ahi {
                break;
            }
            if blo > lo {
                out.push((lo, blo - 1));
            }
            if bhi >= ahi {
                live = false;
                break;
            }
            lo = bhi + 1;
        }
        if live {
            out.push((lo, ahi));
        }
    }
    out
}
```

Replace the `BuiltinOp::ReDiff` arm in `extract_const_regex`:

```rust
BuiltinOp::ReDiff => {
    let rs = sub(ctx, &kids)?;
    // Character-class fast path (slice 25): when every operand is a
    // character class, compute the difference as intervals, so the
    // surrogate-block gadget minted by `range_term` re-extracts as the
    // Range it encodes (round-trip shape stability). Derived endpoints
    // are `operand endpoint ± 1`, which for non-interior inputs can only
    // be the block edges D800/DFFF — never an interior surrogate.
    if let Some(all) = rs
        .iter()
        .map(class_intervals)
        .collect::<Option<Vec<_>>>()
    {
        let mut it = all.into_iter();
        let mut acc = it.next().expect("re.diff arity >= 2");
        for b in it {
            acc = interval_diff(&acc, &b);
        }
        let parts: Vec<Rex> = acc
            .into_iter()
            .map(|(lo, hi)| {
                debug_assert!(
                    range_rex(lo as i128, hi as i128).is_some(),
                    "interval algebra minted an interior-surrogate endpoint"
                );
                Rex::Range(lo, hi)
            })
            .collect();
        return Some(union(parts));
    }
    // Left-associative difference: a \ b \ c = inter(a, comp(b), comp(c)).
    let mut rs = rs.into_iter();
    let first = rs.next().expect("arity >= 2");
    let mut parts = vec![first];
    for r in rs {
        parts.push(comp(r));
    }
    Some(inter(parts))
}
```

(Note the arm now computes `sub` once up front for both paths — same extraction work as before.)

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str` — expected: PASS, including all four new tests. Same adjudication rule as Task 1 for any shape-only pin the fold moves.

- [ ] **Step 5: Format and commit**

```bash
cargo fmt --all -- --check
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): fold character-class re.diff at extraction — surrogate block gadget re-extracts as Range (slice 25)"
```

---

### Task 3: Round-trip property test, consumer-shape pins, doc truth-up in regex.rs

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` — `mod tests` additions; the `Rex` enum invariant doc comment (lines 42–50); the `rex_to_term` doc comment (lines 413–418).

**Interfaces:**
- Consumes: everything from Tasks 1–2. No new production code — this task PINS the spec's acceptance property `extract_const_regex(rex_to_term(r)) == r`.

- [ ] **Step 1: Write the property test and consumer pins**

Add to `mod tests` in `regex.rs`:

```rust
/// Deterministic LCG (same recurrence as the differential harness's).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
}

/// A random legal Range: endpoints drawn from a pool mixing ASCII, the
/// block edges, and beyond-BMP codes; retried until `range_rex`'s endpoint
/// policy admits it (lo may be D800, hi may be DFFF, never interior).
fn arb_range(g: &mut Lcg) -> Rex {
    const POOL: [u32; 8] = [
        0,
        'a' as u32,
        'z' as u32,
        0xD7FF,
        0xD800,
        0xDFFF,
        0xE000,
        MAX_CODE,
    ];
    loop {
        let a = POOL[(g.next() % 8) as usize];
        let b = POOL[(g.next() % 8) as usize];
        let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
        if let Some(r @ Rex::Range(..)) = range_rex(lo as i128, hi as i128) {
            return r;
        }
    }
}

/// A random CANONICAL Rex — built exclusively through the smart
/// constructors, so the enum invariants hold by construction.
fn arb_rex(g: &mut Lcg, depth: u32) -> Rex {
    if depth == 0 {
        return match g.next() % 3 {
            0 => Rex::Eps,
            1 => Rex::Empty,
            _ => arb_range(g),
        };
    }
    match g.next() % 7 {
        0 => arb_range(g),
        1 => concat(vec![arb_rex(g, depth - 1), arb_rex(g, depth - 1)]),
        2 => union(vec![arb_rex(g, depth - 1), arb_rex(g, depth - 1)]),
        3 => inter(vec![arb_rex(g, depth - 1), arb_rex(g, depth - 1)]),
        4 => star(arb_rex(g, depth - 1)),
        5 => comp(arb_rex(g, depth - 1)),
        _ => {
            let lo = (g.next() % 3) as u32;
            let hi = lo + 1 + (g.next() % 3) as u32;
            loop_(arb_rex(g, depth - 1), lo, hi)
        }
    }
}

#[test]
fn roundtrip_extract_of_rex_to_term_is_identity() {
    // The slice's acceptance property: the term↔Rex round-trip is
    // SHAPE-stable (not merely language-preserving) for canonical Rex.
    let mut g = Lcg(0x5EED_25_5EED_25_01);
    let mut ctx = Context::new();
    for i in 0..500 {
        let r = arb_rex(&mut g, 4);
        let t = rex_to_term(&mut ctx, &r);
        assert_eq!(
            extract_const_regex(&ctx, t),
            Some(r.clone()),
            "round-trip changed shape at iter {i}: {r:?}"
        );
    }
}

#[test]
fn straddling_range_consumer_shapes_survive_roundtrip() {
    // The two consumer misses from the spec's Root cause: head_forced and
    // the bare-Range ground-out both key on Rex SHAPE after extraction.
    let mut ctx = Context::new();
    // Bare straddling range: stays a bare Range (memb.rs's ground-out arm).
    let bare = Rex::Range('c' as u32, 0xE000);
    let t = rex_to_term(&mut ctx, &bare);
    let back = extract_const_regex(&ctx, t).unwrap();
    assert!(matches!(back, Rex::Range(..)), "got {back:?}");
    // Straddling Range·Σ*: stays head-forced (memb.rs's Rule-S arm).
    let shape = concat(vec![
        Rex::Range('c' as u32, MAX_CODE),
        star(Rex::Range(0, MAX_CODE)),
    ]);
    let t = rex_to_term(&mut ctx, &shape);
    let back = extract_const_regex(&ctx, t).unwrap();
    assert_eq!(
        head_forced(&back),
        Some((('c' as u32, MAX_CODE), star(Rex::Range(0, MAX_CODE))))
    );
}
```

- [ ] **Step 2: Run to verify they pass**

Run: `cargo test -p shinri-str roundtrip -- --nocapture` and `cargo test -p shinri-str straddling_range_consumer_shapes_survive_roundtrip -- --exact`
Expected: PASS (Tasks 1–2 made them true). If the property test fails on some generated Rex, that is a REAL shape-stability hole — minimize the counterexample, fix in the constructors/extraction (never by weakening the test), and record the case as its own named unit test.

- [ ] **Step 3: Truth-up the two doc comments**

In the `Rex` enum invariant block (lines 42–50), replace the `Range` line:

```rust
/// - `Range(lo, hi)`: `lo <= hi <= MAX_CODE`; a surrogate endpoint is legal
///   only as `lo = 0xD800` / `hi = 0xDFFF` (block edges — `range_rex`'s
///   policy; interval algebra preserves this since derived endpoints are
///   `endpoint ± 1` of non-interior inputs). Interior surrogates may occur
///   strictly INSIDE a range (a straddling range covers the block).
```

In the `rex_to_term` doc comment (lines 413–418), replace the guarantee sentence:

```rust
/// Total (surrogate-endpoint ranges included). Guarantee (slice 25): the
/// minted term re-extracts (`extract_const_regex`) to the SAME Rex — shape
/// identity, not merely language equality; the surrogate-block diff gadget
/// folds back to its Range via the ReDiff character-class fast path.
/// Deterministic, so hash-consing gives TermId identity for equal Rex
/// inputs (the engine's dedup keys rely on this).
/// Pinned by `roundtrip_extract_of_rex_to_term_is_identity`.
```

- [ ] **Step 4: Run the crate suite, format, commit**

```bash
cargo test -p shinri-str
cargo fmt --all -- --check
git add crates/shinri-str/src/regex.rs
git commit -m "test(str): round-trip shape-identity property + consumer-shape pins; invariant truth-up (slice 25)"
```

---

### Task 4: End-to-end verdict pins (oracle file)

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` — append two tests after `targeted_str_order_single_char_left_decides` (currently line 3817–3825).

**Interfaces:**
- Consumes: the file's existing helpers — `expect(src: &str, want: Verdict)` (line 2543; asserts shinri's verdict AND cross-checks z3 when `want != Unknown`) and `shinri_verdict(src: &str) -> Verdict` (line 82; shinri only).

- [ ] **Step 1: Write the pins**

```rust
#[test]
fn targeted_str_order_single_char_left_free_decides() {
    // Slice 25 hard guarantee: constant-on-LEFT over a FULLY-FREE s decides
    // Sat. Pre-slice these were sound Unknowns — the minted membership's
    // Range(m+1, MAX_CODE) straddles the surrogate block, and the straddle
    // lost its Range shape across the term↔Rex round-trip (slice-25 spec,
    // Root cause). Both operators, plus length-pinned variants (the probe
    // rows that were Unknown even WITH length pinned).
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.<= \"b\" s))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))\
         (assert (= (str.len s) 1))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))\
         (assert (= (str.len s) 2))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_straddling_range_membership_decides() {
    // User-written surrogate-straddling re.range memberships (the probe-19/22
    // shapes). Raw U+E000 character in the literal — the text frontend does
    // not decode \u{...} escapes (slice-24 spec §6 note), and z3 WOULD decode
    // them, so the same source would mean different things to each solver;
    // shinri-only verdicts here (the sat model is validated by the post-solve
    // self-check; z3 coverage of this fragment rides the ASCII families).
    let bare = format!(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.range \"c\" \"{}\")))(check-sat)",
        '\u{E000}'
    );
    assert_eq!(shinri_verdict(&bare), Verdict::Sat, "bare straddle, free s");
    let under_concat = format!(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.++ (re.range \"c\" \"{}\") (re.* re.allchar))))\
         (check-sat)",
        '\u{E000}'
    );
    assert_eq!(
        shinri_verdict(&under_concat),
        Verdict::Sat,
        "straddle under concat, free s"
    );
    let len_pinned = format!(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.++ (re.range \"c\" \"{}\") (re.* re.allchar))))\
         (assert (= (str.len s) 1))(check-sat)",
        '\u{E000}'
    );
    assert_eq!(
        shinri_verdict(&len_pinned),
        Verdict::Sat,
        "straddle under concat, len pinned"
    );
}
```

- [ ] **Step 2: Run the pins (foreground, oracle feature)**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_str_order_single_char_left_free_decides -- --exact --nocapture`
Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_straddling_range_membership_decides -- --exact --nocapture`
Expected: PASS. If any pin still returns Unknown, STOP — do not weaken the pin to Unknown; reproduce with a CLI probe (`cargo build -p shinri-cli`, feed the same script to `target/debug/shinri`), find the remaining stall, and surface it for adjudication before proceeding.

- [ ] **Step 3: Verify the standing gap pin still holds**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_str_order_symbolic_pair_known_gap -- --exact --nocapture`
Expected: PASS (two-symbolic comparison stays a sound Unknown — this slice must not touch it).

- [ ] **Step 4: Format and commit**

```bash
cargo fmt --all -- --check
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): pin free-variable str-order and user-written straddling-range verdicts (slice 25)"
```

---

### Task 5: Oracle family re-runs, tally adjudication, spec truth-up

**Files:**
- Modify: `docs/superpowers/specs/2026-07-16-shinri-slice25-surrogate-range-roundtrip-design.md` (Status → IMPLEMENTED + truth-up section with the tallies you SAW).

**Interfaces:**
- Consumes: everything landed in Tasks 1–4. No production code.

- [ ] **Step 1: Re-run the three families the spec expects to MOVE (foreground, captured output)**

```bash
cargo test -p shinri-solver --features oracle --test qfs_differential qfs_str_order_single_char_matches_z3 -- --exact --nocapture
cargo test -p shinri-solver --features oracle --test qfs_differential qfs_str_order_matches_z3 -- --exact --nocapture
cargo test -p shinri-solver --features oracle --test qfs_differential qfs_to_code_range -- --exact --nocapture
```

Expected: all PASS (a disagreement aborts the test — 0 disagreements is enforced by assertion). Record the printed tallies verbatim. Adjudication bar (spec §4):
- `qfs_str_order_single_char_matches_z3`: shinri-unknown substantially below the pre-slice 128/200 (pre-slice baseline: 54 sat / 18 unsat / 128 shinri-unknown / 0 / 0).
- `qfs_str_order_matches_z3` (pre-slice: 54 / 80 / 66) and `qfs_to_code_range` (pre-slice: 28 / 105 / 67, 26 witnesses): movement ONLY in the unknown→decided direction. ANY decided verdict flipping, or an unknown count going UP, is a finding to adjudicate — stop and investigate, never wave through.

- [ ] **Step 2: Run the full differential file**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture`
Expected: every test passes (pre-slice: 62/62; Task 4 added 2). Families outside the three above expected tally-unchanged; adjudicate any movement.

- [ ] **Step 3: Re-run Step 1's three families once more**

Same three commands as Step 1. Expected: bit-for-bit identical tallies (fixed seeds — the house's reproducibility check).

- [ ] **Step 4: Per-crate suites**

```bash
cargo test -p shinri-str
cargo test -p shinri-solver
```

Expected: PASS.

- [ ] **Step 5: Truth-up the slice-25 spec**

In `docs/superpowers/specs/2026-07-16-shinri-slice25-surrogate-range-roundtrip-design.md`: change `Status: DRAFT` to `Status: IMPLEMENTED (2026-07-16). See "Implementation notes (truth-up)" at the end.` and append an `## Implementation notes (truth-up)` section recording: the commits, the observed post-slice tallies for all three moved families (verbatim from Step 1/3 output, noting the two identical runs), the full-file count, and any adjudicated deviations or liberties taken (or "none").

- [ ] **Step 6: Format check and commit docs**

```bash
cargo fmt --all -- --check
git add docs/superpowers/specs/2026-07-16-shinri-slice25-surrogate-range-roundtrip-design.md
git commit -m "docs: slice-25 spec truth-up (IMPLEMENTED) — surrogate range round-trip (slice 25)"
```

---

## Completion

All tasks done → use superpowers:finishing-a-development-branch (PR to `main`, house pattern: `slice25-surrogate-range-roundtrip` branch).
