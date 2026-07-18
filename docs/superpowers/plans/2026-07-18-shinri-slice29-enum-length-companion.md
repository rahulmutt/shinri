# Slice 29 — Enumeration↔Length Exact-Length Companion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Conjoin an entailed exact-length companion onto the slice-20 finite-enumeration rewrite so `s ∈ [0-9] ∧ len(s) = 2` (and kin) refute fuel-free in arith — cashing the slice-22 known gap `targeted_to_code_range_length_seam_known_gap`.

**Architecture:** One new private helper in `crates/shinri-str/src/regex.rs` (`conjoin_len_fact`) called from the finite branch of `try_rewrite_symbolic_in_re`, rewriting `t ∈ R` to `(and (⋁ t = wᵢ) (⋁ len(t) = ℓⱼ))` over the distinct enumerated word lengths (code-point counted, capped at 4 distinct lengths). Co-finite branch untouched. Everything downstream is unchanged — the companion is an entailed conjunct, so the rewrite stays a full equivalence at any polarity.

**Tech Stack:** Rust workspace (`mise install` provisions rust, nextest, z3). Spec: `docs/superpowers/specs/2026-07-18-shinri-slice29-enum-length-companion-design.md`.

## Global Constraints

- Blocking-tier test budget 10–15 min; nothing added here is long-running.
- Oracle differential tests are feature-gated: **without `--features oracle` they silently run 0 tests** — every `qfs_differential` invocation in this plan carries the flag. Run them FOREGROUND with captured output.
- `cargo fmt --all` before every push (CI gates on `fmt --check`); `cargo clippy --workspace --all-targets -- -D warnings` must be clean.
- Pure-Rust mandate: no new dependencies.
- Dump-and-diff acceptance (spec §3): every base→fix verdict flip must be `Unknown → decided`; any `decided → Unknown`, any `sat ↔ unsat`, or any bailout increase is a stop-the-line regression — do not proceed; report it.
- Feature work on branch `slice29-enum-length-companion`, PR to `main`, merge with a merge commit when CI is green, then delete the branch (remote and local).

---

### Task 1: `conjoin_len_fact` — companion at the finite-enumeration rewrite (`regex.rs`)

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (finite branch of `try_rewrite_symbolic_in_re`, ~line 1199; new helper + const near `mk_eq_disjunction`, ~line 1209; unit tests in the `mod tests` section, existing test `symbolic_finite_atom_rewrites_to_eq_disjunction` ~line 2064 plus new tests after ~line 2189)

**Interfaces:**
- Consumes: `enum_lang` / `Words` (regex.rs:826,856), `mk_eq_disjunction` (regex.rs:1209), `crate::wordeq::len_of(terms: &mut Context, t: TermId) -> TermId` (wordeq.rs:38), `Context::{mk_numeral, mk_eq, mk_app, int_sort}`, `shinri_core::Rational`.
- Produces: `fn conjoin_len_fact(ctx: &mut Context, t: TermId, ws: &Words, disj: TermId) -> TermId` and `const LEN_FACT_DISTINCT_CAP: usize = 4` (both private to regex.rs). Rewrite output shape for the finite branch becomes `(and <disjunction> <len-fact>)` when the companion fires; unchanged shape when skipped (empty word set, or > 4 distinct lengths).

- [ ] **Step 1: Create the slice branch**

```bash
git -C /workspace switch -c slice29-enum-length-companion main
```

- [ ] **Step 2: Update the existing shape test and write the new failing tests**

In `crates/shinri-str/src/regex.rs` tests module, first add a helper next to `eq_disjunct_values` (~line 2041):

```rust
    /// Unwrap the slice-29 `(and disj len-fact)` companion wrapper.
    fn unwrap_len_companion(ctx: &Context, t: TermId) -> (TermId, TermId) {
        let TermNode::App {
            op: Op::Builtin(BuiltinOp::And),
            args,
            ..
        } = ctx.term_node(t)
        else {
            panic!("expected (and disj len-fact), got {:?}", ctx.term_node(t));
        };
        let kids = ctx.children(*args).to_vec();
        assert_eq!(kids.len(), 2, "companion And must be binary");
        (kids[0], kids[1])
    }
```

Replace the body of `symbolic_finite_atom_rewrites_to_eq_disjunction` (~line 2064) — the finite branch now wraps in the companion And, including the singleton case:

```rust
    #[test]
    fn symbolic_finite_atom_rewrites_to_eq_disjunction() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let b = slit(&mut ctx, "b");
        let re_a = to_re(&mut ctx, a);
        let re_b = to_re(&mut ctx, b);
        let un = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[re_a, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, s, un);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(!has_unreduced_regex(&ctx, &out), "atom must be rewritten");
        // Slice 29: the finite rewrite is `(and (⋁ s = wᵢ) len-fact)`.
        let (disj, fact) = unwrap_len_companion(&ctx, out[0]);
        let mut vals = eq_disjunct_values(&ctx, disj);
        vals.sort();
        assert_eq!(vals, vec!["a".to_owned(), "b".to_owned()]);
        // Both words have length 1 → the fact is the bare `(= (str.len s) 1)`
        // (hash-consing makes the expected term id an identity check).
        let lt = crate::wordeq::len_of(&mut ctx, s);
        let int_s = ctx.int_sort();
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
        let expected = ctx.mk_eq(lt, one).unwrap();
        assert_eq!(fact, expected);

        // Singleton language: bare equality inside the companion, no Or.
        let atom = in_re(&mut ctx, s, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        let (disj, fact) = unwrap_len_companion(&ctx, out[0]);
        assert_eq!(eq_disjunct_values(&ctx, disj), vec!["a".to_owned()]);
        assert_eq!(fact, expected);
    }
```

Append the new tests after `symbolic_rewrite_keeps_unrelated_termids` (~line 2189):

```rust
    // ── Task 1 (slice 29): exact-length companion ────────────────────────

    #[test]
    fn gappy_length_set_emits_or_of_length_eqs() {
        // {"a", "abc"} → distinct lengths {1, 3} → `(or (= len 1) (= len 3))`
        // in BTreeSet (ascending) order.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let abc = slit(&mut ctx, "abc");
        let re_a = to_re(&mut ctx, a);
        let re_abc = to_re(&mut ctx, abc);
        let un = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[re_a, re_abc])
            .unwrap();
        let atom = in_re(&mut ctx, s, un);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        let (_disj, fact) = unwrap_len_companion(&ctx, out[0]);
        let lt = crate::wordeq::len_of(&mut ctx, s);
        let int_s = ctx.int_sort();
        let n1 = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
        let n3 = ctx.mk_numeral(shinri_core::Rational::from_int(3i128.into()), int_s);
        let e1 = ctx.mk_eq(lt, n1).unwrap();
        let e3 = ctx.mk_eq(lt, n3).unwrap();
        let expected = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[e1, e3]).unwrap();
        assert_eq!(fact, expected);
    }

    #[test]
    fn companion_length_counted_in_code_points() {
        // "\u{2FFFF}b" is 2 SMT-LIB code points (and 5 UTF-8 bytes): the
        // companion must say len = 2, never a byte count. U+2FFFF == MAX_CODE
        // is in-alphabet, so no fence fires.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let w = slit(&mut ctx, "\u{2FFFF}b");
        let re_w = to_re(&mut ctx, w);
        let atom = in_re(&mut ctx, s, re_w);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        let (_disj, fact) = unwrap_len_companion(&ctx, out[0]);
        let lt = crate::wordeq::len_of(&mut ctx, s);
        let int_s = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_core::Rational::from_int(2i128.into()), int_s);
        let expected = ctx.mk_eq(lt, two).unwrap();
        assert_eq!(fact, expected);
    }

    #[test]
    fn distinct_length_cap_skips_companion() {
        // {"a","aa","aaa","aaaa","aaaaa"} → 5 distinct lengths >
        // LEN_FACT_DISTINCT_CAP (4) → NO companion: the rewrite keeps the
        // pre-slice-29 bare-disjunction shape (skipping the implied fact is
        // always sound — today's behavior).
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let res: Vec<TermId> = ["a", "aa", "aaa", "aaaa", "aaaaa"]
            .iter()
            .map(|w| {
                let l = slit(&mut ctx, w);
                to_re(&mut ctx, l)
            })
            .collect();
        let un = ctx.mk_app(Op::Builtin(BuiltinOp::ReUnion), &res).unwrap();
        let atom = in_re(&mut ctx, s, un);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        // Directly a disjunction — `eq_disjunct_values` panics on And.
        let mut vals = eq_disjunct_values(&ctx, out[0]);
        vals.sort();
        assert_eq!(
            vals,
            vec![
                "a".to_owned(),
                "aa".to_owned(),
                "aaa".to_owned(),
                "aaaa".to_owned(),
                "aaaaa".to_owned()
            ]
        );
    }
```

Note: `symbolic_cofinite_atom_rewrites_to_negated_disjunction` and `symbolic_zero_word_languages_fold_to_bool_consts` must keep passing UNCHANGED — the co-finite branch and the empty-set bool fold get no companion.

- [ ] **Step 3: Run the tests to verify they fail**

```bash
cargo nextest run -p shinri-str regex::tests::symbolic_finite_atom_rewrites_to_eq_disjunction regex::tests::gappy_length_set_emits_or_of_length_eqs regex::tests::companion_length_counted_in_code_points regex::tests::distinct_length_cap_skips_companion
```

Expected: FAIL — `symbolic_finite_atom_rewrites_to_eq_disjunction` and the two companion tests panic in `unwrap_len_companion` ("expected (and disj len-fact)"); `distinct_length_cap_skips_companion` passes trivially pre-change (shape already bare) — that is fine, it is the regression guard for the cap.

- [ ] **Step 4: Implement the companion**

In `crates/shinri-str/src/regex.rs`, change the finite branch of `try_rewrite_symbolic_in_re` (~line 1199) from:

```rust
    if let Some(ws) = enum_lang(&rex) {
        return Some(mk_eq_disjunction(ctx, kids[0], &ws, false));
    }
```

to:

```rust
    if let Some(ws) = enum_lang(&rex) {
        let disj = mk_eq_disjunction(ctx, kids[0], &ws, false);
        return Some(conjoin_len_fact(ctx, kids[0], &ws, disj));
    }
```

Then add, right after `mk_eq_disjunction` (~line 1232):

```rust
/// Slice 29: max distinct word lengths for which the entailed exact-length
/// companion is conjoined onto the finite-enumeration rewrite. Beyond the
/// cap the companion is skipped entirely — it is an implied fact, so
/// skipping is always sound (merely today's behavior); the cap bounds the
/// added SAT burden.
const LEN_FACT_DISTINCT_CAP: usize = 4;

/// Slice 29: conjoin the entailed exact-length fact onto the finite
/// enumeration rewrite: `t ∈ W ≡ (⋁ t = wᵢ) ∧ (⋁ len(t) = ℓⱼ)` over the
/// DISTINCT word lengths `ℓⱼ` of `W`, counted in code points (`chars()` —
/// every enumerated character is in-alphabet by the `enum_lang` fences, so
/// Rust chars = SMT-LIB code points). The companion is entailed by the
/// disjunction, so the conjunction preserves the slice-20 equivalence at
/// any polarity. It closes the enumeration↔length seam WITHOUT fuel:
/// refuting an independent `str.len` constraint no longer requires the SAT
/// layer to refute wᵢ-disjuncts one at a time, each costing length-axiom
/// emissions from the shared fuel (the slice-22 known-gap cliff: fuel 40
/// dies at 9 disjuncts; `[0-9]` has 10). The co-finite branch gets no
/// companion (a complement has min length 0 and no finite max).
fn conjoin_len_fact(ctx: &mut Context, t: TermId, ws: &Words, disj: TermId) -> TermId {
    if ws.is_empty() {
        return disj; // already folded to `false` — nothing to strengthen
    }
    let lens: BTreeSet<usize> = ws.iter().map(|w| w.chars().count()).collect();
    if lens.len() > LEN_FACT_DISTINCT_CAP {
        return disj;
    }
    let lt = crate::wordeq::len_of(ctx, t);
    let int_s = ctx.int_sort();
    let eqs: Vec<TermId> = lens
        .into_iter()
        .map(|l| {
            let n = ctx.mk_numeral(shinri_core::Rational::from_int((l as i128).into()), int_s);
            ctx.mk_eq(lt, n).expect("well-sorted length equality")
        })
        .collect();
    let fact = if eqs.len() == 1 {
        eqs[0]
    } else {
        ctx.mk_app(Op::Builtin(BuiltinOp::Or), &eqs)
            .expect("well-sorted disjunction")
    };
    ctx.mk_app(Op::Builtin(BuiltinOp::And), &[disj, fact])
        .expect("well-sorted conjunction")
}
```

- [ ] **Step 5: Run the crate suite to verify green**

```bash
cargo nextest run -p shinri-str
```

Expected: PASS, including the four Step-2 tests, the untouched co-finite/bool-fold tests, and the pre-existing 197-test baseline. If any OTHER test in the crate fails on the new output shape, inspect it: a test asserting the finite-branch shape is updated to unwrap the companion (same pattern as Step 2); a genuine behavior regression is a stop-the-line finding.

- [ ] **Step 6: Format and commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): slice29 — conjoin entailed exact-length companion onto the finite-enumeration rewrite (distinct code-point lengths, cap 4; co-finite branch untouched)"
```

---

### Task 2: End-to-end pins — flip the slice-22 gap, pin the guards (`qfs_differential.rs`)

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (`targeted_to_code_range_length_seam_known_gap` ~line 3418–3450; new tests after it; possibly `targeted_regex_bare_range_multi_atom_residual_stays_unknown` ~line 3400–3416)

**Interfaces:**
- Consumes: Task 1's companion (via the solver pipeline — no new API); test helpers `expect(src, want)` (qfs_differential.rs:2548, asserts shinri verdict AND cross-checks z3 when decided) and `shinri_verdict` (qfs_differential.rs:82).
- Produces: renamed test `targeted_to_code_range_length_seam_now_decides`; new tests `targeted_enum_gappy_length_set_unsat`, `targeted_enum_length_companion_guards`. Task 4's truth-up cites these names.

- [ ] **Step 1: Flip the known-gap pin**

Replace the doc comment and test at ~line 3418–3450 (`targeted_to_code_range_length_seam_known_gap`) with:

```rust
/// Slice 29 FLIP (was `targeted_to_code_range_length_seam_known_gap`,
/// slice 22): the finite-enumeration rewrite now conjoins the entailed
/// exact-length companion (`s ∈ [0-9] ⇒ len(s) = 1`), so an
/// independently-asserted `len(s) = 2` refutes in arith — fuel-free, no
/// per-disjunct SAT churn (the old failure: refuting the 10 enumerated
/// disjuncts one at a time exhausted the shared fuel of 40 at the ninth).
/// Both the `to_code` gadget form and the `to_code`-free control decide
/// Unsat; z3 agrees (cross-checked by `expect`).
#[test]
fn targeted_to_code_range_length_seam_now_decides() {
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (>= (str.to_code s) 48))(assert (<= (str.to_code s) 57))\
         (assert (= (str.len s) 2))(check-sat)",
        Verdict::Unsat,
    );
    // Control: the same language, `to_code`-free.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.range \"0\" \"9\")))\
         (assert (= (str.len s) 2))(check-sat)",
        Verdict::Unsat,
    );
}
```

- [ ] **Step 2: Add the new pins**

Insert directly after the flipped test:

```rust
/// Slice 29: the companion is EXACT (distinct lengths), not min/max bounds:
/// `s ∈ {"a","abc"} ∧ len(s) = 2` is Unsat even though 1 ≤ 2 ≤ 3 — a
/// bounds-only companion could not decide this (the anti-alternative-B pin
/// from the design).
#[test]
fn targeted_enum_gappy_length_set_unsat() {
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.union (str.to_re \"a\") (str.to_re \"abc\"))))\
         (assert (= (str.len s) 2))(check-sat)",
        Verdict::Unsat,
    );
}

/// Slice 29 guards: the companion must not over-fire.
#[test]
fn targeted_enum_length_companion_guards() {
    // Consistent length: stays Sat.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.range \"0\" \"9\")))\
         (assert (= (str.len s) 1))(check-sat)",
        Verdict::Sat,
    );
    // Negative polarity: the rewrite is an equivalence under Not, so
    // ¬(s ∈ [0-9]) ∧ s = "3" refutes (the companion's conjuncts are both
    // true at s = "3", so the negation is false).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (not (str.in_re s (re.range \"0\" \"9\"))))\
         (assert (= s \"3\"))(check-sat)",
        Verdict::Unsat,
    );
    // Co-finite side untouched: ¬(s ∈ [0-9]) ∧ len(s) = 2 is Sat.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (not (str.in_re s (re.range \"0\" \"9\"))))\
         (assert (= (str.len s) 2))(check-sat)",
        Verdict::Sat,
    );
}
```

- [ ] **Step 3: Run the targeted tests (oracle feature ON, foreground, captured output)**

```bash
cargo nextest run -p shinri-solver --features oracle --test qfs_differential targeted_to_code_range_length_seam targeted_enum_gappy targeted_enum_length_companion
```

Expected: 3 tests PASS (each `expect` on a decided verdict also cross-checks z3 inline). If the negative-polarity guard comes back Unknown instead of Unsat: that is sound-but-weaker, NOT a soundness bug — investigate briefly (one SAT branch must refute `¬(len(s)=1)` given `s = "3"`); if it genuinely does not close, change that one `expect(..., Verdict::Unsat)` to `assert_eq!(shinri_verdict(...), Verdict::Unknown)` with a comment explaining the observed residual, and record it for the Task 4 truth-up. A wrong Sat there is stop-the-line.

- [ ] **Step 4: Re-examine the slice-25 multi-atom residual pin**

```bash
cargo nextest run -p shinri-solver --features oracle --test qfs_differential targeted_regex_bare_range_multi_atom_residual
```

- If it PASSES (still Unknown): leave it untouched; note "no cascade" for the truth-up.
- If it FAILS with shinri now answering `Unsat` (its doc comment records z3-confirmed UNSAT — the companion gives `len(s·"a") = 1`, forcing `s = ""` and refuting `"a" ∈ [x-z]` per disjunct): rename it to `targeted_regex_bare_range_multi_atom_residual_now_decides`, change the assertion to `expect(..., Verdict::Unsat)`, and update its doc comment to say slice 29's companion closed it. Any OTHER outcome (wrong Sat) is stop-the-line.

- [ ] **Step 5: Verify the old test name is gone, format, commit**

```bash
grep -c "targeted_to_code_range_length_seam_known_gap" crates/shinri-solver/tests/qfs_differential.rs
```

Expected: `0`.

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): slice29 pins — flip to_code_range_length_seam to now_decides; gappy exact-length pin; companion polarity/consistency guards"
```

---

### Task 3: Oracle differential + per-iteration dump-and-diff (temporary instrumentation, NOT committed)

**Files:**
- No committed changes (temporary uncommitted instrumentation in `crates/shinri-solver/tests/qfs_differential.rs` on both sides; outputs under `/tmp/claude-1000/-workspace/a087cca6-92cc-420c-bbf1-4e361caa5f6f/scratchpad/`)

**Interfaces:**
- Consumes: Tasks 1–2 on `slice29-enum-length-companion`; baseline = the branch point on `main`.
- Produces: `verdict-flips.txt` (base-vs-fix per-query verdict diff) and the fix-side aggregate tallies, both cited by Task 4's truth-up.

- [ ] **Step 1: Full oracle differential on the fix branch**

```bash
z3 --version
cargo test -p shinri-solver --test qfs_differential --features oracle -- --nocapture 2>&1 | tail -40
```

Expected: ~80 tests, 0 failures, 0 disagreements (the fuzz-family summary lines print per-family sat/unsat/skip tallies — save this output; it is the fix-side aggregate).

- [ ] **Step 2: Add the temporary per-iteration dump to BOTH helper functions**

All fuzz families funnel through `shinri_lines` (qfs_differential.rs:56) and `shinri_lines_counting_bailouts` (qfs_differential.rs:96). In `shinri_lines`, immediately before the final `out` return (after the `theory_guard_bailouts` assert), insert:

```rust
    // TEMP DIFFDUMP (slice 29 dump-and-diff — do not commit)
    if std::env::var_os("SHINRI_DIFFDUMP").is_some() {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        src.hash(&mut h);
        eprintln!("DIFFDUMP {:016x} {:?} bail=0", h.finish(), out.first());
    }
```

In `shinri_lines_counting_bailouts`, immediately before its final `(out, bailouts)` return, insert the same block but with `bail={bailouts}`:

```rust
    // TEMP DIFFDUMP (slice 29 dump-and-diff — do not commit)
    if std::env::var_os("SHINRI_DIFFDUMP").is_some() {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        src.hash(&mut h);
        eprintln!("DIFFDUMP {:016x} {:?} bail={bailouts}", h.finish(), out.first());
    }
```

Fixed LCG seeds give query-text identity across runs, so the src hash is a stable join key.

- [ ] **Step 3: Dump fix-side per-iteration verdicts**

```bash
SHINRI_DIFFDUMP=1 cargo test -p shinri-solver --test qfs_differential --features oracle -- --test-threads=1 2> /tmp/claude-1000/-workspace/a087cca6-92cc-420c-bbf1-4e361caa5f6f/scratchpad/dump-fix.txt
grep -c DIFFDUMP /tmp/claude-1000/-workspace/a087cca6-92cc-420c-bbf1-4e361caa5f6f/scratchpad/dump-fix.txt
```

Expected: thousands of DIFFDUMP lines (13 fuzz families × their iteration counts, plus targeted tests).

- [ ] **Step 4: Dump baseline-side verdicts from a worktree at the branch point**

```bash
BASE=$(git merge-base main slice29-enum-length-companion)
git worktree add /tmp/claude-1000/-workspace/a087cca6-92cc-420c-bbf1-4e361caa5f6f/scratchpad/wt-baseline "$BASE"
```

Apply the SAME two-helper instrumentation from Step 2 to `wt-baseline/crates/shinri-solver/tests/qfs_differential.rs`, then:

```bash
cd /tmp/claude-1000/-workspace/a087cca6-92cc-420c-bbf1-4e361caa5f6f/scratchpad/wt-baseline
SHINRI_DIFFDUMP=1 cargo test -p shinri-solver --test qfs_differential --features oracle -- --test-threads=1 2> ../dump-base.txt
cd /workspace
```

- [ ] **Step 5: Diff per-iteration verdicts**

```bash
cd /tmp/claude-1000/-workspace/a087cca6-92cc-420c-bbf1-4e361caa5f6f/scratchpad
grep DIFFDUMP dump-base.txt | sort > base.sorted
grep DIFFDUMP dump-fix.txt  | sort > fix.sorted
join -j2 <(sort -k2 base.sorted) <(sort -k2 fix.sorted) | awk '$3 != $6 || $4 != $7' > verdict-flips.txt
wc -l verdict-flips.txt; cat verdict-flips.txt
```

Acceptance (Global Constraints): every flip is `Unknown → sat/unsat` (each decided verdict already has its z3 cross-check inside the family loop, so flips arrive pre-adjudicated), zero `decided → Unknown`, zero `sat ↔ unsat`, zero bailout increases. Anything else: stop the line and report. Record the flip hashes and counts for Task 4's truth-up. (Lines present on only one side are the Task-2 test additions/renames — expected; note them, don't count them as flips.)

- [ ] **Step 6: Clean up instrumentation and the worktree**

```bash
git -C /workspace checkout -- crates/shinri-solver/tests/qfs_differential.rs
git worktree remove --force /tmp/claude-1000/-workspace/a087cca6-92cc-420c-bbf1-4e361caa5f6f/scratchpad/wt-baseline
git -C /workspace status --short
```

Expected: only committed Task 1–2 changes on the branch, no stray modifications (keep `dump-*.txt` / `verdict-flips.txt` in the scratchpad for Task 4).

---

### Task 4: Full gate, spec truth-up, PR, merge on green

**Files:**
- Modify: `docs/superpowers/specs/2026-07-18-shinri-slice29-enum-length-companion-design.md` (status line + "Implementation notes (truth-up)" section)

**Interfaces:**
- Consumes: Tasks 1–3 results (test names from Task 2, aggregate tallies and `verdict-flips.txt` from Task 3).
- Produces: merged PR on `main`; spec truth-up recording what landed, deviations, flip inventory, and the standing bank.

- [ ] **Step 1: Run the full local gate**

```bash
cargo nextest run -p shinri-str
cargo nextest run -p shinri-solver --features oracle --test qfs_differential
cargo nextest run -p shinri-solver --test script_e2e
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

Expected: all green, clippy 0 warnings, fmt clean. `script_e2e` note (completeness-shifting slice): any z3-confirmed `Unknown → decided` pin flip it surfaces is an ADJUDICATED flip, not a blocker (slice-25/26/28 precedent) — update the affected pin with a comment naming slice 29 and re-run; `decided → Unknown` or `sat ↔ unsat` is stop-the-line.

- [ ] **Step 2: Write the spec truth-up**

In `docs/superpowers/specs/2026-07-18-shinri-slice29-enum-length-companion-design.md`: change the Status line to `IMPLEMENTED (<date>). See "Implementation notes (truth-up)" at the end.` and append an `## Implementation notes (truth-up)` section in the slice-28 house format, recording:

- branch + commit hashes for the Task-1 and Task-2 commits;
- "Landed as designed" per spec section (§2 companion mechanics incl. cap and code-point counting; §5 pins by test name, including the negative-polarity guard's actual observed verdict and the slice-25 pin outcome from Task 2 Step 4);
- deviations, if any (code deltas from this plan, or the Task-2 Step-3 Unknown fallback if taken);
- the oracle dump-and-diff inventory from Task 3 (fix-side tallies, flip count, every flip `Unknown → decided`, zero regressions);
- "Newly banked": expected none — standing bank unchanged (hand-written wide disjunctions / approach C fuel-free constant-length propagation, >4 distinct lengths, co-finite facts, slice-28 §8 items, slice-27 typed-antecedent refactor).

```bash
git add docs/superpowers/specs/2026-07-18-shinri-slice29-enum-length-companion-design.md
git commit -m "docs: slice29 truth-up"
```

- [ ] **Step 3: Push, open the PR, merge on green, delete the branch**

```bash
git push -u origin slice29-enum-length-companion
gh pr create --base main --title "slice29: exact-length companion at the finite-enumeration rewrite" --body "Cashes the slice-22 enumeration-length seam known gap. Spec: docs/superpowers/specs/2026-07-18-shinri-slice29-enum-length-companion-design.md (see truth-up). Oracle differential: 0 disagreements; dump-and-diff: all flips Unknown → decided."
gh pr checks --watch
```

When CI is green (standing instruction — merge on green, merge commit, then delete branch):

```bash
gh pr merge --merge --delete-branch
git switch main && git pull && git remote prune origin
```

---

## Self-Review

**Spec coverage:**
- §2 fix (companion at finite branch, `LEN_FACT_DISTINCT_CAP = 4`, code-point counting, co-finite/degenerate/polarity handling) → Task 1. ✓
- §3 soundness (entailed conjunct; empirical verdict-monotonicity via dump-and-diff) → Task 1 comment + Task 3 acceptance. ✓
- §4 completeness boundary (hand-written disjunctions stay Unknown, cap skip, co-finite skip) → Task 1 cap test + banked, no code. ✓
- §5 testing (flip pin, gappy pin, three guards, slice-25 pin re-exam, regex.rs units, oracle dump-and-diff, gate list incl. script_e2e) → Tasks 1/2/3/4. ✓

**Placeholder scan:** no TBDs; every code step shows the code; fallback paths (Task 2 Step 3 Unknown case, Task 2 Step 4 both outcomes, script_e2e adjudication) specify exact actions. ✓

**Type consistency:** `conjoin_len_fact(ctx: &mut Context, t: TermId, ws: &Words, disj: TermId) -> TermId` defined in Task 1 Step 4 and called with the same signature from the finite branch; `LEN_FACT_DISTINCT_CAP: usize = 4` matches the cap test's 5-length construction; `wordeq::len_of(&mut Context, TermId) -> TermId` matches wordeq.rs:38; test names introduced in Task 2 are the ones Task 4's truth-up cites. Expected-TermId assertions rely on hash-consing (house-established, slice-28 spec). ✓
