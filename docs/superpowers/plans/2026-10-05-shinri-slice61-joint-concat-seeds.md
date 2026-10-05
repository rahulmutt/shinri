# Slice 61 — Joint seeds for concat-subject memberships Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give the free leaves of concat-subject memberships (`(str.++ x "z" y) ∈ R`) jointly chosen witness words at model-build time, so the post-solve gate stops rejecting the composed concat, and measure the effect on the 432 `violated:memb@not-needed` rows.

**Architecture:** A new module `crates/shinri-str/src/joint_seed.rs` has a pure, `Context`-free core (`solve_group`: a derivative DFS over a group's leaves, pass 1 at fixed model lengths, pass 2 at free lengths) and a `Context` front end (`joint_seeds`: extracts eligible constraints, groups them by shared leaves, reads lengths, calls the core). `StrSolver::model_with` merges its result over `memb_seeds`' per-leaf seeds. Everything downstream (`string_values`, the slice-57 reconcile, the gate) is unchanged. A base/after bench run and a report close the slice.

**Tech Stack:** Rust workspace (toolchain pinned in `mise.toml`), cargo-nextest 0.9.140, z3 from mise (oracle, via the existing `easy-smt` dev-dependency), `shinri-bench` for the SMT-LIB 2024 run, python3 for analysis scripts.

**Spec:** `docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md`

## Global Constraints

- Model-side only: no change to the parser, SAT, Combiner, word equations, Rule-E, the slice-28 emptiness conflict, lowering, the model gate, the reconcile acceptance rules, fence names, `fence_detail` tags or the bench tool (spec §5).
- `memb_seeds`, `search_word`, `search_shortest`, `next_classes` and `rule_e_classes` keep their bodies. Allowed edits outside the new module: `model::class_len_in_model` becomes `pub(crate)`; `regex.rs` gains `pub(crate) fn class_witness` and `pub(crate) fn joint_classes`; `lib.rs` gains `mod joint_seed;` and one call in `model_with`.
- Caps (spec §4.4–4.5): `JOINT_SEARCH_STEP_CAP = regex::MEMB_SEARCH_STEP_CAP` (10,000) per pass; `JOINT_FREE_LEN_CAP = 64`. `CLASS_SPLIT_CAP`, `MEMB_SEARCH_STEP_CAP` and `FUEL_NODE_CAP` keep their values.
- A group yields a word for every leaf or nothing; an ineligible, pinned or unsolved group leaves the seed map exactly as `memb_seeds` built it (spec §4.3, §5).
- No new dependency of any kind (pure-Rust mandate; `shinri-str` has no dev-dependencies and needs none).
- Existing tests pass **unmodified** (spec §7.4). If one fails, stop and report; do not edit it.
- Oracle tests only run with `--features oracle`; without it they silently run 0 tests. Always confirm a non-zero discovered count (AGENTS.md).
- nextest filters use the expression form `-E 'test(<name>)'` / `-E 'binary(<name>)'` (AGENTS.md).
- `cargo fmt --all` before every commit; `mise run lint` (clippy `-D warnings`) must be clean.
- Bench: base = the slice-60 variant runs `bench/results/slice60b` and `bench/results/slice60b-sample`, binary `target/slice60b-after/shinri` (`56997aa`, whose `crates/` are identical to `main` `5aa164a`; Task 0 verifies). After runs over QF_S and QF_SLIA plus the seed-59 sample corpus `target/slice59-sample-corpus`; `--timeout 20 --mem-mb 3072 --jobs 6`; detached with `setsid` under `taskset -c 12-23`.
- While a bench run is live, run builds and tests on cores 0–11 (`taskset -c 0-11 …`).
- Branch `slice61-joint-concat-seeds` off `main`; PR to `main`, merge commit when CI is green, then delete the branch remote and local (AGENTS.md). Ask the user before merging.

## Review Focus

1. **A length pin that pass 2 ignores.** `x·y ∈ (ab)*` with `(str.len x) = 3`: if pass 1 fails on the model lengths, pass 2's short words break the pin. Expected: the gate rejects them, so shinri answers `sat` with a witness that holds, or `unknown` — never `unsat` (z3 says `sat`) and never a bad witness. Pinned in Task 4 (`length_pin_sound`).
2. **A constant operand above the SMT-LIB alphabet** (`"\u{10000}"` is fine, `char::from_u32(0x30000)` is not). Expected: the constraint is ineligible and nothing is seeded from it. Pinned in Task 3 (`flatten_rejects_above_alphabet_constant`).
3. **A very long model length** (thousands of characters for one leaf). Expected: no stack overflow (explicit frame stack) and a bounded search. Pinned in Task 1 (`long_fixed_length_found_without_recursion`).
4. **A waiting constraint** (`x·y ∈ R1`, `y·x ∈ R2`): `R2` neither prunes nor (without `joint_classes`) refines `x`'s character classes, and two partial words for `x` can reach the same active state while differing for `R2`. Expected: `x`'s classes are refined by `R2`'s ranges, and the memo never merges such words (pending words are part of the key). Pinned in Task 1 (`waiting_constraint_consumes_whole_word`) and swept in Task 2 (the generator renumbers leaves by first occurrence, so later constraints see leaves out of order).
5. **A jointly empty group** (`x·y ∈ a*`, `x ∈ b+`). Expected: no seed, and the solver never says `sat`. Pinned in Task 1 (`jointly_empty_group_exhausted`) and Task 4 (`joint_empty_not_sat`, with its `sat` sibling).

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-str/src/joint_seed.rs` | Create | the search core (`solve_group`) and the front end (`joint_seeds`), with unit tests |
| `crates/shinri-str/src/regex.rs` | Modify | add `class_witness` (the per-class witness choice `search_word` makes inline) and `joint_classes` (head partition refined by later consumers' ranges) |
| `crates/shinri-str/src/model.rs` | Modify | `class_len_in_model` becomes `pub(crate)` |
| `crates/shinri-str/src/lib.rs` | Modify | `mod joint_seed;`; merge `joint_seeds` over `memb_seeds` in `model_with` |
| `crates/shinri-solver/tests/slice61_probes.rs` | Create | blocking-tier probes: both reproducers, a jointly empty pair, a length-pin case |
| `crates/shinri-solver/tests/joint_seed_oracle.rs` | Create | z3 differential over the probes and generated concat-subject scripts (`--features oracle`) |
| `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice61-joint-concat-seeds-report.md` | Create | bench report and rewritten queue |
| `docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md` | Modify | fix the §8 report path; append §11 *Measured outcomes* |

Task order differs from spec §6 on purpose: the pure search core comes first (Tasks 1–2) because it can be tested without a `Context`; the front end and wiring follow (Task 3).

---

### Task 0: Branch, base check, reproducer trace

**Files:** none in the repo (artifacts under `target/slice61-base/`).

**Interfaces:**
- Consumes: `target/slice60b-after/shinri`, `bench/results/slice60b/results.jsonl`, `bench/results/slice60b-sample/results.jsonl`, `target/slice59-sample-corpus/`.
- Produces: `target/slice61-base/{commit.txt,md5.txt,tagcount.txt,trace.txt,probes.txt}`. Task 7 consumes them.

- [ ] **Step 1: Create the slice branch**

```bash
cd /workspace && git checkout main && git pull --ff-only && git checkout -b slice61-joint-concat-seeds
```

- [ ] **Step 2: Confirm the base artifacts are reusable**

```bash
git diff --quiet 56997aa HEAD -- crates Cargo.toml Cargo.lock && echo "crates identical"
mkdir -p target/slice61-base
cat target/slice60b-after/commit.txt | tee target/slice61-base/commit.txt
md5sum target/slice60b-after/shinri | tee target/slice61-base/md5.txt
wc -l bench/results/slice60b/results.jsonl bench/results/slice60b-sample/results.jsonl
find target/slice59-sample-corpus -name '*.smt2' | wc -l
python3 - <<'EOF' | tee target/slice61-base/tagcount.txt
import json, collections
rows = [r for r in map(json.loads, open("bench/results/slice60b/results.jsonl")) if "path" in r]
tag = [r for r in rows if r.get("fence_detail") == "violated:memb@not-needed"]
print("violated:memb@not-needed", len(tag))
print(collections.Counter(r["path"].split("/")[1] for r in tag).most_common())
EOF
```

Expected: `crates identical`; commit `56997aa`; md5 `6109b2a0266510f2084dab2df1e60240`; 103,336 and 2,001 lines; 2000 sample files; tag count **432** (Norn 356, `slog` 44, z3str2-family 30, others 2). If the crates differ or the count is not 432, stop and report: the base must be re-run.

- [ ] **Step 3: Trace the two reproducers (throwaway, not committed)**

Add this block to `crates/shinri-str/src/lib.rs` in `model_with`, right after the line `let seeds = model::memb_seeds(cx.terms, cx.eq, &known, &membs, m);`:

```rust
        for &(atom, _) in &membs {
            let (t, _) = crate::memb::memb_sides(cx.terms, atom);
            if !model::is_concat(cx.terms, t) {
                continue;
            }
            let k_const = model::class_member(cx.terms, cx.eq, &known, t, |tm, mm| {
                tm.string_const_value(mm).is_some()
            });
            let k_cat = model::class_member(cx.terms, cx.eq, &known, t, |tm, mm| {
                model::is_concat(tm, mm) && mm != t
            });
            eprintln!("slice61-trace: subject {t:?} class-const {k_const:?} class-other-concat {k_cat:?}");
            let kids: Vec<TermId> = match cx.terms.term_node(t) {
                TermNode::App { args, .. } => cx.terms.children(*args).to_vec(),
                _ => Vec::new(),
            };
            for k in kids {
                if cx.terms.string_const_value(k).is_some() {
                    continue;
                }
                let pinned = model::is_repair_pinned(cx.terms, cx.eq, &known, k);
                let len = model::len_of_in_model(cx.terms, m, k);
                eprintln!("slice61-trace:   leaf {k:?} pinned {pinned} len {len} seeded {:?}", seeds.get(&k));
            }
        }
```

(If `TermNode` is not imported in `lib.rs`, write `shinri_core::TermNode`.) Then:

```bash
cargo build --release -p shinri-cli --target-dir target/slice61-trace
for f in QF_SLIA/2015-Norn/HammingDistance/norn-benchmark-531.smt2 \
         QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-035-reverse-fuzz.smt2; do
  echo "== $f"; target/slice61-trace/release/shinri bench/corpus/$f 2>&1 | grep -E 'slice61-trace|^(sat|unsat|unknown)$' | sort | uniq -c
done | tee target/slice61-base/trace.txt
git checkout -- crates && git status --short crates
```

Expected: `git status --short crates` prints nothing. Read `trace.txt` against spec §4.2–4.3:
- **Every** leaf line says `pinned false`. If a leaf of either reproducer is pinned, the group would be skipped: **stop and report** (the design's eligibility assumption is wrong).
- Every subject line says `class-const None`. If a subject has a class constant, **stop and report**.
- `class-other-concat Some(..)` is allowed (minted concats do not disqualify a subject, spec §4.2); record what you see.
- Record the leaf `len` values: they decide whether pass 1 or pass 2 will find the Norn words (z3's model is `var_8 = "a"`, `var_9 = "aa"`).

- [ ] **Step 4: Record the base behaviour of the probe shapes**

```bash
D=target/slice61-base/probes && mkdir -p $D
cp bench/corpus/QF_SLIA/2015-Norn/HammingDistance/norn-benchmark-531.smt2 $D/norn531.smt2
cp bench/corpus/QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-035-reverse-fuzz.smt2 $D/regex035.smt2
printf '(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)\n(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))\n(assert (str.in_re x (re.+ (str.to_re "b"))))\n(check-sat)\n' > $D/empty.smt2
printf '(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)\n(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))\n(assert (str.in_re x (re.+ (str.to_re "a"))))\n(check-sat)\n' > $D/empty-sat-sibling.smt2
printf '(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\n(assert (str.in_re (str.++ x y) (re.* (str.to_re "ab"))))\n(assert (= (str.len x) 3))\n(check-sat)\n' > $D/lenpin.smt2
for f in $D/*.smt2; do printf '%s\t' $(basename $f); target/slice60b-after/shinri --stats $f 2>&1 | grep '^stats:'; done | tee target/slice61-base/probes.txt
for f in $D/*.smt2; do printf '%s\t' $(basename $f); mise exec -- z3 -T:20 $f; done
```

Expected: `norn531` and `regex035` print `outcome=unknown fence=str-model-rejected detail=violated:memb@not-needed`; z3 answers `sat`, `sat`, `unsat` (empty), `sat`, `sat`. Record the other base outcomes as found; they are evidence for the report, not gates.

---

### Task 1: The search core, pass 1 (fixed lengths)

**Files:**
- Create: `crates/shinri-str/src/joint_seed.rs`
- Modify: `crates/shinri-str/src/regex.rs` (add `class_witness` and `joint_classes` after `search_shortest`, around line 820)
- Modify: `crates/shinri-str/src/lib.rs:5` (add `mod joint_seed;` after `pub mod int_conv;`)

**Interfaces:**
- Consumes: `regex::{Rex, deriv, nullable, inter, node_count, FUEL_NODE_CAP, MEMB_SEARCH_STEP_CAP}` and the private `head_bounds`, `range_bounds`, `classes_from_bounds` (inside `regex.rs`).
- Produces (later tasks rely on these exact names):
  - `pub(crate) fn regex::class_witness(lo: u32, hi: u32) -> Option<u32>`
  - `pub(crate) fn regex::joint_classes(head: &Rex, later: &[&Rex]) -> Option<Vec<(u32, u32)>>`
  - `pub(crate) enum JOp { Lit(Vec<u32>), Leaf(usize) }`
  - `pub(crate) struct JConstraint { pub(crate) ops: Vec<JOp>, pub(crate) rex: Rex }`
  - `pub(crate) enum Lengths<'a> { Fixed(&'a [usize]), Free(usize) }`
  - `pub(crate) enum Outcome { Found(Vec<String>), Exhausted, Aborted }`
  - `pub(crate) fn solve_group(own: &[Rex], cons: &[JConstraint], lens: Lengths<'_>) -> Outcome` — precondition: `own.len() >= 1`, leaves numbered `0..own.len()` in first-occurrence order across `cons`, every `Leaf(i)` has `i < own.len()`, `Fixed` slices have `own.len()` entries.
  - `pub(crate) const JOINT_SEARCH_STEP_CAP: usize`, `pub(crate) const JOINT_FREE_LEN_CAP: usize`

- [ ] **Step 1: Add `class_witness` and `joint_classes` to `regex.rs`**

Insert right after the closing brace of `search_shortest`:

```rust
/// The witness character of a next-character class: its smallest
/// NON-SURROGATE code point, or `None` for a pure-surrogate class (no Rust
/// `char`; skipping it loses completeness only). The same choice
/// `search_word` makes inline; slice 61's joint search shares it.
pub(crate) fn class_witness(lo: u32, hi: u32) -> Option<u32> {
    if (SURR_LO..=SURR_HI).contains(&lo) {
        (hi > SURR_HI).then_some(SURR_HI + 1)
    } else {
        Some(lo)
    }
}

/// Slice 61: next-character classes for the joint search — the head
/// partition of `head`, refined by EVERY range of each regex in `later`.
/// A regex in `later` consumes the current characters only afterwards (a
/// constraint waiting on another leaf, or a later occurrence of the same
/// leaf). `deriv` never creates a `Range`, so the ranges it will ever test
/// are among its present ones, and each class is uniform for it too —
/// without this refinement one witness per class could miss the word it
/// needs. `None` iff the partition exceeds `CLASS_SPLIT_CAP`.
pub(crate) fn joint_classes(head: &Rex, later: &[&Rex]) -> Option<Vec<(u32, u32)>> {
    let mut bounds = BTreeSet::new();
    head_bounds(head, &mut bounds);
    for r in later {
        range_bounds(r, &mut bounds);
    }
    classes_from_bounds(bounds)
}
```

And add to `regex.rs`'s `mod tests`:

```rust
    #[test]
    fn class_witness_skips_surrogates() {
        assert_eq!(class_witness(0x61, 0x7A), Some(0x61));
        assert_eq!(class_witness(0xD800, 0xDFFF), None);
        assert_eq!(class_witness(0xD800, 0xE005), Some(0xE000));
        assert_eq!(class_witness(0xE000, MAX_CODE), Some(0xE000));
    }

    #[test]
    fn joint_classes_refine_by_later_ranges() {
        // head [a-b]* cuts at a and c; the later "bab" adds a, b and c.
        let head = star(Rex::Range(0x61, 0x62));
        let later = concat(vec![Rex::Range(0x62, 0x62), Rex::Range(0x61, 0x61), Rex::Range(0x62, 0x62)]);
        assert_eq!(
            next_classes(&head),
            Some(vec![(0, 0x60), (0x61, 0x62), (0x63, MAX_CODE)])
        );
        assert_eq!(
            joint_classes(&head, &[&later]),
            Some(vec![(0, 0x60), (0x61, 0x61), (0x62, 0x62), (0x63, MAX_CODE)])
        );
        assert_eq!(joint_classes(&head, &[]), next_classes(&head));
    }
```

- [ ] **Step 2: Write the failing tests**

Create `crates/shinri-str/src/joint_seed.rs` with only the test module (plus the module doc), so the tests fail to compile against the missing items:

```rust
//! Slice 61: joint witness words for the free leaves of concat-subject
//! memberships (spec
//! `docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md`).
//!
//! `model::memb_seeds` seeds a leaf only against its OWN bare memberships,
//! so the operands of `(str.++ x "z" y) ∈ R` are never chosen together and
//! the post-solve gate rejects the composed concat. `joint_seeds` groups
//! concat-subject memberships by shared free leaves; `solve_group` runs one
//! DFS that assigns the leaves a character at a time while advancing every
//! constraint's derivative. The words are CANDIDATES: they override the
//! per-leaf seeds and the gate re-checks every assertion, so a miss or a bug
//! can only leave the prior sound `unknown`.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::regex::{self, Rex};

    fn ch(c: char) -> Rex {
        Rex::Range(c as u32, c as u32)
    }

    fn lit(s: &str) -> JOp {
        JOp::Lit(s.chars().map(|c| c as u32).collect())
    }

    fn sigma_star() -> Rex {
        regex::inter(Vec::new())
    }

    /// Independent check: every constraint's composed subject and every
    /// leaf's own language accept `words` under `eval_membership`.
    fn satisfies(own: &[Rex], cons: &[JConstraint], words: &[String]) -> bool {
        own.iter()
            .zip(words)
            .all(|(r, w)| regex::eval_membership(w, r) == Some(true))
            && cons.iter().all(|c| {
                let s: String = c
                    .ops
                    .iter()
                    .map(|op| match op {
                        JOp::Lit(cs) => cs.iter().map(|&k| char::from_u32(k).unwrap()).collect(),
                        JOp::Leaf(i) => words[*i].clone(),
                    })
                    .collect();
                regex::eval_membership(&s, &c.rex) == Some(true)
            })
    }

    /// The `norn-benchmark-531` group (spec §1.2), leaves `var_8` = 0,
    /// `var_9` = 1. z3's model: `var_8 = "a"`, `var_9 = "aa"`.
    fn norn_531() -> (Vec<Rex>, Vec<JConstraint>) {
        let ab_star = regex::star(regex::union(vec![ch('b'), ch('a')]));
        let r1 = regex::concat(vec![
            regex::star(regex::concat(vec![ch('a'), ab_star.clone(), ch('z')])),
            ch('a'),
            ab_star,
        ]);
        let r2 = regex::concat(vec![
            regex::star(regex::union(vec![
                ch('z'),
                regex::concat(vec![ch('a'), regex::star(ch('a')), ch('z')]),
            ])),
            ch('a'),
            regex::star(ch('a')),
        ]);
        let r3 = regex::concat(vec![
            regex::star(regex::union(vec![
                ch('z'),
                ch('b'),
                regex::concat(vec![ch('a'), regex::union(vec![ch('z'), ch('a')])]),
            ])),
            ch('a'),
        ]);
        let au = regex::star(Rex::Range('a' as u32, 'u' as u32));
        let xzy = vec![JOp::Leaf(0), lit("z"), JOp::Leaf(1)];
        let cons = vec![
            JConstraint { ops: xzy.clone(), rex: r1 },
            JConstraint { ops: xzy, rex: r2 },
            JConstraint {
                ops: vec![lit("b"), JOp::Leaf(0), lit("z"), lit("b"), JOp::Leaf(1)],
                rex: regex::comp(r3),
            },
        ];
        (vec![au.clone(), au], cons)
    }

    fn found(o: Outcome) -> Vec<String> {
        match o {
            Outcome::Found(w) => w,
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn regex_035_shape_fixed() {
        // (str.++ y x) ∈ b*, no bare memberships: y = 0, x = 1.
        let own = vec![sigma_star(), sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), JOp::Leaf(1)],
            rex: regex::star(ch('b')),
        }];
        let w = found(solve_group(&own, &cons, Lengths::Fixed(&[1, 2])));
        assert_eq!(w, vec!["b".to_string(), "bb".to_string()]);
    }

    #[test]
    fn norn_531_fixed_at_z3_lengths() {
        let (own, cons) = norn_531();
        let w = found(solve_group(&own, &cons, Lengths::Fixed(&[1, 2])));
        assert!(satisfies(&own, &cons, &w), "{w:?}");
        assert_eq!((w[0].chars().count(), w[1].chars().count()), (1, 2));
    }

    #[test]
    fn repeated_leaf_is_forced_on_second_occurrence() {
        // x·"c"·x ∈ abcab: the second copy of x is fed as forced characters.
        let own = vec![sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), lit("c"), JOp::Leaf(0)],
            rex: regex::concat(vec![ch('a'), ch('b'), ch('c'), ch('a'), ch('b')]),
        }];
        assert_eq!(found(solve_group(&own, &cons, Lengths::Fixed(&[2]))), vec!["ab"]);
        // x·"c"·x ∈ abcba has no solution: the second copy must repeat the first.
        let cons2 = vec![JConstraint {
            ops: vec![JOp::Leaf(0), lit("c"), JOp::Leaf(0)],
            rex: regex::concat(vec![ch('a'), ch('b'), ch('c'), ch('b'), ch('a')]),
        }];
        assert_eq!(solve_group(&own, &cons2, Lengths::Fixed(&[2])), Outcome::Exhausted);
    }

    #[test]
    fn waiting_constraint_consumes_whole_word() {
        // x·y ∈ [a-b]* and y·x ∈ bab, leaves x = 0, y = 1: the second
        // constraint waits on y while x is assigned. [a-b]* alone gives x one
        // class [a-b] (witness 'a'); only `joint_classes`' refinement by the
        // waiting "bab" lets x be "ab".
        let ab = regex::star(regex::union(vec![ch('a'), ch('b')]));
        let own = vec![sigma_star(), sigma_star()];
        let cons = vec![
            JConstraint { ops: vec![JOp::Leaf(0), JOp::Leaf(1)], rex: ab },
            JConstraint {
                ops: vec![JOp::Leaf(1), JOp::Leaf(0)],
                rex: regex::concat(vec![ch('b'), ch('a'), ch('b')]),
            },
        ];
        // |x| = 2, |y| = 1 forces y = "b", x = "ab".
        let w = found(solve_group(&own, &cons, Lengths::Fixed(&[2, 1])));
        assert_eq!(w, vec!["ab".to_string(), "b".to_string()]);
        assert!(satisfies(&own, &cons, &w));
    }

    #[test]
    fn jointly_empty_group_exhausted() {
        // x·y ∈ a*, x ∈ b+ (x's own language).
        let own = vec![regex::concat(vec![ch('b'), regex::star(ch('b'))]), sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), JOp::Leaf(1)],
            rex: regex::star(ch('a')),
        }];
        assert_eq!(solve_group(&own, &cons, Lengths::Fixed(&[1, 1])), Outcome::Exhausted);
    }

    #[test]
    fn long_fixed_length_found_without_recursion() {
        // x·"z" ∈ a*z with |x| = 3000: one frame per character.
        let own = vec![sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), lit("z")],
            rex: regex::concat(vec![regex::star(ch('a')), ch('z')]),
        }];
        let w = found(solve_group(&own, &cons, Lengths::Fixed(&[3000])));
        assert_eq!(w[0], "a".repeat(3000));
    }

    #[test]
    fn step_cap_aborts() {
        // x·y ∈ (a|c)* gives x two live characters per position; y·x ∈ ∅
        // waits on y, so every distinct x is a distinct memo key (its word is
        // pending) and no path succeeds: 2^20 paths > JOINT_SEARCH_STEP_CAP.
        let own = vec![sigma_star(), sigma_star()];
        let cons = vec![
            JConstraint {
                ops: vec![JOp::Leaf(0), JOp::Leaf(1)],
                rex: regex::star(regex::union(vec![ch('a'), ch('c')])),
            },
            JConstraint { ops: vec![JOp::Leaf(1), JOp::Leaf(0)], rex: Rex::Empty },
        ];
        assert_eq!(
            solve_group(&own, &cons, Lengths::Fixed(&[20, 0])),
            Outcome::Aborted
        );
    }
}
```

Note on `step_cap_aborts`: `Rex::Empty` is used directly as a constraint's language on purpose. `advance` checks a derivative only after feeding it characters, and the waiting constraint is not fed until leaf 1 ends, so the search must enumerate x's words. `a|c` (not `a|b`) because `union` merges adjacent ranges into one class.

- [ ] **Step 3: Run the tests to verify they fail**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(joint_seed::) | test(class_witness_skips_surrogates) | test(joint_classes_refine_by_later_ranges)'`
Expected: compile errors — `JOp`, `JConstraint`, `solve_group`, `Lengths`, `Outcome` not found (the two `regex` tests cannot run until the crate compiles).

- [ ] **Step 4: Implement the core**

Insert between the module doc and `#[cfg(test)]` in `joint_seed.rs`:

```rust
use crate::regex::{self, Rex};
use rustc_hash::FxHashSet;

/// Per-pass DFS step cap (spec §4.4): the witness search's own cap.
pub(crate) const JOINT_SEARCH_STEP_CAP: usize = regex::MEMB_SEARCH_STEP_CAP;
/// Pass 2's budget on the total characters of a group's leaves (spec §4.5).
pub(crate) const JOINT_FREE_LEN_CAP: usize = 64;

/// One operand of a flattened concat subject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum JOp {
    /// A string constant's code points.
    Lit(Vec<u32>),
    /// A free leaf: an index into the group's leaf list.
    Leaf(usize),
}

/// The concatenation of `ops` is in `rex` (polarity already folded).
#[derive(Clone, Debug)]
pub(crate) struct JConstraint {
    pub(crate) ops: Vec<JOp>,
    pub(crate) rex: Rex,
}

/// How long each leaf's word may be (spec §4.5).
#[derive(Clone, Copy, Debug)]
pub(crate) enum Lengths<'a> {
    /// Pass 1: every leaf's exact model length, by leaf index.
    Fixed(&'a [usize]),
    /// Pass 2: free lengths; the total over all leaves is at most this.
    Free(usize),
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Outcome {
    /// One word per leaf, by leaf index.
    Found(Vec<String>),
    /// No words exist within the lengths (and below every cap but steps).
    Exhausted,
    /// `JOINT_SEARCH_STEP_CAP` was hit: not a verdict.
    Aborted,
}

/// A DFS node. Leaves are assigned in index order.
#[derive(Clone)]
struct Node {
    /// The leaf being assigned (== the leaf count once all are assigned).
    leaf: usize,
    /// `Fixed`: characters the current leaf still needs. `Free`: budget left.
    rem: usize,
    /// The current leaf's own-language derivative.
    own: Rex,
    /// Per constraint: the next unconsumed operand and the derivative of its
    /// regex by everything consumed so far.
    cur: Vec<(usize, Rex)>,
    /// Words by leaf; the current leaf's is partial.
    words: Vec<Vec<u32>>,
}

/// Memo key: the node's state, plus every word that some constraint has
/// still to consume outside its active position (a constraint waiting on a
/// later leaf, or a repeated leaf). Those words shape the future, so two
/// nodes that differ only in them are different states.
type Key = (usize, usize, Rex, Vec<(usize, Rex)>, Vec<(usize, Vec<u32>)>);

#[derive(Clone, Copy)]
enum Move {
    /// Finish the current leaf.
    End,
    /// Append this code point to the current leaf.
    Char(u32),
}

enum Visit {
    Word,
    Dead,
    Abort,
    Explore(Key, Vec<Move>),
}

fn is_dead(r: &Rex) -> bool {
    matches!(r, Rex::Empty) || regex::node_count(r) > regex::FUEL_NODE_CAP
}

fn feed(r: &Rex, cs: &[u32]) -> Rex {
    let mut d = r.clone();
    for &c in cs {
        d = regex::deriv(c, &d);
        if is_dead(&d) {
            break;
        }
    }
    d
}

/// True iff constraint `j`'s next operand is the leaf being assigned.
fn is_active(n: &Node, cons: &[JConstraint], j: usize) -> bool {
    cons[j].ops.get(n.cur[j].0) == Some(&JOp::Leaf(n.leaf))
}

/// Consume each constraint's operands up to its next unassigned leaf
/// (constants, and the words of assigned leaves). False iff a derivative
/// died.
fn advance(n: &mut Node, cons: &[JConstraint]) -> bool {
    let Node {
        leaf, cur, words, ..
    } = n;
    for (c, (i, d)) in cons.iter().zip(cur.iter_mut()) {
        while let Some(op) = c.ops.get(*i) {
            let cs: &[u32] = match op {
                JOp::Lit(cs) => cs,
                JOp::Leaf(l) if *l < *leaf => &words[*l],
                JOp::Leaf(_) => break,
            };
            *d = feed(d, cs);
            if is_dead(d) {
                return false;
            }
            *i += 1;
        }
    }
    true
}

fn key(n: &Node, cons: &[JConstraint]) -> Key {
    let pending = (0..=n.leaf)
        .filter(|&l| {
            cons.iter().zip(&n.cur).any(|(c, (i, _))| {
                c.ops
                    .iter()
                    .enumerate()
                    .skip(*i)
                    .any(|(p, op)| *op == JOp::Leaf(l) && !(p == *i && l == n.leaf))
            })
        })
        .map(|l| (l, n.words[l].clone()))
        .collect();
    (n.leaf, n.rem, n.own.clone(), n.cur.clone(), pending)
}

fn moves(n: &Node, cons: &[JConstraint], lens: Lengths<'_>) -> Vec<Move> {
    let mut mv = Vec::new();
    let may_end = match lens {
        Lengths::Fixed(_) => n.rem == 0,
        Lengths::Free(_) => true,
    };
    // End first: in pass 2 this biases towards short words.
    if may_end && regex::nullable(&n.own) {
        mv.push(Move::End);
    }
    if n.rem > 0 {
        let mut parts = vec![n.own.clone()];
        parts.extend(
            (0..cons.len())
                .filter(|&j| is_active(n, cons, j))
                .map(|j| n.cur[j].1.clone()),
        );
        // Constraints that will consume this leaf's characters later: a
        // waiting one, or a later occurrence of this leaf in any.
        let later: Vec<&Rex> = (0..cons.len())
            .filter(|&j| {
                let from = n.cur[j].0 + usize::from(is_active(n, cons, j));
                cons[j].ops[from..].contains(&JOp::Leaf(n.leaf))
            })
            .map(|j| &n.cur[j].1)
            .collect();
        // The head bounds of an `Inter` are every member's: the common
        // refinement, then refined for `later`. `None` (past the cap) leaves
        // no char move — completeness only.
        if let Some(classes) = regex::joint_classes(&regex::inter(parts), &later) {
            mv.extend(
                classes
                    .into_iter()
                    .filter_map(|(lo, hi)| regex::class_witness(lo, hi))
                    .map(Move::Char),
            );
        }
    }
    mv
}

fn apply(n: &Node, mv: Move, own: &[Rex], cons: &[JConstraint], lens: Lengths<'_>) -> Option<Node> {
    let mut ch = n.clone();
    match mv {
        Move::Char(c) => {
            ch.own = regex::deriv(c, &n.own);
            if is_dead(&ch.own) {
                return None;
            }
            for j in 0..cons.len() {
                if is_active(n, cons, j) {
                    let d = regex::deriv(c, &n.cur[j].1);
                    if is_dead(&d) {
                        return None;
                    }
                    ch.cur[j].1 = d;
                }
            }
            ch.words[n.leaf].push(c);
            ch.rem -= 1;
        }
        Move::End => {
            for j in 0..cons.len() {
                if is_active(n, cons, j) {
                    ch.cur[j].0 += 1;
                }
            }
            ch.leaf += 1;
            if ch.leaf < own.len() {
                ch.own = own[ch.leaf].clone();
                if let Lengths::Fixed(ls) = lens {
                    ch.rem = ls[ch.leaf];
                }
            }
            if !advance(&mut ch, cons) {
                return None;
            }
        }
    }
    Some(ch)
}

fn visit(
    n: &Node,
    own: &[Rex],
    cons: &[JConstraint],
    lens: Lengths<'_>,
    steps: &mut usize,
    dead: &FxHashSet<Key>,
) -> Visit {
    if *steps >= JOINT_SEARCH_STEP_CAP {
        return Visit::Abort;
    }
    *steps += 1;
    if n.leaf == own.len() {
        // Every leaf is assigned, so `advance` consumed every operand.
        debug_assert!(cons.iter().zip(&n.cur).all(|(c, (i, _))| *i == c.ops.len()));
        return if n.cur.iter().all(|(_, d)| regex::nullable(d)) {
            Visit::Word
        } else {
            Visit::Dead
        };
    }
    let k = key(n, cons);
    if dead.contains(&k) {
        return Visit::Dead;
    }
    Visit::Explore(k, moves(n, cons, lens))
}

fn render(words: &[Vec<u32>]) -> Vec<String> {
    words
        .iter()
        .map(|w| {
            w.iter()
                .map(|&c| char::from_u32(c).expect("class_witness yields a char"))
                .collect()
        })
        .collect()
}

/// Words for a group's leaves such that every constraint's concatenation is
/// in its regex and every leaf is in its own language (spec §4.4). DFS with
/// an explicit frame stack (a leaf can be thousands of characters long) and
/// a dead-state memo, like `regex::search_word`.
pub(crate) fn solve_group(own: &[Rex], cons: &[JConstraint], lens: Lengths<'_>) -> Outcome {
    struct Frame {
        node: Node,
        key: Key,
        moves: Vec<Move>,
        idx: usize,
    }
    let mut root = Node {
        leaf: 0,
        rem: match lens {
            Lengths::Fixed(ls) => ls[0],
            Lengths::Free(b) => b,
        },
        own: own[0].clone(),
        cur: cons.iter().map(|c| (0, c.rex.clone())).collect(),
        words: vec![Vec::new(); own.len()],
    };
    if !advance(&mut root, cons) {
        return Outcome::Exhausted;
    }
    let mut steps = 0usize;
    let mut dead: FxHashSet<Key> = FxHashSet::default();
    let mut stack: Vec<Frame> = Vec::new();
    match visit(&root, own, cons, lens, &mut steps, &dead) {
        Visit::Word => return Outcome::Found(render(&root.words)),
        Visit::Dead => return Outcome::Exhausted,
        Visit::Abort => return Outcome::Aborted,
        Visit::Explore(key, moves) => stack.push(Frame {
            node: root,
            key,
            moves,
            idx: 0,
        }),
    }
    'descend: while let Some(mut f) = stack.pop() {
        while f.idx < f.moves.len() {
            let mv = f.moves[f.idx];
            f.idx += 1;
            let Some(child) = apply(&f.node, mv, own, cons, lens) else {
                continue;
            };
            match visit(&child, own, cons, lens, &mut steps, &dead) {
                Visit::Word => return Outcome::Found(render(&child.words)),
                Visit::Dead => continue,
                Visit::Abort => return Outcome::Aborted,
                Visit::Explore(key, moves) => {
                    stack.push(f);
                    stack.push(Frame {
                        node: child,
                        key,
                        moves,
                        idx: 0,
                    });
                    continue 'descend;
                }
            }
        }
        dead.insert(f.key);
    }
    Outcome::Exhausted
}
```

Add `mod joint_seed;` to `crates/shinri-str/src/lib.rs` after `pub mod int_conv;`. Until Task 3 the items are used only by tests; if clippy reports `dead_code` on them, add `#![cfg_attr(not(test), allow(dead_code))]` as the first line after the module doc and remove it in Task 3 Step 6.

- [ ] **Step 5: Run the tests to verify they pass**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(joint_seed::) | test(class_witness_skips_surrogates) | test(joint_classes_refine_by_later_ranges)'`
Expected: 9 tests run, 9 passed (7 in `joint_seed`, 2 in `regex`). If `step_cap_aborts` reports `Exhausted`, the pending-word memo key is collapsing distinct states — that is a bug in `key`, not in the test.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/joint_seed.rs crates/shinri-str/src/regex.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice61 - joint derivative search over concat-subject leaves (fixed lengths)"
```

---

### Task 2: Pass 2 (free lengths) and the soundness/completeness sweep

**Files:**
- Modify: `crates/shinri-str/src/joint_seed.rs` (tests only, unless a test exposes a bug)

**Interfaces:**
- Consumes: Task 1's `solve_group`, `Lengths::Free`, `JOINT_FREE_LEN_CAP`, test helpers `ch`, `lit`, `sigma_star`, `satisfies`, `norn_531`.
- Produces: nothing new for later tasks (pass 2 is already reachable through `Lengths::Free`; this task pins its behaviour).

- [ ] **Step 1: Write the pass-2 tests**

Append inside `mod tests` in `joint_seed.rs`:

```rust
    #[test]
    fn free_lengths_find_when_fixed_cannot() {
        // x·y ∈ (ab)+ with model lengths |x| = 1, |y| = 0: "a" is not in
        // (ab)+, so pass 1 is exhausted; pass 2 finds a short pair.
        let own = vec![sigma_star(), sigma_star()];
        let ab = regex::concat(vec![ch('a'), ch('b')]);
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), JOp::Leaf(1)],
            rex: regex::concat(vec![ab.clone(), regex::star(ab)]),
        }];
        assert_eq!(solve_group(&own, &cons, Lengths::Fixed(&[1, 0])), Outcome::Exhausted);
        let w = found(solve_group(&own, &cons, Lengths::Free(JOINT_FREE_LEN_CAP)));
        assert!(satisfies(&own, &cons, &w), "{w:?}");
    }

    #[test]
    fn free_lengths_prefer_short_words() {
        // x·"z"·y ∈ a*za*: End is tried first, so both leaves come back empty.
        let own = vec![sigma_star(), sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), lit("z"), JOp::Leaf(1)],
            rex: regex::concat(vec![regex::star(ch('a')), ch('z'), regex::star(ch('a'))]),
        }];
        let w = found(solve_group(&own, &cons, Lengths::Free(JOINT_FREE_LEN_CAP)));
        assert_eq!(w, vec![String::new(), String::new()]);
    }

    #[test]
    fn free_budget_bounds_total_length() {
        // x ∈ a{70}: needs 70 leaf characters, more than JOINT_FREE_LEN_CAP.
        let own = vec![sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), lit("z")],
            rex: regex::concat(vec![regex::loop_(ch('a'), 70, 70), ch('z')]),
        }];
        assert_eq!(
            solve_group(&own, &cons, Lengths::Free(JOINT_FREE_LEN_CAP)),
            Outcome::Exhausted
        );
    }

    #[test]
    fn norn_531_free() {
        let (own, cons) = norn_531();
        let w = found(solve_group(&own, &cons, Lengths::Free(JOINT_FREE_LEN_CAP)));
        assert!(satisfies(&own, &cons, &w), "{w:?}");
    }
```

- [ ] **Step 2: Write the sweep**

Append inside `mod tests`:

```rust
    /// Deterministic LCG (no new dependency), as in the oracle files.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
            self.0 >> 16
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// A small regex over {a, b}. Every char other than a/b behaves alike,
    /// so 'c' stands for all of them in the brute force.
    fn gen_rex(rng: &mut Lcg, depth: u32) -> Rex {
        let leafy = depth == 0 || rng.below(3) == 0;
        if leafy {
            return match rng.below(4) {
                0 => ch('a'),
                1 => ch('b'),
                2 => Rex::Range('a' as u32, 'b' as u32),
                _ => regex::star(ch('a')),
            };
        }
        let a = gen_rex(rng, depth - 1);
        match rng.below(5) {
            0 => regex::concat(vec![a, gen_rex(rng, depth - 1)]),
            1 => regex::union(vec![a, gen_rex(rng, depth - 1)]),
            2 => regex::star(a),
            3 => regex::comp(a),
            _ => regex::inter(vec![a, gen_rex(rng, depth - 1)]),
        }
    }

    /// 1–2 leaves, 1–2 constraints of 1–3 operands each (≥ 1 leaf), leaves
    /// renumbered by first occurrence so later constraints may see them out
    /// of order (waiting constraints).
    fn gen_group(rng: &mut Lcg) -> (Vec<Rex>, Vec<JConstraint>) {
        let k = 1 + rng.below(2) as usize;
        let mut cons: Vec<JConstraint> = (0..1 + rng.below(2))
            .map(|_| {
                let mut ops: Vec<JOp> = (0..1 + rng.below(3))
                    .map(|_| match rng.below(4) {
                        0 => lit(["a", "b", "ab"][rng.below(3) as usize]),
                        _ => JOp::Leaf(rng.below(k as u64) as usize),
                    })
                    .collect();
                if !ops.iter().any(|o| matches!(o, JOp::Leaf(_))) {
                    ops[0] = JOp::Leaf(0);
                }
                JConstraint { ops, rex: gen_rex(rng, 3) }
            })
            .collect();
        let mut order: Vec<usize> = Vec::new();
        for c in &cons {
            for op in &c.ops {
                if let JOp::Leaf(l) = op {
                    if !order.contains(l) {
                        order.push(*l);
                    }
                }
            }
        }
        for c in &mut cons {
            for op in &mut c.ops {
                if let JOp::Leaf(l) = op {
                    *l = order.iter().position(|x| x == l).unwrap();
                }
            }
        }
        let own = (0..order.len())
            .map(|_| if rng.below(2) == 0 { sigma_star() } else { gen_rex(rng, 2) })
            .collect();
        (own, cons)
    }

    fn words_over(n: usize) -> Vec<String> {
        let mut out = vec![String::new()];
        for _ in 0..n {
            out = out
                .into_iter()
                .flat_map(|w| ['a', 'b', 'c'].map(|c| format!("{w}{c}")))
                .collect();
        }
        out
    }

    /// Brute force: some assignment with the given per-leaf lengths
    /// satisfies the group.
    fn brute(own: &[Rex], cons: &[JConstraint], lens: &[usize]) -> bool {
        fn go(own: &[Rex], cons: &[JConstraint], lens: &[usize], acc: &mut Vec<String>) -> bool {
            if acc.len() == lens.len() {
                return satisfies(own, cons, acc);
            }
            for w in words_over(lens[acc.len()]) {
                acc.push(w);
                if go(own, cons, lens, acc) {
                    return true;
                }
                acc.pop();
            }
            false
        }
        go(own, cons, lens, &mut Vec::new())
    }

    #[test]
    fn sweep_sound_and_complete() {
        let mut rng = Lcg(61);
        let (mut found_n, mut exhausted_n, mut aborted_n) = (0, 0, 0);
        for _ in 0..1500 {
            let (own, cons) = gen_group(&mut rng);
            // Pass 1 at random fixed lengths (total ≤ 4).
            let lens: Vec<usize> = (0..own.len()).map(|_| rng.below(3) as usize).collect();
            let expect = brute(&own, &cons, &lens);
            match solve_group(&own, &cons, Lengths::Fixed(&lens)) {
                Outcome::Found(w) => {
                    found_n += 1;
                    assert!(satisfies(&own, &cons, &w), "unsound {w:?}: {own:?} {cons:?}");
                    assert!(w.iter().zip(&lens).all(|(w, &n)| w.chars().count() == n));
                }
                Outcome::Exhausted => {
                    exhausted_n += 1;
                    assert!(!expect, "incomplete at {lens:?}: {own:?} {cons:?}");
                }
                Outcome::Aborted => aborted_n += 1,
            }
            // Pass 2 with a budget of 4 vs every length split with total ≤ 4.
            let any = (0..=4usize).any(|t| {
                let mut splits = vec![vec![]];
                for _ in 0..own.len() {
                    splits = splits
                        .into_iter()
                        .flat_map(|s: Vec<usize>| (0..=t).map(move |n| [s.clone(), vec![n]].concat()))
                        .collect();
                }
                splits
                    .into_iter()
                    .filter(|s| s.iter().sum::<usize>() == t)
                    .any(|s| brute(&own, &cons, &s))
            });
            match solve_group(&own, &cons, Lengths::Free(4)) {
                Outcome::Found(w) => {
                    assert!(satisfies(&own, &cons, &w), "unsound free {w:?}: {own:?} {cons:?}");
                    assert!(w.iter().map(|w| w.chars().count()).sum::<usize>() <= 4);
                }
                Outcome::Exhausted => assert!(!any, "incomplete free: {own:?} {cons:?}"),
                Outcome::Aborted => aborted_n += 1,
            }
        }
        eprintln!("sweep: {found_n} found, {exhausted_n} exhausted, {aborted_n} aborted");
        assert!(found_n > 100 && exhausted_n > 100, "generator must exercise both outcomes");
    }
```

- [ ] **Step 3: Run the new tests**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(joint_seed::)'`
Expected: 12 tests run, 12 passed (7 from Task 1, 5 new). `sweep_sound_and_complete` should take under 30 s in a debug build; if it takes longer, lower the iteration count to 1000 and note it in the commit message. If the generator assertion fails (too few found/exhausted), adjust `gen_rex` leaf weights, not the assertion. If an `unsound` or `incomplete` assertion fails, that is a bug in `solve_group`: fix it, keeping the failing case as a named regression test.

- [ ] **Step 4: Commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/joint_seed.rs
git commit -m "test(str): slice61 - free-length pass and the joint-search soundness/completeness sweep"
```

---

### Task 3: Front end — extraction, grouping, `joint_seeds`, wiring

**Files:**
- Modify: `crates/shinri-str/src/joint_seed.rs` (front end and its tests)
- Modify: `crates/shinri-str/src/model.rs:56` (`fn class_len_in_model` → `pub(crate) fn class_len_in_model`)
- Modify: `crates/shinri-str/src/lib.rs` ~1583 (`model_with`)

**Interfaces:**
- Consumes: Task 1's `solve_group`, `JOp`, `JConstraint`, `Lengths`, `Outcome`, `JOINT_FREE_LEN_CAP`; `crate::memb::memb_sides(&Context, TermId) -> (TermId, TermId)`; `model::{is_concat, class_member, is_repair_pinned, class_len_in_model}`; `regex::{extract_const_regex, comp, inter, MAX_CODE}`.
- Produces: `pub(crate) fn joint_seeds(terms: &mut Context, eq: &mut EqualityEngine, known: &[TermId], membs: &[(TermId, bool)], m: &ModelBuilder) -> FxHashMap<TermId, String>`, called from `model_with`.

- [ ] **Step 1: Write the failing tests**

Append a second test module at the end of `joint_seed.rs`:

```rust
#[cfg(test)]
mod front_tests {
    use super::*;
    use crate::regex::{self, Rex};
    use shinri_core::{BuiltinOp, Context, Op, TermId};
    use shinri_theory::types::{EqJust, ModelVal};
    use shinri_theory::{EqualityEngine, ModelBuilder};

    fn var(ctx: &mut Context, n: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn cat(ctx: &mut Context, parts: &[TermId]) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), parts).unwrap()
    }

    fn memb(ctx: &mut Context, t: TermId, r: &Rex) -> TermId {
        let re_t = regex::rex_to_term_test(ctx, r);
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[t, re_t]).unwrap()
    }

    fn pin_len(ctx: &mut Context, m: &mut ModelBuilder, t: TermId, n: i128) {
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[t]).unwrap();
        m.assign(l, ModelVal::Num(shinri_core::Rational::from_int(n.into())));
    }

    fn merge(eq: &mut EqualityEngine, a: TermId, b: TermId) {
        let (ia, ib) = (eq.intern(a), eq.intern(b));
        let _ = eq.merge(ia, ib, EqJust::Definitional);
    }

    #[test]
    fn regex_035_shape_seeds_both_leaves() {
        let mut ctx = Context::new();
        let (x, y) = (var(&mut ctx, "x"), var(&mut ctx, "y"));
        let yx = cat(&mut ctx, &[y, x]);
        let a = memb(&mut ctx, yx, &regex::star_lit_test("b"));
        let mut m = ModelBuilder::default();
        pin_len(&mut ctx, &mut m, y, 1);
        pin_len(&mut ctx, &mut m, x, 2);
        let mut eq = EqualityEngine::default();
        let s = joint_seeds(&mut ctx, &mut eq, &[x, y, yx], &[(a, true)], &m);
        assert_eq!(s.get(&y).map(String::as_str), Some("b"));
        assert_eq!(s.get(&x).map(String::as_str), Some("bb"));
    }

    #[test]
    fn bare_membership_is_the_own_language() {
        // x·y ∈ (a|b)*, x ∈ b+ (bare), negative bare y ∉ a* ⇒ y has a b.
        let mut ctx = Context::new();
        let (x, y) = (var(&mut ctx, "x"), var(&mut ctx, "y"));
        let xy = cat(&mut ctx, &[x, y]);
        let ab = regex::star(regex::union(vec![
            Rex::Range('a' as u32, 'a' as u32),
            Rex::Range('b' as u32, 'b' as u32),
        ]));
        let a1 = memb(&mut ctx, xy, &ab);
        let bplus = regex::concat(vec![regex::lit_test("b"), regex::star_lit_test("b")]);
        let a2 = memb(&mut ctx, x, &bplus);
        let a3 = memb(&mut ctx, y, &regex::star_lit_test("a"));
        let mut m = ModelBuilder::default();
        pin_len(&mut ctx, &mut m, x, 1);
        pin_len(&mut ctx, &mut m, y, 1);
        let mut eq = EqualityEngine::default();
        let s = joint_seeds(&mut ctx, &mut eq, &[x, y, xy], &[(a1, true), (a2, true), (a3, false)], &m);
        assert_eq!(s.get(&x).map(String::as_str), Some("b"));
        assert_eq!(s.get(&y).map(String::as_str), Some("b"));
    }

    #[test]
    fn pinned_leaf_skips_its_group_only() {
        // Group 1: x·y ∈ b*, x pinned to "ab" ⇒ skipped. Group 2: z·w ∈ a*.
        let mut ctx = Context::new();
        let (x, y, z, w) = (var(&mut ctx, "x"), var(&mut ctx, "y"), var(&mut ctx, "z"), var(&mut ctx, "w"));
        let (xy, zw) = (cat(&mut ctx, &[x, y]), cat(&mut ctx, &[z, w]));
        let a1 = memb(&mut ctx, xy, &regex::star_lit_test("b"));
        let a2 = memb(&mut ctx, zw, &regex::star_lit_test("a"));
        let ab = ctx.mk_string_const("ab");
        let mut eq = EqualityEngine::default();
        merge(&mut eq, x, ab);
        let mut m = ModelBuilder::default();
        for t in [x, y, z, w] {
            pin_len(&mut ctx, &mut m, t, 1);
        }
        let s = joint_seeds(&mut ctx, &mut eq, &[x, y, z, w, xy, zw, ab], &[(a1, true), (a2, true)], &m);
        assert!(!s.contains_key(&x) && !s.contains_key(&y), "{s:?}");
        assert_eq!(s.get(&z).map(String::as_str), Some("a"));
        assert_eq!(s.get(&w).map(String::as_str), Some("a"));
    }

    #[test]
    fn constant_pinned_subject_is_skipped() {
        let mut ctx = Context::new();
        let (x, y) = (var(&mut ctx, "x"), var(&mut ctx, "y"));
        let xy = cat(&mut ctx, &[x, y]);
        let a = memb(&mut ctx, xy, &regex::star_lit_test("b"));
        let bb = ctx.mk_string_const("bb");
        let mut eq = EqualityEngine::default();
        merge(&mut eq, xy, bb);
        let m = ModelBuilder::default();
        let s = joint_seeds(&mut ctx, &mut eq, &[x, y, xy, bb], &[(a, true)], &m);
        assert!(s.is_empty(), "{s:?}");
    }

    #[test]
    fn non_leaf_operand_is_ineligible() {
        // f(x)·y ∈ b*: f(x) is not a nullary leaf.
        let mut ctx = Context::new();
        let (x, y) = (var(&mut ctx, "x"), var(&mut ctx, "y"));
        let s_sort = ctx.string_sort();
        let f = ctx.declare_fun("f", &[s_sort], s_sort);
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let t = cat(&mut ctx, &[fx, y]);
        let a = memb(&mut ctx, t, &regex::star_lit_test("b"));
        let mut eq = EqualityEngine::default();
        let m = ModelBuilder::default();
        assert!(joint_seeds(&mut ctx, &mut eq, &[x, y, fx, t], &[(a, true)], &m).is_empty());
    }

    #[test]
    fn nested_concat_is_flattened() {
        // x·("z"·y) ∈ a*za*
        let mut ctx = Context::new();
        let (x, y) = (var(&mut ctx, "x"), var(&mut ctx, "y"));
        let z = ctx.mk_string_const("z");
        let zy = cat(&mut ctx, &[z, y]);
        let t = cat(&mut ctx, &[x, zy]);
        let r = regex::concat(vec![regex::star_lit_test("a"), regex::lit_test("z"), regex::star_lit_test("a")]);
        let a = memb(&mut ctx, t, &r);
        let mut m = ModelBuilder::default();
        pin_len(&mut ctx, &mut m, x, 2);
        pin_len(&mut ctx, &mut m, y, 1);
        let mut eq = EqualityEngine::default();
        let s = joint_seeds(&mut ctx, &mut eq, &[x, y, z, zy, t], &[(a, true)], &m);
        assert_eq!(s.get(&x).map(String::as_str), Some("aa"));
        assert_eq!(s.get(&y).map(String::as_str), Some("a"));
    }

    #[test]
    fn flatten_rejects_above_alphabet_constant() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let hi = ctx.mk_string_const(&char::from_u32(0x30000).unwrap().to_string());
        let ok = ctx.mk_string_const("\u{10000}");
        let bad = cat(&mut ctx, &[x, hi]);
        let good = cat(&mut ctx, &[x, ok]);
        let mut out = Vec::new();
        assert!(!flatten(&ctx, bad, &mut out));
        out.clear();
        assert!(flatten(&ctx, good, &mut out));
        assert_eq!(out.len(), 2);
    }

    #[test]
    fn groups_link_constraints_by_shared_leaves() {
        let mut ctx = Context::new();
        let (x, y, z) = (var(&mut ctx, "x"), var(&mut ctx, "y"), var(&mut ctx, "z"));
        let raw = vec![
            (vec![RawOp::Leaf(x), RawOp::Lit(vec![97])], Rex::Eps),
            (vec![RawOp::Leaf(z)], Rex::Eps),
            (vec![RawOp::Leaf(y), RawOp::Leaf(x)], Rex::Eps),
        ];
        assert_eq!(groups(&raw), vec![vec![0, 2], vec![1]]);
    }
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(joint_seed::front_tests)'`
Expected: compile errors — `joint_seeds`, `flatten`, `groups`, `RawOp` not found.

- [ ] **Step 3: Make `class_len_in_model` crate-visible**

In `crates/shinri-str/src/model.rs:56` change `fn class_len_in_model(` to `pub(crate) fn class_len_in_model(`.

- [ ] **Step 4: Implement the front end**

In `joint_seed.rs`, extend the imports:

```rust
use crate::model;
use crate::regex::{self, Rex};
use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::{EqualityEngine, ModelBuilder};
```

and add after `solve_group`:

```rust
/// An operand before leaves are numbered within their group.
#[derive(Clone, Debug, PartialEq, Eq)]
enum RawOp {
    Lit(Vec<u32>),
    Leaf(TermId),
}

fn is_leaf(terms: &Context, t: TermId) -> bool {
    matches!(
        terms.term_node(t),
        TermNode::App { op: Op::Uninterpreted(_), args, .. } if terms.children(*args).is_empty()
    )
}

/// Flatten `t` into constants and nullary leaves (nested concats inlined).
/// False if an operand is anything else, or a constant holds a character
/// above the SMT-LIB alphabet (spec §4.2).
fn flatten(terms: &Context, t: TermId, out: &mut Vec<RawOp>) -> bool {
    if let Some(s) = terms.string_const_value(t) {
        let cs: Vec<u32> = s.chars().map(|c| c as u32).collect();
        if cs.iter().any(|&c| c > regex::MAX_CODE) {
            return false;
        }
        out.push(RawOp::Lit(cs));
        return true;
    }
    if is_leaf(terms, t) {
        out.push(RawOp::Leaf(t));
        return true;
    }
    match terms.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => terms
            .children(*args)
            .to_vec()
            .into_iter()
            .all(|k| flatten(terms, k, out)),
        _ => false,
    }
}

/// Connected components of `raw`'s constraints, linked by shared leaves:
/// each component's constraints in input order, components ordered by
/// their first constraint.
fn groups(raw: &[(Vec<RawOp>, Rex)]) -> Vec<Vec<usize>> {
    fn find(p: &mut [usize], mut i: usize) -> usize {
        while p[i] != i {
            p[i] = p[p[i]];
            i = p[i];
        }
        i
    }
    let mut parent: Vec<usize> = (0..raw.len()).collect();
    let mut first: FxHashMap<TermId, usize> = FxHashMap::default();
    for (ci, (ops, _)) in raw.iter().enumerate() {
        for op in ops {
            if let RawOp::Leaf(l) = op {
                match first.get(l) {
                    Some(&cj) => {
                        let (a, b) = (find(&mut parent, ci), find(&mut parent, cj));
                        parent[a.max(b)] = a.min(b);
                    }
                    None => {
                        first.insert(*l, ci);
                    }
                }
            }
        }
    }
    let mut out: Vec<Vec<usize>> = Vec::new();
    let mut slot: FxHashMap<usize, usize> = FxHashMap::default();
    for ci in 0..raw.len() {
        let r = find(&mut parent, ci);
        let g = *slot.entry(r).or_insert_with(|| {
            out.push(Vec::new());
            out.len() - 1
        });
        out[g].push(ci);
    }
    out
}

/// Slice 61: joint words for the free leaves of concat-subject memberships
/// (spec §4). Groups eligible constraints by shared leaves; a group whose
/// leaves are all repair-eligible is solved at the leaves' model lengths
/// (pass 1), then at free lengths (pass 2). A group yields a word for every
/// leaf or nothing. The caller merges the result over `memb_seeds`.
pub(crate) fn joint_seeds(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    membs: &[(TermId, bool)],
    m: &ModelBuilder,
) -> FxHashMap<TermId, String> {
    let mut bare: FxHashMap<TermId, Vec<Rex>> = FxHashMap::default();
    let mut raw: Vec<(Vec<RawOp>, Rex)> = Vec::new();
    for &(atom, pos) in membs {
        let (t, re_t) = crate::memb::memb_sides(terms, atom);
        let Some(mut rex) = regex::extract_const_regex(terms, re_t) else {
            continue;
        };
        if !pos {
            rex = regex::comp(rex);
        }
        if is_leaf(terms, t) {
            bare.entry(t).or_default().push(rex);
            continue;
        }
        let mut ops = Vec::new();
        if !model::is_concat(terms, t)
            || !flatten(terms, t, &mut ops)
            || !ops.iter().any(|o| matches!(o, RawOp::Leaf(_)))
        {
            continue;
        }
        // A class constant dictates the subject's value (spec §4.2).
        let pinned = model::class_member(terms, eq, known, t, |tm, mm| {
            tm.string_const_value(mm).is_some()
        });
        if pinned.is_none() {
            raw.push((ops, rex));
        }
    }
    let mut out = FxHashMap::default();
    for group in groups(&raw) {
        // Leaves in first-occurrence order: `solve_group`'s leaf order.
        let mut leaves: Vec<TermId> = Vec::new();
        for &ci in &group {
            for op in &raw[ci].0 {
                if let RawOp::Leaf(l) = op {
                    if !leaves.contains(l) {
                        leaves.push(*l);
                    }
                }
            }
        }
        if leaves
            .iter()
            .any(|&l| model::is_repair_pinned(terms, eq, known, l))
        {
            continue;
        }
        let cons: Vec<JConstraint> = group
            .iter()
            .map(|&ci| JConstraint {
                ops: raw[ci]
                    .0
                    .iter()
                    .map(|op| match op {
                        RawOp::Lit(cs) => JOp::Lit(cs.clone()),
                        RawOp::Leaf(l) => JOp::Leaf(
                            leaves.iter().position(|x| x == l).expect("collected above"),
                        ),
                    })
                    .collect(),
                rex: raw[ci].1.clone(),
            })
            .collect();
        let own: Vec<Rex> = leaves
            .iter()
            .map(|l| regex::inter(bare.get(l).cloned().unwrap_or_default()))
            .collect();
        let lens: Vec<usize> = leaves
            .iter()
            .map(|&l| model::class_len_in_model(terms, eq, known, m, l))
            .collect();
        let words = match solve_group(&own, &cons, Lengths::Fixed(&lens)) {
            Outcome::Found(w) => Some(w),
            _ => match solve_group(&own, &cons, Lengths::Free(JOINT_FREE_LEN_CAP)) {
                Outcome::Found(w) => Some(w),
                _ => None,
            },
        };
        if let Some(words) = words {
            out.extend(leaves.into_iter().zip(words));
        }
    }
    out
}
```

Remove the Task-1 `#![cfg_attr(not(test), allow(dead_code))]` line if it was added. Note `regex::inter(Vec::new())` is Σ* (its documented empty case), which is the own language of a leaf with no bare membership.

- [ ] **Step 5: Wire into `model_with`**

In `crates/shinri-str/src/lib.rs`, replace

```rust
        let seeds = model::memb_seeds(cx.terms, cx.eq, &known, &membs, m);
```

with

```rust
        let mut seeds = model::memb_seeds(cx.terms, cx.eq, &known, &membs, m);
        // Slice 61: joint words for the free leaves of concat-subject
        // memberships override those leaves' per-leaf seeds.
        seeds.extend(joint_seed::joint_seeds(cx.terms, cx.eq, &known, &membs, m));
```

- [ ] **Step 6: Run the crate's tests**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str`
Expected: every test passes, including the 8 new `front_tests` and the 13 from Tasks 1–2; no existing test edited. If an existing test fails, stop and report (Global Constraints).

- [ ] **Step 7: Check the reproducers end to end**

```bash
taskset -c 0-11 cargo build --release -p shinri-cli
for f in target/slice61-base/probes/*.smt2; do printf '%s\t' $(basename $f); target/release/shinri --stats $f 2>&1 | grep '^stats:'; done
```

Expected: `norn531` and `regex035` print `outcome=sat`; `empty` is not `sat`; no line is `unsat` for a file z3 called `sat` (Task 0 Step 4). If `norn531` is still `unknown`, look at Task 0's recorded leaf lengths and the `detail=` tag before changing anything, and report.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all && mise run lint
git add crates/shinri-str/src/joint_seed.rs crates/shinri-str/src/model.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice61 - joint seeds for concat-subject memberships in model_with"
```

---

### Task 4: Blocking-tier probes

**Files:**
- Create: `crates/shinri-solver/tests/slice61_probes.rs`

**Interfaces:**
- Consumes: the wired solver from Task 3 (`shinri_solver::{Solver, CommandResponse}`, `shinri_parser::Parser`).
- Produces: the scripts `NORN_531`, `REGEX_035`, `JOINT_EMPTY`, `JOINT_EMPTY_SAT`, `LEN_PIN` — Task 5 copies them verbatim.

- [ ] **Step 1: Write the probes**

```rust
//! Slice 61 probes (spec §7.2). The free leaves of a concat-subject
//! membership were never seeded jointly, so both reproducers answered
//! `unknown` (`str-model-rejected`, `violated:memb@not-needed`) at the branch
//! point. Each `sat` case re-checks its witness by pinning the `get-value`
//! answers and re-solving: the pinned memberships are ground and fold through
//! the slice-19 evaluator, independent of the seeding path. Each case that
//! must not be `sat` has a `sat` sibling, so the fix cannot pass by
//! refusing everything.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn run_script(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

/// `QF_SLIA/2015-Norn/HammingDistance/norn-benchmark-531.smt2`, assertions
/// verbatim (z3 `sat`: `var_8 = "a"`, `var_9 = "aa"`).
const NORN_531: &str = r#"(set-logic QF_SLIA)
(declare-fun var_8 () String)
(declare-fun var_9 () String)
(assert (str.in_re (str.++ var_8 "z" var_9 ) (re.++ (re.* (re.++ (str.to_re "a") (re.++ (re.* (re.union (str.to_re "b") (str.to_re "a"))) (str.to_re "z")))) (re.++ (str.to_re "a") (re.* (re.union (str.to_re "b") (str.to_re "a")))))))
(assert (str.in_re (str.++ var_8 "z" var_9 ) (re.++ (re.* (re.union (str.to_re "z") (re.++ (str.to_re "a") (re.++ (re.* (str.to_re "a")) (str.to_re "z"))))) (re.++ (str.to_re "a") (re.* (str.to_re "a"))))))
(assert (str.in_re var_9 (re.* (re.range "a" "u"))))
(assert (str.in_re var_8 (re.* (re.range "a" "u"))))
(assert (not (str.in_re (str.++ "b" var_8 "z" "b" var_9 ) (re.++ (re.* (re.union (re.union (str.to_re "z") (str.to_re "b")) (re.++ (str.to_re "a") (re.union (str.to_re "z") (str.to_re "a"))))) (str.to_re "a")))))
"#;

/// `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-035-reverse-fuzz.smt2`
/// (z3 `sat`).
const REGEX_035: &str = r#"(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ y x) (re.* (str.to_re "b"))))
"#;

/// Jointly empty (z3 `unsat`); concat-subject emptiness is queued, so
/// `unknown` is expected, but never `sat`.
const JOINT_EMPTY: &str = r#"(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))
(assert (str.in_re x (re.+ (str.to_re "b"))))
"#;

const JOINT_EMPTY_SAT: &str = r#"(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))
(assert (str.in_re x (re.+ (str.to_re "a"))))
"#;

/// z3 `sat` (e.g. x = "aba", y = "b"). Pass 2 may ignore the pin; the gate
/// must then reject, never print a bad witness.
const LEN_PIN: &str = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "ab"))))
(assert (= (str.len x) 3))
"#;

/// Runs `body` with `(check-sat)(get-value (vars))`; on `sat`, pins every
/// value and re-solves, returning the first verdict.
fn verdict_with_witness_check(body: &str, vars: &[&str]) -> String {
    let out = run_script(&format!("{body}(check-sat)\n(get-value ({}))\n", vars.join(" ")));
    if out[0] == "sat" {
        let values = &out[1];
        let mut pinned = body.to_string();
        for v in vars {
            let at = values.find(&format!("({v} \"")).expect("get-value shape") + v.len() + 3;
            let end = at + values[at..].find("\")").expect("closing quote");
            pinned.push_str(&format!("(assert (= {v} \"{}\"))\n", &values[at..end]));
        }
        assert_eq!(
            run_script(&format!("{pinned}(check-sat)\n")),
            vec!["sat"],
            "witness rejected: {values}"
        );
    }
    out[0].clone()
}

#[test]
fn norn_531_sat_with_valid_witness() {
    assert_eq!(verdict_with_witness_check(NORN_531, &["var_8", "var_9"]), "sat");
}

#[test]
fn regex_035_sat_with_valid_witness() {
    assert_eq!(verdict_with_witness_check(REGEX_035, &["x", "y"]), "sat");
}

#[test]
fn joint_empty_not_sat() {
    assert_ne!(verdict_with_witness_check(JOINT_EMPTY, &["x", "y"]), "sat");
}

#[test]
fn joint_empty_sat_sibling() {
    assert_eq!(verdict_with_witness_check(JOINT_EMPTY_SAT, &["x", "y"]), "sat");
}

#[test]
fn length_pin_sound() {
    // Never unsat (z3 sat); a sat witness is re-checked inside the helper.
    assert_ne!(verdict_with_witness_check(LEN_PIN, &["x", "y"]), "unsat");
}
```

The witness parser takes the text between `(<var> "` and the next `")`; a witness containing `")` would need escaping, which these alphabets never produce.

- [ ] **Step 2: Run them**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice61_probes)'`
Expected: 5 tests discovered, 5 passed. Record the actual verdicts of `joint_empty_not_sat` and `length_pin_sound` (add `eprintln!`s locally if needed, do not commit them) for the report.

- [ ] **Step 3: Confirm the probes are RED on the base code**

```bash
git worktree add --detach ../slice61-red main
cp crates/shinri-solver/tests/slice61_probes.rs ../slice61-red/crates/shinri-solver/tests/
(cd ../slice61-red && CARGO_TARGET_DIR=/workspace/target/slice61-red taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice61_probes)' 2>&1 | tail -15)
git worktree remove --force ../slice61-red
```

Expected on `main`: `norn_531_sat_with_valid_witness` and `regex_035_sat_with_valid_witness` FAIL (`unknown`). Record which of the other three pass on `main`.

- [ ] **Step 4: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/slice61_probes.rs
git commit -m "test(solver): slice61 - probes for concat-subject joint seeds"
```

---

### Task 5: z3 differential oracle

**Files:**
- Create: `crates/shinri-solver/tests/joint_seed_oracle.rs`

**Interfaces:**
- Consumes: Task 4's scripts (copied verbatim without the `(set-logic …)` line), the `oracle` feature of `shinri-solver`, `easy_smt`.
- Produces: the oracle binary `joint_seed_oracle` (Task 6 counts it).

- [ ] **Step 1: Write the oracle**

```rust
//! Differential oracle (slice 61, spec §7.3): concat-subject memberships
//! over 1–3 free leaves with constants between them, mixed polarity,
//! optional bare memberships and an optional length pin. Every decided
//! shinri answer must match z3, and every shinri `sat` witness, re-asserted
//! into z3, must be `sat`.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(joint_seed_oracle)'
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Copied from tests/nary_arith_oracle.rs (the per-binary convention).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0 >> 16
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const N_ITERS: usize = 200;

/// Copied verbatim from tests/slice61_probes.rs (minus `set-logic`).
const NORN_531: &str = r#"(declare-fun var_8 () String)
(declare-fun var_9 () String)
(assert (str.in_re (str.++ var_8 "z" var_9 ) (re.++ (re.* (re.++ (str.to_re "a") (re.++ (re.* (re.union (str.to_re "b") (str.to_re "a"))) (str.to_re "z")))) (re.++ (str.to_re "a") (re.* (re.union (str.to_re "b") (str.to_re "a")))))))
(assert (str.in_re (str.++ var_8 "z" var_9 ) (re.++ (re.* (re.union (str.to_re "z") (re.++ (str.to_re "a") (re.++ (re.* (str.to_re "a")) (str.to_re "z"))))) (re.++ (str.to_re "a") (re.* (str.to_re "a"))))))
(assert (str.in_re var_9 (re.* (re.range "a" "u"))))
(assert (str.in_re var_8 (re.* (re.range "a" "u"))))
(assert (not (str.in_re (str.++ "b" var_8 "z" "b" var_9 ) (re.++ (re.* (re.union (re.union (str.to_re "z") (str.to_re "b")) (re.++ (str.to_re "a") (re.union (str.to_re "z") (str.to_re "a"))))) (str.to_re "a")))))
"#;
const REGEX_035: &str = r#"(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ y x) (re.* (str.to_re "b"))))
"#;
const JOINT_EMPTY: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))
(assert (str.in_re x (re.+ (str.to_re "b"))))
"#;
const JOINT_EMPTY_SAT: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))
(assert (str.in_re x (re.+ (str.to_re "a"))))
"#;
const LEN_PIN: &str = r#"(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "ab"))))
(assert (= (str.len x) 3))
"#;

/// shinri's verdict on `body` and, on `sat`, the quoted values of `vars` in
/// order (the text between each pair of quotes; the alphabets here have no
/// `"`).
fn shinri_run(body: &str, vars: &[&str]) -> (SolveOutcome, Vec<String>) {
    let full = format!(
        "(set-logic QF_SLIA)\n{body}(check-sat)\n(get-value ({}))\n",
        vars.join(" ")
    );
    let mut solver = Solver::new();
    let mut parser = Parser::new(&full);
    let mut outcome = SolveOutcome::Unknown;
    let mut values = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            CommandResponse::Values(s) => {
                values = s
                    .split('"')
                    .skip(1)
                    .step_by(2)
                    .map(str::to_string)
                    .collect();
            }
            _ => {}
        }
    }
    (outcome, values)
}

/// `timeout_s` is z3's wall-clock limit; a timeout comes back as `Unknown`.
fn z3_outcome(body: &str, timeout_s: u32) -> easy_smt::Response {
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver(
            "z3",
            [
                "-smt2".to_string(),
                "-in".to_string(),
                format!("-T:{timeout_s}"),
            ],
        )
        .build()
        .expect("failed to launch z3 — run `mise install`");
    ctx.set_logic("QF_SLIA").expect("z3 set-logic failed");
    for line in body.lines() {
        let t = line.trim();
        if t.starts_with("(declare-") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            let ack = ctx.raw_recv().expect("z3 ack failed");
            let ack = ctx.display(ack).to_string();
            assert!(
                !ack.contains("error"),
                "z3 rejected a line (assertion dropped): {ack}\n{t}"
            );
        }
    }
    match ctx.check() {
        Ok(r) => r,
        Err(e) if e.to_string().contains("timeout") => easy_smt::Response::Unknown,
        Err(e) => panic!("z3 check-sat failed: {e}\n{body}"),
    }
}

/// Checks one script against z3. Returns shinri's verdict; a z3 timeout
/// bumps `z3_timeouts`. A shinri `unsat` that z3 cannot confirm fails.
fn check(body: &str, vars: &[&str], timeout_s: u32, z3_timeouts: &mut usize) -> SolveOutcome {
    let (ours, values) = shinri_run(body, vars);
    let theirs = z3_outcome(body, timeout_s);
    if matches!(theirs, easy_smt::Response::Unknown) {
        *z3_timeouts += 1;
    }
    match (ours, theirs) {
        (SolveOutcome::Sat, easy_smt::Response::Unsat) => panic!("shinri sat, z3 unsat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Sat) => panic!("shinri unsat, z3 sat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Unknown) => {
            panic!("shinri unsat, z3 timed out (-T:{timeout_s}), unconfirmed:\n{body}")
        }
        _ => {}
    }
    if ours == SolveOutcome::Sat {
        assert_eq!(values.len(), vars.len(), "get-value shape:\n{body}");
        let mut pinned = body.to_string();
        for (v, val) in vars.iter().zip(&values) {
            pinned.push_str(&format!("(assert (= {v} \"{val}\"))\n"));
        }
        assert!(
            matches!(z3_outcome(&pinned, 20), easy_smt::Response::Sat),
            "z3 rejects shinri's witness {values:?}:\n{body}"
        );
    }
    ours
}

const REGEXES: [&str; 6] = [
    "(re.* (str.to_re \"a\"))",
    "(re.* (re.union (str.to_re \"a\") (str.to_re \"b\")))",
    "(re.++ (re.* (str.to_re \"a\")) (str.to_re \"z\") (re.* (str.to_re \"b\")))",
    "(re.+ (str.to_re \"ab\"))",
    "(re.++ (str.to_re \"a\") (re.* (re.range \"a\" \"z\")))",
    "(re.* (re.union (str.to_re \"z\") (re.++ (str.to_re \"a\") (str.to_re \"b\"))))",
];
const LITS: [&str; 3] = ["a", "b", "z"];
const NAMES: [&str; 3] = ["x", "y", "z"];

/// One generated script over leaves x, y, z (only the first 1–3 are used
/// in subjects; all three are declared and queried).
fn gen(rng: &mut Lcg) -> String {
    let mut body = String::from(
        "(declare-fun x () String)\n(declare-fun y () String)\n(declare-fun z () String)\n",
    );
    let leaves = 1 + rng.below(3) as usize;
    for _ in 0..1 + rng.below(3) {
        let mut ops: Vec<String> = (0..2 + rng.below(3))
            .map(|_| {
                if rng.below(3) == 0 {
                    format!("\"{}\"", LITS[rng.below(3) as usize])
                } else {
                    NAMES[rng.below(leaves as u64) as usize].to_string()
                }
            })
            .collect();
        if ops.iter().all(|o| o.starts_with('"')) {
            ops[0] = "x".to_string();
        }
        let re = REGEXES[rng.below(REGEXES.len() as u64) as usize];
        let a = format!("(str.in_re (str.++ {}) {re})", ops.join(" "));
        if rng.below(4) == 0 {
            body.push_str(&format!("(assert (not {a}))\n"));
        } else {
            body.push_str(&format!("(assert {a})\n"));
        }
    }
    for n in &NAMES[..leaves] {
        if rng.below(2) == 0 {
            body.push_str(&format!("(assert (str.in_re {n} (re.* (re.range \"a\" \"u\"))))\n"));
        }
    }
    if rng.below(4) == 0 {
        body.push_str(&format!("(assert (= (str.len x) {}))\n", rng.below(5)));
    }
    body
}

#[test]
fn joint_seed_probes_agree_with_z3() {
    let mut t = 0;
    assert_eq!(check(NORN_531, &["var_8", "var_9"], 20, &mut t), SolveOutcome::Sat);
    assert_eq!(check(REGEX_035, &["x", "y"], 20, &mut t), SolveOutcome::Sat);
    assert_ne!(check(JOINT_EMPTY, &["x", "y"], 20, &mut t), SolveOutcome::Sat);
    assert_eq!(check(JOINT_EMPTY_SAT, &["x", "y"], 20, &mut t), SolveOutcome::Sat);
    check(LEN_PIN, &["x", "y"], 20, &mut t);
}

#[test]
fn joint_seed_generated_agree_with_z3() {
    let mut rng = Lcg(61);
    let (mut sat, mut unsat, mut z3_timeouts) = (0usize, 0usize, 0usize);
    for _ in 0..N_ITERS {
        let body = gen(&mut rng);
        // -T is wall-clock: under heavy load a shinri-unsat / z3-timeout
        // failure is a possible flake (it fails closed).
        match check(&body, &NAMES, 3, &mut z3_timeouts) {
            SolveOutcome::Sat => sat += 1,
            SolveOutcome::Unsat => unsat += 1,
            _ => {}
        }
    }
    eprintln!(
        "joint_seed_oracle: {sat} sat, {unsat} unsat, {} unknown, {z3_timeouts} z3 unknown/timeouts",
        N_ITERS - sat - unsat
    );
    assert!(sat > 0, "generator must reach sat: {sat} sat, {unsat} unsat");
}
```

- [ ] **Step 2: Run it**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle -E 'binary(joint_seed_oracle)' --no-capture 2>&1 | tail -20`
Expected: 2 tests discovered, 2 passed; the tally line shows `sat > 0`. Record the tally for the report. A disagreement panic is a real bug: minimise the printed script into a Task 4 probe and fix it before continuing.

- [ ] **Step 3: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/joint_seed_oracle.rs
git commit -m "test(solver): slice61 - z3 differential over concat-subject joint seeds"
```

---

### Task 6: Gates

**Files:** none in the repo (`target/slice61-gates.txt`).

**Interfaces:**
- Consumes: branch HEAD after Tasks 1–5.
- Produces: `target/slice61-gates.txt` (Task 7 cites it).

- [ ] **Step 1: Run the blocking tier and lint**

```bash
cargo fmt --all --check && taskset -c 0-11 mise run ci 2>&1 | tee target/slice61-ci.log | tail -5
```

Expected: exit 0; nextest summary `N run / N passed / 6 skipped` with N = 1773 (slice-60 variant count) + this slice's blocking tests (`regex.rs` 2, `joint_seed` core 12, front 8, probes 5 → 1773 + 27 = **1800**). If N differs, explain the difference in the report instead of forcing it.

- [ ] **Step 2: Run the oracle suite**

```bash
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice61-oracle.log | tail -5
```

Expected: `M run / M passed / 2 skipped` with M = 831 + 5 probes + 2 oracle tests = **838** (this run counts shinri-solver's blocking tests too, as slice 60's 831 did). State the number; if it differs, explain why. The discovered count is non-zero.

- [ ] **Step 3: Record**

```bash
{ git rev-parse --short HEAD; tail -3 target/slice61-ci.log; tail -3 target/slice61-oracle.log; } | tee target/slice61-gates.txt
```

---

### Task 7: After runs, triage, attribution, timing, report, measured outcomes, PR

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice61-joint-concat-seeds-report.md` (date = the day the after runs finish)
- Modify: `docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md` (§8 report path → real date; append §11 *Measured outcomes*)

**Interfaces:**
- Consumes: branch HEAD after Tasks 1–6; Task 0's `target/slice61-base/*`; the base runs `bench/results/slice60b{,-sample}/results.jsonl`; `target/slice60b-after/shinri`; `target/slice59-sample-corpus/`; `target/slice61-gates.txt`.
- Produces: the report and spec section cited by the PR.

- [ ] **Step 1: Build and launch the after runs detached**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice61-after && cp target/release/shinri target/slice61-after/shinri
cp target/release/shinri-bench target/slice61-after/shinri-bench
md5sum target/slice61-after/shinri | tee target/slice61-after/md5.txt
git rev-parse --short HEAD | tee target/slice61-after/commit.txt
uptime | tee target/slice61-after/uptime-start.txt
date -u +%FT%TZ > target/slice61-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice61-after/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice61-after/shinri --run-id slice61 \
  > target/slice61-after/run.log 2>&1; \
  taskset -c 12-23 target/slice61-after/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice61-after/shinri --run-id slice61-sample \
  > target/slice61-after/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice61-after/finished.txt' \
  > /dev/null 2>&1 &
```

About 103,335 string rows (~1.75 h) then 2,000 sample rows (~20 min). Wait for `target/slice61-after/finished.txt` with a Monitor/until-loop, not a foreground sleep. If the 1-min load average is above 24 at launch (slice 60b ran at 70+), record it; it widens timing noise in triage.

- [ ] **Step 2: Render reports and join the runs (criteria 1, 2, 6)**

```bash
for id in slice60b slice61 slice60b-sample slice61-sample; do BENCH_RUN_ID=$id mise run bench-report; done
python3 - <<'EOF' | tee target/slice61-after/join.txt
import json, collections
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
changed = []
for base, after in (("slice60b", "slice61"), ("slice60b-sample", "slice61-sample")):
    a = load(f"bench/results/{base}/results.jsonl")
    b = load(f"bench/results/{after}/results.jsonl")
    assert a.keys() == b.keys(), f"row sets differ: {base} vs {after}"
    c = collections.Counter()
    for p in sorted(a):
        va, vb = a[p]["verdict"], b[p]["verdict"]
        if va != vb:
            c[(a[p]["logic"], va, vb)] += 1
            changed.append((p, a[p]["logic"], va, vb, a[p].get("fence_detail") or "-", after))
    print(f"== {base} -> {after}: {sum(c.values())} changed")
    for k, n in sorted(c.items()):
        print(" ", *k, n)
    print("  wrong rows after:", sum(1 for r in b.values() if r["verdict"] == "wrong"))
a = load("bench/results/slice60b/results.jsonl")
b = load("bench/results/slice61/results.jsonl")
TAG = "violated:memb@not-needed"
base_tag = [p for p in a if a[p].get("fence_detail") == TAG]
after_tag = [p for p in b if b[p].get("fence_detail") == TAG]
moved = [p for p in base_tag if b[p]["verdict"] == "correct"]
unver = [p for p in base_tag if b[p]["verdict"] == "unverified"]
print(f"criterion 2: {TAG} base {len(base_tag)} after {len(after_tag)}; "
      f"base-tag rows now correct {len(moved)} ({len(moved) / len(base_tag):.1%}); "
      f"need >= 87 and >= 20%; now unverified {len(unver)}")
fam = lambda p: "/".join(p.split("/")[1:-1])
print("moved by family:", collections.Counter(fam(p) for p in moved).most_common(10))
print("unverified by family:", collections.Counter(fam(p) for p in unver).most_common(10))
print("still tagged by family:", collections.Counter(fam(p) for p in after_tag).most_common(10))
print("moved by base status:", collections.Counter(a[p]["status"] or "none" for p in moved))
def tags(rows):
    return collections.Counter(r.get("fence_detail") for r in rows.values() if r["verdict"] == "unknown:str-model-rejected")
ta, tb = tags(a), tags(b)
print("fence_detail movement (base -> after):")
for t in sorted(set(ta) | set(tb), key=lambda t: -(ta[t] + tb[t])):
    print(f"  {t}: {ta[t]} -> {tb[t]}")
open("target/slice61-after/changed.tsv", "w").write("".join("\t".join(x) + "\n" for x in changed))
EOF
```

Expected: 0 wrong rows in both after runs (criterion 1; any hit stops the slice for a ruling). Criterion 2's line shows ≥ 87 rows and ≥ 20%. Sample-run changes go to Step 3 to be classified (criterion 6).

- [ ] **Step 3: Triage changed rows (criteria 1, 3, 6)**

Triage every row whose transition is **not** `unknown:* → correct`, and a family-stratified sample of ≥ 32 `unknown:* → correct` rows, 3 runs per binary, interleaved, on cores 12–23 with nothing else running:

```bash
python3 - <<'EOF'
import random, collections
rows = [l.rstrip("\n").split("\t") for l in open("target/slice61-after/changed.tsv")]
gain = [r for r in rows if r[2].startswith("unknown") and r[3] == "correct"]
other = [r for r in rows if r not in gain]
rng = random.Random(61)
fam = collections.defaultdict(list)
for r in gain:
    fam["/".join(r[0].split("/")[1:-1])].append(r)
pick = []
while len(pick) < min(32, len(gain)):
    for f in sorted(fam):
        if fam[f] and len(pick) < 32:
            pick.append(fam[f].pop(rng.randrange(len(fam[f]))))
open("target/slice61-after/triage-in.tsv", "w").write("".join("\t".join(r) + "\n" for r in other + pick))
print(len(other), "non-gain rows,", len(pick), "sampled gain rows")
EOF
while IFS="$(printf '\t')" read -r p logic va vb tag run; do
  case "$run" in *sample) root=target/slice59-sample-corpus ;; *) root=bench/corpus ;; esac
  for i in 1 2 3; do
    for bin in target/slice60b-after/shinri target/slice61-after/shinri; do
      r=$(taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats $root/$p 2>&1 \
          | grep -E '^(sat|unsat|unknown)$|^stats:|memory allocation' | tr '\n' ' ')
      printf '%s\t%s\t%s\t%s\n' "$p" "$(basename $(dirname $bin))" "$i" "$r"
    done
  done
done < target/slice61-after/triage-in.tsv | tee target/slice61-after/triage.tsv
```

If there are more than 200 non-gain rows, triage every small stratum in full and a seeded, family-stratified sample of ≥ 32 from each large one, and state the sizes (slice 60 did this). A row is *noise* if either binary's 3 runs disagree with each other or the two binaries agree on at least one run; *attributable* if each binary reproduces its own bench verdict 3/3 and they differ. Attributable `correct → non-correct` rows fail criterion 3; attributable sample-run rows fail criterion 6; a wrong answer from either binary fails criterion 1. Each stops the slice for a ruling.

For newly `unverified` `unsat` rows (z3 timed out), run the slice-60 cross-check: `z3 -T:120` and `cvc5 --tlimit=120000` per row; any `sat` is a criterion-1 failure. (This slice only builds models, so new `unsat` rows are not expected; if any appear, attribute them before continuing.)

- [ ] **Step 4: Pass attribution (spec §8 item 2) — throwaway, not committed**

Edit `joint_seeds` in the working tree (reverted at the end of this step):
- change the outer `Outcome::Found(w) => Some(w),` arm to `Outcome::Found(w) => { eprintln!("slice61-trace: pass1"); Some(w) }`;
- change the inner (pass-2) `Outcome::Found(w) => Some(w),` arm to `Outcome::Found(w) => { eprintln!("slice61-trace: pass2"); Some(w) }`;
- add `eprintln!("slice61-trace: none");` in the final `_ => None` arm's place (`_ => { eprintln!("slice61-trace: none"); None }`);
- add `eprintln!("slice61-trace: skip-pinned");` right before the `continue;` of the `is_repair_pinned` check.

```bash
cargo build --release -p shinri-cli --target-dir target/slice61-trace
python3 - <<'EOF' > target/slice61-after/attr-in.txt
import random
rows = [l.split("\t") for l in open("target/slice61-after/changed.tsv")]
gain = sorted(r[0] for r in rows if r[2].startswith("unknown") and r[3] == "correct" and r[5].strip() == "slice61")
print("\n".join(random.Random(61).sample(gain, min(40, len(gain)))))
EOF
while read -r p; do
  t=$(timeout 20 target/slice61-trace/release/shinri bench/corpus/$p 2>&1 | grep -o 'slice61-trace: [a-z0-9-]*' | sort | uniq -c | tr '\n' ' ')
  printf '%s\t%s\n' "$p" "$t"
done < target/slice61-after/attr-in.txt | tee target/slice61-after/attribution.tsv
python3 - <<'EOF' > target/slice61-after/still-in.txt
import json, random
b = [r for r in map(json.loads, open("bench/results/slice61/results.jsonl")) if "path" in r]
tag = sorted(r["path"] for r in b if r.get("fence_detail") == "violated:memb@not-needed")
print("\n".join(random.Random(61).sample(tag, min(10, len(tag)))))
EOF
while read -r p; do
  t=$(timeout 20 target/slice61-trace/release/shinri bench/corpus/$p 2>&1 | grep -o 'slice61-trace: [a-z0-9-]*' | sort | uniq -c | tr '\n' ' ')
  printf '%s\t%s\n' "$p" "${t:-no-group}"
done < target/slice61-after/still-in.txt | tee target/slice61-after/still.tsv
git checkout -- crates && git status --short crates
```

Expected: `git status --short crates` prints nothing. Summarise: pass 1 vs pass 2 among gains; for the still-tagged sample, whether a group was solved (then the gate rejected for another reason), not solved (`none`), skipped as pinned, or never formed (`no-group`).

- [ ] **Step 5: Timing (criterion 4)**

Gate on load: wait until the 1-min load average is ≤ 24 (record it). Then:

```bash
python3 - <<'EOF' | tee target/slice61-after/timing.txt
import json, random, subprocess, time, statistics
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
a = load("bench/results/slice60b/results.jsonl")
b = load("bench/results/slice61/results.jsonl")
BIN = {"base": "target/slice60b-after/shinri", "after": "target/slice61-after/shinri"}
rng = random.Random(61)
groups = {lg: sorted(p for p in a if a[p]["logic"] == lg and a[p]["verdict"] == b[p]["verdict"] == "correct")
          for lg in ("QF_S", "QF_SLIA")}
groups["newly-correct"] = sorted(p for p in a if a[p]["verdict"] != "correct" and b[p]["verdict"] == "correct")
for name, rows in groups.items():
    sample = rng.sample(rows, min(150, len(rows)))
    tot = {"base": 0.0, "after": 0.0}
    for p in sample:
        for which in ("base", "after"):
            t0 = time.monotonic()
            subprocess.run(["taskset", "-c", "12", BIN[which], f"bench/corpus/{p}"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
            tot[which] += time.monotonic() - t0
    print(name, len(sample), "rows: base %.2f s, after %.2f s, ratio %.3f"
          % (tot["base"], tot["after"], tot["after"] / tot["base"]))
for lg in ("QF_S", "QF_SLIA"):
    both = [p for p in a if a[p]["logic"] == lg and a[p]["verdict"] == b[p]["verdict"] == "correct"]
    for name, d in (("base", a), ("after", b)):
        ms = sorted(d[p]["wall_ms"] for p in both)
        print(lg, name, "median", statistics.median(ms), "p90", ms[int(0.9 * len(ms))])
EOF
```

Expected: QF_S and QF_SLIA ratios within 0.95–1.05 (criterion 4). If a pass lands outside, run it twice more and pool the three, stating so (slice 59/60 practice). The newly-correct ratio is reported, not gated.

- [ ] **Step 6: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-05-smtlib-2024-slice60-head-classes-report.md`:
- *Headline*: rows moved to `correct` (sat/unsat split), criterion-2 numbers, `unverified` count, criteria summary
- *Commands*: the exact commands from Tasks 0 and 7
- *Runs*: both binaries with md5 and commit (base = `56997aa`, reused `slice60b` runs; state why that is the spec's `5aa164a` base), started/finished, row counts, load at launch
- *Success criteria*: spec §8 table, each PASS/FAIL with evidence (gates from `target/slice61-gates.txt`; Task 0 Step 4 / Task 4 probe outcomes, RED on `main`)
- *Verdict changes*: `join.txt` transitions; the `fence_detail` movement table; moved / unverified / still-tagged rows by family
- *Triage*: dispositions from `triage.tsv`, plus any unsat cross-check
- *Pass attribution*: `attribution.tsv` and `still.tsv` summarised
- *Timing*: `timing.txt`
- *What changed versus the spec*: every deviation, including this plan's task reordering
- *Queued for the next slice*: re-ranked on the after run's `fence_detail` counts: what is left of class 1 and why (from `still.tsv`), then slice-60 queue items 4 onward (item 4 concat-subject emptiness first), the candidate (c) note, and the carried lists verbatim; state every re-rank

- [ ] **Step 7: Append §11 *Measured outcomes* to the spec**

Add `## 11. Measured outcomes` at the end of the spec: a one-line pointer to the report, the criteria table with PASS/FAIL and key numbers, the `violated:memb@not-needed` before/after count, and a *Deviations from this spec* subsection. Fix the §8 report path to the real date.

- [ ] **Step 8: Commit and open the PR**

```bash
git add docs/superpowers/research docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md
git commit -m "docs(bench+spec): slice61 - joint concat seeds run and measured outcomes"
git push -u origin slice61-joint-concat-seeds
gh pr create --base main --title "slice61: joint seeds for concat-subject memberships" --body "$(cat <<'EOF'
Spec: docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md
Plan: docs/superpowers/plans/2026-10-05-shinri-slice61-joint-concat-seeds.md
Report: docs/superpowers/research/<date>-smtlib-2024-slice61-joint-concat-seeds-report.md

The free leaves of concat-subject memberships now get jointly chosen witness words at model-build time (`joint_seed::joint_seeds`, merged over `memb_seeds`), so the gate stops rejecting the composed concat.

<criteria table and violated:memb@not-needed before/after from spec §11>
EOF
)"
```

Fill `<date>` and the criteria lines from the report before running. Wait for CI; when it is green, ask the user before merging (merge commit, then delete the branch remote and local).
