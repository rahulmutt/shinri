# Slice 60 — Head-only next-character classes Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `regex::next_classes` partition Σ by the bounds of head-reachable `Range` nodes only, so the membership witness search, the emptiness conflict and Rule-E stop fencing at `CLASS_SPLIT_CAP` on long literals, and measure the effect on the `violated:memb@not-needed` population.

**Architecture:** One private function changes in `crates/shinri-str/src/regex.rs`: `range_bounds` (every `Range` in the regex) is replaced by `head_bounds` (only the `Range` nodes `deriv` can test on the next character). `next_classes` keeps its signature, its cap and its callers. New tests: unit tests in `regex.rs`, a blocking probe file and an oracle file in `shinri-solver`. A base/after bench run and a report close the slice.

**Tech Stack:** Rust workspace (toolchain pinned in `mise.toml`), cargo-nextest 0.9.140, z3 from mise (oracle, via the existing `easy-smt` dev-dependency), `shinri-bench` for the SMT-LIB 2024 run, python3 for analysis scripts.

**Spec:** `docs/superpowers/specs/2026-10-04-shinri-slice60-head-classes-design.md`

## Global Constraints

- `next_classes` keeps its signature `pub(crate) fn next_classes(r: &Rex) -> Option<Vec<(u32, u32)>>`, its `CLASS_SPLIT_CAP` (64) check and all four callers unchanged (spec §4.1, §5).
- No change to `deriv`, `nullable`, any cap value, any fence site, `memb_seeds`' eligibility, the model gate, fence names or `fence_detail` tags (spec §5).
- No new dependency of any kind (pure-Rust mandate; `shinri-str` has no dev-dependencies and needs none).
- Existing tests pass **unmodified**, including `next_classes_partition_sigma`, `language_empty_class_split_overflow_taints_to_unknown` and `script_e2e::in_re_unfold_unknown_class_cap` (spec §7.1, §7.2, §7.4). If one fails, stop and report; do not edit it.
- Oracle tests only run with `--features oracle`; without it they silently run 0 tests. Always confirm a non-zero discovered count (AGENTS.md).
- nextest filters use the expression form `-E 'test(<name>)'` / `-E 'binary(<name>)'` (AGENTS.md).
- `cargo fmt --all` before every commit; `mise run lint` (clippy `-D warnings`) must be clean.
- Bench: string runs over QF_S and QF_SLIA; neutrality sample = the slice-59 seed-59 corpus `target/slice59-sample-corpus` (2,000 rows over QF_BVFP, QF_DT, QF_LIA, QF_LRA, QF_UF, QF_UFLIA, QF_UFLRA); `--timeout 20 --mem-mb 3072 --jobs 6`; detached with `setsid` under `taskset -c 12-23`; base built from the branch point (spec §8).
- While a bench run is live, run builds and tests on cores 0–11 (`taskset -c 0-11 …`).
- Branch `slice60-head-classes` off `main`; PR to `main`, merge commit when CI is green, then delete the branch remote and local (AGENTS.md). Ask the user before merging.

## Review Focus

1. **A head that is genuinely wider than the cap** (a 70-way union of isolated characters, or `re.* (re.union range×33)`). Expected: `next_classes` still returns `None`; `language_empty` → `Unknown`; the solver answers `unknown`. Pinned by the existing, unmodified `language_empty_class_split_overflow_taints_to_unknown`, `next_classes_partition_sigma` (cap case) and `script_e2e::in_re_unfold_unknown_class_cap`; Task 4 Step 3 runs them by name.
2. **A non-nullable element that only *looks* optional: `comp(a*)·m`.** `comp(a*)` excludes ε, so `deriv` never reaches `m`. Expected: classes cut at `a` only, not at `m`. Pinned in Task 1 (`next_classes_head_only_concat_shapes`, the `comp(a*)·m` row).
3. **Surrogate-block and beyond-BMP ranges at the head.** Expected: classes still cut exactly at `0xD800` / `0xE000` and `MAX_CODE` stays covered; `deriv` uniform across every class. Pinned in Task 1 (`next_classes_head_only_concat_shapes`, the surrogate row; `next_classes_head_only_uniform_sweep` draws `arb_range` leaves and probes the block edges).
4. **A concat subject going through Rule-E** (not the lone-free-leaf witness path) over a long literal: previously fenced at the cap, now expanded into a handful of disjuncts. Expected: any decided answer agrees with z3 and any `sat` witness satisfies z3. Pinned in Task 3 (the generator's `(str.++ x y)` subject).
5. **A `sat` answer whose witness is wrong** (the search returns a word that a membership rejects). Expected: the model gate rejects it, so shinri never prints `sat` with a bad value. Pinned in Task 2 (exact `get-value` strings) and Task 3 (every shinri `sat` witness is re-asserted into z3, which must answer `sat`).

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-str/src/regex.rs` | Modify | `head_bounds` replaces `range_bounds`; `next_classes` doc + call; new unit tests in `mod tests` |
| `crates/shinri-solver/tests/slice60_probes.rs` | Create | blocking-tier probes: the reproducer `unsat`, two `sat` witnesses |
| `crates/shinri-solver/tests/head_classes_oracle.rs` | Create | z3 differential over the probes and generated `re.+` intersections (`--features oracle`) |
| `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice60-head-classes-report.md` | Create | bench report and rewritten queue |
| `docs/superpowers/specs/2026-10-04-shinri-slice60-head-classes-design.md` | Modify | append §11 *Measured outcomes* |

---

### Task 0: Branch, base binary, base runs

**Files:** none in the repo (artifacts under `target/slice60-base/`, `bench/results/slice60-base*/`).

**Interfaces:**
- Consumes: `target/slice59-sample-corpus/` (exists from slice 59; 2,000 hard-linked rows).
- Produces: `target/slice60-base/shinri`, `target/slice60-base/finished.txt`, `bench/results/slice60-base/results.jsonl`, `bench/results/slice60-base-sample/results.jsonl` — Task 5 consumes all four.

- [ ] **Step 1: Create the slice branch**

```bash
cd /workspace && git checkout main && git pull --ff-only && git checkout -b slice60-head-classes
```

- [ ] **Step 2: Confirm the sample corpus is intact**

Run: `find target/slice59-sample-corpus -name '*.smt2' | wc -l; wc -l < target/slice59-sample.txt`
Expected: `2000` and `2000`. If the directory is missing, rebuild it with slice-59 plan Task 0 Step 4 (`docs/superpowers/plans/2026-10-04-shinri-slice59-model-rejected-classes.md`), seed 59, unchanged.

- [ ] **Step 3: Build and freeze the base binary**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice60-base && cp target/release/shinri target/slice60-base/shinri
cp target/release/shinri-bench target/slice60-base/shinri-bench
md5sum target/slice60-base/shinri | tee target/slice60-base/md5.txt
git rev-parse --short HEAD | tee target/slice60-base/commit.txt
```

- [ ] **Step 4: Record the base behaviour of the three probe shapes**

```bash
D=target/slice60-base/probes && mkdir -p $D
L='!#%'"'"')+-/13579;=?ACEGIKMOQSUWY[]_acegikmo'
printf '(set-logic QF_S)(declare-fun x () String)\n(assert (str.in_re x (re.+ (str.to_re "%s"))))\n(assert (str.in_re x (re.+ (str.to_re "%s%s"))))\n(assert (str.in_re x (re.* (re.range "!" "~"))))\n(check-sat)\n' "$L" "$L" "$L" > $D/shared.smt2
printf '(set-logic QF_S)(declare-fun x () String)\n(assert (str.in_re x (re.+ (str.to_re "%s"))))\n(assert (= (str.len x) 80))\n(check-sat)\n' "$L" > $D/pin.smt2
cp bench/corpus/QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-010-reverse-multiply-fuzz.smt2 $D/regex010.smt2
for f in $D/*.smt2; do printf '%s\t' $(basename $f); target/slice60-base/shinri --stats $f 2>&1 | grep '^stats:'; done | tee target/slice60-base/probes.txt
```

Expected (measured while planning): all three print `outcome=unknown fence=str-model-rejected detail=violated:memb@not-needed`. z3 answers `sat`, `sat`, `unsat` respectively.

- [ ] **Step 5: Launch both base runs detached (strings, then the sample)**

```bash
date -u +%FT%TZ > target/slice60-base/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice60-base/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice60-base/shinri --run-id slice60-base \
  > target/slice60-base/run.log 2>&1; \
  taskset -c 12-23 target/slice60-base/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice60-base/shinri --run-id slice60-base-sample \
  > target/slice60-base/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice60-base/finished.txt' \
  > /dev/null 2>&1 &
```

About 103,335 string rows (~1.75 h) then 2,000 sample rows (~20 min). Do not wait: Tasks 1–4 proceed on cores 0–11. Task 5 waits for `target/slice60-base/finished.txt`.

---

### Task 1: `head_bounds` in `next_classes`

**Files:**
- Modify: `crates/shinri-str/src/regex.rs:415-458` (`range_bounds` → `head_bounds`, `next_classes` doc and call)
- Test: `crates/shinri-str/src/regex.rs` `mod tests` (append after `language_empty_class_split_overflow_taints_to_unknown`, the last test in the module)

**Interfaces:**
- Consumes: `nullable(&Rex) -> bool`, `deriv(u32, &Rex) -> Rex`, `concat`, `union`, `inter`, `star`, `comp`, `loop_`, `MAX_CODE`, `CLASS_SPLIT_CAP`, `search_word(&Rex, usize) -> Option<String>`, `search_shortest(&Rex) -> Option<String>`, `language_empty(&Rex) -> Emptiness`, `eval_membership(&str, &Rex) -> Option<bool>`; in `mod tests`: `chr(char) -> Rex`, `lit(&str) -> Rex`, `struct Lcg(u64)` with `fn next(&mut self) -> u64`, `fn arb_range(g: &mut Lcg) -> Rex`.
- Produces: `fn head_bounds(r: &Rex, out: &mut BTreeSet<u32>)` (private); `next_classes` unchanged in signature, coarser in result. Nothing else in the workspace calls `range_bounds` (verify with `grep -rn range_bounds crates`; expected: only the definition and its one call in `next_classes`).

- [ ] **Step 1: Write the failing tests**

Append inside `mod tests` in `crates/shinri-str/src/regex.rs`, after the last test:

```rust
    // ── Slice 60: head-only next-character classes ───────────────────────

    /// `r+` as `extract_const_regex` builds it: `r · r*`.
    fn plus_rex(r: Rex) -> Rex {
        concat(vec![r.clone(), star(r)])
    }

    /// 40 pairwise NON-adjacent printable chars ('!' + 2i). Each is an
    /// isolated range, so the pre-slice-60 all-ranges partition of any regex
    /// containing this word has 1 + 2·40 = 81 cuts > CLASS_SPLIT_CAP.
    fn isolated40() -> String {
        (0..40u32)
            .map(|i| char::from_u32(0x21 + 2 * i).unwrap())
            .collect()
    }

    /// The class lower bounds (= the cut points) of `next_classes(r)`.
    fn los(r: &Rex) -> Vec<u32> {
        next_classes(r)
            .expect("under the cap")
            .iter()
            .map(|c| c.0)
            .collect()
    }

    #[test]
    fn next_classes_head_only_long_literal() {
        // Only the literal's FIRST char can be consumed next: 3 classes,
        // where the all-ranges partition overflowed the cap.
        let w = isolated40();
        let r = plus_rex(lit(&w));
        assert_eq!(
            next_classes(&r),
            Some(vec![(0, 0x20), (0x21, 0x21), (0x22, MAX_CODE)])
        );
    }

    #[test]
    fn next_classes_head_only_concat_shapes() {
        let c = |ch: char| ch as u32;
        let (a, m, x) = (chr('a'), chr('m'), chr('x'));
        // Non-nullable head: the tail is never tested.
        assert_eq!(los(&concat(vec![a.clone(), m.clone()])), vec![0, c('a'), c('b')]);
        // Nullable head: the next element joins.
        assert_eq!(
            los(&concat(vec![star(a.clone()), m.clone()])),
            vec![0, c('a'), c('b'), c('m'), c('n')]
        );
        // Two nullable heads: the third element joins.
        assert_eq!(
            los(&concat(vec![star(a.clone()), star(m.clone()), x.clone()])),
            vec![0, c('a'), c('b'), c('m'), c('n'), c('x'), c('y')]
        );
        // The walk stops at the first non-nullable element.
        assert_eq!(
            los(&concat(vec![star(a.clone()), m.clone(), x.clone()])),
            vec![0, c('a'), c('b'), c('m'), c('n')]
        );
        // comp(a*) is NOT nullable (ε ∈ a*), so `m` is unreachable.
        assert_eq!(
            los(&concat(vec![comp(star(a.clone())), m.clone()])),
            vec![0, c('a'), c('b')]
        );
        // Comp / Inter pass the inner heads through.
        assert_eq!(los(&comp(concat(vec![a.clone(), m.clone()]))), vec![0, c('a'), c('b')]);
        assert_eq!(
            los(&inter(vec![
                concat(vec![a.clone(), m.clone()]),
                concat(vec![x.clone(), a.clone()]),
            ])),
            vec![0, c('a'), c('b'), c('x'), c('y')]
        );
        // Loop: lo = 0 is nullable (next element joins); lo = 1 is not.
        let am = concat(vec![a.clone(), m.clone()]);
        assert_eq!(
            los(&concat(vec![loop_(am.clone(), 0, 3), x.clone()])),
            vec![0, c('a'), c('b'), c('x'), c('y')]
        );
        assert_eq!(
            los(&concat(vec![loop_(am, 1, 3), x.clone()])),
            vec![0, c('a'), c('b')]
        );
        // Surrogate-block head: cuts exactly at the block edges.
        assert_eq!(
            los(&concat(vec![Rex::Range(0xD800, 0xDFFF), a])),
            vec![0, 0xD800, 0xE000]
        );
    }

    #[test]
    fn next_classes_head_only_uniform_sweep() {
        // Soundness guard (spec §4.4): for thousands of random regexes, every
        // probed code point has the same derivative as its class's
        // representative. A head_bounds that missed a range `deriv` tests
        // would split a class's behaviour and fail here.
        fn gen(g: &mut Lcg, depth: u32) -> Rex {
            if depth == 0 || g.next() % 3 == 0 {
                return match g.next() % 6 {
                    0 => Rex::Eps,
                    1 => arb_range(g),
                    _ => {
                        let lo = 'a' as u32 + (g.next() % 8) as u32;
                        Rex::Range(lo, lo + (g.next() % 3) as u32)
                    }
                };
            }
            let kids = |g: &mut Lcg| -> Vec<Rex> {
                (0..2 + g.next() % 2).map(|_| gen(g, depth - 1)).collect()
            };
            match g.next() % 6 {
                0 => concat(kids(g)),
                1 => union(kids(g)),
                2 => inter(kids(g)),
                3 => star(gen(g, depth - 1)),
                4 => comp(gen(g, depth - 1)),
                _ => {
                    let lo = (g.next() % 2) as u32;
                    loop_(gen(g, depth - 1), lo, lo + 1 + (g.next() % 3) as u32)
                }
            }
        }
        let probes: Vec<u32> = (0..=0x90u32)
            .chain([
                0xD7FE, 0xD7FF, 0xD800, 0xD801, 0xDFFE, 0xDFFF, 0xE000, 0xE001,
                MAX_CODE - 1, MAX_CODE,
            ])
            .collect();
        let mut g = Lcg(60);
        let mut checked = 0usize;
        for _ in 0..3000 {
            let r = gen(&mut g, 4);
            let Some(classes) = next_classes(&r) else {
                continue; // over the cap — a fence, not a partition to check
            };
            // A partition of Σ: contiguous, starts at 0, ends at MAX_CODE.
            assert_eq!(classes[0].0, 0, "{r:?}");
            assert_eq!(classes.last().unwrap().1, MAX_CODE, "{r:?}");
            for w in classes.windows(2) {
                assert_eq!(w[0].1 + 1, w[1].0, "{r:?}");
            }
            for &c in &probes {
                let &(lo, _) = classes.iter().find(|(lo, hi)| *lo <= c && c <= *hi).unwrap();
                assert_eq!(deriv(c, &r), deriv(lo, &r), "class of {c:#x} not uniform in {r:?}");
            }
            checked += 1;
        }
        assert!(checked > 2500, "too many regexes over the cap: {checked}");
    }

    #[test]
    fn language_empty_distinct_heads_past_old_cap() {
        // The slice-59 representative reproducer's shape: three r+ literals
        // whose FIRST chars differ ('b', 'a', '!'). One derivative step on
        // any class empties the intersection; pre-slice-60 the 40-char word
        // overflowed the partition and this was Unknown.
        let goal = inter(vec![
            plus_rex(lit("bba")),
            plus_rex(lit("aaps]0e4_b{a")),
            plus_rex(lit(&isolated40())),
        ]);
        assert!(matches!(language_empty(&goal), Emptiness::Empty));
    }

    #[test]
    fn search_finds_long_literal_witness() {
        // Shared member w·w of w+ and (w·w)+ over a printable alphabet;
        // pre-slice-60 both searches gave up on the first step.
        let w = isolated40();
        let ww = format!("{w}{w}");
        let arms = vec![
            plus_rex(lit(&w)),
            plus_rex(lit(&ww)),
            star(Rex::Range('!' as u32, '~' as u32)),
        ];
        let goal = inter(arms.clone());
        let found = search_word(&goal, 80).expect("a word of length 80");
        assert_eq!(found, ww);
        assert_eq!(search_shortest(&goal).as_deref(), Some(ww.as_str()));
        for a in &arms {
            assert_eq!(eval_membership(&found, a), Some(true));
        }
    }
```

- [ ] **Step 2: Run the new tests to verify they fail**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(next_classes_head_only) | test(language_empty_distinct_heads_past_old_cap) | test(search_finds_long_literal_witness)'`
Expected: 5 tests discovered. FAIL: `next_classes_head_only_long_literal` (left `None`), `next_classes_head_only_concat_shapes` (extra cuts, e.g. `[0, 97, 98, 109, 110]` for `a·m`), `language_empty_distinct_heads_past_old_cap`, `search_finds_long_literal_witness` (`expect` on `None`). PASS: `next_classes_head_only_uniform_sweep` (the all-ranges partition is also uniform — this test guards the change, it is not the red test).

- [ ] **Step 3: Replace `range_bounds` with `head_bounds` and switch `next_classes`**

In `crates/shinri-str/src/regex.rs`, replace the whole `range_bounds` function (from its doc comment `/// Collect the class boundaries contributed by every` through its closing brace) with:

```rust
/// Collect the class boundaries of every `Range` that `deriv` can test on
/// the NEXT character — exactly the nodes `deriv` descends into: a concat's
/// first element, and each following element while every element before it
/// is nullable (`deriv`'s `ε ∈ r1` branch); every member of a union or
/// intersection; the body of a star, complement or loop. Each range
/// [lo, hi] cuts Σ at lo and hi+1. Ranges past a non-nullable concat
/// element are never tested and contribute no cut.
fn head_bounds(r: &Rex, out: &mut BTreeSet<u32>) {
    match r {
        Rex::Empty | Rex::Eps => {}
        Rex::Range(lo, hi) => {
            out.insert(*lo);
            if *hi < MAX_CODE {
                out.insert(hi + 1);
            }
        }
        Rex::Concat(ps) => {
            for p in ps {
                head_bounds(p, out);
                if !nullable(p) {
                    break;
                }
            }
        }
        Rex::Union(ps) | Rex::Inter(ps) => {
            for p in ps {
                head_bounds(p, out);
            }
        }
        Rex::Star(i) | Rex::Comp(i) | Rex::Loop(i, ..) => head_bounds(i, out),
    }
}
```

Replace the `next_classes` doc comment and its `range_bounds` call:

```rust
/// Next-character classes: a partition of Σ = [0, MAX_CODE] into maximal
/// ranges on which `deriv` is uniform. `deriv` branches only on membership
/// tests against the head-reachable `Range` nodes that `head_bounds`
/// collects, and no such boundary falls strictly inside a class, so every
/// test answers identically across the class. Ranges deeper in the regex
/// (past a non-nullable concat element) are not cut on: a long literal
/// contributes only its first character. `None` iff the partition exceeds
/// `CLASS_SPLIT_CAP` (→ caller fences).
pub(crate) fn next_classes(r: &Rex) -> Option<Vec<(u32, u32)>> {
    let mut bounds = BTreeSet::new();
    bounds.insert(0u32);
    head_bounds(r, &mut bounds);
```

The rest of `next_classes` (the cap check and class construction) stays byte-identical.

- [ ] **Step 4: Run the new tests to verify they pass**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(next_classes_head_only) | test(language_empty_distinct_heads_past_old_cap) | test(search_finds_long_literal_witness)'`
Expected: 5 passed.

- [ ] **Step 5: Run the whole `shinri-str` suite**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str`
Expected: all pass, with `next_classes_partition_sigma`, `next_classes_derivative_uniform` and `language_empty_class_split_overflow_taints_to_unknown` unmodified. If any existing test fails, stop and report the failure (Global Constraints) — do not edit it.

- [ ] **Step 6: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): slice60 - next_classes cuts on head-reachable ranges only"
```

---

### Task 2: Blocking-tier probes

**Files:**
- Create: `crates/shinri-solver/tests/slice60_probes.rs`

**Interfaces:**
- Consumes: Task 1's coarser `next_classes` (through the solver); `shinri_parser::Parser`, `shinri_solver::{CommandResponse, Solver}`.
- Produces: the three probe scripts as `const`s; Task 3 copies them verbatim (per-binary convention).

- [ ] **Step 1: Write the probe file**

```rust
//! Slice 60 probes (spec §7.2). `regex::next_classes` used to cut Σ at every
//! `Range` in the regex, so a long literal under `re.+` overflowed
//! `CLASS_SPLIT_CAP` on the first derivative step: the witness search and the
//! emptiness conflict both gave up, and every case here answered `unknown`
//! (`str-model-rejected`, `violated:memb@not-needed`) at the branch point.
//! The `unsat` case has `sat` siblings so the fix cannot pass by
//! over-refuting; the `sat` cases pin the exact witness.
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

/// 40 pairwise non-adjacent printable chars ('!' + 2i): 81 cuts under the
/// old all-ranges partition, 3 under the head-only one.
const L40: &str = "!#%')+-/13579;=?ACEGIKMOQSUWY[]_acegikmo";

/// `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-010-reverse-multiply-fuzz.smt2`
/// (assertions verbatim; z3 `unsat`). The three words start with 'b', 'a',
/// 'j', so the intersection is empty after one derivative step.
const REGEX_010: &str = r#"(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.+ (str.to_re "bba"))))
(assert (str.in_re x (re.+ (str.to_re "aaps]0e4_b{a"))))
(assert (str.in_re x (re.+ (str.to_re "j.3F&AXI'\x0c';7lLbg8[c_P1ou^uNIM-(' '%+}q'\x0c''\r''\t''\n'(CW/"))))
(check-sat)
"#;

fn shared_member_script() -> String {
    format!(
        "(set-logic QF_S)(declare-fun x () String)\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}\"))))\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}{L40}\"))))\n\
         (assert (str.in_re x (re.* (re.range \"!\" \"~\"))))\n\
         (check-sat)\n(get-value (x))\n"
    )
}

fn len_pin_script() -> String {
    format!(
        "(set-logic QF_S)(declare-fun x () String)\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}\"))))\n\
         (assert (= (str.len x) 80))\n\
         (check-sat)\n(get-value (x))\n"
    )
}

#[test]
fn regex_010_distinct_heads_unsat() {
    assert_eq!(run_script(REGEX_010), vec!["unsat"]);
}

#[test]
fn shared_member_sat_with_witness() {
    let out = run_script(&shared_member_script());
    assert_eq!(out, vec!["sat".to_string(), format!("((x \"{L40}{L40}\"))")]);
}

#[test]
fn long_literal_len_pin_sat_with_witness() {
    let out = run_script(&len_pin_script());
    assert_eq!(out, vec!["sat".to_string(), format!("((x \"{L40}{L40}\"))")]);
}
```

Note on `REGEX_010`: it is a Rust raw string, so `\x0c`, `\r`, `\t`, `\n` stay as the two-or-four literal characters the corpus file has (SMT-LIB 2.6 has no `\x` escape; the corpus bytes are a backslash followed by `x0c`). Verify with `grep -c 'x0c' bench/corpus/QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-010-reverse-multiply-fuzz.smt2` (expected `1` line) and compare the assertion lines by eye.

- [ ] **Step 2: Confirm the probes fail on the branch point and pass now**

HEAD is Task 1's commit, so `HEAD~1` holds the branch-point `regex.rs`:

Run: `git checkout HEAD~1 -- crates/shinri-str/src/regex.rs; taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice60_probes)'; git checkout HEAD -- crates/shinri-str/src/regex.rs; git status --short crates/shinri-str`
Expected: 3 tests discovered, 3 FAIL (each `unknown`), and the final `git status` prints nothing.

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice60_probes)'`
Expected: 3 passed. If a case answers `unknown` on the new code, stop and report it with the `--stats` line from `target/release/shinri --stats` on the same script — that is a ruling, not something to patch here.

- [ ] **Step 3: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-solver/tests/slice60_probes.rs
git commit -m "test(solver): slice60 - probes for long-literal memberships past the old class cap"
```

---

### Task 3: z3 differential oracle

**Files:**
- Create: `crates/shinri-solver/tests/head_classes_oracle.rs`

**Interfaces:**
- Consumes: Task 2's `L40`, `REGEX_010`, `shared_member_script`, `len_pin_script` (copied verbatim — each integration test is its own binary); the `easy-smt` dev-dependency; z3 from mise.
- Produces: nothing other tasks consume.

- [ ] **Step 1: Write the oracle file**

```rust
//! Differential oracle (slice 60, spec §7.3): `re.+` memberships over long
//! literals of pairwise non-adjacent chars, which overflowed
//! `CLASS_SPLIT_CAP` under the old all-ranges `next_classes`. Every decided
//! shinri answer must match z3, and every shinri `sat` witness, re-asserted
//! into z3, must be `sat`. Subjects are a bare variable (witness search,
//! emptiness conflict) or `(str.++ x y)` (Rule-E unfolding).
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(head_classes_oracle)'
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

/// Copied verbatim from tests/slice60_probes.rs.
const L40: &str = "!#%')+-/13579;=?ACEGIKMOQSUWY[]_acegikmo";
const REGEX_010: &str = r#"(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.+ (str.to_re "bba"))))
(assert (str.in_re x (re.+ (str.to_re "aaps]0e4_b{a"))))
(assert (str.in_re x (re.+ (str.to_re "j.3F&AXI'\x0c';7lLbg8[c_P1ou^uNIM-(' '%+}q'\x0c''\r''\t''\n'(CW/"))))
"#;

fn shared_member_body() -> String {
    format!(
        "(declare-fun x () String)\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}\"))))\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}{L40}\"))))\n\
         (assert (str.in_re x (re.* (re.range \"!\" \"~\"))))\n"
    )
}

fn len_pin_body() -> String {
    format!(
        "(declare-fun x () String)\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}\"))))\n\
         (assert (= (str.len x) 80))\n"
    )
}

/// shinri's verdict on `body` (declarations + assertions, one per line) and,
/// on `sat`, the quoted values of `vars` in order. The pool has no `"` or
/// `\`, so a value is the text between a pair of quotes.
fn shinri_run(body: &str, vars: &[&str]) -> (SolveOutcome, Vec<String>) {
    let full = format!(
        "(set-logic QF_S)\n{body}(check-sat)\n(get-value ({}))\n",
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
                values = s.split('"').skip(1).step_by(2).map(str::to_string).collect();
            }
            _ => {}
        }
    }
    (outcome, values)
}

fn z3_outcome(body: &str) -> easy_smt::Response {
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in", "-T:20"])
        .build()
        .expect("failed to launch z3 — run `mise install`");
    ctx.set_logic("QF_S").expect("z3 set-logic failed");
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
    ctx.check().expect("z3 check-sat failed")
}

/// Checks one script. Returns shinri's verdict for the caller's tally.
fn check(body: &str, vars: &[&str]) -> SolveOutcome {
    let (ours, values) = shinri_run(body, vars);
    let theirs = z3_outcome(body);
    match (ours, theirs) {
        (SolveOutcome::Sat, easy_smt::Response::Unsat) => panic!("shinri sat, z3 unsat:\n{body}"),
        (SolveOutcome::Unsat, easy_smt::Response::Sat) => panic!("shinri unsat, z3 sat:\n{body}"),
        _ => {}
    }
    if ours == SolveOutcome::Sat {
        assert_eq!(values.len(), vars.len(), "get-value shape:\n{body}");
        let mut pinned = body.to_string();
        for (v, val) in vars.iter().zip(&values) {
            pinned.push_str(&format!("(assert (= {v} \"{val}\"))\n"));
        }
        assert!(
            matches!(z3_outcome(&pinned), easy_smt::Response::Sat),
            "z3 rejects shinri's witness {values:?}:\n{body}"
        );
    }
    ours
}

/// One generated script: k ∈ {2, 3} `re.+` memberships on `x` or on
/// `(str.++ x y)`. Half the scripts take every word as a power of one base
/// word (common member base⁶ — sat-leaning); the rest draw words
/// independently (distinct heads — unsat-leaning). A quarter of the bases
/// are the 40-char head-wide word. Optional length pin.
fn gen(rng: &mut Lcg) -> (String, Vec<&'static str>) {
    let pool: Vec<char> = L40.chars().collect();
    let word = |rng: &mut Lcg, len: u64| -> String {
        (0..len).map(|_| pool[rng.below(pool.len() as u64) as usize]).collect()
    };
    let concat_subject = rng.below(3) == 0;
    let (subject, vars, decls) = if concat_subject {
        ("(str.++ x y)", vec!["x", "y"], "(declare-fun x () String)\n(declare-fun y () String)\n")
    } else {
        ("x", vec!["x"], "(declare-fun x () String)\n")
    };
    let base = if rng.below(4) == 0 {
        L40.to_string()
    } else {
        let len = 1 + rng.below(12);
        word(rng, len)
    };
    let k = 2 + rng.below(2);
    let shared = rng.below(2) == 0;
    let words: Vec<String> = (0..k)
        .map(|i| {
            if shared {
                base.repeat(1 + rng.below(3) as usize)
            } else if i == 0 {
                base.clone()
            } else {
                let len = 1 + rng.below(40);
                word(rng, len)
            }
        })
        .collect();
    let mut body = decls.to_string();
    for w in &words {
        body.push_str(&format!("(assert (str.in_re {subject} (re.+ (str.to_re \"{w}\"))))\n"));
    }
    if rng.below(2) == 0 {
        let n = if shared { 6 * base.chars().count() as u64 } else { 1 + rng.below(80) };
        body.push_str(&format!("(assert (= (str.len {subject}) {n}))\n"));
    }
    (body, vars)
}

#[test]
fn head_classes_probes_agree_with_z3() {
    assert_eq!(check(REGEX_010, &["x"]), SolveOutcome::Unsat);
    assert_eq!(check(&shared_member_body(), &["x"]), SolveOutcome::Sat);
    assert_eq!(check(&len_pin_body(), &["x"]), SolveOutcome::Sat);
}

#[test]
fn head_classes_generated_agree_with_z3() {
    let mut rng = Lcg(60);
    let (mut sat, mut unsat) = (0usize, 0usize);
    for _ in 0..N_ITERS {
        let (body, vars) = gen(&mut rng);
        match check(&body, &vars) {
            SolveOutcome::Sat => sat += 1,
            SolveOutcome::Unsat => unsat += 1,
            _ => {}
        }
    }
    eprintln!("head_classes_oracle: {sat} sat, {unsat} unsat, {} unknown", N_ITERS - sat - unsat);
    assert!(sat > 0 && unsat > 0, "generator must exercise both verdicts: {sat} sat, {unsat} unsat");
}
```

- [ ] **Step 2: Run the oracle file**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle -E 'binary(head_classes_oracle)' --no-capture 2>&1 | tail -15`
Expected: **2 tests discovered** (0 means the feature was off — not a pass), 2 passed, and the `head_classes_oracle:` line shows non-zero `sat` and `unsat`. A disagreement panic is a soundness finding: stop the slice for a ruling and keep the printed script. If z3 rejects a line, fix the generator, not the assertion.

- [ ] **Step 3: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-solver/tests/head_classes_oracle.rs
git commit -m "test(solver): slice60 - z3 differential over long-literal re.+ intersections"
```

---

### Task 4: Gates

**Files:** none.

- [ ] **Step 1: Full blocking tier**

Run: `taskset -c 0-11 mise run ci 2>&1 | tee target/slice60-ci.log | tail -30`
Expected: exit 0; all passed. Slice-59 final baseline: 1760 run, 6 skipped. This slice adds 5 `shinri-str` tests and 3 `slice60_probes` tests, so expect 1768 run (state the actual number and the delta in the report).

- [ ] **Step 2: Oracle suite**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice60-oracle-suite.log | tail -15`
Expected: all passed, 2 skipped. The slice-59 gate measured 825 run; the slice-59 final-review fix added one `shinri-solver` unit test (`unlisted_builtin_is_other_op`), and this slice adds 3 probes + 2 oracle tests, so expect 831 run. Any other delta: explain it in the report before claiming the gate. 0 run is not a pass.

- [ ] **Step 3: The wide-head pins by name**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -p shinri-solver -E 'test(next_classes_partition_sigma) | test(language_empty_class_split_overflow_taints_to_unknown) | test(in_re_unfold_unknown_class_cap)'`
Expected: 3 discovered, 3 passed (Review Focus 1).

- [ ] **Step 4: Record**

```bash
{ echo "gates:"; tail -3 target/slice60-ci.log; tail -3 target/slice60-oracle-suite.log; } > target/slice60-gates.txt
cat target/slice60-gates.txt
```

Nothing to commit.

---

### Task 5: After runs, triage, attribution, timing, report, measured outcomes, PR

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice60-head-classes-report.md` (date = the day the after runs finish)
- Modify: `docs/superpowers/specs/2026-10-04-shinri-slice60-head-classes-design.md` (fix the report path in §8 to the real date; append §11 *Measured outcomes*)

**Interfaces:**
- Consumes: branch HEAD after Tasks 1–3; Task 0's `target/slice60-base/shinri`, `bench/results/slice60-base*/results.jsonl`; `target/slice59-sample-corpus/`; `target/slice60-gates.txt`.
- Produces: the report and spec section cited by the PR.

- [ ] **Step 1: Wait for the base runs**

Wait for `target/slice60-base/finished.txt` (use a Monitor/until-loop, not a foreground sleep). Then: `wc -l bench/results/slice60-base/results.jsonl bench/results/slice60-base-sample/results.jsonl` — expect 103,335 + 1 and 2,000 + 1 lines (the `+ 1` is the run header; same counts as slice 59).

- [ ] **Step 2: Build and launch the after runs detached**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice60-after && cp target/release/shinri target/slice60-after/shinri
md5sum target/slice60-after/shinri | tee target/slice60-after/md5.txt
git rev-parse --short HEAD | tee target/slice60-after/commit.txt
date -u +%FT%TZ > target/slice60-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice60-after/shinri --run-id slice60 \
  > target/slice60-after/run.log 2>&1; \
  taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice60-after/shinri --run-id slice60-sample \
  > target/slice60-after/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice60-after/finished.txt' \
  > /dev/null 2>&1 &
```

Wait for `target/slice60-after/finished.txt` the same way.

- [ ] **Step 3: Render reports and join the runs (criteria 1, 2, 6)**

```bash
for id in slice60-base slice60 slice60-base-sample slice60-sample; do BENCH_RUN_ID=$id mise run bench-report; done
python3 - <<'EOF' | tee target/slice60-after/join.txt
import json, collections
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
changed = []
for base, after in (("slice60-base", "slice60"), ("slice60-base-sample", "slice60-sample")):
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
a = load("bench/results/slice60-base/results.jsonl")
b = load("bench/results/slice60/results.jsonl")
TAG = "violated:memb@not-needed"
base_tag = [p for p in a if a[p].get("fence_detail") == TAG]
after_tag = [p for p in b if b[p].get("fence_detail") == TAG]
moved = [p for p in base_tag if b[p]["verdict"] == "correct"]
print(f"criterion 2: {TAG} base {len(base_tag)} after {len(after_tag)}; "
      f"base-tag rows now correct {len(moved)} ({len(moved) / len(base_tag):.1%}); "
      f"need >= 450 and >= 20%")
print("moved by family:", collections.Counter("/".join(p.split("/")[1:-1]) for p in moved).most_common(8))
print("moved by base status:", collections.Counter(a[p]["status"] or "none" for p in moved))
def tags(rows):
    return collections.Counter(r.get("fence_detail") for r in rows.values() if r["verdict"] == "unknown:str-model-rejected")
ta, tb = tags(a), tags(b)
print("fence_detail movement (base -> after):")
for t in sorted(set(ta) | set(tb), key=lambda t: -(ta[t] + tb[t])):
    print(f"  {t}: {ta[t]} -> {tb[t]}")
open("target/slice60-after/changed.tsv", "w").write("".join("\t".join(x) + "\n" for x in changed))
EOF
```

Expected: 0 wrong rows in both after runs (criterion 1; any hit stops the slice for a ruling). Criterion 2's line shows ≥ 450 rows and ≥ 20%. The sample run's changes are all for Step 4 to classify as noise (criterion 6).

- [ ] **Step 4: Triage changed rows (criteria 1, 3, 6)**

Same procedure as slice 59 (3 runs per binary, interleaved, on cores 12–23 with nothing else running). Triage every row whose transition is **not** `unknown:* → correct` (regressions, other moves, every sample row); for `unknown:* → correct` rows triage a stratified sample of ≥ 32 across families (they are the expected effect; the bench already checked them against the corpus status):

```bash
python3 - <<'EOF'
import random, collections
rows = [l.rstrip("\n").split("\t") for l in open("target/slice60-after/changed.tsv")]
gain = [r for r in rows if r[2].startswith("unknown") and r[3] == "correct"]
other = [r for r in rows if r not in gain]
rng = random.Random(60)
fam = collections.defaultdict(list)
for r in gain:
    fam["/".join(r[0].split("/")[1:-1])].append(r)
pick = []
while len(pick) < min(32, len(gain)):
    for f in sorted(fam):
        if fam[f] and len(pick) < 32:
            pick.append(fam[f].pop(rng.randrange(len(fam[f]))))
open("target/slice60-after/triage-in.tsv", "w").write("".join("\t".join(r) + "\n" for r in other + pick))
print(len(other), "non-gain rows,", len(pick), "sampled gain rows")
EOF
while IFS="$(printf '\t')" read -r p logic va vb tag run; do
  case "$run" in *sample) root=target/slice59-sample-corpus ;; *) root=bench/corpus ;; esac
  for i in 1 2 3; do
    for bin in target/slice60-base/shinri target/slice60-after/shinri; do
      r=$(taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats $root/$p 2>&1 \
          | grep -E '^(sat|unsat|unknown)$|^stats:|memory allocation' | tr '\n' ' ')
      printf '%s\t%s\t%s\t%s\n' "$p" "$(basename $(dirname $bin))" "$i" "$r"
    done
  done
done < target/slice60-after/triage-in.tsv | tee target/slice60-after/triage.tsv
```

If there are more than 200 non-gain rows, triage a stratified sample of at least 32 of them and state its size. A row is *noise* if either binary's 3 runs disagree with each other or the two binaries agree on at least one run; *attributable* if each binary reproduces its own bench verdict 3/3 and they differ. Attributable `correct → non-correct` rows fail criterion 3; attributable sample-run rows fail criterion 6; a wrong answer from either binary fails criterion 1. Each stops the slice for a ruling.

- [ ] **Step 5: Caller attribution (spec §8 item 2) — throwaway, not committed**

Add three `eprintln!`s to a debug copy, run a seeded sample of 40 gain rows, then revert:

1. `crates/shinri-str/src/model.rs`, inside `memb_seeds` right after `out.insert(v, w);` — `eprintln!("slice60-trace: seed");`
2. `crates/shinri-str/src/memb.rs`, in the slice-28 emptiness block right before `return Some(TCheck::Conflict(just));` — `eprintln!("slice60-trace: empty-conflict");`
3. `crates/shinri-str/src/memb.rs`, in Rule-E right after `let Some(classes) = regex::next_classes(&cur) else { … };` — `eprintln!("slice60-trace: rule-e {}", classes.len());`

```bash
cargo build --release -p shinri-cli --target-dir target/slice60-trace
python3 - <<'EOF' > target/slice60-after/attr-in.txt
import random
rows = [l.split("\t") for l in open("target/slice60-after/changed.tsv")]
gain = sorted(r[0] for r in rows if r[2].startswith("unknown") and r[3] == "correct" and r[5] == "slice60")
print("\n".join(random.Random(60).sample(gain, min(40, len(gain)))))
EOF
while read -r p; do
  t=$(timeout 20 target/slice60-trace/release/shinri bench/corpus/$p 2>&1 | grep -o 'slice60-trace: [a-z-]*' | sort | uniq -c | tr '\n' ' ')
  printf '%s\t%s\n' "$p" "$t"
done < target/slice60-after/attr-in.txt | tee target/slice60-after/attribution.tsv
git checkout -- crates && git status --short crates
```

Expected: `git status --short crates` prints nothing. Classify each row: *witness* (a `seed` line, verdict `sat`), *emptiness* (an `empty-conflict` line, verdict `unsat`), *Rule-E* (only `rule-e` lines). Also measure Rule-E's per-split class counts on the same rows with the base code if a row is Rule-E-only (optional; state if skipped).

- [ ] **Step 6: Timing (criterion 4)**

```bash
python3 - <<'EOF' | tee target/slice60-after/timing.txt
import json, random, subprocess, time, statistics
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
a = load("bench/results/slice60-base/results.jsonl")
b = load("bench/results/slice60/results.jsonl")
rng = random.Random(60)
groups = {lg: sorted(p for p in a if a[p]["logic"] == lg and a[p]["verdict"] == b[p]["verdict"] == "correct")
          for lg in ("QF_S", "QF_SLIA")}
groups["newly-correct"] = sorted(p for p in a if a[p]["verdict"] != "correct" and b[p]["verdict"] == "correct")
for name, rows in groups.items():
    sample = rng.sample(rows, min(150, len(rows)))
    tot = {"base": 0.0, "after": 0.0}
    for p in sample:
        for which in ("base", "after"):
            t0 = time.monotonic()
            subprocess.run(["taskset", "-c", "12", f"target/slice60-{which}/shinri", f"bench/corpus/{p}"],
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

Expected: the QF_S and QF_SLIA ratios within 0.95–1.05 (criterion 4; if one pass lands outside, repeat the pass twice more and pool the three, as slice 59 did, stating so). The newly-correct ratio is reported, not gated (those rows failed fast before and now do real work).

- [ ] **Step 7: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-04-smtlib-2024-slice59-model-rejected-classes-report.md`:
- *Headline*: rows moved to `correct` (sat/unsat split), criterion-2 numbers, class-1 size before/after, criteria summary
- *Commands*: the exact commands from Tasks 0 and 5
- *Runs*: both binaries with md5 and commit, started/finished, row counts for all four runs
- *Success criteria*: spec §8 table, each PASS/FAIL with evidence (gates from `target/slice60-gates.txt`, Task 0 Step 4 / Task 2 probe outcomes)
- *Verdict changes*: `join.txt` transition counts; the `fence_detail` movement table; moved rows by family and base status
- *Triage*: dispositions from `triage.tsv`
- *Caller attribution*: `attribution.tsv` summarised (witness / emptiness / Rule-E counts out of 40)
- *Timing*: `timing.txt`
- *What changed versus the spec*: every deviation
- *Queued for the next slice*: re-ranked on the after run's `fence_detail` counts: class 1's remainder (state what is left and why, from the attribution and a look at 5 still-`violated:memb@not-needed` rows), the `regex-035-*` unseeded-concat-operand sub-bucket, then slice-59 queue items 2 onward and their carried lists verbatim; state every re-rank

- [ ] **Step 8: Append §11 *Measured outcomes* to the spec**

Add `## 11. Measured outcomes` at the end of the spec: a one-line pointer to the report, the criteria table with PASS/FAIL and key numbers (as slice 59 §11 does), the `violated:memb@not-needed` before/after count, and a *Deviations from this spec* subsection. Fix the §8 report path to the real date.

- [ ] **Step 9: Commit and open the PR**

```bash
git add docs/superpowers/research docs/superpowers/specs/2026-10-04-shinri-slice60-head-classes-design.md
git commit -m "docs(bench+spec): slice60 - head-only classes run and measured outcomes"
git push -u origin slice60-head-classes
gh pr create --base main --title "slice60: head-only next-character classes" --body "$(cat <<'EOF'
Spec: docs/superpowers/specs/2026-10-04-shinri-slice60-head-classes-design.md
Plan: docs/superpowers/plans/2026-10-04-shinri-slice60-head-classes.md
Report: docs/superpowers/research/<date>-smtlib-2024-slice60-head-classes-report.md

`regex::next_classes` now cuts Σ only at the bounds of head-reachable ranges (`head_bounds`), so long literals no longer overflow `CLASS_SPLIT_CAP` in the witness search, the emptiness conflict and Rule-E.

<criteria table and class-1 before/after from spec §11>
EOF
)"
```

Fill the `<date>` and the criteria lines from the report before running. Then wait for CI; when it is green, ask the user before merging (merge commit, then delete the branch remote and local).
