# Slice 58 — Membership Rule G over class concat members Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn `unknown fence=str-model-rejected` into a correct `unsat` when a string membership `t ∈ R` contradicts the constant prefix of a concat that sits in `t`'s EUF class but is not its normal-form representative, without adding any wrong answer.

**Architecture:** A new helper `memb::member_prefix_conflict` scans the concat members of `t`'s class, consumes each member's cited deep-normal-form constant prefix through the regex derivative, and returns a fully cited conflict justification when the derivative is `∅`. `memb_check` calls it (Rule G′) right after Rule G, before the leaf arms and Rule S/E. G′ emits no split, mints nothing, spends no fuel.

**Tech Stack:** Rust workspace (toolchain pinned in `mise.toml`), cargo-nextest 0.9.140, z3 from mise for the oracle, `shinri-bench` for the SMT-LIB 2024 run.

**Spec:** `docs/superpowers/specs/2026-10-03-shinri-slice58-member-prefix-design.md`

## Global Constraints

- Code changes only in `crates/shinri-str/src/memb.rs` (`memb_check` and the new helper, plus its tests). No parser, SAT, Combiner, `wordeq.rs`, `normalize.rs`, `lower`, length-seam, model-builder or gate change (spec §5).
- G′ emits no split or lemma, mints no term, records no dedup key and spends no fuel (spec §4.2). A candidate it cannot evaluate (deep NF `None`, node cap) is skipped, never `Unknown`.
- `MEMBER_CAP = 64` candidates per atom (spec §4.2).
- The emptiness test is `matches!(cur, Rex::Empty)`, the same syntactic test Rule E uses (spec §4.2).
- Any `* → wrong` row stops the slice for a ruling (spec §8, criterion 1).
- Bench: logics QF_S and QF_SLIA only; `--timeout 20 --mem-mb 3072 --jobs 6`; detached with `setsid` under `taskset -c 12-23`; base run `slice58-base` built from the branch point (spec §6, §8).
- Oracle tests only run with `--features oracle`; without it they silently run 0 tests. Always confirm a non-zero discovered count (AGENTS.md).
- nextest filters use the expression form `-E 'test(<name>)'` / `-E 'binary(<name>)'` (AGENTS.md).
- While the base bench run is live, run builds and tests on cores 0–11 (`taskset -c 0-11 …`) so they do not perturb the bench (slice-53 R9).
- `cargo fmt --all` before every commit; `mise run lint` (clippy `-D warnings`) must be clean.
- Branch `slice58-member-prefix` off `main`; PR to `main`, merge commit when CI is green, then delete the branch (AGENTS.md). Ask the user before merging.

## Review Focus

1. **Incremental scripts: a constant-headed member asserted inside `push` and gone after `pop`.** Expected: `unsat` inside the scope, `sat` after the `pop` (no stale member conflict). Pinned in Task 1 (`rf1_member_popped_with_scope`).
2. **An empty constant prefix** (`(str.prefixof "" x)`, whose concat's NF drops `""`). Expected: no conflict; `sat`. Pinned in Task 1 (`rf2_empty_prefix_no_conflict`).
3. **Non-ASCII prefix characters against a non-ASCII range** (`"\u{e9}"` with `[\u{e0}-\u{ff}]*`). Expected: the derivative works on code points, no spurious conflict; `sat`. Pinned in Task 1 (`rf3_non_ascii_prefix_in_range`).
4. **The membership's own string side is a concat** (`(str.in_re (str.++ x "b") R)`) while `x`'s class holds a constant-headed concat. Expected: sound verdict, `sat` here. Pinned in Task 1 (`rf4_concat_membership_side`).
5. **A class member whose deep normal form does not converge** (self-referential `s = s ++ s ++ u`). Expected: that member is skipped, other members still decide; no panic, no `Unknown`. Pinned in Task 2 (`g_prime_skips_unexpandable_member`).

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-str/src/memb.rs` | Modify | `MEMBER_CAP`, `member_prefix_conflict` helper, Rule G′ call in `memb_check`, unit tests |
| `crates/shinri-solver/tests/slice58_probes.rs` | Create | End-to-end targets, sound-direction guards, Review Focus 1–4 (spec §7.3) |
| `crates/shinri-solver/tests/slice57_probes.rs` | Modify | Remove `k1`/`k2`; leave a pointer comment |
| `crates/shinri-solver/tests/qfs_differential.rs` | Modify | `differential_qfs_member_prefix` family (spec §7.4) |
| `docs/superpowers/research/<date>-smtlib-2024-slice58-member-prefix-report.md` | Create | Bench report and re-scoped queue |
| `docs/superpowers/specs/2026-10-03-shinri-slice58-member-prefix-design.md` | Modify | Append *Measured outcomes* |

---

### Task 0: Branch, base binary, base run

**Files:** none in the repo (artifacts under `target/slice58-base/`, `bench/results/slice58-base/`).

- [ ] **Step 1: Create the slice branch**

```bash
cd /workspace && git checkout main && git pull --ff-only && git checkout -b slice58-member-prefix
```

- [ ] **Step 2: Confirm the crates are unchanged from `f515c00`**

Run: `git diff --stat f515c00 HEAD -- crates`
Expected: empty (only the spec and plan commits sit on top of `f515c00`).

- [ ] **Step 3: Build and freeze the base binary**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice58-base && cp target/release/shinri target/slice58-base/shinri
cp target/release/shinri-bench target/slice58-base/shinri-bench
md5sum target/slice58-base/shinri | tee target/slice58-base/md5.txt
echo f515c00 > target/slice58-base/commit.txt
```

- [ ] **Step 4: Confirm the corpus is present**

Run: `ls bench/corpus/QF_S bench/corpus/QF_SLIA | head -3`
Expected: family directories listed. If a logic is missing, run `BENCH_LOGICS=QF_S,QF_SLIA mise run bench-fetch` first.

- [ ] **Step 5: Launch the base run detached**

```bash
date -u +%FT%TZ > target/slice58-base/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice58-base/shinri-bench run \
  --logics QF_S,QF_SLIA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice58-base/shinri --run-id slice58-base \
  > target/slice58-base/run.log 2>&1; date -u +%FT%TZ > target/slice58-base/finished.txt' \
  > /dev/null 2>&1 &
```

About 103,300 rows (QF_SLIA 84,395, QF_S 18,940). Do not wait: Tasks 1–3 proceed meanwhile on cores 0–11. Task 4 waits for `target/slice58-base/finished.txt`.

---

### Task 1: Failing probes, guards and the oracle family (before evidence)

**Files:**
- Create: `crates/shinri-solver/tests/slice58_probes.rs`
- Modify: `crates/shinri-solver/tests/slice57_probes.rs` (remove `k1`/`k2`, lines ~175–205)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (new family, inserted after `differential_qfs_model_reconcile` and before the `// Targeted explicit cases` banner)

**Interfaces:**
- Consumes: nothing new.
- Produces: the probe file Task 2 turns green; the "before" count of the oracle family (`n_unknown_z3_unsat`), recorded in `target/slice58-before.txt` and turned into `MP_BEFORE_UNKNOWN_Z3_UNSAT` in Task 2.

- [ ] **Step 1: Write the probe file**

Create `crates/shinri-solver/tests/slice58_probes.rs`:

```rust
//! Slice 58 probes (spec §7.3). A membership `t ∈ R` whose EUF class holds
//! a constant-headed concat that is not the class's normal-form
//! representative: `normal_form` never picks a concat as rep, so Rule G saw
//! `nf = [t]` and never consumed the constant. At `f515c00` the `m*` targets
//! answered `unknown fence=str-model-rejected` (`m1`/`m2` measured; see the
//! slice-58 report for `m3`/`m4`). The `g*` and `rf*` cases must stay `sat`;
//! their witnesses are checked against every assertion.
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

const H: &str = "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)";

fn verdict(body: &str) -> String {
    run_script(&format!("{H}{body}(check-sat)"))
        .first()
        .cloned()
        .unwrap_or_default()
}

/// Decode the first SMT-LIB 2.6 string literal in `resp` (`""` and `\u{..}`).
fn decode(resp: &str) -> String {
    let start = resp.find('"').expect("a string literal");
    let cs: Vec<char> = resp[start + 1..].chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < cs.len() {
        match cs[i] {
            '"' if cs.get(i + 1) == Some(&'"') => {
                out.push('"');
                i += 2;
            }
            '"' => break,
            '\\' if cs.get(i + 1) == Some(&'u') && cs.get(i + 2) == Some(&'{') => {
                let close = i + cs[i..]
                    .iter()
                    .position(|&c| c == '}')
                    .expect("closing brace");
                let hex: String = cs[i + 3..close].iter().collect();
                let code = u32::from_str_radix(&hex, 16).expect("hex escape");
                out.push(char::from_u32(code).expect("valid code point"));
                i = close + 1;
            }
            c => {
                out.push(c);
                i += 1;
            }
        }
    }
    out
}

/// `body` must be `sat`; returns the model value of `x`.
fn sat_x(body: &str) -> String {
    let out = run_script(&format!("{H}{body}(check-sat)(get-value (x))"));
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{H}{body}");
    decode(&out[1])
}

fn all_in(s: &str, ok: impl Fn(char) -> bool) -> bool {
    s.chars().all(ok)
}

// ── targets (spec §7.3): unsat via a class member's constant prefix ─────────

/// `regex-050-translate-rotate-fuzz.smt2`; z3: unsat. Was
/// `slice57_probes::k1_stringfuzz_translate_rotate_stays_unknown`.
#[test]
fn m1_translate_rotate() {
    assert_eq!(
        verdict(
            "(assert (= (str.len x) 3))(assert (= x y))\
             (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))(assert (str.prefixof \"\\\\\" x))"
        ),
        "unsat"
    );
}

/// `regex-050-translate-graft-translate.smt2`; z3: unsat. Was
/// `slice57_probes::k2_stringfuzz_translate_graft_stays_unknown`.
#[test]
fn m2_translate_graft() {
    assert_eq!(
        verdict(
            "(assert (= 2 (str.len x)))(assert (= x y))\
             (assert (str.in_re y (re.* (re.range \"a\" \"b\"))))(assert (str.prefixof \"1\" x))"
        ),
        "unsat"
    );
}

/// The member's prefix is only visible through its DEEP normal form
/// (`"a" ++ z`, `z = "b" ++ w` ⟹ `"ab" ++ w`).
#[test]
fn m3_deep_nf_prefix() {
    assert_eq!(
        verdict(
            "(declare-fun z () String)(declare-fun w () String)\
             (assert (= x (str.++ \"a\" z)))(assert (= z (str.++ \"b\" w)))(assert (= y x))\
             (assert (str.in_re y (re.++ (str.to_re \"ac\") re.all)))"
        ),
        "unsat"
    );
}

/// Negative polarity: `∂_a comp("a"·Σ*) = comp(Σ*) = ∅`.
#[test]
fn m4_negative_polarity() {
    assert_eq!(
        verdict(
            "(assert (= x y))(assert (str.prefixof \"a\" x))\
             (assert (not (str.in_re y (re.++ (str.to_re \"a\") re.all))))"
        ),
        "unsat"
    );
}

// ── sound-direction guards (spec §7.3) ───────────────────────────────────────

/// Non-empty derivative ⟹ no conflict.
#[test]
fn g1_compatible_prefix() {
    let x = sat_x(
        "(assert (str.prefixof \"a\" x))(assert (= x y))\
         (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))",
    );
    assert!(
        x.starts_with('a') && all_in(&x, |c| c == 'a' || c == 'b'),
        "x = {x:?}"
    );
}

/// The `"1"` branch's conflict must cite its disjunct, so the `"ab"` branch
/// survives (the E1 ce2 shape).
#[test]
fn g2_conditional_member() {
    let x = sat_x(
        "(assert (or (= x (str.++ \"1\" y)) (= x \"ab\")))\
         (assert (str.in_re x (re.* (re.range \"a\" \"b\"))))",
    );
    assert_eq!(x, "ab");
}

/// A consistent minted `"1" ++ !strk` member ⟹ no conflict.
#[test]
fn g3_minted_member_other_branch() {
    let x = sat_x(
        "(assert (= 2 (str.len x)))(assert (= x y))\
         (assert (str.in_re y (re.* (re.union (re.range \"a\" \"b\") (str.to_re \"1\")))))\
         (assert (str.prefixof \"1\" x))",
    );
    assert!(
        x.starts_with('1')
            && x.chars().count() == 2
            && all_in(&x, |c| matches!(c, 'a' | 'b' | '1')),
        "x = {x:?}"
    );
}

// ── Review Focus (plan) ──────────────────────────────────────────────────────

/// RF1: a member asserted inside a scope must not conflict after `pop`.
#[test]
fn rf1_member_popped_with_scope() {
    let out = run_script(&format!(
        "{H}(assert (= x y))(assert (str.in_re y (re.* (re.range \"a\" \"b\"))))\
         (push 1)(assert (str.prefixof \"1\" x))(check-sat)(pop 1)(check-sat)"
    ));
    assert_eq!(out, vec!["unsat".to_string(), "sat".to_string()]);
}

/// RF2: `prefixof ""` mints a concat whose NF drops `""` — nothing to consume.
#[test]
fn rf2_empty_prefix_no_conflict() {
    let x = sat_x(
        "(assert (str.prefixof \"\" x))(assert (= x y))\
         (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))",
    );
    assert!(
        !x.is_empty() && all_in(&x, |c| c == 'a' || c == 'b'),
        "x = {x:?}"
    );
}

/// RF3: code points above ASCII, inside the range ⟹ no conflict.
#[test]
fn rf3_non_ascii_prefix_in_range() {
    let x = sat_x(
        "(assert (str.prefixof \"\\u{e9}\" x))(assert (= x y))\
         (assert (str.in_re y (re.* (re.range \"\\u{e0}\" \"\\u{ff}\"))))",
    );
    assert!(
        x.starts_with('\u{e9}') && all_in(&x, |c| ('\u{e0}'..='\u{ff}').contains(&c)),
        "x = {x:?}"
    );
}

/// RF4: the membership's string side is itself a concat.
#[test]
fn rf4_concat_membership_side() {
    let x = sat_x(
        "(assert (str.prefixof \"a\" x))\
         (assert (str.in_re (str.++ x \"b\") (re.* (re.range \"a\" \"b\"))))",
    );
    assert!(
        x.starts_with('a') && all_in(&x, |c| c == 'a' || c == 'b'),
        "x = {x:?}"
    );
}
```

- [ ] **Step 2: Remove `k1`/`k2` from `slice57_probes.rs`**

In `crates/shinri-solver/tests/slice57_probes.rs`, delete the `// ── known-unknown pins (queued engine-side reconciliation, spec §9 item 1) ──` banner and both functions `k1_stringfuzz_translate_rotate_stays_unknown` and `k2_stringfuzz_translate_graft_stays_unknown` (with their doc comments). Put this comment in their place:

```rust
// `k1`/`k2` (translate-rotate / translate-graft, z3 unsat) moved to
// `slice58_probes::m1_translate_rotate` / `m2_translate_graft`, which assert
// `unsat` (slice-58 spec §7.3).
```

`verdict` stays: `u1`/`u2` still use it.

- [ ] **Step 3: Add the oracle family**

In `crates/shinri-solver/tests/qfs_differential.rs`, insert after the closing `}` of `differential_qfs_model_reconcile` (before the `// Targeted explicit cases` banner):

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Member-prefix differential oracle (slice 58): a membership on a variable
// whose EUF class holds a constant-headed concat (from prefixof / suffixof /
// a concat equation, possibly behind an `or`). Verdicts must agree with z3;
// Sat models are z3-verified. Fresh seed — never perturb existing families'
// seeds.
// ─────────────────────────────────────────────────────────────────────────────

const MP_N_ITERS: usize = 300;

fn gen_member_prefix_body(seed: u64) -> (String, usize) {
    let mut rng = Lcg(seed);
    let nv = 3;
    let mut b = String::from("(set-logic QF_SLIA)\n");
    for k in 0..nv {
        b.push_str(&format!("(declare-fun s{k} () String)\n"));
    }
    const LITS: [&str; 6] = ["a", "b", "ab", "c", "1", "cd"];
    const RES: [&str; 6] = [
        "(re.* (re.range \"a\" \"b\"))",
        "(re.+ (re.range \"a\" \"b\"))",
        "(re.* (re.range \"a\" \"d\"))",
        "(re.++ (str.to_re \"ab\") (re.* (re.range \"a\" \"d\")))",
        "(re.++ (str.to_re \"c\") re.all)",
        "(re.comp (re.++ (str.to_re \"a\") re.all))",
    ];
    let lit = |rng: &mut Lcg| format!("\"{}\"", LITS[rng.below(LITS.len() as u64) as usize]);
    if rng.below(3) != 0 {
        b.push_str("(assert (= s0 s1))\n");
    }
    for _ in 0..1 + rng.below(2) {
        let x = format!("s{}", rng.below(2));
        let l = lit(&mut rng);
        let c = match rng.below(4) {
            0 => format!("(str.prefixof {l} {x})"),
            1 => format!("(str.suffixof {l} {x})"),
            2 => format!("(= {x} (str.++ {l} s2))"),
            _ => format!("(= {x} (str.++ s2 {l}))"),
        };
        if rng.below(3) == 0 {
            let alt = lit(&mut rng);
            b.push_str(&format!("(assert (or {c} (= {x} {alt})))\n"));
        } else {
            b.push_str(&format!("(assert {c})\n"));
        }
    }
    let m = format!(
        "(str.in_re s{} {})",
        rng.below(2),
        RES[rng.below(RES.len() as u64) as usize]
    );
    if rng.below(3) == 0 {
        b.push_str(&format!("(assert (not {m}))\n"));
    } else {
        b.push_str(&format!("(assert {m})\n"));
    }
    if rng.below(2) == 0 {
        b.push_str(&format!("(assert (= (str.len s0) {}))\n", rng.below(5)));
    }
    (b, nv)
}

#[test]
fn differential_qfs_member_prefix() {
    let mut rng = Lcg(0x58_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_unknown_z3_unsat, mut n_z3skip, mut n_witness) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..MP_N_ITERS {
        let seed = rng.next();
        let (body, nv) = gen_member_prefix_body(seed);
        let script = format!("{body}(check-sat)\n");
        let ours = shinri_verdict(&script);
        let theirs = z3_verdict(&script);
        if ours == Verdict::Unknown {
            n_unknown += 1;
            if theirs == Verdict::Unsat {
                n_unknown_z3_unsat += 1;
            }
            continue;
        }
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "MEMBER-PREFIX SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{script}"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let names: Vec<String> = (0..nv).map(|k| format!("s{k}")).collect();
                let get = format!("{script}(get-value ({}))\n", names.join(" "));
                let lines = shinri_lines(&get);
                if let Some(resp) = lines.get(1) {
                    let model = parse_string_values(resp);
                    if !model.is_empty() {
                        let w = z3_with_model(&body, &model);
                        assert_eq!(
                            w,
                            Verdict::Sat,
                            "WITNESS FAILURE (iter {it}, seed {seed}): model {model:?}\n{body}"
                        );
                        n_witness += 1;
                    }
                }
            }
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    println!(
        "differential_qfs_member_prefix: {MP_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown ({n_unknown_z3_unsat} with z3 unsat) / {n_z3skip} z3-unknown; \
         {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "member-prefix family produced zero SAT instances");
    assert!(n_unsat > 0, "member-prefix family produced zero UNSAT instances");
    assert!(n_witness > 0, "no witnesses checked — model path not exercised");
}
```

- [ ] **Step 4: Run the probes at HEAD (before evidence)**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice58_probes)' --no-fail-fast 2>&1 | tee target/slice58-probes-before.log | tail -20`
Expected: 11 tests discovered. `m1_translate_rotate`, `m2_translate_graft` and `rf1_member_popped_with_scope` FAIL (the first `check-sat` answers `"unknown"`; `rf1`'s in-scope `unsat` needs G′). `g1`–`g3` and `rf2`–`rf4` PASS. Record the outcome of `m3`/`m4`: if either already passes at HEAD, keep it as a regression guard and note it in `target/slice58-before.txt` (spec §7.3). If any other `g*`/`rf*` guard fails at HEAD, or `rf1`'s post-`pop` answer is not `sat`, stop and report it: that is a pre-existing defect, not something this slice may re-pin.

- [ ] **Step 5: Run the oracle family at HEAD (before evidence)**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle --no-capture -E 'test(differential_qfs_member_prefix)' 2>&1 | tee target/slice58-oracle-before.log | grep -E 'differential_qfs_member_prefix:|PASS|FAIL|tests run'`
Expected: 1 test discovered (non-zero), PASS, summary line printed. A disagreement or witness failure at HEAD is a pre-existing defect: stop and report it. If the family produces zero UNSAT instances at HEAD, record that and keep going (Task 2 re-checks it).

- [ ] **Step 6: Record the before evidence**

```bash
{
  echo "slice58 before (HEAD $(git rev-parse --short HEAD))"
  grep -E 'PASS|FAIL' target/slice58-probes-before.log
  grep 'differential_qfs_member_prefix:' target/slice58-oracle-before.log
} > target/slice58-before.txt
cat target/slice58-before.txt
```

The number in `(N with z3 unsat)` is the before count used in Task 2 Step 7.

- [ ] **Step 7: Format, lint, commit**

```bash
cargo fmt --all
taskset -c 0-11 mise run lint
taskset -c 0-11 cargo clippy -p shinri-solver --features oracle --tests -- -D warnings 2>&1 | grep -E 'qfs_differential|slice58' || true
git add crates/shinri-solver/tests/slice58_probes.rs crates/shinri-solver/tests/slice57_probes.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(slice58): member-prefix probes and oracle family (m1/m2 fail at HEAD)"
```

The `--features oracle` clippy has pre-existing errors in other oracle files (slice-54 queue). Only errors in the code this task added must be fixed; the `grep` shows them.

---

### Task 2: Rule G′

**Files:**
- Modify: `crates/shinri-str/src/memb.rs` (new const + helper above `memb_check` at line ~146; call site after Rule G's fully-ground block at line ~212; tests in `mod tests` at line ~585)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (add the before const and the strict-fall assertion)

**Interfaces:**
- Consumes: `normalize::deep_normal_form_cited(&mut Context, &mut EqualityEngine, &[TermId], TermId, &mut Vec<EqLeaf>) -> Option<Vec<TermId>>`, `regex::deriv(u32, &Rex) -> Rex`, `regex::node_count(&Rex) -> usize`, `regex::FUEL_NODE_CAP`, `EqualityEngine::{intern, find, explain}`.
- Produces: `pub(crate) const MEMBER_CAP: usize = 64;` and
  `pub(crate) fn member_prefix_conflict(terms: &mut Context, eq: &mut EqualityEngine, known: &[TermId], t: TermId, rex: &Rex, lit: shinri_core::Lit) -> Option<Vec<EqLeaf>>`
  (returns the full conflict justification, `Asserted(lit)` first).

- [ ] **Step 1: Write the failing unit tests**

In `crates/shinri-str/src/memb.rs`, inside `mod tests`, add to the `use` lines:

```rust
    use shinri_theory::types::{EqJust, EqLeaf};
```

and append these helpers and tests at the end of `mod tests`:

```rust
    fn cat(ctx: &mut Context, parts: &[TermId]) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), parts).unwrap()
    }

    fn lit_of(v: u32) -> shinri_core::Lit {
        shinri_core::Lit::new(shinri_core::Var::new(v), true)
    }

    /// Merge `a ≈ b`, justified by the input literal `l`.
    fn merge_by(eq: &mut EqualityEngine, a: TermId, b: TermId, l: shinri_core::Lit) {
        let (an, bn) = (eq.intern(a), eq.intern(b));
        eq.merge(an, bn, EqJust::Asserted(l)).expect("no EUF conflict");
    }

    fn sigma_star() -> Rex {
        regex::star(Rex::Range(0, regex::MAX_CODE))
    }

    #[test]
    fn g_prime_conflict_cites_lit_and_member_merges() {
        // x ≈ y (lit 1), x ≈ "1"·z (lit 2, e.g. a decided disjunct),
        // y ∈ [a-b]*: ∂_1 = ∅ ⟹ conflict citing lit 9 (the membership) and
        // BOTH merges, so it is valid on any branch.
        let mut ctx = Context::new();
        let (x, y, z) = (var(&mut ctx, "x"), var(&mut ctx, "y"), var(&mut ctx, "z"));
        let one = ctx.mk_string_const("1");
        let c = cat(&mut ctx, &[one, z]);
        let mut eq = EqualityEngine::default();
        merge_by(&mut eq, x, y, lit_of(1));
        merge_by(&mut eq, x, c, lit_of(2));
        let known = vec![y, x, c, z, one];
        let just = super::member_prefix_conflict(
            &mut ctx,
            &mut eq,
            &known,
            y,
            &regex::star_range_test('a', 'b'),
            lit_of(9),
        )
        .expect("∂_1([a-b]*) = ∅ must conflict");
        assert_eq!(just[0], EqLeaf::Asserted(lit_of(9)), "membership literal first");
        for l in [lit_of(1), lit_of(2)] {
            assert!(just.contains(&EqLeaf::Asserted(l)), "missing {l:?} in {just:?}");
        }
    }

    #[test]
    fn g_prime_compatible_member_is_none() {
        let mut ctx = Context::new();
        let (y, z) = (var(&mut ctx, "y"), var(&mut ctx, "z"));
        let a = ctx.mk_string_const("a");
        let c = cat(&mut ctx, &[a, z]);
        let mut eq = EqualityEngine::default();
        merge_by(&mut eq, y, c, lit_of(1));
        let known = vec![y, c, z, a];
        assert!(super::member_prefix_conflict(
            &mut ctx,
            &mut eq,
            &known,
            y,
            &regex::star_range_test('a', 'b'),
            lit_of(9),
        )
        .is_none());
    }

    #[test]
    fn g_prime_reads_member_deep_nf() {
        // y ≈ "a"·z (lit 1), z ≈ "b"·w (lit 2), y ∈ "ac"·Σ*: only the deep NF
        // "ab"·w exposes the clash; the z-merge must be cited.
        let mut ctx = Context::new();
        let (y, z, w) = (var(&mut ctx, "y"), var(&mut ctx, "z"), var(&mut ctx, "w"));
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let ca = cat(&mut ctx, &[a, z]);
        let cb = cat(&mut ctx, &[b, w]);
        let mut eq = EqualityEngine::default();
        merge_by(&mut eq, y, ca, lit_of(1));
        merge_by(&mut eq, z, cb, lit_of(2));
        let known = vec![y, ca, z, cb, w, a, b];
        let rex = regex::concat(vec![regex::lit_test("ac"), sigma_star()]);
        let just = super::member_prefix_conflict(&mut ctx, &mut eq, &known, y, &rex, lit_of(9))
            .expect("∂_ab(\"ac\"·Σ*) = ∅ must conflict");
        assert!(just.contains(&EqLeaf::Asserted(lit_of(2))), "deep-NF merge cited: {just:?}");
    }

    #[test]
    fn g_prime_negative_polarity() {
        // ¬(y ∈ "a"·Σ*) is checked as y ∈ comp("a"·Σ*); ∂_a = comp(Σ*) = ∅.
        let mut ctx = Context::new();
        let (y, z) = (var(&mut ctx, "y"), var(&mut ctx, "z"));
        let a = ctx.mk_string_const("a");
        let c = cat(&mut ctx, &[a, z]);
        let mut eq = EqualityEngine::default();
        merge_by(&mut eq, y, c, lit_of(1));
        let known = vec![y, c, z, a];
        let rex = regex::comp(regex::concat(vec![regex::lit_test("a"), sigma_star()]));
        assert!(
            super::member_prefix_conflict(&mut ctx, &mut eq, &known, y, &rex, lit_of(9))
                .is_some()
        );
    }

    #[test]
    fn g_prime_member_cap() {
        // MEMBER_CAP compatible members ("a"·z_i), then one clashing ("1"·z):
        // past the cap ⟹ None. Clashing member first ⟹ Some.
        let mut ctx = Context::new();
        let y = var(&mut ctx, "y");
        let a = ctx.mk_string_const("a");
        let one = ctx.mk_string_const("1");
        let mut eq = EqualityEngine::default();
        let mut compatible = Vec::new();
        for i in 0..super::MEMBER_CAP {
            let zi = var(&mut ctx, &format!("z{i}"));
            let ci = cat(&mut ctx, &[a, zi]);
            merge_by(&mut eq, y, ci, lit_of(1));
            compatible.push(ci);
        }
        let z = var(&mut ctx, "z");
        let clash = cat(&mut ctx, &[one, z]);
        merge_by(&mut eq, y, clash, lit_of(2));
        let rex = regex::star_range_test('a', 'b');

        let mut late = vec![y];
        late.extend(&compatible);
        late.push(clash);
        assert!(
            super::member_prefix_conflict(&mut ctx, &mut eq, &late, y, &rex, lit_of(9)).is_none(),
            "the 65th member is past MEMBER_CAP"
        );

        let mut early = vec![y, clash];
        early.extend(&compatible);
        assert!(
            super::member_prefix_conflict(&mut ctx, &mut eq, &early, y, &rex, lit_of(9)).is_some()
        );
    }

    #[test]
    fn g_prime_skips_unexpandable_member() {
        // Review Focus 5: y ≈ s·s·u (self-referential through s ≈ y) may not
        // converge; it is skipped, and the "1"·z member still decides.
        let mut ctx = Context::new();
        let (y, s, u, z) = (
            var(&mut ctx, "y"),
            var(&mut ctx, "s"),
            var(&mut ctx, "u"),
            var(&mut ctx, "z"),
        );
        let one = ctx.mk_string_const("1");
        let ssu = cat(&mut ctx, &[s, s, u]);
        let c = cat(&mut ctx, &[one, z]);
        let mut eq = EqualityEngine::default();
        merge_by(&mut eq, y, s, lit_of(1));
        merge_by(&mut eq, y, ssu, lit_of(2));
        merge_by(&mut eq, y, c, lit_of(3));
        let known = vec![y, s, ssu, u, c, z, one];
        assert!(super::member_prefix_conflict(
            &mut ctx,
            &mut eq,
            &known,
            y,
            &regex::star_range_test('a', 'b'),
            lit_of(9),
        )
        .is_some());
    }
```

- [ ] **Step 2: Run the unit tests to verify they fail**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(g_prime_)'`
Expected: compile error, `cannot find function member_prefix_conflict in module super` (and `MEMBER_CAP`).

- [ ] **Step 3: Implement the helper**

In `crates/shinri-str/src/memb.rs`, change the import line

```rust
use shinri_theory::{TCheck, TheoryCtx};
```

to

```rust
use shinri_theory::{EqualityEngine, TCheck, TheoryCtx};
```

and insert directly above `pub(crate) fn memb_check(`:

```rust
/// Rule G′ (slice 58): concat members of `t`'s class examined per atom.
/// Past the cap the rest are skipped — decisiveness only, never a verdict.
pub(crate) const MEMBER_CAP: usize = 64;

/// Rule G′ (slice 58): a membership `t ∈ rex` against the concat MEMBERS of
/// `t`'s EUF class. `normalize::rep_rank` never makes a concat the class
/// representative, so when `t`'s class is `{x, y, "1"·z}` Rule G reads
/// `nf(t) = [t]` and never consumes the `"1"`. Here every concat member `k`
/// (`k ≠ t`, at most `MEMBER_CAP`, in `known` order) is read through its
/// cited deep NF; its leading constants are consumed through the derivative,
/// and `∂_w rex = ∅` yields the conflict justification
/// `[Asserted(lit)] ++ explain(t, k) ++ deep-NF antecedents`.
///
/// Sound at any decision level: under the cited merges `t = w·u`, and
/// `∂_w rex = ∅` means no word with prefix `w` is in `rex` (for a negative
/// atom `rex = comp(R)`: every such word is in `R`), contradicting `lit`.
/// Every substituted merge is cited, so — like Rule G's ground conflict —
/// it needs no `side_clean` gate. A member whose deep NF does not converge,
/// or whose derivative exceeds `FUEL_NODE_CAP`, is skipped: G′ is additive,
/// so it never fences to `Unknown`.
pub(crate) fn member_prefix_conflict(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    t: TermId,
    rex: &Rex,
    lit: shinri_core::Lit,
) -> Option<Vec<EqLeaf>> {
    let tn = eq.intern(t);
    let root = eq.find(tn);
    let mut seen: FxHashSet<TermId> = FxHashSet::default();
    let mut examined = 0usize;
    for &k in known {
        let is_concat = matches!(
            terms.term_node(k),
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrConcat),
                ..
            }
        );
        if k == t || !is_concat || !seen.insert(k) {
            continue;
        }
        let kn = eq.intern(k);
        if eq.find(kn) != root {
            continue;
        }
        if examined == MEMBER_CAP {
            break;
        }
        examined += 1;
        let mut just = vec![EqLeaf::Asserted(lit)];
        eq.explain(tn, kn, &mut just);
        let Some(nf) = normalize::deep_normal_form_cited(terms, eq, known, k, &mut just) else {
            continue;
        };
        let mut cur = rex.clone();
        let mut fenced = false;
        'atoms: for &a in &nf {
            let Some(w) = terms.string_const_value(a).map(str::to_owned) else {
                break;
            };
            for c in w.chars() {
                cur = regex::deriv(c as u32, &cur);
                if regex::node_count(&cur) > regex::FUEL_NODE_CAP {
                    fenced = true;
                    break 'atoms;
                }
                if matches!(cur, Rex::Empty) {
                    break 'atoms;
                }
            }
        }
        if !fenced && matches!(cur, Rex::Empty) {
            return Some(just);
        }
    }
    None
}
```

- [ ] **Step 4: Run the unit tests to verify they pass**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(g_prime_)'`
Expected: 6 tests run, 6 passed. If `g_prime_negative_polarity` fails, check `regex::deriv` on `Comp` (`regex.rs:355`, `comp(deriv(c, inner))`) and `regex::comp`'s `Σ*` collapse (`regex.rs:229`) before touching the helper. A syntactic non-reduction is a spec deviation (spec §7.3): record it, mark the test `#[ignore = "slice58 deviation: comp derivative not syntactically ∅"]`, and queue it. Do not widen the emptiness test.

- [ ] **Step 5: Call Rule G′ from `memb_check`**

In `memb_check`, Rule G moves `rex` into `cur`. Change

```rust
        let mut cur = rex;
        let mut i = 0usize;
        let mut fenced = false;
```

to

```rust
        let mut cur = rex.clone();
        let mut i = 0usize;
        let mut fenced = false;
```

Then, directly after the closing `}` of the `if i == nf.len() { … }` block (the fully-ground discharge/conflict) and before the `// ── Bare-range LEAF` comment, insert:

```rust
        // ── Rule G′ (slice 58): the class's concat members ──────────────
        // Rule G read `t`'s own NF, whose head is the class rep; a concat
        // member is never the rep, so its constant prefix was unseen. Runs
        // before the leaf arms (they `continue` past the atom). Conflict
        // only: no split, no mint, no fuel; nothing found ⟹ fall through.
        if let Some(just) = member_prefix_conflict(cx.terms, cx.eq, known, t, &rex, lit) {
            return Some(TCheck::Conflict(just));
        }
```

`rex` here is the original (already complemented for a negative atom), not `cur`: each member's prefix is consumed from the start of the regex.

- [ ] **Step 6: Run the probes and the string unit suite**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice58_probes)' 2>&1 | tee target/slice58-probes-after.log | tail -15`
Expected: 11 discovered, 11 passed (or 10 plus `m4` per the Step 4 deviation rule).

Run: `taskset -c 0-11 cargo nextest run -p shinri-str`
Expected: all pass, including the existing `memb.rs` tests (`rule_e_expansion_shape`, `equality_pinned_leaf_falls_back_to_unfolding`, …) unchanged.

- [ ] **Step 7: Tighten the oracle family**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle --no-capture -E 'test(differential_qfs_member_prefix)' 2>&1 | tee target/slice58-oracle-after.log | grep -E 'differential_qfs_member_prefix:|PASS|FAIL'`
Expected: PASS, 0 disagreements, and `(M with z3 unsat)` with M strictly below the before count N from `target/slice58-before.txt`.

Then, in `qfs_differential.rs`, add below `const MP_N_ITERS: usize = 300;` (N is the measured before count, e.g. `12`):

```rust
/// `unknown`-where-z3-`unsat` count at `f515c00` (slice-58 plan, Task 1 Step 5).
const MP_BEFORE_UNKNOWN_Z3_UNSAT: usize = N;
```

and at the end of `differential_qfs_member_prefix`, after the `n_witness` assertion:

```rust
    assert!(
        n_unknown_z3_unsat < MP_BEFORE_UNKNOWN_Z3_UNSAT,
        "unknown-where-z3-unsat {n_unknown_z3_unsat} not below the slice-58 base \
         {MP_BEFORE_UNKNOWN_Z3_UNSAT}"
    );
```

If M is not below N, stop: the family is not exercising G′. Report the counts rather than changing the generator.

Re-run the Step 7 command: PASS.

- [ ] **Step 8: Format, lint, commit**

```bash
cargo fmt --all
taskset -c 0-11 mise run lint
git add crates/shinri-str/src/memb.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "fix(str): slice58 - membership Rule G over class concat members"
```

---

### Task 3: Gates

**Files:** none (logs under `target/`).

- [ ] **Step 1: Full blocking tier**

Run: `taskset -c 0-11 mise run ci 2>&1 | tee target/slice58-ci.log | tail -30`
Expected: lint, deny, secrets and test green. Record the nextest totals (run / passed / skipped). A failure in an existing string test (`qfs_fuzz_corpus`, `script_e2e`, `slice33_probes`, `slice57_probes`, …) gets investigated, not re-pinned. G′ only adds fully cited conflicts, so a `sat → unsat` flip there is either a pre-existing wrong `sat` (confirm with z3, then report it) or a G′ bug.

- [ ] **Step 2: Oracle suite**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice58-oracle-suite.log | tail -15`
Expected: non-zero discovered count (slice 57 recorded 797 discovered; this slice adds 1), 0 failures. Record discovered / passed / skipped.

- [ ] **Step 3: Note the totals for the report**

Append the totals from Steps 1–2 to `target/slice58-before.txt` under a `gates:` heading. Nothing to commit.

---

### Task 4: Bench run, triage, timing, report, measured outcomes, PR

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice58-member-prefix-report.md` (date = the day the after-run finishes)
- Modify: `docs/superpowers/specs/2026-10-03-shinri-slice58-member-prefix-design.md` (append *Measured outcomes*)

**Interfaces:**
- Consumes: branch HEAD after Task 2; `bench/results/slice58-base/results.jsonl`; `target/slice58-base/shinri`.
- Produces: the report and spec section cited by the PR.

- [ ] **Step 1: Wait for the base run**

Wait for `target/slice58-base/finished.txt` (use a Monitor/until-loop, not a foreground sleep). Then confirm: `wc -l bench/results/slice58-base/results.jsonl` (rows + 1 fixture line).

- [ ] **Step 2: Build and launch the after-run detached**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice58-after && cp target/release/shinri target/slice58-after/shinri
md5sum target/slice58-after/shinri | tee target/slice58-after/md5.txt
git rev-parse --short HEAD | tee target/slice58-after/commit.txt
date -u +%FT%TZ > target/slice58-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_S,QF_SLIA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice58-after/shinri --run-id slice58 \
  > target/slice58-after/run.log 2>&1; date -u +%FT%TZ > target/slice58-after/finished.txt' \
  > /dev/null 2>&1 &
```

Wait for `target/slice58-after/finished.txt` the same way.

- [ ] **Step 3: Render reports and join the runs**

```bash
BENCH_RUN_ID=slice58-base mise run bench-report
BENCH_RUN_ID=slice58 mise run bench-report
python3 - <<'EOF'
import json, collections
def load(p):
    out = {}
    for line in open(p):
        r = json.loads(line)
        if "path" in r:
            out[r["path"]] = r
    return out
a = load("bench/results/slice58-base/results.jsonl")
b = load("bench/results/slice58/results.jsonl")
assert a.keys() == b.keys(), "row sets differ"
c = collections.Counter()
changed = []
for p in sorted(a):
    va, vb = a[p]["verdict"], b[p]["verdict"]
    if va != vb:
        c[(a[p]["logic"], va, vb)] += 1
        changed.append((p, a[p]["logic"], va, vb))
for k, n in sorted(c.items()):
    print(*k, n)
print("total changed", len(changed))
for lg in ("QF_S", "QF_SLIA"):
    for run, d in (("base", a), ("after", b)):
        rej = sum(1 for r in d.values() if r["logic"] == lg and r["verdict"] == "unknown:str-model-rejected")
        cor = sum(1 for r in d.values() if r["logic"] == lg and r["verdict"] == "correct")
        print(lg, run, "correct", cor, "str-model-rejected", rej)
for p in ("QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-translate-rotate-fuzz.smt2",
          "QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-translate-graft-translate.smt2"):
    print(p, a[p]["verdict"], "->", b[p]["verdict"])
open("target/slice58-after/changed.tsv", "w").write(
    "\n".join("\t".join(x) for x in changed) + "\n")
EOF
```

Expected: both stringfuzz rows `-> correct` (criterion 2).

- [ ] **Step 4: Check every changed verdict that has no ground truth**

For every changed row whose after verdict is `unverified` (no `:status`), run z3 (timeout 60 s) and compare with shinri's answer from a single after-binary run. Any disagreement is a wrong answer: stop the slice for a ruling (criterion 1).

```bash
awk -F'\t' '$4=="unverified"{print $1}' target/slice58-after/changed.tsv > target/slice58-after/unverified.txt
while read -r p; do
  ours=$(timeout 20 target/slice58-after/shinri bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$')
  theirs=$(timeout 60 z3 bench/corpus/$p 2>/dev/null | head -1)
  printf '%s\t%s\t%s\n' "$p" "$ours" "$theirs"
done < target/slice58-after/unverified.txt | tee target/slice58-after/unverified-z3.tsv
awk -F'\t' '($2=="sat"&&$3=="unsat")||($2=="unsat"&&$3=="sat")' target/slice58-after/unverified-z3.tsv | wc -l
```

Expected: the last count is 0.

- [ ] **Step 5: Triage**

For every changed row that starts or ends in `correct`, and every row that ends in `wrong`, do 3 runs per binary, interleaved, with the bench's command line, on cores 12–23 with nothing else running:

```bash
for p in $(awk -F'\t' '$3=="correct"||$4=="correct"||$4=="wrong"{print $1}' target/slice58-after/changed.tsv); do
  for i in 1 2 3; do
    for bin in target/slice58-base/shinri target/slice58-after/shinri; do
      r=$(taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats bench/corpus/$p 2>&1 \
          | grep -E '^(sat|unsat|unknown)$|^stats:' | tr '\n' ' ')
      printf '%s\t%s\t%s\t%s\n' "$p" "$(basename $(dirname $bin))" "$i" "$r"
    done
  done
done | tee target/slice58-after/triage.tsv
```

If a group has more than 200 rows, triage a stratified sample of at least 32 rows across its families instead, and state the sample size. Classify each row as in the slice-53 report: *attributable* if base and after each reproduce their bench verdict 3/3, *noise* otherwise. Any wrong answer from the after binary stops the slice (criterion 1). A reproducible `correct → *` loss stops the slice for a ruling (criterion 4). For criterion 3, apply the slice-57 crediting rule: a `* → str-model-rejected` row whose base binary also gives `fence=str-model-rejected` in triage counts as `str-model-rejected` in the base too.

The report must count the attributable `→ correct` rows G′ decided. For each such row, the after binary answers `unsat`, and the base binary answered `unknown` 3/3.

- [ ] **Step 6: Timing (criterion 5)**

Serial, interleaved run on 150 seeded-sampled rows per logic that are `correct` in both runs:

```bash
python3 - <<'EOF'
import json, random, subprocess, time
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
a = load("bench/results/slice58-base/results.jsonl")
b = load("bench/results/slice58/results.jsonl")
rng = random.Random(58)
for lg in ("QF_S", "QF_SLIA"):
    rows = sorted(p for p in a if a[p]["logic"] == lg and a[p]["verdict"] == b[p]["verdict"] == "correct")
    sample = rng.sample(rows, min(150, len(rows)))
    tot = {"base": 0.0, "after": 0.0}
    for p in sample:
        for name in ("base", "after"):
            t0 = time.monotonic()
            subprocess.run(["taskset", "-c", "12", f"target/slice58-{name}/shinri", f"bench/corpus/{p}"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
            tot[name] += time.monotonic() - t0
    print(lg, len(sample), "rows: base %.2f s, after %.2f s, ratio %.3f" % (tot["base"], tot["after"], tot["after"] / tot["base"]))
EOF
```

Expected: each ratio is within 0.95–1.05. Also report median/p90 `wall_ms` per logic from the two `results.jsonl` over both-`correct` rows.

- [ ] **Step 7: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-03-smtlib-2024-slice57-str-model-reconcile-report.md`:
- *Headline*
- *Commands*: the exact commands from Tasks 0, 3 and 4
- *Runs*: both binaries with md5, started/finished, row counts
- *Success criteria*: spec §8 table, each PASS/FAIL with evidence
  - probes: `target/slice58-probes-before.log` / `-after.log`
  - oracle: before/after summary lines
  - gates: Task 3 totals
- *Per-logic matrix*, including `str-model-rejected` base vs after (raw and credited)
- *Transition matrices*
- *Triage*: method, dispositions, the unverified-z3 check, the count of rows G′ decided
- *Timing*
- *What changed versus the spec*: every deviation, including the `m3`/`m4` HEAD outcomes from Task 1 Step 4 and any Task 2 Step 4 ruling
- *Gates*
- *Queued for the next slice*: spec §9 items 1–3, then the slice-57 report's queue items 3–5 and its carried lists, copied verbatim, with a line saying slice-57 items 1 and 6 merge into §9 item 1

- [ ] **Step 8: Append *Measured outcomes* to the spec**

Append to `docs/superpowers/specs/2026-10-03-shinri-slice58-member-prefix-design.md`:

```markdown
## 11. Measured outcomes

Full evidence:
`docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice58-member-prefix-report.md`.

| # | criterion | result |
| --- | --- | --- |
| 1 | 0 `* → wrong`; 0 wrong answers in triage | <PASS/FAIL + counts, unverified-z3 check> |
| 2 | `translate-rotate-fuzz`, `translate-graft-translate` answer `unsat` | <PASS/FAIL> |
| 3 | credited `str-model-rejected` does not increase | <base → after per logic, raw and credited> |
| 4 | no reproducible `correct → *` loss | <PASS/FAIL + triage counts> |
| 5 | serial timing within ±5% | <ratios per logic> |
| 6 | `ci` green; oracle suite non-zero, passing; §7.4 count falls | <PASS/FAIL + counts> |

Rows decided by G′: <count and families>.

### Deviations from this spec

- <each deviation, or "None.">
```

Replace every `<…>` with measured values before committing. None may remain.

- [ ] **Step 9: Commit, push, PR**

```bash
git add docs/superpowers/research/*slice58* docs/superpowers/specs/2026-10-03-shinri-slice58-member-prefix-design.md
git commit -m "docs(bench+spec): slice58 - bench run and measured outcomes"
git push -u origin slice58-member-prefix
gh pr create --base main --title "slice58: membership Rule G over class concat members" \
  --body "Spec: docs/superpowers/specs/2026-10-03-shinri-slice58-member-prefix-design.md
Plan: docs/superpowers/plans/2026-10-03-shinri-slice58-member-prefix.md
Report: docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice58-member-prefix-report.md

<headline numbers from the report: wrong rows, rows decided by G′, str-model-rejected base → after, oracle counts, timing ratios>"
```

Fill the body's placeholders from the report before running. Merge with a merge commit only after CI is green, then delete the branch locally and on the remote (AGENTS.md). Ask the user before merging.
