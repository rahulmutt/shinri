# shinri QF_BVFP Slice 6 — n-ary `=` Soundness Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the two z3-confirmed wrong-SAT families (n-ary `=` over Bool and over uninterpreted sorts) by making `word_norm`'s n-ary `=`/`distinct` expansion sort-universal, and sweep in the four carried slice-5 minors (ABV bare-Bool exemption, RM model extraction, get-value through eliminated ites, 0-ary define-fun bare-symbol expansion).

**Architecture:** One authoritative fix point: delete the `is_word_sort` gate on `word_norm`'s two n-ary expansion arms so every sort expands to binary before any stage runs; pin the old dropping arms (tseitin Bool-Eq, EUF `new_var` Eq) with `debug_assert`s. The minors are four independent, localized changes (one fence guard, one model-extraction channel, one get-value fallback map, one parser resolution-order fix).

**Tech Stack:** Rust workspace (crates `shinri-solver`, `shinri-fp`, `shinri-bv`, `shinri-euf`, `shinri-theory`, `shinri-parser`, `shinri-core`). Differential oracle via `easy-smt` dev-dep driving `z3 -smt2 -in` (z3 4.16.0 is on PATH at `~/.local/share/mise/installs/github-z3-prover-z3/z3-4.16.0/bin/z3`).

**Spec:** `docs/superpowers/specs/2026-07-02-shinri-qfbvfp-slice6-nary-soundness-design.md`

## Global Constraints

- **No new dependencies.** The `oracle` cargo feature and `easy-smt = "0.2"` dev-dep already exist in `crates/shinri-solver/Cargo.toml`; new `--test` files need no Cargo.toml changes.
- **Verdict-soundness invariant:** never trade a wrong verdict for another wrong verdict; sound `Unknown` is always acceptable, wrong SAT/UNSAT never is.
- **Baseline discipline:** all pre-existing differential-oracle suite counts must stay byte-identical to the slice-5 baseline (listed in Task 9); the ONLY deliberately flipped test is the ABV bare-Bool sound-Unknown canary (Task 5).
- **Long suites (multi-minute: full workspace net, full oracle) are run by the controller directly in background Bash** — never inside a subagent (they loop subagents; standing user instruction).
- **Every debug_assert message must name the invariant's enforcement point** (word_norm) so a future failure is self-diagnosing.
- **Commit convention:** `feat(solver): … (slice 6)` / `test(fp): … (slice 6)` / `fix(parser): … (slice 6)` / `docs(qfbvfp): … (slice 6)`, matching slice-5 history.
- **Branch/finish:** work lands on local `main`; KEEP LOCAL, no push (standing user choice across slices 2c..5).

---

### Task 1: Pre-flight — z3 diffs for the untested sorts + canary hunt

Front-loaded per the cross-slice canary lesson: know every verdict and every pinned test BEFORE changing code. Produces an evidence file that Tasks 3 and 9 consume.

**Files:**
- Create: `.superpowers/sdd/6/preflight.md` (evidence notes)
- Create (scratch, not committed): `/tmp/claude-1000/-workspace/494dec5a-c2cc-4035-8399-311b23dedddd/scratchpad/nary_{bool,uf,string,array}.smt2`

**Interfaces:**
- Produces: `.superpowers/sdd/6/preflight.md` recording, for each of the 4 scripts below, the shinri verdict and the z3 verdict. Task 3 reads the String/Array rows to finalize its test expectations; Task 9 re-runs the canary grep.

- [ ] **Step 1: Write the four probe scripts** (one file each in the scratchpad):

`nary_bool.smt2`:
```smt2
(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)
(assert (= p q r))(assert p)(assert q)(assert (not r))
(check-sat)
```

`nary_uf.smt2`:
```smt2
(declare-sort U 0)
(declare-const a U)(declare-const b U)(declare-const d U)
(assert (= a b d))(assert (distinct a d))
(check-sat)
```

`nary_string.smt2`:
```smt2
(declare-const s1 String)(declare-const s2 String)(declare-const s3 String)
(assert (= s1 s2 s3))(assert (distinct s1 s3))
(check-sat)
```

`nary_array.smt2`:
```smt2
(declare-const a1 (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const a2 (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const a3 (Array (_ BitVec 4) (_ BitVec 4)))
(assert (= a1 a2 a3))(assert (distinct a1 a3))
(check-sat)
```

- [ ] **Step 2: Run each through shinri and z3**

Run for each file F:
```bash
cargo run -q -p shinri-cli -- <scratchpad>/F.smt2
z3 <scratchpad>/F.smt2
```
Expected: bool → shinri `sat` (the live bug), z3 `unsat`. uf → shinri `sat`, z3 `unsat`. string → record both (z3 must be `unsat`; shinri may be `sat` = a third live wrong-SAT, `unsat` = already safe, or `unknown` = soundly fenced). array → shinri `unknown` expected (extensionality fence), z3 `unsat`.

- [ ] **Step 3: Canary grep for tests pinning old behavior**

Run:
```bash
grep -rn "nary\|n-ary" crates/*/tests/ crates/*/src/ --include="*.rs" -l
grep -rn "unknown" crates/shinri-solver/tests/script_e2e.rs
```
Known flips (verify no others): `word_norm.rs:270` `nary_eq_and_distinct_expand_for_word_sorts_only` asserts Int n-ary distinct is UNTOUCHED (rewritten in Task 2); `script_e2e.rs:196-212` `abv_select_over_bare_bool_ite_is_sound_unknown` (flipped in Task 5). Record any additional hits in the evidence file with a triage note (flip / unaffected / carry).

- [ ] **Step 4: Write `.superpowers/sdd/6/preflight.md`** with the verdict table + canary triage, and commit:

```bash
git add .superpowers/sdd/6/preflight.md
git commit -m "docs(qfbvfp): slice-6 pre-flight — z3 diffs for Bool/UF/String/Array n-ary =, canary triage (slice 6)"
```

---

### Task 2: Sort-universal n-ary expansion in word_norm

**Files:**
- Modify: `crates/shinri-solver/src/word_norm.rs:8-11` (module doc), `:137-138`, `:151-152` (the two guards), `:269-301` (the canary unit test)
- Modify: `crates/shinri-solver/src/lib.rs:286-292` and `:427-432` (stale comments)

**Interfaces:**
- Consumes: nothing new.
- Produces: the invariant every later task relies on — downstream of `WordNorm::normalize`, no `Eq`/`Distinct` node has arity > 2, for ANY sort. `is_word_sort` (word_norm.rs:44) remains, still used by the ite-elimination arm (unchanged).

- [ ] **Step 1: Rewrite the canary unit test to the new expectation (failing first).** In `word_norm.rs`, replace the entire test `nary_eq_and_distinct_expand_for_word_sorts_only` (lines 269-301) with:

```rust
    #[test]
    fn nary_eq_and_distinct_expand_for_all_sorts() {
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let z = bv_var(&mut ctx, "z", 8);
        let eq3 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y, z]).unwrap();
        let d3 = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, y, z]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[eq3, d3]);
        // (= x y z) → (and (= x y) (= y z))
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let yz = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[y, z]).unwrap();
        let expect_eq = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[xy, yz]).unwrap();
        assert_eq!(out[0], expect_eq);
        // (distinct x y z) → (and (distinct x y) (distinct x z) (distinct y z))
        let dxy = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, y]).unwrap();
        let dxz = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, z]).unwrap();
        let dyz = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[y, z]).unwrap();
        let expect_d = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[dxy, dxz, dyz]).unwrap();
        assert_eq!(out[1], expect_d);

        // Slice 6: NON-word sorts expand too — the expansion is sort-universal
        // (the wrong-SAT family lived exactly in the sorts the old guard skipped).
        // Int n-ary distinct:
        let int_s = ctx.int_sort();
        let af = ctx.declare_fun("ai", &[], int_s);
        let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("bi", &[], int_s);
        let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let cf = ctx.declare_fun("ci", &[], int_s);
        let cc = ctx.mk_app(Op::Uninterpreted(cf), &[]).unwrap();
        let di = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, cc]).unwrap();
        let out2 = wn.normalize(&mut ctx, &[di]);
        let dab = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b]).unwrap();
        let dac = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, cc]).unwrap();
        let dbc = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[b, cc]).unwrap();
        let expect_di =
            ctx.mk_app(Op::Builtin(BuiltinOp::And), &[dab, dac, dbc]).unwrap();
        assert_eq!(out2, vec![expect_di], "Int n-ary distinct expands (slice 6)");
        // Bool n-ary = (the tseitin p↔q wrong-SAT family):
        let p = bool_var(&mut ctx, "p");
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let beq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[p, q, r]).unwrap();
        let out3 = wn.normalize(&mut ctx, &[beq]);
        let pq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[p, q]).unwrap();
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[q, r]).unwrap();
        let expect_beq = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[pq, qr]).unwrap();
        assert_eq!(out3, vec![expect_beq], "Bool n-ary = expands (slice 6)");
    }
```
(Uninterpreted-sort expansion is covered end-to-end in Tasks 3-4; the `Context` sort-declaration API isn't needed here.)

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo test -p shinri-solver --lib word_norm -- --nocapture`
Expected: FAIL on `out2` — old code leaves Int-sorted n-ary distinct untouched.

- [ ] **Step 3: Delete the two sort gates.** In `word_norm.rs`, change line 137-138 from:

```rust
            Op::Builtin(BuiltinOp::Eq)
                if new_kids.len() > 2 && is_word_sort(ctx, ctx.sort_of(new_kids[0])) =>
```
to:
```rust
            Op::Builtin(BuiltinOp::Eq) if new_kids.len() > 2 =>
```
and line 151-152 from:
```rust
            Op::Builtin(BuiltinOp::Distinct)
                if new_kids.len() > 2 && is_word_sort(ctx, ctx.sort_of(new_kids[0])) =>
```
to:
```rust
            Op::Builtin(BuiltinOp::Distinct) if new_kids.len() > 2 =>
```

- [ ] **Step 4: Comment sweep (same commit — they describe the lines being changed).**
  - `word_norm.rs` module doc line ~10: change “**n-ary `=`/`distinct` expansion** over the same word sorts” to “**n-ary `=`/`distinct` expansion** over ALL sorts (slice 6: the old word-sort gate excluded exactly the sorts where tseitin/EUF silently dropped operands 3+ — wrong-SAT)”.
  - `lib.rs:286-292` block comment: change “expands n-ary =/distinct over word sorts to binary” to “expands n-ary =/distinct over ALL sorts to binary (slice 6)”.
  - `lib.rs:427-432` comment: change “This only ever sees non-word n-ary distinct now” to “This never sees n-ary =/distinct at all now: word_norm (above) expands every sort to binary (slice 6); the arms below are defense in depth.”

- [ ] **Step 5: Run the unit tests + fast neighbors**

Run: `cargo test -p shinri-solver --lib -- --nocapture`
Expected: PASS, including `nary_eq_and_distinct_expand_for_all_sorts` and all other word_norm tests (ite arms untouched).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/src/word_norm.rs crates/shinri-solver/src/lib.rs
git commit -m "fix(solver): word_norm n-ary =/distinct expansion is sort-universal — closes Bool/UF wrong-SAT family (slice 6)"
```

---

### Task 3: Pin the old dropping arms + e2e repros for every sort

**Files:**
- Modify: `crates/shinri-solver/src/tseitin.rs:141-147`
- Modify: `crates/shinri-euf/src/solver.rs:59-72` (`new_var` Eq arm)
- Test: `crates/shinri-solver/tests/script_e2e.rs` (append)

**Interfaces:**
- Consumes: Task 2's invariant (no >2-ary `=`/`distinct` downstream of word_norm); Task 1's evidence file for the String/Array expectations.
- Produces: nothing later tasks call; the repro tests are the permanent pins.

- [ ] **Step 1: Write the failing e2e repros.** Append to `crates/shinri-solver/tests/script_e2e.rs` (uses the file's existing `run_script` helper):

```rust
// ── Slice 6: n-ary `=` over the sorts word_norm previously skipped ──────────
// Wrong-SAT before slice 6: tseitin encoded Bool (= p q r) as p↔q (operands
// 3+ dropped); EUF new_var registered only kids[0],kids[1]. z3-diffed in the
// slice-5 final review and re-confirmed in the slice-6 pre-flight.

#[test]
fn bool_nary_eq_third_operand_not_dropped_unsat() {
    // (= p q r) ∧ p ∧ q ∧ ¬r — answered sat before slice 6. z3: unsat.
    let out = run_script(
        "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)\
         (assert (= p q r))(assert p)(assert q)(assert (not r))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn bool_nary_eq_sat_twin() {
    let out = run_script(
        "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)\
         (assert (= p q r))(assert p)(check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn uf_nary_eq_transitivity_unsat() {
    // (= a b d) ∧ (distinct a d) over sort U — answered sat before slice 6.
    let out = run_script(
        "(declare-sort U 0)\
         (declare-const a U)(declare-const b U)(declare-const d U)\
         (assert (= a b d))(assert (distinct a d))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn uf_nary_eq_sat_twin() {
    let out = run_script(
        "(declare-sort U 0)\
         (declare-const a U)(declare-const b U)(declare-const d U)\
         (assert (= a b d))(check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn string_nary_eq_transitivity_unsat() {
    // Post-expansion this is two binary String equalities + a binary distinct
    // — the QF_S core's native shape. z3: unsat (pre-flight, Task 1).
    let out = run_script(
        "(declare-const s1 String)(declare-const s2 String)(declare-const s3 String)\
         (assert (= s1 s2 s3))(assert (distinct s1 s3))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn array_nary_eq_stays_sound_unknown() {
    // SOUND FENCE PIN: array-to-array (dis)equality is extensionality-fenced
    // (atom.rs) — n-ary or binary. Expansion must not change that verdict.
    // z3 decides unsat; Unknown is sound. Fence lift is a spec non-goal.
    let out = run_script(
        "(declare-const a1 (Array (_ BitVec 4) (_ BitVec 4)))\
         (declare-const a2 (Array (_ BitVec 4) (_ BitVec 4)))\
         (declare-const a3 (Array (_ BitVec 4) (_ BitVec 4)))\
         (assert (= a1 a2 a3))(assert (distinct a1 a3))(check-sat)",
    );
    assert_eq!(out, vec!["unknown"]);
}
```
**Adjust the String test's expected verdict if Task 1's evidence file recorded something other than a decidable path** (if shinri soundly fences it, pin `"unknown"` with a SOUND-FENCE comment mirroring the array pin; a `sat` verdict against z3's `unsat` would be a NEW bug — stop and report). Same for the Array pin if pre-flight shows anything but `unknown`.

- [ ] **Step 2: Run the new tests** (Task 2 already landed, so most should pass immediately; this validates rather than red-greens — the true failing-first check for the family happened in Task 2 Step 2):

Run: `cargo test -p shinri-solver --test script_e2e -- nary --nocapture`
Expected: all 6 PASS.

- [ ] **Step 3: Add the debug_assert pins.** In `tseitin.rs`, the Bool-Eq arm (line 141) becomes:

```rust
                    BuiltinOp::Eq if self.is_bool(kids[0]) => {
                        // Bool equality = iff. word_norm expands n-ary = for
                        // ALL sorts (slice 6) before encoding, so only the
                        // binary form can reach this arm — asserting that here
                        // keeps the old silent kids[2..] drop from returning.
                        debug_assert_eq!(
                            kids.len(),
                            2,
                            "n-ary Bool = must be expanded by word_norm"
                        );
                        let a = self.encode(kids[0]);
                        let b = self.encode(kids[1]);
                        let nx = self.xor2(a, b);
                        nx.negate()
                    }
```
In `shinri-euf/src/solver.rs` `new_var` (after line 68's `kids` binding):
```rust
                let kids: Vec<shinri_core::TermId> = cx.terms.children(args_slice).to_vec();
                debug_assert_eq!(
                    kids.len(),
                    2,
                    "Eq atom must be binary (word_norm expands n-ary = for all sorts)"
                );
                let a = self.inner.add_term(cx, kids[0]);
                let b = self.inner.add_term(cx, kids[1]);
```

- [ ] **Step 4: Run the affected suites**

Run: `cargo test -p shinri-solver --test script_e2e && cargo test -p shinri-euf`
Expected: PASS (asserts are unreachable post-Task-2).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/tests/script_e2e.rs crates/shinri-solver/src/tseitin.rs crates/shinri-euf/src/solver.rs
git commit -m "test(solver): e2e pins for Bool/UF/String/Array n-ary =; debug_assert the old dropping arms binary (slice 6)"
```

---

### Task 4: Differential z3 oracle for n-ary `=`/`distinct` over Bool + UF

**Files:**
- Create: `crates/shinri-solver/tests/nary_oracle.rs`

**Interfaces:**
- Consumes: the public `Solver`/`Parser` driving pattern (identical to `tests/fp_oracle.rs`).
- Produces: the suite Task 9's baseline records (`differential_qf_uf_nary`).

- [ ] **Step 1: Write the oracle file** (complete file; Lcg + `shinri_outcome` are the repo-standard forms copied from `fp_oracle.rs`):

```rust
//! Differential oracle: shinri-solver vs z3 on random n-ary =/distinct over
//! Bool and an uninterpreted sort (slice 6 — the sorts word_norm previously
//! skipped, where tseitin/EUF silently dropped operands 3+).
//!
//! Run with:
//!   cargo test -p shinri-solver --features oracle --test nary_oracle -- --nocapture
//!
//! Requires `z3` on PATH at runtime. Mirrors tests/fp_oracle.rs.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand.
/// Copied verbatim from tests/fp_oracle.rs to match the existing convention.
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

fn shinri_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

fn z3_outcome_uf(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_UF").expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-sort ")
            || t.starts_with("(declare-const ")
            || t.starts_with("(assert ")
        {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

const BOOLS: &[&str] = &["p", "q", "r", "s"];
const ELEMS: &[&str] = &["a", "b", "c", "d"];

/// One n-ary (arity 2..=4) =/distinct atom over a single sort family.
/// Duplicate operands are allowed on purpose (they fold = to true-ish
/// constraints and make distinct trivially unsat — both good probes).
fn gen_atom(rng: &mut Lcg) -> String {
    let pool: &[&str] = if rng.below(2) == 0 { BOOLS } else { ELEMS };
    let n = 2 + rng.below(3) as usize;
    let ops: Vec<&str> = (0..n)
        .map(|_| pool[rng.below(pool.len() as u64) as usize])
        .collect();
    let op = if rng.below(2) == 0 { "=" } else { "distinct" };
    format!("({} {})", op, ops.join(" "))
}

fn gen_assertion(rng: &mut Lcg) -> String {
    match rng.below(4) {
        0 => gen_atom(rng),
        1 => format!("(not {})", gen_atom(rng)),
        2 => format!("(and {} {})", gen_atom(rng), gen_atom(rng)),
        _ => format!("(or {} {})", gen_atom(rng), gen_atom(rng)),
    }
}

fn gen_script(rng: &mut Lcg) -> String {
    let mut s = String::new();
    s.push_str("(declare-sort U 0)\n");
    for b in BOOLS {
        s.push_str(&format!("(declare-const {b} Bool)\n"));
    }
    for e in ELEMS {
        s.push_str(&format!("(declare-const {e} U)\n"));
    }
    let n = 2 + rng.below(3);
    for _ in 0..n {
        s.push_str(&format!("(assert {})\n", gen_assertion(rng)));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_uf_nary() {
    let mut rng = Lcg(0x51CE6_ABCD);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_uf(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_UF n-ary DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_uf_nary: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(n_unknown == 0, "unknown must be 0 — QF_UF is total ({n_unknown} unknown)");
    assert!(
        n_z3_checked == N_ITERS,
        "expected every iteration z3-checked with zero disagreements \
         ({n_z3_checked}/{N_ITERS} checked)"
    );
}
```

- [ ] **Step 2: Run it**

Run: `cargo test -p shinri-solver --features oracle --test nary_oracle -- --nocapture`
Expected: PASS, printing `sat=… unsat=… unknown=0 z3_checked=200`. Record the sat/unsat split in the evidence file — Task 9 pins it as the new baseline. If a DISAGREEMENT panics: that's a live bug the fix missed — stop, report the script, do not weaken the assert.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/nary_oracle.rs
git commit -m "test(solver): differential z3 oracle for n-ary =/distinct over Bool + uninterpreted sorts (slice 6)"
```

---

### Task 5: Port the bare-Bool fence exemption to abv_stage + flip the canary

**Files:**
- Modify: `crates/shinri-solver/src/abv_stage.rs` (insert before the Bool-sorted catch-all at lines 131-134, inside `walk_fence`)
- Modify: `crates/shinri-solver/tests/script_e2e.rs:196-212` (the pinned canary)

**Interfaces:**
- Consumes: nothing from other slice-6 tasks (independent).
- Produces: nothing later tasks consume.

- [ ] **Step 1: Flip the canary to its post-port expectation (failing first).** In `script_e2e.rs`, rewrite the test at lines 196-212 as:

```rust
#[test]
fn abv_select_over_bare_bool_ite_decided_sat() {
    // Slice 6: the bare-Bool fence exemption (fp_stage/bv_stage) is now
    // ported to the ABV path too — a bare Bool ite condition decides instead
    // of fencing. Was pinned sound-Unknown from slice 5 until the port.
    // Cross-checked: z3 → sat.
    let out = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const p Bool)\
         (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert (= (select a (ite p x y)) #x2a))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn abv_select_over_bare_bool_ite_decided_unsat_twin() {
    // Condition pinned TRUE → ite resolves to x, but (select a x) is forced
    // to two different values → UNSAT. Cross-checked: z3 → unsat.
    let out = run_script(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const p Bool)\
         (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (assert p)\
         (assert (= (select a x) #x00))\
         (assert (= (select a (ite p x y)) #x2a))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}
```

- [ ] **Step 2: z3-verify both scripts** (write each to the scratchpad and run `z3 <file>`): expected `sat` / `unsat` respectively. Then run the tests to see them fail:

Run: `cargo test -p shinri-solver --test script_e2e -- abv_select_over_bare_bool --nocapture`
Expected: FAIL — both currently return `unknown` (fence).

- [ ] **Step 3: Insert the exemption.** In `abv_stage.rs` `walk_fence`, immediately BEFORE the Bool-sorted catch-all (lines 131-134: `if ctx.sort_of(t) == bool_sort { return true; }`), insert the same guard fp_stage uses (`fp_stage.rs:168-173` is the verbatim template — adapt only the local variable names to `walk_fence`'s bindings for the current `App`'s `op` and children):

```rust
            // A bare declared Bool constant (0-ary uninterpreted symbol,
            // Bool-sorted) needs NO theory reasoning: it is Tseitin-encoded
            // as a plain SAT variable regardless of which theories are in
            // play — skeleton, not a foreign theory atom. Same exemption as
            // fp_stage::has_non_fp_theory_atom / bv_stage's
            // has_non_bv_theory_atom (ported in slice 6; closes the pinned
            // sound-Unknown asymmetry from slice 5).
            if matches!(op, Op::Uninterpreted(_))
                && kids.is_empty()
                && ctx.sort_of(t) == bool_sort
            {
                return false;
            }
```

- [ ] **Step 4: Run the tests to verify they pass, plus the ABV neighbors**

Run: `cargo test -p shinri-solver --test script_e2e -- abv --nocapture && cargo test -p shinri-abv`
Expected: PASS — including the pre-existing decided pair at script_e2e.rs:161-194 (unchanged).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/abv_stage.rs crates/shinri-solver/tests/script_e2e.rs
git commit -m "feat(solver): port bare-Bool fence exemption to abv_stage; flip the slice-5 sound-Unknown canary to decided (slice 6)"
```

---

### Task 6: RM model extraction

RM variables are blasted to a 5-lit one-hot selector (`shinri-fp/src/rm.rs`, `RmSel`) cached in the Lowerer's `rm_cache` (`lower.rs:18`) — a separate store from the word `cache`, so `var_bits_split` never sees them and `ModelVal` has no RM variant. Add the missing channel end-to-end.

**Files:**
- Modify: `crates/shinri-theory/src/types.rs:111-126` (`ModelVal`)
- Modify: `crates/shinri-solver/src/model.rs:85-131` (`format_modelval`)
- Modify: `crates/shinri-fp/src/lower.rs` (new `rm_var_sels` method), `crates/shinri-fp/src/lib.rs:387-417` (`lower_mixed`/`lower`)
- Modify: `crates/shinri-solver/src/bv_stage.rs` (`BvSurrogates` gains `base`), `crates/shinri-solver/src/lib.rs` (replay at 733-775, fp wiring at 463-487, new model site in the Sat arm after line 619)
- Test: `crates/shinri-solver/tests/fp_e2e.rs` (append)

**Interfaces:**
- Consumes: `WordNorm.internal` (existing pub field) for the internal-symbol filter.
- Produces: `ModelVal::Rm(shinri_core::RoundingMode)`; `shinri_fp::MixedLowered { words: shinri_bv::Lowered, rm_var_sels: FxHashMap<TermId, [BitLit; 5]> }`; `BvSurrogates.base: u32`; solver field `fp_rm_sels: FxHashMap<TermId, [shinri_core::Lit; 5]>`. Task 7 extends the model site added here.

- [ ] **Step 1: Write the failing e2e test.** Append to `fp_e2e.rs` (uses its existing `run` helper returning `(SolveOutcome, String)`):

```rust
#[test]
fn rm_variable_gets_model_value() {
    // Slice 6: RM variables were absent from get-model (their one-hot
    // selectors live in rm_cache, which var_bits_split never visited).
    let (o, model) = run(
        "(declare-const r RoundingMode)\
         (assert (= r RTZ))(check-sat)(get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(r RTZ)"), "RM var missing/wrong in model: {model}");
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo test -p shinri-solver --test fp_e2e rm_variable_gets_model_value -- --nocapture`
Expected: FAIL — model has no `r` entry.

- [ ] **Step 3: Add the `ModelVal::Rm` variant.** In `shinri-theory/src/types.rs`, add to the enum:

```rust
    /// A rounding-mode value (slice 6: RM variables get model entries).
    Rm(shinri_core::RoundingMode),
```
In `shinri-solver/src/model.rs` `format_modelval`, add the arm:
```rust
        ModelVal::Rm(rm) => {
            use shinri_core::RoundingMode::*;
            match rm {
                Rne => "RNE",
                Rna => "RNA",
                Rtp => "RTP",
                Rtn => "RTN",
                Rtz => "RTZ",
            }
            .to_string()
        }
```

- [ ] **Step 4: Expose the RM selectors from the Lowerer.** In `shinri-fp/src/lower.rs`, next to `var_bits_split` (line 101), add:

```rust
    /// RM-variable selectors: nullary uninterpreted RoundingMode-sorted terms
    /// → their 5-lit one-hot selectors [Rne, Rna, Rtp, Rtn, Rtz]. The RM
    /// mirror of `var_bits_split` (rm_cache is a separate store — slice 6).
    pub fn rm_var_sels(&self, ctx: &Context) -> FxHashMap<TermId, [BitLit; 5]> {
        let mut out = FxHashMap::default();
        for (&tid, sel) in self.rm_cache.iter() {
            if let TermNode::App { op: Op::Uninterpreted(_), args, .. } = ctx.term_node(tid) {
                if ctx.children(*args).is_empty() {
                    out.insert(tid, *sel);
                }
            }
        }
        out
    }
```
(Only RM-sorted terms ever enter `rm_cache`, so no sort re-check is needed; match the file's existing imports.)

- [ ] **Step 5: Carry the selectors out of `lower_mixed`.** In `shinri-fp/src/lib.rs`, add above `lower_mixed` (line 387):

```rust
/// `lower_mixed`'s result: the word-level CNF plus the RM-variable one-hot
/// selectors (slice 6 — model extraction needs them; they are not word bits).
pub struct MixedLowered {
    pub words: shinri_bv::Lowered,
    pub rm_var_sels: FxHashMap<TermId, [BitLit; 5]>,
}
```
Change `lower_mixed`'s return type to `MixedLowered` and its tail (line 405-409) to:
```rust
    // One shared cache: union both sort-split var maps into Lowered.var_bits.
    let (bv_vars, fp_vars) = lw.var_bits_split(ctx);
    let mut var_bits = bv_vars;
    var_bits.extend(fp_vars);
    let rm_var_sels = lw.rm_var_sels(ctx);
    MixedLowered {
        words: shinri_bv::Lowered { cnf: lw.b.finish(), atom_lit, var_bits },
        rm_var_sels,
    }
```
Keep `lower` (line 415) source-compatible: `lower_mixed(ctx, fp_atoms, &[]).words`. Run `cargo build --workspace` and fix any remaining `lower_mixed` call sites the same way (`.words`); only the solver call site (lib.rs:422) gets the full struct handling in Step 6.

- [ ] **Step 6: Wire through the solver.** In `shinri-solver/src/bv_stage.rs`, add `pub base: u32` to `BvSurrogates`; in `replay_bv_cnf` (lib.rs:733-775) populate it: `crate::bv_stage::BvSurrogates { atom_to_lit, var_bits, base }`. Add the solver field (near `fp_var_bits`):

```rust
    /// RM-variable one-hot selectors, remapped to SAT-solver Lits (slice 6).
    fp_rm_sels: rustc_hash::FxHashMap<TermId, [shinri_core::Lit; 5]>,
```
(initialize `FxHashMap::default()` in `Solver::new`). Rewrite the `lowered_fp` match arms (lib.rs:463-487):
```rust
        match lowered_fp {
            Some(lo) => {
                let rm_sels = lo.rm_var_sels;
                let surrogates = self.replay_bv_cnf(&mut sat, lo.words);
                let base = surrogates.base;
                self.fp_rm_sels = rm_sels
                    .into_iter()
                    .map(|(t, sel)| {
                        (t, sel.map(|bl| {
                            shinri_core::Lit::new(shinri_core::Var::new(base + bl.var), bl.pos)
                        }))
                    })
                    .collect();
                // Slice 4b: the mixed Lowered carries BOTH BV and FP variable
                // words in one map; split by sort into the two decode maps.
                self.fp_var_bits.clear();
                for (term, vars) in surrogates.var_bits {
                    if self.ctx.bv_width(self.ctx.sort_of(term)).is_some() {
                        self.bv_var_bits.insert(term, vars);
                    } else {
                        self.fp_var_bits.insert(term, vars);
                    }
                }
                surrogate_map.extend(surrogates.atom_to_lit);
            }
            None => {
                self.fp_var_bits.clear();
                self.fp_rm_sels.clear();
            }
        }
```
(Preserve the existing slice-4b comment block verbatim; only the shown lines change.) Then add the model site in the Sat arm, directly after the FP var_bits loop (after line 619):
```rust
                // RM variables: decode the one-hot selector (slice 6). Internal
                // word_norm symbols are filtered exactly as in the BV/FP loops.
                for (&term, sel) in &self.fp_rm_sels {
                    if self.word_norm.internal.contains(&term) {
                        continue;
                    }
                    let hot = sel.iter().position(|l| {
                        let b = sat.value_of(l.var()).unwrap_or(false);
                        if l.is_positive() { b } else { !b }
                    });
                    if let Some(i) = hot {
                        use shinri_core::RoundingMode::*;
                        let rm = [Rne, Rna, Rtp, Rtn, Rtz][i];
                        use shinri_theory::types::ModelVal;
                        model.values.insert(term, ModelVal::Rm(rm));
                    }
                }
```

- [ ] **Step 7: Run the test + neighbors**

Run: `cargo test -p shinri-solver --test fp_e2e -- --nocapture && cargo test -p shinri-fp && cargo test -p shinri-theory`
Expected: PASS, including `rm_variable_gets_model_value` and the slice-5 hygiene pin `model_never_leaks_ite_internals` (internal RM ite symbols are filtered by the new site's guard).

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-theory/src/types.rs crates/shinri-solver/src/model.rs \
        crates/shinri-fp/src/lower.rs crates/shinri-fp/src/lib.rs \
        crates/shinri-solver/src/bv_stage.rs crates/shinri-solver/src/lib.rs \
        crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): RM variables get get-model values — one-hot selector decode channel (slice 6)"
```

---

### Task 7: get-value through eliminated ites

`get-value` on a term whose word-`ite` was eliminated finds no model entry (the internal `ite!<n>` symbol's value is deliberately filtered) and degrades to `?`/internal-name output. Fix: at model-build time, stash the internal symbols' values in a solver-side map keyed by the ORIGINAL ite TermId (via `WordNorm.ite_var`), and let `format_value` fall back to it. get-model output stays untouched (no `t<N>` noise).

**Files:**
- Modify: `crates/shinri-solver/src/word_norm.rs` (accessor), `crates/shinri-solver/src/lib.rs` (Sat-arm sites C/D + the Task-6 RM site; `format_value` at 238-245; new field)
- Test: `crates/shinri-solver/tests/fp_e2e.rs` (append)

**Interfaces:**
- Consumes: Task 6's RM model site (extended here the same way as the BV/FP sites).
- Produces: solver field `eliminated_ite_vals: FxHashMap<TermId, ModelVal>`; `WordNorm::ite_map()`.

- [ ] **Step 1: Write the failing test.** Append to `fp_e2e.rs` a values-capturing helper + test:

```rust
/// Like `run`, but also collects every `get-value` response.
fn run_values(src: &str) -> (SolveOutcome, Vec<String>) {
    let mut s = Solver::new();
    let mut p = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    let mut values = Vec::new();
    while let Some(result) = p.next_command(s.ctx_mut()) {
        let cmd = result.expect("parse");
        match s.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            CommandResponse::Values(v) => values.push(v),
            _ => {}
        }
    }
    (outcome, values)
}

#[test]
fn get_value_on_eliminated_ite_returns_value_not_internal_name() {
    // Slice 6: word_norm eliminates (ite c x #x00) into an internal ite!<n>
    // definition; get-value on the ORIGINAL ite term must return its value,
    // never the internal name and never "?".
    let (o, values) = run_values(
        "(declare-const c Bool)(declare-const x (_ BitVec 8))\
         (declare-const z (_ BitVec 8))\
         (assert c)(assert (= x #x0f))(assert (= z (ite c x #x00)))\
         (check-sat)(get-value ((ite c x #x00)))",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert_eq!(values.len(), 1);
    assert!(!values[0].contains("ite!"), "internal name leaked: {}", values[0]);
    assert!(!values[0].contains('?'), "no value produced: {}", values[0]);
    assert!(values[0].contains("#x0f"), "expected #x0f (c true, x=#x0f): {}", values[0]);
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo test -p shinri-solver --test fp_e2e get_value_on_eliminated_ite -- --nocapture`
Expected: FAIL on the `'?'` / `#x0f` asserts.

- [ ] **Step 3: Expose the ite map.** In `word_norm.rs`, next to the `internal` field's impl block:

```rust
    /// Original eliminated-ite term → its internal fresh symbol term.
    /// Used by the solver to answer get-value on eliminated ites (slice 6).
    pub(crate) fn ite_map(&self) -> &FxHashMap<TermId, TermId> {
        &self.ite_var
    }
```

- [ ] **Step 4: Stash internal values at model build.** In lib.rs's Sat arm, declare before the BV var_bits loop (Site C, line ~586):

```rust
                // Values of word_norm-internal symbols, keyed by the internal
                // term — surfaced to users only through the eliminated-ite
                // remap below, never through get-model (slice 6).
                let mut internal_vals: rustc_hash::FxHashMap<TermId, shinri_theory::types::ModelVal> =
                    rustc_hash::FxHashMap::default();
```
In the BV loop, replace `if self.word_norm.internal.contains(&term) { continue; }` with computing the value first and routing it:
```rust
                for (&term, sat_vars) in &self.bv_var_bits {
                    let width = sat_vars.len() as u32;
                    let bits: Vec<bool> = sat_vars
                        .iter()
                        .map(|&v| sat.value_of(v).unwrap_or(false))
                        .collect();
                    let packed = shinri_bv::model::pack(width, &bits);
                    use shinri_theory::types::ModelVal;
                    let val = ModelVal::BitVec(width, packed);
                    if self.word_norm.internal.contains(&term) {
                        internal_vals.insert(term, val); // slice 5 filter, slice 6 stash
                    } else {
                        model.values.insert(term, val);
                    }
                }
```
Apply the same restructure to the FP loop (Site D — build `ModelVal::Float { eb, sb, bits: packed }` then route on `internal`) and Task 6's RM site (route `ModelVal::Rm(rm)` on `internal`). Then, after all three loops:
```rust
                // Answer get-value on eliminated ites: remap each original ite
                // term to its internal symbol's value.
                let mut ite_vals: rustc_hash::FxHashMap<TermId, shinri_theory::types::ModelVal> =
                    rustc_hash::FxHashMap::default();
                for (&ite_t, &w) in self.word_norm.ite_map() {
                    if let Some(v) = internal_vals.get(&w) {
                        ite_vals.insert(ite_t, v.clone());
                    }
                }
                self.eliminated_ite_vals = ite_vals;
```
Add the field (near `last_model`), initialized `FxHashMap::default()` in `Solver::new`, and clear it at the top of `check_sat` (`self.eliminated_ite_vals.clear();`) so a non-sat outcome never serves stale values:
```rust
    /// Eliminated-ite terms → model values (get-value fallback; slice 6).
    eliminated_ite_vals: rustc_hash::FxHashMap<TermId, shinri_theory::types::ModelVal>,
```

- [ ] **Step 5: The get-value fallback.** In `format_value` (lib.rs:238-245), insert between the model lookup and the ABV fallback:

```rust
        if let Some(val) = self.eliminated_ite_vals.get(&t) {
            return Some(crate::model::format_modelval(val));
        }
```

- [ ] **Step 6: Run the test + the model-hygiene pins**

Run: `cargo test -p shinri-solver --test fp_e2e -- --nocapture`
Expected: PASS — including `model_never_leaks_ite_internals` (get-model output unchanged: internal values go to `internal_vals`, not `model.values`).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-solver/src/word_norm.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): get-value evaluates through eliminated word-ites via the internal-value remap (slice 6)"
```

---

### Task 8: Parser — 0-ary define-fun macros expand as bare symbols

`resolve_leaf` (parser.rs:473-507) resolves a bare symbol as let → builtin literal → declared fun, never consulting the macro table — so `(define-fun one () Int 1)` followed by bare `one` errors "undeclared symbol". The documented order (env.rs:12-13) is let → macro → fun.

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs:473-507` (`resolve_leaf`)
- Test: `crates/shinri-parser/src/parser.rs` tests module (~line 1441, after `define_fun_expands_and_emits_no_command`); `crates/shinri-solver/tests/script_e2e.rs` (append)

**Interfaces:**
- Consumes: `Env::lookup_macro` (env.rs:44-46, existing).
- Produces: nothing later tasks consume.

- [ ] **Step 1: Write the failing parser tests.** In parser.rs's tests module, after `define_fun_expands_and_emits_no_command` (line 1441):

```rust
    #[test]
    fn nullary_define_fun_expands_as_bare_symbol() {
        // SMT-LIB: a 0-ary defined fun is used WITHOUT parens. Gap fixed in
        // slice 6 — resolve_leaf never consulted the macro table.
        let cs = commands(
            "(define-fun one () Int 1)\n(declare-fun y () Int)\n(assert (= y one))\n(check-sat)",
        );
        assert!(matches!(cs[0], Ok(Command::DeclareFun { .. })));
        assert!(matches!(cs[1], Ok(Command::Assert(_))));
        assert!(matches!(cs[2], Ok(Command::CheckSat)));
        assert_eq!(cs.len(), 3);
    }

    #[test]
    fn non_nullary_macro_bare_use_is_an_error() {
        let cs = commands(
            "(define-fun dbl ((a Real)) Real (+ a a))\n(declare-fun y () Real)\n(assert (= y dbl))",
        );
        assert!(
            cs.iter().any(|c| c.is_err()),
            "bare use of a non-nullary macro must be a diagnostic"
        );
    }
```

- [ ] **Step 2: Run them to verify the first fails**

Run: `cargo test -p shinri-parser nullary_define_fun -- --nocapture && cargo test -p shinri-parser non_nullary_macro_bare -- --nocapture`
Expected: `nullary_define_fun_expands_as_bare_symbol` FAILS ("undeclared symbol one" diagnostic); the error test may already pass (same diagnostic, different message) — keep it as the pin either way.

- [ ] **Step 3: Add the macro lookup.** In `resolve_leaf`, AFTER the builtin-literal `match name` block and BEFORE the `lookup_fun` check, insert:

```rust
        // define-fun macro used as a bare symbol: a 0-ary macro expands to its
        // body (SMT-LIB conformance — slice 6); a non-nullary macro needs
        // application form. Checked after the builtin literals (true/false/RM
        // can't be shadowed) and before lookup_fun, honoring the documented
        // let → macro → fun order (env.rs).
        if let Some(m) = self.env.lookup_macro(name) {
            if m.formals.is_empty() {
                return Ok(m.body);
            }
            return Err(Diagnostic::new(
                sp.clone(),
                format!("macro {name} expects {} argument(s)", m.formals.len()),
            ));
        }
```
(If `Span` is `Copy`, drop the `.clone()` — match the file's existing `sp` usage.)

- [ ] **Step 4: Run parser tests, then the e2e**

Run: `cargo test -p shinri-parser`
Expected: PASS. Then append to `script_e2e.rs`:

```rust
#[test]
fn nullary_define_fun_bare_symbol_solves() {
    // Slice 6: bare `one` expands to the macro body end-to-end.
    let out = run_script(
        "(define-fun one () Int 1)(declare-const y Int)\
         (assert (= y one))(assert (= y 2))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}
```
Run: `cargo test -p shinri-solver --test script_e2e nullary_define_fun -- --nocapture`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-parser/src/parser.rs crates/shinri-solver/tests/script_e2e.rs
git commit -m "fix(parser): 0-ary define-fun macros expand as bare symbols (SMT-LIB conformance, slice 6)"
```

---

### Task 9: Full net, baselines, docs landed

Controller-heavy verification task. The long suites run in BACKGROUND Bash directly (never subagents).

**Files:**
- Modify: `docs/superpowers/specs/2026-07-02-shinri-qfbvfp-slice6-nary-soundness-design.md` (Status → Landed + verification summary)
- Modify: `.superpowers/sdd/6/preflight.md` → extend into the slice ledger
- Modify: memory `shinri-slice5-followups.md` (all four follow-ups resolved — rewrite or delete per what remains)

**Interfaces:**
- Consumes: everything.

- [ ] **Step 1: Full workspace net (background):**

Run: `cargo test --workspace 2>&1 | tail -40` (background; capture the CARGO exit code directly, not the pipe's — re-run the last failing crate individually if the pipe obscures it)
Expected: all suites 0-failed.

- [ ] **Step 2: Full differential oracle baseline (background, ~20 min):**

Run: `cargo test -p shinri-solver --features oracle -- --nocapture 2>&1 | tee .superpowers/sdd/6/oracle-full.txt`
Expected: all suites pass; every pre-existing count BYTE-IDENTICAL to the slice-5 baseline:
`bvfp_mixed 52/148/200, bitcast 115/85/200, int_to_fp 112/88/200, add_sub 183/17, mul 164/36, div 38/2, rem 11/9, fma 16/4, sqrt 26/4, roundint 165/35, to_fp 51/9, relations 123/77, rounding_free 200, fp_to_bv 105/95/200, ite 128/72/200` — plus the NEW `differential_qf_uf_nary` at the counts Task 4 recorded. ANY drift in a pre-existing count = a behavior change the slice didn't intend — stop and diagnose before landing.

- [ ] **Step 3: Clippy net-new zero:**

Run: `cargo clippy --workspace --all-targets 2>&1 | grep -c "^warning"`
Expected: matches the slice-5 known set (solver=2 pre-existing model.rs, fp=22 pre-existing reference.rs, theory/str/parser per the 4e set). Net-new must be zero.

- [ ] **Step 4: Canary re-grep** (same commands as Task 1 Step 3): confirm the only flipped pins are the ones this plan names (word_norm unit test, ABV bare-Bool pair) and remaining `unknown` pins are all legitimately Real-bridge or array-extensionality.

- [ ] **Step 5: Docs + memory.** Spec Status → `Landed <date> (commits <range>)` with a verification summary paragraph (mirror the slice-5 spec's format); extend `.superpowers/sdd/6/preflight.md` into the slice ledger (commit range, verification evidence); update the auto-memory file `shinri-slice5-followups.md` — the wrong-SAT family, ABV port, RM models, and define-fun gap are all resolved; keep only whatever Task 1 uncovered as still-open (e.g. a String verdict surprise), else convert it to a short "slice 6 landed" note and update `MEMORY.md`'s pointer line.

- [ ] **Step 6: Final commit**

```bash
git add docs/ .superpowers/
git commit -m "docs(qfbvfp): mark slice-6 landed — sort-universal n-ary =, ABV exemption, RM models, get-value ites, 0-ary macros (slice 6)"
```
