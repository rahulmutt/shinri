# Slice 64 — Parser coverage Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove three parser gaps that turn about 42,300 SMT-LIB rows into `parse-error`:
- nullary `define-sort` (QF_FP, 39,994 rows);
- integer literals in Real contexts (QF_LRA/QF_UFLRA, about 2,290 rows);
- `(! t :named n)` annotations (QF_UF Rodin, 34 rows).

**Architecture:** All changes are in `shinri-parser`.
- `Env` gains a `numerals_are_real` flag, set by `set-logic` for Reals-only logics. `Env` is the state that survives between commands in both the batch `Parser` and the CLI's `StreamingParser`. `parse_atom_numeral` reads the flag.
- `unify_arith` and `apply_division` recognise constant `(- k)` operands via `Context::const_real_value`. `apply_division` also stops panicking on a zero divisor.
- A new `parse_annotated` handles `!`, and a new `define-sort` command arm registers resolved sort aliases.

E2E and z3 oracle tests sit on top, and a base/after bench closes the slice.

**Tech Stack:** Rust workspace (toolchain pinned in `mise.toml`), cargo-nextest 0.9.140, cargo-fuzz (nightly via mise), z3 from mise via the existing `easy-smt` dev-dependency, `shinri-bench`, python3.

**Spec:** `docs/superpowers/specs/2026-10-07-shinri-slice64-parser-coverage-design.md`

## Global Constraints

- **Scope (spec §2, §4):** only `crates/shinri-parser/src/{parser.rs,env.rs,stream.rs}` change in production code. Tests go in those files plus new files under `crates/shinri-solver/tests/`. No change to core, solver, theory, the printer, the IR `Command` set, or the bench tool.
- **Numerals:** QF_LIA/ALL numeral sorts stay Int, and decimals stay Real. Indexed-operator numerals and sort indices (`expect_numeral_u32`) are unaffected.
- **`define-sort`:** nullary only. Parametric → `parametric define-sort unsupported`. Redefinition → `define-sort: sort already defined: <N>`. It returns `Ok(None)` (no IR command), exactly like `define-fun`.
- **`:named` collisions:** a let-bound name, a macro (`define-fun` or an earlier `:named`), or a declared function/constant → `named term: name already in use: <n>`.
- **No panics (threat model).** Every new error is a `Diagnostic`. Attribute-value skipping is iterative, and sort aliases store the resolved `SortId`.
- **Division by a zero constant** (`(/ x 0)`, `(/ x (- 0))`, `(/ x 0.0)`) → `Diagnostic` `division by a zero constant unsupported`. This is a pre-existing `recip of zero` panic, found while planning, in code this slice modifies (`apply_division`). It is fixed here under spec §3.4 ("each error is a `Diagnostic`, never a panic") and is listed in the report's *What changed versus the spec*.
- **Existing tests keep their assertions.** Any existing-test failure: stop and report; do not edit it.
- **Cross-track:** slice 63 (separate worktree) makes `(* (- k) x)` linear; this branch does not have it. Generators and tests here must not rely on `(* (- k) x)` being accepted. Negative coefficients are written `(- (* k x))`.
- No new dependency of any kind (pure-Rust mandate).
- Oracle tests run only with `--features oracle`; confirm a non-zero discovered count. nextest filters use `-E 'test(<name>)'` / `-E 'binary(<name>)'`.
- `cargo fmt --all` before every commit; `mise run lint` must be clean.
- **Worktree:** `/workspace/.claude/worktrees/slice64`, branch `slice64-parser-coverage`. Bench corpora, results and binaries live in the main checkout (`/workspace/bench/...`, `/workspace/target/slice64-*`), always passed by absolute path.
- **Host rule:** bench runs use `--jobs 3` under `taskset -c 12-23` and are detached with `setsid`. Builds and tests run under `taskset -c 0-11` while any bench is live. Slice 63's after runs may be live at the same time.
- PR to `main`, merge commit when CI is green, then delete the branch. **Ask the user before merging.** If slice 63 merges first, rebase onto `main` and re-run `mise run ci` and the oracle suite before merging (spec §6).

## Review Focus

1. **`set-logic` and the numeral live in different commands on the CLI path** (`StreamingParser` builds a fresh `Parser` per command). Expected: the Real-numeral mode persists, because it is stored in `Env`. Pinned in Task 1 (`set_logic_numeral_mode_persists_across_commands`, `stream.rs`).
2. **Division by a zero constant in any spelling** (`(/ x 0)`, `(/ x (- 0))`, `(/ 1 0)`, `(/ x 0.0)`). Expected: a `Diagnostic`, never a panic. On `main` `(/ x 0)` aborts the process (`recip of zero`). Pinned in Task 2 (`division_by_zero_constant_is_a_diagnostic_not_a_panic`).
3. **A hostile, deeply nested attribute value** (`(! a :x ((((…))))` 200,000 deep). Expected: skipped without stack overflow. Pinned in Task 3 (`deeply_nested_attribute_value_does_not_overflow`).
4. **A parse error inside `define-sort` or `(! …)` followed by more commands.** Expected: the next command still parses, through the existing stray-token tolerance plus `recover_to_command_end`. Pinned in Task 4 (`command_after_failed_define_sort_still_parses`) and Task 3 (`command_after_failed_named_still_parses`).
5. **A `define-sort` alias used across commands on the streaming path, and an alias of an alias.** Expected: both resolve to the same `SortId`. Pinned in Task 4 (`define_sort_alias_persists_across_commands`, `nullary_define_sort_aliases_resolve`).

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-parser/src/env.rs` | modify | `numerals_are_real` flag (persists across commands) |
| `crates/shinri-parser/src/parser.rs` | modify | `reals_only_arith`, `set-logic` arm, `parse_atom_numeral`, `unify_arith`, `apply_division`, `parse_annotated` + `skip_attribute_value` + `name_in_use`, `define-sort` arm + `BUILTIN_SORT_NAMES`; unit tests |
| `crates/shinri-parser/src/stream.rs` | modify (tests only) | cross-command persistence tests |
| `crates/shinri-solver/tests/parser_coverage_e2e.rs` | create | script-level reproducers |
| `crates/shinri-solver/tests/lra_numeral_oracle.rs` | create | z3 differential over LRA integer literals |
| `docs/superpowers/research/<date>-smtlib-2024-slice64-parser-coverage-report.md` | create | bench report |
| spec | append §11 | measured outcomes |

---

### Task 0: Worktree, base binary, Rodin corpus, base runs

**Files:** none in the repo. Artifacts go under `/workspace/target/slice64-base/` and `/workspace/target/slice64-rodin-corpus/`, and results under `/workspace/bench/results/slice64-base-*`.

**Interfaces:**
- Consumes: local `main` (with this plan committed), `/workspace/bench/corpus/{QF_FP,QF_LRA,QF_UFLRA,QF_UF}`, `/workspace/bench/results/slice56/results.jsonl`, `/workspace/target/slice59-sample-corpus/`.
- Produces: `/workspace/target/slice64-base/{shinri,shinri-bench,md5.txt,commit.txt,oracle-count.txt}`; the corpus `/workspace/target/slice64-rodin-corpus/`; base runs `slice64-base-{fp,lra,rodin,sample}`. Task 6 consumes all of them.

- [ ] **Step 1: Worktree and base binaries**

```bash
cd /workspace && git worktree add .claude/worktrees/slice64 -b slice64-parser-coverage main
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo build --release -p shinri-cli -p shinri-bench
mkdir -p /workspace/target/slice64-base
cp target/release/shinri target/release/shinri-bench /workspace/target/slice64-base/
md5sum /workspace/target/slice64-base/shinri | tee /workspace/target/slice64-base/md5.txt
git rev-parse --short HEAD | tee /workspace/target/slice64-base/commit.txt
/workspace/target/slice64-base/shinri /workspace/bench/corpus/QF_UFLRA/FFT/smtlib.624882.smt2 | grep -m1 error
```

Expected: `(error "sort error: Mismatch { expected: SortId(3), found: SortId(2) }")`.

- [ ] **Step 2: Rodin hard-link corpus**

```bash
cd /workspace && python3 - <<'EOF'
import json, os, pathlib
rows = [r for r in map(json.loads, open("bench/results/slice56/results.jsonl")) if "path" in r]
ps = sorted(r["path"] for r in rows if r["logic"] == "QF_UF" and r["verdict"] == "parse-error")
out = pathlib.Path("target/slice64-rodin-corpus")
for rel in ps:
    dst = out / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    if not dst.exists():
        os.link(pathlib.Path("bench/corpus") / rel, dst)
print(len(ps))
EOF
```

Expected: `34`.

- [ ] **Step 3: Launch the base runs, detached**

```bash
cd /workspace && B=/workspace/target/slice64-base && uptime | tee $B/uptime-start.txt
setsid nohup sh -c "
  taskset -c 12-23 $B/shinri-bench run --logics QF_FP --corpus /workspace/bench/corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $B/shinri --run-id slice64-base-fp > $B/run-fp.log 2>&1;
  taskset -c 12-23 $B/shinri-bench run --logics QF_LRA,QF_UFLRA --corpus /workspace/bench/corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $B/shinri --run-id slice64-base-lra > $B/run-lra.log 2>&1;
  taskset -c 12-23 $B/shinri-bench run --logics QF_UF --corpus /workspace/target/slice64-rodin-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $B/shinri --run-id slice64-base-rodin > $B/run-rodin.log 2>&1;
  taskset -c 12-23 $B/shinri-bench run --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
    --corpus /workspace/target/slice59-sample-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $B/shinri --run-id slice64-base-sample > $B/run-sample.log 2>&1;
  date -u +%FT%TZ > $B/finished.txt" > /dev/null 2>&1 &
```

Expected: QF_FP finishes fast, since nearly every row is an immediate parse error. LRA has about 180 timeouts at base. Continue with Task 1 without waiting.

- [ ] **Step 4: Base oracle count (in the background)**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle > /workspace/target/slice64-base/oracle.log 2>&1
grep -oE 'Starting [0-9]+ tests' /workspace/target/slice64-base/oracle.log | tee /workspace/target/slice64-base/oracle-count.txt
```

Expected: a non-zero count, all passing. Task 1 adds no `shinri-solver` tests, so running this alongside Task 1 does not change the count.

---

### Task 1: Logic-aware numerals

**Files:**
- Modify: `crates/shinri-parser/src/env.rs` (struct `Env` + two methods)
- Modify: `crates/shinri-parser/src/parser.rs`: the `set-logic` arm in `parse_command_body` (~1118), the non-decimal branch of `parse_atom_numeral` (~1618–1623), a new free fn `reals_only_arith`, and tests in `mod tests`
- Modify: `crates/shinri-parser/src/stream.rs` (tests only)

**Interfaces:**
- Produces: `Env::set_numerals_are_real(&mut self, on: bool)`, `Env::numerals_are_real(&self) -> bool`, `fn reals_only_arith(name: &str) -> bool` (private, in `parser.rs`).

- [ ] **Step 1: Write the failing tests**

Append to `mod tests` in `crates/shinri-parser/src/parser.rs` (it has `parse_one` and `parse_all_ok`):

```rust
    /// Slice 64 §3.1: which logics read integer literals as Real.
    #[test]
    fn reals_only_arith_classifies_logic_names() {
        for l in [
            "QF_LRA", "QF_UFLRA", "LRA", "UFLRA", "QF_NRA", "QF_UFNRA", "QF_RDL", "QF_FPLRA",
            "QF_ABVFPLRA",
        ] {
            assert!(reals_only_arith(l), "{l} should be Reals-only");
        }
        for l in [
            "QF_LIRA", "AUFLIRA", "QF_NIRA", "QF_LIA", "QF_UFLIA", "ALL", "QF_BV", "QF_FP", "QF_S",
            "QF_SLIA", "QF_IDL",
        ] {
            assert!(!reals_only_arith(l), "{l} should not be Reals-only");
        }
    }

    #[test]
    fn numeral_sort_follows_env_flag() {
        let (ctx, t) = parse_one("1", |_, p| p.env.set_numerals_are_real(true));
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        let (ctx, t) = parse_one("(- 1)", |_, p| p.env.set_numerals_are_real(true));
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        let (ctx, t) = parse_one("1", |_, _| {});
        assert_eq!(ctx.sort_of(t), ctx.int_sort());
    }

    /// The FFT reproducer (QF_UFLRA/FFT/smtlib.624882) plus let-bound and
    /// comparison shapes all parse once QF_UFLRA numerals are Real.
    #[test]
    fn reals_logic_parses_int_literals_in_real_contexts() {
        let src = "(set-logic QF_UFLRA)(declare-fun f3 (Real) Real)(declare-fun f5 () Real)\
                   (assert (= (f3 f5) (- 1)))\
                   (assert (let ((?v (- 1))) (= f5 ?v)))\
                   (assert (< f5 1))";
        let (_ctx, cmds) = parse_all_ok(src);
        assert_eq!(cmds.len(), 6);
    }

    /// Int logics keep Int literals: `(= n 1)` with `n : Int` only parses
    /// if `1` is Int.
    #[test]
    fn int_and_all_logics_keep_int_numerals() {
        for logic in ["QF_LIA", "ALL"] {
            let src = format!("(set-logic {logic})(declare-fun n () Int)(assert (= n 1))");
            let (_ctx, cmds) = parse_all_ok(&src);
            assert_eq!(cmds.len(), 3, "{logic}");
        }
    }
```

Append to the tests module of `crates/shinri-parser/src/stream.rs` (it has `is_cmd`):

```rust
    /// Slice 64: `set-logic` and a later numeral are separate commands on
    /// the streaming path; the Real-numeral mode lives in the persisted env.
    #[test]
    fn set_logic_numeral_mode_persists_across_commands() {
        let mut ctx = Context::new();
        let mut sp = StreamingParser::new();
        sp.push_str("(set-logic QF_LRA)");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| matches!(
            c,
            Command::SetLogic(_)
        )));
        sp.push_str("(declare-fun x () Real)");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| matches!(
            c,
            Command::DeclareFun { .. }
        )));
        sp.push_str("(assert (let ((?v (- 1))) (= x ?v)))");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| matches!(
            c,
            Command::Assert(_)
        )));
    }
```

- [ ] **Step 2: Run them and verify they fail**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-parser -E 'test(reals_only_arith_classifies_logic_names) | test(numeral_sort_follows_env_flag) | test(reals_logic_parses_int_literals_in_real_contexts) | test(int_and_all_logics_keep_int_numerals) | test(set_logic_numeral_mode_persists_across_commands)'
```

Expected: a compile error (`reals_only_arith` and `set_numerals_are_real` don't exist). After Step 3 adds only the `Env` methods and a stub `fn reals_only_arith(_: &str) -> bool { false }`, re-running gives:
- `reals_logic_parses_int_literals_in_real_contexts` FAILS (`unexpected parse error … Mismatch`);
- `set_logic_numeral_mode_persists_across_commands` FAILS;
- `reals_only_arith_classifies_logic_names` FAILS;
- `int_and_all_logics_keep_int_numerals` PASSES (it's a guard).

Record this RED output in the report.

- [ ] **Step 3: Implement**

In `crates/shinri-parser/src/env.rs`, add a field to `Env` (after `let_frames`) and two methods:

```rust
    /// Slice 64: set by `set-logic`. True for Reals-only logics, where an
    /// integer literal denotes a real (SMT-LIB 2.6 Reals theory). Lives here
    /// because `Env` is the state that persists across commands, on both the
    /// batch and the streaming path.
    numerals_are_real: bool,
```

```rust
    pub fn set_numerals_are_real(&mut self, on: bool) {
        self.numerals_are_real = on;
    }
    pub fn numerals_are_real(&self) -> bool {
        self.numerals_are_real
    }
```

In `crates/shinri-parser/src/parser.rs`, add a free function next to `token_value_text`:

```rust
/// Slice 64 §3.1: true iff logic `name`'s arithmetic is Reals-only, i.e. it
/// ends in `LRA`, `NRA` or `RDL` (`QF_LRA`, `QF_UFLRA`, `QF_RDL`,
/// `QF_FPLRA`, …). Mixed logics end in `IRA` (`QF_LIRA`, `AUFLIRA`) and so
/// never match; `ALL` and logics without arithmetic don't either.
fn reals_only_arith(name: &str) -> bool {
    ["LRA", "NRA", "RDL"].iter().any(|suf| name.ends_with(suf))
}
```

(Spec §3.1's "the character before that suffix is not `I`" is implied: `…LIRA`/`…NIRA` end in `IRA`, never in `LRA`/`NRA`. The test pins both lists.)

The `set-logic` arm in `parse_command_body` becomes:

```rust
            "set-logic" => {
                let (l, _) = self.expect_symbol()?;
                self.env.set_numerals_are_real(reals_only_arith(&l));
                Command::SetLogic(l)
            }
```

The non-decimal branch of `parse_atom_numeral` becomes:

```rust
        } else {
            let n = Integer::from_str_radix(text, 10)
                .map_err(|_| Diagnostic::new(sp, "bad numeral"))?;
            let val = Rational::from_int(n);
            // Slice 64: in a Reals-only logic a numeral denotes a real.
            let sort = if self.env.numerals_are_real() {
                ctx.real_sort()
            } else {
                ctx.int_sort()
            };
            Ok(ctx.mk_numeral(val, sort))
        }
```

Also update the doc comment above `parse_atom_numeral` (~1594), which says "integer literals default to Int": append "; Real under a Reals-only `set-logic` (slice 64)".

- [ ] **Step 4: Run the new tests and the parser suite**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-parser -p shinri-frontend
```

Expected: everything passes, including the 5 new tests. If an existing test fails, stop and report.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-parser/src/env.rs crates/shinri-parser/src/parser.rs crates/shinri-parser/src/stream.rs
git commit -m "feat(parser): slice64 - integer literals are Real under Reals-only logics"
```

---

### Task 2: Constant `(- k)` coercion and safe division

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs`: `unify_arith` (~419–434), `apply_division` (~806–846), tests in `mod tests`

**Interfaces:**
- Consumes: `Context::const_real_value(&self, TermId) -> Option<Rational>` (exists on `main`: numeral or unary `(- c)` of one), `Rational::is_zero(&self) -> bool`.
- Produces: no new names.

- [ ] **Step 1: Write the failing tests**

Append to `mod tests` in `parser.rs`:

```rust
    fn bind_real_x(ctx: &mut Context, p: &mut Parser) {
        let r = ctx.real_sort();
        let sym = ctx.declare_fun("x", &[], r);
        p.bind_fun("x", sym);
    }

    /// Slice 64 §3.1 (ALL/LIRA path): `(- 1)` next to a Real operand is
    /// re-minted as a Real constant.
    #[test]
    fn coerces_negated_int_literal_in_real_context() {
        let (ctx, t) = parse_one("(+ x (- 1))", bind_real_x);
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
    }

    /// `(/ x (- 2))` folds to `(* -1/2 x)` instead of "non-linear division".
    #[test]
    fn division_by_negated_constant_folds() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let (ctx, t) = parse_one("(/ x (- 2))", bind_real_x);
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        match ctx.term_node(t) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Mul),
                args,
                ..
            } => {
                let kids = ctx.children(*args);
                assert_eq!(
                    ctx.numeral_value(kids[0]).cloned(),
                    Some(Rational::new((-1i128).into(), 2i128.into()))
                );
            }
            other => panic!("expected Mul, got {other:?}"),
        }
    }

    /// Threat model: a zero constant divisor is a Diagnostic, never a panic
    /// (`main` aborts with "recip of zero").
    #[test]
    fn division_by_zero_constant_is_a_diagnostic_not_a_panic() {
        for src in ["(/ x 0)", "(/ x (- 0))", "(/ 1 0)", "(/ x 0.0)"] {
            let mut ctx = Context::new();
            let mut p = Parser::new(src);
            bind_real_x(&mut ctx, &mut p);
            let err = p.parse_term(&mut ctx).expect_err(src);
            assert!(
                err.message.contains("division by a zero constant"),
                "{src}: {err:?}"
            );
        }
    }
```

If `Rational` is not already imported in the tests module, use `shinri_num::Rational`, the same path the module's existing division tests use.

- [ ] **Step 2: Run them and verify they fail**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-parser -E 'test(coerces_negated_int_literal_in_real_context) | test(division_by_negated_constant_folds) | test(division_by_zero_constant_is_a_diagnostic_not_a_panic)'
```

Expected: `coerces_negated…` FAILS (sort error), `division_by_negated…` FAILS (`non-linear division`), and `division_by_zero…` FAILS by panicking with `recip of zero`.

- [ ] **Step 3: Implement**

In `unify_arith`, replace the numeral check inside the loop:

```rust
                if ctx.sort_of(*a) == int {
                    // A numeral or `(- c)` of one (slice 64): re-mint as Real.
                    if let Some(v) = ctx.const_real_value(*a) {
                        *a = ctx.mk_numeral(v, real);
                    }
                }
```

In `apply_division`, the fold loop becomes (keep the existing `(_, None)` arm and its message unchanged):

```rust
        for &divisor in &args[1..] {
            // Constants are numerals or `(- c)` of one (slice 64).
            let dv = ctx.const_real_value(divisor);
            match (ctx.const_real_value(acc), dv) {
                (_, Some(d)) if d.is_zero() => {
                    // Threat model: never panic on input (`recip` asserts).
                    return Err(Diagnostic::new(
                        sp,
                        "division by a zero constant unsupported",
                    ));
                }
                (Some(n), Some(d)) => {
                    // constant / constant -> fold
                    let rs = ctx.real_sort();
                    acc = ctx.mk_numeral(n * d.recip(), rs);
                }
                (None, Some(d)) => {
                    // x / const -> (* recip(d) x)
                    let rs = ctx.real_sort();
                    let recip = ctx.mk_numeral(d.recip(), rs);
                    let mut operands = vec![recip, acc];
                    Self::unify_arith(ctx, &mut operands);
                    acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Mul), &operands, &sp)?;
                }
```

- [ ] **Step 4: Run the parser suite**

```bash
taskset -c 0-11 cargo nextest run -p shinri-parser -p shinri-frontend
```

Expected: everything passes.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-parser/src/parser.rs
git commit -m "fix(parser): slice64 - (- k) constants coerce and divide; zero divisor is a diagnostic"
```

---

### Task 3: Named terms `(! t attr*)`

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs`: the head `match` in `parse_compound` (~671), new methods `parse_annotated`, `skip_attribute_value` and `name_in_use`, tests

**Interfaces:**
- Consumes: `Env::{lookup_let, lookup_macro, lookup_fun, add_macro}`, `Token::Keyword(String)` (text includes the leading `:`), and `Parser::{bump, peek, expect_symbol}`.
- Produces: `fn parse_annotated(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic>`, `fn skip_attribute_value(&mut self)`, `fn name_in_use(&self, name: &str) -> bool`.

- [ ] **Step 1: Write the failing tests**

Append to `mod tests` in `parser.rs`:

```rust
    fn first_error(src: &str) -> Diagnostic {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        let results: Vec<_> = std::iter::from_fn(|| p.next_command(&mut ctx)).collect();
        results
            .into_iter()
            .find_map(|r| r.err())
            .unwrap_or_else(|| panic!("no error for {src}"))
    }

    fn assert_terms(cmds: &[Command]) -> Vec<TermId> {
        cmds.iter()
            .filter_map(|c| match c {
                Command::Assert(t) => Some(*t),
                _ => None,
            })
            .collect()
    }

    /// Slice 64 §3.2: `!` is transparent and `:named h` makes `h` an alias.
    #[test]
    fn named_annotation_is_transparent_and_binds_name() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let src = "(declare-fun a () Bool)(declare-fun b () Bool)\
                   (assert (! (= a b) :named h))(assert (not h))(assert (= a b))";
        let (ctx, cmds) = parse_all_ok(src);
        let ts = assert_terms(&cmds);
        assert_eq!(ts[0], ts[2], "annotation must not change the term");
        match ctx.term_node(ts[1]) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Not),
                args,
                ..
            } => assert_eq!(ctx.children(*args)[0], ts[0]),
            other => panic!("expected (not h), got {other:?}"),
        }
    }

    #[test]
    fn named_annotation_rejects_names_in_use() {
        for src in [
            "(declare-fun a () Bool)(assert (! a :named h))(assert (! a :named h))",
            "(declare-fun a () Bool)(assert (! a :named a))",
            "(declare-fun a () Bool)(define-fun k () Bool a)(assert (! a :named k))",
            "(declare-fun a () Bool)(assert (let ((h a)) (! a :named h)))",
        ] {
            let err = first_error(src);
            assert!(err.message.contains("name already in use"), "{src}: {err:?}");
        }
    }

    #[test]
    fn unknown_attributes_are_skipped_including_nested_values() {
        let src = "(declare-fun a () Bool)\
                   (assert (! a :pattern ((f (g x)) y) :weight 3 :flag :named h2))(assert h2)";
        let (_ctx, cmds) = parse_all_ok(src);
        assert_eq!(cmds.len(), 3);
    }

    /// Threat model: attribute-value skipping is iterative.
    #[test]
    fn deeply_nested_attribute_value_does_not_overflow() {
        let depth = 200_000;
        let src = format!(
            "(declare-fun a () Bool)(assert (! a :x {}{}))",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let (_ctx, cmds) = parse_all_ok(&src);
        assert_eq!(cmds.len(), 2);
    }

    #[test]
    fn command_after_failed_named_still_parses() {
        let src = "(declare-fun a () Bool)(assert (! a :named a))(declare-fun b () Bool)";
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        assert!(matches!(p.next_command(&mut ctx), Some(Ok(Command::DeclareFun { .. }))));
        assert!(matches!(p.next_command(&mut ctx), Some(Err(_))));
        assert!(matches!(p.next_command(&mut ctx), Some(Ok(Command::DeclareFun { .. }))));
    }
```

- [ ] **Step 2: Run them and verify they fail**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-parser -E 'test(named_annotation) | test(unknown_attributes_are_skipped) | test(deeply_nested_attribute_value) | test(command_after_failed_named)'
```

Expected:
- `named_annotation_is_transparent…`, `unknown_attributes…` and `deeply_nested…` FAIL with `unknown operator !`.
- `named_annotation_rejects_names_in_use` FAILS: the error it finds is `unknown operator !`, not "name already in use".
- `command_after_failed_named_still_parses` PASSES already (its middle command errors either way). It is a guard.

- [ ] **Step 3: Implement**

In `parse_compound`'s `match head.as_str()`, add an arm before `"let"`:

```rust
            "!" => return self.parse_annotated(ctx),
```

Add these methods to `impl Parser` (next to `parse_let`):

```rust
    /// `(! t attr*)` (slice 64 §3.2), with `(` and `!` already consumed. The
    /// value is `t`; an annotation never changes a term's meaning. `:named n`
    /// binds `n` as a nullary alias of `t` (SMT-LIB 2.6 §3.6.5); any other
    /// attribute is skipped.
    fn parse_annotated(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic> {
        let t = self.parse_term(ctx)?;
        loop {
            match self.bump() {
                Some((Ok(Token::RParen), _)) => return Ok(t),
                Some((Ok(Token::Keyword(k)), _)) => {
                    if k == ":named" {
                        let (name, nsp) = self.expect_symbol()?;
                        if self.name_in_use(&name) {
                            return Err(Diagnostic::new(
                                nsp,
                                format!("named term: name already in use: {name}"),
                            ));
                        }
                        self.env.add_macro(&name, Vec::new(), t);
                    } else {
                        self.skip_attribute_value();
                    }
                }
                Some((_, sp)) => {
                    return Err(Diagnostic::new(
                        sp,
                        "expected an attribute keyword or ')' in (! ...)",
                    ))
                }
                None => {
                    return Err(Diagnostic::new(
                        self.eof..self.eof,
                        "unexpected EOF in (! ...)",
                    ))
                }
            }
        }
    }

    /// Consume one attribute value if present: nothing when the next token is
    /// `)` or a keyword, else one s-expression. Iterative (a depth counter),
    /// so hostile nesting cannot overflow the stack (threat model).
    fn skip_attribute_value(&mut self) {
        match self.peek() {
            None | Some((Ok(Token::RParen), _)) | Some((Ok(Token::Keyword(_)), _)) => {}
            Some((Ok(Token::LParen), _)) => {
                self.bump();
                let mut depth = 1usize;
                while depth > 0 {
                    match self.bump() {
                        None => break,
                        Some((Ok(Token::LParen), _)) => depth += 1,
                        Some((Ok(Token::RParen), _)) => depth -= 1,
                        _ => {}
                    }
                }
            }
            Some(_) => {
                self.bump();
            }
        }
    }

    /// A `:named` name collides with a let-bound name, a macro (`define-fun`
    /// or an earlier `:named`), or a declared function/constant.
    fn name_in_use(&self, name: &str) -> bool {
        self.env.lookup_let(name).is_some()
            || self.env.lookup_macro(name).is_some()
            || self.env.lookup_fun(name).is_some()
    }
```

- [ ] **Step 4: Run the parser suite**

```bash
taskset -c 0-11 cargo nextest run -p shinri-parser -p shinri-frontend
```

Expected: everything passes, and `deeply_nested…` completes in well under a second.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(parser): slice64 - (! t attr*) annotations with :named aliases"
```

---

### Task 4: Nullary `define-sort`

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs`: a new `define-sort` arm in `parse_command_body` (next to `define-fun`, ~1170), a new const `BUILTIN_SORT_NAMES`, tests
- Modify: `crates/shinri-parser/src/stream.rs` (tests only)

**Interfaces:**
- Consumes: `Env::{add_sort, lookup_sort}`, `Parser::parse_sort`.
- Produces: `const BUILTIN_SORT_NAMES: &[&str]`.

- [ ] **Step 1: Write the failing tests**

Append to `mod tests` in `parser.rs` (it uses `first_error` from Task 3):

```rust
    /// Slice 64 §3.3: aliases resolve to the stored SortId, including an
    /// alias of an alias.
    #[test]
    fn nullary_define_sort_aliases_resolve() {
        let src = "(define-sort FPN () (_ FloatingPoint 11 53))(define-sort F2 () FPN)\
                   (declare-fun x () FPN)(declare-fun y () F2)";
        let (mut ctx, cmds) = parse_all_ok(src);
        let fpn = ctx.fp_sort(11, 53);
        let sorts: Vec<_> = cmds
            .iter()
            .filter_map(|c| match c {
                Command::DeclareFun { result, .. } => Some(*result),
                _ => None,
            })
            .collect();
        assert_eq!(sorts, vec![fpn, fpn]);
        assert_eq!(cmds.len(), 2, "define-sort emits no IR command");
    }

    #[test]
    fn define_sort_rejects_parameters_and_redefinition() {
        for (src, needle) in [
            ("(define-sort Arr (X) (Array X X))", "parametric define-sort unsupported"),
            ("(define-sort Real () Int)", "sort already defined: Real"),
            ("(define-sort S () Int)(define-sort S () Bool)", "sort already defined: S"),
            ("(declare-sort U 0)(define-sort U () Int)", "sort already defined: U"),
        ] {
            let err = first_error(src);
            assert!(err.message.contains(needle), "{src}: {err:?}");
        }
    }

    #[test]
    fn command_after_failed_define_sort_still_parses() {
        let src = "(define-sort Arr (X) (Array X X))(declare-fun a () Bool)";
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        assert!(matches!(p.next_command(&mut ctx), Some(Err(_))));
        assert!(matches!(p.next_command(&mut ctx), Some(Ok(Command::DeclareFun { .. }))));
    }
```

Append to the tests module of `stream.rs`:

```rust
    /// Slice 64: a define-sort alias persists into later commands.
    #[test]
    fn define_sort_alias_persists_across_commands() {
        let mut ctx = Context::new();
        let mut sp = StreamingParser::new();
        sp.push_str("(define-sort FPN () (_ FloatingPoint 11 53))(declare-fun x () FPN)");
        let fpn = ctx.fp_sort(11, 53);
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| matches!(
            c,
            Command::DeclareFun { result, .. } if *result == fpn
        )));
    }
```

- [ ] **Step 2: Run them and verify they fail**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-parser -E 'test(define_sort) | test(nullary_define_sort)'
```

Expected:
- `nullary_define_sort_aliases_resolve` and `define_sort_alias_persists_across_commands` FAIL (`unsupported command: define-sort`).
- `define_sort_rejects_parameters_and_redefinition` FAILS: the message is `unsupported command`, not the expected needle.
- `command_after_failed_define_sort_still_parses` PASSES already. It is a guard.

- [ ] **Step 3: Implement**

Add near `token_value_text`:

```rust
/// Sort names `parse_sort` resolves before the environment; `define-sort`
/// may not shadow them (slice 64 §3.3). Keep in sync with `parse_sort`.
const BUILTIN_SORT_NAMES: &[&str] = &[
    "Bool",
    "Int",
    "Real",
    "String",
    "RegLan",
    "Float16",
    "Float32",
    "Float64",
    "Float128",
    "RoundingMode",
];
```

Add an arm to `parse_command_body`, directly after the `"define-fun"` arm:

```rust
            "define-sort" => {
                // Slice 64 §3.3: nullary aliases only. The alias stores the
                // resolved SortId, so it is never re-expanded.
                let (name, nsp) = self.expect_symbol()?;
                self.expect_token(&Token::LParen)?;
                if !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                    // Consume the parameter list (iteratively) first, so the
                    // caller's `recover_to_command_end` resumes at this
                    // command's own ')' instead of treating the sort body as
                    // a stray next command.
                    let mut depth = 1usize;
                    while depth > 0 {
                        match self.bump() {
                            None => break,
                            Some((Ok(Token::LParen), _)) => depth += 1,
                            Some((Ok(Token::RParen), _)) => depth -= 1,
                            _ => {}
                        }
                    }
                    return Err(Diagnostic::new(hsp, "parametric define-sort unsupported"));
                }
                self.bump(); // ')' of the empty parameter list
                if BUILTIN_SORT_NAMES.contains(&name.as_str())
                    || self.env.lookup_sort(&name).is_some()
                {
                    return Err(Diagnostic::new(
                        nsp,
                        format!("define-sort: sort already defined: {name}"),
                    ));
                }
                let s = self.parse_sort(ctx)?;
                self.expect_token(&Token::RParen)?; // close (define-sort …)
                self.env.add_sort(&name, s);
                return Ok(None); // no IR command emitted; caller loops
            }
```

Update the `Ok(None)` doc comments on `next_command` (~1072) and `parse_command_body` (~1111): "for `define-fun`" becomes "for `define-fun` and `define-sort`". Also change the loop comment `Ok(None) => continue, // define-fun: …` (~1093) to `// define-fun / define-sort: …`.

- [ ] **Step 4: Run the parser suite**

```bash
taskset -c 0-11 cargo nextest run -p shinri-parser -p shinri-frontend
```

Expected: everything passes.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-parser/src/parser.rs crates/shinri-parser/src/stream.rs
git commit -m "feat(parser): slice64 - nullary define-sort aliases"
```

---

### Task 5: E2E reproducers and LRA oracle

**Files:**
- Create: `crates/shinri-solver/tests/parser_coverage_e2e.rs`
- Create: `crates/shinri-solver/tests/lra_numeral_oracle.rs`

**Interfaces:**
- Consumes: Tasks 1–4; `shinri_parser::Parser::{new, next_command}`, `shinri_solver::{Solver, CommandResponse, SolveOutcome}`, `easy_smt`, feature `oracle`.
- Produces: tests only.

- [ ] **Step 1: Write the e2e tests**

Create `crates/shinri-solver/tests/parser_coverage_e2e.rs`:

```rust
//! Slice 64: script-level reproducers for the parser-coverage gaps
//! (Reals-logic numerals, `(! t :named n)`, nullary `define-sort`).

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Run an SMT-LIB script; the outcome of its last `check-sat`. Any parse
/// error fails the test: these scripts must parse completely.
fn script_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = None;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.unwrap_or_else(|e| panic!("parse error: {e:?}"));
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = Some(SolveOutcome::Sat),
            CommandResponse::Unsat => outcome = Some(SolveOutcome::Unsat),
            CommandResponse::Unknown => outcome = Some(SolveOutcome::Unknown),
            _ => {}
        }
    }
    outcome.expect("script has a check-sat")
}

/// QF_UFLRA/FFT/smtlib.624882 (`:status unsat`), set-info lines dropped.
#[test]
fn slice64_fft_reproducer_unsat() {
    let src = "(set-logic QF_UFLRA)(declare-sort S1 0)\
               (declare-fun f1 () S1)(declare-fun f2 () S1)(declare-fun f3 (Real) Real)\
               (declare-fun f4 () Real)(declare-fun f5 () Real)\
               (assert (not (= f1 f2)))(assert (not (not (= (f3 f4) 1.0))))\
               (assert (= f4 f5))(assert (= f4 f5))(assert (= (f3 f5) (- 1)))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Unsat);
}

/// Let-bound integer literal in QF_LRA: x = -1 pinned by a let.
#[test]
fn slice64_lra_let_bound_literal() {
    let base = "(set-logic QF_LRA)(declare-fun x () Real)\
                (assert (let ((?k (- 1))) (and (<= x ?k) (>= x ?k))))";
    assert_eq!(
        script_outcome(&format!("{base}(assert (> x (- 2)))(check-sat)")),
        SolveOutcome::Sat
    );
    assert_eq!(
        script_outcome(&format!("{base}(assert (> x 0))(check-sat)")),
        SolveOutcome::Unsat
    );
}

/// Rodin shape (QF_UF/20170829-Rodin): a named hypothesis and its use.
#[test]
fn slice64_rodin_named_hypothesis() {
    let src = "(set-logic QF_UF)(declare-fun a () Bool)(declare-fun b () Bool)\
               (assert (! (= a b) :named hyp1))(assert (not hyp1))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Unsat);
}

/// QF_FP/wintersteiger/abs/abs-has-solution-8522 (`:status sat`) and its
/// `abs-has-no-other-solution-8522` sibling (`:status unsat`).
#[test]
fn slice64_wintersteiger_define_sort() {
    let base = "(set-logic QF_FP)(define-sort FPN () (_ FloatingPoint 11 53))\
                (declare-fun x () FPN)(declare-fun r () FPN)\
                (assert (= x (_ +oo 11 53)))(assert (= r (_ +oo 11 53)))";
    assert_eq!(
        script_outcome(&format!("{base}(assert (= (fp.abs x) r))(check-sat)")),
        SolveOutcome::Sat
    );
    assert_eq!(
        script_outcome(&format!("{base}(assert (not (= (fp.abs x) r)))(check-sat)")),
        SolveOutcome::Unsat
    );
}
```

- [ ] **Step 2: Run the e2e tests**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(parser_coverage_e2e)'
```

Expected: `Starting 4 tests`, and all pass. (Expected outcomes were checked while planning: z3 and the corpus `:status` agree with each.) If any test returns `Unknown` or panics with a parse error, stop and report the script.

- [ ] **Step 3: Write the oracle**

Create `crates/shinri-solver/tests/lra_numeral_oracle.rs`:

```rust
//! Differential oracle: shinri vs z3 on QF_LRA scripts whose constants are
//! integer literals — bare, `(- k)`, and let-bound — in Real contexts
//! (slice 64). Requires z3 on PATH.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(lra_numeral_oracle)'
//!
//! Negative coefficients are written `(- (* k v))`, never `(* (- k) v)`:
//! the latter is linear only after slice 63, a separate branch.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG (same convention as tests/nary_arith_oracle.rs).
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
const VARS: &[&str] = &["a", "b", "c"];

fn shinri_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.unwrap_or_else(|e| panic!("parse error {e:?} in:\n{src}"));
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

fn z3_outcome_lra(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_LRA").expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-const ") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

/// An integer literal; negatives as `(- k)`.
fn int_lit(k: i64) -> String {
    if k < 0 {
        format!("(- {})", -k)
    } else {
        format!("{k}")
    }
}

/// `k·v` with k in -3..=3 \ {0}: `(* k v)`, or `(- (* |k| v))` when negative.
fn gen_product(rng: &mut Lcg) -> String {
    let v = VARS[rng.below(VARS.len() as u64) as usize];
    let mut k = rng.below(6) as i64 - 3;
    if k >= 0 {
        k += 1;
    }
    if k < 0 {
        format!("(- (* {} {v}))", -k)
    } else {
        format!("(* {k} {v})")
    }
}

fn gen_lhs(rng: &mut Lcg) -> String {
    let n = 1 + rng.below(3) as usize;
    let ps: Vec<String> = (0..n).map(|_| gen_product(rng)).collect();
    if n == 1 {
        ps[0].clone()
    } else {
        format!("(+ {})", ps.join(" "))
    }
}

/// An atom whose constant is a bare literal, `(- k)`, or let-bound.
fn gen_atom(rng: &mut Lcg) -> String {
    let op = ["<=", ">=", "=", "<"][rng.below(4) as usize];
    let lhs = gen_lhs(rng);
    let k = int_lit(rng.below(11) as i64 - 5);
    if rng.below(3) == 0 {
        format!("(let ((?k {k})) ({op} {lhs} ?k))")
    } else {
        format!("({op} {lhs} {k})")
    }
}

fn gen_script(rng: &mut Lcg) -> String {
    let mut s = String::from("(set-logic QF_LRA)\n");
    for v in VARS {
        s.push_str(&format!("(declare-const {v} Real)\n"));
    }
    for v in VARS {
        s.push_str(&format!("(assert (and (<= (- 3) {v}) (<= {v} 3)))\n"));
    }
    for _ in 0..2 + rng.below(4) {
        let a = match rng.below(4) {
            0 => format!("(not {})", gen_atom(rng)),
            1 => format!("(or {} {})", gen_atom(rng), gen_atom(rng)),
            _ => gen_atom(rng),
        };
        s.push_str(&format!("(assert {a})\n"));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_lra_integer_literals() {
    let mut rng = Lcg(0x51CE_0064);
    let (mut n_sat, mut n_unsat, mut n_z3_checked) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng);
        let ours = shinri_outcome(&src);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {
                panic!("unknown on a bounded QF_LRA script (iter {iter}):\n{src}")
            }
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        match (ours, z3_outcome_lra(&mut ctx, &src)) {
            (SolveOutcome::Sat, easy_smt::Response::Sat)
            | (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (o, t) => panic!(
                "QF_LRA integer-literal DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_lra_integer_literals: sat={n_sat} unsat={n_unsat} z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat)"
    );
    assert_eq!(n_z3_checked, N_ITERS, "every iteration must be z3-confirmed");
}
```

(A z3 `unknown` on a bounded QF_LRA script falls into the panic arm: here `Unknown` is not tolerated from either solver.)

- [ ] **Step 4: Run the oracle**

```bash
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle -E 'binary(lra_numeral_oracle)' --no-capture
```

Expected: `Starting 1 test`, PASS, and a printed line with non-zero `sat` and `unsat` and `z3_checked=200`. A panic on `unknown`, a parse error or a disagreement is a finding: report the script. Don't change the generator to dodge it.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-solver/tests/parser_coverage_e2e.rs crates/shinri-solver/tests/lra_numeral_oracle.rs
git commit -m "test(solver): slice64 - e2e reproducers and LRA integer-literal oracle"
```

---

### Task 6: Gates, after runs, report, PR

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice64-parser-coverage-report.md` (date = the day the after runs finish)
- Modify: the spec (append `## 11. Measured outcomes`)

**Interfaces:**
- Consumes: branch HEAD after Tasks 1–5; Task 0's base artifacts and runs.

- [ ] **Step 1: Gates (criterion 6)**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 mise run ci > /workspace/target/slice64-ci.log 2>&1; echo "ci exit=$?"; tail -3 /workspace/target/slice64-ci.log
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle > /workspace/target/slice64-oracle.log 2>&1; echo "oracle exit=$?"
grep -E 'Starting|Summary' /workspace/target/slice64-oracle.log; cat /workspace/target/slice64-base/oracle-count.txt
(cd crates/shinri-parser && taskset -c 0-11 mise x rust@nightly -- cargo fuzz run parse_script -- -max_total_time=600) > /workspace/target/slice64-fuzz.log 2>&1; echo "fuzz exit=$?"; tail -5 /workspace/target/slice64-fuzz.log
```

Expected: `ci exit=0`; `oracle exit=0` with `Starting N tests`, where N = base + 5 (the 4 non-feature-gated e2e tests plus the 1 oracle); `fuzz exit=0` with no `crash-` artifact. Record all of this in `/workspace/target/slice64-gates.txt`. If the fuzzer finds a crash, stop and report it with the artifact path.

- [ ] **Step 2: Wait for the base runs**

Wait for `/workspace/target/slice64-base/finished.txt` with a background until-loop, not a foreground sleep. Then:

```bash
wc -l /workspace/bench/results/slice64-base-{fp,lra,rodin,sample}/results.jsonl
```

Expected: 40,408 / 3,038 / 35 / 2,001 lines (rows + fixture).

- [ ] **Step 3: Build and launch the after runs, detached**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo build --release -p shinri-cli -p shinri-bench
A=/workspace/target/slice64-after && mkdir -p $A
cp target/release/shinri target/release/shinri-bench $A/
md5sum $A/shinri | tee $A/md5.txt; git rev-parse --short HEAD | tee $A/commit.txt
$A/shinri /workspace/bench/corpus/QF_UFLRA/FFT/smtlib.624882.smt2 | grep -E '^(sat|unsat|unknown)$|error'
uptime | tee $A/uptime-start.txt
cd /workspace && setsid nohup sh -c "
  taskset -c 12-23 $A/shinri-bench run --logics QF_FP --corpus /workspace/bench/corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $A/shinri --run-id slice64-fp > $A/run-fp.log 2>&1;
  taskset -c 12-23 $A/shinri-bench run --logics QF_LRA,QF_UFLRA --corpus /workspace/bench/corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $A/shinri --run-id slice64-lra > $A/run-lra.log 2>&1;
  taskset -c 12-23 $A/shinri-bench run --logics QF_UF --corpus /workspace/target/slice64-rodin-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $A/shinri --run-id slice64-rodin > $A/run-rodin.log 2>&1;
  taskset -c 12-23 $A/shinri-bench run --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
    --corpus /workspace/target/slice59-sample-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $A/shinri --run-id slice64-sample > $A/run-sample.log 2>&1;
  date -u +%FT%TZ > $A/finished.txt" > /dev/null 2>&1 &
```

Expected: the FFT file prints `unsat` and no `error`. QF_FP is the long leg: its 40,407 rows now reach the FP engine (on the order of 4–6 h at `--jobs 3`). Wait for `$A/finished.txt` with a background until-loop.

- [ ] **Step 4: Join base and after (criteria 1–4, 7)**

```bash
cd /workspace && for id in slice64-base-fp slice64-fp slice64-base-lra slice64-lra slice64-base-rodin slice64-rodin slice64-base-sample slice64-sample; do
  (cd /workspace/.claude/worktrees/slice64 && cargo run -q --release -p shinri-bench -- report /workspace/bench/results/$id); done
python3 - <<'EOF' | tee /workspace/target/slice64-after/join.txt
import json, collections
def load(p):
    return {r["path"]: r for r in map(json.loads, open(p)) if "path" in r}
fam = lambda p: "/".join(p.split("/")[:2])
changed = []
for base, after in (("slice64-base-fp", "slice64-fp"), ("slice64-base-lra", "slice64-lra"),
                    ("slice64-base-rodin", "slice64-rodin"), ("slice64-base-sample", "slice64-sample")):
    a = load(f"bench/results/{base}/results.jsonl"); b = load(f"bench/results/{after}/results.jsonl")
    assert a.keys() == b.keys(), f"row sets differ: {base} vs {after}"
    c = collections.Counter()
    for p in sorted(a):
        va, vb = a[p]["verdict"], b[p]["verdict"]
        if va != vb:
            c[(a[p]["logic"], va, vb)] += 1
            changed.append((p, a[p]["logic"], va, vb, after))
    pe = lambda rows: sum(r["verdict"] == "parse-error" for r in rows.values())
    print(f"== {base} -> {after}: {sum(c.values())} changed; parse-error {pe(a)} -> {pe(b)}; wrong after: {sum(r['verdict'] == 'wrong' for r in b.values())}")
    for k, n in sorted(c.items()):
        print("  ", *k, n)
    print("  destinations of rows leaving parse-error:", dict(collections.Counter(
        b[p]["verdict"] for p in a if a[p]["verdict"] == "parse-error" and b[p]["verdict"] != "parse-error")))
    print("  by family:", collections.Counter(
        (fam(p), b[p]["verdict"]) for p in a if a[p]["verdict"] == "parse-error" and b[p]["verdict"] != "parse-error").most_common(12))
for run in ("slice64-fp", "slice64-lra", "slice64-rodin"):
    b = load(f"bench/results/{run}/results.jsonl")
    open(f"/workspace/target/slice64-after/{run}-parse-errors.txt", "w").write(
        "".join(f"{p}\t{(r.get('first_error') or '')[:120]}\n" for p, r in b.items() if r["verdict"] == "parse-error"))
    open(f"/workspace/target/slice64-after/{run}-unverified.txt", "w").write(
        "".join(p + "\n" for p, r in b.items() if r["verdict"] == "unverified"))
open("/workspace/target/slice64-after/changed.tsv", "w").write("".join("\t".join(x) + "\n" for x in changed))
EOF
```

Expected: `wrong after: 0` on all four lines (criterion 1; any `wrong` stops the slice for a ruling). QF_FP parse-error drops by ≥ 39,900 (criterion 2). LRA by ≥ 2,000 (criterion 3). Rodin falls to 0 (criterion 4).

- [ ] **Step 5: Classify remaining parse errors; confirm `unverified`**

```bash
cd /workspace && A=/workspace/target/slice64-after
cut -f2 $A/slice64-fp-parse-errors.txt $A/slice64-lra-parse-errors.txt | sort | uniq -c | sort -rn | head -20 | tee $A/residual-parse-errors.txt
cat $A/slice64-*-unverified.txt | shuf -n 20 --random-source=<(yes) | while read p; do
  printf '%s\tshinri=%s\tz3=%s\tcvc5=%s\n' $p "$(timeout 25 $A/shinri bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$')" \
    "$(mise exec -- z3 -T:120 bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$')" \
    "$(mise exec -- cvc5 --tlimit=120000 bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$')"; done | tee $A/unverified-confirm.txt
```

Expected: every residual parse-error message has a stated cause in the report. Where z3 or cvc5 decides an `unverified` row, it agrees with shinri; a disagreement is a `wrong` and stops the slice for a ruling.

- [ ] **Step 6: Re-run every `correct → non-correct` row 3× with both binaries (criteria 5, 7)**

```bash
cd /workspace && A=/workspace/target/slice64-after; B=/workspace/target/slice64-base
awk -F'\t' '$3=="correct" && $4!="correct" {print $1}' $A/changed.tsv > $A/losses.txt; wc -l < $A/losses.txt
for p in $(cat $A/losses.txt); do for bin in $B/shinri $A/shinri; do for i in 1 2 3; do
  printf '%s\t%s\t%s\t%s\n' $p $(basename $(dirname $bin)) $i "$(taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin bench/corpus/$p 2>/dev/null | grep -m1 -E '^(sat|unsat|unknown)$' || echo timeout)"; done; done; done | tee $A/loss-reruns.txt
```

Expected: no row where base answers `correct` 3/3 and after fails 3/3. Sample changes reproduce as timeout-edge noise.

- [ ] **Step 7: Write the report**

Create the report in the style of `docs/superpowers/research/2026-10-07-smtlib-2024-slice62-length-consistent-seeds-report.md`, with these sections:
- **Headline:** rows moved to `correct` by logic and family, the parse-error drop per logic, and the criteria table 1–7 with evidence. New timeouts/ooms are reported, not gated.
- **Commands.**
- **Runs:** ids, md5, commit, start/finish, `--jobs`, load.
- **Verdict changes:** from `join.txt`.
- **Residual parse errors:** every message class, with its cause.
- **Unverified confirmation.**
- **What changed versus the spec:** at minimum, the division-by-zero `Diagnostic` (a pre-existing panic fixed in touched code), and that `reals_only_arith` is a plain suffix test (equivalent to the spec's rule).
- **Gates:** ci, oracle and fuzz.
- **Queued for the next slice:** at minimum, the spec §9 error-continuation item and the parametric `define-sort` count from the re-baseline.
- **References.**

- [ ] **Step 8: Spec §11 and commit**

Append to the spec:

```markdown
## 11. Measured outcomes

See `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice64-parser-coverage-report.md`.
Criteria 1–7: <PASS/FAIL each, one line with the key number>.
```

```bash
cd /workspace/.claude/worktrees/slice64
git add docs/superpowers/research/*slice64* docs/superpowers/specs/2026-10-07-shinri-slice64-parser-coverage-design.md
git commit -m "docs(bench+spec): slice64 - report and measured outcomes"
```

- [ ] **Step 9: Push, PR, ask before merging**

```bash
git push -u origin slice64-parser-coverage
gh pr create --base main --title "slice64: parser coverage (Reals-logic numerals, named terms, define-sort)" \
  --body "Spec: docs/superpowers/specs/2026-10-07-shinri-slice64-parser-coverage-design.md. Report: docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice64-parser-coverage-report.md. <headline numbers and criteria table>"
```

Wait for CI to go green. If slice 63 merged first, rebase onto `main`, then re-run `mise run ci` and the oracle suite, and push. **Ask the user** before merging with a merge commit. After the merge, from `/workspace`:

```bash
git push origin --delete slice64-parser-coverage
git worktree remove .claude/worktrees/slice64
git branch -d slice64-parser-coverage
```

---

## Amendment A — FP soundness (spec §3.5, §7.5; added 2026-10-07)

The pre-fix after run (`slice64-fp`) found 3 wrong QF_FP rows, all caused by pre-existing `shinri-fp` bugs (spec §3.5). The owner ruled to fix them in this slice. **Execution order:** Task 6's Steps 1–3 already ran pre-fix (gates passed; after runs launched at `a7dd0cf`). Run Tasks 7 → 8 → 9, then resume Task 6 at Step 4, where the QF_FP set is the **combined** run defined in Task 9.

Additional global constraints:
- **Scope widens** to `crates/shinri-bv/src/blast/mod.rs` (one new `WordSink` method with an `unreachable!` default, like `rm_cache`), `crates/shinri-fp/src/{lib.rs,lower.rs,blast/minmax.rs,blast/fma.rs}`, and the new test file `crates/shinri-solver/tests/fp_soundness_e2e.rs`.
- **Tie bits are shared, never per occurrence** (spec §3.5.1): one bit per key `(is_max, eb, sb, x_is_pos_zero)` per query.
- **Allowed existing-test edit:** the two `fp_min`/`fp_max` calls in `minmax.rs`'s `min_max_words_match_reference` gain the new tie-bit arguments. They pass the bits that reproduce the reference's old choice (`fp_min`: `b.zero(), b.zero()` for −0; `fp_max`: `b.one(), b.one()` for +0). The assertions stay unchanged.
- The fma fix asserts the IEEE result literally. It does not rely on `reference::ref_fma`, which may share the bug.

### Task 7: Shared ±0 tie bits for `fp.min` / `fp.max`

**Files:**
- Modify: `crates/shinri-bv/src/blast/mod.rs`: add the `WordSink::fp_tie_bits` method next to `rm_cache`
- Modify: `crates/shinri-fp/src/lib.rs`: a `tie_bits` field and override on `FpBlaster`, a new `fn tie_bit`, and the `FpMin`/`FpMax` arms (~210–219)
- Modify: `crates/shinri-fp/src/lower.rs`: a `tie_bits` field and override on `Lowerer`
- Modify: `crates/shinri-fp/src/blast/minmax.rs`: `fp_min`, `fp_max`, a new `tie_word`, and tests
- Create: `crates/shinri-solver/tests/fp_soundness_e2e.rs`

**Interfaces:**
- Produces: `WordSink::fp_tie_bits(&mut self) -> &mut FxHashMap<(bool, u32, u32, bool), BitLit>`; `fn tie_bit<S: WordSink>(sink: &mut S, key: (bool, u32, u32, bool)) -> BitLit` (private, `shinri-fp/src/lib.rs`); `pub fn fp_min(b, x, y, eb, sb, tie_pn: BitLit, tie_np: BitLit) -> Vec<BitLit>`, and the same signature for `fp_max`. Here `tie_pn` is the choice when `x = +0, y = −0`, `tie_np` the choice when `x = −0, y = +0`, and a bit value of true means the result is `+0`.
- `fp_soundness_e2e.rs` defines `fn script_outcome(src: &str) -> SolveOutcome`, which Task 8 reuses.

- [ ] **Step 1: Write the failing tests**

Append to `mod tests` in `crates/shinri-fp/src/blast/minmax.rs`:

```rust
    /// Amendment A (spec §3.5.1): a ±0 tie returns the choice bit for its
    /// argument order — true ⇒ +0, false ⇒ −0 — for both fp.min and fp.max.
    #[test]
    fn zero_tie_follows_choice_bit() {
        let (eb, sb) = (8, 24);
        let (pz, nz) = (0x0000_0000u64, 0x8000_0000u64);
        for (x, y, is_pn) in [(pz, nz, true), (nz, pz, false)] {
            for choose_pos in [false, true] {
                for is_max in [false, true] {
                    let mut b = Blaster::new();
                    let xb = const_bits(&b, eb, sb, x);
                    let yb = const_bits(&b, eb, sb, y);
                    let (c, other) = if choose_pos {
                        (b.one(), b.zero())
                    } else {
                        (b.zero(), b.one())
                    };
                    let (pn, np) = if is_pn { (c, other) } else { (other, c) };
                    let w = if is_max {
                        fp_max(&mut b, &xb, &yb, eb, sb, pn, np)
                    } else {
                        fp_min(&mut b, &xb, &yb, eb, sb, pn, np)
                    };
                    let want = if choose_pos { pz } else { nz };
                    assert_eq!(
                        eval_word(b, &w),
                        want,
                        "max={is_max} x={x:#x} y={y:#x} choose_pos={choose_pos}"
                    );
                }
            }
        }
    }
```

In the same module's `min_max_words_match_reference`, change only the two calls:
`fp_min(&mut b, &xb, &yb, eb, sb)` becomes `{ let z = b.zero(); fp_min(&mut b, &xb, &yb, eb, sb, z, z) }`, and
`fp_max(&mut b2, &xb2, &yb2, eb, sb)` becomes `{ let o = b2.one(); fp_max(&mut b2, &xb2, &yb2, eb, sb, o, o) }`.

Create `crates/shinri-solver/tests/fp_soundness_e2e.rs`:

```rust
//! Slice 64 amendment A (spec §3.5, §7.5): FP soundness fixes exposed once
//! `define-sort` let QF_FP files parse.

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Run an SMT-LIB script; the outcome of its last `check-sat`. Any parse
/// error fails the test.
fn script_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = None;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.unwrap_or_else(|e| panic!("parse error: {e:?}"));
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = Some(SolveOutcome::Sat),
            CommandResponse::Unsat => outcome = Some(SolveOutcome::Unsat),
            CommandResponse::Unknown => outcome = Some(SolveOutcome::Unknown),
            _ => {}
        }
    }
    outcome.expect("script has a check-sat")
}

const F64: &str = "(_ FloatingPoint 11 53)";

/// §3.5.1: both zeros are admissible results of a ±0 tie, for both orders
/// and both operators.
#[test]
fn slice64a_zero_tie_admits_both_results() {
    for op in ["fp.min", "fp.max"] {
        for (xv, yv) in [("-zero", "+zero"), ("+zero", "-zero")] {
            for r in ["+zero", "-zero"] {
                let src = format!(
                    "(set-logic QF_FP)(declare-fun x () {F64})(declare-fun y () {F64})\
                     (assert (= x (_ {xv} 11 53)))(assert (= y (_ {yv} 11 53)))\
                     (assert (= ({op} x y) (_ {r} 11 53)))(check-sat)"
                );
                assert_eq!(script_outcome(&src), SolveOutcome::Sat, "{op} {xv} {yv} -> {r}");
            }
        }
    }
}

/// §3.5.1: fp.min/fp.max are functions — two applications to equal
/// arguments must agree, so per-occurrence free choice would be unsound.
#[test]
fn slice64a_zero_tie_is_functionally_consistent() {
    for op in ["fp.min", "fp.max"] {
        let src = format!(
            "(set-logic QF_FP)(declare-fun a () {F64})(declare-fun b () {F64})\
             (declare-fun c () {F64})(declare-fun d () {F64})\
             (assert (= a (_ -zero 11 53)))(assert (= b (_ +zero 11 53)))\
             (assert (= c (_ -zero 11 53)))(assert (= d (_ +zero 11 53)))\
             (assert (not (= ({op} a b) ({op} c d))))(check-sat)"
        );
        assert_eq!(script_outcome(&src), SolveOutcome::Unsat, "{op}");
    }
}

/// QF_FP/wintersteiger/min/min-has-solution-13472 (`:status sat`).
#[test]
fn slice64a_min_has_solution_13472() {
    let src = "(set-logic QF_FP)(define-sort FPN () (_ FloatingPoint 11 53))\
        (declare-fun x () FPN)(declare-fun y () FPN)(declare-fun r () FPN)\
        (assert (= x (fp #b1 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))\
        (assert (= y (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))\
        (assert (= r (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))\
        (assert (= (fp.min x y) r))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Sat);
}
```

- [ ] **Step 2: Run them and verify they fail**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-fp -E 'test(zero_tie_follows_choice_bit)'
taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(fp_soundness_e2e)'
```

Expected:
- shinri-fp does not compile, because `fp_min` takes 5 arguments, not 7. Record that as the RED.
- In `fp_soundness_e2e`, 3 tests are discovered. `slice64a_zero_tie_admits_both_results` FAILS (some combination is `unsat`), and `slice64a_min_has_solution_13472` FAILS (`unsat`).
- `slice64a_zero_tie_is_functionally_consistent` PASSES already. It is the guard that the fix must not break.

- [ ] **Step 3: Implement**

In `crates/shinri-bv/src/blast/mod.rs`, add to `trait WordSink`, directly after `rm_cache`:

```rust
    /// Shared `fp.min`/`fp.max` ±0 tie bits (slice 64 amendment A), keyed by
    /// `(is_max, eb, sb, x_is_pos_zero)`. SMT-LIB leaves a ±0 tie's result
    /// unspecified, but `fp.min` is still a function, so every occurrence must
    /// share one choice per key for the whole query. Only meaningful for FP
    /// sinks; pure-BV lowering never calls this.
    fn fp_tie_bits(&mut self) -> &mut FxHashMap<(bool, u32, u32, bool), BitLit> {
        unreachable!("pure BV lowering has no fp.min/fp.max")
    }
```

In `crates/shinri-fp/src/lib.rs`:
- Add the field `tie_bits: FxHashMap<(bool, u32, u32, bool), BitLit>,` to `FpBlaster`, with the doc `/// Shared fp.min/fp.max ±0 tie bits (amendment A; see WordSink::fp_tie_bits).`, and initialise it with `FxHashMap::default()` in `FpBlaster::new`.
- Add the override to `impl WordSink for FpBlaster`:

```rust
    fn fp_tie_bits(&mut self) -> &mut FxHashMap<(bool, u32, u32, bool), BitLit> {
        &mut self.tie_bits
    }
```

Add the same field, initialiser and override to `Lowerer` in `crates/shinri-fp/src/lower.rs`.

Add next to `blast_fp_word` in `lib.rs`:

```rust
/// The shared ±0 tie bit for `key`, minted once per query (amendment A).
fn tie_bit<S: WordSink>(sink: &mut S, key: (bool, u32, u32, bool)) -> BitLit {
    if let Some(&l) = sink.fp_tie_bits().get(&key) {
        return l;
    }
    let l = sink.blaster().fresh();
    sink.fp_tie_bits().insert(key, l);
    l
}
```

The `FpMin` / `FpMax` arms become:

```rust
                FpMin => {
                    let xw = sink.word(ctx, kids[0]);
                    let yw = sink.word(ctx, kids[1]);
                    let pn = tie_bit(sink, (false, eb, sb, true));
                    let np = tie_bit(sink, (false, eb, sb, false));
                    crate::blast::minmax::fp_min(sink.blaster(), &xw, &yw, eb, sb, pn, np)
                }
                FpMax => {
                    let xw = sink.word(ctx, kids[0]);
                    let yw = sink.word(ctx, kids[1]);
                    let pn = tie_bit(sink, (true, eb, sb, true));
                    let np = tie_bit(sink, (true, eb, sb, false));
                    crate::blast::minmax::fp_max(sink.blaster(), &xw, &yw, eb, sb, pn, np)
                }
```

In `crates/shinri-fp/src/blast/minmax.rs`:
- Update the module doc's "sign-canonical ±0 rule" to "a ±0 tie resolved by a shared choice bit (amendment A)".
- Add:

```rust
/// The ±0 tie result: `+0` when the order's choice bit is true, else `−0`.
/// `x_sign` selects the order: `x = +0` uses `tie_pn`, `x = −0` uses `tie_np`.
/// SMT-LIB leaves the tie unspecified; the bits are shared per format and
/// order by the caller, so the operator stays a function (amendment A).
fn tie_word(
    b: &mut Blaster,
    x_sign: BitLit,
    tie_pn: BitLit,
    tie_np: BitLit,
    eb: u32,
    sb: u32,
) -> Vec<BitLit> {
    let choose_pos = b.mux2(x_sign, tie_np, tie_pn);
    let mut w = zero_word(b, eb, sb, false);
    let last = w.len() - 1;
    w[last] = b.not1(choose_pos);
    w
}
```

`fp_min` gains the parameters `tie_pn: BitLit, tie_np: BitLit`. Its doc's "resolves to -0 (sign-canonical, order-independent)" becomes "resolves to the shared choice bit for its argument order". Replace its two lines

```rust
    let neg_zero = zero_word(b, eb, sb, true);
    let pick = mux_word(b, zero_tie, &neg_zero, &pick);
```

with

```rust
    let tie = tie_word(b, ux.sign, tie_pn, tie_np, eb, sb);
    let pick = mux_word(b, zero_tie, &tie, &pick);
```

`fp_max` gets the same two new parameters, the same doc change ("the (+0,-0) tie resolves to +0" becomes "… to the shared choice bit"), and the same replacement of its `pos_zero` lines. `zero_word` keeps its signature; if it ends up called only with `false`, leave it as it is.

- [ ] **Step 4: Run the tests and the affected suites**

```bash
taskset -c 0-11 cargo nextest run -p shinri-bv -p shinri-fp -E 'not test(_tiny_exhaustive_all_modes)'
taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(fp_soundness_e2e) | binary(fp_e2e)'
```

Expected: everything passes. That includes `min_max_words_match_reference` (unchanged assertions), `zero_tie_follows_choice_bit`, and the 3 `fp_soundness_e2e` tests. The exhaustive `#[ignore]`d suites stay ignored (AGENTS.md); don't un-ignore them.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-bv/src/blast/mod.rs crates/shinri-fp/src/lib.rs crates/shinri-fp/src/lower.rs crates/shinri-fp/src/blast/minmax.rs crates/shinri-solver/tests/fp_soundness_e2e.rs
git commit -m "fix(fp): slice64 - fp.min/fp.max ±0 tie is a shared free choice"
```

---

### Task 8: `fp.fma` zero addend never wins the magnitude election

**Files:**
- Modify: `crates/shinri-fp/src/blast/fma.rs`: the hi/lo election (~70–80), the zero-z comment (~48), tests
- Modify: `crates/shinri-solver/tests/fp_soundness_e2e.rs` (append)

**Interfaces:**
- Consumes: `script_outcome` from Task 7; the `fma.rs` test helpers `const_bits`, `eval_word`, `rmode`, `rm::literal`, and `RoundMode`.

- [ ] **Step 1: Write the failing tests**

Append to `mod tests` in `crates/shinri-fp/src/blast/fma.rs`:

```rust
    /// Amendment A (spec §3.5.2): x·y ≈ −2^-1576 underflows far below a zero
    /// addend's normalized exponent (emin − pw). The exact result is a tiny
    /// negative, so the IEEE result keeps the negative sign. Expected values
    /// are literal IEEE results, not `ref_fma`.
    /// Operands from QF_FP/wintersteiger/fma/fma-has-solution-4663.
    #[test]
    fn fma_zero_addend_loses_to_underflowed_product() {
        let (eb, sb) = (11, 53);
        let (x, y) = (0x0c35_20cc_566c_800fu64, 0x913c_e340_a93e_e431u64);
        let neg_zero = 0x8000_0000_0000_0000u64;
        let neg_min_sub = 0x8000_0000_0000_0001u64;
        for (z, m, want) in [
            (0u64, RoundMode::Rtz, neg_zero),
            (neg_zero, RoundMode::Rtz, neg_zero),
            (0, RoundMode::Rne, neg_zero),
            (0, RoundMode::Rna, neg_zero),
            (0, RoundMode::Rtp, neg_zero),
            (0, RoundMode::Rtn, neg_min_sub),
        ] {
            let mut bl = Blaster::new();
            let xv = const_bits(&bl, eb, sb, x);
            let yv = const_bits(&bl, eb, sb, y);
            let zv = const_bits(&bl, eb, sb, z);
            let sel = rm::literal(&bl, rmode(m));
            let word = fp_fma(&mut bl, &xv, &yv, &zv, &sel, eb, sb);
            assert_eq!(
                eval_word(bl, &word),
                want,
                "fp.fma z={z:#x} m={m:?}"
            );
        }
    }
```

Append to `crates/shinri-solver/tests/fp_soundness_e2e.rs`:

```rust
const FMA_4663: &str = "(set-logic QF_FP)(define-sort FPN () (_ FloatingPoint 11 53))\
    (declare-fun x () FPN)(declare-fun y () FPN)(declare-fun z () FPN)(declare-fun r () FPN)\
    (assert (= x (fp #b0 #b00011000011 #b0101001000001100110001010110011011001000000000001111)))\
    (assert (= y (fp #b1 #b00100010011 #b1100111000110100000010101001001111101110010000110001)))\
    (assert (= z (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))\
    (assert (= r (fp #b1 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))";

/// QF_FP/wintersteiger/fma/fma-has-solution-4663 (`:status sat`).
#[test]
fn slice64a_fma_has_solution_4663() {
    let src = format!("{FMA_4663}(assert (= (fp.fma roundTowardZero x y z) r))(check-sat)");
    assert_eq!(script_outcome(&src), SolveOutcome::Sat);
}

/// QF_FP/wintersteiger/fma/fma-has-no-other-solution-4663 (`:status unsat`).
#[test]
fn slice64a_fma_has_no_other_solution_4663() {
    let src = format!("{FMA_4663}(assert (not (= (fp.fma roundTowardZero x y z) r)))(check-sat)");
    assert_eq!(script_outcome(&src), SolveOutcome::Unsat);
}
```

Before writing the e2e constant, confirm the `no-other-solution` file's assertion shape with `grep -v '^;' /workspace/bench/corpus/QF_FP/wintersteiger/fma/fma-has-no-other-solution-4663.smt2`. If it differs from `(not (= (fp.fma …) r))`, mirror the file exactly.

- [ ] **Step 2: Run them and verify they fail**

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo nextest run -p shinri-fp -E 'test(fma_zero_addend_loses_to_underflowed_product)'
taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(fp_soundness_e2e) & test(fma)'
```

Expected: the unit test FAILS on the first case, getting `0x0` where `0x8000000000000000` was expected. Both e2e tests FAIL (`unsat` and `sat`, respectively). If the unit test fails differently, or passes, **stop**: the spec §3.5.2 hypothesis is wrong. Record the evidence in the report, find the actual cause, and fix that instead (spec §3.5.2 allows this).

- [ ] **Step 3: Implement**

In `fma.rs`, replace

```rust
    let tie = b.and2(exp_eq, sig_ge);
    let p_ge_z = b.or2(exp_gt, tie);
```

with

```rust
    let tie = b.and2(exp_eq, sig_ge);
    // Amendment A: a zero addend's normalized exponent (emin − pw) is not low
    // enough to lose to a product that underflows further, so a zero z must
    // never be elected over a nonzero product (else res_sign takes z's sign).
    let z_zero_p_nonzero = {
        let p_nonzero = b.not1(prod_zero);
        b.and2(oz.is_zero, p_nonzero)
    };
    let p_ge_z = {
        let g = b.or2(exp_gt, tie);
        b.or2(g, z_zero_p_nonzero)
    };
```

Then correct the stale comment line `// For zero z: lzc=pw, z_sig_norm=0, z_exp goes very negative (product wins tie).` to read `// For zero z: lzc=pw, z_sig_norm=0, z_exp = emin − pw; the election below forces the product to win (amendment A).`.

- [ ] **Step 4: Run the tests and the fma suites**

```bash
taskset -c 0-11 cargo nextest run -p shinri-fp -E 'not test(_tiny_exhaustive_all_modes)'
taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(fp_soundness_e2e) | binary(fp_e2e)'
```

Expected: everything passes. That includes `fp_fma_tiny_sampled_all_modes` (sampled against `ref_fma`), the new unit test, and all 5 `fp_soundness_e2e` tests.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all && taskset -c 0-11 mise run lint
git add crates/shinri-fp/src/blast/fma.rs crates/shinri-solver/tests/fp_soundness_e2e.rs
git commit -m "fix(fp): slice64 - fma zero addend never out-elects an underflowed product"
```

---

### Task 9: Gates again; fp-ops re-run; combined QF_FP set

**Files:** none in the repo. Artifacts go under `/workspace/target/slice64-fpfix/` and `/workspace/target/slice64-fp-ops-corpus/`.

**Interfaces:**
- Consumes: branch HEAD after Tasks 7–8; the finished pre-fix after runs (`/workspace/target/slice64-after/finished.txt`); `bench/results/slice64-{base-fp,fp}`.
- Produces: `bench/results/slice64-fp-ops` (the post-fix re-run); `bench/results/slice64-fp-combined/results.jsonl`, which is `slice64-fp` with the fp-ops rows replaced. Task 6 Step 4 onward uses `slice64-fp-combined` in place of `slice64-fp`.

- [ ] **Step 1: Re-run the gates on the fixed branch**

Run Task 6 Step 1's three commands again (ci, the oracle suite, fuzz 600 s). Expected: `ci` exit 0, and the oracle count equal to base 859 + 5 + 5 (the e2e binary `fp_soundness_e2e` adds 5 tests that are not feature-gated). For fuzz, also record a rerun with `ASAN_OPTIONS=detect_leaks=0` if LeakSanitizer fails at exit again, as in the pre-fix gates. Append the results to `/workspace/target/slice64-gates.txt`.

- [ ] **Step 2: Build the fp-ops corpus**

```bash
cd /workspace && python3 - <<'EOF'
import os, pathlib, re
corpus = pathlib.Path("bench/corpus")
ps = sorted(str(p.relative_to(corpus)) for p in (corpus / "QF_FP").rglob("*.smt2")
            if re.search(r"fp\.(min|max|fma)\b", p.read_text(errors="replace")))
out = pathlib.Path("target/slice64-fp-ops-corpus")
for rel in ps:
    dst = out / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    if not dst.exists():
        os.link(corpus / rel, dst)
pathlib.Path("target/slice64-fp-ops.txt").write_text("\n".join(ps) + "\n")
print(len(ps))
EOF
```

Expected: `8570`, matching the spec §8 count. A different number is recorded in the report; it doesn't stop the run.

- [ ] **Step 3: Wait for the pre-fix after runs, then launch the fp-ops re-run**

Wait (with a background until-loop) for `/workspace/target/slice64-after/finished.txt`. Then:

```bash
cd /workspace/.claude/worktrees/slice64
taskset -c 0-11 cargo build --release -p shinri-cli -p shinri-bench
F=/workspace/target/slice64-fpfix && mkdir -p $F
cp target/release/shinri target/release/shinri-bench $F/
md5sum $F/shinri | tee $F/md5.txt; git rev-parse --short HEAD | tee $F/commit.txt
for p in QF_FP/wintersteiger/fma/fma-has-no-other-solution-4663.smt2 QF_FP/wintersteiger/fma/fma-has-solution-4663.smt2 QF_FP/wintersteiger/min/min-has-solution-13472.smt2; do
  echo "$p $($F/shinri /workspace/bench/corpus/$p | grep -E '^(sat|unsat|unknown)$')"; done
uptime | tee $F/uptime-start.txt
cd /workspace && setsid nohup sh -c "
  taskset -c 12-23 $F/shinri-bench run --logics QF_FP --corpus /workspace/target/slice64-fp-ops-corpus --results /workspace/bench/results \
    --timeout 20 --mem-mb 3072 --jobs 3 --solver $F/shinri --run-id slice64-fp-ops > $F/run-fp-ops.log 2>&1;
  date -u +%FT%TZ > $F/finished.txt" > /dev/null 2>&1 &
```

Expected: the three corpus rows print `unsat`, `sat` and `sat`, matching their `:status`. Wait for `$F/finished.txt`.

- [ ] **Step 4: Build the combined QF_FP result**

```bash
cd /workspace && python3 - <<'EOF'
import json, pathlib
lines = open("bench/results/slice64-fp/results.jsonl").read().splitlines()
fixture, rows = lines[0], [json.loads(l) for l in lines[1:] if l.strip()]
ops = {r["path"]: r for r in map(json.loads, open("bench/results/slice64-fp-ops/results.jsonl")) if "path" in r}
assert set(ops) <= {r["path"] for r in rows}, "fp-ops rows must be a subset of slice64-fp"
out = pathlib.Path("bench/results/slice64-fp-combined"); out.mkdir(exist_ok=True)
with open(out / "results.jsonl", "w") as f:
    f.write(fixture + "\n")
    for r in rows:
        f.write(json.dumps(ops.get(r["path"], r)) + "\n")
print("replaced", len(ops), "of", len(rows), "; wrong in combined:",
      sum((ops.get(r["path"], r))["verdict"] == "wrong" for r in rows))
EOF
```

Expected: `replaced 8570 of 40407 ; wrong in combined: 0`. Any `wrong` stops the slice for a ruling under spec §3.5: fix it, or fence it to `unknown` with a stated cause.

- [ ] **Step 5: Resume Task 6 at Step 4**

Run Task 6 Steps 4–9 with `slice64-fp-combined` in place of `slice64-fp` in the join's `(base, after)` pairs. Task 6 Step 6's re-runs use the `$F` (post-fix) binary as "after" for rows in the fp-ops set. The report adds:
- a § *FP soundness (amendment A)* with the three rows, the two root causes, the tie-bit design and the fp-ops re-run (moves, counts, wrong = 0);
- the gates from both rounds;
- a row in *What changed versus the spec* for amendment A.
