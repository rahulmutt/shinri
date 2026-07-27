# Slice 44 — UF/BV congruence in the bit-blaster: Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give uninterpreted applications with a BitVec result sort functional
consistency in the eager bit-blaster, turning a confirmed wrong `sat` on
QF_UFBV / QF_AUFBV / the FP-mixed path into the correct `unsat`.

**Architecture:** Bit-level Ackermann congruence emitted inside
`blast_bv_word`'s `Op::Uninterpreted` arm, following the gadget
`shinri_fp::blast_fp_to_bv` already implements for `fp.to_ubv`/`fp.to_sbv`: a
per-sink registry of prior applications plus pairwise
`(⋀ₖ argₖ equal) → (result equal)` clauses. Two pre-lowering fences (argument
sort, encoding blowup) keep the blast arms' `unreachable!`s internal invariants.
One arm serves three solver paths, because pure-BV (`shinri_bv::lower`),
FP/mixed (`shinri-fp`'s `Lowerer`) and ABV (`abv_stage`'s persistent `Blaster`)
all route BV-sorted nodes through it.

**Tech Stack:** Rust; `cargo nextest` (0.9.140, pinned); `mise` tasks; `z3` and
`cvc5` from mise for the `oracle` feature; `easy_smt` for oracle harnesses.

**Spec:** `docs/superpowers/specs/2026-07-27-shinri-slice44-uf-bv-congruence-design.md`

## Global Constraints

- **Pure-Rust mandate.** Native-link dependencies are banned; `deny.toml` bans
  `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`. Add no new dependency.
- **Blocking PR tier budget: 10–15 min wall-clock** (CI job hard cap 20 min).
  Any test measured >5 min must be `#[ignore = "exhaustive: nightly tier (~N min in CI)"]`d
  with a fast smoke companion on the blocking tier.
- **`cargo fmt --all` before every push.** CI gates on `fmt --check` and fails fast.
- **`cargo clippy --workspace --all-targets -- -D warnings` must be clean.**
  `mise run lint` covers both.
- **nextest filters use the expression form** `-E 'test(<name>)'`, never a
  positional `mod::name` filter — that matches nothing on the pinned nextest and
  a 0-test run reads as green. Use `-E 'binary(<name>)'` to select a whole
  integration-test binary. **Always confirm a non-zero discovered count.**
- **Oracle tests are feature-gated.** `cargo nextest run -p shinri-solver
  --features oracle`. Without `--features oracle` the suites compile to **zero
  tests** and report green. Never cite a run without the flag as coverage.
- **`blast_bv_word` is a shared primitive** across BV, FP and ABV. The gate for
  this slice is the **full unfiltered oracle run**, not a filtered one.
- **Verdict invariant (spec §2.1).** Permitted: `sat` → `unsat`, and
  `unknown` → decided. Regression: any `unsat` → `sat`, any decided → `unknown`
  **except** flips attributable to Task 2's or Task 4's fence, which must be
  named individually with their cause.
- Never remove `#[ignore]` from the exhaustive `shinri-fp` suites
  (`fp_div`/`fp_mul`/`fp_add` `_tiny_exhaustive_all_modes`,
  `to_fp_fp_tiny_exhaustive_both_directions`, `rem_tiny_exhaustive`).

## File Structure

| File | Responsibility | Task |
|---|---|---|
| `crates/shinri-solver/tests/qfbv_oracle.rs` | modify: term pool gains uninterpreted applications — the gate | 1 |
| `crates/shinri-solver/src/bv_stage.rs` | modify: `uf_args_supported` (fence 1), `uf_congruence_cost` + budget (fence 2) | 2, 4 |
| `crates/shinri-solver/src/lib.rs` | modify: call both fences on the pure-BV, FP/mixed and ABV paths | 2, 4 |
| `crates/shinri-bv/src/blast/mod.rs` | modify: `UfApp`, `WordSink::uf_apps`/`word_eq`, `Blaster` store, the congruence arm | 3 |
| `crates/shinri-fp/src/lower.rs` | modify: `Lowerer`'s two hook impls, FP-aware `word_eq` | 5 |
| `crates/shinri-solver/tests/qfufbv_e2e.rs` | create: regression pins, direction tests, fence pins | 6 |
| `crates/shinri-solver/tests/qfdt_model_e2e.rs` | modify: delete the `#[should_panic]` pin, re-measure its release sibling | 6 |
| `crates/shinri-solver/tests/qfabv_oracle.rs`, `fp_oracle.rs` | modify: same generator extension | 5 |
| `docs/superpowers/specs/2026-07-25-shinri-slice43-model-channel-design.md` | modify: rewrite the §5 BV row | 7 |

**Task order is load-bearing.** Fence 1 (Task 2) lands **before** the arm
(Task 3): today's arm never blasts its arguments, so an Int-sorted argument is
harmless; the moment the arm recurses into arguments, an Int-sorted one reaches
`blast_bv_word`'s builtin dispatch or `Lowerer::word`'s
`unreachable!("Lowerer::word on non-BV/non-FP sort")`. Fence 2 (Task 4) lands
**after** the arm, because its budget can only be calibrated against a real
encoding.

Between Task 3 and Task 4 there is no blowup cap. This is safe only because
Task 1's generator uses a 2-symbol pool at arity ≤ 2 over ≤ 3 variables. Do not
add a large-arity generator before Task 4.

---

### Task 1: The gate — teach the QF_BV oracle to emit uninterpreted applications

`qfbv_oracle`'s generator builds its pool exclusively from `BuiltinOp::Bv*` over
declared **nullary** variables, so it cannot emit an uninterpreted application.
That is why this bug survived every green oracle run since `e437ba41`. Fix the
suite first, and **prove it fails before the fix exists** — a generator that
passes on pre-slice `main` is not generating the shape, and its later green
would be meaningless.

**Files:**
- Modify: `crates/shinri-solver/tests/qfbv_oracle.rs` (`gen_instance`, `crates/shinri-solver/tests/qfbv_oracle.rs:89`; the `differential_qf_bv_small` setup block around `:437`)

**Interfaces:**
- Consumes: nothing from earlier tasks.
- Produces: `differential_qf_bv_small` now covers uninterpreted applications.
  Tasks 3 and 5 use it as their pass/fail gate.

- [ ] **Step 1: Declare uninterpreted symbols in both solvers**

In `differential_qf_bv_small`, insert **immediately after** the existing
`for name in &var_names { dump.push_str(...) }` loop — that is the first point
where `bv_type_atom`, `ctx` and `dump` are all in scope. Add a **small** symbol
pool so applications collide on the same symbol (that is what makes congruence
fire):

```rust
        // Uninterpreted symbols over BV, added in slice 44. The pool is small
        // ON PURPOSE: two symbols over three variables means many applications
        // share a symbol, which is exactly what makes a congruence violation
        // reachable. A large pool would spread applications thin and the
        // generator would stop finding the bug.
        let uf1_s = s.declare_fun("f", &[bv_sort], bv_sort);
        let uf2_s = s.declare_fun("g", &[bv_sort, bv_sort], bv_sort);
        // easy-smt 0.2 takes Vec<SExpr> for the parameter list — same idiom as
        // tests/oracle.rs:48.
        ctx.declare_fun("f", vec![bv_type_atom], bv_type_atom)
            .unwrap();
        ctx.declare_fun("g", vec![bv_type_atom, bv_type_atom], bv_type_atom)
            .unwrap();
        dump.push_str(&format!(
            "\n(declare-fun f ((_ BitVec {width})) (_ BitVec {width}))\
             \n(declare-fun g ((_ BitVec {width}) (_ BitVec {width})) (_ BitVec {width}))"
        ));
```

Change the logic string from `QF_BV` to `QF_UFBV` so z3 accepts the
declarations:

```rust
        ctx.set_logic("QF_UFBV").unwrap();
```

and correspondingly the dump header:

```rust
        let mut dump = format!("iter={iter} width={width}\n(set-logic QF_UFBV)");
```

Thread the two symbols into the generator by extending its signature:

```rust
        gen_instance(
            &mut rng, &mut s, &mut ctx, width, &var_names, &vars_s, &z_vars,
            uf1_s, uf2_s, &mut dump,
        );
```

- [ ] **Step 2: Extend `gen_instance` to build applications into the term pool**

Change the signature (add the two symbol parameters before `dump`):

```rust
fn gen_instance(
    rng: &mut Lcg,
    s: &mut Solver,
    ctx: &mut easy_smt::Context,
    width: u32,
    var_names: &[&str],
    vars_s: &[shinri_core::TermId],
    z_vars: &[easy_smt::SExpr],
    uf1: shinri_core::SymbolId,
    uf2: shinri_core::SymbolId,
    dump: &mut String,
) {
```

In the "add a small number of random BV terms to the pool" loop, widen the op
selector from 19 to 21 and add two arms. Insert these two match arms alongside
the existing ones (keep every existing arm unchanged):

```rust
            // slice 44: (f t_i) — a 1-ary uninterpreted application.
            19 => {
                let ns = s.app(Op::Uninterpreted(uf1), &[pool[i].s]);
                let nz = ctx.list(vec![ctx.atom("f"), pool[i].z]);
                (ns, nz, width)
            }
            // slice 44: (g t_i t_j) — a 2-ary uninterpreted application.
            _ => {
                let ns = s.app(Op::Uninterpreted(uf2), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("g"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
```

and change the selector line to:

```rust
        let op_kind = rng.below(21); // 0..18 builtin BV ops, 19..20 uninterpreted apps
```

If the existing `match op_kind` already ends in a catch-all `_ =>` arm for a
builtin op, renumber that arm to its explicit index (`18 =>`) so the two new
arms are reachable. Verify by reading the arm list before editing — an
unreachable arm is the single most likely way this task silently does nothing.

- [ ] **Step 3: Run the extended oracle on unmodified solver code and CONFIRM IT FAILS**

Run:

```bash
cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_bv_small)' --no-capture
```

Expected: **FAIL**, either with a
`QF_BV SOUNDNESS DISAGREEMENT (iter N): shinri=Sat z3=Unsat` panic, or — since
the blocking tier builds the `dev` profile with debug assertions on — with
`panicked at crates/shinri-bv/src/blast/mod.rs:282: non-nullary uninterpreted BV
fn out of scope`.

Confirm the discovered test count is **1**, not 0. A 0-test run reads as green
and proves nothing.

**If it passes, stop and fix the generator** — the new arms are unreachable, the
symbol pool is too large, or `op_kind`'s range was not widened. Do not proceed.

- [ ] **Step 4: Record the failure as a measurement**

Append to the plan's running notes (create
`docs/superpowers/plans/2026-07-27-shinri-slice44-uf-bv-congruence.md` notes
section at the bottom, or a scratch file committed with the task): the exact
failing iteration number, the `shinri=` / `z3=` verdicts, and the reproducer
dump the harness prints. Success criterion 2 requires this.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver/tests/qfbv_oracle.rs
git commit -m "test(bv): slice44 T1 — QF_BV oracle emits uninterpreted applications

The generator built its pool only from BuiltinOp::Bv* over nullary
variables, so it could never emit an uninterpreted application and the
missing-congruence wrong-sat was unreachable by the differential suite.
Two symbols (1-ary f, 2-ary g) join the pool, deliberately small so
applications collide on one symbol.

MEASURED: fails on unmodified solver code — this is the gate."
```

---

### Task 2: Fence 1 — argument sorts the blaster cannot word

Every argument of a non-nullary uninterpreted BV-result application must have a
blastable word before Task 3 makes the arm recurse into arguments. BV always
qualifies; FP qualifies **only on the FP path**, where a `Lowerer` exists to
compare FP words with `core_eq`. Everything else fences to a sound `unknown`.

This task changes verdicts on its own: a query with an Int-sorted argument goes
decided → `unknown`. That is the spec §2.1 named exception, and Step 5 records
it.

**Files:**
- Modify: `crates/shinri-solver/src/bv_stage.rs` (add after `has_non_bv_theory_atom`, `crates/shinri-solver/src/bv_stage.rs:177`)
- Modify: `crates/shinri-solver/src/lib.rs` (pure-BV path `:993`–`:1001`; FP/mixed path `:1009`–`:1056`; ABV path `:902`–`:905`)
- Test: `crates/shinri-solver/src/bv_stage.rs` (unit tests at the bottom of the file, matching the existing convention)

**Interfaces:**
- Consumes: nothing from earlier tasks.
- Produces: `pub fn uf_args_supported(ctx: &Context, atoms: &[TermId], allow_fp_args: bool) -> bool`.
  Task 4 adds a sibling in the same module; Task 3 relies on this having landed.

- [ ] **Step 1: Write the failing unit test**

Add to `bv_stage.rs`'s test module:

```rust
    #[test]
    fn uf_args_supported_admits_bv_arguments() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let c = ctx.mk_bv_const(8, shinri_num::Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fx, c]).unwrap();
        assert!(uf_args_supported(&ctx, &[atom], false));
    }

    #[test]
    fn uf_args_supported_rejects_an_int_argument() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let int_s = ctx.int_sort();
        let h = ctx.declare_fun("h", &[int_s], s8);
        let nf = ctx.declare_fun("n", &[], int_s);
        let n = ctx.mk_app(Op::Uninterpreted(nf), &[]).unwrap();
        let hn = ctx.mk_app(Op::Uninterpreted(h), &[n]).unwrap();
        let c = ctx.mk_bv_const(8, shinri_num::Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[hn, c]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "an Int-sorted argument has no blastable word — must fence"
        );
    }

    #[test]
    fn uf_args_supported_leaves_nullary_applications_alone() {
        // A nullary uninterpreted BV symbol has no arguments to check and must
        // never be fenced — it is the ordinary BV variable case.
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let c = ctx.mk_bv_const(8, shinri_num::Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, c]).unwrap();
        assert!(uf_args_supported(&ctx, &[atom], false));
    }
```

If `Context::int_sort` / `mk_bv_const` / `mk_app` have different names in this
crate, read the neighbouring tests in `bv_stage.rs` and match their idiom
exactly rather than guessing.

- [ ] **Step 2: Run the tests to verify they fail**

```bash
cargo nextest run -p shinri-solver -E 'test(uf_args_supported)'
```

Expected: FAIL to compile, `cannot find function uf_args_supported in this scope`.
Confirm 3 tests are discovered once it compiles.

- [ ] **Step 3: Implement the fence**

Add to `bv_stage.rs`:

```rust
/// Fence 1 (slice 44 §4, SOUNDNESS-CRITICAL). Every non-nullary uninterpreted
/// application with a **BitVec result sort** reachable from `atoms` must have
/// arguments the blaster can turn into words, because `blast_bv_word`'s
/// congruence arm compares argument words pairwise.
///
/// BV-sorted arguments always qualify. FP-sorted arguments qualify only when
/// `allow_fp_args` — that is, on the FP/mixed path, where a `Lowerer` exists
/// with a `core_eq`-based `word_eq`. A `Blaster` alone cannot compare an FP
/// word (`core_eq` lives in `shinri-fp`, which depends on `shinri-bv` and not
/// the reverse).
///
/// Everything else — Int, Bool, Array, String, uninterpreted sorts,
/// RoundingMode — fences the caller to a sound `Unknown`. Without this,
/// `Lowerer::word` reaches its `unreachable!("Lowerer::word on non-BV/non-FP
/// sort")` (`crates/shinri-fp/src/lower.rs:69`) and `Blaster::word` reaches
/// `blast_bv_word`'s builtin dispatch on a non-BV term.
///
/// Walks the ATOM set rather than the assertion list: that is exactly what
/// reaches the blaster, and it stays a superset of what survives `rewrite`
/// (rewriting can fold applications away but never create them), so the
/// conservative bias every other fence in this stage has is preserved.
pub fn uf_args_supported(ctx: &Context, atoms: &[TermId], allow_fp_args: bool) -> bool {
    let mut seen = rustc_hash::FxHashSet::default();
    atoms
        .iter()
        .all(|&a| walk_uf_args(ctx, a, allow_fp_args, &mut seen))
}

fn walk_uf_args(
    ctx: &Context,
    t: TermId,
    allow_fp_args: bool,
    seen: &mut rustc_hash::FxHashSet<TermId>,
) -> bool {
    if !seen.insert(t) {
        return true; // already validated on another path
    }
    let TermNode::App { op, args, sort } = ctx.term_node(t) else {
        return true; // a constant has no arguments
    };
    let kids = ctx.children(*args).to_vec();
    if matches!(op, Op::Uninterpreted(_)) && !kids.is_empty() && ctx.bv_width(*sort).is_some() {
        for &k in &kids {
            let ks = ctx.sort_of(k);
            let wordable =
                ctx.bv_width(ks).is_some() || (allow_fp_args && ctx.fp_widths(ks).is_some());
            if !wordable {
                return false;
            }
        }
    }
    kids.iter()
        .all(|&k| walk_uf_args(ctx, k, allow_fp_args, seen))
}
```

- [ ] **Step 4: Run the tests to verify they pass**

```bash
cargo nextest run -p shinri-solver -E 'test(uf_args_supported)'
```

Expected: 3 tests discovered, 3 PASS.

- [ ] **Step 5: Wire the fence into all three paths**

In `crates/shinri-solver/src/lib.rs`, the pure-BV path becomes:

```rust
        let lowered_bv: Option<shinri_bv::Lowered> = if uses_bv && !uses_fp {
            let bv_atoms = crate::bv_stage::collect_bv_atoms(&self.ctx, &assertions);
            if crate::bv_stage::has_non_bv_theory_atom(&self.ctx, &assertions, &bv_atoms) {
                return SolveOutcome::Unknown;
            }
            // Fence 1 (slice 44 §4): no FP sink on this path, so FP-sorted
            // arguments are not admitted either.
            if !crate::bv_stage::uf_args_supported(&self.ctx, &bv_atoms, false) {
                return SolveOutcome::Unknown;
            }
            Some(shinri_bv::lower(&mut self.ctx, &bv_atoms))
        } else {
            None
        };
```

On the FP/mixed path, add the check immediately after the existing
`bv_atoms_fp_supported` fence (`lib.rs:1053`), before `lower_mixed`, with
`allow_fp_args = true` and the union of both atom sets:

```rust
            // Fence 1 (slice 44 §4). `allow_fp_args` is true here: the Lowerer's
            // word_eq compares FP words with core_eq.
            let uf_atoms: Vec<TermId> = fp_atoms.iter().chain(bv_atoms.iter()).copied().collect();
            if !crate::bv_stage::uf_args_supported(&self.ctx, &uf_atoms, true) {
                return SolveOutcome::Unknown;
            }
```

On the ABV path, add it inside the `uses_arrays_over_bv` block right after the
existing `abv_stage::fenced` check (`lib.rs:903`–`:905`). The ABV stage builds
its own `shinri_bv::Blaster` (`abv_stage.rs:312`), so it has no FP sink:

```rust
            if !crate::bv_stage::uf_args_supported(&self.ctx, &assertions, false) {
                return SolveOutcome::Unknown;
            }
```

Note this one passes `assertions`, not a collected atom set, because
`abv_stage` does its own collection internally — a superset, which keeps the
conservative bias.

- [ ] **Step 6: Add the end-to-end fence pin**

Add to `crates/shinri-solver/tests/qfufbv_e2e.rs` — create the file with the
`run_script` helper copied from `qfdt_model_e2e.rs:12-30` (the same helper, same
imports; Task 6 adds the rest of this file's tests):

```rust
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

/// Fence 1 (spec §4): an Int-sorted argument has no blastable word, so the
/// query fences to a SOUND `unknown` rather than reaching the congruence arm.
/// This is the spec §2.1 named decided → unknown exception.
#[test]
fn int_argument_to_a_bv_uf_fences_to_unknown() {
    let out = run_script(
        "(set-logic ALL)(declare-fun h (Int) (_ BitVec 8))(declare-fun n () Int)\
         (assert (= (h n) #x2a))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unknown"), "got {out:?}");
}
```

- [ ] **Step 7: Run the fence pin and the full fast suite**

```bash
cargo nextest run -p shinri-solver -E 'binary(qfufbv_e2e)'
cargo nextest run --all
```

Expected: the fence pin passes (1 test discovered in that binary); the full fast
suite is green. Any decided → `unknown` flip elsewhere must be an Int/Bool/
Array/String-argument case — record each one by name.

- [ ] **Step 8: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver/src/bv_stage.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/qfufbv_e2e.rs
git commit -m "fix(bv): slice44 T2 — fence uninterpreted BV applications with unwordable arguments

Fence 1 of the spec. Lands BEFORE the congruence arm: today's arm never
blasts its arguments, so an Int-sorted argument is harmless; once the arm
recurses into arguments it would reach Lowerer::word's unreachable! on a
non-BV/non-FP sort.

FP arguments are admitted only on the FP/mixed path, where the Lowerer's
word_eq can compare them with core_eq.

Named decided -> unknown flips (spec 2.1 exception): Int/Bool/Array/String/
uninterpreted-sorted arguments to a BV-result uninterpreted function."
```

---

### Task 3: The congruence arm

Replace the unconstrained-bits arm with Ackermann congruence, following
`shinri_fp::blast_fp_to_bv` (`crates/shinri-fp/src/lib.rs:289`–`:338`) — same
registry shape, same clause shape.

**Files:**
- Modify: `crates/shinri-bv/src/blast/mod.rs` (`UfApp` next to `FpToBvApp` at `:46`–`:57`; `WordSink` at `:63`–`:80`; `Blaster` struct at `:32`–`:38` and `Blaster::new` at `:83`; the arm at `:276`–`:288`)
- Test: `crates/shinri-bv/src/blast/mod.rs` (unit tests) and `crates/shinri-bv/src/lib.rs` (lowering tests, matching the existing `lower_tests` module)

**Interfaces:**
- Consumes: `uf_args_supported` from Task 2 (already fencing unwordable arguments).
- Produces:
  - `pub struct UfApp { pub sym: SymbolId, pub args: Vec<Vec<BitLit>>, pub result: Vec<BitLit> }`, `Clone`.
  - `WordSink::uf_apps(&mut self) -> &mut Vec<UfApp>`
  - `WordSink::word_eq(&mut self, ctx: &Context, sort: SortId, x: &[BitLit], y: &[BitLit]) -> BitLit`
  - Both re-exported from `shinri_bv` alongside `FpToBvApp`. Task 5 implements
    both on `Lowerer`.

- [ ] **Step 1: Write the failing test**

Add to `crates/shinri-bv/src/lib.rs`'s `lower_tests` module:

```rust
    /// Slice 44: two applications of one symbol to terms the CNF forces equal
    /// must have equal results. Encoded as: assert `x = y` and `f(x) != f(y)`;
    /// the CNF must be UNSAT. We check it structurally here — the clause count
    /// for the congruence must be non-zero — and end-to-end in qfufbv_e2e.
    #[test]
    fn congruence_clauses_are_emitted_for_two_applications() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let xf = ctx.declare_fun("x", &[], s8);
        let yf = ctx.declare_fun("y", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let fy = ctx.mk_app(Op::Uninterpreted(f), &[y]).unwrap();
        let a1 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fx, fy]).unwrap();

        let with_two = lower(&mut ctx, &[a1]).cnf.clauses.len();

        // A single application emits no congruence clauses at all.
        let mut ctx2 = Context::new();
        let s8b = ctx2.bv_sort(8);
        let f2 = ctx2.declare_fun("f", &[s8b], s8b);
        let xf2 = ctx2.declare_fun("x", &[], s8b);
        let x2 = ctx2.mk_app(Op::Uninterpreted(xf2), &[]).unwrap();
        let fx2 = ctx2.mk_app(Op::Uninterpreted(f2), &[x2]).unwrap();
        let c = ctx2.mk_bv_const(8, shinri_num::Integer::from(0u64));
        let a2 = ctx2.mk_app(Op::Builtin(BuiltinOp::Eq), &[fx2, c]).unwrap();
        let with_one = lower(&mut ctx2, &[a2]).cnf.clauses.len();

        assert!(
            with_two > with_one,
            "two applications of one symbol must emit congruence clauses \
             (two={with_two}, one={with_one})"
        );
    }

    /// The nullary arm is UNCHANGED: a nullary uninterpreted symbol is
    /// hash-consed to one TermId, so there is one word and nothing to make
    /// consistent. Pins that slice 44 adds no clauses to the pure-variable case.
    #[test]
    fn nullary_applications_emit_no_congruence_clauses() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let yf = ctx.declare_fun("y", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let lo = lower(&mut ctx, &[atom]);
        // 8 bits of xnor-and chain + the pinned var0 clause; the exact number is
        // whatever pre-slice-44 produced. Recorded here as an equality so any
        // future change to the nullary path is loud.
        assert_eq!(
            lo.cnf.clauses.len(),
            NULLARY_EQ_CLAUSES,
            "slice 44 must not change the nullary/pure-BV encoding"
        );
    }
```

Replace `NULLARY_EQ_CLAUSES` with the number measured in Step 2 — do not guess
it. Add it as a `const NULLARY_EQ_CLAUSES: usize = <measured>;` in the test
module with a comment naming the date it was measured.

- [ ] **Step 2: Run the tests to verify they fail, and measure the constant**

```bash
cargo nextest run -p shinri-bv -E 'test(congruence_clauses_are_emitted_for_two_applications)' --no-capture
cargo nextest run -p shinri-bv -E 'test(nullary_applications_emit_no_congruence_clauses)' --no-capture
```

Expected: the first FAILS (`two=N, one=N` — equal, because no congruence exists
yet, or a `debug_assert!` panic on `non-nullary uninterpreted BV fn out of
scope`). The second tells you the real clause count in its failure message; put
that number into `NULLARY_EQ_CLAUSES` and re-run so it passes **before** the arm
changes. That ordering is what makes it a genuine non-regression pin.

- [ ] **Step 3: Add `UfApp` and the two `WordSink` hooks**

In `crates/shinri-bv/src/blast/mod.rs`, add after `FpToBvApp` (`:57`):

```rust
/// One blasted non-nullary uninterpreted application (slice 44). Recorded by
/// the lowering driver so later applications of the SAME symbol can emit
/// Ackermann congruence: an uninterpreted function's only property is
/// functional consistency, so equal arguments must yield equal results.
#[derive(Clone)]
pub struct UfApp {
    pub sym: shinri_core::SymbolId,
    /// One blasted word per argument, in argument order.
    pub args: Vec<Vec<BitLit>>,
    pub result: Vec<BitLit>,
}
```

Extend the `WordSink` trait (`:63`–`:80`):

```rust
    /// Registry of blasted non-nullary uninterpreted applications, for
    /// Ackermann congruence (slice 44).
    ///
    /// UNLIKE `fp2bv_apps`, this has NO `unreachable!` default: pure-BV
    /// lowering is precisely where uninterpreted applications live, so every
    /// sink must carry a real store. A defaulted `unreachable!` here would be
    /// the slice-43 panic all over again.
    fn uf_apps(&mut self) -> &mut Vec<UfApp>;

    /// SMT-LIB **value** equality on two blasted words of `sort`.
    ///
    /// The default is bitwise, which is correct for every BV sort. `Lowerer`
    /// overrides it because SMT-LIB `FloatingPoint` has exactly ONE NaN value
    /// across many bit patterns, so bitwise equality would UNDER-trigger
    /// congruence on NaN arguments and leave results unconstrained where the
    /// semantics require them equal. `core_eq` lives in `shinri-fp`, which
    /// depends on `shinri-bv` and not the reverse — this hook is how the
    /// sort-aware comparison crosses the crate boundary.
    fn word_eq(
        &mut self,
        _ctx: &Context,
        _sort: shinri_core::SortId,
        x: &[BitLit],
        y: &[BitLit],
    ) -> BitLit {
        crate::blast::compare::eq(self.blaster(), x, y)
    }
```

Add the backing store to `Blaster` (`:32`–`:38`):

```rust
pub struct Blaster {
    next_var: u32,
    clauses: Vec<Vec<BitLit>>,
    drained: usize,
    /// Memoized blasted words: TermId -> LSB..MSB bit literals.
    pub(crate) cache: FxHashMap<TermId, Vec<BitLit>>,
    /// Blasted uninterpreted applications, for Ackermann congruence (slice 44).
    uf_apps: Vec<UfApp>,
}
```

and initialise it in `Blaster::new` (`:83`–`:94`), adding `uf_apps: Vec::new(),`
to the struct literal. Then in `impl WordSink for Blaster` (`:236`–`:248`):

```rust
    fn uf_apps(&mut self) -> &mut Vec<UfApp> {
        &mut self.uf_apps
    }
```

`Blaster` inherits the default `word_eq`, which is correct: Task 2's fence
admits FP arguments only on the FP path, so a `Blaster` never sees one.

Export it from `crates/shinri-bv/src/lib.rs:6`:

```rust
pub use blast::{blast_bv_atom, blast_bv_word, BitLit, Blaster, Cnf, FpToBvApp, UfApp, WordSink};
```

- [ ] **Step 4: Replace the arm**

In `blast_bv_word`, replace `:276`–`:288` entirely:

```rust
        TermNode::App {
            op: Op::Uninterpreted(sym),
            args,
            sort,
        } => {
            let child_ids = ctx.children(args).to_vec();
            let width = ctx.bv_width(sort).expect("BV-sorted variable has BV sort");
            if child_ids.is_empty() {
                // A nullary symbol is hash-consed to ONE TermId, so there is
                // exactly one word for it and nothing to make consistent.
                // Unchanged from the original dispatch.
                return (0..width).map(|_| sink.blaster().fresh()).collect();
            }
            // Blast the arguments FIRST. Step order is LOAD-BEARING: `f(f(x))`
            // registers the inner application while this call lowers its own
            // argument, and reading `prior` before that would silently drop the
            // inner/outer pair. The failure mode is missing congruence — a wrong
            // `sat` with no crash and no visible symptom — so it has its own
            // e2e test (`nested_application_congruence`).
            let arg_words: Vec<Vec<BitLit>> =
                child_ids.iter().map(|&k| sink.word(ctx, k)).collect();
            let result: Vec<BitLit> = (0..width).map(|_| sink.blaster().fresh()).collect();
            // Ackermann congruence against every prior application of the same
            // symbol. O(k²) in the per-formula application count; the caller
            // fences past a budget (bv_stage::uf_congruence_cost). Same clause
            // shape as shinri_fp::blast_fp_to_bv.
            let prior: Vec<UfApp> = sink
                .uf_apps()
                .iter()
                .filter(|a| a.sym == sym)
                .cloned()
                .collect();
            for pa in prior {
                debug_assert_eq!(
                    pa.args.len(),
                    arg_words.len(),
                    "same SymbolId at two arities — keying is wrong"
                );
                let mut cond = sink.blaster().one();
                for (k, aw) in arg_words.iter().enumerate() {
                    debug_assert_eq!(
                        pa.args[k].len(),
                        aw.len(),
                        "same SymbolId, differing argument width"
                    );
                    let sort_k = ctx.sort_of(child_ids[k]);
                    let e = sink.word_eq(ctx, sort_k, &pa.args[k], aw);
                    cond = sink.blaster().and2(cond, e);
                }
                let b = sink.blaster();
                let ncond = b.not1(cond);
                for i in 0..width as usize {
                    let d = b.xor2(pa.result[i], result[i]);
                    let nd = b.not1(d);
                    let imp = b.or2(ncond, nd);
                    b.add_clause(&[imp]); // cond → (res_prior[i] ↔ res_new[i])
                }
            }
            sink.uf_apps().push(UfApp {
                sym,
                args: arg_words,
                result: result.clone(),
            });
            result
        }
```

The `debug_assert!(child_ids.is_empty(), "non-nullary uninterpreted BV fn out of
scope")` is **deleted, not weakened** (success criterion 4).

- [ ] **Step 5: Run the unit tests to verify they pass**

```bash
cargo nextest run -p shinri-bv
```

Expected: both new tests PASS; `nullary_applications_emit_no_congruence_clauses`
still passes at its measured constant, proving the pure-BV encoding is
unchanged. Confirm a non-zero discovered count.

- [ ] **Step 6: Run Task 1's gate — it must now pass**

```bash
cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_bv_small)' --no-capture
```

Expected: PASS, 1 test discovered, with a non-zero `unsat=` count in the printed
summary. Record the summary line as a measurement (success criterion 2).

- [ ] **Step 7: Run the full fast suite**

```bash
cargo nextest run --all
```

Expected: green. Any newly-failing test is either a real regression or a
`should_panic` pin that Task 6 removes — `fenced_bv_field_panics_in_debug` in
`qfdt_model_e2e.rs` **will** fail here, because the panic it certifies is gone.
That is expected and is Task 6's work; note it and continue.

- [ ] **Step 8: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-bv/src/blast/mod.rs crates/shinri-bv/src/lib.rs
git commit -m "fix(bv): slice44 T3 — Ackermann congruence for uninterpreted BV applications

The Op::Uninterpreted arm minted fresh unconstrained bits per application
and related none of them, so x=y AND f(x)!=f(y) returned sat where z3 and
cvc5 both return unsat. Hash-consing supplied accidental congruence for
syntactically identical applications only.

Follows shinri_fp::blast_fp_to_bv's existing gadget: a per-sink UfApp
registry plus pairwise (args equal) -> (results equal) clauses. Arguments
are blasted BEFORE reading the registry so f(f(x)) pairs inner with outer.

Deletes the debug_assert! that made every affected query panic in dev
builds. The nullary arm is untouched and pinned clause-for-clause."
```

---

### Task 4: Fence 2 — the encoding blowup cap, calibrated

`pairs(k) = k(k−1)/2` constraints per symbol, each costing roughly
`arg_bits + result_bits` gate-equivalents. Unbounded, this hangs rather than
answers. The budget constant is **measured here, not guessed** — the spec
deliberately leaves it open because fixing a number without measuring is the
failure mode slice 42 was built on.

**Files:**
- Modify: `crates/shinri-solver/src/bv_stage.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (the same three call sites as Task 2)
- Test: `crates/shinri-solver/src/bv_stage.rs`, `crates/shinri-solver/tests/qfufbv_e2e.rs`

**Interfaces:**
- Consumes: `uf_args_supported` (Task 2); the congruence arm (Task 3).
- Produces: `pub fn uf_congruence_cost(ctx: &Context, atoms: &[TermId]) -> u64`
  and `pub const UF_CONGRUENCE_BUDGET: u64`.

- [ ] **Step 1: Write the failing unit test**

```rust
    #[test]
    fn uf_congruence_cost_is_quadratic_in_application_count() {
        // Three applications of one 1-ary 8-bit symbol: pairs(3) = 3, each
        // costing 8 argument bits + 8 result bits = 16. Expect 3 * 16 = 48.
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let mut atoms = Vec::new();
        let mut apps = Vec::new();
        for name in ["x", "y", "z"] {
            let vf = ctx.declare_fun(name, &[], s8);
            let v = ctx.mk_app(Op::Uninterpreted(vf), &[]).unwrap();
            apps.push(ctx.mk_app(Op::Uninterpreted(f), &[v]).unwrap());
        }
        atoms.push(ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[apps[0], apps[1]]).unwrap());
        atoms.push(ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[apps[1], apps[2]]).unwrap());
        assert_eq!(uf_congruence_cost(&ctx, &atoms), 48);
    }

    #[test]
    fn uf_congruence_cost_ignores_nullary_applications() {
        // Nullary symbols emit no congruence, so they must contribute zero.
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let yf = ctx.declare_fun("y", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        assert_eq!(uf_congruence_cost(&ctx, &[atom]), 0);
    }
```

- [ ] **Step 2: Run to verify they fail**

```bash
cargo nextest run -p shinri-solver -E 'test(uf_congruence_cost)'
```

Expected: FAIL to compile, `cannot find function uf_congruence_cost`.
Confirm 2 tests discovered once it compiles.

- [ ] **Step 3: Implement the cost model**

```rust
/// Fence 2 (slice 44 §4). Gate-equivalent cost of the Ackermann encoding for
/// every non-nullary uninterpreted BV-result application reachable from
/// `atoms`: for symbol `s` with `kₛ` applications, total argument width `Aₛ`
/// and result width `wₛ`, the encoding emits `pairs(kₛ) × (Aₛ + wₛ)` gates,
/// where `pairs(k) = k(k−1)/2`.
///
/// Nullary applications contribute zero: they emit no congruence at all.
///
/// FP-sorted arguments are counted at their full word width (eb + sb). That
/// UNDERCOUNTS slightly — `core_eq` unpacks both operands, so it costs more per
/// bit than the bitwise chain — which is the safe direction only if the budget
/// is calibrated against a real FP instance. Step 4 does that.
pub fn uf_congruence_cost(ctx: &Context, atoms: &[TermId]) -> u64 {
    let mut per_sym: FxHashMap<shinri_core::SymbolId, (u64, u64, u64)> = FxHashMap::default();
    let mut seen = rustc_hash::FxHashSet::default();
    for &a in atoms {
        collect_uf_apps(ctx, a, &mut per_sym, &mut seen);
    }
    let mut total: u64 = 0;
    for (_, (k, arg_bits, res_bits)) in per_sym {
        let pairs = k.saturating_mul(k.saturating_sub(1)) / 2;
        total = total.saturating_add(pairs.saturating_mul(arg_bits.saturating_add(res_bits)));
    }
    total
}

fn collect_uf_apps(
    ctx: &Context,
    t: TermId,
    per_sym: &mut FxHashMap<shinri_core::SymbolId, (u64, u64, u64)>,
    seen: &mut rustc_hash::FxHashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    let TermNode::App { op, args, sort } = ctx.term_node(t) else {
        return;
    };
    let kids = ctx.children(*args).to_vec();
    if let Op::Uninterpreted(sym) = op {
        if !kids.is_empty() {
            if let Some(res_bits) = ctx.bv_width(*sort) {
                let arg_bits: u64 = kids
                    .iter()
                    .map(|&k| {
                        let ks = ctx.sort_of(k);
                        ctx.bv_width(ks)
                            .map(u64::from)
                            .or_else(|| ctx.fp_widths(ks).map(|(eb, sb)| u64::from(eb + sb)))
                            .unwrap_or(0)
                    })
                    .sum();
                let e = per_sym.entry(*sym).or_insert((0, arg_bits, u64::from(res_bits)));
                e.0 += 1;
            }
        }
    }
    for &k in &kids {
        collect_uf_apps(ctx, k, per_sym, seen);
    }
}
```

- [ ] **Step 4: Calibrate the budget — this is a MEASUREMENT, not a guess**

Write a throwaway script under the scratchpad that emits QF_UFBV queries with
increasing `k` at width 32, arity 2 (so `Aₛ + wₛ = 96`):

```smt2
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
; k declared variables v0..v{k-1}, then k applications chained by equalities
```

Time `target/release/shinri` on `k = 10, 20, 40, 80, 160`. Find the largest `k`
whose solve stays **under 30 s**, then set:

```rust
/// Calibrated <DATE>: the largest encoding that solves in under 30 s on the
/// release binary, measured on a width-32 arity-2 symbol (Aₛ + wₛ = 96) with
/// k applications. Chosen so a single fenced query cannot consume the 10–15 min
/// PR-tier budget on its own. Recorded here rather than in the spec because it
/// is a measurement, not a design choice.
pub const UF_CONGRUENCE_BUDGET: u64 = <measured pairs(k) * 96>;
```

Record the full `k` → wall-clock table in the commit message. Success
criterion 5 requires it.

- [ ] **Step 5: Wire the cap into the same three call sites**

At each of the three sites Task 2 edited, add immediately after the
`uf_args_supported` check:

```rust
            if crate::bv_stage::uf_congruence_cost(&self.ctx, &bv_atoms)
                > crate::bv_stage::UF_CONGRUENCE_BUDGET
            {
                return SolveOutcome::Unknown;
            }
```

using `uf_atoms` on the FP/mixed path and `&assertions` on the ABV path, to
match what Task 2 passed at each site.

- [ ] **Step 6: Add the end-to-end cap pin**

Append to `crates/shinri-solver/tests/qfufbv_e2e.rs`:

```rust
/// Fence 2 (spec §4): an encoding past the calibrated budget fences to a SOUND
/// `unknown` rather than hanging. Generated rather than written out, because
/// the application count needed to exceed the budget is large by construction.
#[test]
fn encoding_past_the_budget_fences_to_unknown() {
    let k = 400; // pairs(400) * 96 is far past any plausible budget
    let mut src = String::from(
        "(set-logic QF_UFBV)\
         (declare-fun g ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))",
    );
    for i in 0..k {
        src.push_str(&format!("(declare-fun v{i} () (_ BitVec 32))"));
    }
    for i in 0..k {
        src.push_str(&format!("(assert (= (g v{i} v{i}) #x00000000))"));
    }
    src.push_str("(check-sat)");
    let out = run_script(&src);
    assert_eq!(out.first().map(|s| s.as_str()), Some("unknown"), "got {out:?}");
}
```

If `k = 400` proves slow enough to matter on the blocking tier, raise the
budget's *test* threshold by lowering `k` until the test runs in under a second
— the fence should trip before any blasting happens, so it should be near-
instant. If it is not, the cap is being checked too late; move it earlier.

- [ ] **Step 7: Run the tests**

```bash
cargo nextest run -p shinri-solver -E 'test(uf_congruence_cost)'
cargo nextest run -p shinri-solver -E 'binary(qfufbv_e2e)'
```

Expected: 2 + 3 tests discovered, all PASS. Time the second command; the cap
test must not dominate.

- [ ] **Step 8: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver/src/bv_stage.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/qfufbv_e2e.rs
git commit -m "fix(bv): slice44 T4 — cap the Ackermann encoding blowup

pairs(k) constraints per symbol is quadratic and unbounded; past the cap
the query fences to a sound unknown rather than hanging.

CALIBRATED <DATE> on the release binary, width-32 arity-2 symbol:
  k=10  -> <t>s
  k=20  -> <t>s
  k=40  -> <t>s
  k=80  -> <t>s
  k=160 -> <t>s
Budget set at pairs(<k>) * 96 = <value>, the largest encoding solving under
30s, so one fenced query cannot consume the 10-15 min PR tier alone.

Named decided -> unknown flips (spec 2.1 exception): queries whose
congruence encoding exceeds the budget."
```

---

### Task 5: The FP path — `Lowerer`'s hooks and NaN-aware comparison

`Lowerer` routes every BV-sorted node through `blast_bv_word`
(`crates/shinri-fp/src/lower.rs:47`–`:62`), so it hits Task 3's arm and needs
both hooks. Its `word_eq` must use `core_eq` for FP-sorted arguments: SMT-LIB
`FloatingPoint` has one NaN **value** across many bit patterns, so bitwise
equality would under-trigger congruence and leave results unconstrained where
the semantics require them equal.

**Files:**
- Modify: `crates/shinri-fp/src/lower.rs` (`Lowerer` struct `:8`–`:22`, `Lowerer::new` `:24`–`:32`, `impl WordSink for Lowerer` `:41`–`:82`)
- Modify: `crates/shinri-solver/tests/qfabv_oracle.rs`, `crates/shinri-solver/tests/fp_oracle.rs`
- Test: `crates/shinri-solver/tests/qfufbv_e2e.rs`

**Interfaces:**
- Consumes: `UfApp`, `WordSink::uf_apps`, `WordSink::word_eq` (Task 3);
  `shinri_fp::blast::compare::core_eq(b, x, y, eb, sb) -> BitLit`.
- Produces: nothing new; completes the trait surface.

- [ ] **Step 1: Write the failing e2e test**

Append to `crates/shinri-solver/tests/qfufbv_e2e.rs`:

```rust
/// The FP/mixed path shares blast_bv_word, so it had the identical defect.
/// MEASURED pre-slice: shinri `sat`, z3 `unsat`.
#[test]
fn fp_argument_congruence_on_the_mixed_path() {
    let out = run_script(
        "(set-logic ALL)(declare-fun k (Float32) (_ BitVec 8))\
         (declare-fun f () Float32)(declare-fun g () Float32)\
         (assert (= f g))(assert (distinct (k f) (k g)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// core_eq, not bitwise: SMT-LIB Float has ONE NaN value across many bit
/// patterns, so two NaN arguments must trigger congruence. A bitwise word_eq
/// leaves this `sat`.
#[test]
fn nan_arguments_trigger_congruence() {
    let out = run_script(
        "(set-logic ALL)(declare-fun k (Float32) (_ BitVec 8))\
         (declare-fun f () Float32)(declare-fun g () Float32)\
         (assert (fp.isNaN f))(assert (fp.isNaN g))\
         (assert (distinct (k f) (k g)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}
```

- [ ] **Step 2: Run to verify they fail**

```bash
cargo nextest run -p shinri-solver -E 'test(fp_argument_congruence_on_the_mixed_path) + test(nan_arguments_trigger_congruence)'
```

Expected: FAIL to compile (`Lowerer` does not implement `uf_apps`), since Task 3
made it a required trait method. If it compiles, `uf_apps` was given a default —
go back and remove it.

- [ ] **Step 3: Implement both hooks on `Lowerer`**

Add the field to the struct (`lower.rs:20`):

```rust
    // Uninterpreted-application registry for Ackermann congruence (slice 44).
    uf_apps: Vec<shinri_bv::UfApp>,
```

and to `Lowerer::new`'s struct literal:

```rust
            uf_apps: Vec::new(),
```

Add both impls inside `impl WordSink for Lowerer`:

```rust
    fn uf_apps(&mut self) -> &mut Vec<shinri_bv::UfApp> {
        &mut self.uf_apps
    }

    /// Sort-aware value equality. BV words compare bitwise; FP words compare
    /// with `core_eq`, because SMT-LIB `FloatingPoint` has exactly ONE NaN
    /// value across many bit patterns. A bitwise comparison would leave two
    /// NaN-valued arguments looking unequal, so congruence would not fire and
    /// the results would stay unconstrained — a wrong `sat`. This is the same
    /// judgment `blast_fp_to_bv` documents for FP→BV applications.
    fn word_eq(
        &mut self,
        ctx: &Context,
        sort: shinri_core::SortId,
        x: &[BitLit],
        y: &[BitLit],
    ) -> BitLit {
        if let Some((eb, sb)) = ctx.fp_widths(sort) {
            return crate::blast::compare::core_eq(&mut self.b, x, y, eb, sb);
        }
        shinri_bv::blast::compare::eq(&mut self.b, x, y)
    }
```

If `shinri_bv::blast::compare` is not public at that path, re-export `eq` from
`shinri-bv`'s `lib.rs` alongside the other `pub use` items rather than making
the whole module public.

- [ ] **Step 4: Run the tests to verify they pass**

```bash
cargo nextest run -p shinri-solver -E 'binary(qfufbv_e2e)'
```

Expected: 5 tests discovered, all PASS.

- [ ] **Step 5: Extend the ABV and FP oracle generators the same way**

Apply Task 1's edit shape to `crates/shinri-solver/tests/qfabv_oracle.rs` and
`crates/shinri-solver/tests/fp_oracle.rs`: declare a small uninterpreted symbol
pool over the sorts each generator already uses (BV for `qfabv_oracle`, Float
for `fp_oracle`'s BV-result conversions), add the corresponding pool arms, and
widen the op selector. Set each harness's logic string to the UF variant
(`QF_AUFBV`, `QF_UFFPBV`) so z3 accepts the declarations.

Read each generator's existing arm list before editing — as in Task 1, a
catch-all `_ =>` arm must be renumbered to its explicit index or the new arms
are unreachable and the extension silently does nothing.

- [ ] **Step 6: Run the FULL unfiltered oracle suite**

`blast_bv_word` is a shared primitive across BV, FP and ABV, so a filtered run
is not the gate. A filtered run nearly shipped a string `Sat`→`Unknown`
regression in slice 40.

```bash
cargo nextest run -p shinri-solver --features oracle
```

Expected: green, with a **non-zero discovered count** printed. Without
`--features oracle` these suites compile to zero tests and report green —
confirm the flag took effect by checking the count.

- [ ] **Step 7: Run `script_e2e` — this slice shifts completeness**

```bash
cargo nextest run -p shinri-solver -E 'binary(script_e2e)'
```

Expected: green. A z3-confirmed `unknown` → decided pin flip is an adjudicated
flip, not a blocker; confirm any such flip against z3 before accepting it. A
decided → `unknown` flip must be attributable to Task 2's or Task 4's fence.

- [ ] **Step 8: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-fp/src/lower.rs crates/shinri-solver/tests/qfufbv_e2e.rs crates/shinri-solver/tests/qfabv_oracle.rs crates/shinri-solver/tests/fp_oracle.rs
git commit -m "fix(fp): slice44 T5 — Lowerer carries the UF registry, compares FP args with core_eq

The FP/mixed path routes BV-sorted nodes through blast_bv_word, so it had
the identical missing-congruence defect: k(f) != k(g) with f = g over
Float32 returned sat where z3 returns unsat.

word_eq dispatches on sort because SMT-LIB Float has ONE NaN value across
many bit patterns — a bitwise comparison would leave two NaN arguments
looking unequal, congruence would not fire, and the results would stay
unconstrained.

qfabv_oracle and fp_oracle get Task 1's generator extension."
```

---

### Task 6: End-to-end pins, direction tests, and removing the panic certification

The direction tests are the ones that catch the likely bug: congruence is an
implication, not a biconditional, and inverting it silently turns `sat` into
`unsat`.

**Files:**
- Modify: `crates/shinri-solver/tests/qfufbv_e2e.rs`
- Modify: `crates/shinri-solver/tests/qfdt_model_e2e.rs:390`–`:448`

**Interfaces:**
- Consumes: everything from Tasks 2–5.
- Produces: the regression surface for this slice.

- [ ] **Step 1: Write the regression pins for every measured wrong answer**

Append to `crates/shinri-solver/tests/qfufbv_e2e.rs`. Each verdict below was
measured against z3, and the first two against cvc5 as well:

```rust
/// The canonical case. MEASURED pre-slice: shinri `sat`; z3 `unsat`; cvc5 `unsat`.
#[test]
fn one_ary_congruence() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (assert (= x y))(assert (distinct (f x) (f y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// Two-ary with the arguments permuted — congruence must compare argument
/// words POSITIONALLY, not as a set. A position-blind encoding leaves this sat.
#[test]
fn two_ary_congruence_with_permuted_arguments() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun g ((_ BitVec 4)(_ BitVec 4)) (_ BitVec 4))\
         (declare-fun a () (_ BitVec 4))(declare-fun b () (_ BitVec 4))\
         (assert (= a b))(assert (distinct (g a b) (g b a)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// The congruence must reach a BV PREDICATE over two applications, not just an
/// equality between them.
#[test]
fn congruence_reaches_a_bv_predicate() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (= x y))(assert (bvult (f x) (f y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// ...and through a structural op applied to the results.
#[test]
fn congruence_survives_extract_over_the_results() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 8))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (= x y))\
         (assert (distinct ((_ extract 3 0) (f x)) ((_ extract 3 0) (f y))))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// The ABV stage builds its own Blaster, so it hits the same arm.
/// MEASURED pre-slice: shinri `sat`; z3 `unsat`; cvc5 `unsat`.
#[test]
fn congruence_on_the_abv_path() {
    let out = run_script(
        "(set-logic QF_AUFBV)(declare-fun a () (Array (_ BitVec 4)(_ BitVec 8)))\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-fun i () (_ BitVec 4))(declare-fun j () (_ BitVec 4))\
         (assert (= i j))(assert (distinct (f (select a i)) (f (select a j))))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}
```

- [ ] **Step 2: Write the direction tests — both must be `sat`**

```rust
/// DIRECTION TEST. Congruence is an IMPLICATION, not a biconditional. An
/// over-strong encoding (`args equal <-> results equal`) makes this `unsat`.
/// It must be `sat`: nothing forbids a function from differing on differing
/// arguments.
#[test]
fn distinct_arguments_may_give_distinct_results() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (distinct x y))(assert (distinct (f x) (f y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// THE SHARPER DIRECTION TEST. A function may legitimately AGREE on distinct
/// arguments. An inverted encoding (`args differ -> results differ`) fails
/// exactly here and nowhere else — the test above would still pass under it.
#[test]
fn distinct_arguments_may_still_give_equal_results() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (distinct x y))(assert (= (f x) (f y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// Pins Task 3's load-bearing step order: the inner application is registered
/// while the outer one's argument is lowered, so `prior` must be read AFTER
/// argument blasting. Reading it first drops the inner/outer pair and this
/// returns `sat` — silent incompleteness, no crash, no other symptom.
#[test]
fn nested_application_congruence() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (= x y))(assert (distinct (f (f x)) (f (f y))))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}
```

- [ ] **Step 3: Run them**

```bash
cargo nextest run -p shinri-solver -E 'binary(qfufbv_e2e)'
```

Expected: 13 tests discovered, all PASS. If
`distinct_arguments_may_still_give_equal_results` fails, the implication is
inverted — fix Task 3's arm, do not weaken the test.

- [ ] **Step 4: Remove the panic certification**

In `crates/shinri-solver/tests/qfdt_model_e2e.rs`, delete
`fenced_bv_field_panics_in_debug` (`:427`–`:432`) together with its
`#[cfg(debug_assertions)]` attribute, and rewrite the doc comment block above
`BV_FIELD` (`:390`–`:420`) so it no longer describes a debug panic or a
`#[should_panic]` sibling.

Then **re-measure** the release sibling rather than assuming its value. Run:

```bash
cargo build --release -p shinri-cli
printf '%s\n' '(set-logic QF_UFDTBV)(declare-datatype W ((mk (w (_ BitVec 8)))))(declare-fun v () W)(assert (= (w v) #x2a))(check-sat)(get-model)' > /tmp/claude-1000/-workspace/*/scratchpad/bvfield.smt2
./target/release/shinri /tmp/claude-1000/-workspace/*/scratchpad/bvfield.smt2
```

Replace `fenced_bv_field_is_a_placeholder_in_release` with a single
profile-independent test asserting exactly what that command prints, renamed to
describe the shipped behaviour (e.g. `bv_field_after_congruence`). Drop both
`cfg(debug_assertions)` gates — with the panic gone, both profiles agree, and
the sibling pair existed only to document the divergence.

- [ ] **Step 5: Run the DT model suite**

```bash
cargo nextest run -p shinri-solver -E 'binary(qfdt_model_e2e)'
```

Expected: green, with a non-zero discovered count. Confirm no
`#[should_panic]` for `"non-nullary uninterpreted BV fn out of scope"` survives
anywhere:

```bash
grep -rn "non-nullary uninterpreted BV fn out of scope" crates/
```

Expected: **no output** (success criterion 4).

- [ ] **Step 6: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver/tests/qfufbv_e2e.rs crates/shinri-solver/tests/qfdt_model_e2e.rs
git commit -m "test(bv): slice44 T6 — pin every measured wrong answer, and the encoding direction

Six regression pins, one per measured shinri/z3 disagreement: 1-ary,
2-ary with permuted arguments, bvult over two applications, extract over
the results, the Float32 case on the FP path, and the QF_AUFBV case.

Two direction tests, both asserting SAT. Congruence is an implication, not
a biconditional; the sharper of the two (distinct args, EQUAL results)
fails under an inverted encoding where the other would still pass. Plus
f(f(x)) to pin Task 3's load-bearing step order.

Deletes fenced_bv_field_panics_in_debug, which certified a wrong-sat bug
as expected behaviour, and collapses its cfg-gated release sibling now that
both profiles agree."
```

---

### Task 7: Model side effect, cost non-regression, and reconciling slice 43's spec

Two measurements to pin and one committed spec to stop contradicting the code.

**Files:**
- Modify: `crates/shinri-solver/tests/qfufbv_e2e.rs`
- Modify: `docs/superpowers/specs/2026-07-25-shinri-slice43-model-channel-design.md:285`
- Modify: `docs/superpowers/specs/2026-07-27-shinri-slice44-uf-bv-congruence-design.md` (measured-outcomes section)

**Interfaces:**
- Consumes: everything from Tasks 2–6.
- Produces: the slice's recorded outcomes.

- [ ] **Step 1: Measure the model side effect**

Today's arm never calls `sink.word` on its children, so an argument variable is
never blasted and never reaches `exported_var_bits` (which filters
`Blaster.cache`). Congruence forces the arguments to be blasted, so the value
should now appear. **Measure it — do not assume the format:**

```bash
printf '%s\n' '(set-logic QF_UFBV)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(declare-fun x () (_ BitVec 8))(assert (= (f x) #x2a))(check-sat)(get-model)' > /tmp/claude-1000/-workspace/*/scratchpad/model.smt2
./target/release/shinri /tmp/claude-1000/-workspace/*/scratchpad/model.smt2
```

- [ ] **Step 2: Pin exactly what it printed**

Append to `crates/shinri-solver/tests/qfufbv_e2e.rs`, substituting the measured
string:

```rust
/// Spec §2.2: a MEASURED SIDE EFFECT, not a goal. Pre-slice this printed
/// `(define-fun x () (_ BitVec 8) ?)` — the argument was never blasted, so it
/// never entered Blaster.cache and exported_var_bits could not see it.
/// Congruence forces the arguments to be blasted, so the value appears.
///
/// This does NOT make get-model complete for UF queries: `f` itself is still
/// omitted, because a function graph needs EUF congruence-class enumeration
/// (slice 43 §5, still open).
#[test]
fn argument_variables_now_get_a_model_value() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-fun x () (_ BitVec 8))(assert (= (f x) #x2a))(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    // MEASURED <DATE>, release binary — substitute the exact printed line.
    assert_eq!(out[1], "<MEASURED MODEL STRING>");
    assert!(
        !out[1].contains('?'),
        "the argument variable must have a real value, not a placeholder: {}",
        out[1]
    );
}
```

The `assert!` on `'?'` is the load-bearing half: it survives any later change to
the exact formatting, whereas the `assert_eq!` documents today's output.

- [ ] **Step 3: Measure and pin the cost non-regression**

The nullary arm is untouched, so a query with no non-nullary uninterpreted
applications must produce a clause-for-clause identical CNF.
`nullary_applications_emit_no_congruence_clauses` (Task 3) already pins the
unit-level case at its pre-slice constant. Confirm it still passes and record
the PR-tier wall clock:

```bash
cargo nextest run -p shinri-bv -E 'test(nullary_applications_emit_no_congruence_clauses)'
time cargo nextest run --all
```

Expected: PASS; total under the 10–15 min budget. Record the wall clock.

- [ ] **Step 4: Rewrite slice 43's contradicting spec row**

`docs/superpowers/specs/2026-07-25-shinri-slice43-model-channel-design.md:285`
currently states the BV-field gap is fenced, that the debug build panics, and
that both halves are pinned by cfg-gated sibling tests. All three are now false.
Replace the row's Disposition cell with a statement of what shipped: the
congruence arm decides these queries, the `debug_assert!` and its
`#[should_panic]` are gone, and the surviving gap is the DT-side one — `v`
itself is unvalued because DT contributes nothing on the pure-BV path. Reference
this slice's spec by path.

Do **not** rewrite history or edit the row's original diagnosis; add the
correction so the two specs read as a sequence, matching how slice 43's own
spec corrected slice 42's §3.A claim.

- [ ] **Step 5: Record measured outcomes in this slice's spec**

Add a `## 7. Measured outcomes` section to
`docs/superpowers/specs/2026-07-27-shinri-slice44-uf-bv-congruence-design.md`
containing: Task 1's pre-fix oracle failure (iteration, verdicts, reproducer);
Task 3's post-fix oracle summary line; Task 4's full `k` → wall-clock
calibration table and the chosen budget; the complete list of named
fence-attributable decided → `unknown` flips; the Task 2 model string; and the
PR-tier wall clock. Success criteria 2, 3 and 5 are satisfied by this section
existing and being accurate.

- [ ] **Step 6: Run the complete gate set one final time**

```bash
mise run lint
cargo nextest run --all
cargo nextest run -p shinri-solver --features oracle
cargo nextest run -p shinri-solver -E 'binary(script_e2e)'
```

Every command must be green **with a non-zero discovered count**. The oracle
run without `--features oracle` compiles to zero tests and reports green — if
the count looks suspiciously low, the flag did not take effect.

- [ ] **Step 7: Format, lint, commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver/tests/qfufbv_e2e.rs docs/superpowers/specs/
git commit -m "docs(bv): slice44 T7 — record measured outcomes, reconcile slice 43's spec

Pins the model side effect: blasting the arguments for congruence puts them
in Blaster.cache, so exported_var_bits finds them and an argument variable
gets a real value where it printed ? before. This does NOT complete
get-model for UF queries — arity>0 symbols are still omitted.

Slice 43 spec 5's BV row said the gap was fenced, the debug build panicked,
and cfg-gated siblings pinned both halves. All three are now false; the row
is corrected in place so the two specs read as a sequence."
```

---

## Self-Review

**Spec coverage.**

| Spec section | Task |
|---|---|
| §1 the defect + six measured wrong answers | 3 (fix), 6 (pins) |
| §1 why it survived — the generator | 1 |
| §2 scope: three paths | 3 (BV, ABV), 5 (FP) |
| §2.1 verdict invariant + named fence exceptions | 2, 4 (named in commits), 7 (recorded) |
| §2.2 `#[should_panic]` removal | 6 |
| §2.2 model side effect | 7 |
| §3.1 `UfApp`, `uf_apps`, `word_eq`, real store on `Blaster` | 3 |
| §3.1 `core_eq` for FP, crate-boundary reasoning | 5 |
| §3.2 the arm, load-bearing step order | 3 (impl), 6 (`nested_application_congruence`) |
| §4 fence 1 argument sort | 2 |
| §4 fence 2 blowup cap, calibrated not guessed | 4 |
| §5.1 generator gate, must fail pre-fix, full unfiltered oracle | 1, 3 (step 6), 5 (steps 5–7) |
| §5.2 six regression pins | 6 |
| §5.3 two direction tests + nested | 6 |
| §5.4 fence pins, cap pin, model pin, `should_panic` gone | 2, 4, 6, 7 |
| §5.5 cost non-regression | 3 (constant), 7 (confirm) |
| §6 criteria 1–6 | 6, 1/3/5, 2/4/7, 6, 4/7, 7 |

No gaps.

**Placeholder scan.** Four values are deliberately measured rather than written,
each with an explicit measurement step that produces it:
`NULLARY_EQ_CLAUSES` (Task 3 Step 2), `UF_CONGRUENCE_BUDGET` and its `k` table
(Task 4 Step 4), and the model string (Task 7 Steps 1–2). These are measurements
by design — the spec says so for the budget, and guessing the others would
defeat their purpose as pins. No other placeholders.

**Type consistency.** `uf_args_supported(ctx, atoms, allow_fp_args) -> bool`,
`uf_congruence_cost(ctx, atoms) -> u64`, `UF_CONGRUENCE_BUDGET: u64`,
`UfApp { sym: SymbolId, args: Vec<Vec<BitLit>>, result: Vec<BitLit> }`,
`uf_apps(&mut self) -> &mut Vec<UfApp>`, and
`word_eq(&mut self, &Context, SortId, &[BitLit], &[BitLit]) -> BitLit` are used
identically in every task that references them. `SymbolId` is
`Copy + PartialEq + Eq + Hash` (`crates/shinri-core/src/ids.rs:45`–`:63`), so
the `filter(|a| a.sym == sym)` and the `FxHashMap` key both compile.
