# Slice 44 — Congruence for uninterpreted applications in the bit-blaster

**Status:** design
**Date:** 2026-07-27
**Area:** `shinri-bv` (`blast::blast_bv_word`'s `Op::Uninterpreted` arm, the
`WordSink` trait, `Blaster`), `shinri-fp` (`Lowerer`'s two new hook impls),
`shinri-solver` (`bv_stage`/`fp_stage` pre-lowering fences; three oracle
generators). No new crate, no new theory slot, no parser surface change, no
`Combiner` change.
**Predecessors:** the defect dates to `e437ba41` (the original BV blast
dispatch), not to slices 39–43. Slice 43 §5 recorded the debug panic as a
DT-specific fenced gap and pinned it with a `#[should_panic]` test; this slice
shows it is neither DT-specific nor merely a panic, and removes both.

## 1. Summary

`blast_bv_word`'s uninterpreted-application arm
(`crates/shinri-bv/src/blast/mod.rs:276`–`:288`) mints `width` **fresh,
unconstrained** bits per application and asserts nothing relating one
application to another:

```rust
TermNode::App { op: Op::Uninterpreted(_), args, sort } => {
    let child_ids = ctx.children(args).to_vec();
    debug_assert!(child_ids.is_empty(), "non-nullary uninterpreted BV fn out of scope");
    let width = ctx.bv_width(sort).expect("BV-sorted variable has BV sort");
    (0..width).map(|_| sink.blaster().fresh()).collect()
}
```

Functional consistency is therefore lost: two applications of one symbol to
provably-equal arguments get independent bit vectors. `Blaster.cache` is keyed
by `TermId`, so hash-consing supplies *accidental* congruence for syntactically
identical applications only — which is why `f(x) ≠ f(x)` is correctly `unsat`
while `f(x) ≠ f(y) ∧ x = y` is wrong.

Measured, release binary, against both oracles from `mise`:

| Query | shinri | z3 | cvc5 | |
|---|---|---|---|---|
| `x=y ∧ f(x)≠f(y)`, 1-ary BV→BV, `QF_UFBV` | `sat` | `unsat` | `unsat` | **wrong** |
| `a=b ∧ g(a,b)≠g(b,a)`, 2-ary | `sat` | `unsat` | — | **wrong** |
| `x=y ∧ bvult (f x) (f y)` | `sat` | `unsat` | — | **wrong** |
| `x=y ∧ extract(f x) ≠ extract(f y)` | `sat` | `unsat` | — | **wrong** |
| `f=g ∧ k(f)≠k(g)`, Float32→BV (FP path) | `sat` | `unsat` | — | **wrong** |
| the 1-ary case under `QF_AUFBV` (ABV path) | `sat` | `unsat` | `unsat` | **wrong** |
| `x=y ∧ p(x) ∧ ¬p(y)`, BV→**Bool** | `unknown` | `unsat` | — | sound, incomplete |
| `x=y ∧ k(x)≠k(y)`, BV→**FP** | `unknown` | `unsat` | — | sound, incomplete |

In dev/test builds — the tier `mise run test` and CI actually gate on — every
wrong row instead **panics** on the `debug_assert!` above, before `check-sat`
returns.

**Why this survived.** `qfbv_oracle`'s generator (`gen_instance`,
`crates/shinri-solver/tests/qfbv_oracle.rs:89`) builds its term pool from
builtin BV operators over declared **nullary** variables — `op_kind =
rng.below(19)`, every arm a `BuiltinOp::Bv*`. It cannot emit an uninterpreted
application, so the differential oracle was structurally incapable of
generating the triggering shape. That is a finding about the test suite, and
task 1 acts on it before anything else.

**The fix, and its precedent.** This codebase already implements exactly this
gadget one crate up: `shinri_fp::blast_fp_to_bv`
(`crates/shinri-fp/src/lib.rs:289`–`:338`) gives `fp.to_ubv`/`fp.to_sbv`
applications bit-level Ackermann congruence — a per-sink registry of prior
applications, pairwise `(operands equal) → (results equal)` clauses, O(k²) with
a comment saying so. `WordSink` already carries `fp2bv_apps()` for it
(`blast/mod.rs:74`–`:79`). Slice 44 applies that same gadget to
`Op::Uninterpreted`.

## 2. Scope and invariant

**In scope.** Uninterpreted applications whose **result sort is BitVec**, on the
three paths that share the arm: pure-BV (`shinri_bv::lower`,
`crates/shinri-bv/src/lib.rs:31`), FP/mixed (`shinri-fp`'s `Lowerer`, which
routes every BV-sorted node through `blast_bv_word`), and ABV — whose debug
panic on the same query is measured, so the arm is provably reachable there.

**Out of scope, deliberately unchanged.** Bool-result and FP-result
applications, which already fence to `unknown` — sound but incomplete, and left
that way. The two fence by different mechanisms, worth recording so neither is
disturbed: a Bool-result application `p(x)` is not collected by
`collect_bv_atoms` (it is no BV predicate), so `has_non_bv_theory_atom`
(`crates/shinri-solver/src/bv_stage.rs:177`) sees a non-Boolean-structure atom
outside the BV set and fences; an FP-result application routes to the FP path
instead, where `is_supported_fp_word` rejects an uninterpreted FP-sorted word
and `fp_atoms_fully_supported` (`fp_stage.rs:767`) fences. BV ⋈ Int/String/DT
stays fenced; BV is still
not a combinable theory. `get-model` still omits arity > 0 symbols, so it
remains an incomplete model for UF queries (slice 43 §5).

### 2.1 The invariant — the mirror of slice 43's

Slice 43 could not change a verdict. This slice **must**, but only in one
direction:

- **Permitted:** `sat` → `unsat` (the defect's signature), and `unknown` →
  decided.
- **Regression:** any `unsat` → `sat`, and any decided → `unknown`.
- **One exception**, and it must be *named in advance rather than discovered*:
  a query newly caught by §4's argument-sort fence or blowup cap goes decided →
  `unknown`. Every such flip is listed individually with its cause; an
  unattributed one is a regression.

The gates are `qfbv_witnesses`, `script_e2e`, `qfdt_e2e`, and the full
unfiltered oracle suite (§5).

### 2.2 Two consequences to record, not discover

**The `#[should_panic]` certification goes.** `fenced_bv_field_panics_in_debug`
(`crates/shinri-solver/tests/qfdt_model_e2e.rs:430`) currently asserts the crash
is expected behaviour. It is deleted together with the `debug_assert!` it
certifies, and slice 43's spec §5 BV row is **rewritten** rather than left
contradicting the code. Its release sibling
`fenced_bv_field_is_a_placeholder_in_release` is re-measured, not assumed: the
DT/BV query stays `unknown`-free but `v` itself is still unvalued, because DT
contributes nothing on the pure-BV path.

**A model-channel improvement falls out.** Today's arm never calls `sink.word`
on its children, so an argument variable is never blasted, never enters
`Blaster.cache`, and is therefore invisible to `exported_var_bits`
(`blast/mod.rs:215`, which filters the cache). Measured today,
`(assert (= (f x) #x2a))` in `QF_UFBV` yields `sat` with
`(define-fun x () (_ BitVec 8) ?)`. Congruence *requires* blasting the
arguments, so `x` lands in the cache and gets a real value. This is a **measured
side effect to pin**, not a goal, and it does not make `get-model` complete for
UF queries — `f` itself is still omitted.

## 3. The gadget

### 3.1 Registry and comparison, as `WordSink` hooks

```rust
pub struct UfApp {
    pub sym: SymbolId,
    pub args: Vec<Vec<BitLit>>,   // one blasted word per argument, in order
    pub result: Vec<BitLit>,
}

trait WordSink {
    fn uf_apps(&mut self) -> &mut Vec<UfApp>;
    /// SMT-LIB *value* equality on two blasted words of `sort`.
    fn word_eq(&mut self, ctx: &Context, sort: SortId, x: &[BitLit], y: &[BitLit]) -> BitLit;
}
```

One difference from `fp2bv_apps` matters. That hook defaults to `unreachable!`
because pure-BV lowering has no FP→BV conversions. **`uf_apps` gets a real
backing store on `Blaster` as well as on `Lowerer`** — pure-BV lowering is
precisely where uninterpreted applications live, so an `unreachable!` default
would be the panic all over again.

`word_eq` exists because `core_eq` lives in `shinri-fp`, which depends on
`shinri-bv` and not the reverse, so `blast_bv_word` cannot call it directly.
The hook carries the sort-aware comparison to the sink that understands the
sort:

- `Blaster::word_eq` → `compare::eq` (`crates/shinri-bv/src/blast/compare.rs:3`),
  the existing bitwise chain. A `Blaster` only ever sees BV-sorted arguments,
  since §4's fence admits FP arguments on the FP path alone.
- `Lowerer::word_eq` → dispatch on sort: BV → `compare::eq`; FP →
  `shinri_fp::blast::compare::core_eq`. FP needs it because SMT-LIB
  `FloatingPoint` has exactly **one NaN value** across many bit patterns, so
  bitwise equality would under-trigger congruence on NaN arguments — leaving
  the results unconstrained where the SMT semantics require them equal. This is
  the identical judgment `blast_fp_to_bv` already documents at `lib.rs:285`–`:287`.

Applications are keyed on `SymbolId` alone: one `declare-fun` is one signature.
A `debug_assert!` checks that paired applications agree on arity and on each
argument's width, so a keying mistake is loud rather than silently unsound.

### 3.2 The arm

Nullary applications are **unchanged**: hash-consing gives one `TermId` per
nullary symbol, so there is exactly one word and nothing to make consistent.

Non-nullary applications become:

1. Blast every argument via `sink.word(ctx, child)`.
2. Mint the `width` result bits via `sink.blaster().fresh()` — still
   unconstrained in themselves; that is Ackermann's reduction, and the only
   property an uninterpreted function has is functional consistency.
3. For each prior registered application of the same `SymbolId`, emit
   `(⋀ₖ word_eq(argₖ)) → (resᵢ ↔ resⱼ)` — the clause shape of
   `blast_fp_to_bv:314`–`:331`.
4. Push this application onto `uf_apps()`.

**Step order is load-bearing.** `prior` must be read *after* step 1, not before.
`f(f(x))` blasts the inner application while lowering the outer one's argument,
which registers the inner application; reading `prior` first would silently drop
the inner/outer pair. That failure mode is missing congruence — an
incompleteness that produces a wrong `sat`, with no crash and no visible
symptom — so §5 pins it with its own test rather than letting it ride on the
others.

**Why the reduction is sound and complete here.** Ackermann's reduction is
equisatisfiable for an uninterpreted symbol provided every pair of its
applications is constrained. `WordSink::word` memoizes per `TermId`, so each
distinct application is blasted at most once and pushed at most once; each new
application is paired against every earlier one; therefore every pair is
covered. Applications not reachable from the blasted atom set never enter the
CNF at all and need no constraint.

## 4. Two fences, both before lowering

Both follow the discipline already established by `fp_atoms_fully_supported` and
`bv_atoms_fp_supported` (`crates/shinri-solver/src/fp_stage.rs:767`, `:746`):
fence *ahead of* lowering, so the blast arms' `unreachable!`s stay internal
invariants rather than reachable states.

**Fence 1 — argument sort.** Every argument of every non-nullary uninterpreted
BV-result application must have a blastable word: BV-sorted always; FP-sorted
**only on the FP path**, where a `Lowerer` exists to compare it. Int-, Bool-,
Array-, String-, uninterpreted- and RoundingMode-sorted arguments fence to a
sound `unknown`. Without this fence, `Lowerer::word` reaches its
`unreachable!("Lowerer::word on non-BV/non-FP sort")`
(`crates/shinri-fp/src/lower.rs:69`).

**Fence 2 — blowup cap.** For symbol *s* with *kₛ* applications, total argument
width *Aₛ* and result width *wₛ*, the encoding costs
`pairs(kₛ) × (Aₛ + wₛ)` gate-equivalents, where `pairs(k) = k(k−1)/2`. Fence to
`unknown` when `Σₛ pairs(kₛ) × (Aₛ + wₛ)` exceeds a budget.

**The budget constant is deliberately not fixed in this spec.** It is
calibrated in task 1 against the 10–15 min PR-tier budget and recorded as a
measurement, the way slices 42 and 43 recorded theirs. Fixing a number here
without measuring is the failure mode slice 42 was built on.

**Both fences walk the collected atom set**, not the assertion list — that is
exactly what reaches the blaster. It remains a superset of what survives
`rewrite` (`shinri-bv/src/lib.rs:35`), since rewriting can fold applications
away but never create them, so the conservative bias every other fence in this
stage has is preserved.

Fence 1 needs a per-path parameter (FP arguments admitted only where an FP sink
exists); everything else is shared between `bv_stage` and `fp_stage`.

## 5. Testing

### 5.1 The gate goes first, and the gate is the generator

Slice 42 implemented its plan exactly and delivered zero, because only a
measured end-to-end gate could catch its premise. Here the premise is already
measured — but the *suite* is what failed, so task 1 fixes the suite and proves
it fails before any fix lands.

Task 1 extends `qfbv_oracle`'s term pool with uninterpreted symbols over BV:
arity 1–2, a **small** symbol pool so applications collide, arguments drawn from
the existing pool so congruence triggers actually fire. The same extension goes
to `qfabv_oracle` and `fp_oracle` — the FP path's wrong `sat` is measured and
real.

**The extended generators must fail on pre-slice `main`.** A generator that
passes before the fix is not generating the shape, and its later green is
meaningless. That failure is recorded as a measurement.

`blast_bv_word` is a **shared primitive** across BV, FP and ABV, so the gate is
the **full unfiltered oracle run** — `cargo nextest run -p shinri-solver
--features oracle` with no test filter. A filtered run nearly shipped a string
`Sat`→`Unknown` regression in slice 40. Without `--features oracle` the suite
compiles to zero tests, and a zero-test run reads as green. Because the slice
shifts completeness, `script_e2e` runs locally before pushing.

### 5.2 Regression pins for the measured wrong answers

One e2e pin per §1 wrong row, each asserting the oracle's verdict: 1-ary; 2-ary
with argument permutation; `bvult` over two applications; `extract` over two
applications; the Float32→BV case on the FP path; the `QF_AUFBV` case through
the ABV stage.

### 5.3 Direction tests — the ones that catch the likely bug

Congruence is an implication, not a biconditional, and inverting it silently
turns `sat` into `unsat`. Both of these must be **`sat`**:

- `f(x) ≠ f(y) ∧ x ≠ y` — an over-strong encoding (biconditional) makes this
  `unsat`.
- `f(x) = f(y) ∧ x ≠ y` — sharper: a function may legitimately agree on
  distinct arguments, so an "arguments differ → results differ" inversion fails
  exactly here and nowhere else.

And `f(f(x)) ≠ f(f(y)) ∧ x = y` → `unsat`, pinning §3.2's step order.

### 5.4 Fence and side-effect pins

- An Int-argument application → `unknown`: not a panic, not a wrong answer.
- A query past the blowup cap → `unknown`, with the calibrated cap recorded.
- The §2.2 model side effect: the measured `get-model` string for
  `(assert (= (f x) #x2a))`, which prints `?` for `x` today.
- `fenced_bv_field_panics_in_debug` deleted; no `#[should_panic]` certifying
  that message survives anywhere in the workspace.

### 5.5 Cost non-regression

A query with no non-nullary uninterpreted applications must be clause-for-clause
unchanged. The nullary arm is untouched, and a CNF-size assertion on a pure-BV
instance **proves** that rather than asserting it in prose.

## 6. Success criteria

1. All six §1 wrong-answer queries decide correctly, agreeing with **both** z3
   and cvc5.
2. The extended `qfbv_oracle` / `qfabv_oracle` / `fp_oracle` generators fail on
   pre-slice `main` and pass after; both results recorded as measurements.
3. No `unsat` → `sat` and no decided → `unknown` flip across `qfbv_witnesses`,
   `script_e2e`, `qfdt_e2e` and the full unfiltered oracle suite — except flips
   attributable to §4's two fences, each named individually with its cause.
4. The `debug_assert!` at `crates/shinri-bv/src/blast/mod.rs:282` is **deleted,
   not weakened**, and no `#[should_panic]` certifies it anywhere.
5. The PR tier stays inside its 10–15 min budget with the cap at its calibrated
   value, and the calibration measurement is recorded.
6. Slice 43's spec §5 BV row is rewritten to match the shipped behaviour, so no
   committed spec contradicts the code.

## 7. Measured outcomes

### 7.1 Task 1 — the pre-fix oracle failure

Extending `qfbv_oracle`'s term pool with a 1-ary `f` and a 2-ary `g` (small pool
so applications collide) made `differential_qf_bv_small` reach the missing-
congruence defect for the first time. The failure did **not** manifest as a
`shinri=Sat z3=Unsat` verdict-disagreement pair — the process panicked before
either solver reported a verdict for that iteration, so no pair exists to
record:

```
cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_bv_small)' --no-capture
```

discovers 1 test and **panics** at `crates/shinri-bv/src/blast/mod.rs:282`:
`debug_assert!(child_ids.is_empty(), "non-nullary uninterpreted BV fn out of
scope")`, since the dev/test profile builds with debug assertions on. Pinned
to **iteration 3 (0-indexed), width 4** (a temporary `eprintln!` used to locate
it, reverted before the commit — commit `e0d8af06`). The reviewer independently
verified the causal chain: only the newly-added generator arms can construct a
non-nullary `Op::Uninterpreted` node, so nothing else could have triggered this
assertion.

### 7.2 Task 3 — the post-fix oracle summary

After the congruence gadget landed (commit `4acf7903`):

```
differential_qf_bv_small PASS, sat=116 unsat=84 unknown=0 disagreements=0
```

Full unfiltered oracle: **572 passed / 3 skipped**. Full workspace suite:
**1307 passed / 7 skipped** (baseline 1303 + 4 new tests).

### 7.3 Task 4 — the `k` → wall-clock calibration table and the chosen budget

Measured on the release binary, single run each, foreground `bash time`, on a
width-32 arity-2 symbol (`Aₛ + wₛ = 96`): `(set-logic QF_UFBV) (declare-fun g
((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))`, `k` fresh `BitVec 32` variables,
`k` applications `g(vᵢ,vᵢ)` chained pairwise.

| k | wall-clock |
|---|---|
| 10 | 0.013 s |
| 20 | 0.050 s |
| 40 | 0.206 s |
| 80 | 0.843 s |
| 160 | 3.484 s |
| 320 | 15.429 s |
| 400 | 25.140 s |
| 420 | 26.920 s |
| 440 | 29.203 s — largest measured `k` still under 30 s |
| 460 | 32.086 s — first measured `k` over 30 s; true crossing is between 440 and 460 |

**Human ruling** (recorded because it overrode the implementer's first cut):
the implementer initially set the budget at `k=160` (3.484 s), 7.6× below the
plan's own "largest k under 30 s" criterion. The user's ruling: budget the
measured 30 s crossing, since Fence 2 bounds *encoding blowup*, and encoding
size (gate-equivalents) is the right unit for that bound, not a fixed `k`.

**Chosen budget:**
`UF_CONGRUENCE_BUDGET = pairs(440) × 96 = 96,580 × 96 = 9,271,680`
(`crates/shinri-solver/src/bv_stage.rs:424`). The Fence-2 pin test
(`encoding_past_the_budget_fences_to_unknown`) uses `k=1500`
(`pairs(1500) × 96 = 1,124,250 × 96 = 107,928,000`, 11.6× the budget).

The FP-argument cost is not separately calibrated against a real FP instance —
no such instance was run at Task 4. Instead `FP_ARG_COST_MULTIPLIER = 3` is
used as a conservative estimate, later confirmed against real source in Task 4's
review: `bits_eq` is 3 gates/bit (`shinri-fp/src/blast/compare.rs:7-16`) and
`unpack` costs `3·eb + 2·sb + 2` (`shinri-fp/src/unpack.rs:18-58`), giving true
ratios of 2.60× (f32), 2.50× (f64), 2.75× (eb5/sb11) — so 3 is a genuine
rounding-up, not false precision.

### 7.4 Named fence-attributable decided → `unknown` flips

Two named flips, one per fence, each measured directly against the pre-slice
release binary (`main` @ `2e5e7c00`) so the "decided" half of the flip is not
assumed:

1. **Fence 1 (argument sort), `qfufbv_e2e::int_argument_to_a_bv_uf_fences_to_unknown`.**
   `(set-logic ALL)(declare-fun h (Int) (_ BitVec 8))(declare-fun n () Int)
   (assert (= (h n) #x2a))(check-sat)`. MEASURED pre-slice (worktree at
   `e0d8af06`, immediately before Task 2's fence landed): decides `sat`. Post-
   slice: `unknown`, because `n`'s Int sort has no blastable word. This is the
   spec §2.1 named exception.

2. **Fence 1 (argument sort), `qfdt_model_e2e::fenced_bv_field_is_unknown`
   (the `BV_FIELD` query).** `(set-logic QF_UFDTBV)(declare-datatype W ((mk (w
   (_ BitVec 8))))) (declare-fun v () W)(assert (= (w v) #x2a))(check-sat)
   (get-model)`. `(w v)` is a non-nullary BV-result uninterpreted application
   whose argument `v` is Datatype-sorted — also unwordable, also Fence 1, not
   Fence 2 and not the congruence arm (the congruence arm never sees this
   query — it is rejected before lowering starts). MEASURED (worktree at
   `e0d8af06`, immediately before Task 2's fence landed, release binary):
   pre-slice decides `sat`, `get-model` prints `((define-fun v () W ?))` — the
   whole-symbol placeholder, not a partial `(mk ?)`, matching slice 43 spec
   §5's BV row. Post-slice: `unknown`, `get-model` prints `()`. **Precision on
   correctness:** for this specific
   *single-application* query, the pre-slice `sat` was itself
   correct-but-incomplete (an unconstrained placeholder), not unsound — the
   wrong-`sat` defect this slice fixes requires **two or more** applications of
   the same uninterpreted function, which this query never had. This flip is
   therefore a named Fence-1 exception, not a soundness correction, for this
   specific query.

3. **Fence 2 (blowup cap), `qfufbv_e2e::encoding_past_the_budget_fences_to_unknown`.**
   This test's `k=1500` formula is **not** the chained calibration formula of
   §7.3's table — it is a *different* construction that happens to scale by
   the same `pairs(k) × 96` cost: `k` **independent** assertions
   `g(vᵢ,vᵢ) = #x00000000` for `i` in `0..k`, no application ever compared
   against another (`crates/shinri-solver/tests/qfufbv_e2e.rs:51-72`). MEASURED
   pre-slice (`main` @ `2e5e7c00`, release binary, this exact k=1500
   construction reproduced byte-for-byte from the shipped test and run via
   `time ./target/release/shinri`): decides `sat` in 0.168 s — correctly,
   since each `g(vᵢ,vᵢ)` is independent and trivially self-congruent; no
   cross-application constraint is asserted, so nothing in this formula
   depends on congruence firing at all. Post-slice: `unknown`, because the
   encoding cost (`pairs(1500) × 96 = 107,928,000`) exceeds
   `UF_CONGRUENCE_BUDGET`. This flip trades completeness for the PR-tier time
   budget on an intentionally adversarial size, not a correctness fix.

No other decided → `unknown` flips were found across `qfbv_witnesses`,
`script_e2e`, `qfdt_e2e`, or the full unfiltered oracle suite (§7.6).

### 7.5 The Task 2 model side effect

Measured on the release binary:

```
$ printf '%s\n' '(set-logic QF_UFBV)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(declare-fun x () (_ BitVec 8))(assert (= (f x) #x2a))(check-sat)(get-model)' > model.smt2
$ ./target/release/shinri model.smt2
sat
((define-fun x () (_ BitVec 8) #x00))
```

(The `success` lines the CLI also prints are a `:print-success` presentation
detail of `shinri-cli`'s driver, not part of `Solver::execute`'s
`CommandResponse` stream that `run_script` in the test files consumes; the
test-relevant string is the `((define-fun x () (_ BitVec 8) #x00))` line.)
Pre-slice this printed `(define-fun x () (_ BitVec 8) ?)` — `x` was never
blasted, so it never entered `Blaster.cache` and `exported_var_bits` could not
see it. Congruence forces the arguments to be blasted, so the value now
appears. Pinned by `argument_variables_now_get_a_model_value`
(`crates/shinri-solver/tests/qfufbv_e2e.rs`). This does **not** make
`get-model` complete for UF queries: `f` itself is still omitted, because a
function graph needs EUF congruence-class enumeration (slice 43 §5, still
open).

### 7.6 PR-tier wall clock

```
$ time cargo nextest run --all
...
Summary [ 219.640s] 1324 tests run: 1324 passed (5 slow), 7 skipped
real    3m40.100s
```

Well inside the 10–15 min (600–900 s) blocking PR-tier budget (CI hard cap
20 min). `nullary_applications_emit_no_congruence_clauses`
(`crates/shinri-bv/src/lib.rs`) still passes at its pre-slice constant,
`NULLARY_EQ_CLAUSES = 57`, confirming the nullary arm's CNF output is
byte-for-byte unchanged by this slice.
