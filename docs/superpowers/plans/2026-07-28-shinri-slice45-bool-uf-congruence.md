# Slice 45 — Bool-result uninterpreted applications — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let the bit-blaster decide queries containing non-nullary
uninterpreted applications with a **Bool result sort** over blastable
arguments, instead of fencing them to `unknown`.

**Architecture:** Reuse slice 44's Ackermann machinery verbatim at result width
1. `blast_bv_atom` gains one `Op::Uninterpreted` arm delegating to the existing
`blast_uf_app`; `collect_bv_atoms` widens to collect Bool-sorted non-nullary
uninterpreted applications, which satisfies all three paths' foreign-theory
fences at once because all three call it; Fence 1 and Fence 2's result-sort
guards widen from BitVec to BitVec-or-Bool. `Lowerer::atom`'s
first-operand-sort dispatch is reordered so an FP-argument predicate reaches
the BV atom path rather than `blast_fp_atom`.

**Tech Stack:** Rust (workspace crates `shinri-bv`, `shinri-fp`,
`shinri-solver`), `cargo nextest`, differential oracles against z3 and cvc5 via
`easy-smt`, all provisioned by `mise`.

**Spec:** [`docs/superpowers/specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md`](../specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md)

## Global Constraints

- **Pure-Rust mandate.** Native-link dependencies are banned; `deny.toml` bans
  `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`. This slice adds no
  dependencies at all.
- **`cargo fmt --all` before every push.** CI gates on `fmt --check` and fails
  fast. Subagents do not auto-format.
- **`cargo clippy --workspace --all-targets -- -D warnings` must be clean.**
  `mise run lint` covers both.
- **Oracle tests are feature-gated.** Run with `cargo nextest run -p
  shinri-solver --features oracle`. **Without `--features oracle` they silently
  run 0 tests** — never report that as green coverage.
- **nextest filters use the expression form**: `-E 'test(<name>)'`, not a
  positional `mod::name` filter, which matches nothing on the pinned nextest
  0.9.140. Use `-E 'binary(<name>)'` to select a whole integration-test binary.
  **Always confirm a non-zero discovered count** — a 0-test run reads as green.
- **Blocking PR tier budget: 10–15 min wall-clock** (CI job hard cap 20 min).
  Any test measured >5 min must be `#[ignore]`d to the nightly tier.
- **Never remove `#[ignore]`** from the exhaustive `shinri-fp` suites.
- **`UF_CONGRUENCE_BUDGET` stays at its slice-44 calibrated value.** No task
  retunes it. If a task believes it must change, stop and escalate.
- **The slice-45 invariant (spec §2.1):** `unknown` → decided is the ONLY
  permitted verdict flip. Any `sat` → `unsat`, `unsat` → `sat`, or decided →
  `unknown` is a regression with **no named-exception list**. Unlike slice 44,
  there is no legitimate reason for a query that decides today to stop
  deciding.
- **Measurements cite profile and commit.** Every number recorded in the spec's
  §8 must state debug-vs-release and the commit it was measured at.

---

## File Structure

| File | Responsibility | Tasks |
|---|---|---|
| `crates/shinri-solver/tests/qfbv_oracle.rs` | Pure-BV differential generator; gains Bool-result predicates + the family-scoped decidedness assertion | 1 |
| `crates/shinri-bv/src/blast/mod.rs` | `blast_bv_atom` gains the `Op::Uninterpreted` arm; unit tests for the width-1 congruence | 2 |
| `crates/shinri-bv/src/lib.rs` | `lower`'s atom memoization; slice-45 unit tests beside slice 44's | 2 |
| `crates/shinri-solver/src/bv_stage.rs` | `collect_bv_atoms` widening, Fence 1 and Fence 2 result-sort widening, doc/rename | 3, 7 |
| `crates/shinri-solver/tests/qfufbv_e2e.rs` | End-to-end verdict pins: direction tests, `ite`-lifting pins, fence pins | 3, 4, 6 |
| `crates/shinri-fp/src/lower.rs` | `Lowerer::atom` dispatch reorder | 4 |
| `crates/shinri-solver/tests/fp_oracle.rs` | FP-argument predicate coverage + decidedness assertion | 4 |
| `crates/shinri-solver/tests/qfabv_oracle.rs` | ABV predicate coverage + decidedness assertion | 5 |
| `docs/superpowers/specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md` | §8 measured outcomes, filled in as tasks produce them | 1, 4, 6, 7 |

**Task order is load-bearing.** Task 2 (the blaster arm) must land **before**
Task 3 (collection widening). Widening collection first would hand
`blast_bv_atom` an `Op::Uninterpreted` node it has no arm for, reaching its
fallback on a shape it cannot lower. Do not reorder these two.

---

## Task 1: The gate — `qfbv_oracle` predicates and the decidedness assertion

The gate goes first, and it must **fail on pre-slice `main`**. A differential
oracle alone cannot fail here: every harness treats our `Unknown` as a skip
(`qfbv_oracle.rs:483`, "Our Unknown is never a failure"), so pre-slice all
predicate instances are skipped and the suite is green. The teeth come from a
family-scoped decidedness assertion.

**Files:**
- Modify: `crates/shinri-solver/tests/qfbv_oracle.rs` (generator `gen_instance` at `:95`, setup block at `:458`, driver `differential_qf_bv_small` at `:411`)
- Modify: `docs/superpowers/specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md` (§8.1)

**Interfaces:**
- Consumes: nothing from earlier tasks.
- Produces: `gen_instance` returns `bool` (did this instance contain a UF
  predicate application?) instead of `()`. Task 4 and Task 5 mirror this exact
  shape in `fp_oracle.rs` and `qfabv_oracle.rs`.

- [ ] **Step 1: Declare the two Bool-result predicates in the setup block**

In `differential_qf_bv_small`, immediately after the existing `uf1_s`/`uf2_s`
declarations at `qfbv_oracle.rs:458-470`, add:

```rust
        // slice 45: Bool-result uninterpreted predicates. Same small-pool
        // rationale as f/g above — two symbols over a shared term pool is what
        // makes a congruence violation reachable. `bool_sort` is a Solver
        // accessor (crates/shinri-solver/src/lib.rs:277), not a mint.
        let bool_sort = s.bool_sort();
        let pred1_s = s.declare_fun("p", &[bv_sort], bool_sort);
        let pred2_s = s.declare_fun("q", &[bv_sort, bv_sort], bool_sort);
        let z_bool = ctx.atom("Bool");
        ctx.declare_fun("p", vec![bv_type_atom], z_bool).unwrap();
        ctx.declare_fun("q", vec![bv_type_atom, bv_type_atom], z_bool)
            .unwrap();
        dump.push_str(&format!(
            "\n(declare-fun p ((_ BitVec {width})) Bool)\
             \n(declare-fun q ((_ BitVec {width}) (_ BitVec {width})) Bool)"
        ));
```

- [ ] **Step 2: Thread the predicates into `gen_instance` and return the family flag**

Change the signature at `qfbv_oracle.rs:95` to take the two new symbols and
return whether a predicate was emitted:

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
    pred1: shinri_core::SymbolId,
    pred2: shinri_core::SymbolId,
    dump: &mut String,
) -> bool {
```

Declare the flag at the top of the body, right after the `pool` is built:

```rust
    // slice 45: did this instance emit a Bool-result predicate application?
    // The decidedness assertion in the driver is scoped to exactly these
    // instances, so a healthy overall decided rate cannot mask a predicate
    // family that never decides.
    let mut used_pred = false;
```

and return it as the function's last expression:

```rust
    used_pred
}
```

- [ ] **Step 3: Add the two predicate atom kinds**

In the atom-building loop (`qfbv_oracle.rs:314`), widen the kind draw from 11
to 13 and add two arms. Note the existing `_ =>` literal-comparison arm must
become an explicit `10 =>` so the new arms are reachable:

```rust
        let kind = rng.below(13); // 0-1 eq/ne, 2-9 comparisons, 10 literal,
                                  // 11-12 slice-45 Bool-result predicates
```

Change the existing catch-all literal arm's pattern from `_ =>` to `10 =>`,
then append before the closing brace of the match:

```rust
            // slice 45: (p t_i) — a 1-ary Bool-result uninterpreted
            // application. This is the atom the pre-slice fence rejects.
            11 => {
                used_pred = true;
                let sa = s.app(Op::Uninterpreted(pred1), &[pool[i].s]);
                let za = ctx.list(vec![ctx.atom("p"), pool[i].z]);
                (sa, za, format!("(p t{i})"))
            }
            // slice 45: (q t_i t_j) — a 2-ary Bool-result application.
            _ => {
                used_pred = true;
                let sa = s.app(Op::Uninterpreted(pred2), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("q"), pool[i].z, pool[j].z]);
                (sa, za, format!("(q t{i} t{j})"))
            }
```

- [ ] **Step 4: Add the family counters and the decidedness assertion**

In `differential_qf_bv_small`, add counters beside the existing ones:

```rust
    // slice 45: decidedness of the Bool-result predicate family.
    let mut pred_total = 0usize;
    let mut pred_decided = 0usize;
```

Capture the flag at the call site (`qfbv_oracle.rs:473`) and count on the
outcome match — `used_pred` must be read for EVERY outcome, including the
`Unknown` arm, or the denominator is wrong:

```rust
        let used_pred = gen_instance(
            &mut rng, &mut s, &mut ctx, width, &var_names, &vars_s, &z_vars, uf1_s, uf2_s,
            pred1_s, pred2_s, &mut dump,
        );

        dump.push_str("\n(check-sat)");

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();

        if used_pred {
            pred_total += 1;
            if ours != SolveOutcome::Unknown {
                pred_decided += 1;
            }
        }
```

Then, after the existing `n_sat > 0` / `n_unsat > 0` assertions, add:

```rust
    // ── slice 45: the family-scoped decidedness gate ─────────────────────────
    //
    // THIS is the assertion that fails on pre-slice main. The zero-disagreement
    // panic above cannot: pre-slice every predicate instance is Unknown, and
    // Unknown is a skip, so a generator extension ALONE would be green on the
    // unfixed tree and would prove nothing.
    //
    // `pred_total > 0` is not redundant with the ratio check: without it an
    // empty family passes vacuously (0 > 0/2 is false, but a generator change
    // that stopped emitting predicates entirely would be caught only by this
    // line). Same class as a 0-test nextest run reading as green.
    assert!(
        pred_total > 0,
        "generator emitted zero Bool-result predicate instances — the slice-45 \
         family is not being exercised at all"
    );
    assert!(
        pred_decided > pred_total / 2,
        "Bool-result predicate family decided {pred_decided}/{pred_total} — \
         more than half must decide. Pre-slice this is 0/N by construction \
         (the bv_stage foreign-theory fence); post-slice a low rate means the \
         collection widening or a fence is rejecting instances it should admit"
    );
```

- [ ] **Step 5: Run the gate and confirm it FAILS on the unfixed tree**

```bash
cd /workspace
cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_bv_small)' --no-capture
```

Expected: **FAIL**, on the `pred_decided > pred_total / 2` assertion, with
`pred_decided` equal to **0**. Confirm the discovered test count is 1, not 0 —
a 0-test run is not a pass and not a failure, it is no coverage.

If it fails on `pred_total > 0` instead, the atom kinds are not being drawn;
recheck that the `_ =>` literal arm became `10 =>` in Step 3.

If it *passes*, stop — the gate has no teeth and the rest of the slice cannot
be trusted. The most likely cause is that `used_pred` is not being counted on
the `Unknown` arm.

- [ ] **Step 6: Record the pre-slice measurement in the spec**

Fill in spec §8.1 with the verbatim assertion failure, the `pred_decided`/
`pred_total` numbers, the profile (debug — nextest default), and the commit.

- [ ] **Step 7: Commit**

```bash
cd /workspace
cargo fmt --all
git add crates/shinri-solver/tests/qfbv_oracle.rs docs/superpowers/specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md
git commit -m "test(bv): slice45 T1 — QF_BV oracle emits Bool-result predicates

Extends the generator with p (1-ary) and q (2-ary) Bool-result
uninterpreted symbols and adds a family-scoped decidedness assertion.

A plain differential extension cannot gate a completeness slice: the
harness treats our Unknown as a skip, so pre-slice every predicate
instance is skipped and the suite is green. The decidedness assertion is
what fails on the unfixed tree — measured 0/N decided."
```

---

## Task 2: The blaster arm

**Files:**
- Modify: `crates/shinri-bv/src/blast/mod.rs` (`blast_bv_atom` at `:609`)
- Modify: `crates/shinri-bv/src/lib.rs` (`lower` at `:31`; unit tests beside slice 44's at `:194`)

**Interfaces:**
- Consumes: `blast_uf_app(sink, ctx, sym, child_ids, width) -> Vec<BitLit>`
  (`blast/mod.rs:358`), unchanged; `solve_atoms(ctx, &[(TermId, bool)]) -> bool`
  (`lib.rs:262`), the existing slice-44 test helper, reused as-is.
- Produces: `blast_bv_atom` accepts a Bool-sorted non-nullary
  `Op::Uninterpreted` application and returns its literal. Task 3 relies on
  this; Task 4 relies on it being reachable from `Lowerer`.

- [ ] **Step 1: Write the failing unit test — width-1 congruence and its direction**

Append to `crates/shinri-bv/src/lib.rs`'s `lower_tests` module, after slice
44's `nested_application_congruence`:

```rust
    // ── Slice 45: Bool-result uninterpreted applications ─────────────────────

    /// The Bool-result mirror of slice 44's implication test. All three shapes
    /// are pinned together because getting the direction wrong flips exactly
    /// one of them, and at result width 1 a biconditional is an easy slip:
    /// the single-bit case looks like plain equality until distinct arguments
    /// are involved.
    #[test]
    fn bool_result_congruence_is_an_implication_not_a_biconditional() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let b = ctx.bool_sort();
        let p = ctx.declare_fun("p", &[s8], b);
        let xf = ctx.declare_fun("x", &[], s8);
        let yf = ctx.declare_fun("y", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let px = ctx.mk_app(Op::Uninterpreted(p), &[x]).unwrap();
        let py = ctx.mk_app(Op::Uninterpreted(p), &[y]).unwrap();
        let args_eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();

        assert!(
            !solve_atoms(&mut ctx, &[(args_eq, true), (px, true), (py, false)]),
            "x = y AND p(x) AND !p(y) must be UNSAT — this is the congruence"
        );
        assert!(
            solve_atoms(&mut ctx, &[(args_eq, false), (px, true), (py, false)]),
            "x != y AND p(x) AND !p(y) must stay SAT — no converse implication"
        );
        assert!(
            solve_atoms(&mut ctx, &[(args_eq, false), (px, true), (py, true)]),
            "x != y AND p(x) AND p(y) must stay SAT — a predicate may agree on \
             distinct arguments"
        );
    }

    /// A Bool-result and a BitVec-result application of ONE redeclared symbol
    /// name must never be paired. `Context::declare_fun` interns by name and
    /// OVERWRITES `fun_sigs` (crates/shinri-core/src/context.rs:233-237), so
    /// both live under one `SymbolId`; `shape_compatible` discriminates them on
    /// `result.len()` — 1 vs. 8.
    ///
    /// Pairing them would relate a one-bit result word to an eight-bit one.
    /// The test asserts SAT: nothing may constrain the two together, so
    /// asserting the predicate true while pinning the BV result to a constant
    /// must remain satisfiable.
    ///
    /// THE ORDER BELOW IS LOAD-BEARING. `check_app` reads `fun_sigs` at
    /// `mk_app` time, so the Bool-result application must be built BEFORE the
    /// redeclaration — declaring both signatures first would make both
    /// `mk_app` calls see the BV signature and produce two BV-sorted apps.
    /// They would then hash-cons to one TermId (`TermKey::App` includes the
    /// result sort, context.rs:298-302) and the test would be vacuous.
    #[test]
    fn bool_and_bv_results_of_one_symbol_are_never_paired() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let b = ctx.bool_sort();
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();

        // Same NAME, two signatures — the redeclaration hazard slice 44's
        // shape_compatible was built for. Build each application immediately
        // after the declaration that gives it its result sort.
        let f_bool = ctx.declare_fun("f", &[s8], b);
        let f_bool_x = ctx.mk_app(Op::Uninterpreted(f_bool), &[x]).unwrap();
        let f_bv = ctx.declare_fun("f", &[s8], s8);
        let f_bv_x = ctx.mk_app(Op::Uninterpreted(f_bv), &[x]).unwrap();

        assert_eq!(f_bool, f_bv, "one name interns to one SymbolId");
        assert_ne!(
            f_bool_x, f_bv_x,
            "differing result sorts must give differing TermIds"
        );
        assert_eq!(ctx.sort_of(f_bool_x), b, "the Bool-result app kept its sort");

        let c = ctx.mk_bv_const(8, shinri_num::Integer::from(0u64));
        let bv_eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[f_bv_x, c]).unwrap();

        assert!(
            solve_atoms(&mut ctx, &[(f_bool_x, true), (bv_eq, true)]),
            "a Bool-result and a BV-result application of one symbol name must \
             be unrelated — pairing them relates a 1-bit word to an 8-bit one"
        );
    }

    /// Step order, the Bool-result case: `p(f(x))` blasts its argument — the
    /// BV-result application `f(x)` — before reading the registry. With
    /// `x = f(x)` asserted, congruence forces `f(x) = f(f(x))`, and the
    /// predicate applications over them must agree.
    #[test]
    fn bool_result_over_a_bv_result_application() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let b = ctx.bool_sort();
        let f = ctx.declare_fun("f", &[s8], s8);
        let p = ctx.declare_fun("p", &[s8], b);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let p_x = ctx.mk_app(Op::Uninterpreted(p), &[x]).unwrap();
        let p_fx = ctx.mk_app(Op::Uninterpreted(p), &[fx]).unwrap();
        let args_eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, fx]).unwrap();

        assert!(
            !solve_atoms(&mut ctx, &[(args_eq, true), (p_x, true), (p_fx, false)]),
            "x = f(x) AND p(x) AND !p(f(x)) must be UNSAT — the predicate's \
             argument is a BV-result application and congruence must see it"
        );
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

```bash
cd /workspace
cargo nextest run -p shinri-bv -E 'test(bool_result_congruence_is_an_implication_not_a_biconditional) + test(bool_and_bv_results_of_one_symbol_are_never_paired) + test(bool_result_over_a_bv_result_application)'
```

Expected: 3 tests discovered, all **FAIL**. The failure will come from
`blast_bv_atom`'s dispatch reaching a `TermNode::App { op: Op::Uninterpreted(_), .. }`
node it has no arm for. Confirm the discovered count is 3, not 0.

- [ ] **Step 3: Add the arm to `blast_bv_atom`**

In `crates/shinri-bv/src/blast/mod.rs`, inside `blast_bv_atom`'s match
(`:611`), add this arm **before** the `Op::Builtin` arms:

```rust
        // Slice 45: a Bool-result uninterpreted application. Delegates to the
        // slice-44 gadget at result width 1, so the Ackermann clause per prior
        // pair degenerates to the single `cond -> (v_prior <-> v_new)`.
        //
        // `blast_bv_atom` is only ever called on a Bool-sorted term, so no
        // result-sort test is needed here.
        //
        // NULLARY applications must never reach this arm. Collection
        // (`bv_stage::collect_bv_atoms`) excludes them, which is what keeps
        // `blast_uf_app`'s `child_ids.is_empty()` branch unreachable from here.
        // The exclusion is NOT a soundness cliff — `encode_uncached`
        // intercepts a collected atom by TermId and memoizes
        // (`shinri-solver/src/tseitin.rs:112`), so a nullary symbol routed
        // here would still get exactly one literal — it is that bare Bool
        // constants already have a well-understood Tseitin path this slice has
        // no reason to move, and that
        // `nullary_applications_emit_no_congruence_clauses` pins its clause
        // count.
        TermNode::App {
            op: Op::Uninterpreted(sym),
            args,
            ..
        } => {
            let child_ids = ctx.children(args).to_vec();
            debug_assert!(
                !child_ids.is_empty(),
                "nullary Bool application reached blast_bv_atom — collection \
                 must exclude it"
            );
            blast_uf_app(sink, ctx, sym, &child_ids, 1)[0]
        }
```

- [ ] **Step 4: Run the tests to verify they pass**

```bash
cd /workspace
cargo nextest run -p shinri-bv -E 'test(bool_result_congruence_is_an_implication_not_a_biconditional) + test(bool_and_bv_results_of_one_symbol_are_never_paired) + test(bool_result_over_a_bv_result_application)'
```

Expected: 3 tests discovered, all **PASS**.

- [ ] **Step 5: Verify the nullary clause-count constant is untouched**

```bash
cd /workspace
cargo nextest run -p shinri-bv -E 'test(nullary_applications_emit_no_congruence_clauses)'
```

Expected: PASS at `NULLARY_EQ_CLAUSES = 57`. If this moved, the arm is
capturing nullary applications — the arm must not be reachable for them.

- [ ] **Step 6: Memoize the atom literal by rewritten TermId in `lower`**

Spec §3.2(b): `rewrite` is structure-preserving, so `(p (bvadd x #x00))` and
`(p x)` converge to the same rewritten TermId while `lower` blasts each
separately and mints two independent literals. Congruence relates them, so this
is **correct but wasteful** — the memo is an efficiency and clarity change, not
a correctness fix, and must be described that way.

In `crates/shinri-bv/src/lib.rs`, change `lower`'s loop (`:41`):

```rust
pub fn lower(ctx: &mut Context, bv_atoms: &[TermId]) -> Lowered {
    let mut b = Blaster::new();
    let mut atom_lit: FxHashMap<TermId, BitLit> = FxHashMap::default();
    // Memo keyed by the REWRITTEN id: two distinct originals can converge
    // under `rewrite` (it rewrites children bottom-up and rebuilds), and
    // blasting each separately mints two literals for one term. Congruence
    // forces them equal, so this is deduplication, NOT a soundness fix.
    let mut by_rewritten: FxHashMap<TermId, BitLit> = FxHashMap::default();
    for &original in bv_atoms {
        let rewritten = rewrite(ctx, original);
        let lit = match by_rewritten.get(&rewritten) {
            Some(&l) => l,
            None => {
                let l = b.blast_atom(ctx, rewritten);
                by_rewritten.insert(rewritten, l);
                l
            }
        };
        // KEY: store under the ORIGINAL atom id so Task 17's hook can look it up.
        atom_lit.insert(original, lit);
    }
    // Extract var_bits BEFORE consuming the blaster via finish().
    let var_bits = b.exported_var_bits(ctx);
    Lowered {
        cnf: b.finish(),
        atom_lit,
        var_bits,
    }
}
```

- [ ] **Step 7: Write and run the memo test**

Append to `lower_tests`:

```rust
    /// Two ORIGINAL atoms that converge under `rewrite` share one literal.
    /// `(p (bvadd x #x00))` rewrites to `(p x)` via the additive-identity
    /// rule, so both originals must map to the SAME BitLit while `atom_lit`
    /// stays keyed by each original — the contract `lower` documents.
    #[test]
    fn converging_originals_share_one_atom_literal() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let b = ctx.bool_sort();
        let p = ctx.declare_fun("p", &[s8], b);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, shinri_num::Integer::from(0u64));
        let x_plus_0 = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, zero])
            .unwrap();
        let p_x = ctx.mk_app(Op::Uninterpreted(p), &[x]).unwrap();
        let p_x_plus_0 = ctx.mk_app(Op::Uninterpreted(p), &[x_plus_0]).unwrap();
        assert_ne!(p_x, p_x_plus_0, "the two ORIGINAL atoms must differ");

        let lo = lower(&mut ctx, &[p_x, p_x_plus_0]);
        assert_eq!(
            lo.atom_lit[&p_x], lo.atom_lit[&p_x_plus_0],
            "converging originals must share one literal"
        );
    }
```

```bash
cd /workspace
cargo nextest run -p shinri-bv -E 'test(converging_originals_share_one_atom_literal)'
```

Expected: 1 test discovered, PASS.

If it fails with the two literals differing, the additive-identity rewrite rule
does not fire on this shape. Do **not** weaken the assertion — find a shape
that does converge by checking the rules in
`crates/shinri-bv/src/rewrite.rs`, and update the test's comment to name the
rule it relies on.

- [ ] **Step 8: Run the whole `shinri-bv` suite for non-regression**

```bash
cd /workspace
cargo nextest run -p shinri-bv
```

Expected: all pass, zero failures.

- [ ] **Step 9: Commit**

```bash
cd /workspace
cargo fmt --all
cargo clippy -p shinri-bv --all-targets -- -D warnings
git add crates/shinri-bv/src/blast/mod.rs crates/shinri-bv/src/lib.rs
git commit -m "fix(bv): slice45 T2 — Bool-result uninterpreted applications in blast_bv_atom

One arm delegating to slice 44's blast_uf_app at result width 1. The
Ackermann clause per prior pair degenerates to cond -> (v_prior <-> v_new).

shape_compatible needs no change: a Bool-result and a BV-result
application of one redeclared symbol differ in result.len() (1 vs width),
so they can never be paired. Pinned directly.

Also deduplicates atom literals by rewritten TermId in lower(). Two
originals can converge under rewrite and were minting two literals for
one term; congruence already forced them equal, so this is
deduplication, not a soundness fix."
```

---

## Task 3: Collection and the fences — the pure-BV path decides

This is where the spec §1 probes flip from `unknown` to decided.

**Files:**
- Modify: `crates/shinri-solver/src/bv_stage.rs` (`collect_bv_atoms` at `:124`, `walk_uf_args` at `:286`, `collect_uf_apps` at `:378`)
- Modify: `crates/shinri-solver/tests/qfufbv_e2e.rs` (append)

**Interfaces:**
- Consumes: Task 2's `blast_bv_atom` arm.
- Produces: `collect_bv_atoms` returns Bool-sorted non-nullary uninterpreted
  applications in its atom list. Tasks 4 and 5 depend on this, since the FP and
  ABV paths call the same function.

- [ ] **Step 1: Write the failing e2e tests**

Append to `crates/shinri-solver/tests/qfufbv_e2e.rs`. These are the spec §1 and
§1.1 probes, each measured `unknown` on pre-slice `main`:

```rust
// ── Slice 45: Bool-result uninterpreted applications ─────────────────────────

/// Spec §1 Q1: congruence fires through a Bool-result predicate.
#[test]
fn equal_arguments_force_equal_predicate_results() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (assert (= x y))(assert (p x))(assert (not (p y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// Spec §1 Q3: the converse must NOT hold — distinct arguments may disagree.
#[test]
fn distinct_arguments_leave_predicate_results_free() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (assert (p x))(assert (not (p y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// Spec §1 Q5: the same hash-consed term at both polarities is refutable by
/// the SAT skeleton alone. Pre-slice the fence fired before the skeleton ever
/// ran, which is the sharpest illustration of the completeness gap.
#[test]
fn a_predicate_at_both_polarities_is_unsat() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p x))(assert (not (p x)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// Spec §1 Q4: a predicate coexisting with a genuine BV atom decides.
#[test]
fn a_predicate_beside_a_bv_atom_decides() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p x))(assert (bvult x #x05))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// Spec §1.1: a predicate buried inside a BV `ite`. Collection and the fence
/// both treat a collected atom as a LEAF and do not descend, so this shape is
/// invisible to their walks — it decides only because `word_norm.normalize`
/// (crates/shinri-solver/src/lib.rs:759) eliminates BV ites into a fresh
/// symbol plus a defining assertion BEFORE collection, lifting `(p x)` to the
/// assertion level. This test is what proves that lifting, rather than
/// assuming it.
#[test]
fn a_predicate_lifted_out_of_a_bv_ite_decides() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (assert (= x y))\
         (assert (= (ite (p x) #x01 #x00) #x01))\
         (assert (= (ite (p y) #x01 #x00) #x00))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// Spec §1.1, the single-term variant: one hash-consed `(p x)` used at both
/// ite branches must not mint two independent conditions.
#[test]
fn one_predicate_term_in_two_bv_ites_decides() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (= (ite (p x) #x01 #x00) #x01))\
         (assert (= (ite (p x) #x01 #x00) #x00))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// Spec §2 out-of-scope: a Bool ARGUMENT has no blastable word — a Bool child
/// can be an arbitrary formula and the blaster has no Tseitin encoder — so
/// Fence 1 still fences. Sound, deliberately incomplete.
#[test]
fn bool_argument_to_a_predicate_still_fences() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p (Bool) Bool)(declare-fun c () Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p c))(assert (bvult x #x05))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

/// Fence 1, the Bool-result sibling of `int_argument_to_a_bv_uf_fences_to_unknown`.
#[test]
fn int_argument_to_a_predicate_still_fences() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p (Int) Bool)(declare-fun n () Int)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p n))(assert (bvult x #x05))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}
```

- [ ] **Step 2: Run them to verify the six new decidedness tests fail**

```bash
cd /workspace
cargo nextest run -p shinri-solver -E 'binary(qfufbv_e2e)'
```

Expected: the six decidedness tests **FAIL** with `unknown`; the two fence
tests (`bool_argument_…`, `int_argument_…`) **PASS** already, because they
fence today for the reason they must keep fencing. Confirm the discovered count
includes all eight new tests.

- [ ] **Step 3: Widen `collect_bv_atoms`**

In `crates/shinri-solver/src/bv_stage.rs`, in `collect_bv_atoms`'s `is_atom`
match (`:141`), add a third arm:

```rust
            let is_atom = match op {
                _ if is_bv_predicate(op) => true,
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) => {
                    kids.iter().any(|&k| is_bv_sorted(ctx, k))
                }
                // Slice 45: a NON-NULLARY Bool-result uninterpreted
                // application. The blaster owns it (blast_bv_atom's
                // Op::Uninterpreted arm), so collecting it here is what lets
                // the foreign-theory fences pass it: a collected atom is in
                // `bv_set` and each fence's walk returns at it.
                //
                // NULLARY is excluded deliberately — a bare Bool constant
                // keeps its existing Tseitin path
                // (`tseitin.rs`'s `Op::Uninterpreted(_) => self.atom(t)`), and
                // `has_non_bv_theory_atom` already exempts it explicitly.
                Op::Uninterpreted(_) => {
                    !kids.is_empty() && ctx.sort_of(t) == ctx.bool_sort()
                }
                _ => false,
            };
```

- [ ] **Step 4: Widen Fence 1's result-sort guard**

In `walk_uf_args` (`:299`), replace the `ctx.bv_width(*sort).is_some()`
condition:

```rust
    // Slice 45: BitVec-result (slice 44) OR Bool-result applications. Both are
    // lowered by `blast_uf_app`, whose congruence arm compares argument words
    // pairwise, so both need arguments the blaster can turn into words. The
    // argument-admissibility rule below is unchanged.
    let result_is_blastable = ctx.bv_width(*sort).is_some() || *sort == ctx.bool_sort();
    if matches!(op, Op::Uninterpreted(_)) && !kids.is_empty() && result_is_blastable {
```

- [ ] **Step 5: Widen Fence 2's cost accounting**

In `collect_uf_apps` (`:391`), replace the `if let Some(res_bits) =
ctx.bv_width(*sort)` guard so a Bool result is counted at one bit:

```rust
    if let Op::Uninterpreted(sym) = op {
        if !kids.is_empty() {
            // Slice 45: a Bool-result application costs `res_bits = 1` — the
            // width-1 congruence emits one clause per prior pair rather than
            // one per result bit. `UfShapeKey` already keys on the result
            // SortId, so Bool and BitVec groups stay separate, mirroring
            // `shape_compatible`'s `result.len()` discrimination.
            let res_bits = if *sort == ctx.bool_sort() {
                Some(1u32)
            } else {
                ctx.bv_width(*sort)
            };
            if let Some(res_bits) = res_bits {
```

(The rest of the block, including the `arg_bits` computation, the `UfShapeKey`
construction, and the `or_insert`, is unchanged. Keep the existing closing
braces balanced.)

- [ ] **Step 6: Run the e2e tests to verify they pass**

```bash
cd /workspace
cargo nextest run -p shinri-solver -E 'binary(qfufbv_e2e)'
```

Expected: all tests in the binary **PASS**, including slice 44's existing ones.

- [ ] **Step 7: Cross-check the new verdicts against z3 and cvc5**

Do not trust our own answer on a slice that changes what we decide. Build the
release binary and check each decided probe against both oracles:

```bash
cd /workspace
cargo build --release
mise exec -- z3 -h >/dev/null && echo "z3 present"
mise exec -- cvc5 --version >/dev/null && echo "cvc5 present"
```

For each of the six decidedness probes, write the query to a file and run all
three, confirming the verdicts agree:

```bash
printf '%s\n' '(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))(assert (= x y))(assert (p x))(assert (not (p y)))(check-sat)' > /tmp/claude-1000/-workspace/probe.smt2
./target/release/shinri /tmp/claude-1000/-workspace/probe.smt2
mise exec -- z3 /tmp/claude-1000/-workspace/probe.smt2
mise exec -- cvc5 /tmp/claude-1000/-workspace/probe.smt2
```

Expected: `unsat` from all three. Repeat for the other five probes with their
expected verdicts (Q3 `sat`, Q5 `unsat`, Q4 `sat`, both `ite` probes `unsat`).

A disagreement here is a **stop-the-slice** event, not a test to adjust.

- [ ] **Step 8: Run the gate from Task 1 — it must now pass**

```bash
cd /workspace
cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_bv_small)' --no-capture
```

Expected: **PASS**, with `pred_decided` now a clear majority of `pred_total`.
Record both numbers — Task 7 writes them into spec §8.2.

If the decided fraction is close to 50%, do not tune the threshold up to
whatever the run produced. Investigate why instances are fencing first; only
then adjust the threshold, and record the reasoning.

- [ ] **Step 9: Verify no decided → `unknown` and no verdict flips**

```bash
cd /workspace
cargo nextest run -p shinri-solver -E 'binary(qfbv_witnesses) + binary(script_e2e) + binary(qfdt_e2e) + binary(qfuf_e2e)'
```

Expected: all pass, non-zero discovered count for each binary. Per the global
constraints there is **no named-exception list** for this slice — any failure
here is a regression to fix, not a flip to document.

- [ ] **Step 10: Commit**

```bash
cd /workspace
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver/src/bv_stage.rs crates/shinri-solver/tests/qfufbv_e2e.rs
git commit -m "fix(bv): slice45 T3 — collect Bool-result predicates, widen both fences

collect_bv_atoms now collects non-nullary Bool-result uninterpreted
applications, which satisfies every path's foreign-theory fence at once:
a collected atom is in bv_set and each fence's walk returns at it.
Fence 1's and Fence 2's result-sort guards widen from BitVec to
BitVec-or-Bool, the latter counting a Bool result at one bit.

The spec §1 probes now decide, cross-checked against z3 and cvc5. The
ite-lifting probes decide too, which is what proves word_norm's
elimination lifts a buried predicate to where collection sees it —
collection and the fence both treat a collected atom as a leaf and never
descend into one."
```

---

## Task 4: The FP/mixed path

The one place in this slice where a mistake **panics** rather than degrading.

**Files:**
- Modify: `crates/shinri-fp/src/lower.rs` (`Lowerer::atom` at `:113`)
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (generator at `:170`, driver at `:213`)
- Modify: `crates/shinri-solver/tests/qfufbv_e2e.rs` (append)
- Modify: `docs/superpowers/specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md` (§8.1, §8.2 FP rows)

**Interfaces:**
- Consumes: Task 2's `blast_bv_atom` arm; Task 3's widened `collect_bv_atoms`.
- Produces: nothing later tasks depend on.

- [ ] **Step 1: Write the failing e2e tests**

Append to `crates/shinri-solver/tests/qfufbv_e2e.rs`:

```rust
/// Spec §3.2(a): `Lowerer::atom` dispatches on the FIRST OPERAND's sort
/// (crates/shinri-fp/src/lower.rs:117), so a predicate over an FP argument
/// would route to `blast_fp_atom`, which has no uninterpreted-application arm.
/// That is a PANIC, not an `unknown` — the slice-43 shape. This test is the
/// one that catches it.
#[test]
fn fp_argument_predicate_congruence() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p ((_ FloatingPoint 8 24)) Bool)\
         (declare-fun a () (_ FloatingPoint 8 24))\
         (declare-fun b () (_ FloatingPoint 8 24))\
         (assert (= a b))(assert (p a))(assert (not (p b)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}

/// FP value equality is NOT bitwise: SMT-LIB `FloatingPoint` has exactly one
/// NaN VALUE across many bit patterns. `blast_uf_app` calls `sink.word_eq`,
/// which the `Lowerer` overrides with `core_eq` for exactly this reason
/// (crates/shinri-bv/src/blast/mod.rs's `word_eq` doc). A bitwise comparison
/// would UNDER-trigger congruence here and leave the results free, so this
/// comes back `sat` on a wrong implementation.
#[test]
fn nan_arguments_are_congruent_for_a_predicate() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p ((_ FloatingPoint 8 24)) Bool)\
         (declare-fun a () (_ FloatingPoint 8 24))\
         (declare-fun b () (_ FloatingPoint 8 24))\
         (assert (fp.isNaN a))(assert (fp.isNaN b))\
         (assert (p a))(assert (not (p b)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}
```

- [ ] **Step 2: Run them and record HOW they fail**

```bash
cd /workspace
cargo nextest run -p shinri-solver -E 'test(fp_argument_predicate_congruence) + test(nan_arguments_are_congruent_for_a_predicate)'
```

Expected: 2 discovered, both **FAIL**. Record whether the failure is a panic
(the `blast_fp_atom` unsupported arm) or an `unknown`/`sat` — the spec claims
this path panics without the dispatch fix, and that claim is being tested here.
Note the actual outcome for spec §8; if it is not a panic, say so rather than
repeating the spec's prediction.

- [ ] **Step 3: Reorder `Lowerer::atom`'s dispatch**

In `crates/shinri-fp/src/lower.rs`, replace the body of `atom` (`:113-124`):

```rust
    /// Blast a Bool-sorted atom (BV or FP predicate / (dis)equality) to a literal.
    pub fn atom(&mut self, ctx: &Context, t: TermId) -> BitLit {
        // Slice 45: an uninterpreted application is matched BEFORE the
        // first-operand-sort test below. Dispatching it by operand sort would
        // send a predicate over an FP argument — `(p a)` with `a : Float32` —
        // to `blast_fp_atom`, which has no uninterpreted-application arm: a
        // PANIC, not an `unknown`. `blast_bv_atom`'s slice-45 arm handles both
        // argument sorts, because `blast_uf_app` compares arguments through
        // `sink.word_eq`, which this Lowerer overrides with `core_eq`.
        if let TermNode::App {
            op: Op::Uninterpreted(_),
            ..
        } = ctx.term_node(t)
        {
            return blast_bv_atom(self, ctx, t);
        }
        // Dispatch by the sort of the atom's first operand.
        let first_operand_sort = match ctx.term_node(t) {
            TermNode::App { args, .. } => {
                let kids = ctx.children(*args);
                ctx.sort_of(kids[0])
            }
            _ => unreachable!("atom must be an application"),
        };
        if ctx.bv_width(first_operand_sort).is_some() {
            blast_bv_atom(self, ctx, t)
        } else {
            crate::blast_fp_atom(self, ctx, t)
        }
    }
```

Add `Op` to the `shinri_core` import at the top of the file if it is not
already in scope.

- [ ] **Step 4: Widen Fence 1 for FP arguments on this path**

Fence 1 is called with `allow_fp_args: true` on the FP/mixed path. Task 3's
`result_is_blastable` widening already covers Bool results there, so no further
`bv_stage` change is needed. Confirm by reading the FP path's call site in
`crates/shinri-solver/src/lib.rs` and checking it passes `true`; if it does
not, that is the bug to fix here, and the two Step-1 tests will still fail.

- [ ] **Step 5: Run the e2e tests to verify they pass**

```bash
cd /workspace
cargo nextest run -p shinri-solver -E 'test(fp_argument_predicate_congruence) + test(nan_arguments_are_congruent_for_a_predicate)'
```

Expected: 2 discovered, both **PASS**.

- [ ] **Step 6: Extend `fp_oracle` with a Bool-result predicate**

In `crates/shinri-solver/tests/fp_oracle.rs`, add to the declaration preamble
(`:170`):

```
(declare-fun p ((_ FloatingPoint 8 24)) Bool)
```

Add an assertion form that emits `(p <fp-term>)`, mirroring how the existing
generator emits FP predicates, and thread a `used_pred` flag through exactly as
Task 1 did for `qfbv_oracle`. Then add the same two assertions after the
driver's existing checks:

```rust
    assert!(
        pred_total > 0,
        "generator emitted zero Bool-result predicate instances — the slice-45 \
         family is not being exercised at all"
    );
    assert!(
        pred_decided > pred_total / 2,
        "Bool-result predicate family decided {pred_decided}/{pred_total} — \
         more than half must decide"
    );
```

Note `fp_oracle`'s generator is text-based and forwards `(declare-fun …)` and
`(assert …)` lines verbatim (`fp_oracle.rs:150`), so the shinri side needs no
separate term construction — unlike `qfbv_oracle`, which builds both sides.

- [ ] **Step 7: Confirm the FP gate fails before the dispatch fix, then passes**

Stash the Step-3 dispatch change, run the oracle, restore it, run again:

```bash
cd /workspace
git stash push crates/shinri-fp/src/lower.rs
cargo nextest run -p shinri-solver --features oracle -E 'binary(fp_oracle)' --no-capture
git stash pop
cargo nextest run -p shinri-solver --features oracle -E 'binary(fp_oracle)' --no-capture
```

Expected: **FAIL** then **PASS**. Record both, plus whether the pre-fix failure
was a panic or a decidedness-assertion failure.

- [ ] **Step 8: Commit**

```bash
cd /workspace
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-fp/src/lower.rs crates/shinri-solver/tests/fp_oracle.rs crates/shinri-solver/tests/qfufbv_e2e.rs docs/superpowers/specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md
git commit -m "fix(fp): slice45 T4 — predicates over FP arguments reach the BV atom path

Lowerer::atom dispatched on the first operand's sort, so a predicate over
an FP argument routed to blast_fp_atom, which has no uninterpreted arm —
a panic, not an unknown. The Op::Uninterpreted case is now matched before
the sort test.

Congruence over FP arguments goes through word_eq, which the Lowerer
overrides with core_eq, so two distinct NaN bit patterns are correctly
congruent. Pinned, because a bitwise comparison under-triggers and comes
back sat."
```

---

## Task 5: The ABV path

**Files:**
- Modify: `crates/shinri-solver/tests/qfabv_oracle.rs` (setup at `:137`, driver at `:378`)
- Modify: `crates/shinri-solver/tests/qfufbv_e2e.rs` (append)

**Interfaces:**
- Consumes: Tasks 2 and 3. `abv_stage` calls `collect_bv_atoms` on
  `abs.assertions` (`abv_stage.rs:318`) and blasts with a **persistent**
  blaster that survives refinement rounds — unlike `lower`'s one-shot.
- Produces: nothing later tasks depend on.

- [ ] **Step 1: Write the failing e2e test**

Append to `crates/shinri-solver/tests/qfufbv_e2e.rs`:

```rust
/// The ABV path shares `blast_bv_atom` through a PERSISTENT blaster that
/// survives refinement rounds (crates/shinri-solver/src/abv_stage.rs:322),
/// unlike `lower`'s one-shot. The `UfApp` registry must survive with it, or a
/// predicate application registered in round 1 will not be paired with one
/// blasted in round 2.
///
/// The array abstraction replaces `select`/`store` with fresh BV symbols
/// BEFORE `collect_bv_atoms` runs, so the predicate's argument is already a
/// plain word by the time the arm sees it.
#[test]
fn predicate_over_an_array_read_decides() {
    let out = run_script(
        "(set-logic QF_AUFBV)\
         (declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\
         (declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun i () (_ BitVec 4))(declare-fun j () (_ BitVec 4))\
         (assert (= i j))\
         (assert (p (select a i)))(assert (not (p (select a j))))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("unsat"), "got {out:?}");
}
```

- [ ] **Step 2: Run it**

```bash
cd /workspace
cargo nextest run -p shinri-solver -E 'test(predicate_over_an_array_read_decides)'
```

Expected: 1 discovered, **FAIL** with `unknown` if the ABV path still fences,
or **PASS** already if Tasks 2–3 covered it through the shared seam.

**If it passes already, that is a real result, not a reason to skip the task** —
record it, and go on to Step 3 to give the path randomized coverage.

- [ ] **Step 3: Extend `qfabv_oracle` with Bool-result predicates**

Mirror Task 1 exactly. Beside the existing `f`/`g` declarations at
`qfabv_oracle.rs:137`, add:

```rust
        "\n(declare-fun p ((_ BitVec {width})) Bool)\
         \n(declare-fun q ((_ BitVec {width}) (_ BitVec {width})) Bool)"
```

with matching shinri-side `declare_fun` calls using `s.bool_sort()`, an atom
kind emitting `(p t_i)` / `(q t_i t_j)`, a `used_pred` flag, and the same two
assertions:

```rust
    assert!(
        pred_total > 0,
        "generator emitted zero Bool-result predicate instances — the slice-45 \
         family is not being exercised at all"
    );
    assert!(
        pred_decided > pred_total / 2,
        "Bool-result predicate family decided {pred_decided}/{pred_total} — \
         more than half must decide"
    );
```

`qfabv_oracle` already emits `set-logic QF_AUFBV` rather than `QF_ABV` so z3
accepts a non-nullary `declare-fun` (`qfabv_oracle.rs:121`) — no logic-string
change is needed.

Its driver counts `n_unknown_or_skipped` for **two** distinct reasons
(`:394` and `:399`); the predicate counters must increment only on the genuine
`SolveOutcome::Unknown` arm, not on the skip arm, or the denominator conflates
our incompleteness with instances z3 never answered.

- [ ] **Step 4: Run the ABV oracle**

```bash
cd /workspace
cargo nextest run -p shinri-solver --features oracle -E 'binary(qfabv_oracle)' --no-capture
```

Expected: **PASS**, with a clear majority of the predicate family deciding.
Confirm non-zero discovery.

- [ ] **Step 5: Commit**

```bash
cd /workspace
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver/tests/qfabv_oracle.rs crates/shinri-solver/tests/qfufbv_e2e.rs
git commit -m "test(bv): slice45 T5 — ABV predicate coverage

The ABV path shares blast_bv_atom through a persistent blaster across
refinement rounds, so the UfApp registry must survive with it. Adds the
Bool-result predicate family to qfabv_oracle with the same decidedness
assertion, plus an e2e pin over a select-derived argument."
```

---

## Task 6: The Fence-1 blastability audit

Spec §5. The one item in this slice that is an **investigation with a required
measured conclusion**, not a code change with a known shape. It may end in "no
code change, here is the evidence" — that is a valid outcome, but only with
evidence.

**Files:**
- Modify: `crates/shinri-solver/src/bv_stage.rs` (only if the audit finds a gap)
- Modify: `crates/shinri-solver/tests/qfufbv_e2e.rs` (the probe, whatever it shows)
- Modify: `docs/superpowers/specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md` (§8.4)

**Interfaces:**
- Consumes: Tasks 2–5.
- Produces: either a fence in `walk_uf_args` or a documented unreachability
  argument backed by a run.

- [ ] **Step 1: State the claim being tested**

Fence 1 (`walk_uf_args`) checks argument **sorts**, not blastability. A
BitVec-sorted `(select a i)` passes by sort while the pure-BV blaster has no
arm for `select`. The expected resolution is that `uses_arrays` routes such a
query to `abv_stage` before the pure-BV path is reached, and that the array
abstraction replaces `select`/`store` with fresh BitVec symbols before
`collect_bv_atoms` runs — making the shape unreachable.

This applies **equally to slice 44's already-shipped BitVec-result arm**:
`(f (select a i))` has the same shape. Whatever the audit finds is a
pre-existing condition this slice surfaces, not one it introduces.

- [ ] **Step 2: Find the routing predicate**

```bash
cd /workspace
grep -n "uses_arrays\|abv_stage::" crates/shinri-solver/src/lib.rs | head -20
```

Read the dispatch and determine whether a query containing both an array term
and a UF application can reach the `lowered_bv` block at
`crates/shinri-solver/src/lib.rs:1007`.

- [ ] **Step 3: Probe it empirically — both result sorts**

```bash
cd /workspace
cargo build --release
printf '%s\n' '(set-logic QF_AUFBV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(declare-fun i () (_ BitVec 4))(assert (= (f (select a i)) #x2a))(check-sat)' > /tmp/claude-1000/-workspace/audit-bv.smt2
printf '%s\n' '(set-logic QF_AUFBV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))(declare-fun p ((_ BitVec 8)) Bool)(declare-fun i () (_ BitVec 4))(assert (p (select a i)))(check-sat)' > /tmp/claude-1000/-workspace/audit-bool.smt2
./target/release/shinri /tmp/claude-1000/-workspace/audit-bv.smt2
./target/release/shinri /tmp/claude-1000/-workspace/audit-bool.smt2
```

Then run **both** under the debug binary, where a `debug_assert` or an
`unreachable!` would fire rather than producing a quiet wrong answer:

```bash
cargo build
./target/debug/shinri /tmp/claude-1000/-workspace/audit-bv.smt2
./target/debug/shinri /tmp/claude-1000/-workspace/audit-bool.smt2
```

Cross-check each decided verdict against z3 and cvc5.

- [ ] **Step 4: Act on what you measured**

- **If both are routed to `abv_stage` and answer correctly:** the shape is
  unreachable from the pure-BV path. Add both probes to `qfufbv_e2e.rs` as
  pins with a comment naming the routing predicate that makes them safe, so a
  future change to that routing is loud.
- **If either panics, hangs, or gives a verdict z3/cvc5 contradict:** add the
  blastability check to `walk_uf_args` — an argument must be a BV/FP-sorted
  term the blaster has an arm for, not merely BV/FP-**sorted**. Then pin the
  now-`unknown` verdict. Because this also affects slice 44's shipped arm, say
  so explicitly in the commit message.

- [ ] **Step 5: Record the conclusion in the spec**

Fill in spec §8.4 with the commands, both binaries' output, the z3/cvc5
verdicts, and which of the two branches in Step 4 was taken. Success criterion
5 requires a **measured** conclusion — a reasoned argument alone does not close
it.

- [ ] **Step 6: Commit**

```bash
cd /workspace
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add -A
git commit -m "test(bv): slice45 T6 — Fence 1 argument-blastability audit

Fence 1 checks argument sorts, not blastability: a BV-sorted (select a i)
passes by sort while the pure-BV blaster has no select arm. Measured on
both the debug and release binaries, for BV-result and Bool-result
applications, cross-checked against z3 and cvc5. Conclusion recorded in
spec 8.4.

The shape predates this slice — slice 44's BV-result arm has it too."
```

---

## Task 7: Model channel, naming, and the full non-regression sweep

**Files:**
- Modify: `crates/shinri-solver/tests/qfufbv_e2e.rs` (append)
- Modify: `crates/shinri-solver/src/bv_stage.rs` (module doc and/or rename)
- Modify: `docs/superpowers/specs/2026-07-28-shinri-slice45-bool-uf-congruence-design.md` (§8.2, §8.3, §8.5)

**Interfaces:**
- Consumes: all prior tasks.
- Produces: the finished slice.

- [ ] **Step 1: Measure the model channel — do not predict it**

`display_term` (`crates/shinri-solver/src/tseitin.rs:483`) renders non-nullary
`Op::Uninterpreted` applications structurally, so `(get-value ((p x)))` will
emit the **label** `(p x)`. Whether it emits a **value** is unmeasured, because
pre-slice the query never got past the fence.

```bash
cd /workspace
cargo build --release
printf '%s\n' '(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)(declare-fun x () (_ BitVec 8))(assert (p x))(check-sat)(get-value ((p x)))(get-model)' > /tmp/claude-1000/-workspace/model.smt2
./target/release/shinri /tmp/claude-1000/-workspace/model.smt2
```

Record the exact output verbatim.

- [ ] **Step 2: Pin whatever it actually does**

Write the test against the **measured** output, not the expected one. Both of
these are legitimate results to pin — what is not legitimate is rendering
"no value" as a confident default (slice 43's lesson):

```rust
/// Spec §6.5: measured, not predicted. `display_term` renders a non-nullary
/// application structurally, so the LABEL is `(p x)`; what the value channel
/// does was unmeasured pre-slice because the query never got past the fence.
/// This test pins the measured behaviour. `get-model` still omits `p` itself —
/// a function graph needs congruence-class enumeration (slice 43 §5, open).
#[test]
fn get_value_on_a_predicate_application() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p x))(check-sat)(get-value ((p x)))(get-model)",
    );
    // REPLACE the expectations below with the Step-1 measured strings.
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert!(
        !out[2].contains(" p "),
        "get-model must still omit the arity-1 symbol p: {out:?}"
    );
}
```

```bash
cd /workspace
cargo nextest run -p shinri-solver -E 'test(get_value_on_a_predicate_application)'
```

Expected: 1 discovered, PASS.

- [ ] **Step 3: Resolve the `collect_bv_atoms` naming (spec §4.1)**

The function no longer means "BitVec atoms" — it means "atoms the blaster
owns". Its module doc (`crates/shinri-solver/src/bv_stage.rs:11`) calls out BV
(dis)equality inclusion as *the* soundness-critical subtlety; there are now
two.

Pick one and record which:
- **Rename** to `collect_blastable_atoms`, updating all call sites
  (`bv_stage.rs:473`, `:497`, `fp_stage.rs:448`, `:1400`, `:1415`,
  `abv_stage.rs:318`, `lib.rs:1008`, `:1038`), or
- **Keep the name** and rewrite the doc comment to state both subtleties.

What is **not** acceptable is leaving a doc comment that describes the
pre-slice meaning. Success criterion 7.

- [ ] **Step 4: Run the full unfiltered oracle suite**

The whole suite, unfiltered — slice 40's lesson is that a filtered run skips
`qfs_differential` and nearly shipped a string regression.

```bash
cd /workspace
cargo nextest run -p shinri-solver --features oracle
```

Expected: all pass. Record the summary line and the discovered test count.
**Without `--features oracle` this runs 0 oracle tests and reads as green** —
confirm the count reflects the oracle binaries.

- [ ] **Step 5: Run the PR tier and measure wall clock**

```bash
cd /workspace
time cargo nextest run --all
```

Expected: all pass, inside the 10–15 min blocking budget (CI hard cap 20 min).
Record the summary line and the `real` time. `UF_CONGRUENCE_BUDGET` must still
be at its slice-44 value — confirm by grep, and note that the shared-budget
claim is now measured rather than assumed.

- [ ] **Step 6: Fill in the spec's §8**

Complete every row with profile and commit:
- §8.1 — Task 1's pre-slice generator failure (0/N decided), plus Task 4's
  pre-fix FP result and whether it panicked.
- §8.2 — post-slice decided fractions for all three oracles and the thresholds
  chosen, with the reasoning if any threshold moved off `> total / 2`.
- §8.3 — Step 1's verbatim `get-value` / `get-model` output.
- §8.4 — already written by Task 6; verify it is present and complete.
- §8.5 — Steps 4 and 5's oracle summary and PR-tier wall clock.

Change the spec's `**Status:**` from `design` to `implemented`.

- [ ] **Step 7: Final lint and commit**

```bash
cd /workspace
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add -A
git commit -m "docs(bv): slice45 T7 — record measured outcomes, pin the model channel

Measures get-value and get-model on a predicate application rather than
predicting them, and pins the result. get-model still omits p itself: a
function graph needs congruence-class enumeration (slice 43 5, open).

Resolves collect_bv_atoms' naming — it no longer means BitVec atoms — and
records the full unfiltered oracle summary plus PR-tier wall clock with
UF_CONGRUENCE_BUDGET unchanged."
```

- [ ] **Step 8: Whole-branch review before merge**

Slice 43 and slice 44 both had a Critical found by the **whole-branch** review
that every per-task review missed — a wrong get-model default, and a keying
bug in a soundness path. Do not skip this step, and do not defer an
identity/keying "minor" found in it.

Review the complete diff against `main` with fresh eyes, specifically:
- Does anything pair two applications that are not the same function?
- Does any fence widen further than the spec's §2 scope?
- Is there a query shape that decides today and stops deciding? There is no
  named-exception list for this slice.

```bash
cd /workspace
git diff main...HEAD
```

---

## Self-Review

**Spec coverage.** Every spec section maps to a task:

| Spec section | Task |
|---|---|
| §1 probes Q1–Q5 | 3 (Step 1 tests, Step 7 z3/cvc5 cross-check) |
| §1.1 `ite`-lifting | 3 (Steps 1, 6) |
| §2 scope — FP-result, Bool/Int args out | 3 (Step 1 fence tests) |
| §2.1 invariant, no exception list | 3 (Step 9), 7 (Steps 4, 5, 8) |
| §3 the gadget | 2 (Step 3) |
| §3.1 `shape_compatible` unchanged | 2 (Step 1, `bool_and_bv_results_of_one_symbol_are_never_paired`) |
| §3.2(a) `Lowerer::atom` dispatch | 4 (Steps 1–5) |
| §3.2(b) rewrite convergence memo | 2 (Steps 6, 7) |
| §4 collection + both fences | 3 (Steps 3–5) |
| §4.1 renaming | 7 (Step 3) |
| §5 Fence-1 blastability audit | 6 (all steps) |
| §6.1 T1 gate | 1; mirrored in 4 (Step 6), 5 (Step 3) |
| §6.2 T2 direction tests | 2 (Step 1), 3 (Step 1), 4 (Step 1) |
| §6.3 T3 `ite` pins | 3 (Step 1) |
| §6.4 T4 fence pins | 3 (Step 1) |
| §6.5 T5 model channel | 7 (Steps 1, 2) |
| §6.6 T6 non-regression | 3 (Step 9), 7 (Steps 4, 5) |
| §7 success criteria 1–7 | 3, 4, 6, 7 |
| §8 measured outcomes | 1, 4, 6, 7 |

**Placeholder scan.** One deliberate fill-in remains: Task 7 Step 2's test body
says "REPLACE the expectations below with the Step-1 measured strings". That is
intentional and load-bearing — the spec requires the model channel be
*measured* and pinned, not predicted, so writing the assertion in advance would
be exactly the error §6.5 warns against. Task 6's outcome is likewise
branch-dependent by design, with both branches specified.

**Type consistency.** `gen_instance` returns `bool` in Task 1 and Tasks 4–5
mirror that shape. `solve_atoms(&mut Context, &[(TermId, bool)]) -> bool` is
slice 44's existing helper, reused unchanged. `blast_uf_app(sink, ctx, sym,
child_ids, width) -> Vec<BitLit>` is called with `width = 1` and indexed `[0]`
consistently. `result_is_blastable` is introduced and used only within
`walk_uf_args`. Counter names `pred_total` / `pred_decided` are identical
across all three oracles.

---

Plan complete and saved to
`docs/superpowers/plans/2026-07-28-shinri-slice45-bool-uf-congruence.md`.
