# Slice 47 — QF_ABV wrong-`sat` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stop shinri answering `sat` on 359 QF_ABV instances that are `unsat`, by landing a post-solve array-model gate that downgrades a spurious `sat` to a fenced `Unknown`, then using that gate to find and fix the causes.

**Architecture:** The QF_ABV engine is lemmas-on-demand abstraction–refinement: `abstract_arrays` replaces every `select` with a fresh read var and every array-eq atom with a Bool proxy, the SAT layer solves the resulting pure BV+Bool skeleton, and `refine` feeds back array-axiom lemmas until a fixpoint. A spurious `sat` can only come from read vars or proxies holding values no real array can produce, so a new `shinri-abv::validate` module re-derives the array pins from the model and rejects definite violations. Rejection becomes `AbvOutcome::ModelRejected` → `SolveOutcome::Unknown` with fence `abv-model-rejected`, mirroring the existing `str-model-rejected` gate.

**Tech Stack:** Rust workspace, `mise` tasks, `cargo nextest` 0.9.140, `shinri_num::Integer`, `std::collections::BTreeMap`, z3/cvc5 oracles behind `--features oracle`, `shinri-bench` over `bench/corpus/`.

**Spec:** `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md`

## Global Constraints

- **Pure-Rust mandate.** Native-link dependencies are banned; `deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`. Add no new dependency in this slice.
- **Reject only DEFINITE violations.** Where the pinned data leaves an array entry free, the model has real freedom and the gate must stay silent. Over-rejection turns correct answers into fenced unknowns and fails success criterion 2.
- **Never reuse `array_model` for validation.** It pins `default: 0` and drops conflicting reads first-wins (`crates/shinri-abv/src/model.rs:136`), which would mask the violations C1 exists to catch.
- **Oracle runs need `--features oracle`.** Without it the suite silently runs **0 tests** and reads as green. Always confirm a non-zero discovered count.
- **nextest filters use the expression form** `-E 'test(<name>)'`. A positional `mod::name` filter matches nothing on the pinned nextest 0.9.140.
- **`cargo fmt --all` before every push.** CI gates on `fmt --check` and fails fast. `mise run lint` covers fmt + clippy.
- **Blocking PR tier budget: 10–15 min wall-clock.** Any test measured >5 min must be `#[ignore = "exhaustive: nightly tier (~N min in CI)"]`d.
- **`bench-*` tasks are manual and never run in `ci`.** The corpus at `bench/corpus/` is git-ignored.
- **Branch:** `slice47-qfabv-wrong-sat`, PR to `main`, merge commit when CI is green, then delete the branch remote and local.

## File Structure

| File | Responsibility |
| --- | --- |
| `crates/shinri-abv/src/validate.rs` | **Create.** The gate: `pins()`, the four checks, `Rejection` reason type. Self-contained; depends only on `Context`, `SatBridge`, `Abstraction`, `Collected`. |
| `crates/shinri-abv/src/lib.rs` | **Modify.** `pub mod validate;` + re-exports. |
| `crates/shinri-abv/src/driver.rs:37-42` | **Modify.** Add `AbvOutcome::ModelRejected`. |
| `crates/shinri-abv/src/check.rs:99` | **Modify (Task 5).** `accessed_indices` also collects store-chain indices. |
| `crates/shinri-solver/src/abv_stage.rs:706-748` | **Modify.** Call the gate after `refine` returns `Sat`. |
| `crates/shinri-solver/src/lib.rs:976-982` | **Modify.** Map `ModelRejected` → `Unknown` + `abv-model-rejected`. |
| `crates/shinri-solver/tests/qfabv_oracle.rs` | **Modify (Task 1).** Generate store-chain equality and disequality shapes. |
| `crates/shinri-solver/tests/qfabv_wrong_sat_e2e.rs` | **Create (Task 6).** Regression pins from the named reproducers. |
| `crates/shinri-solver/tests/fence_tags.rs` | **Modify (Task 4).** Pin the `abv-model-rejected` tag. |

---

### Task 1: Extend the QF_ABV oracle generator so it reaches the defect

The generator is the reason 359 wrong answers survived a green suite. It equates only **bare array constants** and emits `Store` only as the direct operand of a `Select`, so no store-chain (dis)equality is ever generated.

**This task's acceptance is a FAILING test on unmodified `main`.** If the extended generator passes, it still does not reach the defect and the task is not done.

**Files:**
- Modify: `crates/shinri-solver/tests/qfabv_oracle.rs:224-260` (the array-atom block)

**Interfaces:**
- Consumes: nothing from other tasks.
- Produces: nothing other tasks import. Later tasks re-run this file as a gate.

- [ ] **Step 1: Read the generator's existing shape**

Run: `sed -n '100,300p' crates/shinri-solver/tests/qfabv_oracle.rs`

Note the local helpers in scope: `s` (a `Solver`), `s.eq(a, b)`, `s.app(Op::Builtin(BuiltinOp::Store), &[arr, idx, elt])`, `arrays: Vec<TermId>` (3 arrays `a0 a1 a2`), `idxs: Vec<TermId>`, `elts: Vec<TermId>`, and `rng.next_u32()` on the `Lcg`. Match these names exactly — do not invent new ones.

- [ ] **Step 2: Add a store-chain builder helper**

Add near the other helpers in the file (above `gen_instance`):

```rust
/// Build a `store` chain of `depth` writes over `base`, using index/element
/// terms drawn from `idxs`/`elts` by the `(idx, elt)` pairs in `writes`.
/// `writes` is applied in order, so a later write to the same index wins.
fn store_chain(
    s: &mut Solver,
    base: shinri_core::TermId,
    idxs: &[shinri_core::TermId],
    elts: &[shinri_core::TermId],
    writes: &[(usize, usize)],
) -> shinri_core::TermId {
    let mut acc = base;
    for &(i, e) in writes {
        acc = s.app(
            Op::Builtin(BuiltinOp::Store),
            &[acc, idxs[i % idxs.len()], elts[e % elts.len()]],
        );
    }
    acc
}
```

- [ ] **Step 3: Generate the three new array-atom shapes**

In the array-atom block (around `:224`–`:260`), extend the shape selector with three new arms. Keep the existing arms untouched.

```rust
// Slice 47 shape A: EQUALITY between two store chains of depth >= 2.
// Same base when `same_base`, different bases otherwise.
4 => {
    let same_base = rng.next_u32() % 2 == 0;
    let b0 = arrays[0];
    let b1 = if same_base { arrays[0] } else { arrays[1] };
    let w0 = [(0usize, 0usize), (1, 1)];
    let w1 = [(1usize, 1usize), (0, 0)];
    let c0 = store_chain(s, b0, &idxs, &elts, &w0);
    let c1 = store_chain(s, b1, &idxs, &elts, &w1);
    let atom = s.eq(c0, c1);
    atoms.push(atom);
}
// Slice 47 shape B: DISEQUALITY between two store chains over the SAME base
// writing the SAME index set in OPPOSITE orders — the `wchains002ue` shape.
// Whenever the two orders commute this is UNSAT, which is the case the
// negative extensionality branch must refute.
5 => {
    let w_fwd = [(0usize, 0usize), (1, 1), (2, 2)];
    let w_rev = [(2usize, 2usize), (1, 1), (0, 0)];
    let c0 = store_chain(s, arrays[0], &idxs, &elts, &w_fwd);
    let c1 = store_chain(s, arrays[0], &idxs, &elts, &w_rev);
    let atom = s.eq(c0, c1);
    let neg = s.app(Op::Builtin(BuiltinOp::Not), &[atom]);
    atoms.push(neg);
}
// Slice 47 shape C: a chain that writes the SAME index twice (later wins),
// equated against the single-write chain it must equal.
6 => {
    let w_twice = [(0usize, 0usize), (0, 1)];
    let w_once = [(0usize, 1usize)];
    let c0 = store_chain(s, arrays[0], &idxs, &elts, &w_twice);
    let c1 = store_chain(s, arrays[0], &idxs, &elts, &w_once);
    let atom = s.eq(c0, c1);
    atoms.push(atom);
}
```

Widen the selector's modulus so the new arms are reachable — if the existing code reads `match rng.next_u32() % 4 {`, change it to `% 7`. Check the actual modulus in the file rather than assuming.

- [ ] **Step 4: Add a zero-select instance shape**

The existing generator always emits selects. Add an early return path in `gen_instance` so a fraction of instances contain **no** `Select` at all, leaving the chain atoms with no read to rescue them:

```rust
// Slice 47: 1 instance in 4 carries NO select, so store-chain (dis)equality
// is the only thing constraining the arrays. `wchains002ue` is this shape.
let zero_select = rng.next_u32() % 4 == 0;
```

Guard every block that pushes a `Select`-bearing atom with `if !zero_select { ... }`, and make sure at least one array atom is always pushed so the instance is never empty.

- [ ] **Step 5: Run the extended generator on unmodified `main` and CONFIRM IT FAILS**

```bash
cargo nextest run -p shinri-solver --features oracle -E 'test(qfabv)' 2>&1 | tail -40
```

Expected: **FAIL**, with at least one instance where shinri says `sat` and the oracle says `unsat`.

Confirm a **non-zero discovered count** in the output (`Starting N tests`). If it says `Starting 0 tests`, the filter or the feature flag is wrong — fix that before reading the result.

If the run **passes**, the generator does not reach the defect. Do not proceed. Widen the shapes (deeper chains, more overlapping index sets, more arrays) and repeat this step.

- [ ] **Step 6: Record the failure and commit**

Save the failing output to the task record — the pre-slice failure is success criterion 5 and must be quotable later.

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfabv_oracle.rs
git commit -m "test(qfabv): slice47 T1 - generate store-chain (dis)equality shapes

The generator equated only bare array constants and emitted Store only under
a Select, so the store-chain shapes behind the 359 QF_ABV wrong answers were
unreachable. Adds chain equality, the wchains same-base opposite-order
disequality, a same-index-twice chain, and a zero-select instance shape.

Fails on pre-slice main, which is the point.

Claude-Session: https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM"
```

---

### Task 2: `AbvOutcome::ModelRejected`

A one-variant change, landed on its own so the compiler enumerates every match site before any logic depends on it.

**Files:**
- Modify: `crates/shinri-abv/src/driver.rs:37-42`
- Modify: `crates/shinri-solver/src/abv_stage.rs:728`
- Modify: `crates/shinri-solver/src/lib.rs:976-982`

**Interfaces:**
- Produces: `AbvOutcome::ModelRejected`, consumed by Tasks 3 and 4.

- [ ] **Step 1: Add the variant**

In `crates/shinri-abv/src/driver.rs`, replace the enum:

```rust
/// Outcome of the abstraction-refinement loop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbvOutcome {
    Sat,
    Unsat,
    Unknown,
    /// The loop reached a fixpoint and reported `Sat`, but the post-solve
    /// array-model gate (`crate::validate`) found the model violates an array
    /// axiom, so the `Sat` is spurious. SOUND downgrade to `Unknown` at the
    /// solver boundary — never reported as `sat`.
    ModelRejected,
}
```

- [ ] **Step 2: Build and let the compiler list every match site**

Run: `cargo build --workspace 2>&1 | grep -A 5 "non-exhaustive\|patterns.*not covered"`
Expected: a non-exhaustive-match error at `crates/shinri-solver/src/lib.rs:976`.

- [ ] **Step 3: Handle it at the solver boundary**

In `crates/shinri-solver/src/lib.rs`, extend the match at `:976`:

```rust
return match outcome {
    shinri_abv::AbvOutcome::Sat => SolveOutcome::Sat,
    shinri_abv::AbvOutcome::Unsat => SolveOutcome::Unsat,
    shinri_abv::AbvOutcome::Unknown => {
        self.last_fence = Some("abv-engine");
        SolveOutcome::Unknown
    }
    // Slice 47. The refinement loop's fixpoint is on the LEMMA SET, not on
    // the array axioms, so it can report Sat on a model that no array
    // realises. `validate` catches that; a spurious Sat becomes a SOUND
    // Unknown rather than a wrong answer. Mirrors `str-model-rejected`.
    shinri_abv::AbvOutcome::ModelRejected => {
        self.last_fence = Some("abv-model-rejected");
        SolveOutcome::Unknown
    }
};
```

- [ ] **Step 4: Verify the `!= Sat` early return still behaves**

`crates/shinri-solver/src/abv_stage.rs:728` reads `if outcome != shinri_abv::AbvOutcome::Sat { return (outcome, ..., ...); }`. `ModelRejected != Sat`, so it returns empty model maps — correct, and no change needed. Confirm by reading the line:

Run: `sed -n '726,732p' crates/shinri-solver/src/abv_stage.rs`
Expected: the early return is unchanged and returns `outcome` verbatim.

- [ ] **Step 5: Build and test**

```bash
cargo build --workspace && cargo nextest run -p shinri-abv -p shinri-solver 2>&1 | tail -20
```
Expected: builds clean, all existing tests pass (no behaviour change yet — nothing constructs `ModelRejected`).

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-abv/src/driver.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(abv): slice47 T2 - add AbvOutcome::ModelRejected and its fence

Wires the variant to SolveOutcome::Unknown with the abv-model-rejected fence
tag. Nothing constructs it yet; Task 3 does.

Claude-Session: https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM"
```

---

### Task 3: The gate — `shinri-abv::validate`

Spec §3. Arrays are **partial**: only indices touched by a read or a store are pinned; every other entry is free and can never witness a violation.

**Files:**
- Create: `crates/shinri-abv/src/validate.rs`
- Modify: `crates/shinri-abv/src/lib.rs`

**Interfaces:**
- Consumes: `AbvOutcome::ModelRejected` (Task 2); `Abstraction { read_of, eq_proxy }`, `Collected { selects, array_eqs }`, `SatBridge::{value_bv, value_bool}`.
- Produces:
  - `pub enum Rejection { ReadConflict { array: TermId, index: Integer }, ReadMismatch { select: TermId }, EqPinsDiffer { atom: TermId }, DiseqPinsForceEqual { atom: TermId }, ProxyUnassigned { atom: TermId }, Unsupported { term: TermId, why: &'static str } }`
  - `pub fn validate(ctx: &Context, abs: &Abstraction, c: &Collected, bridge: &dyn SatBridge) -> Result<(), Rejection>`
  - Consumed by Task 4.

- [ ] **Step 1: Write the failing tests**

Create `crates/shinri-abv/src/validate.rs` with the test module first:

```rust
//! Slice 47: the post-solve array-model gate. See
//! `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md` §3.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abstraction::abstract_arrays;
    use crate::collect::collect;
    use crate::driver::fake::FakeBridge;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    fn arr_sort(ctx: &mut Context) -> shinri_core::SortId {
        let i = ctx.bv_sort(8);
        let e = ctx.bv_sort(8);
        ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, n: &str, s: shinri_core::SortId) -> shinri_core::TermId {
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    fn bv(v: u64) -> (u32, Integer) {
        (8, Integer::from(v))
    }

    /// C1: two selects on the SAME array at the SAME index value with
    /// DIFFERENT read values is a definite functional-consistency violation.
    #[test]
    fn c1_rejects_two_reads_same_index_different_values() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let si = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let sj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let atom = ctx.mk_eq(si, sj).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(7));
        b.bv.insert(j, bv(7)); // same index value
        b.bv.insert(abs.read_of[&si], bv(1));
        b.bv.insert(abs.read_of[&sj], bv(2)); // different read values

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::ReadConflict { .. })
        ));
    }

    /// C1 stays SILENT when the index values differ — nothing is pinned twice.
    #[test]
    fn c1_silent_when_indices_differ() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let si = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let sj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let atom = ctx.mk_eq(si, sj).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(7));
        b.bv.insert(j, bv(8)); // different index values
        b.bv.insert(abs.read_of[&si], bv(1));
        b.bv.insert(abs.read_of[&sj], bv(2));

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C1: a read through a store chain must match the chain's pin (ROW).
    #[test]
    fn c1_rejects_read_disagreeing_with_store_pin() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, i]).unwrap();
        let other = uconst(&mut ctx, "o", s8);
        let atom = ctx.mk_eq(sel, other).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(3));
        b.bv.insert(e, bv(9));
        b.bv.insert(abs.read_of[&sel], bv(4)); // must be 9
        b.bv.insert(other, bv(4));

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::ReadMismatch { .. })
        ));
    }

    /// C2-neg: two chains over the SAME base writing the SAME index set with
    /// the SAME values are definitely equal, so a FALSE proxy is a violation.
    /// This is the `wchains002ue` shape.
    #[test]
    fn c2_neg_rejects_false_proxy_on_commuting_chains() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let e = uconst(&mut ctx, "e", s8);
        let f = uconst(&mut ctx, "f", s8);
        // chain1 = store(store(a,i,e),j,f); chain2 = store(store(a,j,f),i,e)
        let c1a = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
        let c1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[c1a, j, f])
            .unwrap();
        let c2a = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, j, f]).unwrap();
        let c2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[c2a, i, e])
            .unwrap();
        let atom = ctx.mk_eq(c1, c2).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(j, bv(2)); // distinct indices ⇒ the writes commute
        b.bv.insert(e, bv(10));
        b.bv.insert(f, bv(20));
        b.boolv.insert(abs.eq_proxy[&atom], false); // claims they differ

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::DiseqPinsForceEqual { .. })
        ));
    }

    /// C2-neg stays SILENT when the chains have DIFFERENT bases: the two base
    /// arrays are free and can be separated at an unpinned index.
    #[test]
    fn c2_neg_silent_on_different_bases() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let a2 = uconst(&mut ctx, "a2", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let c1 = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
        let c2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a2, i, e])
            .unwrap();
        let atom = ctx.mk_eq(c1, c2).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(10));
        b.boolv.insert(abs.eq_proxy[&atom], false);

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C2-pos: a TRUE proxy contradicted by pins that are defined on BOTH
    /// sides and differ.
    #[test]
    fn c2_pos_rejects_true_proxy_when_both_sides_pinned_and_differ() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let f = uconst(&mut ctx, "f", s8);
        let c1 = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
        let c2 = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, f]).unwrap();
        let atom = ctx.mk_eq(c1, c2).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(10));
        b.bv.insert(f, bv(11)); // same index, different value
        b.boolv.insert(abs.eq_proxy[&atom], true);

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::EqPinsDiffer { .. })
        ));
    }

    /// C2-pos stays SILENT when only ONE side is pinned at the index: the
    /// other side is free there and can be made to agree.
    #[test]
    fn c2_pos_silent_when_only_one_side_pinned() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let c1 = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
        let atom = ctx.mk_eq(c1, a).unwrap(); // rhs pins nothing
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(10));
        b.boolv.insert(abs.eq_proxy[&atom], true);

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C3: an unassigned proxy is a rejection, not a don't-care.
    #[test]
    fn c3_rejects_unassigned_proxy() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let a = uconst(&mut ctx, "a", a_s);
        let b_arr = uconst(&mut ctx, "b", a_s);
        let atom = ctx.mk_eq(a, b_arr).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let b = FakeBridge::default(); // no proxy value at all

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::ProxyUnassigned { .. })
        ));
    }

    /// §3.4: an array-sorted `ite` is outside the grammar ⇒ conservative reject.
    #[test]
    fn unsupported_array_ite_is_rejected() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let b_arr = uconst(&mut ctx, "b", a_s);
        let bool_s = ctx.bool_sort();
        let p = uconst(&mut ctx, "p", bool_s);
        let ite = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[p, a, b_arr])
            .unwrap();
        let i = uconst(&mut ctx, "i", s8);
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[ite, i])
            .unwrap();
        let other = uconst(&mut ctx, "o", s8);
        let atom = ctx.mk_eq(sel, other).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(abs.read_of[&sel], bv(1));
        b.bv.insert(other, bv(1));

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::Unsupported { .. })
        ));
    }

    /// The gate must NOT be vacuously rejecting: a genuine model passes.
    #[test]
    fn genuine_model_passes_every_check() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, i]).unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(3));
        b.bv.insert(e, bv(9));
        b.bv.insert(abs.read_of[&sel], bv(9)); // agrees with the store pin

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo nextest run -p shinri-abv -E 'test(validate)' 2>&1 | tail -20`
Expected: FAIL to compile — `cannot find function validate` / `cannot find type Rejection`.

If nextest reports `Starting 0 tests`, the module is not wired; add `pub mod validate;` to `crates/shinri-abv/src/lib.rs` first and re-run.

- [ ] **Step 3: Write the implementation**

Prepend to `crates/shinri-abv/src/validate.rs`, above the test module:

```rust
use std::collections::BTreeMap;

use shinri_num::Integer;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};

use crate::abstraction::Abstraction;
use crate::collect::Collected;
use crate::driver::SatBridge;

/// Why a model was rejected. Carried out of the gate so the caller can report
/// WHICH axiom the model breaks — this is the bisect instrument, not decoration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rejection {
    /// Two reads on the same array at the same index value disagree.
    ReadConflict { array: TermId, index: Integer },
    /// A read disagrees with the pin its store chain forces at that index.
    ReadMismatch { select: TermId },
    /// A TRUE array-eq proxy contradicted by pins defined on both sides.
    EqPinsDiffer { atom: TermId },
    /// A FALSE array-eq proxy on two arrays the pins force to be equal.
    DiseqPinsForceEqual { atom: TermId },
    /// An array-eq proxy with no value in the model.
    ProxyUnassigned { atom: TermId },
    /// An array-sorted term outside the grammar of §3.4.
    Unsupported { term: TermId, why: &'static str },
}

/// The pinned entries of an array term: `base` is the declared array constant
/// at the bottom of the store chain, `points` the indices the model pins.
/// PARTIAL by construction — an index absent from `points` is FREE, and a free
/// entry can never witness a violation.
struct Pins {
    base: TermId,
    points: BTreeMap<Integer, Integer>,
}

/// Extract `(array, index)` from a `select` application.
fn select_parts(ctx: &Context, sel: TermId) -> Option<(TermId, TermId)> {
    match ctx.term_node(sel) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Select),
            args,
            ..
        } => {
            let k = ctx.children(*args);
            Some((k[0], k[1]))
        }
        _ => None,
    }
}

/// Extract `(array, index, element)` from a `store` application.
fn store_parts(ctx: &Context, t: TermId) -> Option<(TermId, TermId, TermId)> {
    match ctx.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Store),
            args,
            ..
        } => {
            let k = ctx.children(*args);
            Some((k[0], k[1], k[2]))
        }
        _ => None,
    }
}

/// True if `t` is a nullary uninterpreted constant — a DECLARED array.
fn is_declared_const(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            matches!(op, Op::Uninterpreted(_)) && ctx.children(*args).is_empty()
        }
        TermNode::Const { .. } => false,
    }
}

/// Pins contributed by the READS on a declared array constant.
///
/// This is where functional consistency is checked, and it is why the gate must
/// NOT reuse `crate::model::array_model`: that function dedups first-wins
/// (`model.rs:136`) and would silently swallow the conflict this detects.
fn base_pins(
    ctx: &Context,
    abs: &Abstraction,
    bridge: &dyn SatBridge,
    arr: TermId,
) -> Result<BTreeMap<Integer, Integer>, Rejection> {
    let mut points: BTreeMap<Integer, Integer> = BTreeMap::new();
    for (&sel, &r) in &abs.read_of {
        let Some((base, idx)) = select_parts(ctx, sel) else {
            continue;
        };
        if base != arr {
            continue;
        }
        let (Some((_, iv)), Some((_, rv))) = (bridge.value_bv(ctx, idx), bridge.value_bv(ctx, r))
        else {
            // No value ⇒ nothing pinned. Not a violation.
            continue;
        };
        if let Some(prev) = points.get(&iv) {
            if prev != &rv {
                return Err(Rejection::ReadConflict {
                    array: arr,
                    index: iv,
                });
            }
        } else {
            points.insert(iv, rv);
        }
    }
    Ok(points)
}

/// Compute the pins of an array-sorted term, walking its store chain down to a
/// declared constant. Anything outside that grammar is a conservative reject.
fn pins(
    ctx: &Context,
    abs: &Abstraction,
    bridge: &dyn SatBridge,
    t: TermId,
) -> Result<Pins, Rejection> {
    if is_declared_const(ctx, t) {
        return Ok(Pins {
            base: t,
            points: base_pins(ctx, abs, bridge, t)?,
        });
    }
    if let Some((inner, i, e)) = store_parts(ctx, t) {
        let mut p = pins(ctx, abs, bridge, inner)?;
        let (Some((_, iv)), Some((_, ev))) = (bridge.value_bv(ctx, i), bridge.value_bv(ctx, e))
        else {
            return Err(Rejection::Unsupported {
                term: t,
                why: "store index or element has no value in the model",
            });
        };
        // A later write to the same index WINS.
        p.points.insert(iv, ev);
        return Ok(p);
    }
    Err(Rejection::Unsupported {
        term: t,
        why: "array term is neither a declared constant nor a store chain",
    })
}

/// Extract the two operands of an array (dis)equality atom.
fn array_pair(ctx: &Context, atom: TermId) -> Option<(TermId, TermId)> {
    match ctx.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Eq),
            args,
            ..
        }
        | TermNode::App {
            op: Op::Builtin(BuiltinOp::Distinct),
            args,
            ..
        } => {
            let k = ctx.children(*args);
            Some((k[0], k[1]))
        }
        _ => None,
    }
}

/// Index/element widths of an array-sorted term.
fn array_widths(ctx: &Context, arr: TermId) -> Option<(u32, u32)> {
    match ctx.sort_node(ctx.sort_of(arr)) {
        SortNode::Array(i, e) => Some((ctx.bv_width(*i)?, ctx.bv_width(*e)?)),
        _ => None,
    }
}

/// The post-solve array-model gate (spec §3).
///
/// Returns `Ok(())` when the model is a genuine QF_ABV witness, and
/// `Err(Rejection)` when it DEFINITELY is not. Underdetermination is NOT a
/// rejection: where the pins leave an entry free the model has real freedom,
/// and rejecting there would turn correct answers into fenced unknowns.
pub fn validate(
    ctx: &Context,
    abs: &Abstraction,
    c: &Collected,
    bridge: &dyn SatBridge,
) -> Result<(), Rejection> {
    // C1 — read soundness. Covers functional consistency (conflicting reads on
    // a bare constant, caught inside `base_pins`) and read-over-write (a read
    // through a chain that disagrees with the chain's pin), in one pass.
    for (&sel, &r) in &abs.read_of {
        let Some((arr, idx)) = select_parts(ctx, sel) else {
            continue;
        };
        let p = pins(ctx, abs, bridge, arr)?;
        let (Some((_, iv)), Some((_, rv))) = (bridge.value_bv(ctx, idx), bridge.value_bv(ctx, r))
        else {
            continue;
        };
        if let Some(pinned) = p.points.get(&iv) {
            if pinned != &rv {
                return Err(Rejection::ReadMismatch { select: sel });
            }
        }
    }

    // C2 / C3 — the array (dis)equality atoms.
    for &atom in &c.array_eqs {
        let Some((a, b)) = array_pair(ctx, atom) else {
            continue;
        };
        let Some(&proxy) = abs.eq_proxy.get(&atom) else {
            continue;
        };
        // §3.4: mismatched widths are outside the grammar.
        match (array_widths(ctx, a), array_widths(ctx, b)) {
            (Some(wa), Some(wb)) if wa == wb => {}
            _ => {
                return Err(Rejection::Unsupported {
                    term: atom,
                    why: "array-eq operands have mismatched or non-BV index/element widths",
                })
            }
        }

        // C3 — proxy totality.
        let Some(pv) = bridge.value_bool(proxy) else {
            return Err(Rejection::ProxyUnassigned { atom });
        };

        let pa = pins(ctx, abs, bridge, a)?;
        let pb = pins(ctx, abs, bridge, b)?;

        if pv {
            // C2-pos: reject only where BOTH sides are pinned and differ.
            for (k, va) in &pa.points {
                if let Some(vb) = pb.points.get(k) {
                    if va != vb {
                        return Err(Rejection::EqPinsDiffer { atom });
                    }
                }
            }
        } else {
            // C2-neg: reject only when the arrays are DEFINITELY equal, i.e.
            // they share a base AND every index in the union of the two pin
            // sets is pinned on both sides with equal values. A one-sided pin
            // leaves that entry free on the other side, so the disequality is
            // still satisfiable and the gate must stay silent.
            if pa.base == pb.base
                && pa.points.len() == pb.points.len()
                && pa
                    .points
                    .iter()
                    .all(|(k, va)| pb.points.get(k) == Some(va))
            {
                return Err(Rejection::DiseqPinsForceEqual { atom });
            }
        }
    }

    Ok(())
}
```

- [ ] **Step 4: Wire the module**

In `crates/shinri-abv/src/lib.rs`:

```rust
pub mod validate;
```

and extend the re-export line:

```rust
pub use validate::{validate, Rejection};
```

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo nextest run -p shinri-abv -E 'test(validate)' 2>&1 | tail -25`
Expected: PASS, with a **non-zero** discovered count — 10 tests.

- [ ] **Step 6: Lint and commit**

```bash
cargo fmt --all
cargo clippy -p shinri-abv --all-targets -- -D warnings
git add crates/shinri-abv/src/validate.rs crates/shinri-abv/src/lib.rs
git commit -m "feat(abv): slice47 T3 - the post-solve array-model gate

Arrays are PARTIAL: only indices a read or a store touches are pinned, and a
free entry can never witness a violation, so the gate rejects only DEFINITE
violations. C1 subsumes functional consistency and read-over-write; C2-pos
catches a true proxy the pins refute; C2-neg catches a false proxy the pins
force equal (the wchains shape); C3 catches an unassigned proxy.

Deliberately does NOT reuse array_model, which pins default 0 and dedups
conflicting reads first-wins - it would mask exactly what C1 detects.

Not called yet; Task 4 hooks it.

Claude-Session: https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM"
```

---

### Task 4: Hook the gate into the solver

**Files:**
- Modify: `crates/shinri-solver/src/abv_stage.rs:706-748`
- Modify: `crates/shinri-solver/tests/fence_tags.rs`

**Interfaces:**
- Consumes: `shinri_abv::validate` and `Rejection` (Task 3), `AbvOutcome::ModelRejected` (Task 2).
- Produces: fence tag `"abv-model-rejected"`, consumed by Tasks 5–7 as the bisect instrument.

- [ ] **Step 1: Write the failing fence test**

Append to `crates/shinri-solver/tests/fence_tags.rs`:

```rust
/// Slice 47: a spurious QF_ABV `sat` is downgraded to a fenced Unknown rather
/// than reported. `wchains002ue`-shaped: two store chains over the same base
/// writing the same index set in opposite orders, asserted DISTINCT. The
/// writes commute, so the assertion is unsat and any `sat` is spurious.
#[test]
fn qfabv_spurious_sat_is_tagged_or_decided() {
    let (r, tag) = run(
        "(set-logic QF_ABV)\
         (declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))\
         (declare-fun i () (_ BitVec 4))(declare-fun j () (_ BitVec 4))\
         (declare-fun e () (_ BitVec 4))(declare-fun f () (_ BitVec 4))\
         (assert (distinct i j))\
         (assert (distinct (store (store a i e) j f) (store (store a j f) i e)))\
         (check-sat)",
    );
    // The writes commute when i != j, so this is UNSAT. Either the engine
    // decides it (best) or the gate downgrades it (sound). What must NEVER
    // happen is a bare `sat`.
    match r {
        Some(CommandResponse::Unsat) => assert_eq!(tag, None),
        Some(CommandResponse::Unknown) => assert_eq!(tag, Some("abv-model-rejected")),
        other => panic!("QF_ABV commuting-store disequality must not be sat: {other:?}"),
    }
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo nextest run -p shinri-solver -E 'test(qfabv_spurious_sat_is_tagged_or_decided)' 2>&1 | tail -20`
Expected: **FAIL** with a panic reading `must not be sat: Some(Sat)`.

Confirm the discovered count is 1, not 0.

- [ ] **Step 3: Call the gate**

In `crates/shinri-solver/src/abv_stage.rs`, inside `solve_qfabv_with_models`, replace the early-return block after `refine`:

```rust
    let outcome = refine(ctx, &mut abs, &mut c, &mut bridge);

    if outcome != shinri_abv::AbvOutcome::Sat {
        return (outcome, FxHashMap::default(), FxHashMap::default());
    }

    // Slice 47: the refinement loop's fixpoint is on the LEMMA SET, not on the
    // array axioms, so it can report Sat on a model no array realises. Re-derive
    // the array pins from the model and reject a DEFINITE violation. Sound
    // downgrade: a rejected Sat becomes Unknown, never a wrong `sat`.
    if let Err(reason) = shinri_abv::validate(ctx, &abs, &c, &bridge) {
        // The reason is the bisect instrument (spec §3.5): it names WHICH axiom
        // the model breaks, so a failing corpus row can be attributed without a
        // full re-run against an oracle.
        if std::env::var_os("SHINRI_ABV_DEBUG").is_some() {
            eprintln!("abv-model-rejected: {reason:?}");
        }
        return (
            shinri_abv::AbvOutcome::ModelRejected,
            FxHashMap::default(),
            FxHashMap::default(),
        );
    }
```

Import `validate` alongside the other `shinri_abv` items already imported in the function.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cargo nextest run -p shinri-solver -E 'test(qfabv_spurious_sat_is_tagged_or_decided)' 2>&1 | tail -20`
Expected: PASS.

- [ ] **Step 5: Check the gate did not break the existing QF_ABV suite**

```bash
cargo nextest run -p shinri-abv -p shinri-solver 2>&1 | tail -30
```
Expected: all pass. **Any previously-`Sat` QF_ABV test that now returns `Unknown` is an over-rejection** — a criterion-2 regression in miniature. Do not relax the test; fix the gate.

- [ ] **Step 6: Verify the fence on the real reproducers**

```bash
cargo build --release -p shinri-cli
for f in brummayerbiere/wchains002ue.smt2 brummayerbiere/bubsort002un.smt2; do
  echo "== $f"
  SHINRI_ABV_DEBUG=1 ./target/release/shinri "bench/corpus/QF_ABV/$f" 2>&1 | tail -3
done
```
Expected: `unknown` (with a printed rejection reason) or `unsat`. **Never `sat`.**

Record the rejection reason for each — Task 5 starts from it.

- [ ] **Step 7: Lint and commit**

```bash
cargo fmt --all
mise run lint
git add crates/shinri-solver/src/abv_stage.rs crates/shinri-solver/tests/fence_tags.rs
git commit -m "feat(abv): slice47 T4 - gate the QF_ABV sat path on the model validator

A spurious sat now returns AbvOutcome::ModelRejected and surfaces as Unknown
with the abv-model-rejected fence. Shinri is sound on the 359 measured QF_ABV
wrong answers from here, whatever the remaining tasks find.

SHINRI_ABV_DEBUG=1 prints the rejection reason - the Task 5 bisect instrument.

Claude-Session: https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM"
```

---

### Task 5: The latent `accessed_indices` fix

Independent of the bisect, confirmed by reading the code, and cheap. Spec §4.

`accessed_indices` builds the extensionality index set solely from `c.selects`, so a positively asserted equality between two store chains with no selects over them is enforced at **zero** indices.

**Files:**
- Modify: `crates/shinri-abv/src/check.rs:99`
- Test: `crates/shinri-abv/src/check.rs` (its existing `mod tests`)

**Interfaces:**
- Consumes: nothing from other tasks.
- Produces: no new public API — `accessed_indices` is private.

- [ ] **Step 1: Write the failing test**

Add to `mod tests` in `crates/shinri-abv/src/check.rs`:

```rust
/// Slice 47: extensionality's positive branch must enforce agreement at the
/// indices a store CHAIN writes, not only at indices some `select` reads.
/// With no selects at all the old code enforced nothing.
#[test]
fn accessed_indices_includes_store_chain_indices() {
    let mut ctx = Context::new();
    let arr_s = arr(&mut ctx);
    let s8 = ctx.bv_sort(8);
    let a = uconst(&mut ctx, "a", arr_s);
    let i = uconst(&mut ctx, "i", s8);
    let j = uconst(&mut ctx, "j", s8);
    let e = uconst(&mut ctx, "e", s8);
    let f = uconst(&mut ctx, "f", s8);
    let c0 = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
    let c1 = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, j, f]).unwrap();
    let atom = ctx.mk_eq(c0, c1).unwrap();
    let c = collect(&ctx, &[atom]);

    let got = accessed_indices(&ctx, &c, c0, c1);

    assert!(got.contains(&i), "store index i must be an accessed index");
    assert!(got.contains(&j), "store index j must be an accessed index");
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo nextest run -p shinri-abv -E 'test(accessed_indices_includes_store_chain_indices)' 2>&1 | tail -15`
Expected: FAIL — `store index i must be an accessed index` (the returned vec is empty; there are no selects).

- [ ] **Step 3: Implement**

Replace `accessed_indices` in `crates/shinri-abv/src/check.rs`:

```rust
/// Push every index written along `t`'s store chain into `out`.
fn store_chain_indices(ctx: &Context, t: TermId, out: &mut Vec<TermId>) {
    let mut cur = t;
    while let Some((inner, i, _e)) = store_parts(ctx, cur) {
        out.push(i);
        cur = inner;
    }
}

/// Index terms relevant to extensionality over `a` and `b`: the indices of all
/// selects whose base is `a` or `b`, PLUS every index either operand's store
/// chain writes.
///
/// Slice 47: the store-chain half was missing, so an equality between two store
/// chains with no selects over them was enforced at ZERO indices — the positive
/// branch emitted nothing and the proxy was a free Boolean.
fn accessed_indices(ctx: &Context, c: &Collected, a: TermId, b: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    for &sel in &c.selects {
        if let Some((base, idx)) = select_parts(ctx, sel) {
            if base == a || base == b {
                out.push(idx);
            }
        }
    }
    store_chain_indices(ctx, a, &mut out);
    store_chain_indices(ctx, b, &mut out);
    out.dedup();
    out
}
```

`store_parts` and `select_parts` already exist in this file — do not redefine them.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cargo nextest run -p shinri-abv -E 'test(accessed_indices)' 2>&1 | tail -15`
Expected: PASS.

- [ ] **Step 5: Run the whole QF_ABV suite for cost regressions**

```bash
cargo nextest run -p shinri-abv -p shinri-solver 2>&1 | tail -20
```
Expected: all pass. Widening the index set means more lemmas per round; if any test now takes visibly longer, note it — success criterion 3 (`timeout ≤ 361`) is the real check and Task 7 measures it.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-abv/src/check.rs
git commit -m "fix(abv): slice47 T5 - extensionality also indexes store-chain writes

accessed_indices built its index set solely from c.selects, so a positively
asserted equality between two store chains with no selects over them was
enforced at zero indices and the proxy stayed a free Boolean. Now the indices
written along both operands' chains are included.

Latent defect found by reading the code; no measured row is known to depend
on it.

Claude-Session: https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM"
```

---

### Task 6: Bisect the measured shapes and fix what the gate names

This is the only open-ended task. It starts from the Task 4 rejection reasons and ends when the named reproducers answer `unsat`.

**Spec §9 hypothesis 3 is the first thing to instrument**, because it explains the `wchains` shape concretely: the negative extensionality branch mints a witness `w` and emits `p ∨ (a[w] ≠ b[w])`, after which ROW must unfold `select(CHAIN, w)` through eight store levels per side. Every ROW guard fires only when the *current* model disagrees, so a model that happens to agree at each examined level ends the round with no new lemma and `refine` reports `Sat` before the chains are fully unfolded.

**Files:**
- Modify: `crates/shinri-abv/src/check.rs` and/or `crates/shinri-abv/src/driver.rs` (whatever the bisect names)
- Create: `crates/shinri-solver/tests/qfabv_wrong_sat_e2e.rs`

**Interfaces:**
- Consumes: `SHINRI_ABV_DEBUG` rejection reasons (Task 4).
- Produces: no new public API.

- [ ] **Step 1: Instrument the refinement loop**

Add a temporary trace behind the existing env var in `crates/shinri-abv/src/driver.rs`'s `refine` loop, printing per round: round number, lemma count emitted, `added.len()`, and the value of `progress`.

```rust
if std::env::var_os("SHINRI_ABV_DEBUG").is_some() {
    eprintln!(
        "abv round: emitted={} added_total={} progress={}",
        round_len, added.len(), progress
    );
}
```

Capture `round_len` before the `for lemma in round` loop consumes it.

- [ ] **Step 2: Run the trace on the two smallest reproducers**

```bash
cargo build --release -p shinri-cli
SHINRI_ABV_DEBUG=1 ./target/release/shinri \
  bench/corpus/QF_ABV/brummayerbiere/wchains002ue.smt2 2>&1 | tail -30
SHINRI_ABV_DEBUG=1 ./target/release/shinri \
  bench/corpus/QF_ABV/brummayerbiere/bubsort002un.smt2 2>&1 | tail -30
```

Read the trace against hypothesis 3: does the loop stop with `progress=false` while the chain is only partly unfolded? Record the answer — confirming or discarding a hypothesis is a result either way.

- [ ] **Step 3: Write the failing e2e pins BEFORE fixing**

Create `crates/shinri-solver/tests/qfabv_wrong_sat_e2e.rs`:

```rust
//! Slice 47: regression pins for the QF_ABV wrong-`sat` cluster. Each fixture
//! is a hand-reduced form of a named reproducer from
//! `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md` §8.
//! All are UNSAT. A `sat` here is a soundness regression; an `unknown` means
//! the gate caught it but the engine still cannot decide it.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn run(src: &str) -> Option<CommandResponse> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut last = None;
    while let Some(r) = parser.next_command(solver.ctx_mut()) {
        let cmd = r.expect("fixture parses");
        let resp = solver.execute(cmd);
        if !matches!(resp, CommandResponse::None) {
            last = Some(resp);
        }
    }
    last
}

/// `wchains002ue` reduced: two chains over the same base writing the same two
/// indices in opposite orders. The writes commute when i != j, so asserting
/// the chains differ is UNSAT.
#[test]
fn commuting_store_chains_are_not_distinct() {
    let r = run(
        "(set-logic QF_ABV)\
         (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 8))(declare-fun j () (_ BitVec 8))\
         (declare-fun e () (_ BitVec 8))(declare-fun f () (_ BitVec 8))\
         (assert (distinct i j))\
         (assert (distinct (store (store a i e) j f) (store (store a j f) i e)))\
         (check-sat)",
    );
    assert_eq!(r, Some(CommandResponse::Unsat));
}

/// `bubsort002un` reduced: a read of a doubly-stored array at the first store's
/// index, where the second store writes a different index, must equal the first
/// store's element.
#[test]
fn read_through_two_stores_is_pinned() {
    let r = run(
        "(set-logic QF_ABV)\
         (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 8))(declare-fun j () (_ BitVec 8))\
         (declare-fun e () (_ BitVec 8))(declare-fun f () (_ BitVec 8))\
         (assert (distinct i j))\
         (assert (distinct (select (store (store a i e) j f) i) e))\
         (check-sat)",
    );
    assert_eq!(r, Some(CommandResponse::Unsat));
}

/// A store chain equated to itself under a different write order, positively
/// asserted — the shape Task 5's `accessed_indices` fix serves.
#[test]
fn commuting_store_chains_are_equal() {
    let r = run(
        "(set-logic QF_ABV)\
         (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 8))(declare-fun j () (_ BitVec 8))\
         (declare-fun e () (_ BitVec 8))(declare-fun f () (_ BitVec 8))\
         (assert (distinct i j))\
         (assert (= (store (store a i e) j f) (store (store a j f) i e)))\
         (check-sat)",
    );
    assert_eq!(r, Some(CommandResponse::Sat));
}
```

- [ ] **Step 4: Run them to see which fail**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfabv_wrong_sat_e2e)' 2>&1 | tail -25`

Note the **binary** filter form — `test(qfabv_wrong_sat_e2e)` finds 0 tests because that is a binary name, not a test name.

Expected: at least one FAIL. A test returning `Unknown` means the gate is working but the engine still cannot decide the shape; a test returning `Sat` on the first two means the gate has a hole and Task 3 needs revisiting first.

- [ ] **Step 5: Fix the cause the trace named**

Implement the fix the Step 2 trace points at. If it is hypothesis 3, the shape of the fix is to make `refine`'s termination a fixpoint on the **axioms** rather than on the lemma set — for example, by running `validate` inside the loop and, on rejection, forcing another round that unfolds the offending chain instead of returning `Sat`.

Do **not** implement a fix for a cause the trace has not demonstrated. If the trace discards all three hypotheses, record what it showed and re-instrument; the gate keeps the engine sound in the meantime.

- [ ] **Step 6: Run the pins to verify they pass**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfabv_wrong_sat_e2e)' 2>&1 | tail -25`
Expected: PASS, 3 tests.

- [ ] **Step 7: Verify on the real reproducers**

```bash
cargo build --release -p shinri-cli
for f in brummayerbiere/wchains002ue.smt2 brummayerbiere/bubsort002un.smt2 \
         dwp_formulas/try5_small_difret_functions_wp_chgrp.i_ring_empty.il.wp.smt2 \
         brummayerbiere2/countbitstable016.smt2; do
  printf "%-60s %s\n" "$f" "$(timeout 120 ./target/release/shinri "bench/corpus/QF_ABV/$f" 2>&1 | tail -1)"
done
```
Expected: `unsat` on each. `unknown` is sound but leaves rows on the table; `sat` is a failure.

- [ ] **Step 8: Remove the temporary trace, lint, commit**

Keep the `SHINRI_ABV_DEBUG` rejection print from Task 4 (it is the documented instrument); remove the per-round `refine` trace added in Step 1 unless it earned its place.

```bash
cargo fmt --all
mise run lint
cargo nextest run -p shinri-abv -p shinri-solver 2>&1 | tail -20
git add -A
git commit -m "fix(abv): slice47 T6 - <name the cause the bisect actually found>

<What the trace showed, which hypothesis it confirmed or discarded, and why
the fix addresses it. Cite the reproducer that now returns unsat.>

Claude-Session: https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM"
```

---

### Task 7: Measure, and close the slice on numbers

The slice ends on a committed run report, not on a code-complete claim.

**Files:**
- Create: `docs/superpowers/research/2026-09-09-smtlib-2024-qfabv-slice47-report.md`
- Modify: `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md` (a `## 11. Measured outcomes` section)

**Interfaces:**
- Consumes: everything above.
- Produces: the report the next slice cites.

- [ ] **Step 1: Run the full oracle suite, unfiltered**

Because this slice changes `shinri-abv` and the shared `abv_stage` bridge, the closing oracle run is the **full unfiltered** suite. A filtered run has previously skipped the file that would have caught a regression.

```bash
cargo nextest run -p shinri-solver --features oracle 2>&1 | tail -30
```
Expected: PASS. Record the discovered test count; a count of 0 is not green.

- [ ] **Step 2: Re-run QF_ABV over the corpus**

```bash
BENCH_LOGICS=QF_ABV BENCH_RUN_ID=slice47 mise run bench-run
BENCH_RUN_ID=slice47 mise run bench-report
```

This is ~15,148 instances and takes roughly half an hour to an hour at `BENCH_JOBS=6`. It is a manual task and never runs in CI.

- [ ] **Step 3: Check every success criterion against the report**

Read `bench/results/slice47/report.md` and fill this in:

| criterion | baseline | slice47 | pass? |
| --- | ---: | ---: | --- |
| 1. `wrong` = 0 | 359 | | |
| 2. `correct` ≥ 8,454 | 8,454 | | |
| 3. `timeout` ≤ 361 | 361 | | |
| 4. `abv-model-rejected` rows | n/a | | report count + families |
| 5. generator failed pre-slice, passes now | — | | |
| 6. panic / parse-error / oom unchanged | 5,787 / 26 / 98 | | explain any movement |

If criterion 1 fails, return to Task 6 with the still-failing families. If criterion 2 or 3 fails, the gate over-rejects or the widened index set costs too much — fix rather than relax the criterion.

- [ ] **Step 4: Commit the run report**

```bash
cp bench/results/slice47/report.md \
   docs/superpowers/research/2026-09-09-smtlib-2024-qfabv-slice47-report.md
git add docs/superpowers/research/2026-09-09-smtlib-2024-qfabv-slice47-report.md
git commit -m "docs(bench): slice47 - QF_ABV re-run report

Claude-Session: https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM"
```

- [ ] **Step 5: Write the measured-outcomes section into the spec**

Append `## 11. Measured outcomes` to the spec with the Step 3 table, the pre-slice generator failure from Task 1 Step 6, the causes the Task 6 bisect actually found (and any hypothesis it discarded), and the `abv-model-rejected` row count with its families if non-zero.

State plainly if a criterion was missed. A residual fenced-unknown count is a sound, honest result — it belongs in the report and in the next slice's queue, not hidden.

- [ ] **Step 6: Final hygiene and push**

```bash
cargo fmt --all
mise run lint
mise run test 2>&1 | tail -20
git add -A && git commit -m "docs(spec): slice47 - measured outcomes

Claude-Session: https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM"
git push -u origin slice47-qfabv-wrong-sat
```

- [ ] **Step 7: Open the PR**

```bash
gh pr create --base main --title "slice47: QF_ABV wrong-sat - array-model gate and the fixes it named" --body "$(cat <<'EOF'
Rank 1 of the slice-46 baseline queue: 359 QF_ABV rows answered `sat` where the
reference is `unsat`.

Lands a post-solve array-model gate that rejects only DEFINITE violations and
downgrades a spurious `sat` to a fenced `Unknown`, then fixes the causes the
gate named.

Measured against `baseline-8de004d44944`; see
`docs/superpowers/research/2026-09-09-smtlib-2024-qfabv-slice47-report.md`.

Out of scope and reported unchanged: the blast_word panics and stack overflows.

https://claude.ai/code/session_017jU6ZC7i25FBLky8BpSufM
EOF
)"
```

Merge with a merge commit when CI is green, then delete the branch remote and local.

---

## Self-Review

**Spec coverage:**

| spec section | task |
| --- | --- |
| §3.2 pins, partial arrays, no `array_model` reuse | Task 3 Step 3 (`base_pins`, `pins`) |
| §3.3 C1 | Task 3 (`validate` C1 loop; 3 tests) |
| §3.3 C2-pos | Task 3 (2 tests: rejects, and stays silent one-sided) |
| §3.3 C2-neg | Task 3 (2 tests: rejects commuting chains, silent on different bases) |
| §3.3 C3 | Task 3 (`ProxyUnassigned`) |
| §3.4 conservative rejection | Task 3 (`Rejection::Unsupported`, ite test, width check) |
| §3.5 hook + fence + rejection reason | Task 4 |
| §4 latent `accessed_indices` | Task 5 |
| §5 task 1 generator | Task 1 |
| §6.1 fences | Task 3 Step 1 |
| §6.2 regression pins | Task 6 Step 3 |
| §6.3 oracle, unfiltered | Task 7 Step 1 |
| §7 criteria 1–6 | Task 7 Step 3 |
| §9 hypotheses | Task 6 Steps 1–2 |

**Known gap, stated rather than papered over:** Task 6 Step 5 cannot contain the real fix, because no cause of a measured wrong answer is diagnosed yet — that is the spec's §4 position, not an oversight. The step tells the implementer what to instrument, what hypothesis to test first, and explicitly forbids implementing a fix for a cause the trace has not demonstrated. Tasks 1–5 and 7 are fully specified.

**Type consistency:** `validate(ctx, abs, c, bridge) -> Result<(), Rejection>` is used identically in Task 3's tests, Task 3's implementation, and Task 4's call site. `Rejection` variant names match between the enum definition and every `matches!` assertion. `AbvOutcome::ModelRejected` is defined in Task 2 and used in Tasks 2 and 4. `store_chain(s, base, idxs, elts, writes)` is defined and used only within Task 1.
