# Slice 43 — Model Channel Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `get-model` / `get-value` emit conformant SMT-LIB `define-fun` output with real datatype field values, no internal `tN` names, and no missing declared symbols.

**Architecture:** Two independent halves. Combiner-side, `DtSolver::model` moves to run **last, directly into the shared `combined` builder** — the pattern `StrSolver` already uses to read arith's `(str.len ·)` values — so datatype field values resolve from whichever theory owns them; inside the Combiner every TermId is valid, which is what makes in-search-minted selector applications reachable. Solver-side, `format_model` stops iterating the theory value map and instead enumerates a new registry of user-declared symbols, printing each as a `define-fun` with a new `shinri-core` sort printer.

**Tech Stack:** Rust (workspace, edition/rust-version pinned in `Cargo.toml`), `cargo nextest` 0.9.140, mise task runner, z3/cvc5 for the oracle tier.

**Spec:** [docs/superpowers/specs/2026-07-25-shinri-slice43-model-channel-design.md](../specs/2026-07-25-shinri-slice43-model-channel-design.md). Read §2 (the invariant) and §3.C (the branch-order fence) before starting.

## Global Constraints

- **This slice cannot change a verdict** (spec §2). Every edit is downstream of `SolveResult::Sat`. Any `sat`/`unsat`/`unknown` flip in any direction is a regression — there is **no adjudicated-flip escape hatch** here, unlike slice 42 §4.A. Stop and diagnose.
- `cargo fmt --all` before every push. CI gates on `fmt --check` and fails fast.
- `cargo clippy --workspace --all-targets -- -D warnings` must be clean. `mise run lint` covers fmt + clippy.
- nextest filters use the expression form `-E 'test(<name>)'`, never a positional `mod::name` filter — the latter matches nothing on the pinned nextest 0.9.140. **Always confirm a non-zero discovered test count**; a 0-test run reads as green.
- Oracle tests are feature-gated: `cargo nextest run -p shinri-solver --features oracle`. **Without `--features oracle` they compile to zero tests.** Never report a flagless run as coverage.
- Pure-Rust mandate: no new native-link dependencies. This slice adds no dependencies at all.
- `get-model` output must remain **a single line**. `crates/shinri-solver/tests/qfbv_witnesses.rs:279` asserts `out.len() >= 2` and reads `out[1]` as the entire model.
- Do **not** touch `crates/shinri-abv/src/model.rs`. It has its own private copies of `format_hex_fixed`/`format_bin_fixed`; that duplication is pre-existing and out of scope.

## File Structure

| File | Responsibility | Task |
|---|---|---|
| `crates/shinri-theory/src/model.rs` | `ModelBuilder` **+ (new) `ModelVal` → SMT-LIB text formatting**, relocated so every theory can call it | 1 |
| `crates/shinri-solver/src/model.rs` | `Model`, `SolveOutcome`, BV extraction. Loses the formatting helpers | 1 |
| `crates/shinri-theory/src/combiner.rs` | `build_model` ordering: DT last, into `combined` | 2 |
| `crates/shinri-euf/src/solver.rs` | `model` skips datatype sorts (DT owns them) | 2 |
| `crates/shinri-dt/src/lib.rs` | `render_value`/`render_value_inner` consult the builder; new `render_field` | 2 |
| `crates/shinri-core/src/context.rs` | **(new)** `sort_name` — exhaustive `SortId` → SMT-LIB text | 3 |
| `crates/shinri-solver/src/lib.rs` | **(new)** declared-symbol registry; `format_model` → `define-fun`; sort defaults; `GetValue` labels | 4, 5, 6 |
| `crates/shinri-solver/src/tseitin.rs` | `display_term` prints full applications | 6 |
| `crates/shinri-solver/tests/qfdt_model_e2e.rs` | **(new)** the model-channel gate: exact expected output | 2, 5, 6, 7 |

**Why the gate is Task 2 and not Task 1.** Spec §6 requires the measured e2e gate early, because slice 42 implemented its plan exactly, passed every per-task review, and delivered nothing — its premise was wrong and only the end-to-end gate caught it, having been scheduled second-to-last. Task 1 here is a pure mechanical file move with no behaviour to gate. **Task 2 is the premise gate**: it asserts against the real binary that a datatype field renders its arith-assigned value. If Task 2's test does not go green, the premise ("the value is already in `arith_m`, it just isn't reachable") is wrong and the design needs revisiting — not the test.

Task 2 deliberately asserts with `contains`, in the **current** output shape. Exact-string assertions only become possible once Task 5 makes output deterministic; Task 5 converts them.

---

### Task 1: Relocate value formatting into `shinri-theory`

`shinri-dt` needs to turn a `ModelVal` into SMT-LIB text (Task 2), but the formatter lives in `shinri-solver`, which sits *above* `shinri-dt` in the dependency order. Move it down beside `ModelBuilder`. Pure code motion: no behaviour changes, and the existing tests are the proof.

**Note on imports:** `shinri-theory` has **no `shinri-num` dependency** (see `crates/shinri-theory/Cargo.toml`). The moved code must use `shinri_core::{Integer, Rational}`, which `shinri-core` re-exports at `crates/shinri-core/src/lib.rs:19` (`pub use shinri_num::{DeltaRational, Integer, Rational};`). These are the same types, so no logic changes — only the paths.

**Files:**
- Modify: `crates/shinri-theory/src/model.rs` (append the formatters + their tests)
- Modify: `crates/shinri-solver/src/model.rs:26-82` and `:84-201` (delete the formatters and their tests)
- Modify: `crates/shinri-solver/src/lib.rs:329`, `:332`, `:349` (three call sites)

**Interfaces:**
- Consumes: nothing.
- Produces: `shinri_theory::model::format_modelval(v: &ModelVal) -> String` and `shinri_theory::model::format_rational(r: &Rational) -> String`, both `pub`. Task 2 calls both from `shinri-dt`.

- [ ] **Step 1: Confirm the existing tests pass before moving anything**

Run: `cargo nextest run -p shinri-solver -E 'test(format_string_modelval_escapes_quotes) or test(format_float_modelval_as_fp_triple)'`
Expected: PASS, **2 tests discovered**. If 0 are discovered, the filter is wrong — fix that before proceeding.

- [ ] **Step 2: Append the formatters to `crates/shinri-theory/src/model.rs`**

Add at the top of the file, after the existing `use` lines:

```rust
use shinri_core::{Integer, Rational};
```

Then append at end of file (before any `#[cfg(test)]` block):

```rust
/// Format a `Rational` as SMT-LIB: `n` if integral, else `(/ n d)`; negatives
/// as `(- …)`.
pub fn format_rational(r: &Rational) -> String {
    let n = r.numer();
    let d = r.denom();
    if d == Integer::one() {
        if n.is_negative() {
            format!("(- {})", n.abs())
        } else {
            n.to_string()
        }
    } else if n.is_negative() {
        format!("(- (/ {} {}))", n.abs(), d)
    } else {
        format!("(/ {n} {d})")
    }
}

/// Format an `Integer` as fixed-width hexadecimal with exactly `digits` hex
/// digits (zero-padded, no prefix).
fn format_hex_fixed(val: &Integer, digits: usize) -> String {
    let sixteen = Integer::from(16u64);
    let mut remaining = val.clone();
    let mut nibbles: Vec<u8> = Vec::with_capacity(digits);
    for _ in 0..digits {
        let (q, r) = remaining.div_rem(&sixteen);
        let nibble = r.to_i128().unwrap_or(0) as u8;
        nibbles.push(nibble);
        remaining = q;
    }
    nibbles.reverse();
    nibbles.iter().map(|&n| format!("{:x}", n)).collect::<String>()
}

/// Format an `Integer` as a binary string with exactly `width` bits (MSB first,
/// zero-padded).
fn format_bin_fixed(val: &Integer, width: u32) -> String {
    let two = Integer::from(2u64);
    let mut remaining = val.clone();
    let mut bits: Vec<u8> = Vec::with_capacity(width as usize);
    for _ in 0..width {
        let (q, r) = remaining.div_rem(&two);
        bits.push(r.to_i128().unwrap_or(0) as u8);
        remaining = q;
    }
    bits.reverse();
    bits.iter().map(|&b| if b == 1 { '1' } else { '0' }).collect()
}

/// Format a single `ModelVal` as SMT-LIB text.
pub fn format_modelval(v: &ModelVal) -> String {
    match v {
        ModelVal::Bool(b) => {
            if *b {
                "true".into()
            } else {
                "false".into()
            }
        }
        ModelVal::Num(r) => format_rational(r),
        ModelVal::Elem(_, idx) => format!("@elem{idx}"),
        ModelVal::String(s) => format!("\"{}\"", s.replace('"', "\"\"")),
        ModelVal::BitVec(width, val) => {
            if width % 4 == 0 {
                let digits = (width / 4) as usize;
                format!("#x{}", format_hex_fixed(val, digits))
            } else {
                format!("#b{}", format_bin_fixed(val, *width))
            }
        }
        ModelVal::Float { eb, sb, bits } => {
            let two = Integer::from(2u64);
            let mut modulus = Integer::one();
            for _ in 0..(sb - 1) {
                modulus *= two.clone();
            }
            let sig = bits.div_rem(&modulus).1;
            let mut hi = bits.clone();
            for _ in 0..(sb - 1) {
                hi = hi.div_rem(&two).0;
            }
            let mut exp_mod = Integer::one();
            for _ in 0..*eb {
                exp_mod *= two.clone();
            }
            let exp = hi.div_rem(&exp_mod).1;
            let mut sign = hi.clone();
            for _ in 0..*eb {
                sign = sign.div_rem(&two).0;
            }
            format!(
                "(fp #b{} #b{} #b{})",
                format_bin_fixed(&sign, 1),
                format_bin_fixed(&exp, *eb),
                format_bin_fixed(&sig, sb - 1),
            )
        }
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
        ModelVal::Datatype(s) => s.clone(),
    }
}
```

The `ModelVal::Float` arm is copied verbatim from `crates/shinri-solver/src/model.rs:107-136` with `shinri_num::Integer` → `Integer`; the comments there explaining the sign/exp/sig split are worth carrying across too.

- [ ] **Step 3: Move the two formatter tests across**

Append to `crates/shinri-theory/src/model.rs`:

```rust
#[cfg(test)]
mod format_tests {
    use super::*;

    #[test]
    fn format_string_modelval_escapes_quotes() {
        assert_eq!(format_modelval(&ModelVal::String("ab".into())), "\"ab\"");
        assert_eq!(
            format_modelval(&ModelVal::String("a\"b".into())),
            "\"a\"\"b\""
        );
    }

    #[test]
    fn format_float_modelval_as_fp_triple() {
        // Float32 +zero: sign 0, exp 00000000, sig 0*23
        let pz = ModelVal::Float {
            eb: 8,
            sb: 24,
            bits: Integer::from(0u64),
        };
        assert_eq!(
            format_modelval(&pz),
            "(fp #b0 #b00000000 #b00000000000000000000000)"
        );
    }

    #[test]
    fn format_rational_renders_integral_negative_and_fraction() {
        assert_eq!(format_rational(&Rational::from_int(3i128.into())), "3");
        assert_eq!(format_rational(&Rational::from_int((-3i128).into())), "(- 3)");
    }
}
```

Read `crates/shinri-solver/src/model.rs:145-201` for the exact body of the two pre-existing tests and copy their assertions rather than retyping from memory — the float test asserts a specific 32-bit pattern.

- [ ] **Step 4: Delete the originals from `shinri-solver` and repoint the callers**

In `crates/shinri-solver/src/model.rs`, delete `format_rational`, `format_hex_fixed`, `format_bin_fixed`, `format_modelval`, and the `#[cfg(test)] mod tests` block that tests them. Keep `SolveOutcome`, `Model`, and everything else. Remove the now-unused `use shinri_num::Rational;` if nothing else in the file uses it (the compiler will say).

In `crates/shinri-solver/src/lib.rs`, replace all three occurrences of `crate::model::format_modelval` with `shinri_theory::model::format_modelval` (lines `:329`, `:332`, `:349`).

- [ ] **Step 5: Verify the move changed nothing**

```bash
cargo nextest run -p shinri-theory -E 'test(format_)'
cargo nextest run -p shinri-solver -p shinri-theory
```
Expected: the three `format_` tests discovered and PASS in `shinri-theory`; the full `shinri-solver` suite green with the **same** pass count as before the move (model output text is byte-identical, so `fp_e2e` and `qfbv_witnesses` must not budge).

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add -A
git commit -m "refactor(model): slice43 T1 — relocate ModelVal formatting to shinri-theory

shinri-dt needs to format a ModelVal (T2) but the formatter lived in
shinri-solver, above shinri-dt in the dependency order. Pure code motion beside
ModelBuilder; shinri_num paths become shinri_core re-exports since
shinri-theory has no shinri-num dependency. Output text is byte-identical."
```

---

### Task 2: PREMISE GATE — DT reads the combined model

The measured gate for the whole slice. If the e2e assertion in Step 1 does not go green by Step 7, **the premise is wrong** — report that as evidence about the design, not as a test problem, and stop.

**Files:**
- Create: `crates/shinri-solver/tests/qfdt_model_e2e.rs`
- Modify: `crates/shinri-theory/src/combiner.rs:961-996`
- Modify: `crates/shinri-euf/src/solver.rs:209-215`
- Modify: `crates/shinri-dt/src/lib.rs:638-702` and `:826-837`

**Interfaces:**
- Consumes: `shinri_theory::model::{format_modelval, format_rational}` (Task 1).
- Produces: `DtSolver::render_value(&self, cx: &mut TheoryCtx, t: TermId, visited: &mut FxHashSet<ENodeId>, depth: u32, m: &ModelBuilder) -> Option<String>` — note the **new trailing `m` parameter**. No later task calls it directly.

- [ ] **Step 1: Write the failing gate**

Create `crates/shinri-solver/tests/qfdt_model_e2e.rs`:

```rust
//! Slice 43 — the model channel. Datatype field values must come from the
//! theory that owns them, not render as `?`.
//!
//! Task 2 asserts with `contains` because model output is not yet deterministic
//! (entries come from an FxHashMap). Task 5 makes it deterministic and converts
//! these to exact-string assertions.

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

const LIST: &str = "(declare-datatype List ((nil) (cons (head Int) (tail List))))";

/// Probe C3 of the spec: arith pins the selector's value, so the field must
/// render 42 — not `?`. THE PREMISE GATE: the value is already in `arith_m`
/// (Arith::build_model assigns every var it knows); this asserts it is now
/// reachable from DtSolver's renderer.
#[test]
fn int_field_renders_arith_assigned_value() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert ((_ is cons) l))(assert (= (head l) 42))\
         (check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    let model = &out[1];
    assert!(
        model.contains("(cons 42 nil)"),
        "Int field must render its arith value, got: {model}"
    );
    assert!(
        !model.contains('?'),
        "no `?` placeholder may survive for an Int field, got: {model}"
    );
}

/// Probe C2: a LITERAL field. Independent of any theory — readable straight off
/// the term via Context::numeral_value, so this passes even with an empty
/// builder. Pins spec §3.C branch 2.
#[test]
fn literal_int_field_renders_from_the_term() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert (= l (cons 1 nil)))(check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert!(
        out[1].contains("(cons 1 nil)"),
        "literal field must render as 1, got: {}",
        out[1]
    );
}

/// Probe C1: the field is entirely UNCONSTRAINED and its selector application
/// was minted in-search, so it is not in the Solver's own ctx. Arith still holds
/// it at its current beta, and inside the Combiner the TermId is valid — which is
/// the whole reason rendering moved there.
#[test]
fn unconstrained_minted_int_field_still_renders_a_value() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert ((_ is cons) l))(check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert!(
        !out[1].contains('?'),
        "an unconstrained Int field must still get a value, got: {}",
        out[1]
    );
}

/// Probe C4: two levels of tester-driven instantiation.
#[test]
fn nested_int_fields_both_render() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert ((_ is cons) l))(assert ((_ is cons) (tail l)))\
         (assert (= (head l) 7))(check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert!(
        out[1].contains("(cons 7 (cons "),
        "outer field must render 7 with a nested cons, got: {}",
        out[1]
    );
}
```

- [ ] **Step 2: Run the gate to verify it fails, and record HOW**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfdt_model_e2e)'`
Expected: **4 tests discovered**, all FAIL. `int_field_renders_arith_assigned_value` must fail on `(cons ? nil)` — i.e. the `contains("(cons 42 nil)")` assertion, reporting `?` in the message. If it fails for any *other* reason (a parse error, a non-`sat` verdict, a panic), stop and investigate: the gate must be failing for the reason the slice exists.

- [ ] **Step 3: Move `DtSolver::model` last, into `combined`**

In `crates/shinri-theory/src/combiner.rs`, delete the `dt_m` block (`:970-978`) and the `combined.absorb(dt_m);` line (`:982`). Then, immediately after the existing `self.string.model(&mut cx, &mut combined);` block, add:

```rust
        // Build the datatype model LAST, directly into `combined`, so
        // `render_value` can read the field values the owning theories assigned:
        // arith's Num for Int/Real fields (Arith::build_model assigns EVERY var
        // it knows, free ones included), EUF's Elem for uninterpreted-sorted
        // ones, and the string model's values. A separate empty builder hides
        // all of them and every field renders `?` (slice 43 §3.A).
        //
        // Going last is safe because nothing reads DT's values: DtSolver::model
        // assigns only datatype-sorted terms, and no string/arith/EUF term is
        // datatype-sorted.
        {
            let mut cx = TheoryCtx {
                terms: &mut self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            self.dt.model(&mut cx, &mut combined);
        }
```

**Verify the "nothing reads DT's values" claim rather than trusting this comment** (spec §3.A makes this an explicit obligation): read `StrSolver::model` and confirm it never looks up a datatype-sorted term's value. If it does, keep DT before string and give DT a second `combined`-reading pass instead, and say so in the commit message.

- [ ] **Step 3b: Unit-test the ordering in `shinri-theory`**

The ordering *is* the mechanism, so it needs a test that fails if someone moves the block back. Add to the test module in `crates/shinri-theory/src/combiner.rs`, using the existing stub-theory harness — read `build_model_collects_theory_assignments` (`:1391-1402`) and reuse its `Combiner<OneShotProp, ValTheory, NullTheory, NullTheory, NullTheory>` construction idiom:

```rust
    #[test]
    fn build_model_runs_dt_last_so_it_can_read_other_theories() {
        // Slice 43 §3.A: DtSolver::model must receive a builder that ALREADY
        // holds the other theories' assignments. With a fresh empty builder every
        // datatype field renders `?`, which is the defect this ordering fixes.
        // Assert on the COMBINED builder: (a) a value an earlier theory assigned
        // is visible to the dt slot's `model` call, and (b) the dt slot's own
        // assignment survives into the returned builder.
        // ... construct the Combiner with a stub dt theory that records whether
        // the builder it was handed already contained the arith value ...
    }
```

The stub `dt` theory needs to capture what it saw — e.g. an `AtomicBool`/`Cell` it sets when `m.get(known_term).is_some()` on entry. Assert both that flag and the surviving assignment; a test that only checks (b) would still pass if DT ran first.

- [ ] **Step 4: Make EUF stop claiming datatype-sorted terms**

In `crates/shinri-euf/src/solver.rs`, extend the skip at `:209-215`:

```rust
            let sort = cx.terms.sort_of(term);
            // Skip Real/Int-sorted terms: the Arith theory assigns their numeric
            // values. EUF assigning Elem(...) for them would conflict with Arith's
            // Num(...) assignments and trigger the model seam debug_assert.
            //
            // Skip datatype-sorted terms for the same ownership reason: DtSolver
            // renders them as ground constructor terms. This is REQUIRED, not
            // cosmetic — since slice 43 DtSolver::model writes into the shared
            // `combined` builder, so an Elem here would be visible to its
            // `m.get(t).is_some()` guard and it would skip every datatype term.
            // It also removes a latent fragility: before this skip, correct
            // output depended on `absorb` being last-write-wins with dt_m
            // absorbed after euf_m, which nothing documented or tested.
            if sort == real_s || sort == int_s || cx.terms.is_datatype_sort(sort) {
                continue;
            }
```

- [ ] **Step 5: Write the EUF unit fence**

Append to the test module in `crates/shinri-euf/src/solver.rs`. Follow the surrounding tests' construction idiom for `Context`/`TheoryCtx` — read two neighbouring tests first and match them; the sketch below is the assertion, not the scaffolding:

```rust
    #[test]
    fn model_does_not_assign_datatype_sorted_terms() {
        // DT owns datatype-sorted values (slice 43 §3.B). If EUF assigns an Elem
        // here, DtSolver::model's already-assigned guard skips every datatype
        // term against the shared builder and the model regresses.
        // Build a datatype sort, register a term of it plus a term of an
        // uninterpreted sort, run `model`, and assert asymmetry.
        // ... construct ctx/euf per the neighbouring tests ...
        assert!(
            m.get(dt_term).is_none(),
            "EUF must leave datatype-sorted terms to DtSolver"
        );
        assert!(
            m.get(u_term).is_some(),
            "EUF must still assign uninterpreted-sorted terms"
        );
    }
```

- [ ] **Step 6: Thread the builder into the DT renderer**

In `crates/shinri-dt/src/lib.rs`, add `m: &ModelBuilder` as the trailing parameter of `render_value` (`:638`) and `render_value_inner` (`:658`), forwarding it at the recursive call. Import `shinri_theory::model::ModelBuilder` if it is not already in scope.

Replace the non-datatype arm of the field loop (`:685-698`) so the whole `map` closure reads:

```rust
        let parts: Option<Vec<String>> = cargs
            .iter()
            .map(|&a| {
                if cx.terms.is_datatype_sort(cx.terms.sort_of(a)) {
                    self.render_value(cx, a, visited, depth + 1, m)
                } else {
                    Some(Self::render_field(cx.terms, m, a))
                }
            })
            .collect();
```

And add the helper next to `render_value_inner`:

```rust
    /// A non-datatype constructor field as SMT-LIB text (slice 43 §3.C).
    ///
    /// The branch order is load-bearing. A numeral is readable straight off the
    /// term, needing no theory. Otherwise the value the OWNING theory assigned
    /// wins. Only when nothing assigned one do we fall back to a nullary
    /// application's own symbol name — that is a *term*, not a value, so it must
    /// never outrank the builder: a declared Int constant `x` with arith value 7
    /// would otherwise render as `x`, and two distinct constants merged into one
    /// class would render as two different "values", which is a wrong model
    /// rather than an ugly one. `?` remains only for a field no theory assigned
    /// and that is not a nullary application (Bool/BV fields today, §5).
    fn render_field(terms: &Context, m: &ModelBuilder, a: TermId) -> String {
        if let Some(r) = terms.numeral_value(a) {
            return shinri_theory::model::format_rational(r);
        }
        if let Some(v) = m.get(a) {
            return shinri_theory::model::format_modelval(v);
        }
        match Self::uapp(terms, a) {
            Some((s, kids)) if kids.is_empty() => terms.symbol_name(s).to_string(),
            _ => "?".to_string(),
        }
    }
```

Then update `DtSolver::model` (`:826-837`) to pass the builder through. The immutable reborrow of `m` ends before `m.assign`, so this borrow-checks:

```rust
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        for t in self.watched_dt_terms() {
            if m.get(t).is_some() {
                continue;
            }
            let mut visited = FxHashSet::default();
            let Some(v) = self.render_value(cx, t, &mut visited, 0, m) else {
                continue;
            };
            m.assign(t, shinri_theory::types::ModelVal::Datatype(v));
        }
    }
```

- [ ] **Step 7: Run the gate — this is the premise check**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfdt_model_e2e)'`
Expected: **4 tests discovered, all PASS.**

If `int_field_renders_arith_assigned_value` still shows `?`, **stop**. Do not adjust the test. Report which of these is false: (a) `Arith::build_model` does assign the selector term, (b) `DtSolver::model` now receives a builder containing it, (c) `render_field` looks up the same TermId arith keyed. Print the builder contents at the DT call site to find out which.

- [ ] **Step 8: Write the branch-order fence (spec §3.C, the wrong-model guard)**

Add a `shinri-dt` unit test asserting that a field which is a declared constant **with** an assigned value renders the *value*, not the constant's name — and that two distinct constants in one class render the same value. Construct a `ModelBuilder`, `assign` the field term a `ModelVal::Num`, and call `render_value` directly. This is the fence that keeps a future refactor from reordering branches 3 and 4.

- [ ] **Step 9: Measure the Bool-field question (spec §5) and pin whatever it is**

Run the M5 probe and observe:

```bash
cargo build --release --bin shinri
printf '%s\n' '(set-logic QF_UFDT)(declare-datatype B ((mk (b Bool))))(declare-fun z () B)(assert (b z))(check-sat)(get-model)' > /tmp/m5.smt2
./target/release/shinri /tmp/m5.smt2
```

`Euf::model`'s Bool branch (`crates/shinri-euf/src/solver.rs:199-208`) assigns `ModelVal::Bool` for terms merged with its truth node, so the Bool field **may** now resolve. Add a test to `qfdt_model_e2e.rs` pinning the observed behaviour either way — `(mk true)` if it resolves, `(mk ?)` if it does not — with a comment naming which. **Do not assume; record what the binary does.**

- [ ] **Step 10: Verify no verdict moved**

```bash
cargo nextest run -p shinri-solver -p shinri-dt -p shinri-euf -p shinri-theory
```
Expected: all green, with `qfdt_e2e`'s DT⋈arith set (`qfdt_e2e.rs:146-231`) unchanged. Any verdict flip violates the Global Constraint — stop.

- [ ] **Step 11: Commit**

```bash
cargo fmt --all
git add -A
git commit -m "feat(model): slice43 T2 — DT renders field values from the combined model

DtSolver::model built into a fresh empty ModelBuilder, so it could never see
the values other theories assigned and every non-datatype field rendered `?`.
Build it last directly into `combined` — the pattern StrSolver already uses to
read arith's str.len values — so Int/Real fields resolve from arith, which
assigns every var it knows including free ones. Inside the Combiner every
TermId is valid, so in-search-minted selector applications resolve too.

EUF stops assigning Elem to datatype-sorted terms: required, since its Elem
would otherwise reach DtSolver::model's already-assigned guard through the now
shared builder and skip every datatype term.

render_field's branch order (numeral, then builder, then symbol name) is a
wrong-model fence, not a style choice — see its doc comment."
```

---

### Task 3: An exhaustive sort printer in `shinri-core`

`define-fun` needs a sort in its signature and **nothing in the workspace prints a `SortId`** — no `display_sort`, no `sort_name`. New component, so its own unit test is the only thing standing behind it.

`SortNode` (`crates/shinri-core/src/sort.rs:6-28`) is a closed 11-variant algebra, so an exhaustive match with no catch-all arm is achievable — and required: an unprintable sort would emit malformed SMT-LIB, which is a bug, not a fallback case.

**On recursion:** the `Array` arm recurses. That is safe here because `Parser::parse_sort` (`crates/shinri-parser/src/parser.rs:228-236`) is *itself* unbounded-recursive over nested `Array` sorts, so a sort deep enough to overflow this printer cannot be parsed in the first place — the parser is the tighter bound. (That parser recursion is a pre-existing concern and explicitly **not** in scope for this slice.)

**Files:**
- Modify: `crates/shinri-core/src/context.rs` (add `sort_name` near `sort_node` at `:186`)

**Interfaces:**
- Consumes: `Context::sort_node(&self, id: SortId) -> &SortNode` (`:186`), `Context::symbol_name`.
- Produces: `Context::sort_name(&self, s: SortId) -> String`. Task 5 calls it for the `define-fun` signature.

- [ ] **Step 1: Write the failing test**

Add to the test module in `crates/shinri-core/src/context.rs`:

Every sort **must be bound to a local first**: `array_sort`, `bv_sort`, `fp_sort`, `declare_sort`, and `rm_sort` take `&mut self` (`context.rs:144-174`), while `sort_name` takes `&self`, so an inline `ctx.sort_name(ctx.bv_sort(8))` fails to borrow-check — the receiver's shared borrow is taken before the argument is evaluated.

```rust
    #[test]
    fn sort_name_prints_every_sort_shape() {
        let mut ctx = Context::new();
        // Bind first: the *_sort constructors below need &mut self.
        let b = ctx.bool_sort();
        let i = ctx.int_sort();
        let r = ctx.real_sort();
        let st = ctx.string_sort();
        let rl = ctx.reglan_sort();
        let rm = ctx.rm_sort();
        let bv8 = ctx.bv_sort(8);
        let bv3 = ctx.bv_sort(3);
        let f32s = ctx.fp_sort(8, 24);
        let u = ctx.declare_sort("U");
        let arr = ctx.array_sort(i, b);
        let nested = ctx.array_sort(bv8, arr);

        assert_eq!(ctx.sort_name(b), "Bool");
        assert_eq!(ctx.sort_name(i), "Int");
        assert_eq!(ctx.sort_name(r), "Real");
        assert_eq!(ctx.sort_name(st), "String");
        assert_eq!(ctx.sort_name(rl), "RegLan");
        assert_eq!(ctx.sort_name(rm), "RoundingMode");
        assert_eq!(ctx.sort_name(bv8), "(_ BitVec 8)");
        assert_eq!(ctx.sort_name(bv3), "(_ BitVec 3)");
        assert_eq!(ctx.sort_name(f32s), "(_ FloatingPoint 8 24)");
        assert_eq!(ctx.sort_name(u), "U");
        assert_eq!(ctx.sort_name(arr), "(Array Int Bool)");
        // Nested, to pin the recursion.
        assert_eq!(
            ctx.sort_name(nested),
            "(Array (_ BitVec 8) (Array Int Bool))"
        );
    }
```

That covers 10 of the 11 `SortNode` variants. **Add the `Datatype` variant too** so the match is fully exercised: find how a datatype sort is created via `grep -n "SortNode::Datatype" crates/shinri-core/src/context.rs`, declare a one-constructor datatype in the test, and assert its `sort_name` is the datatype's own name.

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo nextest run -p shinri-core -E 'test(sort_name_prints_every_sort_shape)'`
Expected: **1 test discovered**, FAIL to compile with "no method named `sort_name`".

- [ ] **Step 3: Implement `sort_name`**

Add immediately after `sort_node` in `crates/shinri-core/src/context.rs`:

```rust
    /// An interned sort as SMT-LIB text: `Int`, `(_ BitVec 8)`,
    /// `(Array Int Bool)`. Used for the signature position of `define-fun` in
    /// `get-model` output (slice 43 §4.B).
    ///
    /// Deliberately EXHAUSTIVE over `SortNode` with no catch-all arm: an
    /// unprintable sort would emit malformed SMT-LIB, so a new sort variant must
    /// break this match rather than silently render as a placeholder.
    ///
    /// The `Array` arm recurses. `Parser::parse_sort` is itself recursive over
    /// nested `Array` sorts, so a sort deep enough to overflow here cannot be
    /// parsed in the first place — the parser bounds this, not a depth cap.
    pub fn sort_name(&self, s: SortId) -> String {
        match self.sort_node(s) {
            SortNode::Bool => "Bool".to_string(),
            SortNode::Int => "Int".to_string(),
            SortNode::Real => "Real".to_string(),
            SortNode::String => "String".to_string(),
            SortNode::RoundingMode => "RoundingMode".to_string(),
            SortNode::RegLan => "RegLan".to_string(),
            SortNode::Uninterpreted(sym) | SortNode::Datatype(sym) => {
                self.symbol_name(*sym).to_string()
            }
            SortNode::BitVec(n) => format!("(_ BitVec {n})"),
            SortNode::Float(eb, sb) => format!("(_ FloatingPoint {eb} {sb})"),
            SortNode::Array(i, e) => {
                format!("(Array {} {})", self.sort_name(*i), self.sort_name(*e))
            }
        }
    }
```

Add `use crate::sort::SortNode;` to the file's imports if it is not already there.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo nextest run -p shinri-core -E 'test(sort_name)'`
Expected: **1 test discovered**, PASS.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add -A
git commit -m "feat(core): slice43 T3 — exhaustive SortId -> SMT-LIB sort printer

get-model's define-fun output needs a sort in the signature position and
nothing in the workspace printed a SortId. Exhaustive over SortNode with no
catch-all: a new sort variant must break the match rather than silently render
as a placeholder, since malformed output is worse than a compile error."
```

---

### Task 4: A registry of user-declared symbols

`format_model` currently iterates the theory value map, which is why internal `tN` names and constructor constants like `nil` appear, and why a symbol no theory touched vanishes. Enumerate declarations instead. This task adds the registry and proves it is populated; Task 5 consumes it.

`Command::DeclareFun` (`crates/shinri-frontend/src/lib.rs:25-30`) carries `{ name: String, sym: SymbolId, params: Vec<SortId>, result: SortId }` and is currently discarded in the no-op match arm at `crates/shinri-solver/src/lib.rs:316`. Constructor/selector/tester symbols arrive via `Command::DeclareDatatypes`, a **different** arm — so excluding them needs no name filtering, which is why `nil` disappears for free.

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (struct fields near `:55-100`; the `DeclareFun` arm at `:316`; `Reset` at `:305`)

**Interfaces:**
- Consumes: `Command::DeclareFun { name, sym, params, result }`.
- Produces: a private field `declared: Vec<DeclaredFun>` on `Solver` with
  ```rust
  struct DeclaredFun { name: String, sym: SymbolId, arity: usize, result: SortId }
  ```
  in declaration order, and a test-visible accessor `#[cfg(test)] pub(crate) fn declared_names(&self) -> Vec<&str>`. Task 5 iterates `declared` and filters on `arity == 0`.

- [ ] **Step 1: Write the failing test**

Add to the test module in `crates/shinri-solver/src/lib.rs`:

```rust
    #[test]
    fn declare_fun_populates_the_declared_registry_in_order() {
        // The registry is what get-model enumerates (slice 43 §4.A). It must
        // hold user declarations in declaration order, and must NOT pick up
        // constructor/selector/tester symbols, which arrive via
        // Command::DeclareDatatypes rather than Command::DeclareFun.
        let src = "(set-logic QF_UFDTLIA)\
                   (declare-datatype List ((nil) (cons (head Int) (tail List))))\
                   (declare-fun l () List)\
                   (declare-fun x () Int)\
                   (declare-fun f (Int) Int)";
        let mut s = Solver::new();
        let mut p = shinri_parser::Parser::new(src);
        while let Some(Ok(cmd)) = p.next_command(s.ctx_mut()) {
            s.execute(cmd);
        }
        assert_eq!(s.declared_names(), vec!["l", "x", "f"]);
    }
```

`shinri-parser` depends on `shinri-solver`, not the reverse, so it may not be available as a `shinri-solver` dev-dependency. Check `crates/shinri-solver/Cargo.toml`: if `shinri-parser` is absent, drive the registry through `Solver::execute` with hand-built `Command::DeclareFun` values instead of parsing — the assertion is unchanged.

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo nextest run -p shinri-solver -E 'test(declare_fun_populates_the_declared_registry_in_order)'`
Expected: **1 test discovered**, FAIL to compile with "no method named `declared_names`".

- [ ] **Step 3: Add the field and the struct**

Add near the other `Solver` fields (after `abv_array_models` at `crates/shinri-solver/src/lib.rs:75` is a natural home):

```rust
    /// User-declared functions in declaration order — what `get-model`
    /// enumerates (slice 43 §4.A). Datatype constructor/selector/tester symbols
    /// are absent by construction: they arrive via `Command::DeclareDatatypes`,
    /// not `Command::DeclareFun`, which is why `nil` cannot appear as a model
    /// entry. Internal mints (`ite!`, `!`-prefixed bridge symbols) never pass
    /// through a command at all.
    declared: Vec<DeclaredFun>,
```

And beside the `BridgeRow` enum:

```rust
/// One user-declared function. `arity == 0` entries are the ones `get-model`
/// emits; higher arities are recorded but not printed (slice 43 §5 — function
/// graphs need EUF congruence-class enumeration and are a later slice).
struct DeclaredFun {
    name: String,
    #[allow(dead_code)] // consumed by the arity>0 successor slice
    sym: shinri_core::SymbolId,
    arity: usize,
    result: shinri_core::SortId,
}
```

If `Solver` derives `Default`, `Vec` is already `Default`; if it has a manual `new`, initialize `declared: Vec::new()`.

- [ ] **Step 4: Populate it, and clear it on reset**

Split `Command::DeclareFun` out of the no-op arm at `:313-319` into its own arm:

```rust
            Command::DeclareFun {
                name,
                sym,
                params,
                result,
            } => {
                self.declared.push(DeclaredFun {
                    name,
                    sym,
                    arity: params.len(),
                    result,
                });
                CommandResponse::None
            }
```

Add `self.declared.clear();` to the `Command::Reset` arm (`:305-312`) alongside the other cleared state.

Add the accessor next to the other `#[cfg(test)]` helpers:

```rust
    #[cfg(test)]
    pub(crate) fn declared_names(&self) -> Vec<&str> {
        self.declared.iter().map(|d| d.name.as_str()).collect()
    }
```

- [ ] **Step 5: Run to verify it passes**

Run: `cargo nextest run -p shinri-solver -E 'test(declare_fun_populates)'`
Expected: **1 test discovered**, PASS. Model output is untouched so far, so the whole `shinri-solver` suite must also still be green: `cargo nextest run -p shinri-solver`.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add -A
git commit -m "feat(model): slice43 T4 — registry of user-declared functions

get-model enumerated the theory value map, which is why internal tN names and
constructor constants appeared and why a symbol no theory touched vanished.
Record declarations in order instead. Constructor/selector/tester symbols are
excluded by construction — they arrive via DeclareDatatypes, a different
command arm — so no name filtering is needed."
```

---

### Task 5: `format_model` emits `define-fun`, deterministically

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs:338-360` (`format_model`), plus a new `sort_default` helper
- Modify: `crates/shinri-solver/tests/qfdt_model_e2e.rs` (convert Task 2's `contains` assertions to exact strings)

**Interfaces:**
- Consumes: `self.declared: Vec<DeclaredFun>` (Task 4), `Context::sort_name` (Task 3), `shinri_theory::model::format_modelval` (Task 1).
- Produces: `get-model` output of the form `((define-fun l () List (cons 42 nil))(define-fun x () Int 0))` — one line, declaration order.

- [ ] **Step 1: Write the failing tests**

Add to `crates/shinri-solver/tests/qfdt_model_e2e.rs`:

```rust
/// Spec §4.B: conformant define-fun, single line, declaration order.
#[test]
fn model_emits_define_fun_in_declaration_order() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)(declare-fun x () Int)\
         (assert ((_ is cons) l))(assert (= (head l) 42))(assert (= x 5))\
         (check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(
        out[1],
        "((define-fun l () List (cons 42 nil))(define-fun x () Int 5))"
    );
}

/// Determinism: the same query must produce byte-identical model output every
/// run. Before slice 43 entries came out in FxHashMap order.
#[test]
fn model_output_is_deterministic() {
    let q = format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)(declare-fun x () Int)\
         (assert ((_ is cons) l))(assert (= x 5))(check-sat)(get-model)"
    );
    let first = run_script(&q);
    for _ in 0..8 {
        assert_eq!(run_script(&q), first, "model output must be deterministic");
    }
}

/// Spec §1 probes M4/M4c: a declared symbol occurring in NO assertion. It is in
/// no registered atom, so no theory assigns it and there is nothing in the value
/// map to iterate — it used to vanish entirely, returning `()`. M4c is the
/// non-datatype control: a fix that only handles the datatype path fails it.
#[test]
fn unasserted_int_symbol_gets_a_default() {
    let out = run_script("(set-logic QF_LIA)(declare-fun x () Int)(check-sat)(get-model)");
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun x () Int 0))");
}

#[test]
fn unasserted_datatype_symbol_gets_a_structural_default() {
    // `List` has a nullary constructor, so the default is `nil`.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)(check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun l () List nil))");
}

#[test]
fn unasserted_datatype_without_nullary_ctor_recurses_into_field_defaults() {
    // `Box` has NO nullary constructor, so the default must be built by
    // recursing into the field's own default (spec §4.B).
    let out = run_script(
        "(set-logic QF_UFDTLIA)(declare-datatype Box ((mk (unbox Int))))\
         (declare-fun b () Box)(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun b () Box (mk 0)))");
}

/// Spec §1 defect 2: no internal name and no undeclared symbol may appear.
#[test]
fn model_names_only_declared_symbols() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert (= l (cons 1 nil)))(check-sat)(get-model)"
    ));
    let model = &out[1];
    assert!(
        !model.contains("(define-fun nil"),
        "a constructor constant is not a declared symbol: {model}"
    );
    for tn in ["t3", "t4", "t5", "t6", "t7"] {
        assert!(
            !model.contains(&format!("(define-fun {tn} ")),
            "internal term id {tn} leaked into the model: {model}"
        );
    }
}
```

Then **convert Task 2's four assertions to exact strings** now that output is deterministic — e.g. `int_field_renders_arith_assigned_value` becomes `assert_eq!(out[1], "((define-fun l () List (cons 42 nil)))")`. Keep the explanatory comments; they are what makes a future failure diagnosable.

For `nested_int_fields_both_render` and `unconstrained_minted_int_field_still_renders_a_value` the exact tail value depends on arith's chosen β and DT's constructor choice — **run the binary and record what it actually produces**, then pin that. Do not guess a value into an `assert_eq!`.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfdt_model_e2e)'`
Expected: the new tests FAIL showing the old `(name value)` shape. Confirm the discovered count matches the number of tests in the file.

- [ ] **Step 3: Implement the sort default**

Add to `crates/shinri-solver/src/lib.rs`:

```rust
    /// A canonical value for a sort, used for a declared symbol that occurs in no
    /// assertion — it is in no registered atom, so no theory assigns it a value
    /// (slice 43 §4.B). Without this the symbol vanishes from `get-model`.
    ///
    /// `on_path` carries the datatype sorts on the current recursion path: a
    /// constructor whose field re-enters a sort already on the path cannot be
    /// used as a base case, so we try the next constructor. `Context`'s
    /// inhabitance fixpoint (`dt_first_ill_founded`) guarantees a usable
    /// constructor exists for a well-founded datatype, which SMT-LIB requires.
    fn sort_default(&self, s: shinri_core::SortId, on_path: &mut Vec<shinri_core::SortId>) -> String {
        use shinri_core::SortNode;
        match self.ctx.sort_node(s) {
            SortNode::Bool => "false".to_string(),
            SortNode::Int | SortNode::Real => "0".to_string(),
            SortNode::String => "\"\"".to_string(),
            SortNode::RoundingMode => "RNE".to_string(),
            SortNode::BitVec(n) => format!("#b{}", "0".repeat(*n as usize)),
            SortNode::Float(eb, sb) => format!(
                "(fp #b0 #b{} #b{})",
                "0".repeat(*eb as usize),
                "0".repeat((*sb - 1) as usize)
            ),
            // No value vocabulary for these; `@elem0` matches what
            // `format_modelval` already emits for an assigned `Elem`, so the
            // defaulted and assigned cases read alike.
            SortNode::Uninterpreted(_) | SortNode::RegLan => "@elem0".to_string(),
            SortNode::Datatype(_) => self.datatype_default(s, on_path),
        }
    }

    /// The structural default for a datatype sort: the first constructor whose
    /// fields can all be defaulted without re-entering a sort already on the
    /// recursion path. A nullary constructor trivially qualifies and is found
    /// first when one exists.
    fn datatype_default(
        &self,
        s: shinri_core::SortId,
        on_path: &mut Vec<shinri_core::SortId>,
    ) -> String {
        if on_path.contains(&s) {
            // Re-entering a sort already on the path: this constructor choice is
            // not a base case. Signalled to the caller, which tries the next one.
            return String::new();
        }
        on_path.push(s);
        let ctors: Vec<shinri_core::SymbolId> = self
            .ctx
            .dt_constructors(s)
            .map(|c| c.to_vec())
            .unwrap_or_default();
        let mut rendered = None;
        for c in ctors {
            let params: Vec<shinri_core::SortId> =
                self.ctx.fun_params(c).map(|p| p.to_vec()).unwrap_or_default();
            let name = self.ctx.symbol_name(c).to_string();
            if params.is_empty() {
                rendered = Some(name);
                break;
            }
            let mut parts: Vec<String> = Vec::with_capacity(params.len());
            let mut usable = true;
            for p in params {
                let d = self.sort_default(p, on_path);
                if d.is_empty() {
                    usable = false;
                    break;
                }
                parts.push(d);
            }
            if usable {
                rendered = Some(format!("({} {})", name, parts.join(" ")));
                break;
            }
        }
        on_path.pop();
        // An empty return propagates "not a base case" to the caller; a
        // well-founded datatype always yields Some here.
        rendered.unwrap_or_default()
    }
```

Prefer sorting the constructor list so a nullary one is tried first if the declaration order puts a recursive constructor first — `cons` before `nil` would otherwise cost a wasted recursion, though the result is the same. Keep it simple unless a test shows otherwise.

- [ ] **Step 4: Rewrite `format_model`**

Replace `crates/shinri-solver/src/lib.rs:338-360` entirely:

```rust
    /// `get-model` output: one `define-fun` per user-declared 0-arity symbol, in
    /// declaration order, on a SINGLE line (slice 43 §4.B — `qfbv_witnesses`
    /// reads the model as `out[1]`, so a multi-line model breaks the
    /// line-oriented response contract).
    ///
    /// Enumerating declarations rather than the theory value map is what keeps
    /// internal `tN` names and constructor constants out, makes the output
    /// deterministic, and stops a symbol occurring in no assertion from
    /// vanishing. Functions of arity > 0 are omitted: a graph needs EUF
    /// congruence-class enumeration (§5), so this is NOT yet a complete model
    /// for UF queries.
    fn format_model(&self) -> String {
        let mut out = String::from("(");
        for d in self.declared.iter().filter(|d| d.arity == 0) {
            let val = self
                .value_of_declared(d)
                .unwrap_or_else(|| self.sort_default(d.result, &mut Vec::new()));
            out.push_str(&format!(
                "(define-fun {} () {} {})",
                d.name,
                self.ctx.sort_name(d.result),
                val
            ));
        }
        out.push(')');
        out
    }

    /// The assigned value of a declared 0-arity symbol, if some theory produced
    /// one. Mirrors `format_value`'s channel order (theory model, then the
    /// eliminated-ite remap, then the ABV array model) but keyed by the symbol's
    /// own term rather than an arbitrary term.
    fn value_of_declared(&self, d: &DeclaredFun) -> Option<String> {
        let t = self.ctx.app_of_symbol(d.sym)?;
        self.format_value(t)
    }
```

`app_of_symbol` is a placeholder for however the `Solver` maps a declared 0-arity `SymbolId` back to its `TermId`. **Find the real mechanism before writing this** — `Context` hash-conses `Op::Uninterpreted(sym)` with no args, so the term may be obtainable by interning it (`ctx.mk_app(Op::Uninterpreted(sym), &[])`) which returns the existing hash-consed id rather than a new one. Check whether `mk_app` takes `&mut self`; if it does, either record the `TermId` in `DeclaredFun` at declare time (simplest — `Command::DeclareFun` fires before any solve, so it is a pre-clone mint and safe per the ctx-clone rules) or add a read-only lookup. **Recording the `TermId` in `DeclaredFun` at declare time is the recommended route**; adjust Task 4's struct accordingly and note it in the commit.

- [ ] **Step 5: Run the tests**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfdt_model_e2e)'`
Expected: all discovered tests PASS.

Then the pins that assert on model text: `cargo nextest run -p shinri-solver -E 'binary(fp_e2e) or binary(qfbv_witnesses) or binary(ite_e2e)'`. These assert `contains` on value text (`(fp #b`, `#x2a`) which survives being wrapped in a `define-fun`, and `ite_e2e.rs:213` asserts `!model.contains("ite!")` which the registry makes structurally true. **If any fails, read it before editing it** — `qfbv_witnesses.rs:279`'s `out.len() >= 2` is the single-line constraint and must not be "fixed" by relaxing it.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add -A
git commit -m "feat(model): slice43 T5 — get-model emits conformant define-fun

Enumerate declared symbols instead of the theory value map: internal tN names
and constructor constants can no longer appear, output becomes deterministic
(declaration order, not FxHashMap order), and a symbol occurring in no
assertion gets a sort default instead of vanishing. Datatype defaults recurse
structurally with a path-visited set, so a datatype with no nullary
constructor still gets a value.

Single-line output is a hard constraint: qfbv_witnesses reads the model as
out[1]. Arity>0 functions remain omitted (spec §5) — get-model is not yet a
complete model for UF queries."
```

---

### Task 6: `get-value` labels responses with the requested term

**Files:**
- Modify: `crates/shinri-solver/src/tseitin.rs:408-417` (`display_term`)
- Modify: `crates/shinri-solver/tests/qfdt_model_e2e.rs`

**Interfaces:**
- Consumes: `Context::term_node`, `Context::children`, `Context::symbol_name`.
- Produces: `display_term` printing full applications. `format_model` no longer calls it (Task 5), so `GetValue` (`crates/shinri-solver/src/lib.rs:291-303`) is its only remaining caller of consequence.

- [ ] **Step 1: Write the failing test**

Add to `crates/shinri-solver/tests/qfdt_model_e2e.rs`:

```rust
/// Spec §4.C: get-value must label each response with the term the user asked
/// for, not an internal id.
#[test]
fn get_value_labels_responses_with_the_requested_term() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert ((_ is cons) l))(assert (= (head l) 7))\
         (check-sat)(get-value ((head l) l))"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "(((head l) 7) (l (cons 7 nil)))");
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo nextest run -p shinri-solver -E 'test(get_value_labels_responses_with_the_requested_term)'`
Expected: **1 test discovered**, FAIL showing `((t4 7) (l ...))`.

- [ ] **Step 3: Make `display_term` print applications**

Replace `crates/shinri-solver/src/tseitin.rs:408-417`:

```rust
/// An SMT-LIB rendering of a term, for `get-value` response labels: `x`,
/// `(head l)`, `(+ x 1)`. The `t{index}` fallback remains for a term with no
/// printable form; it should be unreachable for anything the user could have
/// written (slice 43 §4.C).
pub(crate) fn display_term(ctx: &shinri_core::Context, t: shinri_core::TermId) -> String {
    match ctx.term_node(t) {
        TermNode::App {
            op: Op::Uninterpreted(sym),
            args,
            ..
        } => {
            let sym = *sym;
            let kids = ctx.children(*args).to_vec();
            if kids.is_empty() {
                return ctx.symbol_name(sym).to_string();
            }
            let parts: Vec<String> = kids.iter().map(|&k| display_term(ctx, k)).collect();
            format!("({} {})", ctx.symbol_name(sym), parts.join(" "))
        }
        _ => format!("t{}", t.index()),
    }
}
```

Only the `Op::Uninterpreted` case is needed for the spec's success criteria: `get-value` on a selector application. Extending it to arithmetic and other `Op`s is out of scope — the `tN` fallback covers them, and the test above must not be widened to demand more.

**Note the recursion:** term depth is attacker-controlled per the threat model. `render_value` (`crates/shinri-dt/src/lib.rs:645`) uses an explicit `depth > 10_000` backstop for exactly this reason. Add the same backstop here — pass a depth and return `t{index}` beyond the cap — rather than relying on the input being shallow.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfdt_model_e2e)'`
Expected: all discovered tests PASS.

- [ ] **Step 5: Check nothing else depended on the old labels**

Run: `cargo nextest run -p shinri-solver`
Expected: green. `ite_e2e.rs:184` does a `get-value` on an eliminated ite — read what it asserts and confirm the new rendering satisfies it. If it asserted a `tN` label, that assertion was pinning the defect and updating it is correct; say so in the commit message.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add -A
git commit -m "feat(model): slice43 T6 — get-value labels responses with the term

display_term rendered every compound term as t{index}, so get-value answered
`(t4 7)` for `(head l)`. Print uninterpreted applications structurally, with
the same explicit depth backstop render_value uses — term depth is
attacker-controlled per the threat model."
```

---

### Task 7: Pin the fenced gaps

Spec §5 leaves three gaps deliberately. Pin each with a test so the current behaviour is *recorded* rather than merely believed, and so the successor slices can find them. A gap with no test is indistinguishable from a bug.

**Files:**
- Modify: `crates/shinri-solver/tests/qfdt_model_e2e.rs`

**Interfaces:** consumes everything from Tasks 2–6; produces nothing.

- [ ] **Step 1: Run each gap probe against the real binary and record the output**

```bash
cargo build --release --bin shinri
# BV-sorted datatype field
printf '%s\n' '(set-logic QF_UFDTBV)(declare-datatype W ((mk (w (_ BitVec 8)))))(declare-fun v () W)(assert (= (w v) #x2a))(check-sat)(get-model)' > /tmp/g1.smt2
./target/release/shinri /tmp/g1.smt2
# arity>0 function
printf '%s\n' '(set-logic QF_UFLIA)(declare-fun x () Int)(declare-fun f (Int) Int)(assert (> (f x) 3))(check-sat)(get-model)' > /tmp/g2.smt2
./target/release/shinri /tmp/g2.smt2
# uninterpreted-sort field
printf '%s\n' '(set-logic QF_UFDT)(declare-sort U 0)(declare-datatype P ((mk (f U))))(declare-fun p () P)(declare-fun q () P)(assert (= p q))(check-sat)(get-model)' > /tmp/g3.smt2
./target/release/shinri /tmp/g3.smt2
```

- [ ] **Step 2: Write one test per gap, asserting the observed output**

```rust
// ── Spec §5: gaps fenced on purpose. Each test records CURRENT behaviour so a
// successor slice can find it, and so a change here is a deliberate decision
// rather than an accident.

/// BV-sorted fields still render `?`: BV values are extracted solver-side from
/// SAT vars and never enter the Combiner's ModelBuilder, so DT cannot see them.
/// Lifting this is the channel-unification successor slice.
#[test]
fn fenced_bv_field_still_renders_placeholder() {
    // ... assert the recorded output from Step 1 ...
}

/// get-model omits functions of arity > 0, so it is NOT a complete model for UF
/// queries. A graph needs EUF congruence-class enumeration plus a default point.
#[test]
fn fenced_arity_gt_zero_function_is_omitted() {
    // ... assert `f` is absent and `x` is present ...
}

/// Uninterpreted-sort field VALUES resolve (via EUF's Elem), but render as
/// `@elem0` rather than SMT-LIB's `(as @U!val!0 U)`. Pre-existing; the two
/// fields of one class must at least agree.
#[test]
fn fenced_uninterpreted_field_renders_elem_syntax() {
    // ... assert both p and q render the SAME field value ...
}
```

Fill each body from Step 1's recorded output. Where a gap's output surprises you — for instance if the BV field turns out to resolve after all — **pin what actually happens and flag the divergence from spec §5 in the commit message**; do not force the test to match the spec's prediction.

- [ ] **Step 3: Run**

Run: `cargo nextest run -p shinri-solver -E 'binary(qfdt_model_e2e)'`
Expected: all discovered tests PASS.

- [ ] **Step 4: Commit**

```bash
cargo fmt --all
git add -A
git commit -m "test(model): slice43 T7 — pin the three fenced gaps

BV fields, arity>0 functions, and @elem syntax are left for successor slices
(spec §5). Each is now pinned by a test recording actual behaviour, so the gap
is discoverable and any future change to it is deliberate."
```

---

### Task 8: Full verification and the invariant check

Nothing new is implemented here. This is the slice's whole-system gate, and the Global Constraints are what it enforces.

**Files:** none modified unless a gate fails.

- [ ] **Step 1: Lint and format**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
```
Expected: no diff from fmt, zero clippy warnings. Equivalent: `mise run lint`.

- [ ] **Step 2: The fast tier**

```bash
mise run test
```
Expected: green. Note the wall-clock; this slice adds no search work, so it must be unchanged within noise.

- [ ] **Step 3: The FULL unfiltered oracle run**

```bash
cargo nextest run -p shinri-solver --features oracle
```
No `-E` filter. **Confirm a non-zero discovered test count and record it** — without `--features oracle` this compiles to zero tests and a 0-test run reads as green. This is non-negotiable for this slice: Tasks 2 and 3 change the shared model path used by every logic, and a filtered run on slice 40 skipped `qfs_differential` and nearly shipped a string `Sat` → `Unknown` regression.

- [ ] **Step 4: `script_e2e`, the invariant check**

```bash
cargo nextest run -p shinri-solver -E 'binary(script_e2e)'
```
Expected: green, **zero flips of any kind**. `script_e2e` has no `get-model` pins, and per the Global Constraint no verdict can change. Unlike slice 42 there is no permitted-flip direction: an `unknown` → decided flip is as much a regression as `sat` ↔ `unsat`. If anything flips, stop and diagnose — the likely culprit is Task 2's `build_model` reordering having a side effect beyond model text.

- [ ] **Step 5: Confirm the slice's success criteria against the real binary**

Re-run every probe from spec §1 and check each success criterion in spec §7 by hand. Do not accept a subagent's report of a passing gate — run the release binary and read the output.

```bash
cargo build --release --bin shinri
```

Record the before/after for the §1 table in the commit message.

- [ ] **Step 6: Commit and open the PR**

```bash
git add -A
git commit -m "docs(model): slice43 — record measured outcomes and verification

Full unfiltered oracle run: <N> tests discovered, all green. script_e2e: zero
flips. Before/after for every spec §1 probe recorded below.

<paste the before/after table>"
git push -u origin slice43-model-channel
gh pr create --fill
```

Per AGENTS.md: feature work happens on a slice branch with a PR to `main`; merge with a merge commit when CI is green, then delete the branch remote and local.

---

## Self-Review

**Spec coverage:**

| Spec section | Task |
|---|---|
| §2 invariant (no verdict change) | Global Constraints; T2 S10; T8 S4 |
| §3.A DT last into `combined` (+ verify `StrSolver`) | T2 S3 |
| §3.B EUF skips datatype sorts | T2 S4, S5 |
| §3.C builder lookup, numeral branch, **branch order 3-before-4** | T2 S6, S8 |
| §3.C `format_modelval` relocation | T1 |
| §4.A declared-symbol registry | T4 |
| §4.B `define-fun`, single line, determinism, sort defaults | T5 |
| §4.B sort printer | T3 |
| §4.C term printer + `get-value` | T6 |
| §5 all four gaps pinned | T7 (BV, arity>0, `@elem`); T2 S9 (Bool, measured) |
| §6 gate first | T2 (first task with behaviour to gate; rationale in File Structure) |
| §6 unit tiers: dt / euf / theory / core | T2 S8; T2 S5; T2 S3b; T3 |
| §6 oracle, `script_e2e`, standing gates | T8 |
| §7 success criteria | T8 S5 |

**Gaps found and closed during review:**

1. Spec §6 asks for a `shinri-theory` unit test that `build_model` runs `dt` last, asserting on the *combined* builder. No task covered it — now folded in as **Task 2, Step 3b**.
2. Task 3's test as first drafted did not compile: `array_sort`/`bv_sort`/`fp_sort`/`declare_sort`/`rm_sort` take `&mut self` (`context.rs:144-174`) while `sort_name` takes `&self`, so `ctx.sort_name(ctx.bv_sort(8))` cannot borrow-check. Rewritten to bind every sort to a local first, with the reason stated inline so the implementer does not "fix" it back.

**Placeholder scan:** two deliberate "find the real thing first" markers remain, both flagged inline rather than left silent — `app_of_symbol` in T5 S4 (with the recommended resolution: record the `TermId` in `DeclaredFun` at declare time) and the `Context` constructor names in T3 S1. Both are cases where guessing an API name into the plan would be worse than telling the implementer to look. The T2 S5 and T7 S2 test bodies intentionally defer to observed output, per the slice-42 lesson that a predicted number in an assertion hides a wrong premise.

**Type consistency:** `DeclaredFun { name, sym, arity, result }` is introduced in T4 and consumed in T5 — note T5 S4 amends it with a `TermId` field; keep the two in sync. `render_value`'s new trailing `m: &ModelBuilder` parameter is added in T2 S6 and used consistently at both call sites and in `render_field(terms, m, a)`. `sort_name` is defined in T3 and called in T5's `format_model`. `format_modelval`/`format_rational` are made `pub` in T1 and called from `shinri-dt` in T2 and `shinri-solver` in T5.
