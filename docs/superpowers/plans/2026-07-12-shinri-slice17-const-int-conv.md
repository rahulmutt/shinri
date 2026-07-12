# Slice 17 — Constant-RHS int-conv Decision Stage Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decide the constant-RHS fragment of symbolic `str.to_int` / `str.from_int` — both verdicts, zero search — by exact static rewriting (from_int equivalences, to_int range fact, length-pin expansion, lone-occurrence witness rewrites with model repair), keeping slice 15's fence for everything else.

**Architecture:** A stage-2 rewrite pass `decide_const_int_conv` joins the slice-15 fold/fence seam in `shinri-str`'s `int_conv.rs`, between `partial_eval_int_conv` and `has_unreduced_int_conv`. Every rewrite preserves both verdicts (no bound, no Unsat demotion — unlike the closed slice 16). Witness rewrites return `IntConvRepair` obligations; the solver applies them to the model before its existing string witness self-check. Spec: `docs/superpowers/specs/2026-07-12-shinri-slice17-const-int-conv-design.md`.

**Tech Stack:** Rust workspace (`shinri-str`, `shinri-solver`), z3 differential harness in `crates/shinri-solver/tests/qfs_differential.rs`.

## Global Constraints

- Digit classification is EXACTLY ASCII `'0'..='9'` (`char::is_ascii_digit`) — never `char::is_numeric()` (R1; unsound on Unicode digits).
- Every rewrite preserves BOTH verdicts. There is NO bound and NO Unsat→Unknown demotion anywhere in this slice.
- Witness rewrites (lone-occurrence `to_int(s) = k`) fire at ANY polarity and ALWAYS record an `IntConvRepair { var, witness, fallback }`; the solver applies repairs at model output: if the model's value for `var` ≠ `witness`, replace it with `fallback` (R2). Fallbacks: `""` for `k ≥ 0` (its to_int is -1 ≠ k), `"0"` for `k = -1` (its to_int is 0 ≠ -1).
- Witness rewrites require the to_int argument to be a NULLARY UNINTERPRETED CONSTANT that occurs nowhere else in the entire assertion set (R3, global DAG-aware check). Compound arguments fence. (Documented spec refinement: model repair overrides a variable's value.)
- Length pins are TOP-LEVEL atoms `(= (str.len s) L)` (either order), `L` an integral literal in `0..=INT_CONV_PIN_LEN_CAP`; `pub const INT_CONV_PIN_LEN_CAP: usize = 1024;` (documented spec refinement: memory-bomb guard; over-cap pins are ignored → fence). Pins are never removed (R4).
- Int literals are recognized via `Context::const_real_value` ONLY (handles the parser's `(- 5)` Neg-wrapping; slice-15 rule). All numerics arbitrary-precision via `shinri_num::Integer`/`Rational` — no i64/i128 value round-trips.
- Unchanged subterms keep their TermId. `cargo fmt` before every commit (CI fails fast on `cargo fmt --check`). Iterate per-crate (`-p shinri-str -p shinri-solver`), NOT `--workspace` (~50 min).
- New oracle family gets FRESH seed `0x51_61_0000_0001`; existing oracle families and their seeds are untouched (slice-16's planned `0x51_60…` never landed and is NOT reused).
- All work on branch `slice17-const-int-conv`; commit subjects end `(slice 17)`; PR to `main` at the end.

---

### Task 1: from_int equivalences + to_int range fact (stage-2 skeleton)

**Files:**
- Modify: `crates/shinri-str/src/int_conv.rs` (module doc lines 1–19; append after `has_unreduced_int_conv`, ~line 144)
- Test: same file, `#[cfg(test)] mod tests`

**Interfaces:**
- Consumes: existing private helpers `eval_to_int(&str) -> Integer`, `eval_from_int(&Integer) -> String` (same file); `Context` builders `mk_eq`, `mk_app`, `mk_numeral`, `mk_string_const`, `mk_const_bool`, `const_real_value`, `string_const_value`, `int_sort`.
- Produces: `pub struct IntConvRepair { pub var: TermId, pub witness: String, pub fallback: String }`; `pub fn decide_const_int_conv(ctx: &mut Context, assertions: Vec<TermId>) -> (Vec<TermId>, Vec<IntConvRepair>)` (Task 3 wires this into the solver); internal `struct ConstIntConv` with `rewrite`/`try_atom`/`rw_from_int_const`/`rw_to_int_const` and free fn `int_const_value` (Task 2 extends `ConstIntConv` and `rw_to_int_const`). Task 1 never emits repairs (equivalences only).

- [ ] **Step 1: Create the branch**

```bash
git checkout -b slice17-const-int-conv
```

- [ ] **Step 2: Write the failing tests**

Append inside the existing `mod tests` in `crates/shinri-str/src/int_conv.rs` (the module already has `nullary`, `to_int`, `from_int` helpers):

```rust
    // ── Slice 17: constant-RHS decision stage ───────────────────────────────

    #[test]
    fn const_from_int_canonical_literal_rewrites_to_int_eq() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let app = from_int(&mut ctx, n);
        let lit = ctx.mk_string_const("42");
        let atom = ctx.mk_eq(app, lit).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![atom]);
        let k42 = ctx.mk_numeral(Rational::from_int(Integer::from(42i128)), int_s);
        let expected = ctx.mk_eq(n, k42).unwrap();
        assert_eq!(out, vec![expected], "from_int = \"42\"  <=>  n = 42");
        assert!(repairs.is_empty(), "equivalences carry no repair");
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn const_from_int_reversed_args_and_zero() {
        // (= "0" (str.from_int n)) — reversed argument order; "0" IS canonical.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let app = from_int(&mut ctx, n);
        let lit = ctx.mk_string_const("0");
        let atom = ctx.mk_eq(lit, app).unwrap();
        let (out, _) = decide_const_int_conv(&mut ctx, vec![atom]);
        let zero = ctx.mk_numeral(Rational::from_int(Integer::from(0i128)), int_s);
        let expected = ctx.mk_eq(n, zero).unwrap();
        assert_eq!(out, vec![expected]);
    }

    #[test]
    fn const_from_int_empty_literal_rewrites_to_n_lt_zero() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let app = from_int(&mut ctx, n);
        let lit = ctx.mk_string_const("");
        let atom = ctx.mk_eq(app, lit).unwrap();
        let (out, _) = decide_const_int_conv(&mut ctx, vec![atom]);
        let zero = ctx.mk_numeral(Rational::from_int(Integer::from(0i128)), int_s);
        let expected = ctx
            .mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero])
            .unwrap();
        assert_eq!(out, vec![expected], "from_int = \"\"  <=>  n < 0");
    }

    #[test]
    fn const_from_int_noncanonical_literals_rewrite_to_false() {
        // Leading zero, non-digit, and sign literals are outside from_int's
        // range: the atom is FALSE regardless of n.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let f = ctx.mk_const_bool(false);
        for bad in ["05", "abc", "-5", "+5", " 5", "0042"] {
            let app = from_int(&mut ctx, n);
            let lit = ctx.mk_string_const(bad);
            let atom = ctx.mk_eq(app, lit).unwrap();
            let (out, _) = decide_const_int_conv(&mut ctx, vec![atom]);
            assert_eq!(out, vec![f], "from_int = {bad:?} must be false");
        }
    }

    #[test]
    fn const_from_int_rewrites_under_negation() {
        // Full equivalence: valid at ANY polarity — the Not survives, the
        // atom inside it rewrites.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let app = from_int(&mut ctx, n);
        let lit = ctx.mk_string_const("7");
        let atom = ctx.mk_eq(app, lit).unwrap();
        let neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[atom]).unwrap();
        let (out, _) = decide_const_int_conv(&mut ctx, vec![neg]);
        let k7 = ctx.mk_numeral(Rational::from_int(Integer::from(7i128)), int_s);
        let inner = ctx.mk_eq(n, k7).unwrap();
        let expected = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[inner]).unwrap();
        assert_eq!(out, vec![expected]);
    }

    #[test]
    fn const_from_int_big_literal_arbitrary_precision() {
        let big = "1234567890123456789012345678901234567890";
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let app = from_int(&mut ctx, n);
        let lit = ctx.mk_string_const(big);
        let atom = ctx.mk_eq(app, lit).unwrap();
        let (out, _) = decide_const_int_conv(&mut ctx, vec![atom]);
        let v = Integer::from_str_radix(big, 10).unwrap();
        let k = ctx.mk_numeral(Rational::from_int(v), int_s);
        let expected = ctx.mk_eq(n, k).unwrap();
        assert_eq!(out, vec![expected]);
    }

    #[test]
    fn const_to_int_below_neg_one_rewrites_to_false() {
        // to_int's range is {-1} ∪ ℕ: k <= -2 is a context-free range fact.
        // Covers both a directly-built negative numeral and the parser's
        // Neg-wrapped shape (via const_real_value).
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let f = ctx.mk_const_bool(false);
        let app = to_int(&mut ctx, s);
        let m2 = ctx.mk_numeral(Rational::from_int(Integer::from(-2i128)), int_s);
        let atom = ctx.mk_eq(app, m2).unwrap();
        let (out, _) = decide_const_int_conv(&mut ctx, vec![atom]);
        assert_eq!(out, vec![f]);
        // Neg-wrapped `(- 7)`.
        let seven = ctx.mk_numeral(Rational::from_int(Integer::from(7i128)), int_s);
        let neg7 = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[seven]).unwrap();
        let app = to_int(&mut ctx, s);
        let atom = ctx.mk_eq(app, neg7).unwrap();
        let (out, _) = decide_const_int_conv(&mut ctx, vec![atom]);
        assert_eq!(out, vec![f]);
    }

    #[test]
    fn const_to_int_non_lone_survives_to_fence() {
        // Two atoms over the same to_int(s): outside Task 1's fragment (and
        // Task 2 keeps them fenced: the to_int node has two atom parents).
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let app = to_int(&mut ctx, s);
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let seven = ctx.mk_numeral(Rational::from_int(Integer::from(7i128)), int_s);
        let a1 = ctx.mk_eq(app, five).unwrap();
        let a2 = ctx.mk_eq(app, seven).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![a1, a2]);
        assert_eq!(out, vec![a1, a2], "non-lone to_int atoms are untouched");
        assert!(repairs.is_empty());
        assert!(has_unreduced_int_conv(&ctx, &out), "still fenced");
    }

    #[test]
    fn const_stage_noop_without_int_conv() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = nullary(&mut ctx, "x", str_s);
        let y = nullary(&mut ctx, "y", str_s);
        let eq = ctx.mk_eq(x, y).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![eq]);
        assert_eq!(out, vec![eq], "assertions untouched (same TermIds)");
        assert!(repairs.is_empty());
    }
```

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p shinri-str int_conv`
Expected: compile error — `decide_const_int_conv` not found.

- [ ] **Step 4: Implement the stage-2 skeleton**

First, replace the module doc's stage list (lines 9–15, the block starting `//! Stages (run by the solver's string-path seam):` through `//! fences the query to a sound `Unknown`.`) with:

```rust
//! Stages (run by the solver's string-path seam):
//! 1. [`partial_eval_int_conv`] — bottom-up memoized rewrite:
//!    - fold `str.to_int(<lit>)` / `str.from_int(<numeral>)` to a literal;
//!    - rewrite `str.to_int(str.from_int(n))` → `ite(n >= 0, n, -1)` (exact).
//! 2. [`decide_const_int_conv`] (slice 17) — constant-RHS decision: rewrite
//!    `str.from_int(n) = "lit"` to its exact Int equivalent and
//!    `str.to_int(s) = k` to `false` for `k <= -2` (range fact). Full
//!    equivalences, valid at any polarity; both verdicts preserved exactly —
//!    no bound, no demotion (unlike the closed slice 16).
//! 3. [`has_unreduced_int_conv`] — presence fence: any surviving application
//!    (symbolic string to `to_int`; symbolic non-roundtrip Int to `from_int`)
//!    fences the query to a sound `Unknown`.
```

Also change the module doc's first line from `//! Slice 15 pre-pass:` to `//! Slice 15 + 17 pre-pass:`.

Then append after `has_unreduced_int_conv`:

```rust
/// A model-repair obligation recorded by a lone-occurrence witness rewrite
/// (spec R2, added in Task 2). The rewrite `to_int(s) = k` → `s = dec(k)` is
/// verdict-exact at any polarity, but on a negative-polarity branch the
/// solver may falsify `s = dec(k)` with a value that still satisfies the
/// ORIGINAL atom (e.g. "05" for k = 5). At model output the solver replaces
/// `var`'s value by `fallback` whenever it differs from `witness` — the
/// canonical value falsifying the original atom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntConvRepair {
    pub var: TermId,
    pub witness: String,
    pub fallback: String,
}

/// Integer value of an Int-sorted literal — numeral or the parser's
/// Neg-wrapped `(- 5)` shape — via the cross-crate `const_real_value`
/// (single source of truth for literal recognition). None for non-literals
/// and non-integral rationals.
fn int_const_value(ctx: &Context, t: TermId) -> Option<Integer> {
    let r = ctx.const_real_value(t)?;
    if r.denom() == Integer::one() {
        Some(r.numer())
    } else {
        None
    }
}

/// Stage 2 (slice 17): constant-RHS decision. Rewrites decidable
/// `str.to_int` / `str.from_int` equality atoms in place (bottom-up,
/// memoized; unchanged subterms keep their TermId) and returns the rewritten
/// assertions plus the model-repair obligations of any witness rewrites
/// (Task 2). Every rewrite preserves BOTH verdicts: no bound, no demotion.
pub fn decide_const_int_conv(
    ctx: &mut Context,
    assertions: Vec<TermId>,
) -> (Vec<TermId>, Vec<IntConvRepair>) {
    let mut st = ConstIntConv {
        memo: FxHashMap::default(),
        repairs: Vec::new(),
    };
    let out: Vec<TermId> = assertions.iter().map(|&a| st.rewrite(ctx, a)).collect();
    (out, st.repairs)
}

struct ConstIntConv {
    /// Term-rewrite memo: hash-consing gives a repeated atom the same TermId,
    /// so a memo hit reuses the same replacement and (Task 2) emits its
    /// repair obligation exactly once.
    memo: FxHashMap<TermId, TermId>,
    /// Witness-rewrite repair obligations (Task 2; always empty in Task 1).
    repairs: Vec<IntConvRepair>,
}

impl ConstIntConv {
    fn rewrite(&mut self, ctx: &mut Context, t: TermId) -> TermId {
        if let Some(&r) = self.memo.get(&t) {
            return r;
        }
        let result = match ctx.term_node(t).clone() {
            TermNode::Const { .. } => t,
            TermNode::App { op, args, .. } => {
                let children: Vec<TermId> = ctx.children(args).to_vec();
                let new_children: Vec<TermId> =
                    children.iter().map(|&c| self.rewrite(ctx, c)).collect();
                if let Some(r) = self.try_atom(ctx, t, &op, &new_children) {
                    r
                } else {
                    let changed = new_children
                        .iter()
                        .zip(children.iter())
                        .any(|(n, o)| n != o);
                    if changed {
                        ctx.mk_app(op, &new_children)
                            .expect("const int-conv: well-sorted rebuild")
                    } else {
                        t
                    }
                }
            }
        };
        self.memo.insert(t, result);
        result
    }

    /// Constant-RHS atom match: `(= (str.to_int s) k)` / `(= (str.from_int n)
    /// "lit")`, either argument order. Candidate atoms never have rewritten
    /// children (their children are a to_int/from_int app and a literal), so
    /// `atom` — the original node id — identifies the atom for Task 2's
    /// occurrence analysis. Returns the replacement, or None (not a
    /// constant-RHS int-conv atom, or outside the decided fragment → fence).
    fn try_atom(
        &mut self,
        ctx: &mut Context,
        atom: TermId,
        op: &Op,
        kids: &[TermId],
    ) -> Option<TermId> {
        if !matches!(op, Op::Builtin(BuiltinOp::Eq)) || kids.len() != 2 {
            return None;
        }
        for (a, b) in [(kids[0], kids[1]), (kids[1], kids[0])] {
            match ctx.term_node(a).clone() {
                TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrFromInt),
                    args,
                    ..
                } => {
                    let n = ctx.children(args)[0];
                    if let Some(lit) = ctx.string_const_value(b).map(str::to_owned) {
                        return Some(self.rw_from_int_const(ctx, n, &lit));
                    }
                }
                TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrToInt),
                    args,
                    ..
                } => {
                    let s = ctx.children(args)[0];
                    if let Some(k) = int_const_value(ctx, b) {
                        if let Some(r) = self.rw_to_int_const(ctx, atom, a, s, &k) {
                            return Some(r);
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// `(= (str.from_int n) "lit")` — full equivalence, any polarity:
    /// canonical decimal ⇒ `n = val(lit)`; empty ⇒ `n < 0`; anything else
    /// (leading zeros, non-digits, signs) is outside from_int's range ⇒
    /// `false`. Canonicality check reuses the slice-15 evaluators: `lit` is
    /// canonical iff `to_int(lit) >= 0` and `from_int(to_int(lit))`
    /// round-trips to `lit` exactly (rejects "05": to_int("05") = 5 but
    /// from_int(5) = "5" ≠ "05").
    fn rw_from_int_const(&mut self, ctx: &mut Context, n: TermId, lit: &str) -> TermId {
        let v = eval_to_int(lit);
        if v.signum() >= 0 && eval_from_int(&v) == lit {
            let int_s = ctx.int_sort();
            let k = ctx.mk_numeral(Rational::from_int(v), int_s);
            return ctx.mk_eq(n, k).expect("const int-conv: well-sorted n = k");
        }
        if lit.is_empty() {
            let int_s = ctx.int_sort();
            let zero = ctx.mk_numeral(Rational::from_int(Integer::from(0i128)), int_s);
            return ctx
                .mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero])
                .expect("const int-conv: well-sorted n < 0");
        }
        ctx.mk_const_bool(false)
    }

    /// `(= (str.to_int s) k)`. Task 1 decides only the context-free range
    /// fact: `k <= -2` is outside to_int's range `{-1} ∪ ℕ` ⇒ `false` (any
    /// polarity). Task 2 adds the length-pin expansion and the
    /// lone-occurrence witness rewrite. None ⇒ the atom survives to the
    /// fence.
    fn rw_to_int_const(
        &mut self,
        ctx: &mut Context,
        atom: TermId,
        to_int_node: TermId,
        s: TermId,
        k: &Integer,
    ) -> Option<TermId> {
        let _ = (atom, to_int_node, s); // used by Task 2
        if k.signum() < 0 && *k != Integer::from(-1i128) {
            return Some(ctx.mk_const_bool(false));
        }
        None
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-str int_conv`
Expected: all PASS (9 new + the pre-existing slice-15 tests, untouched).

- [ ] **Step 6: Format, lint, commit**

```bash
cargo fmt
cargo fmt --check
cargo clippy -p shinri-str --all-targets
git add crates/shinri-str/src/int_conv.rs
git commit -m "feat(str): const-RHS int_conv equivalences — from_int/=lit + to_int range fact (slice 17)"
```

Note: if clippy flags the `let _ = …` placeholders, silence per its suggestion (e.g. prefix the parameters with `_` instead) — they disappear in Task 2.

---

### Task 2: Length-pin expansion + lone-occurrence witness rewrites (model repair)

**Files:**
- Modify: `crates/shinri-str/src/int_conv.rs` (the `ConstIntConv` from Task 1)
- Test: same file, `mod tests`

**Interfaces:**
- Consumes: Task 1's `ConstIntConv`, `IntConvRepair`, `int_const_value`, and the slice-15 evaluators.
- Produces: the complete `decide_const_int_conv` contract Task 3 wires: pins expand, lone witness atoms rewrite AND emit repairs, everything else survives to the fence. Also `pub const INT_CONV_PIN_LEN_CAP: usize = 1024;`.

- [ ] **Step 1: Write the failing tests**

Append inside `mod tests`:

```rust
    /// Builds `(= (str.len s) l)` for pin tests.
    fn len_pin(ctx: &mut Context, s: TermId, l: i128) -> TermId {
        let int_s = ctx.int_sort();
        let len = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[s])
            .unwrap();
        let ln = ctx.mk_numeral(Rational::from_int(Integer::from(l)), int_s);
        ctx.mk_eq(len, ln).unwrap()
    }

    #[test]
    fn pin_expansion_pads_leading_zeros() {
        // len(s) = 3 ∧ to_int(s) = 5  ⇒  s = "005" (pin kept, atom replaced).
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let pin = len_pin(&mut ctx, s, 3);
        let app = to_int(&mut ctx, s);
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let atom = ctx.mk_eq(app, five).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![pin, atom]);
        let w = ctx.mk_string_const("005");
        let expected = ctx.mk_eq(s, w).unwrap();
        assert_eq!(out, vec![pin, expected], "pin unchanged, atom expanded");
        assert!(repairs.is_empty(), "pin expansion is an equivalence: no repair");
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn pin_expansion_edges() {
        // k = 0, L = 3 → "000"; |dec(k)| = L → no padding; |dec(k)| > L → false.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let f = ctx.mk_const_bool(false);
        for (k, l, want) in [(0i128, 3i128, Some("000")), (123, 3, Some("123")), (1234, 3, None)] {
            let s = nullary(&mut ctx, &format!("s_{k}_{l}"), str_s);
            let pin = len_pin(&mut ctx, s, l);
            let app = to_int(&mut ctx, s);
            let kn = ctx.mk_numeral(Rational::from_int(Integer::from(k)), int_s);
            let atom = ctx.mk_eq(app, kn).unwrap();
            let (out, _) = decide_const_int_conv(&mut ctx, vec![pin, atom]);
            let expected = match want {
                Some(w) => {
                    let wt = ctx.mk_string_const(w);
                    ctx.mk_eq(s, wt).unwrap()
                }
                None => f,
            };
            assert_eq!(out, vec![pin, expected], "k={k} L={l}");
        }
    }

    #[test]
    fn pin_expansion_reversed_pin_and_neg_one_fences() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        // Reversed pin argument order: (= 2 (str.len s)) still counts.
        let s = nullary(&mut ctx, "s", str_s);
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
        let two = ctx.mk_numeral(Rational::from_int(Integer::from(2i128)), int_s);
        let pin = ctx.mk_eq(two, len).unwrap();
        let app = to_int(&mut ctx, s);
        let k = ctx.mk_numeral(Rational::from_int(Integer::from(42i128)), int_s);
        let atom = ctx.mk_eq(app, k).unwrap();
        let (out, _) = decide_const_int_conv(&mut ctx, vec![pin, atom]);
        let w = ctx.mk_string_const("42");
        let expected = ctx.mk_eq(s, w).unwrap();
        assert_eq!(out, vec![pin, expected]);
        // k = -1 under a pin: "length-L non-digit-run" has no finite exact
        // form — fence (spec table).
        let t = nullary(&mut ctx, "t", str_s);
        let pin_t = len_pin(&mut ctx, t, 2);
        let app_t = to_int(&mut ctx, t);
        let neg1 = ctx.mk_numeral(Rational::from_int(Integer::from(-1i128)), int_s);
        let atom_t = ctx.mk_eq(app_t, neg1).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![pin_t, atom_t]);
        assert_eq!(out, vec![pin_t, atom_t], "k = -1 under a pin fences");
        assert!(repairs.is_empty());
        assert!(has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn pin_over_cap_is_ignored() {
        // A pathological pin (L > INT_CONV_PIN_LEN_CAP) must NOT expand
        // (memory-bomb guard) — and s is not lone (it occurs in the pin), so
        // the atom fences.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let pin = len_pin(&mut ctx, s, (INT_CONV_PIN_LEN_CAP as i128) + 1);
        let app = to_int(&mut ctx, s);
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let atom = ctx.mk_eq(app, five).unwrap();
        let (out, _) = decide_const_int_conv(&mut ctx, vec![pin, atom]);
        assert_eq!(out, vec![pin, atom], "over-cap pin ignored → fence");
        assert!(has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn lone_witness_rewrite_positive_and_repair() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let app = to_int(&mut ctx, s);
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let atom = ctx.mk_eq(app, five).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![atom]);
        let w = ctx.mk_string_const("5");
        let expected = ctx.mk_eq(s, w).unwrap();
        assert_eq!(out, vec![expected]);
        assert_eq!(
            repairs,
            vec![IntConvRepair {
                var: s,
                witness: "5".to_string(),
                fallback: String::new(),
            }]
        );
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn lone_witness_rewrite_neg_one_and_negated_polarity() {
        // k = -1: witness "" / fallback "0". Negated atom (any polarity):
        // rewrites INSIDE the Not, repair still emitted.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let app = to_int(&mut ctx, s);
        let neg1 = ctx.mk_numeral(Rational::from_int(Integer::from(-1i128)), int_s);
        let atom = ctx.mk_eq(app, neg1).unwrap();
        let not = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[atom]).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![not]);
        let empty = ctx.mk_string_const("");
        let inner = ctx.mk_eq(s, empty).unwrap();
        let expected = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[inner]).unwrap();
        assert_eq!(out, vec![expected]);
        assert_eq!(
            repairs,
            vec![IntConvRepair {
                var: s,
                witness: String::new(),
                fallback: "0".to_string(),
            }]
        );
    }

    #[test]
    fn witness_repair_emitted_once_for_shared_atom() {
        // The same atom TermId in two assertions: memoized rewrite ⇒ one
        // consistent replacement, exactly ONE repair obligation.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let app = to_int(&mut ctx, s);
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let atom = ctx.mk_eq(app, five).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![atom, atom]);
        assert_eq!(out[0], out[1], "consistent replacement");
        assert_eq!(repairs.len(), 1, "memo hit must not duplicate the repair");
    }

    #[test]
    fn non_lone_and_compound_args_fence() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        // s reused by a second atom: not lone.
        let s = nullary(&mut ctx, "s", str_s);
        let x = nullary(&mut ctx, "x", str_s);
        let app = to_int(&mut ctx, s);
        let a1 = ctx.mk_eq(app, five).unwrap();
        let a2 = ctx.mk_eq(s, x).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![a1, a2]);
        assert_eq!(out, vec![a1, a2], "non-lone s fences");
        assert!(repairs.is_empty());
        // Compound to_int argument: fences even when its vars are lone
        // (witness rewrites require a nullary uninterpreted constant — the
        // model repair overrides a VARIABLE's value).
        let u = nullary(&mut ctx, "u", str_s);
        let v = nullary(&mut ctx, "v", str_s);
        let cc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[u, v])
            .unwrap();
        let app = to_int(&mut ctx, cc);
        let a = ctx.mk_eq(app, five).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![a]);
        assert_eq!(out, vec![a], "compound argument fences");
        assert!(repairs.is_empty());
        assert!(has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn lone_witness_multi_digit() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let app = to_int(&mut ctx, s);
        let k = ctx.mk_numeral(Rational::from_int(Integer::from(305i128)), int_s);
        let atom = ctx.mk_eq(app, k).unwrap();
        let (out, repairs) = decide_const_int_conv(&mut ctx, vec![atom]);
        let w = ctx.mk_string_const("305");
        let expected = ctx.mk_eq(s, w).unwrap();
        assert_eq!(out, vec![expected]);
        assert_eq!(repairs[0].witness, "305");
        assert_eq!(repairs[0].fallback, "");
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str int_conv`
Expected: compile error — `INT_CONV_PIN_LEN_CAP` not found; after a stub const, the pin/witness tests FAIL (atoms survive unchanged; `rw_to_int_const` only handles `k <= -2`).

- [ ] **Step 3: Implement pins, occurrence analysis, witness rewrites**

Add `FxHashSet` to the imports (top of file):

```rust
use rustc_hash::{FxHashMap, FxHashSet};
```

Add after the `IntConvRepair` struct:

```rust
/// Length-pin expansion guard: a pin `(= (str.len s) L)` with
/// `L > INT_CONV_PIN_LEN_CAP` is ignored (the padded witness string would
/// allocate L bytes). Over-cap instances fence to sound Unknown.
pub const INT_CONV_PIN_LEN_CAP: usize = 1024;

/// Distinct parent nodes of every term reachable from `assertions`
/// (DAG-aware: parent edges are recorded when the parent is first visited).
/// Drives the R3 lone-occurrence check.
fn parent_map(ctx: &Context, assertions: &[TermId]) -> FxHashMap<TermId, FxHashSet<TermId>> {
    let mut parents: FxHashMap<TermId, FxHashSet<TermId>> = FxHashMap::default();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if let TermNode::App { args, .. } = ctx.term_node(t) {
            for &c in ctx.children(*args) {
                parents.entry(c).or_default().insert(t);
                stack.push(c);
            }
        }
    }
    parents
}

/// Top-level length pins: assertions of the exact shape `(= (str.len x) L)`
/// (either argument order) with `L` an integral literal in
/// `0..=INT_CONV_PIN_LEN_CAP`. First pin per subject wins; the expansion is
/// valid GIVEN the pin (R4), which always stays asserted, so contradictory
/// pins are harmless.
fn collect_len_pins(ctx: &Context, assertions: &[TermId]) -> FxHashMap<TermId, usize> {
    let mut pins: FxHashMap<TermId, usize> = FxHashMap::default();
    for &a in assertions {
        let TermNode::App {
            op: Op::Builtin(BuiltinOp::Eq),
            args,
            ..
        } = ctx.term_node(a)
        else {
            continue;
        };
        let kids: Vec<TermId> = ctx.children(*args).to_vec();
        if kids.len() != 2 {
            continue;
        }
        for (x, y) in [(kids[0], kids[1]), (kids[1], kids[0])] {
            let TermNode::App {
                op: Op::Builtin(BuiltinOp::StrLen),
                args,
                ..
            } = ctx.term_node(x)
            else {
                continue;
            };
            let subject = ctx.children(*args)[0];
            let Some(l) = int_const_value(ctx, y) else {
                continue;
            };
            if l.signum() < 0 {
                continue;
            }
            let Some(l) = l.to_i128() else { continue };
            if l < 0 || l as usize > INT_CONV_PIN_LEN_CAP {
                continue;
            }
            pins.entry(subject).or_insert(l as usize);
            break;
        }
    }
    pins
}
```

Extend `ConstIntConv` and `decide_const_int_conv`:

```rust
pub fn decide_const_int_conv(
    ctx: &mut Context,
    assertions: Vec<TermId>,
) -> (Vec<TermId>, Vec<IntConvRepair>) {
    let pins = collect_len_pins(ctx, &assertions);
    let parents = parent_map(ctx, &assertions);
    let mut st = ConstIntConv {
        memo: FxHashMap::default(),
        repairs: Vec::new(),
        pins,
        parents,
    };
    let out: Vec<TermId> = assertions.iter().map(|&a| st.rewrite(ctx, a)).collect();
    (out, st.repairs)
}

struct ConstIntConv {
    /// Term-rewrite memo: hash-consing gives a repeated atom the same TermId,
    /// so a memo hit reuses the same replacement and emits its repair
    /// obligation exactly once.
    memo: FxHashMap<TermId, TermId>,
    /// Witness-rewrite repair obligations, consumed by the solver at model
    /// output (R2).
    repairs: Vec<IntConvRepair>,
    /// Top-level length pins (R4), computed over the ORIGINAL assertions.
    pins: FxHashMap<TermId, usize>,
    /// Parent map for the R3 lone-occurrence check, computed over the
    /// ORIGINAL assertions (rewrites do not change other atoms' occurrence
    /// structure).
    parents: FxHashMap<TermId, FxHashSet<TermId>>,
}
```

Replace `rw_to_int_const` with the full version:

```rust
    /// `(= (str.to_int s) k)` — the three decidable cases (spec table):
    ///
    /// 1. `k <= -2` ⇒ `false`: outside to_int's range `{-1} ∪ ℕ` (any
    ///    polarity, context-free).
    /// 2. Top-level length pin `len(s) = L` and `k >= 0` ⇒ the unique
    ///    length-L digit string of value k, or `false` if `|dec(k)| > L`.
    ///    Valid at any polarity GIVEN the pin, which stays asserted (R4).
    ///    `k = -1` under a pin has no finite exact form ⇒ None (fence).
    /// 3. `s` a lone nullary uninterpreted constant (R3) ⇒ witness rewrite
    ///    `s = dec(k)` (`s = ""` for k = -1), verdict-exact at any polarity,
    ///    plus an [`IntConvRepair`] the solver applies at model output (R2):
    ///    with `s` lone, both the original atom and the replacement are
    ///    two-way realizable, so satisfiability is preserved exactly in both
    ///    directions; only the reported model can drift, and the repair's
    ///    fallback (`""` has to_int -1 ≠ k; `"0"` has to_int 0 ≠ -1)
    ///    restores it.
    ///
    /// None ⇒ the atom survives to the fence.
    fn rw_to_int_const(
        &mut self,
        ctx: &mut Context,
        atom: TermId,
        to_int_node: TermId,
        s: TermId,
        k: &Integer,
    ) -> Option<TermId> {
        let neg1 = Integer::from(-1i128);
        if k.signum() < 0 && *k != neg1 {
            return Some(ctx.mk_const_bool(false));
        }
        if let Some(&l) = self.pins.get(&s) {
            if *k == neg1 {
                return None;
            }
            let dec = eval_from_int(k);
            if dec.len() > l {
                return Some(ctx.mk_const_bool(false));
            }
            let padded = format!("{}{}", "0".repeat(l - dec.len()), dec);
            let w = ctx.mk_string_const(&padded);
            return Some(ctx.mk_eq(s, w).expect("const int-conv: well-sorted s = padded"));
        }
        if self.is_lone_var(ctx, s, to_int_node, atom) {
            let (witness, fallback) = if *k == neg1 {
                (String::new(), "0".to_string())
            } else {
                (eval_from_int(k), String::new())
            };
            let w = ctx.mk_string_const(&witness);
            let eq = ctx
                .mk_eq(s, w)
                .expect("const int-conv: well-sorted s = witness");
            self.repairs.push(IntConvRepair {
                var: s,
                witness,
                fallback,
            });
            return Some(eq);
        }
        None
    }

    /// R3: `s` is lone iff it is a nullary uninterpreted constant whose only
    /// parent in the whole assertion forest is `to_int_node`, and that node's
    /// only parent is the candidate `atom`. The atom's own parents are
    /// unrestricted (any boolean structure — polarity is handled by R2's
    /// repair). Restricted to variables because the repair overrides the
    /// var's model value; compound arguments fence.
    fn is_lone_var(&self, ctx: &Context, s: TermId, to_int_node: TermId, atom: TermId) -> bool {
        let is_nullary_var = matches!(
            ctx.term_node(s),
            TermNode::App {
                op: Op::Uninterpreted(_),
                args,
                ..
            } if ctx.children(*args).is_empty()
        );
        is_nullary_var
            && self
                .parents
                .get(&s)
                .is_some_and(|p| p.len() == 1 && p.contains(&to_int_node))
            && self
                .parents
                .get(&to_int_node)
                .is_some_and(|p| p.len() == 1 && p.contains(&atom))
    }
```

Remove the Task-1 placeholder line `let _ = (atom, to_int_node, s);` from `rw_to_int_const` (all parameters are now used).

Also replace the module doc's stage-2 bullet (the block from `//! 2. [`decide_const_int_conv`] (slice 17)` through `//!    no bound, no demotion (unlike the closed slice 16).`) with:

```rust
//! 2. [`decide_const_int_conv`] (slice 17) — constant-RHS decision: rewrite
//!    `str.from_int(n) = "lit"` to its exact Int equivalent and
//!    `str.to_int(s) = k` to `false` for `k <= -2` (any polarity, exact);
//!    expand `str.to_int(s) = k` under a top-level length pin (R4, capped by
//!    [`INT_CONV_PIN_LEN_CAP`]); witness-rewrite lone-occurrence
//!    `str.to_int(s) = k` atoms to `s = dec(k)` / `s = ""` with a
//!    model-repair obligation ([`IntConvRepair`], R2). Both verdicts
//!    preserved exactly — no bound, no demotion (unlike the closed slice 16).
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str int_conv`
Expected: all PASS (Task 1's 9 + Task 2's 9 + pre-existing slice-15 tests).

- [ ] **Step 5: Run the full crate suite, format, lint, commit**

```bash
cargo test -p shinri-str
cargo fmt
cargo fmt --check
cargo clippy -p shinri-str --all-targets
git add crates/shinri-str/src/int_conv.rs
git commit -m "feat(str): length-pin expansion + lone-witness rewrites w/ model repair (slice 17)"
```

---

### Task 3: Solver wiring, model repair, canary flips + e2e pins

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (string-path seam ~line 434–444; model construction ~line 920, just before the string witness self-check)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (`targeted_symbolic_to_from_int_fences_unknown`, ~line 1501)

**Interfaces:**
- Consumes: `shinri_str::int_conv::{decide_const_int_conv, IntConvRepair}` (Tasks 1–2); test helpers `expect(src, Verdict)`, `shinri_verdict(src)`, `shinri_lines_counting_bailouts(src)`, `parse_string_values(resp)`, `z3_with_model(body, model)` (all existing in qfs_differential.rs).
- Produces: the decided/fenced e2e behavior Task 4's oracle family relies on.

The brief's line numbers are planning-time estimates — locate anchors by CONTENT: the `let mut on_string_path = false;` declaration; the slice-15 comment block + fence calling `partial_eval_int_conv`/`has_unreduced_int_conv`; the line `self.eliminated_ite_vals = ite_vals;` followed by the `// Witness self-check (string path)` comment in the `SolveResult::Sat` arm.

- [ ] **Step 1: Update the e2e pins (failing first)**

In `crates/shinri-solver/tests/qfs_differential.rs`, REPLACE the whole `targeted_symbolic_to_from_int_fences_unknown` test with these four:

```rust
#[test]
fn targeted_const_int_conv_decided_sat() {
    // Slice-15 fence canaries FLIPPED (slice 17): the constant-RHS decision
    // stage decides these with zero search.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_int s) 5))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.from_int n) \"5\"))(check-sat)",
        Verdict::Sat,
    );
    // Leading zeros: a length pin forces the non-canonical form "005".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_int s) 5))(assert (= (str.len s) 3))(check-sat)",
        Verdict::Sat,
    );
    // Non-digit escape: -1 is reachable (empty or any non-digit string).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_int s) (- 1)))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.from_int n) \"42\"))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_const_int_conv_decided_unsat() {
    // GENUINE Unsat, matching z3 — the equivalence rewrites prove these
    // outright (slice 16's bounded bridge could only have demoted them).
    expect(
        "(set-logic QF_S)(declare-fun x () String)\
         (assert (= (str.to_int x) (- 5)))(check-sat)",
        Verdict::Unsat,
    );
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.from_int n) \"05\"))(check-sat)",
        Verdict::Unsat,
    );
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.from_int n) \"abc\"))(check-sat)",
        Verdict::Unsat,
    );
    // Pin shorter than the decimal: no 3-char string has value 1234.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_int s) 1234))(assert (= (str.len s) 3))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_const_int_conv_fences_unknown() {
    // Outside the constant-RHS fragment: still fenced (sound Unknown).
    // Flip-markers for a future lazy-propagator slice.
    // Non-lone s (EUF-pinned to a literal the syntactic pre-pass won't chase).
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (= (str.to_int s) (- 1)))(assert (= s \"7\"))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // Fully-symbolic linking.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)(declare-fun n () Int)\
             (assert (= (str.to_int s) n))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // k = -1 under a length pin has no finite exact form.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (= (str.to_int s) (- 1)))(assert (= (str.len s) 2))(check-sat)"
        ),
        Verdict::Unknown,
    );
}

#[test]
fn targeted_const_int_conv_negated_witness_model_repair() {
    // R2 end-to-end: a NEGATED lone witness atom is decided Sat, and the
    // reported model must satisfy the ORIGINAL formula (z3-checked). Without
    // the repair the engine could answer s = "05" — it falsifies the
    // rewritten (= s "5") but still has to_int 5, violating the negation.
    let body = "(set-logic QF_S)(declare-fun s () String)\
                (assert (not (= (str.to_int s) 5)))\n";
    let get = format!("{body}(check-sat)\n(get-value (s))\n");
    let (lines, bailouts) = shinri_lines_counting_bailouts(&get);
    assert_eq!(bailouts, 0, "no guard bailouts expected");
    assert_eq!(lines.first().map(String::as_str), Some("sat"));
    let resp = lines.get(1).expect("get-value response");
    let model = parse_string_values(resp);
    assert!(!model.is_empty(), "model must bind s");
    assert_eq!(
        z3_with_model(body, &model),
        Verdict::Sat,
        "repaired model must satisfy the ORIGINAL negated atom (got {model:?})"
    );
}
```

- [ ] **Step 2: Run the new tests to verify they fail**

Run: `cargo test -p shinri-solver --test qfs_differential targeted_const_int_conv`
Expected: `targeted_const_int_conv_decided_sat`, `_decided_unsat`, and `_negated_witness_model_repair` FAIL (everything still fences to Unknown — the stage isn't wired). `_fences_unknown` passes trivially (still fenced); it locks the fence behavior once wired.

- [ ] **Step 3: Wire the stage and the model repair**

In `crates/shinri-solver/src/lib.rs`, next to `let mut on_string_path = false;` add:

```rust
        let mut int_conv_repairs: Vec<shinri_str::int_conv::IntConvRepair> = Vec::new();
```

Then REPLACE the slice-15 comment block and fence (the lines from `// ── Slice 15: str.to_int / str.from_int ──` down through the `has_unreduced_int_conv` early-return `}`) with:

```rust
            // ── Slice 15 + 17: str.to_int / str.from_int ─────────────────────
            // Stage 1 (slice 15): polarity-free exact rewrites — fold
            // all-literal applications; rewrite the roundtrip
            // str.to_int(str.from_int(n)) → ite(n≥0,n,-1) (eliminated below
            // by reduce_assertions' elim_term_ite).
            // Stage 2 (slice 17): constant-RHS decision — from_int/"lit" and
            // to_int ≤ -2 equivalences, length-pin expansion, lone-occurrence
            // witness rewrites. Verdict-exact at any polarity: NO bound, NO
            // demotion. Witness rewrites record model-repair obligations
            // applied to the Sat model below (R2).
            // Stage 3: any SURVIVING application still fences to sound
            // Unknown — flip-markers for a future lazy-propagator slice.
            assertions = shinri_str::int_conv::partial_eval_int_conv(&mut self.ctx, &assertions);
            let (decided, repairs) =
                shinri_str::int_conv::decide_const_int_conv(&mut self.ctx, assertions);
            assertions = decided;
            int_conv_repairs = repairs;
            if shinri_str::int_conv::has_unreduced_int_conv(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

Then in the `SolveResult::Sat` arm, directly AFTER the line `self.eliminated_ite_vals = ite_vals;` and BEFORE the `// Witness self-check (string path)` comment, insert:

```rust
                // Slice 17 (R2): apply int-conv witness-rewrite model repairs
                // BEFORE the string witness self-check. On a negative-polarity
                // branch the engine may falsify the witness equality
                // `s = dec(k)` with a value that still satisfies the ORIGINAL
                // to_int atom (e.g. "05" for k = 5); replace it with the
                // canonical fallback that falsifies the original atom. Safe:
                // the var is lone (R3), so the change perturbs nothing else,
                // and the fallback also differs from the witness, keeping the
                // rewritten atom false.
                for rep in &int_conv_repairs {
                    let needs_repair = matches!(
                        model.values.get(&rep.var),
                        Some(shinri_theory::types::ModelVal::String(v)) if v != &rep.witness
                    );
                    if needs_repair {
                        model.values.insert(
                            rep.var,
                            shinri_theory::types::ModelVal::String(rep.fallback.clone()),
                        );
                    }
                }
```

- [ ] **Step 4: Run the targeted tests to verify they pass**

Run: `cargo test -p shinri-solver --test qfs_differential targeted_`
Expected: ALL targeted tests PASS — the four new const-int-conv tests AND every pre-existing targeted pin (fold, roundtrip, predicates, indexof/replace, replace_all, substr, fences). If a decided_sat pin returns Unknown, the rewrite did not fire (check the wiring order); if `_negated_witness_model_repair` fails on the z3 check, the repair loop is wrong — STOP and re-read R2, do not weaken the pin.

- [ ] **Step 5: Run the full per-crate suites**

Run: `cargo test -p shinri-str -p shinri-solver`
Expected: all PASS. The five existing string oracle families must be unperturbed except `qfs_to_from_int_matches_z3`, whose unknown count may DROP (some previously-fenced instances are now decided — verdict DISAGREEMENTS are the failure signal, tolerated-count drift is not).

- [ ] **Step 6: Format, lint, commit**

```bash
cargo fmt
cargo fmt --check
cargo clippy -p shinri-solver --all-targets
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "feat(str): wire const int-conv decision stage + model repair, canary flips + e2e pins (slice 17)"
```

---

### Task 4: Differential oracle family `qfs_const_int_conv_matches_z3`

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (Gen impl — after `finish_to_from_int`, ~line 500; gen fns ~line 580; family test after `qfs_to_from_int_matches_z3`, ~line 1145)

**Interfaces:**
- Consumes: existing harness pieces in the same file — `Gen::new`, `Gen::var()`, `Gen::lit()`, `Gen::digit_lit()`, `Gen::small_int_rhs()`, `Gen::to_int_arg()`, `Gen::assertion()`, `Lcg`, `Verdict`, `N_VARS`, `shinri_lines_counting_bailouts`, `z3_verdict`, `z3_with_model`, `parse_string_values`.
- Produces: the 0-disagreement gate for the slice; Task 5 records its tally in the spec.

- [ ] **Step 1: Add the generator methods**

In `impl Gen`, after `finish_to_from_int`:

```rust
    /// One constant-RHS int-conv assertion (slice 17): decided shapes
    /// dominate (equivalences, pin expansion, witness rewrites), with fence
    /// shapes (var reuse across assertions breaks loneness; symbolic RHS)
    /// and fold shapes mixed in. MAY be negated — the decision stage is
    /// verdict-exact at any polarity, and the family's z3 witness check
    /// exercises the R2 model repair on negated witness shapes.
    fn const_int_conv_assertion(&mut self) {
        let atom = match self.rng.below(6) {
            // to_int(var) = k, k in -2..=3: range fact, -1 escape, witness.
            0 => format!("(= (str.to_int {}) {})", self.var(), self.small_int_rhs()),
            // to_int(<mixed arg>) = k: literals keep the fold path's
            // sat/unsat coverage; vars exercise witness/fence.
            1 => {
                let arg = self.to_int_arg();
                let k = self.small_int_rhs();
                format!("(= (str.to_int {arg}) {k})")
            }
            // to_int(var) = multi-digit k: multi-digit witnesses.
            2 => format!(
                "(= (str.to_int {}) {})",
                self.var(),
                100 + self.rng.below(400)
            ),
            // from_int(n0) = target: full equivalence — canonical digits,
            // letters (false), explicit leading-zero literals (false).
            3 => {
                let target = match self.rng.below(3) {
                    0 => self.digit_lit(),
                    1 => self.lit(),
                    _ => format!("\"0{}\"", self.rng.below(10)),
                };
                format!("(= (str.from_int n0) {target})")
            }
            // from_int(n0) = var: symbolic RHS -> fence (tolerated unknown).
            4 => format!("(= (str.from_int n0) {})", self.var()),
            // Length pin + to_int on the same var: pin expansion straddling
            // |dec(k)| (pin 1..=3 vs 1-3 digit k), both padded-Sat and
            // too-short-Unsat.
            _ => {
                let v = self.var();
                let l = 1 + self.rng.below(3);
                self.body
                    .push_str(&format!("(assert (= (str.len {v}) {l}))\n"));
                let k = if self.rng.below(2) == 0 {
                    self.small_int_rhs()
                } else {
                    (10 + self.rng.below(990)).to_string()
                };
                format!("(= (str.to_int {v}) {k})")
            }
        };
        let atom = if self.rng.below(4) == 0 {
            format!("(not {atom})")
        } else {
            atom
        };
        self.body.push_str(&format!("(assert {atom})\n"));
    }

    /// Instance body for the slice-17 family: shared string vars, an Int var
    /// `n0`, 1–2 int-conv assertions, 0–1 general assertions (cross-theory
    /// mixing; reusing a var in a general assertion breaks loneness, giving
    /// the fence path differential coverage).
    fn finish_const_int_conv(mut self) -> String {
        self.body.push_str("(declare-fun n0 () Int)\n");
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.const_int_conv_assertion();
        }
        if self.rng.below(2) == 0 {
            self.assertion();
        }
        self.body
    }
```

Next to the other `gen_*_body` functions:

```rust
fn gen_const_int_conv_body(seed: u64) -> String {
    Gen::new(seed).finish_const_int_conv()
}
```

- [ ] **Step 2: Add the family test**

After `qfs_to_from_int_matches_z3`, copying its harness exactly (unknown-tolerant, witness-checking, guard-bailout-counting) with `CIC_` constants, the fresh seed, and `gen_const_int_conv_body`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Const-int-conv differential oracle (slice 17): constant-RHS to_int/from_int
// atoms are DECIDED by exact rewriting (both verdicts — no demotion). Sat AND
// Unsat must agree with z3 (a wrong equivalence surfaces as a verdict
// disagreement; a wrong witness model surfaces as a WITNESS FAILURE via the
// R2 repair path). Out-of-fragment shapes fence (tolerated unknown). Fresh
// seed — never perturb existing families' seeds.
// ─────────────────────────────────────────────────────────────────────────────

const CIC_N_ITERS: usize = 200;
const CIC_MAX_GUARD_BAILOUTS: usize = CIC_N_ITERS / 10;

#[test]
fn qfs_const_int_conv_matches_z3() {
    let mut rng = Lcg(0x51_61_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness, mut n_guard_bailout) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..CIC_N_ITERS {
        let seed = rng.next();
        let body = gen_const_int_conv_body(seed);

        let (lines, bailouts) = shinri_lines_counting_bailouts(&format!("{body}(check-sat)\n"));
        if bailouts > 0 {
            n_guard_bailout += 1;
            continue;
        }
        let ours = match lines.first().map(String::as_str) {
            Some("sat") => Verdict::Sat,
            Some("unsat") => Verdict::Unsat,
            _ => Verdict::Unknown,
        };
        if ours == Verdict::Unknown {
            n_unknown += 1;
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S CONST-INT-CONV SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{body}(check-sat)"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let get = format!(
                    "{body}(check-sat)\n(get-value ({}))\n",
                    (0..N_VARS)
                        .map(|k| format!("s{k}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                let (lines, _b) = shinri_lines_counting_bailouts(&get);
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
        "qfs_const_int_conv_matches_z3: {CIC_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown / \
         {n_guard_bailout} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "const-int-conv family produced zero SAT instances");
    assert!(
        n_unsat > 0,
        "const-int-conv family produced zero UNSAT instances (false-rewrite shapes missing?)"
    );
    assert!(
        n_witness > 0,
        "no witnesses checked — model/repair path not exercised"
    );
    assert!(
        n_guard_bailout <= CIC_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailout} exceed bound {CIC_MAX_GUARD_BAILOUTS}"
    );
}
```

- [ ] **Step 3: Run the new family**

Run: `cargo test -p shinri-solver --test qfs_differential qfs_const_int_conv_matches_z3 -- --nocapture`
Expected: PASS with 0 disagreements and non-zero sat/unsat/witness counts. Record the printed tally — Task 5 writes it into the spec. A DISAGREEMENT or WITNESS FAILURE is a soundness bug in a rewrite or in the repair: STOP, minimize the printed reproducer, fix in `int_conv.rs` (or the repair loop in lib.rs), and add the minimized case as a targeted pin before rerunning.

- [ ] **Step 4: Re-run all string families unperturbed**

Run: `cargo test -p shinri-solver --test qfs_differential -- --nocapture`
Expected: all families PASS; pre-slice-17 families print tallies consistent with their committed values (`qfs_to_from_int_matches_z3`'s unknown count may DROP — its symbolic constant-RHS instances are now decided; disagreements remain the only failure).

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
cargo fmt --check
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_const_int_conv_matches_z3 differential oracle family (slice 17)"
```

---

### Task 5: Full verification, spec truth-up, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-07-12-shinri-slice17-const-int-conv-design.md` (Status header)

**Interfaces:**
- Consumes: Task 4's printed oracle tally.
- Produces: the merged slice.

- [ ] **Step 1: Full per-crate verification**

```bash
cargo fmt --check
cargo clippy --workspace --all-targets
cargo test -p shinri-str -p shinri-solver
```

Expected: fmt and clippy clean; all tests PASS. (The ~50-min `--workspace` test run is CI's job.)

- [ ] **Step 2: Spec truth-up**

In the spec, change `Status: APPROVED (design), not yet implemented.` to `Status: IMPLEMENTED (slice 17 landed <date>).` and add, below it, the oracle tally paragraph (house format): family name, seed, iters, sat/unsat/unknown/z3-unknown/guard-bailout/witness counts, `**0 disagreements**`, plus a line confirming the pre-existing families re-ran unperturbed. Record the plan's two documented refinements as a numbered **Deviations from the spec** list: (1) witness rewrites restricted to nullary uninterpreted constants (repair overrides a variable's model value; compound arguments fence); (2) `INT_CONV_PIN_LEN_CAP = 1024` pin guard (over-cap pins ignored → fence). Add any further deviations discovered during implementation, or state "none beyond the two above".

- [ ] **Step 3: Commit and open the PR**

```bash
git add docs/superpowers/specs/2026-07-12-shinri-slice17-const-int-conv-design.md
git commit -m "docs: slice-17 spec truth-up — IMPLEMENTED + oracle tally"
git push -u origin slice17-const-int-conv
gh pr create --title "Slice 17: constant-RHS decision stage for symbolic str.to_int/str.from_int" \
  --body "Decides the constant-RHS fragment by exact static rewriting — both verdicts, zero search, no demotion (spec: docs/superpowers/specs/2026-07-12-shinri-slice17-const-int-conv-design.md; successor to the closed slice 16, see docs/superpowers/research/2026-07-11-eager-digit-bridge-infeasibility.md). Witness rewrites carry model repair (R2). New oracle family qfs_const_int_conv_matches_z3: 0 disagreements @ 200 iters."
```

Expected: PR opens; CI (fmt gate + full workspace tests + differential families) goes green before merge.
