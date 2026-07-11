# Slice 16 — Bounded Digit Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decide the sat-side of symbolic `str.to_int(u)` / `str.from_int(n)` by an eager bounded under-approximate encoding (word equations over fresh single-char vars + linear digit sums), replacing slice 15's presence fence; in-bound Unsat is demoted to Unknown.

**Architecture:** A third stage `bridge_int_conv` joins the slice-15 fold/fence seam in `shinri-str`'s `int_conv.rs`: it replaces each surviving application with a fresh value variable plus top-level defining assertions, and returns a `fired` flag. The solver's string path consumes the flag at its single `SolveResult::Unsat` point to demote to `Unknown`. Spec: `docs/superpowers/specs/2026-07-11-shinri-slice16-digit-bridge-design.md`.

**Tech Stack:** Rust workspace (`shinri-str`, `shinri-solver`), z3 differential harness in `crates/shinri-solver/tests/qfs_differential.rs`.

## Global Constraints

- Digit classification is EXACTLY ASCII `'0'..='9'` — never `char::is_numeric()` (spec: unsound on Unicode digits).
- `INT_CONV_DIGIT_CAP = 8` — the bound is ASSERTED (under-approximation). Sat → Sat; Unsat → Unknown **iff the bridge fired**.
- `to_int`'s `dig_i` selector MUST be the char-only disjunction `(or (= c_i "0") … (= c_i "9"))`, never the one-hot with digit values — the one-hot variant lets a mismatched `d_i` fabricate `v = -1` (spec R2, unsound Sat).
- Fresh internal vars use the `!` prefix (`!tiv/!tic/!tid`, `!fis/!fic/!fid`) via `reduce::next_fresh()`.
- New oracle family gets a FRESH seed (`0x51_60_0000_0001`); existing oracle families and their seeds are untouched.
- Run `cargo fmt` before every commit; CI fails fast on `cargo fmt --check`. Iterate with per-crate tests (`-p shinri-str -p shinri-solver`), NOT `--workspace` (~50 min).
- All work on branch `slice16-digit-bridge`; PR to `main` at the end.

---

### Task 1: `to_int` bridge encoding in `int_conv.rs`

**Files:**
- Modify: `crates/shinri-str/src/int_conv.rs` (append after `has_unreduced_int_conv`, ~line 144)
- Test: same file, `#[cfg(test)] mod tests`

**Interfaces:**
- Consumes: `crate::reduce::next_fresh() -> u32` (crate-private counter, already `pub(crate)`); slice-15 helpers `partial_eval_int_conv`, `has_unreduced_int_conv`; `Context` term builders (`declare_fun`, `mk_app`, `mk_numeral`, `mk_string_const`, `int_sort`, `string_sort`).
- Produces: `pub fn bridge_int_conv(ctx: &mut Context, assertions: Vec<TermId>) -> (Vec<TermId>, bool)` — Task 3 wires this into the solver; Task 2 adds the `from_int` arm. Also `pub const INT_CONV_DIGIT_CAP: usize = 8`. Internal: `struct Bridger { memo, defs }`, `fn bridge_to_int`, helpers `fresh_var`, `int_num`, `bapp`, `digit_sum`, `concat_prefix`.

- [ ] **Step 1: Create the branch**

```bash
git checkout -b slice16-digit-bridge
```

- [ ] **Step 2: Write the failing tests**

Append inside the existing `mod tests` in `crates/shinri-str/src/int_conv.rs` (the module already has `nullary`, `to_int`, `from_int` helpers):

```rust
    // ── Slice 16: digit bridge ───────────────────────────────────────────────

    #[test]
    fn bridge_to_int_eliminates_op_and_fires() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let app = to_int(&mut ctx, s);
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[app, five])
            .unwrap();
        let (out, fired) = bridge_int_conv(&mut ctx, vec![atom]);
        assert!(fired, "symbolic to_int must fire the bridge");
        assert!(
            !has_unreduced_int_conv(&ctx, &out),
            "bridge must eliminate every to_int application"
        );
        assert!(
            out.len() > 1,
            "defining assertions must be appended (got {})",
            out.len()
        );
        // Every emitted assertion is Bool-sorted (well-formed top-level).
        let bool_s = ctx.sort_of(out[0]);
        for &a in &out {
            assert_eq!(ctx.sort_of(a), bool_s);
        }
    }

    #[test]
    fn bridge_memoizes_repeated_to_int() {
        // Two atoms over the SAME to_int(s) application: gadget defs appended
        // once (hash-consing gives both atoms the same app TermId).
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let app = to_int(&mut ctx, s);
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let seven = ctx.mk_numeral(Rational::from_int(Integer::from(7i128)), int_s);
        let a1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[app, five])
            .unwrap();
        let a2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[app, seven])
            .unwrap();
        let (out1, _) = bridge_int_conv(&mut ctx, vec![a1]);
        let base = out1.len();
        // Fresh context, same shapes, both atoms: exactly ONE more assertion
        // (the second rewritten atom), zero duplicate defs.
        let mut ctx2 = Context::new();
        let str_s2 = ctx2.string_sort();
        let int_s2 = ctx2.int_sort();
        let s2 = nullary(&mut ctx2, "s", str_s2);
        let app2 = to_int(&mut ctx2, s2);
        let five2 = ctx2.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s2);
        let seven2 = ctx2.mk_numeral(Rational::from_int(Integer::from(7i128)), int_s2);
        let b1 = ctx2
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[app2, five2])
            .unwrap();
        let b2 = ctx2
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[app2, seven2])
            .unwrap();
        let (out2, _) = bridge_int_conv(&mut ctx2, vec![b1, b2]);
        assert_eq!(out2.len(), base + 1, "shared gadget: defs emitted once");
    }

    #[test]
    fn bridge_noop_without_survivors() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = nullary(&mut ctx, "x", str_s);
        let y = nullary(&mut ctx, "y", str_s);
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let (out, fired) = bridge_int_conv(&mut ctx, vec![eq]);
        assert!(!fired, "no int_conv application: bridge must not fire");
        assert_eq!(out, vec![eq], "assertions untouched");
    }
```

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p shinri-str int_conv`
Expected: compile error — `bridge_int_conv` not found.

- [ ] **Step 4: Implement the bridge (to_int arm)**

Append after `has_unreduced_int_conv` in `crates/shinri-str/src/int_conv.rs`:

```rust
/// Slice 16: max digit count K for the bounded digit-bridge encodings below.
/// The bound is ASSERTED (`str.len u <= K`; `n < 10^K`), making the bridge an
/// UNDER-approximation of the unbounded semantics: Sat verdicts are genuine
/// (the encoding is exact inside the bound and fresh vars extend any model);
/// an Unsat under the bound does NOT entail unbounded Unsat, so the solver
/// demotes Unsat to Unknown whenever the bridge fired (see the string path's
/// outcome match in shinri-solver's lib.rs). Per occurrence the encoding is
/// K char gadgets + K length-case implications + 10·K value links, with LIA
/// coefficients up to 10^(K-1); K = 8 keeps a solve comfortably inside the
/// wordeq fuel budget while covering the digit ranges QF_S benchmarks use.
/// There is no over-cap fence: the cap IS the asserted bound; over-bound
/// instances are what the Unsat demotion pays for.
pub const INT_CONV_DIGIT_CAP: usize = 8;

/// A fresh nullary uninterpreted constant (internal: `!`-prefixed names keep
/// it out of printed models, same convention as slice 12's `!pfx`/`!sfx`).
fn fresh_var(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
    let f = ctx.declare_fun(name, &[], sort);
    ctx.mk_app(Op::Uninterpreted(f), &[])
        .expect("digit bridge: fresh nullary var")
}

/// Int numeral from an i128 (negative values allowed: mk_numeral accepts a
/// negative Rational, matching the slice-15 fold tests).
fn int_num(ctx: &mut Context, v: i128) -> TermId {
    let int_s = ctx.int_sort();
    ctx.mk_numeral(Rational::from_int(Integer::from(v)), int_s)
}

/// Builtin application; the digit bridge only builds well-sorted shapes.
fn bapp(ctx: &mut Context, op: BuiltinOp, args: &[TermId]) -> TermId {
    ctx.mk_app(Op::Builtin(op), args)
        .expect("digit bridge: well-sorted app")
}

/// Σ digits[i]·10^(k-1-i) — digits[0] is the MOST significant. k = len >= 1.
/// Pure LINEAR arithmetic: constant coefficient times Int var; 10^(k-1) at
/// K = 8 is 10^7, far inside i128 (spec R4).
fn digit_sum(ctx: &mut Context, digits: &[TermId]) -> TermId {
    let k = digits.len();
    let mut terms = Vec::with_capacity(k);
    for (i, &d) in digits.iter().enumerate() {
        let pow = 10i128.pow((k - 1 - i) as u32);
        terms.push(if pow == 1 {
            d
        } else {
            let c = int_num(ctx, pow);
            bapp(ctx, BuiltinOp::Mul, &[c, d])
        });
    }
    if terms.len() == 1 {
        terms[0]
    } else {
        bapp(ctx, BuiltinOp::Add, &terms)
    }
}

/// c_1 ++ … ++ c_k; StrConcat requires >= 2 args, so k = 1 is the bare char.
fn concat_prefix(ctx: &mut Context, chars: &[TermId]) -> TermId {
    if chars.len() == 1 {
        chars[0]
    } else {
        bapp(ctx, BuiltinOp::StrConcat, chars)
    }
}

/// Stage 3 (slice 16): bounded digit bridge. Replaces every application that
/// SURVIVED [`partial_eval_int_conv`] with a fresh value variable plus
/// defining assertions (appended after the rewritten originals). Returns the
/// extended assertion list and `fired` (true iff anything was replaced — the
/// solver demotes Unsat to Unknown exactly when `fired`).
pub fn bridge_int_conv(ctx: &mut Context, assertions: Vec<TermId>) -> (Vec<TermId>, bool) {
    let mut br = Bridger {
        memo: FxHashMap::default(),
        defs: Vec::new(),
    };
    let mut out: Vec<TermId> = assertions.iter().map(|&a| br.rewrite(ctx, a)).collect();
    let fired = !br.defs.is_empty();
    out.append(&mut br.defs);
    (out, fired)
}

struct Bridger {
    /// Term-rewrite memo: hash-consing gives a repeated application the same
    /// TermId, so a memo hit reuses the SAME fresh value var and its gadget
    /// defs are emitted exactly once.
    memo: FxHashMap<TermId, TermId>,
    /// Defining assertions, appended to the assertion list by the caller.
    defs: Vec<TermId>,
}

impl Bridger {
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
                match op {
                    Op::Builtin(BuiltinOp::StrToInt) => self.bridge_to_int(ctx, new_children[0]),
                    _ => {
                        let changed = new_children
                            .iter()
                            .zip(children.iter())
                            .any(|(n, o)| n != o);
                        if changed {
                            ctx.mk_app(op, &new_children)
                                .expect("digit bridge: well-sorted rebuild")
                        } else {
                            t
                        }
                    }
                }
            }
        };
        self.memo.insert(t, result);
        result
    }

    /// `str.to_int(u)`, u symbolic (post-fold) → fresh Int `v` with:
    ///   |u| >= 0                       (exhaustiveness insurance)
    ///   |u| <= K                       (the ASSERTED under-approximation)
    ///   |u| = 0 → v = -1
    ///   |c_i| = 1                      (unconditional; chars are fresh)
    ///   c_i = "j" → d_i = j            (value links, j in 0..=9)
    ///   |u| = k → u = c_1 ++…++ c_k
    ///           ∧ (alldig_k → v = Σ d_i·10^(k-i))
    ///           ∧ (¬alldig_k → v = -1)          (k in 1..=K)
    /// where dig_i is the CHAR-ONLY digit disjunction (or (= c_i "0") …) and
    /// alldig_k = (and dig_1 … dig_k). dig_i must NOT be the one-hot with
    /// digit values: ¬one-hot is satisfiable by a digit char with a mismatched
    /// d_i, which would fabricate v = -1 for an all-digit string (spec R2,
    /// unsound Sat). Under ¬dig_i the free d_i is harmless: every sum use is
    /// gated behind alldig_k.
    fn bridge_to_int(&mut self, ctx: &mut Context, u: TermId) -> TermId {
        let k_cap = INT_CONV_DIGIT_CAP;
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let n = crate::reduce::next_fresh();
        let v = fresh_var(ctx, &format!("!tiv{n}"), int_s);
        let chars: Vec<TermId> = (0..k_cap)
            .map(|i| fresh_var(ctx, &format!("!tic{n}_{i}"), str_s))
            .collect();
        let digits: Vec<TermId> = (0..k_cap)
            .map(|i| fresh_var(ctx, &format!("!tid{n}_{i}"), int_s))
            .collect();
        let digit_lits: Vec<TermId> = (0..10).map(|j| ctx.mk_string_const(&j.to_string())).collect();
        let len_u = bapp(ctx, BuiltinOp::StrLen, &[u]);
        let zero = int_num(ctx, 0);
        let one = int_num(ctx, 1);
        let neg1 = int_num(ctx, -1);
        let cap_num = int_num(ctx, k_cap as i128);
        let v_neg1 = bapp(ctx, BuiltinOp::Eq, &[v, neg1]);
        // Exhaustiveness + bound.
        let ge0 = bapp(ctx, BuiltinOp::Ge, &[len_u, zero]);
        self.defs.push(ge0);
        let le_cap = bapp(ctx, BuiltinOp::Le, &[len_u, cap_num]);
        self.defs.push(le_cap);
        // |u| = 0 → v = -1.
        let g0 = bapp(ctx, BuiltinOp::Eq, &[len_u, zero]);
        let imp0 = bapp(ctx, BuiltinOp::Implies, &[g0, v_neg1]);
        self.defs.push(imp0);
        // Per-char: |c_i| = 1, value links, dig_i disjunction.
        let mut dig: Vec<TermId> = Vec::with_capacity(k_cap);
        for i in 0..k_cap {
            let len_ci = bapp(ctx, BuiltinOp::StrLen, &[chars[i]]);
            let l1 = bapp(ctx, BuiltinOp::Eq, &[len_ci, one]);
            self.defs.push(l1);
            let ors: Vec<TermId> = (0..10)
                .map(|j| bapp(ctx, BuiltinOp::Eq, &[chars[i], digit_lits[j]]))
                .collect();
            for (j, &cj) in ors.iter().enumerate() {
                let jn = int_num(ctx, j as i128);
                let dv = bapp(ctx, BuiltinOp::Eq, &[digits[i], jn]);
                let link = bapp(ctx, BuiltinOp::Implies, &[cj, dv]);
                self.defs.push(link);
            }
            dig.push(bapp(ctx, BuiltinOp::Or, &ors));
        }
        // Length cases 1..=K.
        for k in 1..=k_cap {
            let kn = int_num(ctx, k as i128);
            let g = bapp(ctx, BuiltinOp::Eq, &[len_u, kn]);
            let cc = concat_prefix(ctx, &chars[0..k]);
            let ueq = bapp(ctx, BuiltinOp::Eq, &[u, cc]);
            let alldig = if k == 1 {
                dig[0]
            } else {
                bapp(ctx, BuiltinOp::And, &dig[0..k])
            };
            let sum = digit_sum(ctx, &digits[0..k]);
            let v_sum = bapp(ctx, BuiltinOp::Eq, &[v, sum]);
            let pos_case = bapp(ctx, BuiltinOp::Implies, &[alldig, v_sum]);
            let nd = bapp(ctx, BuiltinOp::Not, &[alldig]);
            let neg_case = bapp(ctx, BuiltinOp::Implies, &[nd, v_neg1]);
            let body = bapp(ctx, BuiltinOp::And, &[ueq, pos_case, neg_case]);
            let case = bapp(ctx, BuiltinOp::Implies, &[g, body]);
            self.defs.push(case);
        }
        v
    }
}
```

Also replace the stage list in the module doc comment (lines 9–15, the block starting `//! Stages (run by the solver's string-path seam):`) with:

```rust
//! Stages (run by the solver's string-path seam):
//! 1. [`partial_eval_int_conv`] — bottom-up memoized rewrite:
//!    - fold `str.to_int(<lit>)` / `str.from_int(<numeral>)` to a literal;
//!    - rewrite `str.to_int(str.from_int(n))` → `ite(n >= 0, n, -1)` (exact).
//! 2. [`bridge_int_conv`] (slice 16) — bounded digit bridge: every surviving
//!    application is replaced by a fresh value variable plus defining
//!    word-equation/LIA assertions, exact inside [`INT_CONV_DIGIT_CAP`]
//!    digits; the bound is ASSERTED, so the solver demotes Unsat → Unknown
//!    whenever the bridge fired.
//! 3. [`has_unreduced_int_conv`] — formerly the slice-15 presence fence; now
//!    the solver's post-bridge debug invariant (nothing may survive stage 2).
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-str int_conv`
Expected: all PASS (including the pre-existing slice-15 tests, untouched).

- [ ] **Step 6: Format and commit**

```bash
cargo fmt
git add crates/shinri-str/src/int_conv.rs
git commit -m "feat(str): digit-bridge to_int encoding — gadget + Bridger (slice 16)"
```

---

### Task 2: `from_int` bridge encoding

**Files:**
- Modify: `crates/shinri-str/src/int_conv.rs` (the `Bridger` from Task 1)
- Test: same file, `mod tests`

**Interfaces:**
- Consumes: Task 1's `Bridger`, `fresh_var`, `int_num`, `bapp`, `digit_sum`, `concat_prefix`, `INT_CONV_DIGIT_CAP`.
- Produces: `Bridger::bridge_from_int(&mut self, ctx: &mut Context, n: TermId) -> TermId` and the `StrFromInt` arm in `Bridger::rewrite`, completing `bridge_int_conv` for both directions (Task 3 relies on: NO application of either op survives `bridge_int_conv`).

- [ ] **Step 1: Write the failing tests**

Append inside `mod tests`:

```rust
    #[test]
    fn bridge_from_int_eliminates_op_and_fires() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let app = from_int(&mut ctx, n);
        let lit = ctx.mk_string_const("5");
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[app, lit]).unwrap();
        let (out, fired) = bridge_int_conv(&mut ctx, vec![atom]);
        assert!(fired, "symbolic from_int must fire the bridge");
        assert!(
            !has_unreduced_int_conv(&ctx, &out),
            "bridge must eliminate every from_int application"
        );
        assert!(out.len() > 1, "defining assertions must be appended");
    }

    #[test]
    fn bridge_handles_nested_survivors_bottom_up() {
        // from_int(n) nested under str.len: the String-sorted replacement must
        // slot into the parent app (well-sorted rebuild), no survivor.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fi = from_int(&mut ctx, n);
        let len = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[fi])
            .unwrap();
        let two = ctx.mk_numeral(Rational::from_int(Integer::from(2i128)), int_s);
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[len, two]).unwrap();
        let (out, fired) = bridge_int_conv(&mut ctx, vec![atom]);
        assert!(fired);
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str int_conv`
Expected: `bridge_from_int_eliminates_op_and_fires` FAILS — `has_unreduced_int_conv` still true (the `StrFromInt` arm doesn't exist, the app survives). `bridge_handles_nested_survivors_bottom_up` FAILS the same way.

- [ ] **Step 3: Implement `bridge_from_int`**

In `Bridger::rewrite`, replace the match on `op`:

```rust
                match op {
                    Op::Builtin(BuiltinOp::StrToInt) => self.bridge_to_int(ctx, new_children[0]),
                    Op::Builtin(BuiltinOp::StrFromInt) => {
                        self.bridge_from_int(ctx, new_children[0])
                    }
                    _ => {
                        let changed = new_children
                            .iter()
                            .zip(children.iter())
                            .any(|(n, o)| n != o);
                        if changed {
                            ctx.mk_app(op, &new_children)
                                .expect("digit bridge: well-sorted rebuild")
                        } else {
                            t
                        }
                    }
                }
```

Add the method to `impl Bridger`:

```rust
    /// `str.from_int(n)`, n symbolic (post-fold) → fresh String `s` with:
    ///   n < 10^K                        (the ASSERTED under-approximation)
    ///   n < 0 → s = ""                  (exact; the bound is compatible:
    ///                                    n < 0 < 10^K)
    ///   |c_i| = 1                       (unconditional)
    ///   (n >= lo_k ∧ n < 10^k) → s = c_1 ++…++ c_k ∧ n = Σ d_i·10^(k-i)
    ///                            ∧ onehot_1 … onehot_k        (k in 1..=K)
    /// where lo_1 = 0, lo_k = 10^(k-1), and onehot_i is the BARE one-hot
    /// (or (and (= c_i "0") (= d_i 0)) … (and (= c_i "9") (= d_i 9))) —
    /// from_int has no non-digit case, so the to_int-only dig_i selector
    /// escape is not needed here (spec §Design). Canonicality (no leading
    /// zero) is implied: n >= 10^(k-1) plus the digit sum forces d_1 >= 1
    /// for k >= 2. The k-ranges plus the n < 0 branch partition
    /// ℤ ∩ (-∞, 10^K): exactly one case fires under the asserted bound.
    fn bridge_from_int(&mut self, ctx: &mut Context, n_arg: TermId) -> TermId {
        let k_cap = INT_CONV_DIGIT_CAP;
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let fresh_n = crate::reduce::next_fresh();
        let s = fresh_var(ctx, &format!("!fis{fresh_n}"), str_s);
        let chars: Vec<TermId> = (0..k_cap)
            .map(|i| fresh_var(ctx, &format!("!fic{fresh_n}_{i}"), str_s))
            .collect();
        let digits: Vec<TermId> = (0..k_cap)
            .map(|i| fresh_var(ctx, &format!("!fid{fresh_n}_{i}"), int_s))
            .collect();
        let digit_lits: Vec<TermId> = (0..10).map(|j| ctx.mk_string_const(&j.to_string())).collect();
        let zero = int_num(ctx, 0);
        let one = int_num(ctx, 1);
        // Bound: n < 10^K.
        let ten_cap = int_num(ctx, 10i128.pow(k_cap as u32));
        let bound = bapp(ctx, BuiltinOp::Lt, &[n_arg, ten_cap]);
        self.defs.push(bound);
        // n < 0 → s = "".
        let lt0 = bapp(ctx, BuiltinOp::Lt, &[n_arg, zero]);
        let empty = ctx.mk_string_const("");
        let s_empty = bapp(ctx, BuiltinOp::Eq, &[s, empty]);
        let neg_case = bapp(ctx, BuiltinOp::Implies, &[lt0, s_empty]);
        self.defs.push(neg_case);
        // |c_i| = 1.
        for &c in &chars {
            let len_c = bapp(ctx, BuiltinOp::StrLen, &[c]);
            let l1 = bapp(ctx, BuiltinOp::Eq, &[len_c, one]);
            self.defs.push(l1);
        }
        // Digit-count cases 1..=K.
        for k in 1..=k_cap {
            let lo = if k == 1 {
                bapp(ctx, BuiltinOp::Ge, &[n_arg, zero])
            } else {
                let lo_num = int_num(ctx, 10i128.pow((k - 1) as u32));
                bapp(ctx, BuiltinOp::Ge, &[n_arg, lo_num])
            };
            let hi_num = int_num(ctx, 10i128.pow(k as u32));
            let hi = bapp(ctx, BuiltinOp::Lt, &[n_arg, hi_num]);
            let g = bapp(ctx, BuiltinOp::And, &[lo, hi]);
            let cc = concat_prefix(ctx, &chars[0..k]);
            let seq = bapp(ctx, BuiltinOp::Eq, &[s, cc]);
            let sum = digit_sum(ctx, &digits[0..k]);
            let neq = bapp(ctx, BuiltinOp::Eq, &[n_arg, sum]);
            let mut conj = vec![seq, neq];
            for i in 0..k {
                let onehot: Vec<TermId> = (0..10)
                    .map(|j| {
                        let ce = bapp(ctx, BuiltinOp::Eq, &[chars[i], digit_lits[j]]);
                        let jn = int_num(ctx, j as i128);
                        let de = bapp(ctx, BuiltinOp::Eq, &[digits[i], jn]);
                        bapp(ctx, BuiltinOp::And, &[ce, de])
                    })
                    .collect();
                conj.push(bapp(ctx, BuiltinOp::Or, &onehot));
            }
            let body = bapp(ctx, BuiltinOp::And, &conj);
            let case = bapp(ctx, BuiltinOp::Implies, &[g, body]);
            self.defs.push(case);
        }
        s
    }
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str int_conv`
Expected: all PASS.

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
git add crates/shinri-str/src/int_conv.rs
git commit -m "feat(str): digit-bridge from_int encoding — both directions complete (slice 16)"
```

---

### Task 3: Solver wiring, Unsat demotion, canary flips + e2e pins

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (string-path seam ~line 436–447; outcome match ~line 803)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (`targeted_symbolic_to_from_int_fences_unknown`, ~line 1500)

**Interfaces:**
- Consumes: `shinri_str::int_conv::bridge_int_conv(ctx, Vec<TermId>) -> (Vec<TermId>, bool)`, `has_unreduced_int_conv` (both from Tasks 1–2); test helpers `expect(src, Verdict)`, `shinri_verdict(src)` (existing in qfs_differential.rs).
- Produces: the flipped-canary behavior Tasks 4–5 build on: symbolic `to_int`/`from_int` queries return Sat when satisfiable in-bound, Unknown instead of Unsat when the bridge fired.

- [ ] **Step 1: Update the e2e pins (failing first)**

In `crates/shinri-solver/tests/qfs_differential.rs`, REPLACE the whole `targeted_symbolic_to_from_int_fences_unknown` test with:

```rust
#[test]
fn targeted_digit_bridge_decided() {
    // Slice-15 canaries FLIPPED (slice 16): the digit bridge decides the
    // sat-side of symbolic to_int / from_int.
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
    // Non-digit escape: -1 is reachable (any non-digit or empty string).
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
fn targeted_digit_bridge_demotions_unknown() {
    // The bridge UNDER-approximates (its digit bound is asserted), so an
    // in-bound Unsat is demoted to a sound Unknown. z3 answers unsat on all
    // three; deciding them needs the one-sided range abstraction (future
    // slice — these are its flip-markers).
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun x () String)\
             (assert (= (str.to_int x) (- 5)))(check-sat)"
        ),
        Verdict::Unknown,
    );
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun n () Int)\
             (assert (= (str.from_int n) \"05\"))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // Spec-R2 guard: dig_i must be the CHAR-ONLY digit disjunction. The
    // unsound one-hot variant would let a mismatched d_i fabricate v = -1
    // for the all-digit string "7" and answer Sat here.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (= (str.to_int s) (- 1)))(assert (= s \"7\"))(check-sat)"
        ),
        Verdict::Unknown,
    );
}
```

- [ ] **Step 2: Run the new tests to verify they fail**

Run: `cargo test -p shinri-solver --test qfs_differential targeted_digit_bridge`
Expected: `targeted_digit_bridge_decided` FAILS (all five pins currently return Unknown — the fence is still wired). `targeted_digit_bridge_demotions_unknown` passes trivially for the first two (still fenced) — that's fine; it locks the demotion behavior once wired.

- [ ] **Step 3: Wire the bridge and the demotion gate**

In `crates/shinri-solver/src/lib.rs`, next to `let mut on_string_path = false;` (~line 401) add:

```rust
        let mut int_conv_bridged = false;
```

Then REPLACE the slice-15 fence block (~lines 436–447):

```rust
            assertions = shinri_str::int_conv::partial_eval_int_conv(&mut self.ctx, &assertions);
            if shinri_str::int_conv::has_unreduced_int_conv(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

with:

```rust
            assertions = shinri_str::int_conv::partial_eval_int_conv(&mut self.ctx, &assertions);
            // ── Slice 16: bounded digit bridge ────────────────────────────
            // Surviving symbolic applications are ENCODED (fresh value var +
            // word-equation/LIA defining assertions, exact inside
            // INT_CONV_DIGIT_CAP digits) instead of fenced. The digit bound
            // is ASSERTED, so the encoding UNDER-approximates: Sat is
            // genuine; Unsat is demoted to Unknown at the outcome match
            // below (`int_conv_bridged`).
            let (bridged, fired) =
                shinri_str::int_conv::bridge_int_conv(&mut self.ctx, assertions);
            assertions = bridged;
            int_conv_bridged = fired;
            debug_assert!(
                !shinri_str::int_conv::has_unreduced_int_conv(&self.ctx, &assertions),
                "digit bridge must eliminate every surviving int_conv application"
            );
```

Also replace the slice-15 comment block directly above (the lines from `// ── Slice 15: str.to_int / str.from_int ──` through `// canary-pinned flip-markers for a future digit-bridge slice.`) with:

```rust
            // ── Slice 15: str.to_int / str.from_int ──────────────────────────
            // Polarity-FREE exact rewrites: fold all-literal applications;
            // rewrite the roundtrip str.to_int(str.from_int(n)) → ite(n≥0,n,-1)
            // (eliminated below by reduce_assertions' elim_term_ite). Surviving
            // symbolic applications no longer fence: slice 16's digit bridge
            // (below) encodes them.
```

Then at the final outcome match (~line 803), REPLACE:

```rust
            SolveResult::Unsat { .. } => SolveOutcome::Unsat,
```

with:

```rust
            SolveResult::Unsat { .. } => {
                // Slice 16: the digit bridge ASSERTED its bound (|u| <= K,
                // n < 10^K), so Unsat under the under-approximation does not
                // entail unbounded Unsat — demote to a sound Unknown. Only
                // the string path can set the flag (routing is exclusive).
                if int_conv_bridged {
                    SolveOutcome::Unknown
                } else {
                    SolveOutcome::Unsat
                }
            }
```

- [ ] **Step 4: Run the targeted tests to verify they pass**

Run: `cargo test -p shinri-solver --test qfs_differential targeted_`
Expected: ALL targeted tests PASS — the two new digit-bridge tests AND every pre-existing targeted pin (fold, roundtrip, predicates, indexof/replace, replace_all, substr, fences). If `targeted_digit_bridge_decided` returns Unknown on a Sat pin, the engine failed to solve the encoding (fuel/budget) — STOP and escalate (plan deviation), do not weaken the pin.

- [ ] **Step 5: Run the full per-crate suites**

Run: `cargo test -p shinri-str -p shinri-solver`
Expected: all PASS. The five existing string oracle families must be unperturbed (they generate symbolic to_int/from_int args only in `qfs_to_from_int_matches_z3`, whose symbolic instances were Unknown-tolerated before and are now decided-or-demoted — both tolerated; verdict DISAGREEMENTS are the failure signal).

- [ ] **Step 6: Format and commit**

```bash
cargo fmt
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "feat(str): wire digit bridge + unsat demotion, canary flips + e2e pins (slice 16)"
```

---

### Task 4: Differential oracle family `qfs_digit_bridge_matches_z3`

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (Gen impl ~line 500, gen fns ~line 580, family tests after `qfs_to_from_int_matches_z3` ~line 1145)

**Interfaces:**
- Consumes: existing harness pieces in the same file — `Gen::new`, `Gen::var()`, `Gen::lit()`, `Gen::digit_lit()`, `Gen::small_int_rhs()`, `Gen::assertion()`, `Lcg`, `Verdict`, `N_VARS`, `shinri_lines_counting_bailouts`, `z3_verdict`, `z3_with_model`, `parse_string_values`.
- Produces: the 0-disagreement gate for the slice; Task 5 records its tally in the spec.

- [ ] **Step 1: Add the generator methods**

In `impl Gen`, after `finish_to_from_int`:

```rust
    /// One digit-bridge assertion (slice 16): SYMBOLIC to_int/from_int
    /// arguments dominate (bridged path), with fold-path literal arguments
    /// mixed in — bridged instances can never yield Unsat (the demotion turns
    /// in-bound Unsat into Unknown), so the family's unsat coverage comes
    /// from the fold shapes. MAY be negated (definitions are polarity-free).
    fn digit_bridge_assertion(&mut self) {
        let atom = match self.rng.below(5) {
            // to_int(arg) = small k; arg mixes var (bridge) / literals (fold).
            0 => {
                let arg = self.to_int_arg();
                let k = self.small_int_rhs();
                format!("(= (str.to_int {arg}) {k})")
            }
            // to_int(var) = n0 : bridged, cross String↔Int.
            1 => format!("(= (str.to_int {}) n0)", self.var()),
            // from_int(n0) = digit/letter literal : bridged.
            2 => {
                let target = if self.rng.below(2) == 0 {
                    self.digit_lit()
                } else {
                    self.lit()
                };
                format!("(= (str.from_int n0) {target})")
            }
            // from_int(n0) = var : bridged, fully symbolic.
            3 => format!("(= (str.from_int n0) {})", self.var()),
            // Length pin straddling INT_CONV_DIGIT_CAP (= 8): lengths 6..=10
            // exercise both the decidable in-bound cases and the asserted-
            // bound conflict (in-bound unsat → demoted Unknown, tolerated).
            _ => {
                let l = 6 + self.rng.below(5);
                let v = self.var();
                self.body.push_str(&format!("(assert (= (str.len {v}) {l}))\n"));
                let k = self.small_int_rhs();
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

    /// Instance body for the slice-16 family: shared string vars, an Int var
    /// `n0`, 1–2 digit-bridge assertions, 0–1 general assertions for
    /// cross-theory mixing (so the SAT witness path references string vars).
    fn finish_digit_bridge(mut self) -> String {
        self.body.push_str("(declare-fun n0 () Int)\n");
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.digit_bridge_assertion();
        }
        if self.rng.below(2) == 0 {
            self.assertion();
        }
        self.body
    }
```

Next to the other `gen_*_body` functions:

```rust
fn gen_digit_bridge_body(seed: u64) -> String {
    Gen::new(seed).finish_digit_bridge()
}
```

- [ ] **Step 2: Add the family test**

After `qfs_to_from_int_matches_z3`, copying its harness exactly (unknown-tolerant, witness-checking, guard-bailout-counting) with `DB_` constants, the fresh seed, and `gen_digit_bridge_body`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Digit-bridge differential oracle (slice 16): symbolic to_int/from_int are
// now DECIDED (bounded under-approximation). Sat must agree with z3 (an
// unsound encoding surfaces as shinri-Sat/z3-Unsat); bridged Unsat is demoted
// to Unknown (tolerated, counted). Unsat coverage comes from fold-path
// literal shapes mixed into the generator. Fresh seed — never perturb
// existing families' seeds.
// ─────────────────────────────────────────────────────────────────────────────

const DB_N_ITERS: usize = 200;
const DB_MAX_GUARD_BAILOUTS: usize = DB_N_ITERS / 10;

#[test]
fn qfs_digit_bridge_matches_z3() {
    let mut rng = Lcg(0x51_60_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness, mut n_guard_bailout) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..DB_N_ITERS {
        let seed = rng.next();
        let body = gen_digit_bridge_body(seed);

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
            "QF_S DIGIT-BRIDGE SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
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
        "qfs_digit_bridge_matches_z3: {DB_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown / \
         {n_guard_bailout} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "digit-bridge family produced zero SAT instances");
    assert!(
        n_unsat > 0,
        "digit-bridge family produced zero UNSAT instances (fold shapes missing?)"
    );
    assert!(
        n_witness > 0,
        "no witnesses checked — model path not exercised"
    );
    assert!(
        n_guard_bailout <= DB_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailout} exceed bound {DB_MAX_GUARD_BAILOUTS}"
    );
}
```

- [ ] **Step 3: Run the new family**

Run: `cargo test -p shinri-solver --test qfs_differential qfs_digit_bridge_matches_z3 -- --nocapture`
Expected: PASS with 0 disagreements and non-zero sat/unsat/witness counts. Record the printed tally — Task 5 writes it into the spec. A DISAGREEMENT or WITNESS FAILURE is an encoding soundness bug: STOP, minimize the printed reproducer, fix in `int_conv.rs`, and add the minimized case as a targeted pin before rerunning.

- [ ] **Step 4: Re-run all string families unperturbed**

Run: `cargo test -p shinri-solver --test qfs_differential -- --nocapture`
Expected: all families PASS; the pre-slice-16 families print tallies consistent with their committed values (`qfs_to_from_int_matches_z3`'s unknown count may DROP — its symbolic instances are now decided or demoted, both tolerated; disagreements remain the only failure).

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_digit_bridge_matches_z3 differential oracle family (slice 16)"
```

---

### Task 5: Full verification, spec truth-up, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-07-11-shinri-slice16-digit-bridge-design.md` (Status header)

**Interfaces:**
- Consumes: Task 4's printed oracle tally.
- Produces: the merged slice.

- [ ] **Step 1: Full per-crate verification**

```bash
cargo fmt --check
cargo test -p shinri-str -p shinri-solver
```

Expected: fmt clean; all tests PASS. (The ~50-min `--workspace` run is CI's job.)

- [ ] **Step 2: Spec truth-up**

In the spec, change `Status: APPROVED (design), not yet implemented.` to `Status: IMPLEMENTED (slice 16 landed <date>).` and add, below it, the oracle tally paragraph (slice-15 format): family name, seed, iters, sat/unsat/unknown/z3-unknown/guard-bailout/witness counts, `**0 disagreements**`, plus a line confirming the pre-existing families re-ran unperturbed. Record any plan deviations as a numbered **Deviations from the plan** list (or "none").

- [ ] **Step 3: Commit and open the PR**

```bash
git add docs/superpowers/specs/2026-07-11-shinri-slice16-digit-bridge-design.md
git commit -m "docs: slice-16 spec truth-up — IMPLEMENTED + oracle tally"
git push -u origin slice16-digit-bridge
gh pr create --title "Slice 16: bounded digit bridge for symbolic str.to_int/from_int" \
  --body "Replaces the slice-15 int_conv fence with a bounded under-approximate encoding (spec: docs/superpowers/specs/2026-07-11-shinri-slice16-digit-bridge-design.md). Sat decided; bridged Unsat demoted to Unknown. New oracle family qfs_digit_bridge_matches_z3: 0 disagreements @ 200 iters."
```

Expected: PR opens; CI (fmt gate + full workspace tests + differential families) goes green before merge.
