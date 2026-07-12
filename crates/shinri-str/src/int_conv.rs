//! Slice 15 + 17 pre-pass: `str.to_int` / `str.from_int` — fold + exact roundtrip
//! rewrite + fence.
//!
//! Both ops are value-sorted FUNCTIONS (Int / String), so — like the slice-13
//! indexof/replace ops — the rewrites are exact at any position and polarity;
//! zero fresh variables are introduced here (the only fresh var is the `!ite`
//! that `reduce_assertions`' `elim_term_ite` mints for the roundtrip below).
//!
//! Stages (run by the solver's string-path seam):
//! 1. [`partial_eval_int_conv`] — bottom-up memoized rewrite:
//!    - fold `str.to_int(<lit>)` / `str.from_int(<numeral>)` to a literal;
//!    - rewrite `str.to_int(str.from_int(n))` → `ite(n >= 0, n, -1)` (exact).
//! 2. [`decide_const_int_conv`] (slice 17) — constant-RHS decision: rewrite
//!    `str.from_int(n) = "lit"` to its exact Int equivalent and
//!    `str.to_int(s) = k` to `false` for `k <= -2` (any polarity, exact);
//!    expand `str.to_int(s) = k` under a top-level length pin (R4, capped by
//!    [`INT_CONV_PIN_LEN_CAP`]); witness-rewrite lone-occurrence
//!    `str.to_int(s) = k` atoms to `s = dec(k)` / `s = ""` with a
//!    model-repair obligation ([`IntConvRepair`], R2). Both verdicts
//!    preserved exactly — no bound, no demotion (unlike the closed slice 16).
//! 3. [`has_unreduced_int_conv`] — presence fence: any surviving application
//!    (symbolic string to `to_int`; symbolic non-roundtrip Int to `from_int`)
//!    fences the query to a sound `Unknown`.
//!
//! Strings are handled as code points; digit classification is EXACTLY
//! `char::is_ascii_digit()` (`'0'..='9'`) — never `char::is_numeric()`, which
//! would unsoundly fold non-ASCII Unicode digits.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, TermId, TermNode};

/// Concrete `str.to_int(s)` per SMT-LIB 2.6: the value of `s` iff it is a
/// non-empty run of ASCII digits (leading zeros allowed); otherwise `-1`.
fn eval_to_int(s: &str) -> Integer {
    if s.is_empty() || !s.chars().all(|c| c.is_ascii_digit()) {
        return Integer::from(-1i128);
    }
    Integer::from_str_radix(s, 10).expect("validated ASCII-digit run parses")
}

/// Concrete `str.from_int(n)` per SMT-LIB 2.6: canonical decimal for `n >= 0`
/// (no leading zeros, `0 -> "0"`); the empty string for `n < 0`.
fn eval_from_int(n: &Integer) -> String {
    if n.signum() < 0 {
        String::new()
    } else {
        n.to_string()
    }
}

/// Stage 1: bottom-up memoized rewrite. Folds fully-literal applications and
/// rewrites the roundtrip `str.to_int(str.from_int(n))` → `ite(n >= 0, n, -1)`.
/// Untouched subtrees keep their TermIds.
pub fn partial_eval_int_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect()
}

fn rewrite(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> =
                children.iter().map(|&c| rewrite(ctx, c, memo)).collect();
            let special = match op {
                Op::Builtin(BuiltinOp::StrToInt) => rewrite_to_int(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrFromInt) => rewrite_from_int(ctx, &new_children),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(n, o)| n != o);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("rewrite: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// `(str.to_int x)`, child already rewritten. Folds a literal argument and
/// rewrites the roundtrip `str.to_int(str.from_int(n))` → `ite(n >= 0, n, -1)`.
/// None leaves the app in place (-> fence).
fn rewrite_to_int(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    if let Some(s) = ctx.string_const_value(kids[0]).map(str::to_owned) {
        let int_s = ctx.int_sort();
        return Some(ctx.mk_numeral(Rational::from_int(eval_to_int(&s)), int_s));
    }
    // Exact roundtrip: str.to_int(str.from_int(n)) = ite(n >= 0, n, -1).
    // For n >= 0, from_int yields canonical digits recovered exactly; for n < 0,
    // from_int = "" and to_int("") = -1. Polarity-free, exact.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrFromInt),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let n = ctx.children(args)[0];
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::from(0i128)), int_s);
        let neg1 = ctx.mk_numeral(Rational::from_int(Integer::from(-1i128)), int_s);
        let ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero])
            .expect("n >= 0");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[ge, n, neg1])
                .expect("roundtrip ite"),
        );
    }
    None
}

/// `(str.from_int x)`, child already rewritten. Folds a numeral argument.
/// None (symbolic Int) leaves the app in place (-> fence).
/// Uses `Context::const_real_value` (the single source of truth for literal
/// recognition shared with the FP to_fp fence) to identify numeral literals and
/// handle nested negations consistently.
fn rewrite_from_int(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let r = ctx.const_real_value(kids[0])?;
    Some(ctx.mk_string_const(&eval_from_int(&r.numer())))
}

/// Stage 2: presence fence. True iff any `str.to_int` / `str.from_int`
/// application SURVIVED [`partial_eval_int_conv`].
pub fn has_unreduced_int_conv(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrToInt | BuiltinOp::StrFromInt))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

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

/// Integer value of an Int-sorted literal — numeral or the parser's
/// Neg-wrapped `(- 5)` shape — via the cross-crate `const_real_value`
/// (single source of truth for literal recognition). None for non-literals
/// and non-integral rationals.
pub(crate) fn int_const_value(ctx: &Context, t: TermId) -> Option<Integer> {
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
            return Some(
                ctx.mk_eq(s, w)
                    .expect("const int-conv: well-sorted s = padded"),
            );
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
}

#[cfg(test)]
mod tests {
    use super::*; // brings in Integer, Rational, BuiltinOp, Context, Op, TermId, TermNode

    /// A nullary uninterpreted constant of the given sort (codebase pattern —
    /// there is no `mk_const`).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn eval_to_int_pinned_semantics() {
        assert_eq!(eval_to_int("0"), Integer::from(0i128));
        assert_eq!(eval_to_int("007"), Integer::from(7i128)); // leading zeros ok
        assert_eq!(eval_to_int("42"), Integer::from(42i128));
        assert_eq!(eval_to_int(""), Integer::from(-1i128)); // empty
        assert_eq!(eval_to_int("12a"), Integer::from(-1i128)); // non-digit
        assert_eq!(eval_to_int("-5"), Integer::from(-1i128)); // sign char
        assert_eq!(eval_to_int("+5"), Integer::from(-1i128));
        assert_eq!(eval_to_int(" 5"), Integer::from(-1i128)); // whitespace
                                                              // NON-ASCII digit trap: must be -1, NOT 3.
        assert_eq!(eval_to_int("\u{0663}"), Integer::from(-1i128)); // Arabic-Indic ٣
        assert_eq!(eval_to_int("\u{FF13}"), Integer::from(-1i128)); // fullwidth ３
                                                                    // Big int (no i128 overflow): 40-digit roundtrip.
        let big = "1234567890123456789012345678901234567890";
        assert_eq!(eval_to_int(big).to_string(), big);
    }

    #[test]
    fn eval_from_int_pinned_semantics() {
        assert_eq!(eval_from_int(&Integer::from(0i128)), "0");
        assert_eq!(eval_from_int(&Integer::from(42i128)), "42");
        assert_eq!(eval_from_int(&Integer::from(-1i128)), ""); // negative -> ""
        assert_eq!(eval_from_int(&Integer::from(-5i128)), "");
    }

    fn to_int(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s]).unwrap()
    }
    fn from_int(ctx: &mut Context, n: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[n])
            .unwrap()
    }

    #[test]
    fn fold_literal_applications() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        // str.to_int("42") folds to the numeral 42.
        let lit = ctx.mk_string_const("42");
        let app = to_int(&mut ctx, lit);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(
            ctx.numeral_value(out[0]).map(|r| r.numer().to_string()),
            Some("42".to_string())
        );
        // str.from_int(-5) folds to "".
        let neg = ctx.mk_numeral(Rational::from_int(Integer::from(-5i128)), int_s);
        let app = from_int(&mut ctx, neg);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(ctx.string_const_value(out[0]), Some(""));
        // No survivor -> not fenced.
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn fold_from_int_of_neg_wrapped_numeral_literal() {
        // The SMT-LIB parser spells negative integer literals as `(- 5)` —
        // `BuiltinOp::Neg` applied to a numeral, NOT a single `Const` numeral
        // (see `Context::const_real_value` in shinri-core's context.rs). This is the shape `str.from_int`
        // actually sees from parsed input for its spec-mandated negative case;
        // it must fold exactly like a directly-built negative `mk_numeral`.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let neg_five = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[five]).unwrap();
        let app = from_int(&mut ctx, neg_five);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(ctx.string_const_value(out[0]), Some(""));
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn fold_from_int_of_nested_neg_wrapped_numeral_literal() {
        // Consolidation to `Context::const_real_value` enables recursion:
        // `(- (- 5))` now folds to "5". This pins the capability gained by
        // using the cross-crate shared literal-recognition helper.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let neg_five = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[five]).unwrap();
        let neg_neg_five = ctx
            .mk_app(Op::Builtin(BuiltinOp::Neg), &[neg_five])
            .unwrap();
        let app = from_int(&mut ctx, neg_neg_five);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(ctx.string_const_value(out[0]), Some("5"));
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn symbolic_application_survives_to_fence() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s); // symbolic string
        let app = to_int(&mut ctx, s);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert!(
            has_unreduced_int_conv(&ctx, &out),
            "symbolic to_int must fence"
        );
    }

    #[test]
    fn roundtrip_to_int_of_from_int_rewrites_to_ite() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s); // symbolic Int (helper from Task 3)
        let inner = from_int(&mut ctx, n);
        let app = to_int(&mut ctx, inner);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        // Neither str op survives -> not fenced.
        assert!(
            !has_unreduced_int_conv(&ctx, &out),
            "roundtrip must fully eliminate both ops"
        );
        // Top node is an Int-sorted ite.
        match ctx.term_node(out[0]) {
            TermNode::App { op, .. } => {
                assert_eq!(*op, Op::Builtin(BuiltinOp::Ite), "expected ite, got {op:?}");
            }
            other => panic!("expected ite app, got {other:?}"),
        }
        assert_eq!(ctx.sort_of(out[0]), int_s);
    }

    #[test]
    fn nested_literal_roundtrip_folds_through() {
        // str.to_int(str.from_int(42)) : from_int folds to "42", then to_int folds to 42.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let k = ctx.mk_numeral(Rational::from_int(Integer::from(42i128)), int_s);
        let inner = from_int(&mut ctx, k); // split: avoid double &mut ctx in one expr
        let app = to_int(&mut ctx, inner);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(
            ctx.numeral_value(out[0]).map(|r| r.numer().to_string()),
            Some("42".to_string())
        );
    }

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
        let expected = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero]).unwrap();
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

    /// Builds `(= (str.len s) l)` for pin tests.
    fn len_pin(ctx: &mut Context, s: TermId, l: i128) -> TermId {
        let int_s = ctx.int_sort();
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
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
        assert!(
            repairs.is_empty(),
            "pin expansion is an equivalence: no repair"
        );
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn pin_expansion_edges() {
        // k = 0, L = 3 → "000"; |dec(k)| = L → no padding; |dec(k)| > L → false.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let str_s = ctx.string_sort();
        let f = ctx.mk_const_bool(false);
        for (k, l, want) in [
            (0i128, 3i128, Some("000")),
            (123, 3, Some("123")),
            (1234, 3, None),
        ] {
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
}
