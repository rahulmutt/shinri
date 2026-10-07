//! Slice 59: classify a model the string witness gate rejected
//! (`str-model-rejected`) into a stable detail tag `<mode>:<kind>@<rebuild>`
//! (spec §4.1). Diagnostics only: it runs after the gate has already
//! rejected and never decides a verdict.

use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Op, TermId, TermNode};
use shinri_theory::RebuildOutcome;

use crate::model::Model;
use crate::Solver;

impl Solver {
    /// The detail tag for a model that `string_model_satisfies(assertions,
    /// model, strict)` rejected: the first failing assertion in order
    /// decides the mode and kind (spec §4.1). `unclassified:none` only if
    /// nothing fails, which the gate's own rejection rules out.
    pub(crate) fn model_reject_detail(
        &self,
        assertions: &[TermId],
        model: &Model,
        strict: bool,
        rebuild: RebuildOutcome,
    ) -> String {
        let (mode, kind) = self
            .first_failure(assertions, model, strict)
            .unwrap_or(("unclassified", "none".to_owned()));
        format!("{mode}:{kind}@{}", rebuild.as_str())
    }

    /// Mirror of `string_model_satisfies`: the first assertion that is
    /// definitely false, or (strict gate only) undecided.
    fn first_failure(
        &self,
        assertions: &[TermId],
        model: &Model,
        strict: bool,
    ) -> Option<(&'static str, String)> {
        for &a in assertions {
            match self.eval_bool(a, model) {
                Some(true) => {}
                Some(false) => {
                    let (atom, neg) = self.strip_not(a);
                    return Some(("violated", polarised(neg, self.kind_of(atom))));
                }
                None if strict => {
                    let (leaf, neg) = self.first_none_leaf(a, false, model);
                    return Some(("unevaluable", polarised(neg, self.kind_of(leaf))));
                }
                None => {}
            }
        }
        None
    }

    /// Strip outer `not`s, returning the atom and whether an odd number was
    /// stripped.
    fn strip_not(&self, mut t: TermId) -> (TermId, bool) {
        let mut neg = false;
        while let TermNode::App {
            op: Op::Builtin(BuiltinOp::Not),
            args,
            ..
        } = self.ctx.term_node(t)
        {
            let kids = self.ctx.children(*args);
            if kids.len() != 1 {
                break;
            }
            t = kids[0];
            neg = !neg;
        }
        (t, neg)
    }

    /// `t` evaluates to `None`. Descend its Boolean skeleton to the first
    /// child (left to right; for `ite`, the condition or the chosen branch)
    /// that is also undecided; the first non-connective reached is the leaf
    /// the evaluator cannot decide. `neg` tracks `not`s on the way down.
    fn first_none_leaf(&self, t: TermId, neg: bool, model: &Model) -> (TermId, bool) {
        let TermNode::App {
            op: Op::Builtin(b),
            args,
            ..
        } = self.ctx.term_node(t)
        else {
            return (t, neg);
        };
        let b = *b;
        let kids = self.ctx.children(*args).to_vec();
        let bool_sort = self.ctx.bool_sort();
        let connective = match b {
            BuiltinOp::Not
            | BuiltinOp::And
            | BuiltinOp::Or
            | BuiltinOp::Implies
            | BuiltinOp::Xor => true,
            BuiltinOp::Ite => kids.len() == 3,
            BuiltinOp::Eq | BuiltinOp::Distinct => kids
                .first()
                .is_some_and(|&k| self.ctx.sort_of(k) == bool_sort),
            _ => false,
        };
        if !connective {
            return (t, neg);
        }
        let candidates: Vec<TermId> = if b == BuiltinOp::Ite {
            match self.eval_bool(kids[0], model) {
                None => vec![kids[0]],
                Some(true) => vec![kids[1]],
                Some(false) => vec![kids[2]],
            }
        } else {
            kids
        };
        let child_neg = if b == BuiltinOp::Not { !neg } else { neg };
        for k in candidates {
            if self.eval_bool(k, model).is_none() {
                return self.first_none_leaf(k, child_neg, model);
            }
        }
        (t, neg)
    }

    /// The §4.1 kind of an atom (outer `not`s already stripped).
    fn kind_of(&self, atom: TermId) -> String {
        if self.mentions_int_conv(atom) {
            return "int-conv".to_owned();
        }
        let (op, kids) = match self.ctx.term_node(atom) {
            TermNode::App { op, args, .. } => (*op, self.ctx.children(*args)),
            _ => return "other:leaf".to_owned(),
        };
        let b = match op {
            Op::Builtin(b) => b,
            Op::Uninterpreted(_) => return "other:uf".to_owned(),
        };
        let sort0 = kids.first().map(|&k| self.ctx.sort_of(k));
        let string_s = Some(self.ctx.string_sort());
        let bool_s = Some(self.ctx.bool_sort());
        let numeric = sort0 == Some(self.ctx.int_sort()) || sort0 == Some(self.ctx.real_sort());
        let kind = match b {
            BuiltinOp::Eq if sort0 == string_s => "word-eq",
            BuiltinOp::Distinct if sort0 == string_s => "str-diseq",
            BuiltinOp::Eq | BuiltinOp::Distinct if sort0 == bool_s => "bool",
            BuiltinOp::Eq | BuiltinOp::Distinct if numeric => "len-arith",
            BuiltinOp::Le | BuiltinOp::Lt | BuiltinOp::Ge | BuiltinOp::Gt => "len-arith",
            BuiltinOp::StrInRe => "memb",
            BuiltinOp::StrContains | BuiltinOp::StrPrefixOf | BuiltinOp::StrSuffixOf => "str-pred",
            BuiltinOp::StrLt | BuiltinOp::StrLeq => "str-order",
            BuiltinOp::Not
            | BuiltinOp::And
            | BuiltinOp::Or
            | BuiltinOp::Implies
            | BuiltinOp::Xor
            | BuiltinOp::Ite => "bool",
            other => {
                return format!(
                    "other:{}",
                    tag_safe(&shinri_core::smtlib_print::builtin_name(other))
                )
            }
        };
        kind.to_owned()
    }

    /// Whether a string/int conversion occurs anywhere under `t`
    /// (visited-set walk: linear in the shared DAG).
    fn mentions_int_conv(&self, t: TermId) -> bool {
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut stack = vec![t];
        while let Some(u) = stack.pop() {
            if !seen.insert(u) {
                continue;
            }
            if let TermNode::App { op, args, .. } = self.ctx.term_node(u) {
                if matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::StrToInt
                            | BuiltinOp::StrFromInt
                            | BuiltinOp::StrToCode
                            | BuiltinOp::StrFromCode
                    )
                ) {
                    return true;
                }
                stack.extend_from_slice(self.ctx.children(*args));
            }
        }
        false
    }
}

fn polarised(neg: bool, kind: String) -> String {
    if neg {
        format!("not-{kind}")
    } else {
        kind
    }
}

/// A tag never contains whitespace: the `stats:` line is split on it.
fn tag_safe(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_whitespace() { '_' } else { c })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Rational;
    use shinri_theory::types::ModelVal;

    fn fx() -> (Solver, TermId, TermId) {
        let mut s = Solver::new();
        let ss = s.ctx_mut().string_sort();
        let xf = s.declare_fun("x", &[], ss);
        let x = s.app(Op::Uninterpreted(xf), &[]);
        let yf = s.declare_fun("y", &[], ss);
        let y = s.app(Op::Uninterpreted(yf), &[]);
        (s, x, y)
    }

    fn strs(pairs: &[(TermId, &str)]) -> Model {
        let mut m = Model::default();
        for &(t, v) in pairs {
            m.values.insert(t, ModelVal::String(v.to_owned()));
        }
        m
    }

    fn lit(s: &mut Solver, v: &str) -> TermId {
        s.ctx_mut().mk_string_const(v)
    }

    fn int(s: &mut Solver, n: i128) -> TermId {
        let is = s.ctx_mut().int_sort();
        s.ctx_mut().mk_numeral(Rational::from_int(n.into()), is)
    }

    fn b(s: &mut Solver, op: BuiltinOp, args: &[TermId]) -> TermId {
        s.app(Op::Builtin(op), args)
    }

    fn tag(s: &Solver, a: &[TermId], m: &Model, strict: bool) -> String {
        s.model_reject_detail(a, m, strict, RebuildOutcome::NotNeeded)
    }

    #[test]
    fn violated_word_eq() {
        let (mut s, x, _) = fx();
        let bb = lit(&mut s, "b");
        let a = s.eq(x, bb);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(a, &m), Some(false));
        assert_eq!(tag(&s, &[a], &m, false), "violated:word-eq@not-needed");
    }

    #[test]
    fn violated_str_diseq() {
        let (mut s, x, _) = fx();
        let la = lit(&mut s, "a");
        let d = b(&mut s, BuiltinOp::Distinct, &[x, la]);
        assert!(matches!(
            s.ctx().term_node(d),
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Distinct),
                ..
            }
        ));
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[d], &m, false), "violated:str-diseq@not-needed");
    }

    #[test]
    fn not_prefix_and_double_negation() {
        let (mut s, x, _) = fx();
        let la = lit(&mut s, "a");
        let e = s.eq(x, la);
        let ne = b(&mut s, BuiltinOp::Not, &[e]);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[ne], &m, false), "violated:not-word-eq@not-needed");
        let lb = lit(&mut s, "b");
        let e2 = s.eq(x, lb);
        let n1 = b(&mut s, BuiltinOp::Not, &[e2]);
        let n2 = b(&mut s, BuiltinOp::Not, &[n1]);
        assert_eq!(tag(&s, &[n2], &m, false), "violated:word-eq@not-needed");
    }

    #[test]
    fn violated_memb() {
        let (mut s, x, _) = fx();
        let lb = lit(&mut s, "b");
        let re = b(&mut s, BuiltinOp::StrToRe, &[lb]);
        let a = b(&mut s, BuiltinOp::StrInRe, &[x, re]);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(a, &m), Some(false));
        assert_eq!(tag(&s, &[a], &m, false), "violated:memb@not-needed");
    }

    #[test]
    fn violated_len_arith() {
        let (mut s, x, _) = fx();
        let len = b(&mut s, BuiltinOp::StrLen, &[x]);
        let two = int(&mut s, 2);
        let a = s.eq(len, two);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[a], &m, false), "violated:len-arith@not-needed");
    }

    #[test]
    fn violated_bool_skeleton() {
        let (mut s, x, _) = fx();
        let lb = lit(&mut s, "b");
        let lc = lit(&mut s, "c");
        let e1 = s.eq(x, lb);
        let e2 = s.eq(x, lc);
        let a = b(&mut s, BuiltinOp::Or, &[e1, e2]);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[a], &m, false), "violated:bool@not-needed");
    }

    #[test]
    fn unevaluable_str_pred_and_order() {
        let (mut s, x, y) = fx();
        let la = lit(&mut s, "a");
        let p = b(&mut s, BuiltinOp::StrPrefixOf, &[la, x]);
        let m = strs(&[(x, "a"), (y, "b")]);
        assert_eq!(s.eval_bool(p, &m), None);
        assert_eq!(
            s.model_reject_detail(&[p], &m, true, RebuildOutcome::Adopted),
            "unevaluable:str-pred@adopted"
        );
        let lt = b(&mut s, BuiltinOp::StrLt, &[x, y]);
        assert_eq!(tag(&s, &[lt], &m, true), "unevaluable:str-order@not-needed");
    }

    #[test]
    fn int_conv_wins_over_len_arith() {
        let (mut s, x, _) = fx();
        let ti = b(&mut s, BuiltinOp::StrToInt, &[x]);
        let five = int(&mut s, 5);
        let a = s.eq(ti, five);
        let m = strs(&[(x, "5")]);
        assert_eq!(s.eval_bool(a, &m), None);
        assert_eq!(tag(&s, &[a], &m, true), "unevaluable:int-conv@not-needed");
    }

    /// Slice 62: compound length arithmetic is folded from its operands even
    /// when the arith model never valued the compound term.
    #[test]
    fn compound_len_arith_evaluates_from_operands() {
        let (mut s, x, _) = fx();
        let len = b(&mut s, BuiltinOp::StrLen, &[x]);
        let one = int(&mut s, 1);
        let sum = b(&mut s, BuiltinOp::Add, &[len, one]);
        let two = int(&mut s, 2);
        let three = int(&mut s, 3);
        let holds = s.eq(sum, two);
        let fails = s.eq(sum, three);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(holds, &m), Some(true));
        assert_eq!(s.eval_bool(fails, &m), Some(false));
    }

    /// An operand with no value keeps the term unevaluable.
    #[test]
    fn unevaluable_compound_len_arith() {
        let (mut s, x, _) = fx();
        let len = b(&mut s, BuiltinOp::StrLen, &[x]);
        let is = s.ctx_mut().int_sort();
        let nf = s.declare_fun("n", &[], is);
        let n = s.app(Op::Uninterpreted(nf), &[]);
        let sum = b(&mut s, BuiltinOp::Add, &[len, n]);
        let two = int(&mut s, 2);
        let a = s.eq(sum, two);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(a, &m), None);
        assert_eq!(tag(&s, &[a], &m, true), "unevaluable:len-arith@not-needed");
    }

    /// Slice 62 (item 5): `len x + len y = 3` under `x = y = ""`, with no
    /// arith value for the sum, is a violation the non-strict gate sees.
    #[test]
    fn unvalued_sum_of_lengths_is_violated() {
        let (mut s, x, y) = fx();
        let lx = b(&mut s, BuiltinOp::StrLen, &[x]);
        let ly = b(&mut s, BuiltinOp::StrLen, &[y]);
        let sum = b(&mut s, BuiltinOp::Add, &[lx, ly]);
        let three = int(&mut s, 3);
        let a = s.eq(sum, three);
        let m = strs(&[(x, ""), (y, "")]);
        assert_eq!(s.eval_bool(a, &m), Some(false));
        assert!(!s.string_model_satisfies(&[a], &m, false));
    }

    /// `(= (f (str.len x)) 1)` with the model's `f(len x) = 1` built at a
    /// stale `len x = 3`, while `x = ""`.
    fn stale_uf_arg(len_val: i128, x_val: &str) -> (Solver, TermId, Model) {
        let (mut s, x, _) = fx();
        let len = b(&mut s, BuiltinOp::StrLen, &[x]);
        let is = s.ctx_mut().int_sort();
        let ff = s.declare_fun("f", &[is], is);
        let fl = s.app(Op::Uninterpreted(ff), &[len]);
        let one = int(&mut s, 1);
        let a = s.eq(fl, one);
        let mut m = strs(&[(x, x_val)]);
        m.values
            .insert(len, ModelVal::Num(Rational::from_int(len_val.into())));
        m.values
            .insert(fl, ModelVal::Num(Rational::from_int(1i128.into())));
        (s, a, m)
    }

    /// Slice 62 backstop: a UF application whose argument now evaluates to a
    /// different value than the model's interpretation was built at is
    /// unevaluable, so the strict gate cannot confirm it from the stale value.
    #[test]
    fn uf_app_with_stale_argument_is_unevaluable() {
        let (s, a, m) = stale_uf_arg(3, "");
        assert_eq!(s.eval_bool(a, &m), None);
        assert!(!s.string_model_satisfies(&[a], &m, true));
        assert_eq!(tag(&s, &[a], &m, true), "unevaluable:len-arith@not-needed");
    }

    /// An argument consistent with the model keeps the model's value.
    #[test]
    fn uf_app_with_consistent_argument_keeps_model_value() {
        let (s, a, m) = stale_uf_arg(0, "");
        assert_eq!(s.eval_bool(a, &m), Some(true));
        assert!(s.string_model_satisfies(&[a], &m, true));
    }

    #[test]
    fn unevaluable_descends_to_the_first_undecided_leaf() {
        let (mut s, x, _) = fx();
        let la = lit(&mut s, "a");
        let lb = lit(&mut s, "b");
        let e = s.eq(x, lb); // false under x = "a"
        let p = b(&mut s, BuiltinOp::StrPrefixOf, &[la, x]); // undecided
        let or1 = b(&mut s, BuiltinOp::Or, &[e, p]);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[or1], &m, true), "unevaluable:str-pred@not-needed");
        let np = b(&mut s, BuiltinOp::Not, &[p]);
        let or2 = b(&mut s, BuiltinOp::Or, &[e, np]);
        assert_eq!(
            tag(&s, &[or2], &m, true),
            "unevaluable:not-str-pred@not-needed"
        );
        // ite: the condition is true, so the undecided leaf is the then-branch.
        let ea = s.eq(x, la);
        let sfx = b(&mut s, BuiltinOp::StrSuffixOf, &[la, x]);
        let ite = b(&mut s, BuiltinOp::Ite, &[ea, sfx, e]);
        assert_eq!(tag(&s, &[ite], &m, true), "unevaluable:str-pred@not-needed");
    }

    #[test]
    fn the_first_failing_assertion_decides() {
        let (mut s, x, y) = fx();
        let lb = lit(&mut s, "b");
        let e = s.eq(x, lb);
        let lt = b(&mut s, BuiltinOp::StrLt, &[x, y]);
        let m = strs(&[(x, "a"), (y, "c")]);
        assert_eq!(
            tag(&s, &[lt, e], &m, true),
            "unevaluable:str-order@not-needed"
        );
        assert_eq!(tag(&s, &[e, lt], &m, true), "violated:word-eq@not-needed");
        // Without the strict gate an undecided assertion is not a failure.
        assert_eq!(tag(&s, &[lt, e], &m, false), "violated:word-eq@not-needed");
    }

    #[test]
    fn uninterpreted_bool_constant_is_other_uf() {
        let (mut s, x, _) = fx();
        let bs = s.ctx_mut().bool_sort();
        let pf = s.declare_fun("p", &[], bs);
        let p = s.app(Op::Uninterpreted(pf), &[]);
        let m = strs(&[(x, "a")]);
        assert_eq!(tag(&s, &[p], &m, true), "unevaluable:other:uf@not-needed");
    }

    /// A Boolean builtin outside the §4.1 list is tagged `other:<op>` through
    /// `builtin_name` + `tag_safe`. No indexed Boolean builtin exists (every
    /// `(_ …)` op is BV-, regex- or FP-valued), so `bvult` stands in.
    #[test]
    fn unlisted_builtin_is_other_op() {
        let (mut s, x, _) = fx();
        let c1 = s.ctx_mut().mk_bv_const(8, shinri_core::Integer::from(1u64));
        let c2 = s.ctx_mut().mk_bv_const(8, shinri_core::Integer::from(2u64));
        let a = b(&mut s, BuiltinOp::BvUlt, &[c1, c2]);
        let m = strs(&[(x, "a")]);
        assert_eq!(s.eval_bool(a, &m), None);
        assert_eq!(
            tag(&s, &[a], &m, true),
            "unevaluable:other:bvult@not-needed"
        );
    }

    #[test]
    fn rebuild_suffix_and_unclassified_fallback() {
        let (s, x, _) = fx();
        let m = strs(&[(x, "a")]);
        assert_eq!(
            s.model_reject_detail(&[], &m, true, RebuildOutcome::Budget),
            "unclassified:none@budget"
        );
    }

    #[test]
    fn tag_safe_replaces_whitespace() {
        assert_eq!(tag_safe("(_ extract 7 0)"), "(__extract_7_0)");
        assert_eq!(tag_safe("str.in_re"), "str.in_re");
    }

    /// Review Focus 3: a 60-level shared `str.++` doubling. A tree walk would
    /// visit 2^60 nodes; the visited-set walk visits 61.
    #[test]
    fn shared_dag_classifies_in_linear_time() {
        let (mut s, x, _) = fx();
        let mut t = x;
        for _ in 0..60 {
            t = b(&mut s, BuiltinOp::StrConcat, &[t, t]);
        }
        let len = b(&mut s, BuiltinOp::StrLen, &[t]);
        let zero = int(&mut s, 0);
        let a = s.eq(len, zero);
        let m = Model::default(); // x unvalued: eval stops at the first leaf
        let t0 = std::time::Instant::now();
        assert_eq!(tag(&s, &[a], &m, true), "unevaluable:len-arith@not-needed");
        assert!(t0.elapsed().as_secs() < 2, "{:?}", t0.elapsed());
    }
}
