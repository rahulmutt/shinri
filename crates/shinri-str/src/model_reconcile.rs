//! Slice 57: reconciliation rebuild of the string model.
//!
//! The default builder (`model::string_values`) values a variable from the
//! FIRST concat in its class. When the word-equation search leaves a class
//! holding several concats (an input equation's side next to a minted
//! char-peel/F-split side), or a cycle through a minted concat, that choice can
//! violate an input equation, and the solver's model gate rejects the model
//! (`str-model-rejected`). This rebuild prefers input concats, length-checks
//! every candidate against the arith model, and rolls back a rejected
//! candidate's values. `StrSolver::model_with` adopts its result only if every
//! input equation holds, and then sets `ModelBuilder::require_strict_check`.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::ModelVal;
use shinri_theory::{EqualityEngine, ModelBuilder};

use crate::model::{class_member, concat_arity, const_word_of, free_fill, is_concat};

/// What the rebuild reads besides the term context, EUF and the arith model.
pub(crate) struct ReconcileInput<'a> {
    /// Every string term visible to the solver (as for `model::string_values`).
    pub known: &'a [TermId],
    /// The terms to value, in output order.
    pub str_terms: &'a [TermId],
    /// Membership seeds for free leaves (`model::memb_seeds`).
    pub seeds: &'a FxHashMap<TermId, String>,
    /// Both sides of every asserted input (non-minted) string equality.
    pub input_sides: &'a FxHashSet<TermId>,
    /// Both sides of every asserted minted string equality.
    pub minted_sides: &'a FxHashSet<TermId>,
}

/// Rebuild the string valuation (spec §4.2): `(term, value)` for every term of
/// `str_terms` that `m` does not already hold a string for, in `str_terms`
/// order. Starts from a fresh memo seeded only with the membership seeds.
pub(crate) fn reconciled_values(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    m: &ModelBuilder,
    inp: &ReconcileInput<'_>,
) -> Vec<(TermId, String)> {
    let mut r = Reconciler {
        terms,
        eq,
        m,
        inp,
        memo: inp.seeds.clone(),
        in_progress: FxHashSet::default(),
    };
    // Input-equation concats first, longest first, so a top-level concat sets
    // its operands' values before they are valued on their own.
    let mut firsts: Vec<TermId> = inp
        .input_sides
        .iter()
        .copied()
        .filter(|&t| is_concat(r.terms, t))
        .collect();
    firsts.sort_by_key(|&t| (std::cmp::Reverse(concat_arity(r.terms, t)), t.index()));
    for t in firsts {
        let _ = r.value(t);
    }
    let mut out = Vec::new();
    for &t in inp.str_terms {
        if matches!(m.get(t), Some(ModelVal::String(_))) {
            continue;
        }
        let v = r.value(t);
        out.push((t, v));
    }
    out
}

struct Reconciler<'a, 'b> {
    terms: &'a mut Context,
    eq: &'a mut EqualityEngine,
    m: &'a ModelBuilder,
    inp: &'a ReconcileInput<'b>,
    memo: FxHashMap<TermId, String>,
    in_progress: FxHashSet<TermId>,
}

impl Reconciler<'_, '_> {
    fn value(&mut self, t: TermId) -> String {
        if let Some(v) = self.memo.get(&t) {
            return v.clone();
        }
        if let Some(v) = self.terms.string_const_value(t) {
            let v = v.to_owned();
            self.memo.insert(t, v.clone());
            return v;
        }
        if !self.in_progress.insert(t) {
            // Re-entry: a cycle such as `x ≈ s ++ "c"`, `s ≈ x ++ k` (minted).
            // A free fill of the class length, NOT memoised, so the enclosing
            // candidate is judged on its own length and rolled back if wrong.
            let n = self.class_len(t).unwrap_or(0);
            return free_fill(self.eq, t, n);
        }
        let out = if is_concat(self.terms, t) {
            self.value_concat(t)
        } else {
            self.value_var(t)
        };
        self.in_progress.remove(&t);
        self.memo.insert(t, out.clone());
        out
    }

    /// A class constant wins; otherwise the first candidate concat whose word
    /// has the class length (rule 2), with a rejected candidate's memo entries
    /// rolled back; otherwise a free fill of the class length.
    fn value_var(&mut self, t: TermId) -> String {
        let known = self.inp.known;
        if let Some(c) = class_member(self.terms, self.eq, known, t, |terms, mm| {
            terms.string_const_value(mm).is_some() && mm != t
        }) {
            return self
                .terms
                .string_const_value(c)
                .expect("class constant")
                .to_owned();
        }
        let n = self.class_len(t);
        for k in self.candidates(t) {
            let saved = self.memo.clone();
            let v = self.value(k);
            if n.is_none_or(|n| v.chars().count() == n) {
                return v;
            }
            self.memo = saved;
        }
        free_fill(self.eq, t, n.unwrap_or(0))
    }

    /// Concats in `t`'s class other than `t` (rule 1): input-equation sides
    /// first, then other non-minted concats, then minted sides; longer first,
    /// then by term id for determinism.
    fn candidates(&mut self, t: TermId) -> Vec<TermId> {
        let known = self.inp.known;
        let tn = self.eq.intern(t);
        let root = self.eq.find(tn);
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut c: Vec<TermId> = Vec::new();
        for &k in known {
            if k == t || !is_concat(self.terms, k) || !seen.insert(k) {
                continue;
            }
            let kn = self.eq.intern(k);
            if self.eq.find(kn) == root {
                c.push(k);
            }
        }
        let (input, minted) = (self.inp.input_sides, self.inp.minted_sides);
        let rank = |k: TermId| {
            if input.contains(&k) {
                0
            } else if minted.contains(&k) {
                2
            } else {
                1
            }
        };
        let terms = &*self.terms;
        c.sort_by_key(|&k| {
            (
                rank(k),
                std::cmp::Reverse(concat_arity(terms, k)),
                k.index(),
            )
        });
        c
    }

    /// A concat anchored to a fixed word in its class is sliced among its
    /// operands by length (as `model::value_concat` does); otherwise it is
    /// assembled from its operands' values.
    fn value_concat(&mut self, t: TermId) -> String {
        let kids: Vec<TermId> = match self.terms.term_node(t) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrConcat),
                args,
                ..
            } => self.terms.children(*args).to_vec(),
            _ => return String::new(),
        };
        let known = self.inp.known;
        let anchor = class_member(self.terms, self.eq, known, t, |terms, mm| {
            const_word_of(terms, mm).is_some()
        })
        .and_then(|c| const_word_of(self.terms, c));
        match anchor {
            Some(word) => self.slice_word(&kids, &word),
            None => kids.into_iter().map(|k| self.value(k)).collect(),
        }
    }

    /// Record each operand's slice of `word` (constants and already-valued
    /// operands keep their own length; the last operand takes the remainder;
    /// others take their arith length) and return `word`.
    fn slice_word(&mut self, kids: &[TermId], word: &str) -> String {
        let chars: Vec<char> = word.chars().collect();
        let mut off = 0usize;
        for (i, &k) in kids.iter().enumerate() {
            let len = if let Some(c) = self.terms.string_const_value(k) {
                c.chars().count()
            } else if let Some(v) = self.memo.get(&k) {
                v.chars().count()
            } else if i + 1 == kids.len() {
                chars.len().saturating_sub(off)
            } else {
                self.len_of(k).unwrap_or(0)
            };
            let start = off.min(chars.len());
            let end = (off + len).min(chars.len());
            if self.terms.string_const_value(k).is_none() {
                self.memo
                    .entry(k)
                    .or_insert_with(|| chars[start..end].iter().collect());
            }
            off = end;
        }
        word.to_owned()
    }

    /// `str.len k` in the arith model, if arith assigned it.
    fn len_of(&mut self, k: TermId) -> Option<usize> {
        let lt = self
            .terms
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[k])
            .expect("str.len of a string term");
        match self.m.get(lt) {
            Some(ModelVal::Num(r)) if !r.is_negative() => r.numer().to_i128().map(|v| v as usize),
            _ => None,
        }
    }

    /// `t`'s own arith length, else the largest arith length over its class
    /// members; `None` when arith assigned none (then no candidate is
    /// length-checked).
    fn class_len(&mut self, t: TermId) -> Option<usize> {
        if let Some(n) = self.len_of(t) {
            return Some(n);
        }
        let known = self.inp.known;
        let tn = self.eq.intern(t);
        let root = self.eq.find(tn);
        let mut best: Option<usize> = None;
        for &k in known {
            let kn = self.eq.intern(k);
            if self.eq.find(kn) == root {
                if let Some(n) = self.len_of(k) {
                    best = best.max(Some(n));
                }
            }
        }
        best
    }
}

/// True iff every input equation's two sides denote the same word under
/// `vals` (falling back to `m`'s string values). A side is evaluated the way
/// the solver's gate (`Solver::eval_str_val`) does: a constant, else the
/// assigned value, else the concatenation of its operands. A side that cannot
/// be evaluated counts as holding, so this never fires on a term the gate
/// cannot see either. `eq_true` may hold a `Distinct` asserted false; its
/// sides must be equal too.
pub(crate) fn input_eqs_hold(
    terms: &Context,
    input_eqs: &[TermId],
    vals: &[(TermId, String)],
    m: &ModelBuilder,
) -> bool {
    let view: FxHashMap<TermId, &str> = vals.iter().map(|(t, v)| (*t, v.as_str())).collect();
    input_eqs.iter().all(|&atom| {
        let (l, r) = crate::wordeq::diseq_sides(terms, atom);
        match (eval_word(terms, &view, m, l), eval_word(terms, &view, m, r)) {
            (Some(a), Some(b)) => a == b,
            _ => true,
        }
    })
}

fn eval_word(
    terms: &Context,
    view: &FxHashMap<TermId, &str>,
    m: &ModelBuilder,
    t: TermId,
) -> Option<String> {
    if let Some(s) = terms.string_const_value(t) {
        return Some(s.to_owned());
    }
    if let Some(s) = view.get(&t) {
        return Some((*s).to_owned());
    }
    if let Some(ModelVal::String(s)) = m.get(t) {
        return Some(s.clone());
    }
    match terms.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => {
            let mut out = String::new();
            for &k in terms.children(*args) {
                out.push_str(&eval_word(terms, view, m, k)?);
            }
            Some(out)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_theory::types::EqJust;

    fn var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn cat(ctx: &mut Context, a: TermId, b: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, b])
            .unwrap()
    }

    fn set_len(ctx: &mut Context, m: &mut ModelBuilder, t: TermId, n: i128) {
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[t]).unwrap();
        m.assign(l, ModelVal::Num(shinri_core::Rational::from_int(n.into())));
    }

    fn merge(eq: &mut EqualityEngine, a: TermId, b: TermId) {
        let an = eq.intern(a);
        let bn = eq.intern(b);
        let _ = eq.merge(an, bn, EqJust::Definitional);
    }

    fn value_in(vals: &[(TermId, String)], t: TermId) -> String {
        vals.iter()
            .find(|(k, _)| *k == t)
            .map(|(_, v)| v.clone())
            .expect("term valued")
    }

    fn sides(ts: &[TermId]) -> FxHashSet<TermId> {
        ts.iter().copied().collect()
    }

    /// `x ≈ "cd" ++ p` (input) and `x ≈ "c" ++ k` (minted, listed first, as the
    /// search produces it), `len x = 3`, `len p = 1`. The default build takes
    /// the minted concat and free-fills `x`; the rebuild gives `"cd?"`.
    #[test]
    fn char_peel_class_prefers_input_concat() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let mut m = ModelBuilder::default();
        let (x, p, k) = (var(&mut ctx, "x"), var(&mut ctx, "p"), var(&mut ctx, "k"));
        let cd = ctx.mk_string_const("cd");
        let c = ctx.mk_string_const("c");
        let input = cat(&mut ctx, cd, p);
        let minted = cat(&mut ctx, c, k);
        merge(&mut eq, x, input);
        merge(&mut eq, x, minted);
        set_len(&mut ctx, &mut m, x, 3);
        set_len(&mut ctx, &mut m, p, 1);
        let known = vec![minted, x, cd, input, k, p, c];
        let input_eq = ctx.mk_eq(x, input).unwrap();
        let seeds = FxHashMap::default();

        let default = crate::model::string_values(&mut ctx, &mut eq, &known, &known, &m, &seeds);
        assert!(
            !value_in(&default, x).starts_with("cd"),
            "documents the defect"
        );
        assert!(!input_eqs_hold(&ctx, &[input_eq], &default, &m));

        let inp = ReconcileInput {
            known: &known,
            str_terms: &known,
            seeds: &seeds,
            input_sides: &sides(&[x, input]),
            minted_sides: &sides(&[x, minted]),
        };
        let rebuilt = reconciled_values(&mut ctx, &mut eq, &m, &inp);
        let xv = value_in(&rebuilt, x);
        assert!(
            xv.starts_with("cd") && xv.chars().count() == 3,
            "x = {xv:?}"
        );
        assert!(input_eqs_hold(&ctx, &[input_eq], &rebuilt, &m));
    }

    /// `x ≈ s ++ "c"` (input) and `s ≈ x ++ k` (minted, an infeasible cycle),
    /// `len x = 3`, `len s = 2`. The cycle must fall back to a free fill of
    /// `s`, and the rejected candidate must not poison `x`.
    #[test]
    fn minted_cycle_fills_freely_without_poisoning() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let mut m = ModelBuilder::default();
        let (x, s, k) = (var(&mut ctx, "x"), var(&mut ctx, "s"), var(&mut ctx, "k"));
        let c = ctx.mk_string_const("c");
        let input = cat(&mut ctx, s, c);
        let minted = cat(&mut ctx, x, k);
        merge(&mut eq, x, input);
        merge(&mut eq, s, minted);
        set_len(&mut ctx, &mut m, x, 3);
        set_len(&mut ctx, &mut m, s, 2);
        let known = vec![minted, x, input, s, k, c];
        let input_eq = ctx.mk_eq(x, input).unwrap();
        let seeds = FxHashMap::default();
        let inp = ReconcileInput {
            known: &known,
            str_terms: &known,
            seeds: &seeds,
            input_sides: &sides(&[x, input]),
            minted_sides: &sides(&[s, minted]),
        };
        let rebuilt = reconciled_values(&mut ctx, &mut eq, &m, &inp);
        let (xv, sv) = (value_in(&rebuilt, x), value_in(&rebuilt, s));
        assert_eq!(sv.chars().count(), 2, "s = {sv:?}");
        assert_eq!(xv, format!("{sv}c"));
        assert!(input_eqs_hold(&ctx, &[input_eq], &rebuilt, &m));
    }

    /// A side that cannot be evaluated counts as holding.
    #[test]
    fn unevaluable_side_counts_as_holding() {
        let mut ctx = Context::new();
        let m = ModelBuilder::default();
        let (x, y) = (var(&mut ctx, "x"), var(&mut ctx, "y"));
        let e = ctx.mk_eq(x, y).unwrap();
        assert!(input_eqs_hold(&ctx, &[e], &[(x, "a".to_owned())], &m));
        assert!(!input_eqs_hold(
            &ctx,
            &[e],
            &[(x, "a".to_owned()), (y, "b".to_owned())],
            &m
        ));
    }
}
