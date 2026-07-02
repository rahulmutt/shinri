//! Word-level normalization (slice 5). Runs FIRST in check_sat(), before atom
//! collection, fences, and Tseitin, so every downstream consumer sees only
//! shapes the blasters already handle:
//!
//! 1. **ite elimination**: `(ite c x y)` with BitVec/Float/RoundingMode-sorted
//!    branches becomes a fresh nullary symbol `w` plus one appended defining
//!    assertion `(ite c (= w x) (= w y))` (Bool-sorted ite — plain Boolean
//!    structure for every stage). Equisatisfiable and model-preserving for
//!    user symbols: `w` is functionally determined by (c, x, y).
//! 2. **n-ary `=`/`distinct` expansion** over the same word sorts: `=` chains
//!    adjacent pairs, `distinct` expands pairwise, both under `and`. The blast
//!    arms are binary-only; unexpanded n-ary atoms were the confirmed
//!    wrong-SAT family (design doc §1).
//!
//! INVARIANTS (load-bearing; see design doc §4):
//! - A term with no rewritten subterm is returned with its ORIGINAL TermId —
//!   downstream stages key on TermIds.
//! - Other sorts (Bool/Int/Real/Array/String) pass through untouched.
//! - Fresh names `ite!<n>` are probed against the symbol table so they can
//!   never alias a user symbol; model filtering keys on the `internal`
//!   TermId set, never on the name.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, SortId, SortNode, TermId, TermNode};

#[derive(Default)]
pub struct WordNorm {
    /// ite TermId (post-child-rewrite) → its fresh symbol term. Solver-lifetime:
    /// repeated check-sats and shared subterms reuse one symbol.
    ite_var: FxHashMap<TermId, TermId>,
    /// Every fresh symbol term ever minted — the model-output filter set.
    /// Only guards the bv/fp `var_bits` model-extraction loops in lib.rs. The
    /// other two model-insertion sites (the `mb`-based `atom_vars` loop and the
    /// `mb.iter()` surface-everything loop) do NOT check `internal` — they rely
    /// instead on the implicit invariant that RM/FP/BV atoms are intercepted by
    /// Tseitin's surrogate mechanism before ever reaching EUF registration, so
    /// `mb` (the EUF/theory model) never holds an entry for a fresh `ite!`
    /// symbol in the first place (verified slice 5).
    pub internal: FxHashSet<TermId>,
    /// Monotone counter for fresh names.
    ctr: u32,
}

fn is_word_sort(ctx: &Context, s: SortId) -> bool {
    matches!(
        ctx.sort_node(s),
        SortNode::BitVec(_) | SortNode::Float(_, _) | SortNode::RoundingMode
    )
}

impl WordNorm {
    /// Rewrite `assertions`; returns the rewritten set with all defining
    /// assertions for the ites encountered THIS call appended (deduped).
    pub fn normalize(&mut self, ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
        let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut defs: Vec<TermId> = Vec::new();
        let mut seen_defs: FxHashSet<TermId> = FxHashSet::default();
        let mut out: Vec<TermId> = assertions
            .iter()
            .map(|&a| self.walk(ctx, a, &mut memo, &mut defs, &mut seen_defs))
            .collect();
        out.extend(defs);
        out
    }

    fn fresh_var(&mut self, ctx: &mut Context, sort: SortId) -> TermId {
        loop {
            let name = format!("ite!{}", self.ctr);
            self.ctr += 1;
            if ctx.lookup_symbol(&name).is_some() {
                continue; // user (or an earlier check) owns this name
            }
            let sym = ctx.declare_fun(&name, &[], sort);
            // Reserve the name so a later user `declare-fun`/`declare-const`
            // naming it is rejected at parse time — otherwise the user's app
            // hash-conses to `w` and inherits this ite definition (slice 5
            // final review: wrong-UNSAT via post-mint re-declaration).
            ctx.reserve_symbol(sym);
            let w = ctx
                .mk_app(Op::Uninterpreted(sym), &[])
                .expect("nullary app of a declared symbol is well-sorted");
            self.internal.insert(w);
            return w;
        }
    }

    fn walk(
        &mut self,
        ctx: &mut Context,
        t: TermId,
        memo: &mut FxHashMap<TermId, TermId>,
        defs: &mut Vec<TermId>,
        seen_defs: &mut FxHashSet<TermId>,
    ) -> TermId {
        if let Some(&r) = memo.get(&t) {
            return r;
        }
        let TermNode::App { op, args, .. } = ctx.term_node(t).clone() else {
            memo.insert(t, t);
            return t;
        };
        let kids: Vec<TermId> = ctx.children(args).to_vec();
        let new_kids: Vec<TermId> = kids
            .iter()
            .map(|&k| self.walk(ctx, k, memo, defs, seen_defs))
            .collect();
        // No-change ⇒ SAME TermId (hard requirement); otherwise rebuild.
        let rebuilt = if new_kids == kids {
            t
        } else {
            ctx.mk_app(op, &new_kids)
                .expect("child-for-child rebuild preserves sorts")
        };
        let result = match op {
            Op::Builtin(BuiltinOp::Ite)
                if is_word_sort(ctx, ctx.sort_of(rebuilt)) =>
            {
                let (c, x, y) = (new_kids[0], new_kids[1], new_kids[2]);
                let w = if let Some(&w) = self.ite_var.get(&rebuilt) {
                    w
                } else {
                    let w = self.fresh_var(ctx, ctx.sort_of(rebuilt));
                    self.ite_var.insert(rebuilt, w);
                    w
                };
                let wx = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, x])
                    .expect("(= w then) well-sorted");
                let wy = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, y])
                    .expect("(= w else) well-sorted");
                let def = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, wx, wy])
                    .expect("definition well-sorted");
                if seen_defs.insert(def) {
                    defs.push(def);
                }
                w
            }
            Op::Builtin(BuiltinOp::Eq)
                if new_kids.len() > 2 && is_word_sort(ctx, ctx.sort_of(new_kids[0])) =>
            {
                // (= a b c ...) → (and (= a b) (= b c) ...): adjacent chain.
                let pairs: Vec<TermId> = new_kids
                    .windows(2)
                    .map(|w| {
                        ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w[0], w[1]])
                            .expect("binary = well-sorted")
                    })
                    .collect();
                ctx.mk_app(Op::Builtin(BuiltinOp::And), &pairs)
                    .expect("and well-sorted")
            }
            Op::Builtin(BuiltinOp::Distinct)
                if new_kids.len() > 2 && is_word_sort(ctx, ctx.sort_of(new_kids[0])) =>
            {
                // (distinct a b c ...) → conjunction over all pairs i<j.
                let mut pairs: Vec<TermId> = Vec::new();
                for i in 0..new_kids.len() {
                    for j in (i + 1)..new_kids.len() {
                        pairs.push(
                            ctx.mk_app(
                                Op::Builtin(BuiltinOp::Distinct),
                                &[new_kids[i], new_kids[j]],
                            )
                            .expect("binary distinct well-sorted"),
                        );
                    }
                }
                ctx.mk_app(Op::Builtin(BuiltinOp::And), &pairs)
                    .expect("and well-sorted")
            }
            _ => rebuilt,
        };
        memo.insert(t, result);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};

    fn bv_var(ctx: &mut Context, name: &str, w: u32) -> shinri_core::TermId {
        let s = ctx.bv_sort(w);
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    fn bool_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let s = ctx.bool_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn unchanged_assertion_keeps_identical_termid() {
        // HARD REQUIREMENT: no-change must mean same TermId, not an equal rebuild.
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom]);
        assert!(wn.internal.is_empty());
    }

    #[test]
    fn bv_ite_becomes_fresh_var_plus_definition() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let z = bv_var(&mut ctx, "z", 8);
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, z]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        // Rewritten atom + appended definition.
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
        let w = *wn.internal.iter().next().unwrap();
        // Rewritten atom is (= w z).
        let expect_atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, z]).unwrap();
        assert_eq!(out[0], expect_atom);
        // Definition is (ite c (= w x) (= w y)).
        let wx = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, x]).unwrap();
        let wy = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, y]).unwrap();
        let expect_def = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, wx, wy]).unwrap();
        assert_eq!(out[1], expect_def);
    }

    #[test]
    fn shared_ite_and_repeated_calls_reuse_one_symbol() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let a1 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, x]).unwrap();
        let a2 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, y]).unwrap();
        let mut wn = WordNorm::default();
        let out1 = wn.normalize(&mut ctx, &[a1, a2]);
        assert_eq!(wn.internal.len(), 1, "one ite term → one fresh symbol");
        assert_eq!(out1.len(), 3, "two rewritten atoms + ONE deduped definition");
        // Second check-sat: same memoized symbol, definition re-emitted.
        let out2 = wn.normalize(&mut ctx, &[a1]);
        assert_eq!(wn.internal.len(), 1);
        assert_eq!(out2.len(), 2);
    }

    #[test]
    fn nested_ite_rewrites_bottom_up() {
        // (ite c (ite d x y) z): inner ite becomes w1, outer becomes w2,
        // and w2's definition references w1.
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let d = bool_var(&mut ctx, "d");
        let x = bv_var(&mut ctx, "x", 4);
        let y = bv_var(&mut ctx, "y", 4);
        let z = bv_var(&mut ctx, "z", 4);
        let inner = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[d, x, y]).unwrap();
        let outer = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, inner, z]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[outer, x]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(wn.internal.len(), 2);
        assert_eq!(out.len(), 3, "one rewritten atom + two definitions");
    }

    #[test]
    fn nary_eq_and_distinct_expand_for_word_sorts_only() {
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let z = bv_var(&mut ctx, "z", 8);
        let eq3 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y, z]).unwrap();
        let d3 = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, y, z]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[eq3, d3]);
        // (= x y z) → (and (= x y) (= y z))
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let yz = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[y, z]).unwrap();
        let expect_eq = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[xy, yz]).unwrap();
        assert_eq!(out[0], expect_eq);
        // (distinct x y z) → (and (distinct x y) (distinct x z) (distinct y z))
        let dxy = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, y]).unwrap();
        let dxz = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, z]).unwrap();
        let dyz = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[y, z]).unwrap();
        let expect_d = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[dxy, dxz, dyz]).unwrap();
        assert_eq!(out[1], expect_d);
        // Non-word sorts pass through untouched (arith keeps its existing path).
        let int_s = ctx.int_sort();
        let af = ctx.declare_fun("ai", &[], int_s);
        let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("bi", &[], int_s);
        let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let cf = ctx.declare_fun("ci", &[], int_s);
        let cc = ctx.mk_app(Op::Uninterpreted(cf), &[]).unwrap();
        let di = ctx.mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, cc]).unwrap();
        let out2 = wn.normalize(&mut ctx, &[di]);
        assert_eq!(out2, vec![di], "Int-sorted n-ary distinct is untouched");
    }

    #[test]
    fn bool_and_nonword_ite_pass_through() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let p = bool_var(&mut ctx, "p");
        let q = bool_var(&mut ctx, "q");
        let bool_ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, p, q]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[bool_ite]);
        assert_eq!(out, vec![bool_ite]);
        assert!(wn.internal.is_empty());
    }

    #[test]
    fn fresh_name_skips_user_declared_collision() {
        let mut ctx = Context::new();
        // User squats on the first fresh name.
        let s8 = ctx.bv_sort(8);
        ctx.declare_fun("ite!0", &[], s8);
        let c = bool_var(&mut ctx, "c");
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, x]).unwrap();
        let mut wn = WordNorm::default();
        wn.normalize(&mut ctx, &[atom]);
        let w = *wn.internal.iter().next().unwrap();
        // The fresh symbol must NOT be the user's `ite!0` term.
        let user_sym = ctx.lookup_symbol("ite!0").unwrap();
        let user_term = ctx.mk_app(Op::Uninterpreted(user_sym), &[]).unwrap();
        assert_ne!(w, user_term, "fresh symbol must not alias a user symbol");
    }

    #[test]
    fn rm_ite_rewrites_too() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let rtz = ctx.mk_rm_const(shinri_core::RoundingMode::Rtz);
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, rne, rtz]).unwrap();
        // Embed under an FP op so the ite is in operand position:
        // (fp.sqrt (ite c RNE RTZ) x)
        let f32s = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32s);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let sq = ctx.mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[ite, x]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[sq, x]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
        // The rewritten atom's sqrt operand is the fresh RM variable.
        let w = *wn.internal.iter().next().unwrap();
        let new_sq = ctx.mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[w, x]).unwrap();
        let expect = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[new_sq, x]).unwrap();
        assert_eq!(out[0], expect);
    }
}
