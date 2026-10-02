//! Word-level normalization (slice 5). Runs FIRST in check_sat(), before atom
//! collection, fences, and Tseitin, so every downstream consumer sees only
//! shapes the blasters already handle:
//!
//! 1. **ite elimination**: `(ite c x y)` with any non-Bool, non-String sort
//!    (BitVec/Float/RoundingMode — slice 5; Int/Real/uninterpreted/Array —
//!    slice 10) becomes a fresh nullary symbol `w` plus one appended defining
//!    assertion `(ite c (= w x) (= w y))` (Bool-sorted ite — plain Boolean
//!    structure for every stage). Equisatisfiable and model-preserving for
//!    user symbols: `w` is functionally determined by (c, x, y).
//! 2. **n-ary `=`/`distinct` expansion** over ALL sorts (slice 6: the old word-sort gate excluded exactly the sorts where tseitin/EUF silently dropped operands 3+ — wrong-SAT): `=` chains
//!    adjacent pairs, `distinct` expands pairwise, both under `and`. The blast
//!    arms are binary-only; unexpanded n-ary atoms were the confirmed
//!    wrong-SAT family (design doc §1).
//! 3. **Bool-argument purification** (slice 54): a Bool-sorted child of a
//!    parent that is NOT a Boolean connective (UF and datatype applications,
//!    `select`/`store`) — other than `true`/`false` or a nullary symbol —
//!    becomes a fresh nullary Bool symbol `b` (`bool!<n>`) plus one appended
//!    definition `(= b t)` (Bool `=` is iff for Tseitin). Without it the
//!    argument was an opaque e-graph node, never tied to its truth value:
//!    `(P (= x 1))`, `(not (P true))`, `(= x 1)` was a wrong `sat`. `b` takes
//!    the same path as a user Bool constant (an EUF atom merged with ⊤/⊥), and
//!    the definition puts `t` in a Boolean position (so slice 53's arithmetic
//!    `=` axioms reach it).
//!
//! INVARIANTS (load-bearing; see design doc §4):
//! - A term with no rewritten subterm is returned with its ORIGINAL TermId —
//!   downstream stages key on TermIds.
//! - Only Bool and String ites pass through untouched (see exclusions above);
//!   n-ary `=`/`distinct` still expands for every sort (slice 6).
//! - Fresh names `ite!<n>` / `bool!<n>` are probed against the symbol table so
//!   they can never alias a user symbol; model filtering keys on the
//!   `internal` TermId set, never on the name.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, SortId, SortNode, TermId, TermNode};

#[derive(Default)]
pub struct WordNorm {
    /// ite TermId (post-child-rewrite) → its fresh symbol term. Solver-lifetime:
    /// repeated check-sats and shared subterms reuse one symbol.
    ite_var: FxHashMap<TermId, TermId>,
    /// Original (child-un-rewritten) eliminated-ite term → its fresh symbol.
    /// `ite_var` is keyed by the POST-rewrite ite (needed for structural dedup
    /// during the walk); a nested outer ite's post-rewrite key embeds the inner
    /// fresh var and never matches the user's original get-value query term.
    /// This parallel map keyed by the original `t` closes that gap (item 4,
    /// slice 7). Get-value only; get-model output is unchanged.
    orig_ite: FxHashMap<TermId, TermId>,
    /// Slice 54: compound Bool argument (post-child-rewrite) → its proxy
    /// symbol. Solver-lifetime, like `ite_var`: a shared argument and repeated
    /// check-sats reuse one proxy.
    bool_arg_var: FxHashMap<TermId, TermId>,
    /// Every fresh symbol term ever minted — the model-output filter set.
    /// ALL model-surfacing loops in lib.rs check `internal`: the bv/fp/rm
    /// `var_bits` model-extraction loops (slice 5/6) and the two `mb`-based
    /// loops (the `atom_vars` loop and the `mb.iter()` surface-everything
    /// loop). Through slice 9, the `mb`-based loops didn't need the check —
    /// RM/FP/BV atoms were intercepted by Tseitin's surrogate mechanism
    /// before reaching EUF registration, so `mb` (the EUF/theory model)
    /// never held an entry for a fresh `ite!` symbol. Slice 10 broadened ite
    /// elimination to Int/Real/uninterpreted-sort ites, which register their
    /// `ite!` symbols with EUF/arith as ordinary terms — so `mb` now DOES
    /// hold entries for them, and both `mb`-based loops filter on `internal`
    /// too (see the `internal_vals` extraction in lib.rs).
    pub internal: FxHashSet<TermId>,
    /// Monotone counter for fresh names.
    ctr: u32,
}

impl WordNorm {
    /// Original eliminated-ite term → its internal fresh symbol term.
    /// Used by the solver to answer get-value on eliminated ites (slice 6).
    pub(crate) fn ite_map(&self) -> &FxHashMap<TermId, TermId> {
        &self.ite_var
    }

    /// Original eliminated-ite term → internal fresh symbol, for get-value on
    /// nested ites (item 4, slice 7).
    pub(crate) fn orig_ite_map(&self) -> &FxHashMap<TermId, TermId> {
        &self.orig_ite
    }
}

/// Sorts whose ites word_norm ELIMINATES (fresh symbol + defining assertion).
/// Slice 5 covered the word sorts (BitVec/Float/RoundingMode) so the blasters
/// never see term-level ite. Slice 10 broadens to Int/Real/uninterpreted/
/// Array: those ites previously fell through to EUF as OPAQUE applications,
/// silently unlinking the condition from the branches — wrong-SAT on every
/// non-string path (design §1). Exclusions: Bool ite is plain Boolean
/// structure (Tseitin handles it); String ite is handled by the string path's
/// own reduce_assertions elimination (design §1.1 item 2) and is left
/// untouched to avoid disturbing a working, semi-decidable path.
fn eliminates_ite_sort(ctx: &Context, s: SortId) -> bool {
    !matches!(ctx.sort_node(s), SortNode::Bool | SortNode::String)
}

/// Slice 54: parents whose Bool-sorted children sit in a Boolean position
/// (Tseitin encodes them as structure). Every other parent's Bool child is a
/// term-position argument and is purified. `Ite` is listed for both shapes:
/// a Bool ite is structure, and a term ite's condition stays Boolean in its
/// elimination definition `(ite c (= w x) (= w y))`.
fn is_bool_connective(op: Op) -> bool {
    matches!(
        op,
        Op::Builtin(
            BuiltinOp::Not
                | BuiltinOp::And
                | BuiltinOp::Or
                | BuiltinOp::Implies
                | BuiltinOp::Xor
                | BuiltinOp::Eq
                | BuiltinOp::Distinct
                | BuiltinOp::Ite
        )
    )
}

/// Slice 54: a Bool-sorted argument needs a proxy unless it is already a
/// single atom EUF links to ⊤/⊥: a Bool constant (`true`/`false`) or a
/// nullary symbol (a user Bool constant, or an earlier proxy).
fn needs_bool_proxy(ctx: &Context, t: TermId) -> bool {
    if ctx.sort_of(t) != ctx.bool_sort() {
        return false;
    }
    match ctx.term_node(t) {
        TermNode::Const { .. } => false,
        TermNode::App {
            op: Op::Uninterpreted(_),
            args,
            ..
        } => !ctx.children(*args).is_empty(),
        TermNode::App { .. } => true,
    }
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

    fn fresh_var(&mut self, ctx: &mut Context, sort: SortId, prefix: &str) -> TermId {
        loop {
            let name = format!("{prefix}{}", self.ctr);
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

    /// Slice 54: the proxy for argument `t`, appending `(= b t)` once per call.
    fn bool_proxy(
        &mut self,
        ctx: &mut Context,
        t: TermId,
        defs: &mut Vec<TermId>,
        seen_defs: &mut FxHashSet<TermId>,
    ) -> TermId {
        let b = if let Some(&b) = self.bool_arg_var.get(&t) {
            b
        } else {
            let b = self.fresh_var(ctx, ctx.bool_sort(), "bool!");
            self.bool_arg_var.insert(t, b);
            b
        };
        let def = ctx
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[b, t])
            .expect("(= b t) over Bool is well-sorted");
        if seen_defs.insert(def) {
            defs.push(def);
        }
        b
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
        let mut new_kids: Vec<TermId> = kids
            .iter()
            .map(|&k| self.walk(ctx, k, memo, defs, seen_defs))
            .collect();
        // Slice 54 (item 3): purify compound Bool arguments of non-connectives.
        if !is_bool_connective(op) {
            for k in new_kids.iter_mut() {
                if needs_bool_proxy(ctx, *k) {
                    *k = self.bool_proxy(ctx, *k, defs, seen_defs);
                }
            }
        }
        // No-change ⇒ SAME TermId (hard requirement); otherwise rebuild.
        let rebuilt = if new_kids == kids {
            t
        } else {
            ctx.mk_app(op, &new_kids)
                .expect("child-for-child rebuild preserves sorts")
        };
        let result = match op {
            Op::Builtin(BuiltinOp::Ite) if eliminates_ite_sort(ctx, ctx.sort_of(rebuilt)) => {
                let (c, x, y) = (new_kids[0], new_kids[1], new_kids[2]);
                let w = if let Some(&w) = self.ite_var.get(&rebuilt) {
                    w
                } else {
                    let w = self.fresh_var(ctx, ctx.sort_of(rebuilt), "ite!");
                    self.ite_var.insert(rebuilt, w);
                    w
                };
                let wx = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Eq), &[w, x])
                    .expect("(= w then) well-sorted");
                let wy = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Eq), &[w, y])
                    .expect("(= w else) well-sorted");
                let def = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Ite), &[c, wx, wy])
                    .expect("definition well-sorted");
                if seen_defs.insert(def) {
                    defs.push(def);
                }
                // Item 4 (slice 7): also key by the ORIGINAL term so get-value on
                // a nested outer ite (whose original child was not yet rewritten)
                // resolves. `t` is this ite's original id; `w` its fresh symbol.
                self.orig_ite.insert(t, w);
                w
            }
            Op::Builtin(BuiltinOp::Eq) if new_kids.len() > 2 => {
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
            Op::Builtin(BuiltinOp::Distinct) if new_kids.len() > 2 => {
                // An n-ary distinct with a repeated operand can never hold (a value
                // cannot differ from itself), so the whole atom is `false`. Fold it
                // directly rather than emit a self-distinct pair `(distinct x x)` that
                // the string/EUF theory then mishandles regardless of polarity
                // (I1 wrong-UNSAT, slice 7).
                let mut has_dup = false;
                'outer: for i in 0..new_kids.len() {
                    for j in (i + 1)..new_kids.len() {
                        if new_kids[i] == new_kids[j] {
                            has_dup = true;
                            break 'outer;
                        }
                    }
                }
                if has_dup {
                    ctx.mk_const_bool(false)
                } else {
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
            }
            Op::Builtin(BuiltinOp::Not) => {
                // C2 (slice 7): De Morgan a negated n-ary `=`. word_norm has already
                // expanded the Eq child to (and (= a b) (= b c) …) — all binary (the
                // EUF/tseitin invariant). Rewrite (not (and …)) → (or (not (= a b))
                // (not (= b c)) …) so lower's binary Not(Eq) arm enforces each arith
                // pair as (or Lt Gt). Sound for every sort; every Eq stays binary.
                // Any other Not child falls through unchanged (same as `_ => rebuilt`),
                // preserving the no-change ⇒ same-TermId invariant.
                let child_is_nary_eq = matches!(
                    ctx.term_node(kids[0]).clone(),
                    TermNode::App { op: Op::Builtin(BuiltinOp::Eq), args: ca, .. }
                        if ctx.children(ca).len() > 2
                );
                if child_is_nary_eq {
                    if let TermNode::App {
                        op: Op::Builtin(BuiltinOp::And),
                        args: aa,
                        ..
                    } = ctx.term_node(new_kids[0]).clone()
                    {
                        let conjs: Vec<TermId> = ctx.children(aa).to_vec();
                        let disj: Vec<TermId> = conjs
                            .iter()
                            .map(|&c| {
                                ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[c])
                                    .expect("not well-sorted")
                            })
                            .collect();
                        ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disj)
                            .expect("or well-sorted")
                    } else {
                        rebuilt
                    }
                } else {
                    rebuilt
                }
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
        let expect_def = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[c, wx, wy])
            .unwrap();
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
        assert_eq!(
            out1.len(),
            3,
            "two rewritten atoms + ONE deduped definition"
        );
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
        let outer = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[c, inner, z])
            .unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[outer, x]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(wn.internal.len(), 2);
        assert_eq!(out.len(), 3, "one rewritten atom + two definitions");
    }

    #[test]
    fn nary_eq_and_distinct_expand_for_all_sorts() {
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let y = bv_var(&mut ctx, "y", 8);
        let z = bv_var(&mut ctx, "z", 8);
        let eq3 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y, z]).unwrap();
        let d3 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, y, z])
            .unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[eq3, d3]);
        // (= x y z) → (and (= x y) (= y z))
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let yz = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[y, z]).unwrap();
        let expect_eq = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[xy, yz]).unwrap();
        assert_eq!(out[0], expect_eq);
        // (distinct x y z) → (and (distinct x y) (distinct x z) (distinct y z))
        let dxy = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, y])
            .unwrap();
        let dxz = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, z])
            .unwrap();
        let dyz = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[y, z])
            .unwrap();
        let expect_d = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[dxy, dxz, dyz])
            .unwrap();
        assert_eq!(out[1], expect_d);

        // Slice 6: NON-word sorts expand too — the expansion is sort-universal
        // (the wrong-SAT family lived exactly in the sorts the old guard skipped).
        // Int n-ary distinct:
        let int_s = ctx.int_sort();
        let af = ctx.declare_fun("ai", &[], int_s);
        let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("bi", &[], int_s);
        let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let cf = ctx.declare_fun("ci", &[], int_s);
        let cc = ctx.mk_app(Op::Uninterpreted(cf), &[]).unwrap();
        let di = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, cc])
            .unwrap();
        let out2 = wn.normalize(&mut ctx, &[di]);
        let dab = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b])
            .unwrap();
        let dac = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, cc])
            .unwrap();
        let dbc = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[b, cc])
            .unwrap();
        let expect_di = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[dab, dac, dbc])
            .unwrap();
        assert_eq!(
            out2,
            vec![expect_di],
            "Int n-ary distinct expands (slice 6)"
        );
        // Bool n-ary = (the tseitin p↔q wrong-SAT family):
        let p = bool_var(&mut ctx, "p");
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let beq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[p, q, r]).unwrap();
        let out3 = wn.normalize(&mut ctx, &[beq]);
        let pq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[p, q]).unwrap();
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[q, r]).unwrap();
        let expect_beq = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[pq, qr]).unwrap();
        assert_eq!(out3, vec![expect_beq], "Bool n-ary = expands (slice 6)");
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
        let ite = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[c, rne, rtz])
            .unwrap();
        // Embed under an FP op so the ite is in operand position:
        // (fp.sqrt (ite c RNE RTZ) x)
        let f32s = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32s);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let sq = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[ite, x])
            .unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[sq, x]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
        // The rewritten atom's sqrt operand is the fresh RM variable.
        let w = *wn.internal.iter().next().unwrap();
        let new_sq = ctx.mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[w, x]).unwrap();
        let expect = ctx
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[new_sq, x])
            .unwrap();
        assert_eq!(out[0], expect);
    }

    #[test]
    fn not_nary_eq_de_morgans_to_or_of_binary_diseqs() {
        let mut ctx = Context::new();
        let a = bv_var(&mut ctx, "a", 8);
        let b = bv_var(&mut ctx, "b", 8);
        let c = bv_var(&mut ctx, "c", 8);
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[a, b, c]).unwrap();
        let not = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[not]);
        // Expected: (or (not (= a b)) (not (= b c))).
        let eab = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[a, b]).unwrap();
        let ebc = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[b, c]).unwrap();
        let nab = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eab]).unwrap();
        let nbc = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[ebc]).unwrap();
        let expect = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[nab, nbc]).unwrap();
        assert_eq!(out, vec![expect]);
    }

    fn real_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let s = ctx.real_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    /// Slice 10: Real-sorted ite is eliminated exactly like a word ite —
    /// rewritten atom (= w z) + appended definition (ite c (= w x) (= w y)).
    #[test]
    fn real_ite_becomes_fresh_var_plus_definition() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let z = real_var(&mut ctx, "z");
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, z]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2, "rewritten atom + definition");
        assert_eq!(wn.internal.len(), 1);
        let w = *wn.internal.iter().next().unwrap();
        let expect_atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[w, z]).unwrap();
        assert_eq!(out[0], expect_atom);
    }

    /// Slice 10: Int-sorted ite nested under arithmetic is eliminated.
    #[test]
    fn int_ite_under_plus_is_eliminated() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let int = ctx.int_sort();
        let xf = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let yf = ctx.declare_fun("y", &[], int);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[ite, x]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[sum, y]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
    }

    /// Slice 10: uninterpreted-sort ite is eliminated.
    #[test]
    fn usort_ite_is_eliminated() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let u = ctx.declare_sort("U");
        let af = ctx.declare_fun("a", &[], u);
        let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("b2", &[], u);
        let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, a, b]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, a]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
    }

    /// Slice 10: Array-sorted ite is eliminated (fixes the ABV-path wrong-SAT).
    #[test]
    fn array_ite_is_eliminated() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let idx = ctx.bv_sort(8);
        let elem = ctx.bv_sort(8);
        let arr = ctx.array_sort(idx, elem);
        let af = ctx.declare_fun("a1", &[], arr);
        let a1 = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("a2", &[], arr);
        let a2 = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let ite = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[c, a1, a2])
            .unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, a1]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out.len(), 2);
        assert_eq!(wn.internal.len(), 1);
    }

    /// Slice 10: a Real ite shared by two atoms mints ONE symbol + ONE deduped
    /// definition (same contract as shared_ite_and_repeated_calls_reuse_one_symbol).
    #[test]
    fn shared_real_ite_reuses_one_symbol() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, x, y]).unwrap();
        let a1 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, x]).unwrap();
        let a2 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, y]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[a1, a2]);
        assert_eq!(wn.internal.len(), 1, "one ite term → one fresh symbol");
        assert_eq!(out.len(), 3, "two rewritten atoms + ONE deduped definition");
    }

    /// Slice 10 exclusion: String-sorted ite passes through UNTOUCHED (the
    /// string path's own reduce handles it — design §1.1 item 2). Original
    /// TermId must be preserved (no-change ⇒ same-TermId invariant).
    #[test]
    fn string_ite_passes_through_untouched() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let strs = ctx.string_sort();
        let af = ctx.declare_fun("s1", &[], strs);
        let s1 = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let bf = ctx.declare_fun("s2", &[], strs);
        let s2 = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let ite = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[c, s1, s2])
            .unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ite, s1]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "String ite must not be rewritten");
        assert!(wn.internal.is_empty());
    }

    /// Slice 10 exclusion: Bool-sorted ite passes through UNTOUCHED.
    #[test]
    fn bool_ite_passes_through_untouched() {
        let mut ctx = Context::new();
        let c = bool_var(&mut ctx, "c");
        let p = bool_var(&mut ctx, "p");
        let q = bool_var(&mut ctx, "q");
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, p, q]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[ite]);
        assert_eq!(out, vec![ite], "Bool ite must not be rewritten");
        assert!(wn.internal.is_empty());
    }

    #[test]
    fn distinct_with_duplicate_operand_folds_to_false() {
        use shinri_core::{ConstVal, TermNode};
        let mut ctx = Context::new();
        let a = bv_var(&mut ctx, "a", 8);
        let b = bv_var(&mut ctx, "b", 8);
        // (distinct a b b) — b repeated ⇒ unsatisfiable-as-true ⇒ false.
        let d = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, b])
            .unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[d]);
        // Single assertion rewritten to the `false` constant.
        assert_eq!(out.len(), 1);
        assert!(
            matches!(
                ctx.term_node(out[0]),
                TermNode::Const {
                    val: ConstVal::Bool(false),
                    ..
                }
            ),
            "expected false constant, got {:?}",
            ctx.term_node(out[0])
        );
    }

    // ── Slice 54: compound Bool arguments → proxy + (= b t) ─────────────────

    fn int_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let s = ctx.int_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    /// Declares `name : Bool -> Bool` and returns the symbol.
    fn bool_pred(ctx: &mut Context, name: &str) -> shinri_core::SymbolId {
        let b = ctx.bool_sort();
        ctx.declare_fun(name, &[b], b)
    }

    #[test]
    fn compound_bool_argument_becomes_proxy_plus_definition() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let p = bool_pred(&mut ctx, "P");
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let pe = ctx.mk_app(Op::Uninterpreted(p), &[eq]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[pe]);
        assert_eq!(wn.internal.len(), 1);
        let b = *wn.internal.iter().next().unwrap();
        let pb = ctx.mk_app(Op::Uninterpreted(p), &[b]).unwrap();
        let def = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[b, eq]).unwrap();
        assert_eq!(out, vec![pb, def]);
        // The proxy is named bool!<n>.
        let TermNode::App {
            op: Op::Uninterpreted(sym),
            ..
        } = ctx.term_node(b).clone()
        else {
            panic!("proxy must be a nullary uninterpreted app");
        };
        assert_eq!(ctx.lookup_symbol("bool!0"), Some(sym));
    }

    #[test]
    fn bare_constants_and_connective_children_are_not_purified() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let q = bool_var(&mut ctx, "q");
        let p = bool_pred(&mut ctx, "P");
        let t = ctx.mk_const_bool(true);
        let pq = ctx.mk_app(Op::Uninterpreted(p), &[q]).unwrap();
        let pt = ctx.mk_app(Op::Uninterpreted(p), &[t]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let conj = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[eq, q]).unwrap();
        let iff = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[q, eq]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[pq, pt, conj, iff]);
        assert_eq!(
            out,
            vec![pq, pt, conj, iff],
            "same TermIds, nothing appended"
        );
        assert!(wn.internal.is_empty());
    }

    #[test]
    fn one_proxy_per_argument_term_across_parents_and_calls() {
        let mut ctx = Context::new();
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let p = bool_pred(&mut ctx, "P");
        let g = bool_pred(&mut ctx, "G");
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[q, r]).unwrap();
        let pqr = ctx.mk_app(Op::Uninterpreted(p), &[qr]).unwrap();
        let gqr = ctx.mk_app(Op::Uninterpreted(g), &[qr]).unwrap();
        let mut wn = WordNorm::default();
        let out1 = wn.normalize(&mut ctx, &[pqr, gqr]);
        assert_eq!(
            wn.internal.len(),
            1,
            "P and G share one proxy for (and q r)"
        );
        assert_eq!(
            out1.len(),
            3,
            "two rewritten atoms + ONE deduped definition"
        );
        // Second check-sat: same proxy, definition re-emitted.
        let out2 = wn.normalize(&mut ctx, &[pqr]);
        assert_eq!(wn.internal.len(), 1);
        assert_eq!(out2.len(), 2);
        assert_eq!(out2[1], out1[2], "same hash-consed definition");
    }

    #[test]
    fn nested_bool_arguments_purify_bottom_up() {
        // (P (P (and q r))): inner (and q r) → b0, then (P b0) → b1.
        let mut ctx = Context::new();
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let p = bool_pred(&mut ctx, "P");
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[q, r]).unwrap();
        let inner = ctx.mk_app(Op::Uninterpreted(p), &[qr]).unwrap();
        let outer = ctx.mk_app(Op::Uninterpreted(p), &[inner]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[outer]);
        assert_eq!(wn.internal.len(), 2);
        let b0 = ctx
            .mk_app(Op::Uninterpreted(ctx.lookup_symbol("bool!0").unwrap()), &[])
            .unwrap();
        let b1 = ctx
            .mk_app(Op::Uninterpreted(ctx.lookup_symbol("bool!1").unwrap()), &[])
            .unwrap();
        let pb0 = ctx.mk_app(Op::Uninterpreted(p), &[b0]).unwrap();
        let pb1 = ctx.mk_app(Op::Uninterpreted(p), &[b1]).unwrap();
        let def0 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[b0, qr]).unwrap();
        let def1 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[b1, pb0]).unwrap();
        assert_eq!(out, vec![pb1, def0, def1]);
    }

    #[test]
    fn bool_ite_argument_is_purified_but_term_ite_condition_is_not() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let c = bool_var(&mut ctx, "c");
        let p = bool_pred(&mut ctx, "P");
        let f = ctx.declare_fun("f", &[ctx.bool_sort()], ctx.bool_sort());
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let fls = ctx.mk_const_bool(false);
        // (f (ite c (P (= x y)) false)): (= x y) → b0 as P's argument; the Bool
        // ite is Boolean structure (not eliminated) and is itself f's argument → b1.
        let pe = ctx.mk_app(Op::Uninterpreted(p), &[eq]).unwrap();
        let bite = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[c, pe, fls])
            .unwrap();
        let fb = ctx.mk_app(Op::Uninterpreted(f), &[bite]).unwrap();
        let mut wn = WordNorm::default();
        wn.normalize(&mut ctx, &[fb]);
        assert_eq!(
            wn.internal.len(),
            2,
            "one proxy for (= x y), one for the Bool ite"
        );

        // (= (ite (= x y) x y) x): Int term ite → ite!; its condition is NOT purified.
        let tite = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[eq, x, y])
            .unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[tite, x]).unwrap();
        let mut wn2 = WordNorm::default();
        wn2.normalize(&mut ctx, &[atom]);
        assert_eq!(wn2.internal.len(), 1, "only the ite! symbol");
        assert!(ctx.lookup_symbol("ite!0").is_some());
    }

    #[test]
    fn bool_proxy_name_skips_user_declared_collision() {
        let mut ctx = Context::new();
        let bs = ctx.bool_sort();
        ctx.declare_fun("bool!0", &[], bs);
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let p = bool_pred(&mut ctx, "P");
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[q, r]).unwrap();
        let pqr = ctx.mk_app(Op::Uninterpreted(p), &[qr]).unwrap();
        let mut wn = WordNorm::default();
        wn.normalize(&mut ctx, &[pqr]);
        let b = *wn.internal.iter().next().unwrap();
        let user = ctx
            .mk_app(Op::Uninterpreted(ctx.lookup_symbol("bool!0").unwrap()), &[])
            .unwrap();
        assert_ne!(b, user, "proxy must not alias a user symbol");
    }
}
