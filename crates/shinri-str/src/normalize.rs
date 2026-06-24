use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermId, TermNode};
use shinri_theory::types::ENodeId;
use shinri_theory::EqualityEngine;

/// Build an authoritative `ENodeId → TermId` reverse map for the given set of
/// known string terms.  For each equivalence class, we prefer to record a string
/// **constant** (`ConstVal::String`) so that `rep()` returns the constant when
/// the class contains one (needed for correct normal-form comparison in Task 11).
///
/// Tie-breaking rule (applied in iteration order of `known`):
/// - If the class has no entry yet, insert the term.
/// - If the class already has a non-constant entry and the new term is a
///   constant, replace it (promote constant to representative).
/// - If the class already has a constant, keep it (don't demote).
pub(crate) fn build_node_of(
    terms: &Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
) -> FxHashMap<ENodeId, TermId> {
    let mut node_of: FxHashMap<ENodeId, TermId> = FxHashMap::default();
    for &t in known {
        let n = eq.intern(t);
        let root = eq.find(n);
        let is_const = matches!(terms.term_node(t), TermNode::Const { val: ConstVal::String(_), .. });
        match node_of.get(&root).copied() {
            None => {
                node_of.insert(root, t);
            }
            Some(prev) => {
                // Promote to constant if current entry is not already a constant.
                let prev_is_const = matches!(
                    terms.term_node(prev),
                    TermNode::Const { val: ConstVal::String(_), .. }
                );
                if is_const && !prev_is_const {
                    node_of.insert(root, t);
                }
            }
        }
    }
    node_of
}

/// Return the representative `TermId` of `t`'s equivalence class, consulting
/// the global `node_of` map (built from all known string terms via
/// `build_node_of`).
///
/// Preference order:
/// 1. A string constant in the same class (so `rep(x)` returns `"ab"` when
///    `x = "ab"` was merged, enabling correct constant/constant alignment in
///    Task 11).
/// 2. Any term in `node_of` that shares `t`'s root.
/// 3. `t` itself as a conservative fallback (never incorrect, just opaque).
pub(crate) fn rep(
    eq: &mut EqualityEngine,
    node_of: &FxHashMap<ENodeId, TermId>,
    t: TermId,
) -> TermId {
    let n = eq.intern(t);
    let r = eq.find(n);
    *node_of.get(&r).unwrap_or(&t)
}

/// Flatten `str.++` into a sequence; map each atom to its class representative
/// (reflecting global EqualityEngine merges, preferring constants); fold
/// adjacent string-literal atoms; drop empty-string `""` atoms.
///
/// `known` must include every string-sorted term visible to the solver so that
/// `rep()` can honour merges with terms that do not appear in `t` itself
/// (e.g. when `x = "ab"` was asserted, `known` must contain `"ab"`).
pub fn normal_form(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    t: TermId,
) -> Vec<TermId> {
    let mut flat = Vec::new();
    flatten(terms, t, &mut flat);

    // Build the authoritative reverse map from ALL known string terms so rep()
    // reflects global EqualityEngine merges (not just the atoms in this concat).
    let mut node_of = build_node_of(terms, eq, known);

    // Also ensure every atom we just flattened is in the map (covers the case
    // where `known` was not yet updated to include a fresh atom).
    for &a in &flat {
        let n = eq.intern(a);
        let root = eq.find(n);
        let is_const = matches!(terms.term_node(a), TermNode::Const { val: ConstVal::String(_), .. });
        match node_of.get(&root).copied() {
            None => {
                node_of.insert(root, a);
            }
            Some(prev) => {
                let prev_is_const = matches!(
                    terms.term_node(prev),
                    TermNode::Const { val: ConstVal::String(_), .. }
                );
                if is_const && !prev_is_const {
                    node_of.insert(root, a);
                }
            }
        }
    }

    let mut out: Vec<TermId> = Vec::new();
    for a in flat {
        let r = rep(eq, &node_of, a);
        if let Some(s) = terms.string_const_value(r) {
            let s = s.to_owned();
            if s.is_empty() {
                continue; // drop ""
            }
            // Try to fold into the preceding literal.
            if let Some(&last) = out.last() {
                if let Some(ls) = terms.string_const_value(last) {
                    let merged = format!("{ls}{s}");
                    let m = terms.mk_string_const(&merged);
                    *out.last_mut().unwrap() = m;
                    continue;
                }
            }
        }
        out.push(r);
    }
    out
}

/// Compute a "deep" normal form that recursively expands class representatives
/// that are concat terms.
///
/// Unlike `normal_form`, this function handles the case where a variable `x` is
/// merged in the EqualityEngine with a concat term `"a"++y`: after `rep(x)` returns
/// `"a"++y`, we further flatten and recurse so the result is `["a", y]` rather
/// than the opaque `[x]` or `["a"++y]`.
///
/// Used for disequality checking (Task 14) where we need to detect that both sides
/// of an asserted disequality represent the same word.
pub fn deep_normal_form(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    t: TermId,
) -> Vec<TermId> {
    // First compute the regular normal form.
    let nf = normal_form(terms, eq, known, t);
    // If any atom in the normal form is itself a concat (because rep() substituted
    // a variable with a concat-valued class member), recursively expand it.
    let needs_expansion = nf.iter().any(|&a| {
        matches!(
            terms.term_node(a),
            TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), .. }
        )
    });
    if !needs_expansion {
        return nf;
    }
    // Expand each atom: recursively compute the NF of any concat-rep atoms.
    let mut out = Vec::new();
    for a in nf {
        if matches!(
            terms.term_node(a),
            TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), .. }
        ) {
            // Recursively expand (one level: concat atoms in `known` should not
            // themselves have concat reps since we build `known` from problem terms).
            let sub = normal_form(terms, eq, known, a);
            out.extend(sub);
        } else {
            out.push(a);
        }
    }
    // Fold adjacent string literals in the final result.
    let mut folded = Vec::new();
    for a in out {
        if let Some(s) = terms.string_const_value(a) {
            let s = s.to_owned();
            if s.is_empty() {
                continue;
            }
            if let Some(&last) = folded.last() {
                if let Some(ls) = terms.string_const_value(last) {
                    let merged = format!("{ls}{s}");
                    let m = terms.mk_string_const(&merged);
                    *folded.last_mut().unwrap() = m;
                    continue;
                }
            }
        }
        folded.push(a);
    }
    folded
}

/// Returns `true` iff `a` and `b` are in the same EqualityEngine class.
///
/// This is the canonical check for string-theory conflict detection (Task 11/14).
#[allow(dead_code)] // used in Task 11/14
pub fn atoms_equal(eq: &mut EqualityEngine, a: TermId, b: TermId) -> bool {
    let na = eq.intern(a);
    let nb = eq.intern(b);
    eq.are_equal(na, nb)
}

/// Recursively flatten a (possibly nested) `str.++` into its atom leaves.
fn flatten(terms: &Context, t: TermId, out: &mut Vec<TermId>) {
    match terms.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => {
            let kids: Vec<TermId> = terms.children(*args).to_vec();
            for k in kids {
                flatten(terms, k, out);
            }
        }
        _ => out.push(t),
    }
}

#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_theory::types::EqJust;
    use shinri_theory::EqualityEngine;
    use shinri_core::Lit;
    use shinri_core::Var;

    use crate::normalize::{atoms_equal, normal_form};

    /// Helper: build an asserted justification for use in merge calls.
    fn just(seed: u32) -> EqJust {
        EqJust::Asserted(Lit::new(Var::new(seed), true))
    }

    #[test]
    fn flattens_nested_concat_and_folds_literals() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let ab = ctx.mk_string_const("ab");
        let cd = ctx.mk_string_const("cd");
        let inner = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ab, cd])
            .unwrap();
        let outer = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, inner])
            .unwrap();
        let mut eq = EqualityEngine::default();
        // known = all string-sorted terms visible to the solver
        let known = vec![x, ab, cd];
        let nf = normal_form(&mut ctx, &mut eq, &known, outer);
        // x ++ "ab" ++ "cd"  ==  x ++ "abcd"  (literals folded)
        assert_eq!(nf.len(), 2);
        assert_eq!(ctx.string_const_value(nf[1]), Some("abcd"));
    }

    /// Discriminating test: rep() must return the CONSTANT "ab" for variable x
    /// when x = "ab" was merged in the EqualityEngine.
    ///
    /// This test catches the original bug where `node_of` was built only from
    /// the atoms in the concat call, causing rep(x) to return x instead of "ab".
    #[test]
    fn rep_reflects_global_merge_prefers_constant() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();

        // Build: string var x, string var y, string literal "ab"
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let y = {
            let s = ctx.declare_fun("y", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let ab = ctx.mk_string_const("ab");

        // Intern x and "ab" in the EqualityEngine and MERGE them (x = "ab").
        let mut eq = EqualityEngine::default();
        let nx = eq.intern(x);
        let nab = eq.intern(ab);
        eq.merge(nx, nab, just(1)).unwrap();

        // Build the concatenation x ++ y
        let concat = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();

        // `known` includes "ab" (mirrors how StrSolver.str_terms collects all terms).
        let known = vec![x, y, ab];

        let nf = normal_form(&mut ctx, &mut eq, &known, concat);

        // After the fix: nf[0] must be the CONSTANT "ab", not the variable x.
        // This fails against the old code (which returned x) and passes after the fix.
        assert_eq!(
            nf.len(),
            2,
            "normal form of x++y should have 2 atoms (neither is empty)"
        );
        assert_eq!(
            ctx.string_const_value(nf[0]),
            Some("ab"),
            "rep(x) must return the constant \"ab\" (x was merged with \"ab\")"
        );
        // nf[1] should be y (no merge for y)
        assert_eq!(
            nf[1], y,
            "rep(y) should be y (no merge)"
        );
    }

    /// atoms_equal returns true iff two terms share an EqualityEngine class.
    #[test]
    fn atoms_equal_reflects_merges() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x_ae", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let ab = ctx.mk_string_const("ab_ae");

        let mut eq = EqualityEngine::default();

        // Before merge: not equal
        assert!(!atoms_equal(&mut eq, x, ab));

        // After merge: equal
        let nx = eq.intern(x);
        let nab = eq.intern(ab);
        eq.merge(nx, nab, just(2)).unwrap();

        assert!(atoms_equal(&mut eq, x, ab));
    }
}
