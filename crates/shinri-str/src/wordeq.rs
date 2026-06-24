use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::EqLeaf;
use shinri_theory::EqualityEngine;

pub enum StepResult {
    Done,
    Conflict(Vec<EqLeaf>),
    Split(Vec<TermId>),
}

/// Mint a fresh string constant `!strk<N>` and return its term ID.
pub fn fresh_str(terms: &mut Context, ctr: &mut u32) -> TermId {
    let name = format!("!strk{}", *ctr);
    *ctr += 1;
    let str_s = terms.string_sort();
    let sym = terms.declare_fun(&name, &[], str_s);
    terms.mk_app(Op::Uninterpreted(sym), &[]).expect("well-sorted")
}

/// Build `(str.len t)`.
pub fn len_of(terms: &mut Context, t: TermId) -> TermId {
    terms
        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[t])
        .expect("well-sorted")
}

/// Build the three F-split atoms for heads `a`, `b` (at least one a variable).
///
/// Returns `[len_eq, a_pref, b_pref]` where:
///   `len_eq`  = `(= (str.len a) (str.len b))`
///   `a_pref`  = `(= a (str.++ b z1))`   for a fresh remainder `z1`
///   `b_pref`  = `(= b (str.++ a z2))`   for a fresh remainder `z2`
///
/// Soundness: the disjunction `len_eq ∨ a_pref ∨ b_pref` is valid over string
/// algebra given the triggering word equation (Nielsen transformation: if two words
/// starting with `a` resp. `b` are equal, one head is a prefix of the other or
/// they have equal length). The clause is learned as a persistent split (mirroring
/// the arrays ROW-2 pattern); the fresh z1/z2 have no other constraints, so the
/// clause is always satisfiable and cannot cause spurious UNSAT.
pub fn fsplit_atoms(terms: &mut Context, a: TermId, b: TermId, ctr: &mut u32) -> Vec<TermId> {
    let la = len_of(terms, a);
    let lb = len_of(terms, b);
    let len_eq = terms.mk_eq(la, lb).expect("well-sorted");
    let z1 = fresh_str(terms, ctr);
    let bc = terms
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[b, z1])
        .expect("well-sorted");
    let a_pref = terms.mk_eq(a, bc).expect("well-sorted");
    let z2 = fresh_str(terms, ctr);
    let ac = terms
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, z2])
        .expect("well-sorted");
    let b_pref = terms.mk_eq(b, ac).expect("well-sorted");
    vec![len_eq, a_pref, b_pref]
}

/// Returns the two children of an `Eq` atom.
pub fn sides(terms: &Context, atom: TermId) -> (TermId, TermId) {
    match terms.term_node(atom) {
        TermNode::App { op: Op::Builtin(BuiltinOp::Eq), args, .. } => {
            let ch = terms.children(*args);
            (ch[0], ch[1])
        }
        _ => panic!("sides: expected Eq atom"),
    }
}

/// Compare two atoms for definite equality: same TermId, same literal string
/// value, or same EqualityEngine equivalence class.
fn same(terms: &mut Context, eq: &mut EqualityEngine, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    if let (Some(x), Some(y)) = (terms.string_const_value(a), terms.string_const_value(b)) {
        return x == y;
    }
    let an = eq.intern(a);
    let bn = eq.intern(b);
    eq.are_equal(an, bn)
}

/// Resolve one word equation between two normal forms.
///
/// - Strips equal leading and trailing atoms (sound cancellation in free monoid).
/// - If both sides are fully consumed after stripping → Done (trivially satisfied).
/// - If both sides have constant heads whose first characters differ → Conflict.
/// - If one side is empty and the other still contains a non-empty constant → Conflict.
/// - If the residual has a variable head and the pair has not been split yet →
///   emits an F-split (three-disjunct length-aware alignment).
/// - If the pair was already split (dedup) → Done (wait for SAT to case-split).
///
/// `fresh_ctr` is used to mint fresh string variables for the split remainders.
/// `emitted` deduplicates splits to prevent re-emitting the same pair (termination).
pub fn resolve_equation(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    lhs: &[TermId],
    rhs: &[TermId],
    just: Vec<EqLeaf>,
    fresh_ctr: &mut u32,
    emitted: &mut FxHashSet<(TermId, TermId)>,
) -> StepResult {
    let (mut i, mut j) = (0usize, 0usize);
    let (mut le, mut re) = (lhs.len(), rhs.len());

    // Strip equal heads.
    while i < le && j < re && same(terms, eq, lhs[i], rhs[j]) {
        i += 1;
        j += 1;
    }

    // Strip equal tails.
    while le > i && re > j && same(terms, eq, lhs[le - 1], rhs[re - 1]) {
        le -= 1;
        re -= 1;
    }

    // Both exhausted: equation holds trivially.
    if i == le && j == re {
        return StepResult::Done;
    }

    // Both sides non-empty: check for constant-head character mismatch.
    // When both heads are string constants, strip the longest common character
    // prefix. If after stripping both have remaining characters with different
    // first chars, it is a genuine contradiction in the free monoid.
    if i < le && j < re {
        if let (Some(a_str), Some(b_str)) =
            (terms.string_const_value(lhs[i]).map(str::to_owned),
             terms.string_const_value(rhs[j]).map(str::to_owned))
        {
            // Walk character by character to find the first mismatch.
            let mut a_chars = a_str.chars();
            let mut b_chars = b_str.chars();
            loop {
                match (a_chars.next(), b_chars.next()) {
                    (Some(ca), Some(cb)) if ca != cb => {
                        return StepResult::Conflict(just);
                    }
                    (Some(_), Some(_)) => {} // common prefix char, keep walking
                    // One constant is a prefix of the other or they are equal;
                    // cannot determine a conflict here without knowing what follows.
                    // Fall through to the variable-head case.
                    _ => break,
                }
            }
        }
    }

    // One side empty, other has a non-empty constant remaining: contradiction.
    if (i == le) != (j == re) {
        let rest = if i == le { &rhs[j..re] } else { &lhs[i..le] };
        if rest
            .iter()
            .any(|&a| terms.string_const_value(a).map_or(false, |s| !s.is_empty()))
        {
            return StepResult::Conflict(just);
        }
    }

    // Residual has at least one variable head: emit an F-split if not yet emitted.
    if i < le && j < re {
        let (ha, hb) = (lhs[i], rhs[j]);
        let var_head = terms.string_const_value(ha).is_none()
            || terms.string_const_value(hb).is_none();
        if var_head {
            // Canonical (unordered) key for dedup.
            let key = if ha.index() <= hb.index() {
                (ha, hb)
            } else {
                (hb, ha)
            };
            if emitted.insert(key) {
                return StepResult::Split(fsplit_atoms(terms, ha, hb, fresh_ctr));
            }
            // Already split this pair; wait for SAT to case-split.
            return StepResult::Done;
        }
    }

    StepResult::Done
}

#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};
    use crate::StrSolver;
    use rustc_hash::FxHashSet;
    use crate::wordeq::{resolve_equation, StepResult};

    // Helper: make a string variable term in `ctx`.
    fn mk_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let str_s = ctx.string_sort();
        let s = ctx.declare_fun(name, &[], str_s);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    // ── Non-conflict case 1: prefix-of-constant ───────────────────────────────
    // Normal forms: lhs = ["ab", X],  rhs = ["abc", Y]
    // After stripping: both heads are constants "ab" vs "abc".
    // "ab" is a proper prefix of "abc" — no character mismatch, just one is
    // shorter.  This is satisfiable (X = "c" ++ Y), so resolve_equation MUST
    // return Done (constant heads → no F-split needed), not Conflict.
    #[test]
    fn prefix_of_constant_is_done_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = mk_var(&mut ctx, "x_pfx");
        let y = mk_var(&mut ctx, "y_pfx");
        let ab  = ctx.mk_string_const("ab");
        let abc = ctx.mk_string_const("abc");
        let lhs = [ab,  x];
        let rhs = [abc, y];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(&mut ctx, &mut eq, &lhs, &rhs, vec![], &mut ctr, &mut emitted);
        assert!(
            matches!(result, StepResult::Done),
            "prefix-of-constant residual must be Done (satisfiable: X = \"c\" ++ Y)"
        );
    }

    // ── Non-conflict case 2: variable head ───────────────────────────────────
    // Normal forms: lhs = [X, "a"],  rhs = ["b", Y]
    // After stripping: lhs head is variable X — emits an F-split on the first
    // call, then Done on the second (dedup prevents re-emission).
    #[test]
    fn variable_head_is_done_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = mk_var(&mut ctx, "x_vh");
        let y = mk_var(&mut ctx, "y_vh");
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let lhs = [x, a];
        let rhs = [b, y];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        // First call: emits F-split (not Conflict).
        let result = resolve_equation(&mut ctx, &mut eq, &lhs, &rhs, vec![], &mut ctr, &mut emitted);
        assert!(
            matches!(result, StepResult::Split(_) | StepResult::Done),
            "variable-headed residual must NOT be Conflict (X could equal \"b\" ++ ...)"
        );
        assert!(
            !matches!(result, StepResult::Conflict(_)),
            "variable-headed residual must NOT be Conflict"
        );
    }

    // ── Non-conflict case 3: both sides fully consumed after strip ────────────
    // Normal forms: lhs = [X, "a"],  rhs = [X, "a"]
    // Both heads are equal (same TermId X), both tails "a" are equal.
    // After stripping the solver exhausts both sides — trivially satisfied.
    // Must return Done.
    #[test]
    fn equal_sides_fully_consumed_is_done() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = mk_var(&mut ctx, "x_eq");
        let a = ctx.mk_string_const("a");
        let lhs = [x, a];
        let rhs = [x, a]; // identical slices
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(&mut ctx, &mut eq, &lhs, &rhs, vec![], &mut ctr, &mut emitted);
        assert!(
            matches!(result, StepResult::Done),
            "fully-consumed (trivially equal) sides must be Done"
        );
    }

    // ── Non-conflict case 4: one side empty, other is all-variable ────────────
    // Normal forms: lhs = [],  rhs = [Y]
    // lhs is exhausted; rhs has only a variable Y.  Y = "" is a valid
    // assignment, so this is NOT a conflict.  Must return Done.
    #[test]
    fn empty_vs_single_variable_is_done_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let y = mk_var(&mut ctx, "y_emp");
        let lhs: [shinri_core::TermId; 0] = [];
        let rhs = [y];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(&mut ctx, &mut eq, &lhs, &rhs, vec![], &mut ctr, &mut emitted);
        assert!(
            matches!(result, StepResult::Done),
            "empty lhs vs single-variable rhs must be Done (Y could be \"\")"
        );
    }

    // ── Task 12: variable-headed word equation emits an F-split ──────────────
    // x ++ "a"  =  "b" ++ y  with x,y variables → an F-split is emitted (not
    // immediate sat/conflict).
    #[test]
    fn variable_head_emits_fsplit() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, a]).unwrap();
        let r = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[b, y]).unwrap();
        let atom = ctx.mk_eq(l, r).unwrap();
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        s.test_force_eq_true(atom);
        let mut saw_split = false;
        for _ in 0..32 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split(atoms) => {
                    if atoms.len() >= 2 {
                        saw_split = true;
                        break;
                    }
                }
                TCheck::Sat => break,
                TCheck::Conflict(_) => break,
            }
        }
        assert!(saw_split, "a variable-headed word equation must emit a multi-atom F-split");
    }

    // ── Positive control: conflict still detected ─────────────────────────────
    // "ab" ++ x  =  "ac" ++ x   is UNSAT by prefix mismatch (b != c at index 1).
    #[test]
    fn constant_prefix_mismatch_is_conflict() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = { let s = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap() };
        let ab = ctx.mk_string_const("ab");
        let ac = ctx.mk_string_const("ac");
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ab, x]).unwrap();
        let r = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ac, x]).unwrap();
        let atom = ctx.mk_eq(l, r).unwrap();

        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        // Simulate the SAT layer asserting the equality true:
        s.test_force_eq_true(atom);
        // Drain length axioms, then expect a conflict.
        loop {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split(_) => continue,
                TCheck::Conflict(_) => break,
                TCheck::Sat => panic!("expected conflict on prefix mismatch"),
            }
        }
    }
}
