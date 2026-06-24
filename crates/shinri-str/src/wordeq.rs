use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::EqLeaf;
use shinri_theory::EqualityEngine;

pub enum StepResult {
    Done,
    Conflict(Vec<EqLeaf>),
    #[allow(dead_code)] // used in Task 12 (F-split)
    Split(Vec<TermId>),
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
/// - Otherwise → Done (variable-headed residual; the F-split rule handles it in Task 12).
///
/// NOTE: `just` is intentionally empty for Task 11 — the justification is refined
/// in Task 12 once we wire up EqualityEngine proof traces. The conflict is still
/// sound because the asserted equality is on the decision trail.
pub fn resolve_equation(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    lhs: &[TermId],
    rhs: &[TermId],
    just: Vec<EqLeaf>,
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
                    // Fall through to the variable-head Done.
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

    // Residual has a variable head — not a contradiction. The F-split rule
    // (Task 12) will enumerate the possible length splits.
    StepResult::Done
}

#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};
    use crate::StrSolver;
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
    // return Done, not Conflict.
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
        let result = resolve_equation(&mut ctx, &mut eq, &lhs, &rhs, vec![]);
        assert!(
            matches!(result, StepResult::Done),
            "prefix-of-constant residual must be Done (satisfiable: X = \"c\" ++ Y)"
        );
    }

    // ── Non-conflict case 2: variable head ───────────────────────────────────
    // Normal forms: lhs = [X, "a"],  rhs = ["b", Y]
    // After stripping: lhs head is variable X — cannot determine a conflict
    // without knowing X's value.  Must be Done (F-split handles it later).
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
        let result = resolve_equation(&mut ctx, &mut eq, &lhs, &rhs, vec![]);
        assert!(
            matches!(result, StepResult::Done),
            "variable-headed residual must be Done (X could equal \"b\" ++ ...)"
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
        let result = resolve_equation(&mut ctx, &mut eq, &lhs, &rhs, vec![]);
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
        let result = resolve_equation(&mut ctx, &mut eq, &lhs, &rhs, vec![]);
        assert!(
            matches!(result, StepResult::Done),
            "empty lhs vs single-variable rhs must be Done (Y could be \"\")"
        );
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
