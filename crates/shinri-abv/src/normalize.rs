//! Normalize array equality/disequality atoms to pairwise BINARY equalities.
//!
//! SMT-LIB admits n-ary `(= x1 ... xn)` and `(distinct x1 ... xn)`. The QF_ABV
//! abstraction mints ONE Bool eq-proxy per array atom and interprets it with
//! EQUALITY semantics — which is wrong for `distinct` (it would force agreement)
//! and lossy for n-ary atoms (it drops the 3rd+ operand). This pass rewrites every
//! ARRAY-sorted `Eq`/`Distinct` node into a binary-eq Bool term BEFORE collection
//! and abstraction, so the proxy + extensionality eq-semantics are always correct:
//!
//!   * `(= x1 ... xn)`        → `(and (= x1 x2) (= x2 x3) ...)`  (adjacent chain;
//!     equivalent to all-pairs for `=`, and minimal)
//!   * `(distinct x1 ... xn)` → `(and (not (= xi xj)) for all i<j)`  (ALL C(n,2)
//!     pairs — `distinct` is pairwise-distinct, a chain would be unsound)
//!   * binary `(= a b)`        → unchanged
//!   * binary `(distinct a b)` → `(not (= a b))`
//!
//! After the rewrite every array atom reaching `collect`/`abstraction` is a binary
//! `Eq` (possibly under `Not`/`And`), so distinctness is enforced: the skeleton
//! forces the proxy FALSE via the `Not`, triggering the witness-disequality lemma.
//!
//! Only ARRAY-sorted operands are touched; BV/Bool `=`/`distinct` are left intact.
//! The walk is memoized over the shared DAG.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};

/// True if `t` has an `(Array _ _)` sort.
fn is_array_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::Array(_, _))
}

/// Rewrite array `Eq`/`Distinct` atoms in each assertion to pairwise binary eqs.
/// Non-array atoms and all other nodes are structurally preserved (and shared).
pub fn normalize_array_atoms(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect()
}

fn rewrite(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&m) = memo.get(&t) {
        return m;
    }
    let (op, kids) = match ctx.term_node(t) {
        TermNode::App { op, args, .. } => (*op, ctx.children(*args).to_vec()),
        TermNode::Const { .. } => {
            memo.insert(t, t);
            return t;
        }
    };

    // First rewrite children (so any nested array atom is normalized too).
    let new_kids: Vec<TermId> = kids.iter().map(|&k| rewrite(ctx, k, memo)).collect();

    // Is this an array-sorted (dis)equality? (Operands share one sort, so the
    // first child's sort decides.)
    let is_array_atom = matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct))
        && new_kids.first().is_some_and(|&k| is_array_sorted(ctx, k));

    let rebuilt = if is_array_atom {
        desugar_array_atom(ctx, op, &new_kids)
    } else if new_kids == kids {
        t
    } else {
        ctx.mk_app(op, &new_kids)
            .expect("normalization preserves sorts")
    };
    memo.insert(t, rebuilt);
    rebuilt
}

/// Desugar a (possibly n-ary) array `Eq`/`Distinct` over `operands` into a Bool
/// term built only from binary `(= ai aj)` (under `Not`/`And`).
fn desugar_array_atom(ctx: &mut Context, op: Op, operands: &[TermId]) -> TermId {
    let is_eq = matches!(op, Op::Builtin(BuiltinOp::Eq));
    if is_eq {
        // Adjacent chain: (and (= x1 x2) (= x2 x3) ...). Binary stays a lone eq.
        let pairs: Vec<TermId> = operands
            .windows(2)
            .map(|w| ctx.mk_eq(w[0], w[1]).expect("array eq is well-sorted"))
            .collect();
        conjoin(ctx, pairs)
    } else {
        // distinct: (and (not (= xi xj)) for all i<j) — ALL pairs.
        let mut neqs: Vec<TermId> = Vec::new();
        for i in 0..operands.len() {
            for j in (i + 1)..operands.len() {
                let eq = ctx
                    .mk_eq(operands[i], operands[j])
                    .expect("array eq well-sorted");
                let neq = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Not), &[eq])
                    .expect("not of bool");
                neqs.push(neq);
            }
        }
        conjoin(ctx, neqs)
    }
}

/// Conjoin a non-empty list of Bool terms. A single element is returned as-is
/// (no redundant `And`); two-or-more become one n-ary `And`. An empty list cannot
/// occur (operands.len() >= 2 always yields >= 1 pair).
fn conjoin(ctx: &mut Context, terms: Vec<TermId>) -> TermId {
    debug_assert!(
        !terms.is_empty(),
        "(dis)equality has >=2 operands => >=1 pair"
    );
    if terms.len() == 1 {
        return terms[0];
    }
    ctx.mk_app(Op::Builtin(BuiltinOp::And), &terms)
        .expect("And over bools")
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Op;

    fn arr(ctx: &mut Context) -> shinri_core::SortId {
        let i = ctx.bv_sort(1);
        let e = ctx.bv_sort(8);
        ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, n: &str, s: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    /// Count distinct binary array-eq atoms reachable from `t`.
    fn binary_array_eqs(ctx: &Context, t: TermId) -> Vec<(TermId, TermId)> {
        let mut out = Vec::new();
        let mut seen = rustc_hash::FxHashSet::default();
        let mut stack = vec![t];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if let TermNode::App { op, args, .. } = ctx.term_node(x) {
                let kids = ctx.children(*args).to_vec();
                if matches!(op, Op::Builtin(BuiltinOp::Eq))
                    && kids.len() == 2
                    && is_array_sorted(ctx, kids[0])
                {
                    out.push((kids[0], kids[1]));
                }
                for k in kids {
                    stack.push(k);
                }
            }
        }
        out
    }

    #[test]
    fn binary_eq_unchanged() {
        let mut ctx = Context::new();
        let s = arr(&mut ctx);
        let a = uconst(&mut ctx, "a", s);
        let b = uconst(&mut ctx, "b", s);
        let atom = ctx.mk_eq(a, b).unwrap();
        let out = normalize_array_atoms(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "binary array = stays the same term");
    }

    #[test]
    fn binary_distinct_becomes_not_eq() {
        let mut ctx = Context::new();
        let s = arr(&mut ctx);
        let a = uconst(&mut ctx, "a", s);
        let b = uconst(&mut ctx, "b", s);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b])
            .unwrap();
        let out = normalize_array_atoms(&mut ctx, &[atom]);
        // Result is (not (= a b)).
        match ctx.term_node(out[0]) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Not),
                args,
                ..
            } => {
                let kids = ctx.children(*args).to_vec();
                let eq = ctx.mk_eq(a, b).unwrap();
                assert_eq!(kids, vec![eq]);
            }
            other => panic!("expected (not (= a b)), got {other:?}"),
        }
    }

    #[test]
    fn nary_eq_becomes_adjacent_chain() {
        let mut ctx = Context::new();
        let s = arr(&mut ctx);
        let a = uconst(&mut ctx, "a", s);
        let b = uconst(&mut ctx, "b", s);
        let c = uconst(&mut ctx, "c", s);
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[a, b, c]).unwrap();
        let out = normalize_array_atoms(&mut ctx, &[atom]);
        let eqs = binary_array_eqs(&ctx, out[0]);
        let ab = ctx.mk_eq(a, b).unwrap();
        let bc = ctx.mk_eq(b, c).unwrap();
        assert!(eqs.contains(&(a, b)) && eqs.contains(&(b, c)));
        // Top is an And over exactly the chain pairs.
        match ctx.term_node(out[0]) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::And),
                args,
                ..
            } => {
                let kids = ctx.children(*args).to_vec();
                assert_eq!(kids, vec![ab, bc]);
            }
            other => panic!("expected (and (= a b) (= b c)), got {other:?}"),
        }
    }

    #[test]
    fn nary_distinct_becomes_all_pairs_negated() {
        let mut ctx = Context::new();
        let s = arr(&mut ctx);
        let a = uconst(&mut ctx, "a", s);
        let b = uconst(&mut ctx, "b", s);
        let c = uconst(&mut ctx, "c", s);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, c])
            .unwrap();
        let out = normalize_array_atoms(&mut ctx, &[atom]);
        // Expect (and (not(=a b)) (not(=a c)) (not(=b c))).
        let eqs = binary_array_eqs(&ctx, out[0]);
        assert!(eqs.contains(&(a, b)) && eqs.contains(&(a, c)) && eqs.contains(&(b, c)));
        match ctx.term_node(out[0]) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::And),
                args,
                ..
            } => {
                assert_eq!(ctx.children(*args).len(), 3, "C(3,2) = 3 pairs");
            }
            other => panic!("expected 3-conjunct And, got {other:?}"),
        }
    }

    #[test]
    fn non_array_eq_untouched() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let x = uconst(&mut ctx, "x", s8);
        let y = uconst(&mut ctx, "y", s8);
        let z = uconst(&mut ctx, "z", s8);
        // n-ary BV equality must NOT be rewritten.
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y, z]).unwrap();
        let out = normalize_array_atoms(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom]);
    }

    #[test]
    fn nested_array_distinct_under_not_is_rewritten() {
        // (not (distinct a b c)) — the inner distinct is array-sorted and must be
        // desugared even though it is under a Not.
        let mut ctx = Context::new();
        let s = arr(&mut ctx);
        let a = uconst(&mut ctx, "a", s);
        let b = uconst(&mut ctx, "b", s);
        let c = uconst(&mut ctx, "c", s);
        let dist = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, c])
            .unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[dist]).unwrap();
        let out = normalize_array_atoms(&mut ctx, &[atom]);
        let eqs = binary_array_eqs(&ctx, out[0]);
        assert!(eqs.contains(&(a, b)) && eqs.contains(&(a, c)) && eqs.contains(&(b, c)));
    }
}
