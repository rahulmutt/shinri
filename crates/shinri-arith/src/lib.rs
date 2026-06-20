//! shinri-arith: a Dutertre–de Moura simplex theory solver for QF_LRA.
//! Implements `shinri_theory::TheorySolver`; depends only on core + theory.

pub mod bounds;
pub mod diseq;
pub mod encode;
pub mod farkas;
pub mod model;
pub mod normalize;
pub mod simplex;
pub mod tableau;
pub mod vars;

pub use vars::ArithVar;

use crate::bounds::{BoundKind, Bounds, TightenResult};
use crate::encode::AtomEncoding;
use crate::normalize::{normalize_atom, LinComb, Rel};
use crate::tableau::Tableau;
use crate::vars::VarStore;
use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_num::{DeltaRational, Rational};
use shinri_theory::types::EqLeaf;
use shinri_theory::{Effort, Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct Arith {
    vars: VarStore,
    tableau: Tableau,
    bounds: Bounds,
    /// Assignment β(v) for every ArithVar (DeltaRational).
    value: Vec<DeltaRational>,
    /// Per SAT-var encoding (indexed by Var::index()).
    enc: Vec<Option<AtomEncoding>>,
    /// Asserted disequalities `(var, rhs, lit)` — repaired in `check` (Task 12).
    diseqs: crate::diseq::DiseqStore,
    level: usize,
}

impl Arith {
    fn grow_value(&mut self) {
        while self.value.len() < self.vars.len() {
            self.value
                .push(DeltaRational::from_rational(Rational::zero()));
        }
        self.bounds.ensure(self.vars.len());
    }

    /// Reduce a normalized atom to a *bound on one variable*. For a single-term
    /// comb `{x:c}` the bound is on `x` (rhs divided by c, kind flipped if c<0);
    /// for ≥2-term combs a slack var is interned and defined as a tableau row.
    fn atom_var_and_rhs(&mut self, comb: &LinComb, rhs: &Rational) -> (ArithVar, Rational, bool) {
        // returns (var, scaled_rhs, flipped)  where flipped means c < 0.
        if comb.0.len() == 1 {
            let (x, c) = &comb.0[0];
            let scaled = rhs.clone() / c.clone();
            (*x, scaled, c.is_negative())
        } else {
            let s = self.vars.slack_var(comb);
            self.tableau.define_slack(s, comb);
            (s, rhs.clone(), false)
        }
    }

    fn build_encoding(&mut self, n: &crate::normalize::Normalized) -> AtomEncoding {
        if n.comb.0.is_empty() {
            // Constant relation: 0 (rel) rhs is decided now.
            let truth = match n.rel {
                Rel::Le => Rational::zero() <= n.rhs,
                Rel::Lt => Rational::zero() < n.rhs,
                Rel::Eq => Rational::zero() == n.rhs,
            };
            return AtomEncoding::Const(truth);
        }
        let (var, rhs, flipped) = self.atom_var_and_rhs(&n.comb, &n.rhs);
        let zero = Rational::zero();
        let one = Rational::one();
        match n.rel {
            Rel::Eq => AtomEncoding::Eq {
                var,
                rhs: DeltaRational::new(rhs, zero),
            },
            Rel::Le | Rel::Lt => {
                // base (un-flipped) positive bound:
                let (pos_kind, pos_k, neg_kind, neg_k) = match n.rel {
                    // x <= rhs : pos Upper (rhs,0); neg Lower (rhs,+1)
                    Rel::Le => (
                        BoundKind::Upper,
                        zero.clone(),
                        BoundKind::Lower,
                        one.clone(),
                    ),
                    // x < rhs : pos Upper (rhs,-1); neg Lower (rhs,0)
                    Rel::Lt => (
                        BoundKind::Upper,
                        -one.clone(),
                        BoundKind::Lower,
                        zero.clone(),
                    ),
                    _ => unreachable!(),
                };
                let (mut pk, mut pkk, mut nk, mut nkk) = (pos_kind, pos_k, neg_kind, neg_k);
                if flipped {
                    // dividing by a negative coefficient flips ≤ into ≥: swap
                    // the kinds and negate the infinitesimals accordingly.
                    std::mem::swap(&mut pk, &mut nk);
                    pkk = -pkk;
                    nkk = -nkk;
                }
                AtomEncoding::Ineq {
                    var,
                    pos: (pk, DeltaRational::new(rhs.clone(), pkk)),
                    neg: (nk, DeltaRational::new(rhs, nkk)),
                }
            }
        }
    }

    /// β-update: set nonbasic `v` to `val`, propagating the delta to all basics.
    fn update(&mut self, v: ArithVar, val: DeltaRational) {
        let delta = val.clone() - self.value[v.index()].clone();
        let affected: Vec<ArithVar> = self
            .tableau
            .basic
            .iter()
            .copied()
            .filter(|b| !self.tableau.row(*b).coeff(v).is_zero())
            .collect();
        for b in affected {
            let a = self.tableau.row(b).coeff(v);
            let cur = self.value[b.index()].clone();
            self.value[b.index()] = cur + delta.scale(&a);
        }
        self.value[v.index()] = val;
    }

    fn apply_bound(
        &mut self,
        var: ArithVar,
        kind: BoundKind,
        val: DeltaRational,
        lit: Lit,
    ) -> Option<Vec<EqLeaf>> {
        match self.bounds.tighten(var, kind, val.clone(), lit) {
            TightenResult::Redundant => None,
            TightenResult::Conflict { other } => {
                Some(vec![EqLeaf::Asserted(lit), EqLeaf::Asserted(other)])
            }
            TightenResult::Tightened => {
                // Maintain the DdM invariant for nonbasic vars: if the bound is
                // violated by the current value, move the value onto the bound.
                if !self.tableau.is_basic(var) {
                    let v = self.value[var.index()].clone();
                    let violated = match kind {
                        BoundKind::Lower => v < val,
                        BoundKind::Upper => v > val,
                    };
                    if violated {
                        self.update(var, val);
                    }
                }
                None
            }
        }
    }

    // -----------------------------------------------------------------------
    // Stubs for Tasks 9–13 (replaced later)
    // -----------------------------------------------------------------------

    fn check_full(&mut self) -> TCheck {
        use crate::simplex::{entering_for, first_violated_basic, Below};
        loop {
            let Some((basic, dir)) = first_violated_basic(&self.tableau, &self.bounds, &self.value)
            else {
                // Bounds feasible. Disequality repair (Task 12) runs here.
                return self.repair_diseqs();
            };
            let increase = dir == Below::Lower;
            match entering_for(&self.tableau, &self.bounds, &self.value, basic, increase) {
                Some(entering) => {
                    // Target = the violated bound of `basic`.
                    let target = match dir {
                        Below::Lower => self.bounds.lower(basic).unwrap().0.clone(),
                        Below::Upper => self.bounds.upper(basic).unwrap().0.clone(),
                    };
                    self.pivot_and_update(basic, entering, target);
                }
                None => {
                    // No candidate: Farkas conflict (Task 11).
                    return TCheck::Conflict(self.farkas_conflict(basic, dir));
                }
            }
        }
    }

    /// Move `entering` so that `basic` reaches `target`, then pivot the basis.
    fn pivot_and_update(&mut self, basic: ArithVar, entering: ArithVar, target: DeltaRational) {
        let a = self.tableau.row(basic).coeff(entering); // basic = ... + a*entering
        debug_assert!(!a.is_zero());
        // theta = (target - value[basic]) / a, applied to `entering`.
        let diff = target - self.value[basic.index()].clone();
        let theta = diff.scale(&a.recip());
        let new_entering = self.value[entering.index()].clone() + theta;
        self.update(entering, new_entering);
        self.tableau.pivot(basic, entering);
        debug_assert!(self.tableau_well_formed());
    }

    fn repair_diseqs(&mut self) -> TCheck {
        TCheck::Sat
    }

    fn farkas_conflict(&mut self, basic: ArithVar, dir: crate::simplex::Below) -> Vec<EqLeaf> {
        crate::farkas::conflict_lits(&self.tableau, &self.bounds, basic, dir)
            .into_iter()
            .map(EqLeaf::Asserted)
            .collect()
    }

    fn tableau_well_formed(&self) -> bool {
        true
    }

    fn build_model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn recompute_basic_values(&mut self) {
        // 1. Clamp nonbasic vars into restored bounds.
        let n = self.vars.len();
        for i in 0..n {
            let v = ArithVar(i as u32);
            if self.tableau.is_basic(v) {
                continue;
            }
            if let Some((lo, _)) = self.bounds.lower(v).cloned() {
                if self.value[i] < lo {
                    self.value[i] = lo;
                    continue;
                }
            }
            if let Some((hi, _)) = self.bounds.upper(v).cloned() {
                if self.value[i] > hi {
                    self.value[i] = hi;
                }
            }
        }
        // 2. Recompute every basic var from its row.
        // Collect (basic, [(j, coeff)]) pairs first to avoid holding a borrow on
        // self.tableau while we also need to read/write self.value.
        let basics: Vec<ArithVar> = self.tableau.basic.iter().copied().collect();
        for b in basics {
            let pairs: Vec<(ArithVar, Rational)> = {
                let row = self.tableau.row(b);
                row.vars().map(|j| (j, row.coeff(j))).collect()
            };
            let mut acc = DeltaRational::from_rational(Rational::zero());
            for (j, a) in pairs {
                acc = acc + self.value[j.index()].clone().scale(&a);
            }
            self.value[b.index()] = acc;
        }
    }
}

impl TheorySolver for Arith {
    const THEORY_ID: u16 = 2;

    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId) {
        let n = normalize_atom(cx.terms, &mut self.vars, atom);
        let enc = self.build_encoding(&n);
        let idx = v.index();
        if idx >= self.enc.len() {
            self.enc.resize_with(idx + 1, || None);
        }
        self.enc[idx] = Some(enc);
        self.grow_value();
    }

    fn assert(&mut self, _cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        let enc = self.enc[lit.var().index()].clone();
        match enc {
            None => None,
            Some(AtomEncoding::Const(truth)) => {
                // Asserting against a decided constant: conflict iff polarity disagrees.
                if truth == lit.is_positive() {
                    None
                } else {
                    Some(vec![EqLeaf::Asserted(lit)])
                }
            }
            Some(AtomEncoding::Ineq { var, pos, neg }) => {
                let (kind, val) = if lit.is_positive() { pos } else { neg };
                self.apply_bound(var, kind, val, lit)
            }
            Some(AtomEncoding::Eq { var, rhs }) => {
                if lit.is_positive() {
                    if let Some(cf) = self.apply_bound(var, BoundKind::Lower, rhs.clone(), lit) {
                        return Some(cf);
                    }
                    self.apply_bound(var, BoundKind::Upper, rhs, lit)
                } else {
                    self.diseqs.push(var, rhs, lit);
                    None
                }
            }
        }
    }

    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        None // spec §1 decision 3: check-only; propagate is a no-op.
    }

    fn check(&mut self, _cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        self.check_full() // Task 10
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
        unreachable!("arith emits conflicts directly as EqLeaf::Asserted; no lazy tags (spec §7)")
    }

    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        self.build_model(cx, m) // Task 13
    }

    fn push(&mut self) {
        self.level += 1;
        self.bounds.mark();
        self.diseqs.mark();
    }

    fn pop(&mut self, level: usize) {
        // absolute target level; restore bounds/diseqs/assignment (Task 9 refines).
        self.bounds.undo_to(level);
        self.diseqs.undo_to(level);
        self.recompute_basic_values();
        self.level = level;
    }
}

#[cfg(test)]
mod backtrack_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let s = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    #[test]
    fn assert_then_pop_is_consistent_again() {
        // x <= 1 ; push ; x >= 2 (conflict at check) ; pop ; check sat
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let one = ctx.mk_numeral(Rational::one(), ctx.real_sort());
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), ctx.real_sort());
        let le1 = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, one]).unwrap();
        let ge2 = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, two]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), le1);
        arith.new_var(&mut cx, Var::new(1), ge2);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.push();
        // the >= 2 conflicts directly at assert here (single var), so just exercise pop:
        let _ = arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.pop(0);
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}

#[cfg(test)]
mod check_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let s = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }
    fn num(ctx: &mut Context, n: i128) -> TermId {
        ctx.mk_numeral(Rational::from_int(n.into()), ctx.real_sort())
    }

    // Build: x + y <= 1 ; x >= 0 ; y >= 0  -> SAT
    //        plus  x + y >= 3              -> UNSAT
    fn setup(unsat: bool) -> bool {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let one = num(&mut ctx, 1);
        let zero = num(&mut ctx, 0);
        let three = num(&mut ctx, 3);
        let a = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap(); // x+y<=1
        let b = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero]).unwrap(); // x>=0
        let c = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[y, zero]).unwrap(); // y>=0
        let d = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[xy, three])
            .unwrap(); // x+y>=3

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        for (i, atom) in [a, b, c, d].iter().enumerate() {
            arith.new_var(&mut cx, Var::new(i as u32), *atom);
        }
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.assert(&mut cx, Lit::new(Var::new(2), true));
        if unsat {
            arith.assert(&mut cx, Lit::new(Var::new(3), true));
        }
        matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat)
    }

    #[test]
    fn feasible_system_is_sat() {
        assert!(setup(false));
    }

    #[test]
    fn infeasible_system_is_unsat() {
        assert!(!setup(true));
    }

    #[test]
    fn unsat_conflict_cites_participating_literals() {
        // Reuse the infeasible setup but capture the conflict leaves.
        use shinri_core::{BuiltinOp, Context, Op, Var};
        use shinri_theory::types::EqLeaf;
        use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xs = ctx.declare_fun("x", &[], real);
        let ys = ctx.declare_fun("y", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(ys), &[]).unwrap();
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let one = ctx.mk_numeral(Rational::one(), real);
        let three = ctx.mk_numeral(Rational::from_int(3i128.into()), real);
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap();
        let ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[xy, three])
            .unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), le);
        arith.new_var(&mut cx, Var::new(1), ge);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        match arith.check(&mut cx, Effort::Full) {
            TCheck::Conflict(leaves) => {
                assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(0), true))));
                assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(1), true))));
            }
            TCheck::Sat => panic!("expected conflict"),
        }
    }

    #[test]
    fn sat_requiring_a_pivot() {
        // x + y >= 2, no upper bounds: infeasible at the all-zero start (slack s=0 < 2),
        // so check_full MUST pivot to reach a feasible assignment (e.g. x=2, y=0).
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let two = num(&mut ctx, 2);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[xy, two]).unwrap(); // x+y >= 2
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), ge);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}

#[cfg(test)]
mod assert_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Lit, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::types::EqLeaf;
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn real_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let real = ctx.real_sort();
        let s = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    #[test]
    fn flipped_strict_lower_conflicts_with_upper_at_boundary() {
        // (> x 2)  must install a STRICT lower bound x>2 (Lower(2,+1)).
        // (<= x 2) installs Upper(2,0). Together UNSAT -> crossing conflict at assert.
        // With the encoding bug, (> x 2) installs x>=2 (Lower(2,0)) and there is NO conflict.
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let real = ctx.real_sort();
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[x, two]).unwrap(); // x > 2
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, two]).unwrap(); // x <= 2
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let va = Var::new(0);
        let vb = Var::new(1);
        {
            let mut cx = TheoryCtx {
                terms: &ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            arith.new_var(&mut cx, va, gt);
            arith.new_var(&mut cx, vb, le);
            assert!(arith.assert(&mut cx, Lit::new(va, true)).is_none()); // x>2 alone: ok
            let cf = arith.assert(&mut cx, Lit::new(vb, true)); // x<=2: crosses x>2
            let leaves = cf.expect("x>2 and x<=2 must conflict at the boundary");
            assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(va, true))));
            assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(vb, true))));
        }
    }

    #[test]
    fn contradictory_bounds_on_one_var_conflict_at_assert() {
        // x <= 1 (var A true) and x >= 2 (i.e. ¬(x <= 1)? no — use two atoms)
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let one = ctx.mk_numeral(Rational::one(), ctx.real_sort());
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), ctx.real_sort());
        let le1 = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, one]).unwrap(); // x <= 1
        let ge2 = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, two]).unwrap(); // x >= 2

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let va = Var::new(0);
        let vb = Var::new(1);
        {
            let mut cx = TheoryCtx {
                terms: &ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            arith.new_var(&mut cx, va, le1);
            arith.new_var(&mut cx, vb, ge2);
            // assert x <= 1
            assert!(arith.assert(&mut cx, Lit::new(va, true)).is_none());
            // assert x >= 2  -> crossing conflict
            let cf = arith.assert(&mut cx, Lit::new(vb, true));
            let leaves = cf.expect("expected conflict");
            assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(vb, true))));
            assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(va, true))));
        }
    }
}
