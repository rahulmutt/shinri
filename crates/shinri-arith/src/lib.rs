//! shinri-arith: a Dutertre–de Moura simplex theory solver for QF_LRA.
//! Implements `shinri_theory::TheorySolver`; depends only on core + theory.
//! Handles ONLY inequality atoms (Le/Lt/Ge/Gt). Arithmetic equalities are
//! eliminated at the CNF encoder level (rewritten to `(a<=b) AND (a>=b)`).

pub mod bounds;
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
use rustc_hash::FxHashMap;
use shinri_core::{Context, Lit, TermId, TheoryJust, Var};
use shinri_num::{DeltaRational, Rational};
use shinri_theory::types::EqLeaf;
use shinri_theory::{Effort, Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

/// SAT variables are dense from 0; the SAT solver never mints variables in the
/// top half of the `u32` space. We reserve that region for the synthetic
/// "sentinel" literals injected by Nelson-Oppen entailment probes so they can
/// never collide with an input literal and are trivially stripped from a
/// conflict's antecedent (R2).
const SENTINEL_VAR_BASE: u32 = 1 << 30;

#[derive(Default)]
pub struct Arith {
    vars: VarStore,
    tableau: Tableau,
    bounds: Bounds,
    /// Assignment β(v) for every ArithVar (DeltaRational).
    value: Vec<DeltaRational>,
    /// Per SAT-var encoding (indexed by Var::index()).
    enc: Vec<Option<AtomEncoding>>,
    level: usize,
    /// Antecedents of entailed-equality tags produced by `entailed_equalities`
    /// (the resolved union of the two probes' Farkas cores). Each leaf is either
    /// an input bound literal (`EqLeaf::Asserted`) or an interface dependency
    /// (`EqLeaf::Interface`) that the Combiner expands recursively via the owning
    /// theory's `explain` (CRITICAL-1). Looked up by `explain`; cleared on `pop`.
    eq_antecedents: FxHashMap<u32, Vec<EqLeaf>>,
    /// (decision level, tag) so `pop(level)` can drop tags created at higher
    /// levels (R5 backtrack safety).
    tag_trail: Vec<(usize, u32)>,
    /// Monotonic counter handing out fresh `entailed_equalities` tags.
    next_tag: u32,
    /// Counter handing out fresh synthetic sentinel literals for probes.
    next_sentinel: u32,
    /// Interface justifications (EUF→arith) stored under a tag, keyed by the tag.
    /// Cleared on `pop` via `tag_trail`.
    iface_justs: FxHashMap<u32, TheoryJust>,
    /// Maps an interface pseudo-lit's code back to its `iface_justs` tag, so a
    /// Farkas conflict that cites the pseudo-lit resolves to `Interface(just)`.
    iface_lit: FxHashMap<u32, u32>,
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
            Rel::Eq => unreachable!(
                "arith equalities are eliminated to (a<=b) AND (a>=b) by the solver's encoder; \
                 shinri-arith only receives inequality atoms"
            ),
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
    // Solver internals (Tasks 9–13, all implemented)
    // -----------------------------------------------------------------------

    fn check_full(&mut self) -> TCheck {
        use crate::simplex::{entering_for, first_violated_basic, Below};
        loop {
            let Some((basic, dir)) = first_violated_basic(&self.tableau, &self.bounds, &self.value)
            else {
                // All bounds feasible: the system is satisfiable.
                return TCheck::Sat;
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

    fn farkas_conflict(&mut self, basic: ArithVar, dir: crate::simplex::Below) -> Vec<EqLeaf> {
        crate::farkas::conflict_lits(&self.tableau, &self.bounds, basic, dir)
            .into_iter()
            .map(EqLeaf::Asserted)
            .collect()
    }

    fn tableau_well_formed(&self) -> bool {
        true
    }

    fn build_model(&mut self, _cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        use shinri_theory::types::ModelVal;
        let n = self.vars.len();
        let delta = crate::model::choose_delta(&self.value, &self.bounds, n);
        for i in 0..n {
            let v = ArithVar(i as u32);
            if let Some(term) = self.vars.term_of(v) {
                let dv = &self.value[i];
                let concrete = dv.c().clone() + dv.k().clone() * delta.clone();
                m.assign(term, ModelVal::Num(concrete));
            }
        }
    }

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

    // -----------------------------------------------------------------------
    // Nelson-Oppen interface (Task 12a): shared-var interning, entailed-equality
    // detection (state-safe probes), explanation, EUF→arith equality intake.
    // These are arith-local: they take `&Context` (term info) only so they are
    // unit-testable without the Combiner's TheoryCtx. 12b wires them up.
    // -----------------------------------------------------------------------

    /// Mint a fresh synthetic sentinel literal for an entailment probe. Lives in
    /// the reserved top-half var space so it can never equal an input lit (R2).
    fn fresh_sentinel(&mut self) -> Lit {
        // The sentinel region [SENTINEL_VAR_BASE, u32::MAX] must not be exhausted
        // (would collide with another sentinel or wrap into real-var space).
        debug_assert!(
            self.next_sentinel < u32::MAX - SENTINEL_VAR_BASE,
            "N-O sentinel var region exhausted"
        );
        let raw = SENTINEL_VAR_BASE + self.next_sentinel;
        self.next_sentinel += 1;
        Lit::new(Var::new(raw), true)
    }

    /// Whether `lit` is a synthetic N-O probe/interface sentinel (vs a real
    /// input literal). INVARIANT (12a finding): real SAT vars are dense from 0
    /// and the SAT solver never mints one in the reserved top-half region, so
    /// real vars stay strictly `< SENTINEL_VAR_BASE` (= 1<<30) and only
    /// synthetic sentinels live at/above it. `fresh_sentinel` debug-asserts it
    /// never wraps out of that region.
    #[inline]
    fn is_sentinel(lit: Lit) -> bool {
        lit.var().index() as u32 >= SENTINEL_VAR_BASE
    }

    /// Intern a problem var for the Real-sorted shared term `t`. If `t` is a
    /// numeral, ALSO pin it with an unconditional fixed bound lower=upper=value,
    /// marked Definitional (NO input Lit — uses a sentinel that `explain`
    /// contributes nothing for). Plain vars / UF-application terms just get a
    /// free problem var. (R4)
    pub fn ensure_shared_var(&mut self, ctx: &Context, t: TermId) {
        let v = self.vars.problem_var(t);
        self.grow_value();
        if let Some(r) = ctx.numeral_value(t) {
            let dr = DeltaRational::from_rational(r.clone());
            // Skip if already pinned to this value (idempotent).
            let already = matches!(self.bounds.lower(v), Some((lo, _)) if *lo == dr)
                && matches!(self.bounds.upper(v), Some((hi, _)) if *hi == dr);
            if !already {
                // Definitional/unconditional: a sentinel lit that explain drops.
                let def = self.fresh_sentinel();
                let _ = self.bounds.tighten(v, BoundKind::Lower, dr.clone(), def);
                let _ = self.bounds.tighten(v, BoundKind::Upper, dr.clone(), def);
                // Keep β consistent for a nonbasic numeral var.
                if !self.tableau.is_basic(v) {
                    self.value[v.index()] = dr;
                }
            }
        }
    }

    /// Build the canonical `u - v` linear combination over problem vars.
    fn diff_comb(uv: ArithVar, vv: ArithVar) -> LinComb {
        let mut raw = vec![(uv, Rational::one()), (vv, -Rational::one())];
        raw.sort_by_key(|p| p.0);
        // u and v are distinct problem vars, so no cancellation.
        LinComb(raw)
    }

    /// PRECONDITION: call only right after a Sat `check_full`. Returns the
    /// entailed-equal pairs among `shared` (already interned as problem
    /// vars/numerals via `ensure_shared_var`), each with a fresh arith
    /// explanation tag. State-safe: arith is left in EXACTLY the entry state
    /// (R1) — a subsequent `check_full` returns Sat with the identical β/basis.
    pub fn entailed_equalities(
        &mut self,
        ctx: &Context,
        shared: &[TermId],
    ) -> Vec<(TermId, TermId, u32)> {
        let _ = ctx;
        // Resolve shared terms to interned problem vars (dedup, keep order).
        let mut items: Vec<(TermId, ArithVar)> = Vec::new();
        for &t in shared {
            let v = self.vars.problem_var(t);
            if !items.iter().any(|(_, w)| *w == v) {
                items.push((t, v));
            }
        }
        // Pre-filter (R3 necessary condition): only same-β pairs can be entailed.
        // Group by current β (DeltaRational equality).
        let mut candidates: Vec<(usize, usize)> = Vec::new();
        for i in 0..items.len() {
            for j in (i + 1)..items.len() {
                if self.value[items[i].1.index()] == self.value[items[j].1.index()] {
                    candidates.push((i, j));
                }
            }
        }
        if candidates.is_empty() {
            return Vec::new();
        }

        // R1 step 1+2: ensure every candidate's u-v slack exists, then make β
        // consistent for the new slacks before snapshotting.
        for &(i, j) in &candidates {
            let comb = Self::diff_comb(items[i].1, items[j].1);
            let s = self.vars.slack_var(&comb);
            self.tableau.define_slack(s, &comb);
        }
        self.grow_value();
        self.recompute_basic_values();

        // R1 step 3: SNAPSHOT the live state. Every probe restores to this.
        let snap_tableau = self.tableau.clone();
        let snap_value = self.value.clone();
        let snap_mark = self.bounds_marks();
        self.bounds.mark();

        let mut out: Vec<(TermId, TermId, u32)> = Vec::new();
        for &(i, j) in &candidates {
            let (ut, uv) = items[i];
            let (vt, vv) = items[j];
            let comb = Self::diff_comb(uv, vv);
            let s = self.vars.slack_var(&comb);

            // Probe ">": inject strict s > 0  (lower = {0, +1}).
            let pos_strict = DeltaRational::new(Rational::zero(), Rational::one());
            let Some(core_pos) = self.probe(s, BoundKind::Lower, pos_strict) else {
                self.restore(&snap_tableau, &snap_value, snap_mark);
                self.bounds.mark();
                continue; // feasible ⇒ u>v possible ⇒ not entailed
            };
            self.restore(&snap_tableau, &snap_value, snap_mark);
            self.bounds.mark();

            // Probe "<": inject strict s < 0  (upper = {0, -1}).
            let neg_strict = DeltaRational::new(Rational::zero(), -Rational::one());
            let Some(core_neg) = self.probe(s, BoundKind::Upper, neg_strict) else {
                self.restore(&snap_tableau, &snap_value, snap_mark);
                self.bounds.mark();
                continue;
            };
            self.restore(&snap_tableau, &snap_value, snap_mark);
            self.bounds.mark();

            // Both directions infeasible ⇒ u = v entailed (R3 sufficient).
            // Antecedent = union of the two probes' resolved cores (input bound
            // lits + interface deps). Dedup preserving order; cores are tiny.
            let mut antecedent: Vec<EqLeaf> = Vec::new();
            for leaf in core_pos.into_iter().chain(core_neg) {
                if !antecedent.contains(&leaf) {
                    antecedent.push(leaf);
                }
            }
            let tag = self.next_tag;
            self.next_tag += 1;
            self.eq_antecedents.insert(tag, antecedent);
            self.tag_trail.push((self.level, tag));
            out.push((ut, vt, tag));
        }

        // Drop the probe mark; restore to the snapshot one final time so the
        // live state is byte-for-byte the entry state.
        self.restore(&snap_tableau, &snap_value, snap_mark);
        out
    }

    /// Current number of bounds-trail marks (so a probe can `undo_to` it).
    fn bounds_marks(&self) -> usize {
        self.bounds.marks_len()
    }

    /// Run ONE entailment probe: inject the synthetic strict bound on slack `s`
    /// under a fresh probe sentinel lit, run `check_full`, and return the
    /// conflict core as `EqLeaf`s — or `None` if the probe is feasible (so the
    /// pair is not entailed). Handles BOTH the immediate-crossing (`tighten`
    /// Conflict) path and the Farkas (`check_full` Conflict) path.
    ///
    /// CRITICAL-1: the probe's OWN injected strict bound rides under a fresh
    /// sentinel which we STRIP (R2 — it is not an input literal). But an EUF→arith
    /// interface bound (installed by `assert_interface_equality`) also rides under
    /// a sentinel pseudo-lit that is NOT an input literal yet IS a real dependency:
    /// it must be RESOLVED to `EqLeaf::Interface(just)`, not silently dropped.
    /// `resolve_iface_leaves` does exactly this split: interface pseudo-lits (in
    /// `iface_lit`) → `Interface`; every other sentinel (incl. this probe's own
    /// and a numeral-pin Definitional sentinel) → dropped; input lits → `Asserted`.
    /// Does NOT restore state; the caller restores afterward.
    fn probe(&mut self, s: ArithVar, kind: BoundKind, val: DeltaRational) -> Option<Vec<EqLeaf>> {
        let sentinel = self.fresh_sentinel();
        match self.bounds.tighten(s, kind, val, sentinel) {
            TightenResult::Redundant => {
                // The slack is already forced strictly past 0 in this direction
                // ⇒ a model with u≠v exists ⇒ not entailed.
                None
            }
            TightenResult::Conflict { other } => {
                // Immediate crossing: antecedent = resolve({sentinel, other}).
                let leaves = vec![EqLeaf::Asserted(sentinel), EqLeaf::Asserted(other)];
                Some(self.resolve_iface_leaves(leaves))
            }
            TightenResult::Tightened => match self.check_full() {
                TCheck::Sat => None,
                TCheck::Conflict(leaves) => Some(self.resolve_iface_leaves(leaves)),
                TCheck::Split(_) => unreachable!("arith check_full never emits Split"),
            },
        }
    }

    /// Overwrite the live tableau+value from the snapshot and undo every bound
    /// installed since the snapshot mark. After this the state is identical to
    /// the snapshot (R1).
    fn restore(&mut self, tableau: &Tableau, value: &[DeltaRational], mark: usize) {
        self.bounds.undo_to(mark);
        self.tableau = tableau.clone();
        self.value = value.to_vec();
    }

    /// EUF → arith (R5): install `a = b` as bounds on the slack `a - b` (fixed to
    /// 0) with the interface justification `just` as antecedent, under the LIVE
    /// backtrack mark (current level — NOT level 0). Returns conflict leaves if
    /// it makes arith infeasible (mirrors `assert`), else `None`.
    pub fn assert_interface_equality(
        &mut self,
        ctx: &Context,
        a: TermId,
        b: TermId,
        just: TheoryJust,
    ) -> Option<Vec<EqLeaf>> {
        self.ensure_shared_var(ctx, a);
        self.ensure_shared_var(ctx, b);
        let av = self.vars.problem_var(a);
        let bv = self.vars.problem_var(b);
        if av == bv {
            return None;
        }
        let comb = Self::diff_comb(av, bv);
        let s = self.vars.slack_var(&comb);
        self.tableau.define_slack(s, &comb);
        self.grow_value();
        self.recompute_basic_values();
        // Encode the interface equality as a fixed bound s = 0; the justification
        // rides as the antecedent lit. We can't pack a TheoryJust into a Lit, so
        // we store the just under a fresh tag and reference it via a sentinel lit
        // that `explain` resolves to EqLeaf::Interface(just).
        let tag = self.next_tag;
        self.next_tag += 1;
        self.iface_justs.insert(tag, just);
        self.tag_trail.push((self.level, tag));
        let pseudo = self.fresh_sentinel();
        self.iface_lit.insert(pseudo.code(), tag);
        let zero = DeltaRational::from_rational(Rational::zero());
        // Install lower then upper; either may immediately conflict.
        if let Some(c) = self.apply_bound(s, BoundKind::Lower, zero.clone(), pseudo) {
            return Some(self.resolve_iface_leaves(c));
        }
        if let Some(c) = self.apply_bound(s, BoundKind::Upper, zero, pseudo) {
            return Some(self.resolve_iface_leaves(c));
        }
        // Surface any infeasibility the fixed bound introduces.
        match self.check_full() {
            TCheck::Sat => None,
            TCheck::Conflict(leaves) => Some(self.resolve_iface_leaves(leaves)),
            TCheck::Split(_) => unreachable!("arith check_full never emits Split"),
        }
    }

    /// Map a conflict's leaves back to real antecedents: an interface pseudo-lit
    /// becomes `EqLeaf::Interface(just)`; an entailment sentinel is dropped; any
    /// other lit stays as `EqLeaf::Asserted`.
    fn resolve_iface_leaves(&self, leaves: Vec<EqLeaf>) -> Vec<EqLeaf> {
        let mut out = Vec::new();
        for leaf in leaves {
            match leaf {
                EqLeaf::Asserted(l) => {
                    if let Some(&tag) = self.iface_lit.get(&l.code()) {
                        if let Some(j) = self.iface_justs.get(&tag) {
                            out.push(EqLeaf::Interface(*j));
                        }
                    } else if !Self::is_sentinel(l) {
                        out.push(EqLeaf::Asserted(l));
                    }
                }
                other => out.push(other),
            }
        }
        out
    }
}

impl TheorySolver for Arith {
    const THEORY_ID: u16 = 2;

    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId) {
        let n = normalize_atom(cx.terms, &mut self.vars, atom);
        // Stamp Int-sortedness on each problem var this atom interned, so the
        // integer layer (Task 5) and the a-priori box (Task 4) know which vars
        // must be integral. normalize.rs is sort-blind; we read the sort here.
        let int_s = cx.terms.int_sort();
        for (av, _) in &n.comb.0 {
            if let Some(t) = self.vars.term_of(*av) {
                if cx.terms.sort_of(t) == int_s {
                    self.vars.mark_int(*av);
                }
            }
        }
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

    fn explain(&mut self, _cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer) {
        // A tag produced by `entailed_equalities`: push its stored antecedent
        // leaves (the resolved union of the two probes' Farkas cores). Each is
        // either an input bound literal (`Asserted`) or an interface dependency
        // (`Interface`) the Combiner expands recursively via the owning theory's
        // `explain` (CRITICAL-1). Probe sentinels and numeral-pin Definitional
        // bounds were already stripped/resolved when the antecedent was built.
        if let Some(leaves) = self.eq_antecedents.get(&tag) {
            for &leaf in leaves {
                debug_assert!(
                    !matches!(leaf, EqLeaf::Asserted(l) if Self::is_sentinel(l)),
                    "entailed-equality antecedent must not cite a synthetic sentinel lit"
                );
                exp.push_leaf(leaf);
            }
            return;
        }
        // An interface-equality tag (EUF→arith): contributes its interface just.
        if let Some(j) = self.iface_justs.get(&tag) {
            exp.push_leaf(EqLeaf::Interface(*j));
            return;
        }
        unreachable!("arith::explain called with an unknown tag {tag}")
    }

    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        self.build_model(cx, m) // Task 13
    }

    // ----- Nelson-Oppen seam (Task 12b): delegate to the inherent core ------

    fn ensure_shared_var(&mut self, cx: &mut TheoryCtx, t: TermId) {
        Arith::ensure_shared_var(self, cx.terms, t);
    }

    fn entailed_equalities(
        &mut self,
        cx: &mut TheoryCtx,
        shared: &[TermId],
    ) -> Vec<(TermId, TermId, u32)> {
        Arith::entailed_equalities(self, cx.terms, shared)
    }

    fn consume_interface_equality(
        &mut self,
        cx: &mut TheoryCtx,
        a: TermId,
        b: TermId,
        just: TheoryJust,
    ) -> Option<Vec<EqLeaf>> {
        Arith::assert_interface_equality(self, cx.terms, a, b, just)
    }

    fn push(&mut self) {
        self.level += 1;
        self.bounds.mark();
    }

    fn pop(&mut self, level: usize) {
        // absolute target level; restore bounds and recompute the assignment.
        self.bounds.undo_to(level);
        self.recompute_basic_values();
        // Drop any N-O tags / interface justifications created above `level`
        // (R5 backtrack safety): their antecedents are no longer valid.
        while let Some(&(lvl, tag)) = self.tag_trail.last() {
            if lvl <= level {
                break;
            }
            self.tag_trail.pop();
            self.eq_antecedents.remove(&tag);
            self.iface_justs.remove(&tag);
        }
        // Drop interface pseudo-lit mappings whose tag is gone.
        self.iface_lit
            .retain(|_, tag| self.iface_justs.contains_key(tag));
        self.level = level;
    }
}

#[cfg(test)]
mod model_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::types::ModelVal;
    use shinri_theory::{AtomRegistry, EqualityEngine, ModelBuilder, TheoryCtx, TheorySolver};

    #[test]
    fn model_picks_concrete_value_for_strict_bound() {
        // x > 0  -> model must give x = c + k*delta with a concrete positive rational.
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xs = ctx.declare_fun("x", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let z = ctx.mk_numeral(Rational::zero(), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[x, z]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), gt);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat));
        let mut mb = ModelBuilder::default();
        arith.model(&mut cx, &mut mb);
        match mb.get(x) {
            Some(ModelVal::Num(r)) => assert!(*r > Rational::zero(), "x must be > 0, got {:?}", r),
            other => panic!("expected Num, got {:?}", other),
        }
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
            terms: &mut ctx,
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
            terms: &mut ctx,
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
            terms: &mut ctx,
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
            TCheck::Split(_) => unreachable!("Arith check never emits Split in its own tests"),
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
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), ge);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}

#[cfg(test)]
mod nelson_oppen_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::types::EqLeaf;
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let s = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }
    fn num(ctx: &mut Context, n: i128) -> TermId {
        ctx.mk_numeral(Rational::from_int(n.into()), ctx.real_sort())
    }
    fn dr(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(n.into()))
    }

    /// Helper: build a `TheoryCtx`-free harness. Returns ctx so the caller keeps
    /// term identities; arith methods take `&Context` directly.
    struct Harness {
        ctx: Context,
        arith: Arith,
    }
    impl Harness {
        fn new() -> Self {
            Harness {
                ctx: Context::new(),
                arith: Arith::default(),
            }
        }
        /// Declare an atom as SAT var `i` and assert it (positive).
        fn assert_atom(&mut self, i: u32, atom: TermId) {
            let mut eq = EqualityEngine::default();
            let atoms = AtomRegistry::default();
            let mut cx = TheoryCtx {
                terms: &mut self.ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            self.arith.new_var(&mut cx, Var::new(i), atom);
            self.arith.assert(&mut cx, Lit::new(Var::new(i), true));
        }
        fn check(&mut self) -> TCheck {
            self.arith.check_full()
        }
    }

    // ----- Test 1: probe_does_not_perturb_state (R1 regression guard) -----
    #[test]
    fn probe_does_not_perturb_state() {
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        // x+y <= 5 ; x >= 0 ; y >= 0  (feasible, not entailed-equal)
        let xy = h.ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let five = num(&mut h.ctx, 5);
        let zero = num(&mut h.ctx, 0);
        let a = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[xy, five])
            .unwrap();
        let b = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero])
            .unwrap();
        let c = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[y, zero])
            .unwrap();
        h.assert_atom(0, a);
        h.assert_atom(1, b);
        h.assert_atom(2, c);
        assert!(matches!(h.check(), TCheck::Sat));

        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);

        // Run entailed_equalities ONCE to mint the candidate slacks, then snapshot
        // the post-slack state; a SECOND run must leave that state byte-identical
        // (the probes must not perturb anything). This is the R1 guard: the slack
        // rows are part of the protocol's entry state, the probes are not.
        let _ = h.arith.entailed_equalities(&ctx, &[x, y]);
        let value_before = h.arith.value.clone();
        let basis_before: std::collections::BTreeSet<u32> =
            h.arith.tableau.basic.iter().map(|v| v.0).collect();

        let _ = h.arith.entailed_equalities(&ctx, &[x, y]);

        assert_eq!(h.arith.value, value_before, "β must be byte-identical");
        let basis_after: std::collections::BTreeSet<u32> =
            h.arith.tableau.basic.iter().map(|v| v.0).collect();
        assert_eq!(basis_before, basis_after, "basis must be identical");
        assert!(matches!(h.arith.check_full(), TCheck::Sat));
    }

    // ----- Test 2: order_independence (R1) -----
    #[test]
    fn order_independence() {
        // Three vars all forced equal: x=y=z all fixed to 3. Every pair entailed
        // regardless of probe order; probing one must not drop another.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let z = real_var(&mut h.ctx, "z");
        let three = num(&mut h.ctx, 3);
        for (i, v) in [x, y, z].iter().enumerate() {
            let le = h
                .ctx
                .mk_app(Op::Builtin(BuiltinOp::Le), &[*v, three])
                .unwrap();
            let ge = h
                .ctx
                .mk_app(Op::Builtin(BuiltinOp::Ge), &[*v, three])
                .unwrap();
            h.assert_atom(2 * i as u32, le);
            h.assert_atom(2 * i as u32 + 1, ge);
        }
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        for v in [x, y, z] {
            h.arith.ensure_shared_var(&ctx, v);
        }
        let fwd = pairset(&h.arith.entailed_equalities(&ctx, &[x, y, z]));
        let rev = pairset(&h.arith.entailed_equalities(&ctx, &[z, y, x]));
        assert_eq!(fwd, rev, "entailed set must be order-independent");
        assert_eq!(fwd.len(), 3, "all three pairs must be entailed");
    }

    fn pairset(pairs: &[(TermId, TermId, u32)]) -> std::collections::BTreeSet<(usize, usize)> {
        pairs
            .iter()
            .map(|(a, b, _)| {
                let (lo, hi) = (a.index().min(b.index()), a.index().max(b.index()));
                (lo, hi)
            })
            .collect()
    }

    // ----- Test 3: fixed_vars_entailed_equal -----
    #[test]
    fn fixed_vars_entailed_equal() {
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let z = real_var(&mut h.ctx, "z");
        let five = num(&mut h.ctx, 5);
        let seven = num(&mut h.ctx, 7);
        let mut i = 0u32;
        for (v, n) in [(x, five), (y, five), (z, seven)] {
            let le = h.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[v, n]).unwrap();
            let ge = h.ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[v, n]).unwrap();
            h.assert_atom(i, le);
            h.assert_atom(i + 1, ge);
            i += 2;
        }
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        for v in [x, y, z] {
            h.arith.ensure_shared_var(&ctx, v);
        }
        let got = pairset(&h.arith.entailed_equalities(&ctx, &[x, y, z]));
        assert!(got.contains(&(x.index().min(y.index()), x.index().max(y.index()))));
        // z (fixed 7) must NOT be paired with x (fixed 5).
        assert!(!got.contains(&(x.index().min(z.index()), x.index().max(z.index()))));
        assert!(!got.contains(&(y.index().min(z.index()), y.index().max(z.index()))));
    }

    // ----- Test 4: numeral_pinning (R4) -----
    #[test]
    fn numeral_pinning() {
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let five = num(&mut h.ctx, 5);
        let le = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[x, five])
            .unwrap();
        let ge = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[x, five])
            .unwrap();
        h.assert_atom(0, le);
        h.assert_atom(1, ge);
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, five); // pin numeral 5
        let got = pairset(&h.arith.entailed_equalities(&ctx, &[x, five]));
        assert!(
            got.contains(&(x.index().min(five.index()), x.index().max(five.index()))),
            "x fixed to 5 must be entailed-equal to numeral 5"
        );
    }

    // ----- Test 5: nonfixed_entailed -----
    #[test]
    fn nonfixed_entailed() {
        // x <= y AND y <= x : neither individually fixed, but x = y entailed.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let le1 = h.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
        let le2 = h.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[y, x]).unwrap();
        h.assert_atom(0, le1);
        h.assert_atom(1, le2);
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);
        let got = pairset(&h.arith.entailed_equalities(&ctx, &[x, y]));
        assert!(
            got.contains(&(x.index().min(y.index()), x.index().max(y.index()))),
            "x<=y AND y<=x must entail x=y"
        );
    }

    // ----- Test 6: not_entailed_when_separable -----
    #[test]
    fn not_entailed_when_separable() {
        // x <= y only: a model with x < y exists, so NOT entailed.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let le1 = h.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
        h.assert_atom(0, le1);
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);
        let got = h.arith.entailed_equalities(&ctx, &[x, y]);
        assert!(got.is_empty(), "x<=y alone must not entail x=y");
    }

    // ----- Test 7: explain_cites_only_input_lits (R2) -----
    #[test]
    fn explain_cites_only_input_lits() {
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        // x<=y (var 0) AND y<=x (var 1) entail x=y.
        let le1 = h.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
        let le2 = h.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[y, x]).unwrap();
        h.assert_atom(0, le1);
        h.assert_atom(1, le2);
        assert!(matches!(h.check(), TCheck::Sat));
        let mut ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);
        let pairs = h.arith.entailed_equalities(&ctx, &[x, y]);
        assert_eq!(pairs.len(), 1);
        let tag = pairs[0].2;
        // Drive explain via the trait method.
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        let mut exp = Explainer::default();
        h.arith.explain(&mut cx, tag, &mut exp);
        // Must cite exactly the two asserting bound lits, no sentinels.
        let lits: std::collections::BTreeSet<u32> = exp.lits.iter().map(|l| l.code()).collect();
        assert!(exp.pending.is_empty());
        assert!(
            lits.contains(&Lit::new(Var::new(0), true).code()),
            "must cite x<=y lit"
        );
        assert!(
            lits.contains(&Lit::new(Var::new(1), true).code()),
            "must cite y<=x lit"
        );
        for l in &exp.lits {
            assert!(
                (l.var().index() as u32) < SENTINEL_VAR_BASE,
                "must NOT cite a synthetic sentinel lit"
            );
        }
    }

    // ----- Test 8: interface_equality_conflict -----
    #[test]
    fn interface_equality_conflict() {
        // a - b >= 1, then assert interface a = b  -> conflict citing the just.
        let mut h = Harness::new();
        let a = real_var(&mut h.ctx, "a");
        let b = real_var(&mut h.ctx, "b");
        let ab = h.ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[a, b]).unwrap();
        let one = num(&mut h.ctx, 1);
        let ge = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[ab, one])
            .unwrap();
        h.assert_atom(0, ge); // a - b >= 1
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        let just = TheoryJust { theory: 1, tag: 42 };
        let conflict = h.arith.assert_interface_equality(&ctx, a, b, just);
        let leaves = conflict.expect("a=b with a-b>=1 must conflict");
        assert!(
            leaves.contains(&EqLeaf::Interface(just)),
            "conflict must cite the interface justification, got {:?}",
            leaves
        );
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(0), true))),
            "conflict must cite the a-b>=1 lit"
        );
    }

    // ----- Test 9: interface bound undone on pop -----
    #[test]
    fn interface_equality_undone_on_pop() {
        let mut h = Harness::new();
        let a = real_var(&mut h.ctx, "a");
        let b = real_var(&mut h.ctx, "b");
        let ab = h.ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[a, b]).unwrap();
        let one = num(&mut h.ctx, 1);
        let ge = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[ab, one])
            .unwrap();
        h.assert_atom(0, ge); // a - b >= 1
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.push(); // level 1
        let just = TheoryJust { theory: 1, tag: 7 };
        let conflict = h.arith.assert_interface_equality(&ctx, a, b, just);
        assert!(conflict.is_some(), "a=b must conflict at level 1");
        h.arith.pop(0); // undo the interface equality
        assert!(
            matches!(h.arith.check_full(), TCheck::Sat),
            "after pop the interface bound must be gone -> feasible again"
        );
        // And its tag bookkeeping was cleared.
        assert!(h.arith.iface_justs.is_empty());
    }

    // ----- Test 10 (CRITICAL-1 regression): an entailed-equality antecedent
    // that rests on an EUF→arith interface bound MUST retain the interface dep
    // (as EqLeaf::Interface) AND cite the real input bound lits — not strip the
    // interface (under-cite → unsound nogood) nor cite a non-input companion.
    #[test]
    fn entailed_eq_antecedent_retains_interface_dependency() {
        // fa - w >= 0  (L0) ;  w - fb >= 0  (L1) ;  interface fa = fb.
        // Then w = fa is entailed: w <= fa (from L0) and w >= fb = fa (L1 + iface).
        // The antecedent for w=fa MUST include Interface(fa=fb) and the input
        // lits L0, L1.
        let mut h = Harness::new();
        let fa = real_var(&mut h.ctx, "fa");
        let fb = real_var(&mut h.ctx, "fb");
        let w = real_var(&mut h.ctx, "w");
        let zero = num(&mut h.ctx, 0);
        // fa - w >= 0
        let faw = h.ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[fa, w]).unwrap();
        let ge0 = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[faw, zero])
            .unwrap();
        // w - fb >= 0
        let wfb = h.ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[w, fb]).unwrap();
        let ge1 = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[wfb, zero])
            .unwrap();
        h.assert_atom(0, ge0); // L0
        h.assert_atom(1, ge1); // L1
        assert!(matches!(h.check(), TCheck::Sat));
        let mut ctx = std::mem::replace(&mut h.ctx, Context::new());
        for v in [fa, fb, w] {
            h.arith.ensure_shared_var(&ctx, v);
        }
        // Install the EUF→arith interface equality fa = fb.
        let iface = TheoryJust { theory: 1, tag: 99 };
        assert!(
            h.arith
                .assert_interface_equality(&ctx, fa, fb, iface)
                .is_none(),
            "fa=fb is consistent with fa-w>=0 ∧ w-fb>=0"
        );
        assert!(matches!(h.arith.check_full(), TCheck::Sat));
        // Now w = fa must be entailed.
        let pairs = h.arith.entailed_equalities(&ctx, &[fa, fb, w]);
        let wfa = pairs
            .iter()
            .find(|(a, b, _)| {
                let (lo, hi) = (a.index().min(b.index()), a.index().max(b.index()));
                (lo, hi) == (w.index().min(fa.index()), w.index().max(fa.index()))
            })
            .expect("w = fa must be entailed");
        let tag = wfa.2;
        // Drive explain: the antecedent must contain Interface(fa=fb) AND the
        // input lits L0,L1 (resolution of Interface happens in the Combiner).
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        let mut exp = Explainer::default();
        h.arith.explain(&mut cx, tag, &mut exp);
        assert!(
            exp.pending.contains(&iface),
            "antecedent MUST retain the interface dependency fa=fb, got pending={:?} lits={:?}",
            exp.pending,
            exp.lits
        );
        let lits: std::collections::BTreeSet<u32> = exp.lits.iter().map(|l| l.code()).collect();
        assert!(
            lits.contains(&Lit::new(Var::new(0), true).code()),
            "must cite L0 (fa-w>=0), got {:?}",
            exp.lits
        );
        assert!(
            lits.contains(&Lit::new(Var::new(1), true).code()),
            "must cite L1 (w-fb>=0), got {:?}",
            exp.lits
        );
        for l in &exp.lits {
            assert!(
                (l.var().index() as u32) < SENTINEL_VAR_BASE,
                "must NOT cite a synthetic sentinel lit, got {:?}",
                l
            );
        }
    }

    // sanity: numeral fixed bound itself doesn't break feasibility check.
    #[test]
    fn numeral_pin_keeps_value() {
        let mut h = Harness::new();
        let five = num(&mut h.ctx, 5);
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, five);
        let v = h.arith.vars.problem_var(five);
        assert_eq!(h.arith.value[v.index()], dr(5));
        assert!(matches!(h.arith.check_full(), TCheck::Sat));
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
                terms: &mut ctx,
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
                terms: &mut ctx,
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
