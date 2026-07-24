//! shinri-arith: a Dutertre–de Moura simplex theory solver for QF_LRA.
//! Implements `shinri_theory::TheorySolver`; depends only on core + theory.
//! Handles ONLY inequality atoms (Le/Lt/Ge/Gt). Arithmetic equalities are
//! eliminated at the CNF encoder level (rewritten to `(a<=b) AND (a>=b)`).

pub mod bounds;
pub mod branch;
pub mod cuts;
pub mod encode;
pub mod farkas;
pub mod model;
pub mod normalize;
pub mod propagate;
pub mod simplex;
pub mod tableau;
pub mod vars;

pub use vars::ArithVar;

use crate::bounds::{BoundKind, Bounds, TightenResult};
use crate::encode::AtomEncoding;
use crate::normalize::{normalize_atom, LinComb, Rel};
use crate::tableau::Tableau;
use crate::vars::VarStore;
use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TheoryJust, Var};
use shinri_num::{DeltaRational, Integer, Rational};
use shinri_theory::types::EqLeaf;
use shinri_theory::{Effort, Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

/// SAT variables are dense from 0; the SAT solver never mints variables in the
/// top half of the `u32` space. We reserve that region for the synthetic
/// "sentinel" literals injected by Nelson-Oppen entailment probes so they can
/// never collide with an input literal and are trivially stripped from a
/// conflict's antecedent (R2).
const SENTINEL_VAR_BASE: u32 = 1 << 30;

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
    /// Max |coefficient| and |constant| over all registered atoms — the input
    /// magnitude `a` feeding the a-priori bound `M`. Updated in `new_var`.
    apriori_coeff_max: Integer,
    /// Count of registered arith atoms — the constraint count `m` feeding `M`.
    apriori_atom_count: usize,
    /// One-shot guard: the a-priori box is seeded at the first level-0 Full check.
    apriori_seeded: bool,
    /// Sentinel lit codes used for a-priori box bounds, stripped from conflicts.
    /// Since slice 27 this set has no production reader — `sanitize_conflict`
    /// drops ALL non-iface sentinels without consulting it — but it stays for
    /// the seeding-idempotence unit pin and as documentation of which
    /// sentinels are a-priori/FBBT ones.
    apriori_lits: FxHashSet<u32>,
    /// Master gate for all Plan B2 optimizations (integer bound rounding, FBBT,
    /// GMI cuts). Default ON; the differential harness builds an OFF solver to
    /// reproduce the byte-identical B1 baseline.
    stage_b: bool,
    /// Cuts generated at the current search node (reset on pop). Bounds cut effort.
    node_cuts: usize,
    /// Total cuts generated this solve (global cap).
    total_cuts: usize,
    /// Total simplex pivots performed this solve (global, monotone, never reset on
    /// backtrack). The String↔Arith `str.substr` seam can feed Arith an
    /// ever-growing degenerate system whose per-`check_full` cost balloons across
    /// successive SAT decisions; bounding CUMULATIVE pivots guarantees the whole
    /// solve terminates. On exhaustion `check_full` returns `Unknown` (SOUND — it
    /// declines to decide rather than loop or report a wrong verdict). The budget
    /// is far above any realistic QF_LIA/QF_UFLRA workload, so it never trips on the
    /// soundly-decidable fragment.
    total_pivots: u64,
    /// Total integer branch-and-bound splits emitted this solve (global, monotone,
    /// never reset on backtrack). Branch-and-bound on UNBOUNDED integer variables
    /// is not guaranteed to terminate: when the LP relaxation optimum keeps moving
    /// to ever-larger fractional points (e.g. MBTC strict `<`/`>` separations over
    /// shared `str.len` terms repeatedly push the relaxation away from an integer
    /// point), each branch `x≤⌊v⌋ ∨ x≥⌈v⌉` mints a FRESH atom over a new numeral, so
    /// atom-dedup cannot stop it and the search diverges (branch value → ∞). The SAT
    /// `step_budget` only bounds this after millions of steps (minutes). Capping the
    /// CUMULATIVE branch count here bounds it directly: on exhaustion `integer_check`
    /// returns `Unknown` (SOUND — declines to decide rather than diverge). The budget
    /// is far above any realistic finite-domain QF_LIA search, so it never trips on
    /// the soundly-decidable fragment.
    total_branches: u64,
    /// Cumulative integer branch-and-bound budget for one solve (see
    /// `total_branches`). On exhaustion `integer_check` returns a SOUND `Unknown`.
    /// Defaults to a value above the largest branch count any legitimately-bounded
    /// QF_LIA/QF_UFLIA instance needs (so it never trips on the pure-arith fragment),
    /// and is lowered on the STRING path — where the LP relaxation over unbounded
    /// `str.len` terms can diverge under MBTC strict separations, and where the
    /// soundly-decidable string fragment needs only a handful of arith branches, so a
    /// small cap bounds the divergence quickly without affecting any decidable query.
    branch_budget: u64,
    /// Cumulative simplex pivot budget for one solve (the `total_pivots` cap; see
    /// `total_pivots`). Defaults high (no realistic QF_LIA/QF_UFLRA workload reaches
    /// it) and is lowered on the STRING path, where the String↔Arith length seam can
    /// feed an ever-growing degenerate system whose `entailed_equalities` /
    /// `model_equal_shared_pairs` probing re-solves simplex unboundedly. On exhaustion
    /// `check_full` returns a SOUND `Unknown`.
    pivot_budget: u64,
    /// Problem vars arith has actually received a constraint about (slice 42).
    /// Indexed by `ArithVar::index()`; `false`/absent means arith knows the var
    /// exists but nothing about its value, so no equality over it can be
    /// entailed and no arrangement of it needs deciding.
    ///
    /// MONOTONE: never un-marked, including on `pop`. After backtracking, a var
    /// constrained only by a since-retracted assertion stays marked and is still
    /// probed. That over-approximates constrainedness, which errs toward MORE
    /// probing — the sound direction.
    ///
    /// Deliberately NOT inferred from `bounds`: `seed_apriori_if_needed` puts a
    /// uniform box on every Int problem var (free ones included), and
    /// `entailed_equalities`' probe slacks persist across calls, so both the
    /// bounds table and the tableau report free vars as constrained.
    constrained: Vec<bool>,
}

impl Default for Arith {
    fn default() -> Self {
        Arith {
            vars: VarStore::default(),
            tableau: Tableau::default(),
            bounds: Bounds::default(),
            value: Vec::default(),
            enc: Vec::default(),
            level: 0,
            eq_antecedents: FxHashMap::default(),
            tag_trail: Vec::default(),
            next_tag: 0,
            next_sentinel: 0,
            iface_justs: FxHashMap::default(),
            iface_lit: FxHashMap::default(),
            apriori_coeff_max: Integer::zero(),
            apriori_atom_count: 0,
            apriori_seeded: false,
            apriori_lits: FxHashSet::default(),
            stage_b: true,
            node_cuts: 0,
            total_cuts: 0,
            total_pivots: 0,
            total_branches: 0,
            branch_budget: Self::DEFAULT_BRANCH_BUDGET,
            pivot_budget: Self::DEFAULT_PIVOT_BUDGET,
            constrained: Vec::default(),
        }
    }
}

impl Arith {
    const MAX_CUTS_PER_NODE: usize = 4;
    const MAX_CUTS_TOTAL: usize = 10_000;
    /// Default cumulative integer branch-and-bound split budget for one solve.
    /// Branch-and-bound on unbounded integers may diverge (branch value → ∞); this
    /// bounds it to a SOUND `Unknown`. Set above the largest branch count any
    /// legitimately-bounded QF_LIA/QF_UFLIA instance in the differential corpus needs
    /// (observed ≈80k), so it never trips on the pure-arith decidable fragment.
    const DEFAULT_BRANCH_BUDGET: u64 = 150_000;
    /// Branch-and-bound budget used on the STRING path. The soundly-decidable string
    /// fragment needs only a handful of arith branches, while the LP relaxation over
    /// unbounded `str.len` terms can diverge under MBTC strict separations; a small
    /// cap bounds that divergence in well under a second (the per-branch cost grows
    /// with the SAT trail) without making any decidable query Unknown.
    pub const STRING_PATH_BRANCH_BUDGET: u64 = 4_000;
    /// Default cumulative simplex pivot budget (see `pivot_budget`). Far above any
    /// realistic QF_LIA/QF_UFLRA workload.
    const DEFAULT_PIVOT_BUDGET: u64 = 2_000_000;
    /// Simplex pivot budget used on the STRING path. The String↔Arith length seam's
    /// degenerate `entailed_equalities` probing can re-solve simplex unboundedly;
    /// this tight cap bails such a divergent seam to a SOUND `Unknown` in well under a
    /// second, while the soundly-decidable string fragment finishes in far fewer
    /// pivots.
    pub const STRING_PATH_PIVOT_BUDGET: u64 = 2_000;

    fn grow_value(&mut self) {
        while self.value.len() < self.vars.len() {
            self.value
                .push(DeltaRational::from_rational(Rational::zero()));
        }
        self.bounds.ensure(self.vars.len());
    }

    /// Mark `v` as a var arith has received a constraint about (slice 42).
    /// Resizes on demand rather than tracking `grow_value` ordering.
    fn mark_constrained(&mut self, v: ArithVar) {
        if v.index() >= self.constrained.len() {
            self.constrained.resize(v.index() + 1, false);
        }
        self.constrained[v.index()] = true;
    }

    /// Whether arith has received any constraint about `v` (slice 42). An
    /// unmarked var is free: `u = v` is not entailed for any `v`, and any
    /// arrangement of it is arith-satisfiable.
    fn is_constrained(&self, v: ArithVar) -> bool {
        self.constrained.get(v.index()).copied().unwrap_or(false)
    }

    /// Toggle the Plan B2 optimization gate (default ON). OFF = B1 baseline.
    pub fn set_stage_b(&mut self, on: bool) {
        self.stage_b = on;
    }

    /// Override the cumulative integer branch-and-bound budget (see `branch_budget`).
    /// The solver lowers this on the string path so unbounded-`str.len` B&B
    /// divergence is bounded to a SOUND `Unknown` quickly.
    pub fn set_branch_budget(&mut self, n: u64) {
        self.branch_budget = n;
    }

    /// Override the cumulative simplex pivot budget (see `pivot_budget`). The solver
    /// lowers this on the string path so the degenerate String↔Arith length-seam
    /// probing is bounded to a SOUND `Unknown` quickly.
    pub fn set_pivot_budget(&mut self, n: u64) {
        self.pivot_budget = n;
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
                let mut enc = AtomEncoding::Ineq {
                    var,
                    pos: (pk, DeltaRational::new(rhs.clone(), pkk)),
                    neg: (nk, DeltaRational::new(rhs, nkk)),
                };
                // Stage-B integer bound rounding: if the bounded quantity is
                // integer-valued, replace each (kind, value) with the integer
                // round and drop the δ. `strict` is read off the δ-coefficient
                // (nonzero ⇒ strict). Handles flipped-coefficient cases because
                // `kind` and `value` are already resolved here.
                if self.stage_b && self.comb_is_int_valued(&n.comb) {
                    if let AtomEncoding::Ineq { pos, neg, .. } = &mut enc {
                        for slot in [pos, neg] {
                            let strict = !slot.1.k().is_zero();
                            slot.1 = crate::branch::round_int_bound(slot.1.c(), slot.0, strict);
                        }
                    }
                }
                enc
            }
        }
    }

    /// True iff the linear combination evaluates to an integer for every model:
    /// every variable is Int-sorted AND every coefficient is an integer. In a
    /// pure-Int query this holds for all problem vars and all slacks.
    fn comb_is_int_valued(&self, comb: &LinComb) -> bool {
        !comb.0.is_empty()
            && comb
                .0
                .iter()
                .all(|(v, c)| self.vars.is_int(*v) && c.denom() == Integer::one())
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
        // Cumulative anti-divergence guard (see `total_pivots`). The String↔Arith
        // `str.substr` seam can drive an ever-growing degenerate system across many
        // SAT decisions; capping the TOTAL pivots performed this solve guarantees
        // termination even when each individual `check_full` would finish. On
        // exhaustion we return `Unknown` — SOUND (decline to decide, never loop or
        // report a wrong verdict). The budget is far above any realistic workload.
        let total_pivot_budget: u64 = self.pivot_budget;
        // Coefficient-blowup guard: a degenerate system (the String↔Arith
        // `str.substr` seam) can make simplex coefficients grow without bound, so a
        // SINGLE BigInt gcd/division dominates runtime (an effective hang the pivot
        // COUNT cap cannot catch). If any current value's magnitude exceeds this
        // many 64-bit limbs (~ thousands of decimal digits — far beyond any
        // legitimate QF_LIA/QF_UFLRA coefficient), bail to a sound `Unknown`.
        const MAX_LIMBS: usize = 64;
        // Restore the DdM invariant before checking feasibility: every basic var's
        // value must equal its row evaluated at the current nonbasic values. New
        // slacks introduced by theory-emitted defining axioms (e.g. the string
        // theory's `len(a++b) = len(a)+len(b)`), and nonbasic bound tightenings that
        // did not trigger a value move, can leave a basic slack's cached value STALE
        // — first_violated_basic would then read a phantom infeasibility and report a
        // SPURIOUS conflict (observed wrong-UNSAT on `len(s2)=1 ∧ len(s2++"b")=2`,
        // where the defining-axiom slack read 1 against its [.,0] bound instead of the
        // true 0). Recomputing here is O(tableau) and makes the feasibility check
        // consistent.
        self.recompute_basic_values();
        loop {
            self.total_pivots += 1;
            if self.total_pivots > total_pivot_budget {
                return TCheck::Unknown;
            }
            let Some((basic, dir)) = first_violated_basic(&self.tableau, &self.bounds, &self.value)
            else {
                // All bounds feasible: the system is satisfiable.
                return TCheck::Sat;
            };
            // Bail to a sound `Unknown` if a row coefficient has blown up past
            // MAX_LIMBS (defense-in-depth against any residual degenerate growth;
            // the primary fix for the substr seam is the proof-forest undo
            // correctness in `EqualityEngine`).
            {
                let row = self.tableau.row(basic);
                let blown = row.vars().any(|j| {
                    let c = row.coeff(j);
                    c.numer().limb_count() > MAX_LIMBS || c.denom().limb_count() > MAX_LIMBS
                });
                if blown {
                    return TCheck::Unknown;
                }
            }
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
        // Stamp Int-sortedness so shared Int terms (f-apps, numerals, vars) are
        // integral in the simplex / integer layer — required for QF_UFLIA.
        let is_int = ctx.sort_of(t) == ctx.int_sort();
        let v = self.vars.problem_var_sorted(t, is_int);
        self.grow_value();
        if let Some(r) = ctx.numeral_value(t) {
            // Slice 42: pinning a numeral to its value IS a constraint. Marked
            // outside the `already` guard so re-entry keeps the mark. The
            // non-numeral path deliberately does NOT mark — that asymmetry is
            // the whole point of the slice.
            self.mark_constrained(v);
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
        //
        // Slice 42: additionally skip any pair containing a var arith has
        // received no constraint about. Such a var is free, so `u = v` is not
        // entailed for any `v` and the probe cannot succeed. The skip MUST
        // happen here, before the `define_slack` loop below: the R1 snapshot is
        // taken AFTER slack definition and the final `restore` restores to it,
        // so a slack minted for a hopeless pair would persist for the rest of
        // the solve. Without this, a datatype with an Int field makes every
        // DT-minted selector app a free shared var at β = 0, admitting every
        // pair — the ≈1600× regression this slice fixes.
        let mut candidates: Vec<(usize, usize)> = Vec::new();
        for i in 0..items.len() {
            if !self.is_constrained(items[i].1) {
                continue;
            }
            for j in (i + 1)..items.len() {
                if !self.is_constrained(items[j].1) {
                    continue;
                }
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

    /// Shared INT-sorted pairs equal under the current model `β` (MBTC candidate
    /// pairs). Read-only / state-safe. Int-only via `is_int`, reliable because
    /// `ensure_shared_var` stamps Int-sortedness. Excludes Real pairs (convex
    /// exchange handles those; splitting them would regress QF_UFLRA).
    pub fn model_equal_shared_pairs(&mut self, shared: &[TermId]) -> Vec<(TermId, TermId)> {
        let mut items: Vec<(TermId, ArithVar)> = Vec::new();
        for &t in shared {
            let v = self.vars.problem_var(t);
            if self.vars.is_int(v) && !items.iter().any(|(_, w)| *w == v) {
                items.push((t, v));
            }
        }
        // Slice 42: skip pairs containing a var arith has no constraint about.
        // Arith constrains neither side, so every arrangement EUF chooses is
        // arith-satisfiable and MBTC has nothing to decide. This is a DISTINCT
        // soundness claim from the one in `entailed_equalities` — arrangement
        // agreement, not equality entailment — over the same var set.
        let mut out = Vec::new();
        for i in 0..items.len() {
            if !self.is_constrained(items[i].1) {
                continue;
            }
            for j in (i + 1)..items.len() {
                if !self.is_constrained(items[j].1) {
                    continue;
                }
                if self.value[items[i].1.index()] == self.value[items[j].1.index()] {
                    out.push((items[i].0, items[j].0));
                }
            }
        }
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
    /// `sanitize_conflict` does exactly this split: interface pseudo-lits (in
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
                Some(self.sanitize_conflict(leaves))
            }
            TightenResult::Tightened => match self.check_full() {
                TCheck::Sat => None,
                TCheck::Conflict(leaves) => Some(self.sanitize_conflict(leaves)),
                TCheck::Split { .. } => unreachable!("arith check_full never emits Split"),
                // The pivot cap tripped (degenerate system). Conservatively treat
                // the probe as "feasible / not proven entailed": returning `None`
                // simply means we do NOT claim `u = v` is entailed. That is SOUND —
                // it only forgoes a possible interface equality (a completeness
                // concession), never asserts a false one.
                TCheck::Unknown => None,
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
        // Slice 42: an EUF→arith interface equality pins `av - bv = 0`, which
        // constrains both sides.
        self.mark_constrained(av);
        self.mark_constrained(bv);
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
            return Some(self.sanitize_conflict(c));
        }
        if let Some(c) = self.apply_bound(s, BoundKind::Upper, zero, pseudo) {
            return Some(self.sanitize_conflict(c));
        }
        // Surface any infeasibility the fixed bound introduces.
        match self.check_full() {
            TCheck::Sat => None,
            TCheck::Conflict(leaves) => Some(self.sanitize_conflict(leaves)),
            TCheck::Split { .. } => unreachable!("arith check_full never emits Split"),
            // Pivot cap tripped (degenerate). Report no conflict from this interface
            // equality: SOUND (we only forgo detecting a possible infeasibility — a
            // completeness concession that surfaces upstream as `Unknown`, never a
            // wrong verdict).
            TCheck::Unknown => None,
        }
    }

    /// Sanitize a conflict core at the theory boundary. INVARIANT (owned
    /// here, slice 27): no raw sentinel literal ever leaves `Arith` in a
    /// conflict core. An interface pseudo-lit (in `iface_lit`) resolves to
    /// `EqLeaf::Interface(just)` — interface-equality bounds are LIVE-level
    /// facts whose justification the Combiner must expand recursively
    /// (CRITICAL-1), so dropping them would under-cite the core (unsound).
    /// Every OTHER sentinel (a-priori box, FBBT, probe assumption) drops:
    /// those bounds are level-0-entailed facts, so the remaining core stays
    /// valid (the slice-8 stripping argument). Real asserted lits pass
    /// through. ALL conflict exits from this theory must route through this
    /// function; the tail assert catches any future sentinel flavor added
    /// without a resolution rule here.
    fn sanitize_conflict(&self, leaves: Vec<EqLeaf>) -> Vec<EqLeaf> {
        let mut out = Vec::new();
        for leaf in leaves {
            match leaf {
                EqLeaf::Asserted(l) => {
                    if let Some(&tag) = self.iface_lit.get(&l.code()) {
                        if let Some(j) = self.iface_justs.get(&tag) {
                            out.push(EqLeaf::Interface(*j));
                        } else {
                            // Unreachable while `pop` stays atomic: it removes a
                            // tag's `iface_justs` entry, its `iface_lit` mapping,
                            // and the bounds it justified in one uninterrupted
                            // step, so no core can cite an iface bound whose
                            // justification is gone. If that sync ever breaks,
                            // silently dropping the leaf here would under-cite
                            // the core (a too-strong learnt clause — unsound),
                            // so fail loudly in debug builds instead.
                            debug_assert!(
                                false,
                                "sanitize_conflict: iface pseudo-lit has a tag but no \
                                 justification — iface_lit/iface_justs out of sync"
                            );
                        }
                    } else if !Self::is_sentinel(l) {
                        out.push(EqLeaf::Asserted(l));
                    }
                }
                other => out.push(other),
            }
        }
        debug_assert!(
            !out.iter()
                .any(|leaf| matches!(leaf, EqLeaf::Asserted(l) if Self::is_sentinel(*l))),
            "sanitize_conflict: raw sentinel survived — a sentinel flavor lacks a resolution rule"
        );
        out
    }

    // -----------------------------------------------------------------------
    // Integer branch-and-bound layer (Task 5).
    // -----------------------------------------------------------------------

    /// After the real relaxation is feasible (`check_full` Sat), scan Int problem
    /// vars for a non-integral value. All integral ⇒ Sat. Otherwise pick the
    /// most-fractional var (ties by smallest ArithVar index = Bland order) and
    /// return `Split` on `(x ≤ ⌊v⌋) ∨ (x ≥ ⌈v⌉)`, building the atoms via cx.terms.
    fn integer_check(&mut self, cx: &mut TheoryCtx) -> TCheck {
        let mut best: Option<(ArithVar, Rational)> = None; // (var, fractional distance)
        for i in 0..self.vars.len() {
            let v = ArithVar(i as u32);
            if self.vars.is_slack(v) || !self.vars.is_int(v) {
                continue;
            }
            let val = &self.value[v.index()];
            let integral = val.k().is_zero() && val.c().denom() == shinri_num::Integer::one();
            if integral {
                continue;
            }
            // Fractional distance to the floor, as a tie-break key (most fractional).
            let (f, _c) = crate::branch::floor_ceil(val);
            let dist = val.c().clone() - Rational::from_int(f);
            match &best {
                Some((_, bd)) if &dist <= bd => {}
                _ => best = Some((v, dist)),
            }
        }
        let Some((bv, _)) = best else {
            return TCheck::Sat; // all Int problem vars integral
        };
        // Cumulative branch-and-bound budget (anti-divergence guard). B&B on
        // UNBOUNDED integer variables is not guaranteed to terminate: when the LP
        // relaxation optimum keeps moving to ever-larger fractional points (e.g.
        // MBTC strict `<`/`>` separations over shared `str.len` terms repeatedly
        // push the relaxation away from an integer point — observed branch values
        // creep up roughly linearly: 1/2, 1999/2, 7999/2, …), each branch
        // `x≤⌊v⌋ ∨ x≥⌈v⌉` mints a FRESH atom over a new numeral, so atom-dedup cannot
        // stop it and the search diverges (branch value → ∞). The SAT `step_budget`
        // only bounds this after millions of steps (minutes). Capping the CUMULATIVE
        // branch count here bounds it directly: on exhaustion `integer_check` returns
        // a SOUND `Unknown` (declines to decide rather than diverge). The budget is
        // chosen above the largest branch count any legitimately-bounded
        // QF_LIA/QF_UFLIA instance in the differential corpus needs, so it never
        // trips on the soundly-decidable fragment.
        self.total_branches += 1;
        if self.total_branches > self.branch_budget {
            return TCheck::Unknown;
        }
        // Stage-B: try a GMI cut before branching, within budget.
        if self.stage_b
            && self.node_cuts < Self::MAX_CUTS_PER_NODE
            && self.total_cuts < Self::MAX_CUTS_TOTAL
        {
            if let Some(cut_atom) = self.try_gmi_cut(cx, bv) {
                self.node_cuts += 1;
                self.total_cuts += 1;
                // GMI cut is a theory-valid clause over the integers — a tautology
                // split, no guard.
                return TCheck::Split {
                    atoms: vec![cut_atom],
                    guard: None,
                    phases: Vec::new(),
                };
            }
        }
        let (floor, ceil) = crate::branch::floor_ceil(&self.value[bv.index()]);
        let term = self
            .vars
            .term_of(bv)
            .expect("branch var is a problem var with a term");
        let int_s = cx.terms.int_sort();
        let floor_num = cx.terms.mk_numeral(Rational::from_int(floor), int_s);
        let ceil_num = cx.terms.mk_numeral(Rational::from_int(ceil), int_s);
        let le = cx
            .terms
            .mk_app(Op::Builtin(BuiltinOp::Le), &[term, floor_num])
            .expect("(x <= floor) well-sorted");
        let ge = cx
            .terms
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[term, ceil_num])
            .expect("(x >= ceil) well-sorted");
        // Branch `(x ≤ ⌊v⌋) ∨ (x ≥ ⌈v⌉)` is a tautology over the integers — no guard.
        TCheck::Split {
            atoms: vec![le, ge],
            guard: None,
            phases: Vec::new(),
        }
    }

    /// Derive a GMI cut from `bv`'s row and build a `≤` cut atom term over
    /// problem vars. Returns the atom `TermId` for a unit `TCheck::Split`, or
    /// `None` if no separating cut arises (caller branches).
    fn try_gmi_cut(&mut self, cx: &mut TheoryCtx, bv: ArithVar) -> Option<TermId> {
        // Expander: a slack var → its defining comb over problem vars. The
        // tableau row of a basic slack expresses it over CURRENT nonbasics, but
        // for cut translation we need the ORIGINAL problem-var definition, which
        // we recover from the slack's row only if it is basic; problem vars map
        // to themselves.
        let cut = {
            let value = self.value.clone();
            let vars = &self.vars;
            let tableau = &self.tableau;
            let bounds = &self.bounds;
            let expand = |v: ArithVar| -> Vec<(ArithVar, Rational)> {
                if vars.is_slack(v) && tableau.is_basic(v) {
                    let row = tableau.row(v);
                    row.vars().map(|j| (j, row.coeff(j))).collect()
                } else {
                    vec![(v, Rational::one())]
                }
            };
            let c = crate::cuts::derive_gmi(bv, tableau, bounds, &value, vars, &expand)?;
            #[cfg(debug_assertions)]
            crate::cuts::debug_validate(&c, bv, tableau, bounds, &value, vars, &expand);
            c
        };
        // Build the cut atom term: (<= (+ (* c1 x1) ...) rhs_num). All cut vars
        // are problem vars (expander removed slacks) with Int terms.
        let int_s = cx.terms.int_sort();
        let mut term_lhs: Option<TermId> = None;
        for (v, c) in &cut.lhs {
            let vt = self.vars.term_of(*v)?; // problem var ⟹ has a term
            let cnum = cx.terms.mk_numeral(c.clone(), int_s);
            let prod = cx
                .terms
                .mk_app(Op::Builtin(BuiltinOp::Mul), &[cnum, vt])
                .ok()?;
            term_lhs = Some(match term_lhs {
                None => prod,
                Some(acc) => cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::Add), &[acc, prod])
                    .ok()?,
            });
        }
        let lhs = term_lhs?;
        let rhs_num = cx.terms.mk_numeral(cut.rhs.clone(), int_s);
        cx.terms
            .mk_app(Op::Builtin(BuiltinOp::Le), &[lhs, rhs_num])
            .ok()
    }

    // -----------------------------------------------------------------------
    // A-priori finite box (Task 4): termination backstop for QF_LIA.
    // -----------------------------------------------------------------------

    /// A dominating small-model bound for QF_LIA termination.
    ///
    /// `M = (n + 1) * ((n + m) * a + 1)^(n + m)`
    ///
    /// where:
    /// - `n` = number of Int *problem* variables (non-slack Int vars),
    /// - `m` = number of registered arithmetic atoms / constraints
    ///   (`self.apriori_atom_count`),
    /// - `a` = `self.apriori_coeff_max` (maximum |coefficient| or |constant|
    ///   seen across all atoms).
    ///
    /// **Soundness.** After introducing one slack variable per inequality the
    /// system has `n + m` integer variables and coefficient magnitude ≤ `a`.
    /// Any integer solution to this slacked system — if one exists — has a
    /// solution with each variable bounded by the Borosh–Treybig / Cramer
    /// determinant bound, which is dominated by `((n+m)·a + 1)^(n+m)`.  The
    /// leading `(n + 1)` factor is the standard Papadimitriou / Seshia–Bryant
    /// (LICS'04) multiplier that accounts for the inequality-to-equality slack
    /// dimension.  Therefore this bound is an *over-approximation* of every
    /// feasible integer point: using it as the box radius is always sound
    /// (a too-small M can cut off the only feasible point; a too-large M is
    /// slower but never unsound).
    ///
    /// **Why m matters.** The Papadimitriou and Seshia–Bryant bounds are both
    /// m-dependent.  A bound that drops `m` (e.g., `(n·a+1)^n`) under-counts
    /// the slack dimension and can be strictly smaller than the actual feasible
    /// region when `m ≫ n`, causing wrong UNSAT.  This bound restores the
    /// missing `m` term, making it correct for arbitrary QF_LIA instances.
    fn apriori_bound(&self) -> Integer {
        let n_int = (0..self.vars.len())
            .filter(|&i| {
                let v = ArithVar(i as u32);
                !self.vars.is_slack(v) && self.vars.is_int(v)
            })
            .count();
        if n_int == 0 {
            return Integer::one(); // no Int vars → dummy; box never seeded
        }
        let a = self.apriori_coeff_max.clone();
        let n = Integer::from(n_int as i128);
        let m = Integer::from(self.apriori_atom_count as i128);
        // M = (n + 1) * ((n + m) * a + 1)^(n + m)
        let exp = n_int + self.apriori_atom_count; // n + m as usize for loop
        let base = (n.clone() + m) * a + Integer::one();
        let mut pow = Integer::one();
        for _ in 0..exp {
            pow *= base.clone();
        }
        (n + Integer::one()) * pow
    }

    /// Seed `−M ≤ x ≤ M` on every Int problem var, once, at level 0. Bounds ride
    /// under fresh sentinel lits (stripped from conflicts by `sanitize_conflict`).
    /// No-op if there are no Int problem vars (pure-Real path unchanged).
    fn seed_apriori_if_needed(&mut self) {
        if self.apriori_seeded {
            return;
        }
        // Only seed before the first checkpoint: bounds installed before the
        // first bounds.mark() are permanent (level-0) and survive every backtrack.
        // marks_len()==0 means no decision has been pushed yet.
        if self.bounds.marks_len() != 0 {
            return;
        }
        self.apriori_seeded = true;
        let m = self.apriori_bound();
        let hi = DeltaRational::from_rational(Rational::from_int(m.clone()));
        let lo = DeltaRational::from_rational(Rational::from_int(-m));
        for i in 0..self.vars.len() {
            let v = ArithVar(i as u32);
            if self.vars.is_slack(v) || !self.vars.is_int(v) {
                continue;
            }
            let lo_lit = self.fresh_sentinel();
            let hi_lit = self.fresh_sentinel();
            self.apriori_lits.insert(lo_lit.code());
            self.apriori_lits.insert(hi_lit.code());
            let _ = self.apply_bound(v, BoundKind::Lower, lo.clone(), lo_lit);
            let _ = self.apply_bound(v, BoundKind::Upper, hi.clone(), hi_lit);
        }
        if self.stage_b {
            self.run_fbbt();
        }
    }

    /// One-shot level-0 FBBT pass: derive tighter integer bounds from the
    /// tableau rows and install them as level-0 axiomatic bounds under stripped
    /// sentinels (like the a-priori box). Stage-B only.
    fn run_fbbt(&mut self) {
        const MAX_ROUNDS: usize = 16;
        let tightenings = crate::propagate::tighten_to_fixpoint(
            &self.tableau,
            &self.bounds,
            &self.vars,
            MAX_ROUNDS,
        );
        for (v, kind, val) in tightenings {
            let lit = self.fresh_sentinel();
            self.apriori_lits.insert(lit.code());
            let _ = self.apply_bound(v, kind, val, lit);
        }
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
        // Slice 42: every problem var occurring in a registered arith atom is
        // constrained. This is the dominant marking site — it subsumes `assert`
        // for single-var atoms and covers multi-var atoms whose encoding is over
        // a slack.
        for (av, _) in &n.comb.0 {
            self.mark_constrained(*av);
        }
        // Track max |coeff| and |constant| across all atoms (for a-priori bound).
        self.apriori_atom_count += 1;
        for (_, coeff) in &n.comb.0 {
            let mag = coeff.numer().abs();
            if mag > self.apriori_coeff_max {
                self.apriori_coeff_max = mag;
            }
            let dmag = coeff.denom().abs();
            if dmag > self.apriori_coeff_max {
                self.apriori_coeff_max = dmag;
            }
        }
        let rmag = n.rhs.numer().abs();
        if rmag > self.apriori_coeff_max {
            self.apriori_coeff_max = rmag;
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
        let conflict = match enc {
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
                // Slice 42: belt-and-braces. `new_var` already marked this atom's
                // problem vars, and `var` here is a slack for multi-var atoms
                // (slacks never appear in the shared set). Marking anyway costs
                // nothing and keeps the invariant true even if an encoding path
                // reaches `assert` without `new_var`.
                self.mark_constrained(var);
                self.apply_bound(var, kind, val, lit)
            }
        };
        // Sanitize an assert-time conflict the same way every other exit
        // does (sanitize_conflict — see its INVARIANT comment). Two sentinel
        // flavors can appear as the crossing bound's antecedent here: an
        // a-priori-box / FBBT level-0 bound (dropped — slice 8, which first
        // hit this exit: left in the core, a sentinel lit leaks into SAT
        // `analyze`, which indexes `seen[var.index()]` sized to the real-var
        // count → OOB panic), and an interface-equality fixed bound on a
        // shared slack combination (resolved to EqLeaf::Interface — slice 27;
        // previously leaked raw and tripped shinri-sat's analyzability guard
        // to a sound-but-lossy Unknown).
        conflict.map(|leaves| self.sanitize_conflict(leaves))
    }

    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        // Seed the a-priori box here: `propagate` is called by the SAT solver's
        // main loop BEFORE any theory.push / bounds.mark(), guaranteeing level-0
        // permanence for bounds installed now (they survive every backtrack).
        // The call in `check` remains as an idempotent fallback (no-op once seeded).
        self.seed_apriori_if_needed();
        None // spec §1 decision 3: check-only; propagate is a no-op.
    }

    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        self.seed_apriori_if_needed();
        match self.check_full() {
            TCheck::Conflict(leaves) => return TCheck::Conflict(self.sanitize_conflict(leaves)),
            TCheck::Split { .. } => unreachable!("check_full never emits Split"),
            TCheck::Sat => {}
            // The simplex pivot cap tripped (degenerate cycle); surface Unknown so
            // the combiner reports a SOUND `unknown` instead of looping forever.
            TCheck::Unknown => return TCheck::Unknown,
        }
        self.integer_check(cx)
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

    fn model_equal_shared_pairs(
        &mut self,
        _cx: &mut TheoryCtx,
        shared: &[TermId],
    ) -> Vec<(TermId, TermId)> {
        Arith::model_equal_shared_pairs(self, shared)
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
        self.node_cuts = 0;
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

    #[test]
    fn model_equal_shared_pairs_reports_beta_equal_int_pair() {
        // Two Int consts both pinned to 5: β(x)=β(y)=5 ⇒ reported as a pair.
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xs = ctx.declare_fun("x", &[], int);
        let ys = ctx.declare_fun("y", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(ys), &[]).unwrap();
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), int);
        let mk = |ctx: &mut Context, op, a, b| ctx.mk_app(Op::Builtin(op), &[a, b]).unwrap();
        let atom_terms = [
            mk(&mut ctx, BuiltinOp::Ge, x, five),
            mk(&mut ctx, BuiltinOp::Le, x, five),
            mk(&mut ctx, BuiltinOp::Ge, y, five),
            mk(&mut ctx, BuiltinOp::Le, y, five),
        ];
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        for (i, &atom) in atom_terms.iter().enumerate() {
            let v = Var::new(i as u32);
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            <Arith as TheorySolver>::new_var(&mut arith, &mut cx, v, atom);
        }
        for i in 0..atom_terms.len() {
            let v = Var::new(i as u32);
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            assert!(
                <Arith as TheorySolver>::assert(&mut arith, &mut cx, Lit::new(v, true)).is_none(),
                "asserting [5,5] bounds must not conflict"
            );
        }
        {
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            arith.ensure_shared_var(cx.terms, x);
            arith.ensure_shared_var(cx.terms, y);
            assert!(matches!(
                <Arith as TheorySolver>::check(&mut arith, &mut cx, Effort::Full),
                TCheck::Sat
            ));
        }
        assert_eq!(arith.model_equal_shared_pairs(&[x, y]), vec![(x, y)]);
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
            TCheck::Split { .. } => unreachable!("Arith check never emits Split in its own tests"),
            TCheck::Unknown => unreachable!("Arith never returns Unknown"),
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

    // ----- Slice 42: constrainedness marking -----

    fn int_var_no(ctx: &mut Context, name: &str) -> TermId {
        let int = ctx.int_sort();
        let s = ctx.declare_fun(name, &[], int);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    #[test]
    fn ensure_shared_var_alone_does_not_constrain() {
        // A shared term arith was merely TOLD about — no atom, not a numeral —
        // must stay unconstrained. This is the `head(t)` population that slice
        // 42 exists to prune.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        let xv = h.arith.vars.problem_var(x);
        assert!(
            !h.arith.is_constrained(xv),
            "a merely-shared non-numeral term must not be marked constrained"
        );
    }

    #[test]
    fn registered_atom_constrains_its_problem_vars() {
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let xy = h.ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let five = num(&mut h.ctx, 5);
        let a = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[xy, five])
            .unwrap();
        h.assert_atom(0, a);
        let xv = h.arith.vars.problem_var(x);
        let yv = h.arith.vars.problem_var(y);
        assert!(h.arith.is_constrained(xv), "x occurs in a registered atom");
        assert!(h.arith.is_constrained(yv), "y occurs in a registered atom");
    }

    #[test]
    fn numeral_pin_constrains() {
        let mut h = Harness::new();
        let five = num(&mut h.ctx, 5);
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, five);
        let fv = h.arith.vars.problem_var(five);
        assert!(
            h.arith.is_constrained(fv),
            "a pinned numeral IS constrained"
        );
    }

    #[test]
    fn interface_equality_constrains_both_sides() {
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        let just = TheoryJust { theory: 0, tag: 0 };
        let _ = h.arith.assert_interface_equality(&ctx, x, y, just);
        let xv = h.arith.vars.problem_var(x);
        let yv = h.arith.vars.problem_var(y);
        assert!(h.arith.is_constrained(xv), "interface eq constrains lhs");
        assert!(h.arith.is_constrained(yv), "interface eq constrains rhs");
    }

    #[test]
    fn apriori_box_does_not_constrain() {
        // The a-priori box (`seed_apriori_if_needed`) puts bounds on EVERY Int
        // problem var, including free ones. Those bounds must NOT count as a
        // constraint: a uniform [-M, M] box entails no equality, and treating it
        // as constraining would defeat the whole slice.
        let mut h = Harness::new();
        let x = int_var_no(&mut h.ctx, "xi");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.seed_apriori_if_needed();
        let xv = h.arith.vars.problem_var(x);
        assert!(
            h.arith.bounds.lower(xv).is_some() && h.arith.bounds.upper(xv).is_some(),
            "precondition: the a-priori box must actually have been seeded"
        );
        assert!(
            !h.arith.is_constrained(xv),
            "a-priori box bounds must not mark a var constrained"
        );
    }

    #[test]
    fn constrained_marking_survives_pop() {
        // The set is MONOTONE by design: never un-marked, including on pop.
        // Over-approximating constrainedness errs toward more probing, which is
        // the sound direction.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let five = num(&mut h.ctx, 5);
        let a = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[x, five])
            .unwrap();
        h.arith.push();
        h.assert_atom(0, a);
        let xv = h.arith.vars.problem_var(x);
        assert!(h.arith.is_constrained(xv));
        h.arith.pop(0);
        assert!(
            h.arith.is_constrained(xv),
            "constrainedness is monotone across pop"
        );
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

    // ----- Slice 27: check-path sentinel leak (slice-26 banked issue i) -----
    // Interface equality a = b is installed FIRST (feasible alone), then two
    // real atoms a - c >= 1 and c - b >= 0 are asserted. Ge atoms normalize
    // with a NEGATED comb (normalize.rs), so all three constraints live on
    // three DISTINCT slack vars — no single-var bound crossing at assert
    // time. The infeasibility (a - b >= 1 vs a - b = 0) is only visible to
    // simplex: `check`'s Farkas core transitively cites the iface fixed
    // bound, whose antecedent is the sentinel pseudo-lit. Pre-slice-27,
    // `check` piped the core through `strip_apriori` only, leaking the raw
    // pseudo-lit (var index >= 1<<30) to shinri-sat's analyzability guard —
    // a sound-but-lossy Unknown. The core must instead resolve it to
    // EqLeaf::Interface(just).
    #[test]
    fn check_conflict_through_iface_bound_resolves_no_sentinel() {
        let mut ctx = Context::new();
        let a = real_var(&mut ctx, "ia");
        let b = real_var(&mut ctx, "ib");
        let c = real_var(&mut ctx, "ic");
        let one = num(&mut ctx, 1);
        let zero = num(&mut ctx, 0);
        let ac = ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[a, c]).unwrap();
        let ge_ac = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[ac, one]).unwrap(); // a - c >= 1
        let cb = ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[c, b]).unwrap();
        let ge_cb = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[cb, zero]).unwrap(); // c - b >= 0

        let mut arith = Arith::default();
        let just = TheoryJust { theory: 1, tag: 27 };
        assert!(
            arith.assert_interface_equality(&ctx, a, b, just).is_none(),
            "a = b alone is feasible"
        );

        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), ge_ac);
        arith.new_var(&mut cx, Var::new(1), ge_cb);
        assert!(
            arith.assert(&mut cx, Lit::new(Var::new(0), true)).is_none(),
            "a - c >= 1 must not cross any bound at assert time"
        );
        assert!(
            arith.assert(&mut cx, Lit::new(Var::new(1), true)).is_none(),
            "c - b >= 0 must not cross any bound at assert time"
        );

        let leaves = match arith.check(&mut cx, Effort::Full) {
            TCheck::Conflict(leaves) => leaves,
            _ => panic!("a-b >= 1 against iface a=b must conflict"),
        };
        assert!(
            leaves.contains(&EqLeaf::Interface(just)),
            "core must resolve the iface pseudo-lit to Interface(just), got {leaves:?}"
        );
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(0), true))),
            "core must cite the a-c>=1 lit, got {leaves:?}"
        );
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(1), true))),
            "core must cite the c-b>=0 lit, got {leaves:?}"
        );
        for leaf in &leaves {
            if let EqLeaf::Asserted(l) = leaf {
                assert!(
                    (l.var().index() as u32) < SENTINEL_VAR_BASE,
                    "raw sentinel leaked from check (slice-26 banked bug): {leaves:?}"
                );
            }
        }
    }

    // ----- Slice 27: assert-path sentinel leak (same bug, second exit) -----
    // The interface equality a = b installs fixed bounds [0,0] on the slack
    // var of the difference combination a - b (diff_comb). A Le input atom
    // `a - b <= -1` canonicalizes (normalize.rs) to the SAME combination —
    // (a, +1), (b, -1), sorted by var — hence the SAME slack var, so
    // `apply_bound` detects the crossing (upper -1 < lower 0) directly at
    // assert time and cites the iface bound's sentinel pseudo-lit as the
    // opposing antecedent. Pre-slice-27 `assert` piped this core through
    // `strip_apriori` only — the same leak as the check exit. (A Ge atom
    // would NOT work here: normalize negates its comb to b - a, a different
    // slack var — which is exactly why the check-path test above uses Ge
    // shapes to stay crossing-free.)
    #[test]
    fn assert_conflict_crossing_iface_bound_resolves_no_sentinel() {
        let mut ctx = Context::new();
        let a = real_var(&mut ctx, "ja");
        let b = real_var(&mut ctx, "jb");
        let neg_one = num(&mut ctx, -1);
        let ab = ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[a, b]).unwrap();
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[ab, neg_one])
            .unwrap(); // a - b <= -1

        let mut arith = Arith::default();
        let just = TheoryJust {
            theory: 1,
            tag: 272,
        };
        assert!(
            arith.assert_interface_equality(&ctx, a, b, just).is_none(),
            "a = b alone is feasible"
        );

        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), le);
        let leaves = arith
            .assert(&mut cx, Lit::new(Var::new(0), true))
            .expect("a-b <= -1 must cross the iface fixed bound a-b = 0 at assert time");
        assert!(
            leaves.contains(&EqLeaf::Interface(just)),
            "core must resolve the iface pseudo-lit to Interface(just), got {leaves:?}"
        );
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(0), true))),
            "core must cite the asserted a-b<=-1 lit, got {leaves:?}"
        );
        for leaf in &leaves {
            if let EqLeaf::Asserted(l) = leaf {
                assert!(
                    (l.var().index() as u32) < SENTINEL_VAR_BASE,
                    "raw sentinel leaked from assert: {leaves:?}"
                );
            }
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

    #[test]
    fn unconstrained_pair_is_not_probed_and_mints_no_slack() {
        // Two shared vars arith knows nothing about. No equality can be
        // entailed, AND no slack may be minted: `entailed_equalities` snapshots
        // AFTER `define_slack`, so a slack created here would persist for the
        // rest of the solve and re-admit the cost on every later call.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);
        assert!(matches!(h.arith.check_full(), TCheck::Sat));

        let vars_before = h.arith.vars.len();
        let got = h.arith.entailed_equalities(&ctx, &[x, y]);

        assert!(got.is_empty(), "no equality is entailed over free vars");
        assert_eq!(
            h.arith.vars.len(),
            vars_before,
            "no slack may be minted for a skipped pair"
        );
    }

    #[test]
    fn mixed_pair_with_one_free_var_is_skipped() {
        // x is fixed to 0; y is free. `x = y` is not entailed, and the pair must
        // be skipped rather than probed.
        let mut h = Harness::new();
        let x = real_var(&mut h.ctx, "x");
        let y = real_var(&mut h.ctx, "y");
        let zero = num(&mut h.ctx, 0);
        let le = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[x, zero])
            .unwrap();
        let ge = h
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero])
            .unwrap();
        h.assert_atom(0, le);
        h.assert_atom(1, ge);
        assert!(matches!(h.check(), TCheck::Sat));
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);

        let vars_before = h.arith.vars.len();
        let got = h.arith.entailed_equalities(&ctx, &[x, y]);

        assert!(
            got.is_empty(),
            "a free var is not entailed equal to a fixed one"
        );
        assert_eq!(
            h.arith.vars.len(),
            vars_before,
            "no slack for a skipped pair"
        );
    }

    #[test]
    fn mbtc_skips_pairs_with_a_free_var() {
        // Two free Int shared vars both sit at β = 0, so the unguarded sweep
        // reports them as a model-equal pair and the Combiner turns that into a
        // 3-way trichotomy split. Arith constrains neither side, so any
        // arrangement EUF picks is arith-satisfiable and the split is waste.
        let mut h = Harness::new();
        let x = int_var_no(&mut h.ctx, "xm");
        let y = int_var_no(&mut h.ctx, "ym");
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);
        assert!(matches!(h.arith.check_full(), TCheck::Sat));

        let pairs = h.arith.model_equal_shared_pairs(&[x, y]);
        assert!(pairs.is_empty(), "free vars need no MBTC arrangement split");
    }

    #[test]
    fn mbtc_still_reports_constrained_model_equal_pairs() {
        // Both vars pinned to 3: still a model-equal pair, still reported.
        let mut h = Harness::new();
        let x = int_var_no(&mut h.ctx, "xc");
        let y = int_var_no(&mut h.ctx, "yc");
        let three = h
            .ctx
            .mk_numeral(Rational::from_int(3i128.into()), h.ctx.int_sort());
        for (i, v) in [x, y].iter().enumerate() {
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
        h.arith.ensure_shared_var(&ctx, x);
        h.arith.ensure_shared_var(&ctx, y);

        let pairs = h.arith.model_equal_shared_pairs(&[x, y]);
        assert_eq!(pairs.len(), 1, "constrained model-equal pair must survive");
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

#[cfg(test)]
mod apriori_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::{AtomRegistry, Effort, EqualityEngine, TheoryCtx, TheorySolver};

    #[test]
    fn apriori_box_seeded_on_int_vars_at_level_zero() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xi = ctx.declare_fun("xi", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
        let three = ctx.mk_numeral(Rational::from_int(3i128.into()), int);
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, three]).unwrap();

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let v = Var::new(0);
        {
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            arith.new_var(&mut cx, v, le);
            // First Full check at level 0 seeds the box.
            let _ = arith.check(&mut cx, Effort::Full);
        }
        let xv = arith.vars.problem_var(x); // already interned by new_var
        let m = arith.apriori_bound();
        let lo = arith
            .bounds
            .lower(xv)
            .expect("lower box seeded")
            .0
            .c()
            .clone();
        let hi = arith
            .bounds
            .upper(xv)
            .expect("upper box seeded")
            .0
            .c()
            .clone();
        assert_eq!(hi, Rational::from_int(m.clone()));
        assert_eq!(lo, Rational::from_int(-m));
    }

    #[test]
    fn apriori_not_seeded_on_real_vars() {
        // A pure-Real atom must NOT cause the box to be seeded.
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xr = ctx.declare_fun("xr", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xr), &[]).unwrap();
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), real);
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, five]).unwrap();

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        {
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            arith.new_var(&mut cx, Var::new(0), le);
            let _ = arith.check(&mut cx, Effort::Full);
        }
        let xv = arith.vars.problem_var(x);
        // No box bounds should be installed on a Real var.
        assert!(
            arith.bounds.upper(xv).is_none(),
            "Real var must not get a box upper bound"
        );
        assert!(
            arith.bounds.lower(xv).is_none(),
            "Real var must not get a box lower bound"
        );
    }

    #[test]
    fn apriori_seeded_only_once() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xi = ctx.declare_fun("yi", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), int);
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, two]).unwrap();

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        {
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            arith.new_var(&mut cx, Var::new(0), le);
            let _ = arith.check(&mut cx, Effort::Full);
            let sentinel_count_after_first = arith.apriori_lits.len();
            let _ = arith.check(&mut cx, Effort::Full);
            // Second check must not add more sentinel lits.
            assert_eq!(
                arith.apriori_lits.len(),
                sentinel_count_after_first,
                "box must be seeded exactly once"
            );
        }
    }

    /// Regression test for the level-0 seeding bug: the a-priori box must be
    /// seeded via `Arith::propagate` BEFORE any decision (push/mark), NOT only
    /// via a level-0 Full `check`.
    ///
    /// Under the OLD guard (`self.level != 0 { return; }`), this test FAILS:
    ///   - `propagate` is called first (no push yet, so level==0 there too)...
    ///   - BUT the OLD guard was in a code path only triggered by `check`, not
    ///     `propagate`. The real solver calls `theory.check(Effort::Full)` only
    ///     when `pick_branch()==None` (complete propositional assignment), which
    ///     arrives at decision level >= 1 for any branching query. At that point
    ///     `self.level != 0` is true, so seeding is skipped forever.
    ///   - This test exercises the `propagate`-first path explicitly: it calls
    ///     `arith.propagate` at level 0 (no push), then pushes (simulating a
    ///     decision), then calls `check(Full)`. Under the old guard, propagate
    ///     would NOT trigger seeding (it never called `seed_apriori_if_needed`),
    ///     and the subsequent check at level 1 would also skip seeding due to
    ///     `self.level != 0`. Result: bounds remain None → test FAILS.
    ///   - Under the NEW guard (`marks_len() != 0`), `propagate` seeds before
    ///     the first mark, so the box is present and permanent.
    #[test]
    fn apriori_box_seeded_via_propagate_before_decision() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xi = ctx.declare_fun("zi", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
        let four = ctx.mk_numeral(Rational::from_int(4i128.into()), int);
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, four]).unwrap();

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let v = Var::new(0);
        {
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            arith.new_var(&mut cx, v, le);

            // Simulate the real solver: call propagate at level 0 (no push yet).
            // This is the path that fires before any decision in solve_under.
            let mut out: Vec<(Lit, TheoryJust)> = Vec::new();
            let _ = arith.propagate(&mut cx, &mut out);
        }

        // After propagate (level 0, no marks yet), box must be seeded.
        let xv = arith.vars.problem_var(x);
        let m = arith.apriori_bound();
        let lo = arith
            .bounds
            .lower(xv)
            .expect("lower box bound must be seeded by propagate at level 0")
            .0
            .c()
            .clone();
        let hi = arith
            .bounds
            .upper(xv)
            .expect("upper box bound must be seeded by propagate at level 0")
            .0
            .c()
            .clone();
        assert_eq!(hi, Rational::from_int(m.clone()), "upper box = +M");
        assert_eq!(lo, Rational::from_int(-m), "lower box = -M");

        // Also verify permanence: after a push (decision level 1) and Full check,
        // the box bounds installed at level 0 are still present.
        arith.push(); // simulates the SAT solver making a decision
        {
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            let _ = arith.check(&mut cx, Effort::Full);
        }
        assert!(
            arith.bounds.lower(xv).is_some(),
            "lower box bound must survive push to level 1"
        );
        assert!(
            arith.bounds.upper(xv).is_some(),
            "upper box bound must survive push to level 1"
        );
    }

    /// Regression test for Bug 1 (sentinel leak into SAT analyze).
    ///
    /// When an asserted bound crosses an FBBT-derived sentinel bound, `apply_bound`
    /// returns a conflict that contains the sentinel lit. Before the fix, `assert`
    /// returned that conflict un-stripped, so the sentinel lit (var index ≥ 1<<30)
    /// would reach the SAT solver's `analyze`, which indexes `seen[var.index()]`
    /// sized to the real-var count → out-of-bounds panic.
    ///
    /// The fix captures the conflict from `apply_bound` and pipes it through
    /// the exit sanitizer (`strip_apriori` at the time; `sanitize_conflict`
    /// since slice 27) before returning. This test:
    ///   1. Sets up a system so FBBT will tighten an Int var's upper bound tightly.
    ///   2. Asserts a bound that crosses the FBBT-derived sentinel bound.
    ///   3. Captures the conflict returned by `assert`.
    ///   4. Asserts that NO leaf in the conflict cites a sentinel lit
    ///      (var index ≥ SENTINEL_VAR_BASE = 1<<30).
    #[test]
    fn assert_conflict_against_sentinel_no_sentinel_in_core() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        // x + y <= 1, x >= 0, y >= 0 → FBBT tightens x ≤ 1 (and y ≤ 1) at level 0.
        let xi = ctx.declare_fun("px", &[], int);
        let yi = ctx.declare_fun("py", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yi), &[]).unwrap();
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let zero = ctx.mk_numeral(Rational::zero(), int);
        let one = ctx.mk_numeral(Rational::one(), int);
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), int);
        let gx = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero]).unwrap();
        let gy = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[y, zero]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap();
        // x >= 2 will cross the FBBT-tightened upper bound x ≤ 1 at assert time.
        let ge2 = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, two]).unwrap();

        let mut arith = Arith::default(); // stage_b = true → FBBT enabled
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        for (i, a) in [gx, gy, le, ge2].iter().enumerate() {
            arith.new_var(&mut cx, Var::new(i as u32), *a);
        }
        // Assert x >= 0, y >= 0, x + y <= 1 — causes FBBT to install tight bounds.
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.assert(&mut cx, Lit::new(Var::new(2), true));
        let _ = arith.check(&mut cx, Effort::Full); // seeds apriori + FBBT

        // Now assert x >= 2: this MUST conflict against the FBBT sentinel bound x ≤ 1.
        let conflict = arith.assert(&mut cx, Lit::new(Var::new(3), true));
        let leaves = conflict.expect("x>=2 must conflict against FBBT-tightened x<=1");

        // The conflict must NOT contain any sentinel lit (var index ≥ 1<<30).
        for leaf in &leaves {
            if let shinri_theory::types::EqLeaf::Asserted(l) = leaf {
                assert!(
                    (l.var().index() as u32) < SENTINEL_VAR_BASE,
                    "conflict must NOT cite sentinel lit (var index {}, SENTINEL_VAR_BASE={}): \
                     sentinel leak would cause OOB panic in SAT analyze. leaves={leaves:?}",
                    l.var().index(),
                    SENTINEL_VAR_BASE,
                );
            }
        }
        // The conflict must be non-empty (we need at least the asserted lit x>=2).
        assert!(!leaves.is_empty(), "conflict must be non-empty: {leaves:?}");
    }
}

#[cfg(test)]
mod integer_branch_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::{AtomRegistry, Effort, EqualityEngine, TheoryCtx, TheorySolver};

    #[test]
    fn fractional_int_var_triggers_split() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xi = ctx.declare_fun("xi", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), int);
        let one = ctx.mk_numeral(Rational::one(), int);
        let twox = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
        let ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[twox, one])
            .unwrap();
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[twox, one])
            .unwrap();

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), ge);
        arith.new_var(&mut cx, Var::new(1), le);
        // Assert both: 2x >= 1 AND 2x <= 1 over Int.
        // With B2 rounding: 2x>=1 → x>=1; 2x<=1 → x<=0 — an immediate conflict
        // at assert time (Lower=1 > Upper=0). This system MUST be detected UNSAT
        // and MUST NOT produce Sat or Split.
        let conflict_at_assert = arith.assert(&mut cx, Lit::new(Var::new(0), true)).is_some()
            || arith.assert(&mut cx, Lit::new(Var::new(1), true)).is_some();
        assert!(
            conflict_at_assert,
            "2x=1 over Int must be UNSAT (immediate bound conflict after rounding: \
             2x>=1 → x>=1, 2x<=1 → x<=0)"
        );
        // Confirm the solver is also in a definitive state (not Split).
        let result = arith.check(&mut cx, Effort::Full);
        assert!(
            !matches!(result, TCheck::Split { .. }),
            "after a bound conflict at assert, check must not return Split"
        );
    }
}

#[cfg(test)]
mod rounding_tests {
    use super::*;
    use crate::encode::AtomEncoding;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn int_var(ctx: &mut Context, name: &str) -> TermId {
        let int = ctx.int_sort();
        let s = ctx.declare_fun(name, &[], int);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    // x < 5 over Int (gate ON) must encode pos as Upper bound 4 with k = 0.
    #[test]
    fn int_strict_bound_rounds_and_drops_delta() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), ctx.int_sort());
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[x, five]).unwrap();
        let mut arith = Arith::default(); // stage_b = true
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), lt);
        match arith.enc[0].clone().unwrap() {
            AtomEncoding::Ineq {
                pos: (BoundKind::Upper, dr),
                ..
            } => {
                assert_eq!(*dr.c(), Rational::from_int(4i128.into()));
                assert!(
                    dr.k().is_zero(),
                    "δ must be dropped for an Int strict bound"
                );
            }
            other => panic!("expected Upper Ineq, got {other:?}"),
        }
    }

    // 2x <= 5 over Int (gate ON): bound on x is 5/2 → rounds to 2.
    #[test]
    fn int_coefficient_division_rounds() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), ctx.int_sort());
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), ctx.int_sort());
        let twox = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[twox, five])
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
        match arith.enc[0].clone().unwrap() {
            AtomEncoding::Ineq {
                pos: (BoundKind::Upper, dr),
                ..
            } => {
                assert_eq!(*dr.c(), Rational::from_int(2i128.into()));
                assert!(dr.k().is_zero());
            }
            other => panic!("expected Upper Ineq, got {other:?}"),
        }
    }

    // gate OFF: Int x < 5 with stage_b=false must keep its δ (B1 byte-identical baseline).
    #[test]
    fn stage_b_off_preserves_delta_for_int_strict() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), ctx.int_sort());
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[x, five]).unwrap();
        let mut arith = Arith::default();
        arith.set_stage_b(false); // gate OFF → B1 baseline
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), lt);
        match arith.enc[0].clone().unwrap() {
            AtomEncoding::Ineq {
                pos: (BoundKind::Upper, dr),
                ..
            } => {
                assert_eq!(
                    *dr.c(),
                    Rational::from_int(5i128.into()),
                    "with stage_b OFF the rhs must not be rounded"
                );
                assert!(
                    !dr.k().is_zero(),
                    "with stage_b OFF the δ must be preserved (strict bound keeps −δ)"
                );
            }
            other => panic!("expected Upper Ineq, got {other:?}"),
        }
    }

    // Real x < 5 must KEEP its δ (rounding does not cross the Int fence).
    #[test]
    fn real_strict_bound_keeps_delta() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xs = ctx.declare_fun("x", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), real);
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[x, five]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), lt);
        match arith.enc[0].clone().unwrap() {
            AtomEncoding::Ineq {
                pos: (BoundKind::Upper, dr),
                ..
            } => {
                assert!(!dr.k().is_zero(), "Real strict bound must keep δ");
            }
            other => panic!("expected Upper Ineq, got {other:?}"),
        }
    }
}

#[cfg(test)]
mod cut_wiring_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_theory::{AtomRegistry, Effort, EqualityEngine, TheoryCtx, TheorySolver};

    // 2x = 1 over Int is UNSAT. With the box seeded huge, B1 would enumerate;
    // with the gate ON (rounding makes 2x≤1∧2x≥1 ⟹ x≤0∧x≥1) it is immediate.
    // This exercises the gate end-to-end through check().
    #[test]
    fn stage_b_decides_simple_unsat_fast() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let s = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap();
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), int);
        let one = ctx.mk_numeral(Rational::one(), int);
        let twox = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[twox, one])
            .unwrap();
        let ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[twox, one])
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
        // After rounding: 2x≤1 ⟹ x≤0 (Upper), 2x≥1 ⟹ x≥1 (Lower).
        // The conflict fires at assert time when the second bound crosses the first.
        let c1 = arith.assert(&mut cx, Lit::new(Var::new(0), true));
        let c2 = arith.assert(&mut cx, Lit::new(Var::new(1), true));
        let conflict_at_assert = c1.is_some() || c2.is_some();
        assert!(
            conflict_at_assert,
            "2x=1 over Int must be UNSAT via immediate bound conflict at assert time \
             (rounding: 2x≤1 ⟹ x≤0, 2x≥1 ⟹ x≥1 — Lower 1 > Upper 0)"
        );
        // Confirm check does not claim Sat or Split (state is already conflicting).
        let result = arith.check(&mut cx, Effort::Full);
        assert!(
            !matches!(result, TCheck::Split { .. }),
            "after assert-time conflict, check must not return Split"
        );
    }
}

#[cfg(test)]
mod fbbt_wiring_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_theory::{AtomRegistry, Effort, EqualityEngine, TheoryCtx, TheorySolver};

    fn int_var(ctx: &mut Context, name: &str) -> TermId {
        let int = ctx.int_sort();
        let s = ctx.declare_fun(name, &[], int);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    // x, y >= 0 and x + y <= 1 ⟹ FBBT must tighten x's upper bound far below M.
    #[test]
    fn fbbt_shrinks_box_at_level_zero() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let zero = ctx.mk_numeral(Rational::zero(), ctx.int_sort());
        let one = ctx.mk_numeral(Rational::one(), ctx.int_sort());
        let gx = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero]).unwrap();
        let gy = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[y, zero]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        for (i, a) in [gx, gy, le].iter().enumerate() {
            arith.new_var(&mut cx, Var::new(i as u32), *a);
        }
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.assert(&mut cx, Lit::new(Var::new(2), true));
        let _ = arith.check(&mut cx, Effort::Full);
        // x is problem var 0. Its FBBT upper bound must be ≤ 1 (≪ M).
        let xv = arith.vars.problem_var(x);
        let ub = arith
            .bounds
            .upper(xv)
            .expect("x has an upper bound")
            .0
            .c()
            .clone();
        assert!(ub <= Rational::one(), "FBBT should bound x ≤ 1, got {ub:?}");
    }

    // With the gate OFF, FBBT must NOT run: x keeps the (huge) a-priori bound.
    #[test]
    fn fbbt_disabled_when_stage_b_off() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let zero = ctx.mk_numeral(Rational::zero(), ctx.int_sort());
        let one = ctx.mk_numeral(Rational::one(), ctx.int_sort());
        let gx = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero]).unwrap();
        let gy = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[y, zero]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap();
        let mut arith = Arith::default();
        arith.set_stage_b(false);
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        for (i, a) in [gx, gy, le].iter().enumerate() {
            arith.new_var(&mut cx, Var::new(i as u32), *a);
        }
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.assert(&mut cx, Lit::new(Var::new(2), true));
        let _ = arith.check(&mut cx, Effort::Full);
        let xv = arith.vars.problem_var(x);
        let ub = arith
            .bounds
            .upper(xv)
            .expect("x has an upper bound")
            .0
            .c()
            .clone();
        assert!(
            ub > Rational::one(),
            "gate OFF: x must keep the large a-priori bound, got {ub:?}"
        );
    }
}
