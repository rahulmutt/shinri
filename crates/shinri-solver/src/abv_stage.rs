//! QF_ABV detection, fence, and the real `SatBridge` over the live SAT solver.
//!
//! ## Pipeline
//! 1. `uses_arrays_over_bv` decides whether `check_sat` should route here: true
//!    iff a `select`/`store`/array-eq over a `(Array (_ BitVec _) (_ BitVec _))`
//!    is present. Arrays with an uninterpreted index or element are NOT QF_ABV —
//!    they go to the EUF/Arrays Combiner path, so detection returns false.
//! 2. `fenced` is the soundness fence: BV-arrays mixed with a non-BV/non-array
//!    theory atom (EUF/arith/uninterpreted-sort) are out of scope → the caller
//!    returns Unknown.
//! 3. `solve_qfabv` builds the pure-BV+Bool abstraction (`shinri_abv`), wires it
//!    into a `RealBridge` over a live `NoTheory` SAT solver + a persistent
//!    `shinri_bv::Blaster`, and runs the lemmas-on-demand `refine` loop.
//!
//! ## Why a `NoTheory` solver (adaptation vs the existing BV path)
//! After abstraction every assertion is pure BV + Boolean structure (BV atoms,
//! array-eq Bool proxies, and connectives). No lazy theory atom survives, so we
//! do NOT need the `Combiner` (EUF/Arith/Arrays) machinery — and we MUST avoid
//! it, because the existing `Encoder` would register the Bool proxy constants as
//! EUF atoms. We therefore run a `shinri_sat::Solver<NoTheory, ..>` and Tseitin-
//! encode the (small) abstracted Boolean skeleton ourselves, mapping BV atoms to
//! their pre-blasted surrogate literals and array-eq proxies to fresh SAT vars.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Lit, Op, SortNode, TermId, TermNode, Var};

/// True iff `t`'s sort is `(Array (_ BitVec _) (_ BitVec _))` — both index and
/// element are bit-vectors. Arrays with an uninterpreted index/element are NOT
/// QF_ABV arrays (they belong to the Combiner / QF_AX path).
fn is_bv_array(ctx: &Context, t: TermId) -> bool {
    match ctx.sort_node(ctx.sort_of(t)) {
        SortNode::Array(i, e) => ctx.bv_width(*i).is_some() && ctx.bv_width(*e).is_some(),
        _ => false,
    }
}

/// True iff a `select`/`store`/array-(dis)equality over a BV-indexed,
/// BV-valued array appears in any assertion.
pub fn uses_arrays_over_bv(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen = rustc_hash::FxHashSet::default();
    assertions.iter().any(|&a| walk_uses(ctx, a, &mut seen))
}

fn walk_uses(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
    if !seen.insert(t) {
        return false;
    }
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            let kids = ctx.children(*args).to_vec();
            // select/store over a BV array.
            let access_hit = matches!(
                op,
                Op::Builtin(BuiltinOp::Select) | Op::Builtin(BuiltinOp::Store)
            ) && kids.first().is_some_and(|&k| is_bv_array(ctx, k));
            // array (dis)equality whose operands are BV arrays.
            let eq_hit = matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct))
                && kids.first().is_some_and(|&k| is_bv_array(ctx, k));
            access_hit || eq_hit || kids.iter().any(|&k| walk_uses(ctx, k, seen))
        }
        TermNode::Const { .. } => false,
    }
}

/// Soundness fence (SOUNDNESS-CRITICAL, conservative). Given that the query DOES
/// use BV-arrays, returns true iff it ALSO contains a Bool-sorted atom that is
/// not in scope. In-scope atoms are: a BV predicate / BV (dis)equality (handled
/// by the bit-blaster); an array operation (select/store/array-eq — handled by
/// refinement); and pure Boolean structure (And/Or/Not/Implies/Xor/Ite, plus
/// Bool iff/xor). Anything else — EUF over an uninterpreted sort, an arithmetic
/// relation, an array over an uninterpreted index/element, an uninterpreted
/// predicate — would route to a theory we cannot combine with the eager
/// abstraction here, so it fences and the caller returns Unknown.
pub fn fenced(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut visited = rustc_hash::FxHashSet::default();
    assertions.iter().any(|&a| walk_fence(ctx, a, &mut visited))
}

fn walk_fence(ctx: &Context, t: TermId, visited: &mut rustc_hash::FxHashSet<TermId>) -> bool {
    if !visited.insert(t) {
        return false;
    }
    let bool_sort = ctx.bool_sort();
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            // Pure Boolean structure: not an atom, recurse into children.
            let is_bool_structure = matches!(
                op,
                Op::Builtin(
                    BuiltinOp::Not
                        | BuiltinOp::And
                        | BuiltinOp::Or
                        | BuiltinOp::Implies
                        | BuiltinOp::Xor
                        | BuiltinOp::Ite
                )
            );
            // Bool-operand (dis)equality is iff/xor — Boolean structure.
            let is_bool_eq = matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct))
                && kids.first().is_some_and(|&k| ctx.sort_of(k) == bool_sort);
            if is_bool_structure || is_bool_eq {
                return kids.iter().any(|&k| walk_fence(ctx, k, visited));
            }
            // BV predicate atom: in scope.
            if is_bv_predicate(op) {
                return false;
            }
            // (dis)equality whose operands are BV-sorted or BV-array-sorted: in scope.
            if matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct)) {
                if let Some(&k) = kids.first() {
                    if is_bv_sorted(ctx, k) || is_bv_array(ctx, k) {
                        // BV / BV-array (dis)equality is handled; do not descend into
                        // BV operands (they are not Bool atoms) but DO descend into
                        // array operands so a nested out-of-scope atom is still found.
                        return kids.iter().any(|&k| walk_fence(ctx, k, visited));
                    }
                    // A (dis)equality over an uninterpreted/arith/array-with-
                    // uninterpreted-index sort is out of scope.
                    return true;
                }
            }
            // select/store: in scope only over BV arrays; recurse into operands.
            if matches!(op, Op::Builtin(BuiltinOp::Select | BuiltinOp::Store)) {
                if kids.first().is_some_and(|&k| is_bv_array(ctx, k)) {
                    return kids.iter().any(|&k| walk_fence(ctx, k, visited));
                }
                // select/store over a non-BV array → out of scope.
                return true;
            }
            // Any other Bool-sorted application is an out-of-scope theory atom.
            if ctx.sort_of(t) == bool_sort {
                return true;
            }
            // Non-Bool term (e.g. a BV/arith subexpression): descend so nested
            // Bool atoms are still discovered, but it is not itself an atom.
            kids.iter().any(|&k| walk_fence(ctx, k, visited))
        }
        TermNode::Const { .. } => false,
    }
}

fn is_bv_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::BitVec(_))
}

fn is_bv_predicate(op: &Op) -> bool {
    matches!(
        op,
        Op::Builtin(
            BuiltinOp::BvUlt
                | BuiltinOp::BvUle
                | BuiltinOp::BvUgt
                | BuiltinOp::BvUge
                | BuiltinOp::BvSlt
                | BuiltinOp::BvSle
                | BuiltinOp::BvSgt
                | BuiltinOp::BvSge
        )
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// RealBridge
// ─────────────────────────────────────────────────────────────────────────────

type Sat = shinri_sat::Solver<shinri_sat::NoTheory, shinri_core::NoProof, shinri_sat::Vmtf>;

/// The blast-mutable interior of `RealBridge`. Held behind a `RefCell` so the
/// `&self` `value_bv` can blast a not-yet-seen BV word on demand (the brief's
/// recipe) — minting fresh SAT vars + definitional clauses and reading them back.
/// `solve`/`ensure_atom`/`add_lemma` (all `&mut self`) `borrow_mut` it directly.
struct BlastState {
    sat: Sat,
    blaster: shinri_bv::Blaster,
    /// First SAT `Var` index of the blaster's BitVar namespace. BitVar `v` maps
    /// to SAT `Var::new(base + v)`. The blaster's var 0 (pinned-true) lives at
    /// `base + 0`, allocated once and reused across drained batches.
    base: u32,
    /// High-water mark: how many blaster BitVars already have a mirrored SAT var.
    /// Lets `replay_batch` allocate only the genuinely new vars.
    mirrored_vars: u32,
    /// BV term (read var, index, element, …) → its blasted SAT vars (LSB→MSB).
    var_bits: FxHashMap<TermId, Vec<Var>>,
}

/// The real `SatBridge` over a live `NoTheory` SAT solver plus a persistent
/// `shinri_bv::Blaster`. Built once by `RealBridge::new` (which blasts the
/// initial abstraction and Tseitin-encodes its Boolean skeleton); the refinement
/// controller then drives `solve`/`value_*`/`ensure_atom`/`add_lemma`.
struct RealBridge {
    st: std::cell::RefCell<BlastState>,
    /// Original BV (dis)equality atom TermId → its surrogate SAT literal.
    atom_lit: FxHashMap<TermId, Lit>,
    /// Array-eq Bool proxy TermId → its fresh SAT var.
    proxy_var: FxHashMap<TermId, Var>,
}

impl BlastState {
    /// Replay a freshly-drained batch of blaster clauses into the SAT solver,
    /// allocating mirror vars only for BitVars that don't have one yet. Var 0 and
    /// every previously-mirrored var are reused (no re-pinning).
    fn replay_batch(&mut self, ctx: &Context, batch: &[Vec<shinri_bv::BitLit>]) {
        let num = self.blaster.num_vars();
        for _ in self.mirrored_vars..num {
            self.sat.new_var();
        }
        self.mirrored_vars = num;
        for clause in batch {
            let mapped: Vec<Lit> = clause.iter().map(|&bl| self.map_bitlit(bl)).collect();
            self.sat.add_clause(&mapped);
        }
        self.refresh_var_bits(ctx);
    }

    /// Map a blaster `BitLit` to a SAT `Lit` via the contiguous `base` offset.
    fn map_bitlit(&self, bl: shinri_bv::BitLit) -> Lit {
        Lit::new(Var::new(self.base + bl.var), bl.pos)
    }

    /// Refresh `var_bits` from the blaster's current cache (BV variable terms →
    /// SAT vars). Idempotent; cheap relative to a solve.
    fn refresh_var_bits(&mut self, ctx: &Context) {
        for (term, bits) in self.blaster.exported_var_bits(ctx) {
            let vars: Vec<Var> = bits
                .iter()
                .map(|&bl| Var::new(self.base + bl.var))
                .collect();
            self.var_bits.insert(term, vars);
        }
    }

    /// Blast a Bool-sorted BV atom into the live solver (idempotent at the
    /// blaster's cache level), returning its surrogate SAT literal.
    fn ensure_atom_lit(&mut self, ctx: &mut Context, atom: TermId) -> Lit {
        let rewritten = shinri_bv::rewrite(ctx, atom);
        let bl = self.blaster.blast_atom(ctx, rewritten);
        let batch = self.blaster.take_new_clauses();
        self.replay_batch(ctx, &batch);
        self.map_bitlit(bl)
    }

    /// Blast a BV-sorted WORD term on demand and replay its new clauses. Used by
    /// `value_bv` so an index/witness word that only ever appeared inside an
    /// abstracted-away select still has SAT bits to read.
    ///
    /// Takes `&Context` (not `&mut`) because the `SatBridge::value_bv` seam is
    /// `&self`. We therefore blast the term AS WRITTEN (no `shinri_bv::rewrite`,
    /// which needs `&mut Context`). This is sound: `blast_word` handles every BV
    /// operator directly, so the un-rewritten blast is semantically identical;
    /// rewrite is only a normalization/CSE pass. The blasted words queried here
    /// are plain BV variables (indices / witnesses), so rewrite is a no-op anyway.
    fn ensure_word(&mut self, ctx: &Context, t: TermId) {
        if self.var_bits.contains_key(&t) {
            return;
        }
        let bits = self.blaster.blast_word(ctx, t);
        let vars: Vec<Var> = bits
            .iter()
            .map(|&bl| Var::new(self.base + bl.var))
            .collect();
        let batch = self.blaster.take_new_clauses();
        self.replay_batch(ctx, &batch);
        // Record this exact term's bits (covers compound index/word terms that
        // `exported_var_bits` — which only reports plain BV variables — omits).
        self.var_bits.insert(t, vars);
    }
}

impl RealBridge {
    fn new(ctx: &mut Context, abs: &shinri_abv::Abstraction) -> RealBridge {
        let mut blaster = shinri_bv::Blaster::new();

        // (1) Collect the Bool-sorted BV atoms of the abstracted assertions and
        //     blast each with the PERSISTENT blaster (not the one-shot `lower`),
        //     so the blaster — and its subterm cache / var namespace — survives
        //     across refinement rounds.
        let bv_atoms = crate::bv_stage::collect_bv_atoms(ctx, &abs.assertions);
        let mut atom_bitlit: FxHashMap<TermId, shinri_bv::BitLit> = FxHashMap::default();
        for &original in &bv_atoms {
            let rewritten = shinri_bv::rewrite(ctx, original);
            let bl = blaster.blast_atom(ctx, rewritten);
            atom_bitlit.insert(original, bl);
        }

        // (2) Build the SAT solver and allocate the contiguous mirror block for
        //     the blaster's current BitVar namespace. The blaster's var 0 (pinned
        //     true) is the first var of the block, so `base + 0` is forced true.
        let mut sat: Sat = Sat::new(shinri_sat::SolverConfig::default());
        let num = blaster.num_vars();
        debug_assert!(num >= 1, "blaster always has var0 (pinned true)");
        let first = sat.new_var();
        for _ in 1..num {
            sat.new_var();
        }
        let base = first.index() as u32;
        let map_bitlit =
            |bl: shinri_bv::BitLit| -> Lit { Lit::new(Var::new(base + bl.var), bl.pos) };

        // Replay every clause produced so far (includes the var0 unit clause).
        for clause in blaster.take_new_clauses() {
            let mapped: Vec<Lit> = clause.iter().map(|&bl| map_bitlit(bl)).collect();
            sat.add_clause(&mapped);
        }

        // (3) Map each BV atom's BitLit to its mirrored SAT Lit.
        let mut atom_lit: FxHashMap<TermId, Lit> = FxHashMap::default();
        for (&atom, &bl) in &atom_bitlit {
            atom_lit.insert(atom, map_bitlit(bl));
        }

        let mut st = BlastState {
            sat,
            blaster,
            base,
            mirrored_vars: num,
            var_bits: FxHashMap::default(),
        };
        st.refresh_var_bits(ctx);

        // (4) Tseitin-encode the abstracted Boolean skeleton over `NoTheory`,
        //     mapping BV atoms → surrogate lits and array-eq proxies → fresh vars,
        //     and assert each top-level formula.
        let mut proxy_var: FxHashMap<TermId, Var> = FxHashMap::default();
        for &a in &abs.assertions {
            let lit = encode_skeleton(&mut st, &atom_lit, &mut proxy_var, ctx, a);
            st.sat.add_clause(&[lit]);
        }

        RealBridge {
            st: std::cell::RefCell::new(st),
            atom_lit,
            proxy_var,
        }
    }
}

/// Tseitin-encode a Bool-sorted abstracted term over the `NoTheory` solver.
/// BV atoms resolve to their pre-blasted surrogate lit; array-eq proxies (and
/// any other Bool leaf) resolve to a fresh SAT var; connectives are encoded
/// with standard Tseitin gates.
fn encode_skeleton(
    st: &mut BlastState,
    atom_lit: &FxHashMap<TermId, Lit>,
    proxy_var: &mut FxHashMap<TermId, Var>,
    ctx: &Context,
    t: TermId,
) -> Lit {
    // A surrogated BV atom: return its pre-blasted literal directly.
    if let Some(&lit) = atom_lit.get(&t) {
        return lit;
    }
    let enc = |st: &mut BlastState, pv: &mut FxHashMap<TermId, Var>, k| {
        encode_skeleton(st, atom_lit, pv, ctx, k)
    };
    match ctx.term_node(t).clone() {
        TermNode::App {
            op: Op::Builtin(b),
            args,
            ..
        } => {
            let kids: Vec<TermId> = ctx.children(args).to_vec();
            let is_bool = |k: TermId| ctx.sort_of(k) == ctx.bool_sort();
            match b {
                BuiltinOp::Not => enc(st, proxy_var, kids[0]).negate(),
                BuiltinOp::And => {
                    let lits: Vec<Lit> = kids.iter().map(|&k| enc(st, proxy_var, k)).collect();
                    gate_and(&mut st.sat, &lits)
                }
                BuiltinOp::Or => {
                    let lits: Vec<Lit> = kids.iter().map(|&k| enc(st, proxy_var, k)).collect();
                    gate_or(&mut st.sat, &lits)
                }
                BuiltinOp::Implies => {
                    let mut acc = enc(st, proxy_var, kids[kids.len() - 1]);
                    for i in (0..kids.len() - 1).rev() {
                        let a = enc(st, proxy_var, kids[i]);
                        acc = gate_or(&mut st.sat, &[a.negate(), acc]);
                    }
                    acc
                }
                BuiltinOp::Xor => {
                    let mut acc = enc(st, proxy_var, kids[0]);
                    for &k in &kids[1..] {
                        let b = enc(st, proxy_var, k);
                        acc = gate_xor(&mut st.sat, acc, b);
                    }
                    acc
                }
                BuiltinOp::Ite => {
                    let c = enc(st, proxy_var, kids[0]);
                    let th = enc(st, proxy_var, kids[1]);
                    let el = enc(st, proxy_var, kids[2]);
                    gate_ite(&mut st.sat, c, th, el)
                }
                BuiltinOp::Eq if is_bool(kids[0]) => {
                    let a = enc(st, proxy_var, kids[0]);
                    let b = enc(st, proxy_var, kids[1]);
                    gate_xor(&mut st.sat, a, b).negate()
                }
                BuiltinOp::Distinct if is_bool(kids[0]) => {
                    let a = enc(st, proxy_var, kids[0]);
                    let b = enc(st, proxy_var, kids[1]);
                    gate_xor(&mut st.sat, a, b)
                }
                // Any other builtin Bool atom that was not surrogated. After a
                // sound abstraction + fence this should not occur, but encode it
                // as a fresh proxy leaf rather than panic.
                _ => bool_leaf(&mut st.sat, proxy_var, t),
            }
        }
        // Bool proxy const / uninterpreted Bool leaf.
        _ => bool_leaf(&mut st.sat, proxy_var, t),
    }
}

/// A Bool leaf (array-eq proxy or other uninterpreted Bool const): map to a
/// fresh SAT var, memoized in `proxy_var`.
fn bool_leaf(sat: &mut Sat, proxy_var: &mut FxHashMap<TermId, Var>, t: TermId) -> Lit {
    if let Some(&v) = proxy_var.get(&t) {
        return Lit::new(v, true);
    }
    let v = sat.new_var();
    proxy_var.insert(t, v);
    Lit::new(v, true)
}

fn gate_and(sat: &mut Sat, lits: &[Lit]) -> Lit {
    // o <-> AND(lits).
    let o = Lit::new(sat.new_var(), true);
    for &l in lits {
        sat.add_clause(&[o.negate(), l]); // o -> l
    }
    let mut big: Vec<Lit> = vec![o]; // AND(lits) -> o
    big.extend(lits.iter().map(|l| l.negate()));
    sat.add_clause(&big);
    o
}

fn gate_or(sat: &mut Sat, lits: &[Lit]) -> Lit {
    // o <-> OR(lits).
    let o = Lit::new(sat.new_var(), true);
    for &l in lits {
        sat.add_clause(&[o, l.negate()]); // l -> o
    }
    let mut big: Vec<Lit> = vec![o.negate()]; // o -> OR(lits)
    big.extend(lits.iter().copied());
    sat.add_clause(&big);
    o
}

fn gate_xor(sat: &mut Sat, a: Lit, b: Lit) -> Lit {
    let o = Lit::new(sat.new_var(), true);
    sat.add_clause(&[o.negate(), a, b]);
    sat.add_clause(&[o.negate(), a.negate(), b.negate()]);
    sat.add_clause(&[o, a.negate(), b]);
    sat.add_clause(&[o, a, b.negate()]);
    o
}

fn gate_ite(sat: &mut Sat, sel: Lit, a: Lit, b: Lit) -> Lit {
    let o = Lit::new(sat.new_var(), true);
    sat.add_clause(&[sel.negate(), o.negate(), a]);
    sat.add_clause(&[sel.negate(), o, a.negate()]);
    sat.add_clause(&[sel, o.negate(), b]);
    sat.add_clause(&[sel, o, b.negate()]);
    o
}

impl shinri_abv::SatBridge for RealBridge {
    fn solve(&mut self) -> bool {
        matches!(
            self.st.borrow_mut().sat.solve(),
            shinri_sat::SolveResult::Sat
        )
    }

    fn value_bv(&self, ctx: &Context, t: TermId) -> Option<(u32, shinri_num::Integer)> {
        // Only BV-sorted terms have bits. (A non-BV term — a Bool proxy, say —
        // has no width: return None.)
        let width = ctx.bv_width(ctx.sort_of(t))?;
        let mut st = self.st.borrow_mut();
        // Blast `t` on demand if it has never been blasted (e.g. an index or
        // extensionality witness that only ever appeared inside an abstracted-away
        // select). The current SAT model leaves the fresh bits unassigned, which
        // `value_of` reports as `false` (an arbitrary but consistent value); the
        // next solve assigns them and the relevant check re-runs. This is the
        // brief's "blast it now" recipe, realized via interior mutability because
        // the `SatBridge::value_bv` signature is `&self`.
        //
        // SAFETY/SOUNDNESS: `ensure_word` only ADDS definitional clauses (and, for
        // a plain variable, no clauses at all) over fresh vars — it never removes
        // or weakens a constraint, so it cannot turn a real UNSAT into SAT.
        st.ensure_word(ctx, t);
        let vars = st.var_bits.get(&t)?;
        debug_assert_eq!(vars.len() as u32, width, "var_bits width mismatch");
        let bits: Vec<bool> = vars
            .iter()
            .map(|&v| st.sat.value_of(v).unwrap_or(false))
            .collect();
        Some((width, shinri_bv::model::pack(width, &bits)))
    }

    fn value_bool(&self, t: TermId) -> Option<bool> {
        let st = self.st.borrow();
        let v = self.proxy_var.get(&t)?;
        // An unassigned proxy var defaults to false (the abstraction left it free).
        Some(st.sat.value_of(*v).unwrap_or(false))
    }

    fn ensure_atom(&mut self, ctx: &mut Context, atom: TermId) {
        if self.atom_lit.contains_key(&atom) {
            return;
        }
        let lit = self.st.borrow_mut().ensure_atom_lit(ctx, atom);
        self.atom_lit.insert(atom, lit);
    }

    fn add_lemma(&mut self, ctx: &mut Context, lemma: &shinri_abv::Lemma) {
        let mut lits: Vec<Lit> = Vec::with_capacity(lemma.0.len());
        for lit in &lemma.0 {
            // A lemma lit is either a BV (dis)equality atom (in `atom_lit`) or an
            // array-eq Bool proxy (in `proxy_var`). Ensure the BV atom is blasted.
            let base = if let Some(&l) = self.atom_lit.get(&lit.atom) {
                l
            } else if let Some(&v) = self.proxy_var.get(&lit.atom) {
                Lit::new(v, true)
            } else {
                // Not yet blasted — blast it now (idempotent ensure).
                self.ensure_atom(ctx, lit.atom);
                self.atom_lit[&lit.atom]
            };
            lits.push(if lit.pos { base } else { base.negate() });
        }
        self.st.borrow_mut().sat.add_clause(&lits);
    }
}

/// Build the abstraction, wire up the real bridge, and run the refinement loop.
pub fn solve_qfabv(ctx: &mut Context, assertions: &[TermId]) -> shinri_abv::AbvOutcome {
    use shinri_abv::{abstract_arrays, collect, refine};
    let mut c = collect(ctx, assertions);
    let mut abs = abstract_arrays(ctx, assertions, &c);
    let mut bridge = RealBridge::new(ctx, &abs);
    refine(ctx, &mut abs, &mut c, &mut bridge)
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};

    fn uconst(ctx: &mut Context, n: &str, s: shinri_core::SortId) -> shinri_core::TermId {
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn detects_select_over_bv_array() {
        let mut ctx = Context::new();
        let i = ctx.bv_sort(8);
        let e = ctx.bv_sort(8);
        let arr = ctx.array_sort(i, e);
        let a = uconst(&mut ctx, "a", arr);
        let idx = uconst(&mut ctx, "i", i);
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[a, idx])
            .unwrap();
        assert!(uses_arrays_over_bv(&ctx, &[sel]));
    }

    #[test]
    fn array_with_uninterpreted_index_is_fenced() {
        let mut ctx = Context::new();
        let i = ctx.declare_sort("I"); // uninterpreted index
        let e = ctx.bv_sort(8);
        let arr = ctx.array_sort(i, e);
        let a = uconst(&mut ctx, "a", arr);
        let idx = uconst(&mut ctx, "i", i);
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[a, idx])
            .unwrap();
        // Not a QF_ABV array (index not BV) → detection is false (Combiner/QF_AX).
        assert!(!uses_arrays_over_bv(&ctx, &[sel]));
    }

    #[test]
    fn end_to_end_row1_unsat_via_real_bridge() {
        // (= (select (store a i e) i) (bvadd e #x01))  is UNSAT (ROW-1 forces
        // select=e, but e != e+1 in BV8).
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let mk = |ctx: &mut Context, n: &str, s| {
            let f = ctx.declare_fun(n, &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let a = mk(&mut ctx, "a", arr);
        let i = mk(&mut ctx, "i", i8);
        let e = mk(&mut ctx, "e", i8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
        let ep1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvAdd), &[e, one])
            .unwrap();
        let atom = ctx.mk_eq(sel, ep1).unwrap();
        let outcome = solve_qfabv(&mut ctx, &[atom]);
        assert_eq!(outcome, shinri_abv::AbvOutcome::Unsat);
    }

    #[test]
    fn end_to_end_row1_sat() {
        // (= (select (store a i e) i) e) is SAT (ROW-1: the read equals e).
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", i8);
        let e = uconst(&mut ctx, "e", i8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        assert_eq!(solve_qfabv(&mut ctx, &[atom]), shinri_abv::AbvOutcome::Sat);
    }

    #[test]
    fn end_to_end_functional_consistency_unsat() {
        // i = j ∧ (select a i) = #x01 ∧ (select a j) = #x02  → UNSAT
        // (functional consistency: same array + equal indices ⇒ equal reads).
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", i8);
        let j = uconst(&mut ctx, "j", i8);
        let si = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let sj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
        let two = ctx.mk_bv_const(8, shinri_num::Integer::from(2u64));
        let eq_ij = ctx.mk_eq(i, j).unwrap();
        let eq_si = ctx.mk_eq(si, one).unwrap();
        let eq_sj = ctx.mk_eq(sj, two).unwrap();
        let conj = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[eq_ij, eq_si, eq_sj])
            .unwrap();
        assert_eq!(
            solve_qfabv(&mut ctx, &[conj]),
            shinri_abv::AbvOutcome::Unsat
        );
    }

    #[test]
    fn end_to_end_distinct_reads_is_sat() {
        // (select a i) = #x01 ∧ (select a j) = #x02 with i, j free → SAT
        // (i and j can differ, so the two reads are independent).
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", i8);
        let j = uconst(&mut ctx, "j", i8);
        let si = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let sj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
        let two = ctx.mk_bv_const(8, shinri_num::Integer::from(2u64));
        let eq_si = ctx.mk_eq(si, one).unwrap();
        let eq_sj = ctx.mk_eq(sj, two).unwrap();
        let conj = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[eq_si, eq_sj])
            .unwrap();
        assert_eq!(solve_qfabv(&mut ctx, &[conj]), shinri_abv::AbvOutcome::Sat);
    }

    #[test]
    fn fence_array_with_arith_atom() {
        // A BV-array select coexisting with a Real arith atom must be fenced.
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", i8);
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
        let bv_atom = ctx.mk_eq(sel, one).unwrap();
        let real = ctx.real_sort();
        let y = uconst(&mut ctx, "y", real);
        let zero = ctx.mk_numeral(shinri_core::Rational::zero(), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[y, zero]).unwrap();
        assert!(uses_arrays_over_bv(&ctx, &[bv_atom, gt]));
        assert!(fenced(&ctx, &[bv_atom, gt]));
    }

    #[test]
    fn fence_pure_bv_array_not_fenced() {
        // A pure QF_ABV query is NOT fenced.
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", i8);
        let e = uconst(&mut ctx, "e", i8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        let ult = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[i, e]).unwrap();
        assert!(uses_arrays_over_bv(&ctx, &[atom, ult]));
        assert!(!fenced(&ctx, &[atom, ult]));
    }
}
