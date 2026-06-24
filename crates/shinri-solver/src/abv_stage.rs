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
    /// Blaster BitVar index → its mirrored SAT `Var`, allocated lazily the first
    /// time the BitVar is seen and reused thereafter. Indexed by BitVar; an entry
    /// is `None` until that BitVar has been mirrored.
    ///
    /// A FIXED `base + var` offset CANNOT be used: `encode_skeleton` allocates SAT
    /// vars for Tseitin gate outputs and array-eq proxies that interleave with the
    /// blaster's namespace, so later batches' fresh SAT vars do NOT land at
    /// `base + var`. This explicit table records each BitVar's TRUE SAT `Var`.
    bitvar_to_sat: Vec<Option<Var>>,
    /// BV term (read var, index, element, …) → its blasted bits (LSB→MSB), each
    /// stored as `(sat_var, pos)` so the bit's POLARITY is preserved. A bit's
    /// concrete value is `sat.value_of(sat_var) == pos`. Polarity MUST be retained:
    /// the blaster uses `var 0` (pinned true) for both 0-bits (`pos=false`) and
    /// 1-bits (`pos=true`), and emits negated signal bits (`bvnot`/`bvneg`/
    /// `zero_extend` high bits, …) as `BitLit{var:N, pos:false}`. Dropping `pos`
    /// (storing only `Var`) would misread every such bit — a SOUNDNESS hole, since
    /// `value_bv` feeds index/read/element values into ROW/functional-consistency
    /// lemma checks that gate the sat/unsat verdict.
    var_bits: FxHashMap<TermId, Vec<(Var, bool)>>,
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
    /// Allocate (if needed) and return the SAT `Var` mirroring blaster BitVar `v`.
    /// First sight allocates a fresh SAT var via `new_var()` and records it; later
    /// sights reuse it. This is the single source of truth for the mapping.
    fn sat_var(&mut self, v: u32) -> Var {
        let idx = v as usize;
        if idx >= self.bitvar_to_sat.len() {
            self.bitvar_to_sat.resize(idx + 1, None);
        }
        if let Some(sv) = self.bitvar_to_sat[idx] {
            return sv;
        }
        let sv = self.sat.new_var();
        self.bitvar_to_sat[idx] = Some(sv);
        sv
    }

    /// Map a blaster `BitLit` to a SAT `Lit`, allocating the BitVar's SAT var on
    /// first sight (so this is `&mut self`).
    fn map_bitlit(&mut self, bl: shinri_bv::BitLit) -> Lit {
        Lit::new(self.sat_var(bl.var), bl.pos)
    }

    /// Replay a freshly-drained batch of blaster clauses into the SAT solver. Each
    /// BitVar referenced is mapped (and allocated on first sight) via the table.
    fn replay_batch(&mut self, ctx: &Context, batch: &[Vec<shinri_bv::BitLit>]) {
        for clause in batch {
            let mapped: Vec<Lit> = clause.iter().map(|&bl| self.map_bitlit(bl)).collect();
            self.sat.add_clause(&mapped);
        }
        self.refresh_var_bits(ctx);
    }

    /// Refresh `var_bits` from the blaster's current cache (BV variable terms →
    /// SAT vars). Idempotent; cheap relative to a solve.
    fn refresh_var_bits(&mut self, ctx: &Context) {
        for (term, bits) in self.blaster.exported_var_bits(ctx) {
            // Map each BitVar through the table for its SAT Var, but RETAIN `pos`.
            let vars: Vec<(Var, bool)> = bits
                .iter()
                .map(|&bl| (self.sat_var(bl.var), bl.pos))
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
        // Replay first so definitional clauses allocate their BitVars' SAT vars.
        let batch = self.blaster.take_new_clauses();
        self.replay_batch(ctx, &batch);
        // Then map this term's bits through the table, RETAINING `pos`. For a
        // plain variable the batch is empty (no clauses), so `sat_var` allocates
        // the fresh SAT vars here on first sight. Done after `replay_batch` so the
        // mapping is stable. Polarity is kept because compound words (`bvnot`,
        // `bvneg`, `zero_extend`, constant 0-bits, …) emit `pos=false` bits whose
        // value is `value_of(sat_var) == pos`, not `value_of(sat_var)`.
        let vars: Vec<(Var, bool)> = bits
            .iter()
            .map(|&bl| (self.sat_var(bl.var), bl.pos))
            .collect();
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

        // (2) Build the SAT solver and the BlastState; the BitVar→SAT-Var table
        //     allocates mirror vars lazily through `sat_var` as each BitVar is seen.
        let sat: Sat = Sat::new(shinri_sat::SolverConfig::default());
        let mut st = BlastState {
            sat,
            blaster,
            bitvar_to_sat: Vec::new(),
            var_bits: FxHashMap::default(),
        };

        // Replay every clause produced so far (includes the var0 pinned-true unit
        // clause), allocating each referenced BitVar's SAT var via the table.
        let batch = st.blaster.take_new_clauses();
        st.replay_batch(ctx, &batch);

        // (3) Map each BV atom's BitLit to its mirrored SAT Lit through the table.
        let mut atom_lit: FxHashMap<TermId, Lit> = FxHashMap::default();
        for (&atom, &bl) in &atom_bitlit {
            atom_lit.insert(atom, st.map_bitlit(bl));
        }

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
        // Reconstruct each bit POLARITY-AWARE: the bit is `value_of(sat_var) == pos`.
        // This is correct for every blasted shape, including:
        //   * constant 0-bits / `zero()`  → BitLit{var0, pos:false}: value_of(var0)
        //     is always the pinned `true`, and `true == false` = bit 0 (correct);
        //   * constant 1-bits / `one()`    → BitLit{var0, pos:true}: `true == true` = 1;
        //   * negated signal bits (`bvnot`/`bvneg`/`zero_extend` high bits, …)
        //     → BitLit{var:N, pos:false}: bit is `value_of(N) == false`.
        // Dropping `pos` (the prior bug) misread every such bit and could starve a
        // ROW / functional-consistency lemma of a needed value → wrong verdict.
        let bits: Vec<bool> = vars
            .iter()
            .map(|&(v, pos)| st.sat.value_of(v).unwrap_or(false) == pos)
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
        // Already surrogated as a BV atom — nothing to do.
        if self.atom_lit.contains_key(&atom) {
            return;
        }
        // A Bool proxy (array-eq abstraction) is already live as a SAT var in
        // `proxy_var`; it does NOT need to be blasted. Calling `blast_atom` on it
        // would panic because it is not a BV predicate.
        if self.proxy_var.contains_key(&atom) {
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
/// Returns only the outcome (discards array models). See `solve_qfabv_with_models`
/// for the version that also builds array models on SAT.
/// Used by unit tests; `lib.rs` uses `solve_qfabv_with_models` directly.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn solve_qfabv(ctx: &mut Context, assertions: &[TermId]) -> shinri_abv::AbvOutcome {
    solve_qfabv_with_models(ctx, assertions).0
}

/// Enumerate every declared array constant (nullary `Op::Uninterpreted` whose
/// sort is `(Array (_ BitVec _) (_ BitVec _))`) appearing in the assertions.
/// Only top-level named constants are returned — `store(...)` subexpressions
/// are not model entries.
fn collect_array_consts(ctx: &Context, assertions: &[TermId]) -> Vec<TermId> {
    use shinri_core::TermNode;
    let mut seen = rustc_hash::FxHashSet::default();
    let mut result = Vec::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids = ctx.children(*args).to_vec();
                // A nullary uninterpreted const whose sort is a BV-array is a
                // declared array constant.
                if matches!(op, Op::Uninterpreted(_)) && kids.is_empty() && is_bv_array(ctx, t) {
                    result.push(t);
                }
                for k in kids {
                    stack.push(k);
                }
            }
            TermNode::Const { .. } => {}
        }
    }
    result
}

/// Like `solve_qfabv`, but on SAT additionally builds the array model for every
/// declared array constant in the assertions, returning the rendered strings.
/// Returns (`outcome`, `array_models`) where `array_models` maps each declared
/// array constant `TermId` → its rendered SMT-LIB `store`-chain string.
/// On non-SAT outcomes the map is empty.
pub fn solve_qfabv_with_models(
    ctx: &mut Context,
    assertions: &[TermId],
) -> (shinri_abv::AbvOutcome, FxHashMap<TermId, String>) {
    use shinri_abv::{
        abstract_arrays, array_model, collect, normalize_array_atoms, refine, render,
    };
    // SOUNDNESS: desugar n-ary + `distinct` array atoms into pairwise binary eqs
    // BEFORE collection/abstraction, so every array atom the pipeline sees is a
    // binary `Eq` (possibly under `Not`/`And`). See `shinri_abv::normalize`.
    let assertions = normalize_array_atoms(ctx, assertions);
    let assertions = assertions.as_slice();
    let mut c = collect(ctx, assertions);
    let mut abs = abstract_arrays(ctx, assertions, &c);
    let mut bridge = RealBridge::new(ctx, &abs);
    let outcome = refine(ctx, &mut abs, &mut c, &mut bridge);

    if outcome != shinri_abv::AbvOutcome::Sat {
        return (outcome, FxHashMap::default());
    }

    // Build array models while `bridge`, `c`, and `abs` are still live.
    let arr_consts = collect_array_consts(ctx, assertions);
    let mut models = FxHashMap::default();
    for arr in arr_consts {
        let m = array_model(ctx, &c, &abs, arr, &bridge);
        models.insert(arr, render(&m));
    }
    (outcome, models)
}

/// Test helper: run a QF_ABV query and return the rendered array model string
/// for the single array term `arr`. Panics if the query is not SAT.
#[cfg(test)]
pub fn solve_qfabv_model_string(ctx: &mut Context, assertions: &[TermId], arr: TermId) -> String {
    use shinri_abv::{
        abstract_arrays, array_model, collect, normalize_array_atoms, refine, render,
    };
    let assertions = normalize_array_atoms(ctx, assertions);
    let assertions = assertions.as_slice();
    let mut c = collect(ctx, assertions);
    let mut abs = abstract_arrays(ctx, assertions, &c);
    let mut bridge = RealBridge::new(ctx, &abs);
    let outcome = refine(ctx, &mut abs, &mut c, &mut bridge);
    assert_eq!(
        outcome,
        shinri_abv::AbvOutcome::Sat,
        "solve_qfabv_model_string: expected SAT"
    );
    let m = array_model(ctx, &c, &abs, arr, &bridge);
    render(&m)
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

    /// REGRESSION (BitVar→SAT-Var mapping soundness). This is the value-sensitive
    /// instance that the OLD fixed `base + var` mapping gets WRONG.
    ///
    /// The abstraction here contains real Boolean structure (a top-level `And`
    /// with several conjuncts plus a nested `Or`), so `encode_skeleton` allocates
    /// a batch of Tseitin GATE vars at SAT indices that interleave the blaster's
    /// namespace BEFORE any index word is blasted on demand. The correct verdict
    /// (UNSAT) hinges on functional consistency reading the model values of the
    /// indices `i` and `j` — which are only blasted ON DEMAND (they vanish into
    /// the abstracted-away selects). Under the old mapping those index bits aliased
    /// onto gate/proxy vars (e.g. an And-gate output forced true), so the indices
    /// read garbage, functional consistency could not fire, and the solver returned
    /// a WRONG Sat. With the explicit table the indices read their true SAT vars.
    ///
    /// Formula: i = #x07 ∧ j = #x07 ∧ (select a i) = #x01 ∧ (select a j) = #x02
    ///          ∧ (true ∨ <filler>).
    /// i = j = 7 forces (select a i) = (select a j) by functional consistency,
    /// but they are pinned to 1 and 2 → UNSAT.
    #[test]
    fn regression_bitvar_mapping_value_sensitive_unsat() {
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", i8);
        let j = uconst(&mut ctx, "j", i8);
        let si = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let sj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let seven = ctx.mk_bv_const(8, shinri_num::Integer::from(7u64));
        let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
        let two = ctx.mk_bv_const(8, shinri_num::Integer::from(2u64));
        // Pin both indices to the SAME value so functional consistency must fire,
        // but only if the on-demand-blasted index bits are read correctly.
        let eq_i7 = ctx.mk_eq(i, seven).unwrap();
        let eq_j7 = ctx.mk_eq(j, seven).unwrap();
        let eq_si = ctx.mk_eq(si, one).unwrap();
        let eq_sj = ctx.mk_eq(sj, two).unwrap();
        // Extra Boolean structure to force a batch of gate vars before on-demand
        // index blasting: a nested Or whose first disjunct is trivially satisfiable.
        let bvult = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvUlt), &[i, seven])
            .unwrap();
        let bvuge = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvUge), &[i, seven])
            .unwrap();
        let disj = ctx
            .mk_app(Op::Builtin(BuiltinOp::Or), &[bvult, bvuge])
            .unwrap(); // tautology, but mints gate vars
        let conj = ctx
            .mk_app(
                Op::Builtin(BuiltinOp::And),
                &[eq_i7, eq_j7, eq_si, eq_sj, disj],
            )
            .unwrap();
        assert_eq!(
            solve_qfabv(&mut ctx, &[conj]),
            shinri_abv::AbvOutcome::Unsat,
            "functional consistency over correctly-read indices i=j=7 must force \
             (select a i)=(select a j), contradicting 1 vs 2"
        );
    }

    /// REGRESSION (value_bv polarity, COMPOUND index). The select indices here are
    /// `(bvnot x)` and `y`, with `y = (bvnot x)` asserted — so the two effective
    /// indices are equal, and functional consistency must force the two reads
    /// equal, contradicting #x01 vs #x02 → UNSAT.
    ///
    /// `value_bv((bvnot x))` exercises the polarity path: `bvnot` blasts to
    /// `BitLit{var:N, pos:false}` bits (negated signals). Under the OLD bug
    /// `var_bits` dropped `pos`, so each negated bit was read as `value_of(N)`
    /// instead of `value_of(N) == false` — i.e. the bvnot index read GARBAGE. The
    /// functional-consistency check (`value_bv(ix) == value_bv(iy)`) then compared
    /// a corrupted index against the correctly-read `y`, failed to detect they are
    /// equal, never fired the ROW lemma, and returned a WRONG Sat. With the
    /// polarity-aware read the bvnot index reads correctly, the indices match, the
    /// lemma fires, and the verdict is the correct UNSAT.
    #[test]
    fn regression_value_bv_polarity_compound_index_unsat() {
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let a = uconst(&mut ctx, "a", arr);
        let x = uconst(&mut ctx, "x", i8);
        let y = uconst(&mut ctx, "y", i8);
        // notx = (bvnot x): a compound index whose bits carry pos=false.
        let notx = ctx.mk_app(Op::Builtin(BuiltinOp::BvNot), &[x]).unwrap();
        // (select a (bvnot x)) = #x01
        let sel_notx = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[a, notx])
            .unwrap();
        // (select a y) = #x02
        let sel_y = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, y]).unwrap();
        let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
        let two = ctx.mk_bv_const(8, shinri_num::Integer::from(2u64));
        let eq_notx = ctx.mk_eq(sel_notx, one).unwrap();
        let eq_y = ctx.mk_eq(sel_y, two).unwrap();
        // y = (bvnot x): forces the two effective indices equal.
        let eq_idx = ctx.mk_eq(y, notx).unwrap();
        let conj = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[eq_notx, eq_y, eq_idx])
            .unwrap();
        assert_eq!(
            solve_qfabv(&mut ctx, &[conj]),
            shinri_abv::AbvOutcome::Unsat,
            "functional consistency over the correctly-read compound index \
             (bvnot x) = y must force (select a (bvnot x)) = (select a y), \
             contradicting 1 vs 2"
        );
    }

    /// SOUNDNESS REGRESSION C1 — array `(distinct a b)` must NOT be read as `(= a b)`.
    /// a,b are 1-bit-indexed (only cells #b0,#b1). They agree at both cells, so
    /// extensionality forces a=b — contradicting `(distinct a b)` → UNSAT.
    /// Pre-fix the proxy was forced TRUE (eq semantics), emitting agreement lemmas
    /// and never a witness disequality, so distinctness was lost → WRONG Sat.
    #[test]
    fn regression_c1_array_distinct_is_not_equality_unsat() {
        let mut ctx = Context::new();
        let i1 = ctx.bv_sort(1);
        let e8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i1, e8);
        let a = uconst(&mut ctx, "a", arr);
        let b = uconst(&mut ctx, "b", arr);
        let zero = ctx.mk_bv_const(1, shinri_num::Integer::from(0u64));
        let one = ctx.mk_bv_const(1, shinri_num::Integer::from(1u64));
        let sa0 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[a, zero])
            .unwrap();
        let sb0 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[b, zero])
            .unwrap();
        let sa1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[a, one])
            .unwrap();
        let sb1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[b, one])
            .unwrap();
        let dist = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b])
            .unwrap();
        let eq0 = ctx.mk_eq(sa0, sb0).unwrap();
        let eq1 = ctx.mk_eq(sa1, sb1).unwrap();
        let conj = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[dist, eq0, eq1])
            .unwrap();
        assert_eq!(
            solve_qfabv(&mut ctx, &[conj]),
            shinri_abv::AbvOutcome::Unsat,
            "(distinct a b) with agreement at both (only) 1-bit cells must be UNSAT"
        );
    }

    /// SOUNDNESS REGRESSION C2 — n-ary array `(distinct a b c)` must not collapse to
    /// a single binary proxy. `(= a b)` contradicts `(distinct a b c)` → UNSAT.
    /// Pre-fix only the (a,b) pair survived and was read with eq semantics, so
    /// distinctness was never enforced → WRONG Sat.
    #[test]
    fn regression_c2_nary_array_distinct_unsat() {
        let mut ctx = Context::new();
        let i1 = ctx.bv_sort(1);
        let e8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i1, e8);
        let a = uconst(&mut ctx, "a", arr);
        let b = uconst(&mut ctx, "b", arr);
        let c = uconst(&mut ctx, "c", arr);
        let dist = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, c])
            .unwrap();
        let eq_ab = ctx.mk_eq(a, b).unwrap();
        let conj = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[dist, eq_ab])
            .unwrap();
        assert_eq!(
            solve_qfabv(&mut ctx, &[conj]),
            shinri_abv::AbvOutcome::Unsat,
            "(= a b) contradicts (distinct a b c) → UNSAT"
        );
    }

    /// Complement: n-ary `(= a b c)` with c forced to differ from a must be UNSAT
    /// (exercises the n-ary `=` desugar chain, not just distinct).
    #[test]
    fn regression_c2_nary_array_eq_chain_unsat() {
        let mut ctx = Context::new();
        let i1 = ctx.bv_sort(1);
        let e8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i1, e8);
        let a = uconst(&mut ctx, "a", arr);
        let b = uconst(&mut ctx, "b", arr);
        let c = uconst(&mut ctx, "c", arr);
        let zero = ctx.mk_bv_const(1, shinri_num::Integer::from(0u64));
        // (= a b c) forces a=c at cell 0, but reads are pinned to differ.
        let sa0 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[a, zero])
            .unwrap();
        let sc0 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[c, zero])
            .unwrap();
        let one8 = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
        let two8 = ctx.mk_bv_const(8, shinri_num::Integer::from(2u64));
        let eq_all = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[a, b, c]).unwrap();
        let pin_a = ctx.mk_eq(sa0, one8).unwrap();
        let pin_c = ctx.mk_eq(sc0, two8).unwrap();
        let conj = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[eq_all, pin_a, pin_c])
            .unwrap();
        assert_eq!(
            solve_qfabv(&mut ctx, &[conj]),
            shinri_abv::AbvOutcome::Unsat,
            "(= a b c) forces a=c, contradicting (select a 0)=1 vs (select c 0)=2"
        );
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
    fn get_model_renders_array_after_sat() {
        // (= (select a #x01) #xff) is SAT; model must map a at index 1 to 0xff.
        let mut ctx = Context::new();
        let i8 = ctx.bv_sort(8);
        let arr = ctx.array_sort(i8, i8);
        let af = ctx.declare_fun("a", &[], arr);
        let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[a, one])
            .unwrap();
        let ff = ctx.mk_bv_const(8, shinri_num::Integer::from(255u64));
        let atom = ctx.mk_eq(sel, ff).unwrap();

        // (driver test helper that returns the model string for the array term)
        let s = super::solve_qfabv_model_string(&mut ctx, &[atom], a);
        assert!(s.contains("#x01") && s.contains("#xff") && s.starts_with("(store ((as const"));
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
