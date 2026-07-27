//! Boolean-structure CNF encoding + theory-atom registration.

// The Encoder and its helpers are the public API consumed by Task 14's
// check_sat() implementation; they are intentionally unused until then.
#![allow(dead_code)]

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TermNode, Var};
use shinri_euf::Euf;
use shinri_theory::Combiner;

type Sat = shinri_sat::Solver<
    Combiner<
        Euf,
        shinri_arith::Arith,
        shinri_arrays::Arrays,
        shinri_str::StrSolver,
        shinri_dt::DtSolver,
    >,
    shinri_core::NoProof,
    shinri_sat::Vmtf,
>;

pub struct Encoder<'a> {
    ctx: &'a Context,
    sat: &'a mut Sat,
    cache: FxHashMap<TermId, Lit>,
    pub atom_vars: Vec<(Var, TermId)>,
    pub refused: bool,
    pub saw_euf: bool,
    pub saw_arith: bool,
    pub saw_shared: bool,
    /// True if at least one EUF atom's top-level terms are of a *non-arithmetic*
    /// (uninterpreted) sort, e.g. `(= p q)` where p,q are of sort U.
    /// Used to gate the "pure EUF + arith" mixed fence: we want to fence
    /// `(= p:U q:U) ∧ (> x:Real 0)` (no N-O propagation), but NOT
    /// `(= x:Real y:Real) ∧ (Le x y)` (valid QF_UFLRA with companion Le/Ge).
    pub saw_euf_nonreal: bool,
    /// True if any arith atom's operands are Int-sorted.
    pub saw_int_arith: bool,
    /// True if any arith atom's operands are Real-sorted.
    pub saw_real_arith: bool,
    /// Optional BV surrogate map: original BV atom TermId → its pre-blasted SAT
    /// literal. When set and `t` is a key, the Encoder returns the surrogate
    /// literal DIRECTLY instead of registering a theory atom — BV atoms must
    /// NEVER reach `register_atom`/`classify` (they would be mis-routed to EUF
    /// as uninterpreted functions, an unsoundness). See bv_stage module doc.
    bv_atom_lit: Option<FxHashMap<TermId, Lit>>,
    t_true: TermId,
    t_false: TermId,
}

impl<'a> Encoder<'a> {
    pub fn new(ctx: &'a Context, sat: &'a mut Sat, t_true: TermId, t_false: TermId) -> Self {
        Encoder {
            ctx,
            sat,
            cache: FxHashMap::default(),
            atom_vars: Vec::new(),
            refused: false,
            saw_euf: false,
            saw_arith: false,
            saw_shared: false,
            saw_euf_nonreal: false,
            saw_int_arith: false,
            saw_real_arith: false,
            bv_atom_lit: None,
            t_true,
            t_false,
        }
    }

    /// Install the BV surrogate map. After this, any term in the map encodes to
    /// its pre-blasted literal instead of becoming a theory atom.
    pub fn set_bv_surrogates(&mut self, map: FxHashMap<TermId, Lit>) {
        self.bv_atom_lit = Some(map);
    }

    /// Force the encoded top-level formula literal to be true.
    pub fn assert_top(&mut self, lit: Lit) {
        self.sat.add_clause(&[lit]);
    }

    /// Add a raw clause (disjunction of literals) directly to the SAT engine.
    /// Used by the slice-9 symbolic Real-bridge arm to gate guarded-linear rows
    /// and significand-channel ties by blasted FP bit literals.
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        self.sat.add_clause(lits)
    }

    /// Encode `t` (a Bool-sorted term); return a literal true iff `t` holds.
    pub fn encode(&mut self, t: TermId) -> Lit {
        if let Some(&l) = self.cache.get(&t) {
            return l;
        }
        let lit = self.encode_uncached(t);
        self.cache.insert(t, lit);
        lit
    }

    fn fresh(&mut self) -> Lit {
        Lit::new(self.sat.new_var(), true)
    }

    fn encode_uncached(&mut self, t: TermId) -> Lit {
        // BV surrogate interception (SOUNDNESS-CRITICAL): if `t` is a collected
        // BV atom, return its pre-blasted SAT literal WITHOUT registering a
        // theory atom. Must come first so BV (dis)equalities never reach
        // `atom()`/`register_atom`/`classify` (where they would mis-route to
        // EUF). The Boolean skeleton (and/or/not over BV atoms) still encodes
        // normally because those connective nodes are not in the map.
        if let Some(map) = &self.bv_atom_lit {
            if let Some(&lit) = map.get(&t) {
                return lit;
            }
        }
        match self.ctx.term_node(t) {
            TermNode::App {
                op: Op::Builtin(b),
                args,
                ..
            } => {
                let kids: Vec<TermId> = self.ctx.children(*args).to_vec();
                match b {
                    BuiltinOp::Not => {
                        let a = self.encode(kids[0]);
                        a.negate()
                    }
                    BuiltinOp::And => self.encode_and(&kids),
                    BuiltinOp::Or => self.encode_or(&kids),
                    BuiltinOp::Implies => {
                        // a -> b  ≡  ¬a ∨ b ; chain right-assoc for n args.
                        let mut acc = self.encode(kids[kids.len() - 1]);
                        for i in (0..kids.len() - 1).rev() {
                            let a = self.encode(kids[i]);
                            acc = self.or2(a.negate(), acc);
                        }
                        acc
                    }
                    BuiltinOp::Xor => {
                        let mut acc = self.encode(kids[0]);
                        for k in &kids[1..] {
                            let b = self.encode(*k);
                            acc = self.xor2(acc, b);
                        }
                        acc
                    }
                    BuiltinOp::Ite => {
                        let c = self.encode(kids[0]);
                        let th = self.encode(kids[1]);
                        let el = self.encode(kids[2]);
                        self.ite(c, th, el)
                    }
                    BuiltinOp::Eq if self.is_bool(kids[0]) => {
                        // Bool equality = iff. word_norm expands n-ary = for
                        // ALL sorts (slice 6) before encoding, so only the
                        // binary form can reach this arm — asserting that here
                        // keeps the old silent kids[2..] drop from returning.
                        debug_assert_eq!(
                            kids.len(),
                            2,
                            "n-ary Bool = must be expanded by word_norm"
                        );
                        let a = self.encode(kids[0]);
                        let b = self.encode(kids[1]);
                        let nx = self.xor2(a, b);
                        nx.negate()
                    }
                    BuiltinOp::Distinct if self.is_bool(kids[0]) => {
                        // Bool distinct (binary) = xor. word_norm expands n-ary
                        // distinct for ALL sorts (slice 6) before encoding, so
                        // only the binary form can reach this arm — asserting
                        // that here keeps the old silent kids[2..] drop from
                        // returning.
                        debug_assert_eq!(
                            kids.len(),
                            2,
                            "n-ary Bool distinct must be expanded by word_norm"
                        );
                        let a = self.encode(kids[0]);
                        let b = self.encode(kids[1]);
                        self.xor2(a, b)
                    }
                    BuiltinOp::Distinct => self.encode_distinct(t, &kids),
                    BuiltinOp::Eq => self.atom(t), // theory equality atom
                    _ => self.atom(t),             // arithmetic etc. -> atom (refused later)
                }
            }
            // Uninterpreted predicate application, or a Bool constant.
            TermNode::App {
                op: Op::Uninterpreted(_),
                ..
            } => self.atom(t),
            TermNode::Const { .. } => {
                if t == self.t_true {
                    // Represent constant true with a fixed satisfied literal.
                    let l = self.fresh();
                    self.sat.add_clause(&[l]);
                    l
                } else if t == self.t_false {
                    let l = self.fresh();
                    self.sat.add_clause(&[l.negate()]);
                    l
                } else {
                    self.atom(t)
                }
            }
        }
    }

    fn is_bool(&self, t: TermId) -> bool {
        self.ctx.sort_of(t) == self.ctx.bool_sort()
    }

    /// True if the atom's top-level argument terms are of a non-arithmetic sort
    /// (i.e., not Real or Int). Used to identify "purely uninterpreted" EUF atoms
    /// like `(= p:U q:U)` which cannot be combined with arith without N-O propagation,
    /// vs `(= x:Real y:Real)` which has companion Le/Ge atoms in the arith theory.
    fn euf_atom_has_nonreal_args(&self, t: TermId) -> bool {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let real = self.ctx.real_sort();
        let int = self.ctx.int_sort();
        let bool_s = self.ctx.bool_sort();
        let is_arith_or_bool = |s| s == real || s == int || s == bool_s;
        match self.ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let children = self.ctx.children(*args);
                match op {
                    Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) => {
                        // Check argument sorts: if any arg is of a non-arith sort, it's
                        // a "pure EUF" atom (uninterpreted sort like U).
                        children
                            .iter()
                            .any(|&c| !is_arith_or_bool(self.ctx.sort_of(c)))
                    }
                    Op::Uninterpreted(_) => {
                        // Predicate application: check if the sort of the atom (Bool)
                        // indicates an uninterpreted predicate over non-arith sorts.
                        // For now, treat any uninterpreted predicate as non-real EUF.
                        true
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// A theory atom leaf: one SAT var, registered with the Combiner.
    fn atom(&mut self, t: TermId) -> Lit {
        let v = self.sat.new_var();
        // Refusal (unsupported atom) surfaces as Unknown at the solver layer;
        // register_atom returns Err for those. Set refused=true so check_sat
        // can return Unknown without calling solve().
        if self.sat.theory_mut().register_atom(v, t).is_err() {
            self.refused = true;
        } else {
            match shinri_theory::atom::classify(self.ctx, t) {
                Ok(shinri_theory::types::Owner::Euf) => {
                    self.saw_euf = true;
                    // Track whether this EUF atom's top-level terms are of a
                    // non-arithmetic sort (e.g. sort U vs Real). Used to gate the
                    // mixed-theory fence: `(= p:U q:U) ∧ (> x:Real 0)` is fenced
                    // to Unknown (no N-O propagation), but `(= x:Real y:Real)` with
                    // companion Le/Ge atoms is valid QF_UFLRA and must NOT be fenced.
                    if self.euf_atom_has_nonreal_args(t) {
                        self.saw_euf_nonreal = true;
                    }
                }
                Ok(shinri_theory::types::Owner::Arith) => {
                    self.saw_arith = true;
                    if self.arith_atom_is_int(t) {
                        self.saw_int_arith = true;
                    } else {
                        self.saw_real_arith = true;
                    }
                }
                Ok(shinri_theory::types::Owner::Shared) => self.saw_shared = true,
                Ok(shinri_theory::types::Owner::Arrays) => {
                    // Arrays atoms are EUF-adjacent (select/store/array-eq);
                    // treat them like EUF for the mixed-theory fence.
                    self.saw_euf = true;
                    self.saw_euf_nonreal = true;
                }
                Ok(shinri_theory::types::Owner::String) => {
                    // String equality atoms are EUF-adjacent in v1 (parked with
                    // EUF until the string theory slot is wired in Task 7).
                    self.saw_euf = true;
                    self.saw_euf_nonreal = true;
                }
                Ok(shinri_theory::types::Owner::Datatypes) => {
                    // Datatype atoms are EUF-adjacent (constructor/selector/
                    // tester applications congruence-close in EUF); treat them
                    // like EUF for the mixed-theory fence.
                    self.saw_euf = true;
                    self.saw_euf_nonreal = true;
                }
                Err(_) => {}
            }
        }
        self.atom_vars.push((v, t));
        Lit::new(v, true)
    }

    /// True iff this arith relation atom's operands are Int-sorted. `mk_app`
    /// forbids mixed Int/Real arithmetic, so checking the first child suffices.
    fn arith_atom_is_int(&self, t: TermId) -> bool {
        use shinri_core::TermNode;
        if let TermNode::App { args, .. } = self.ctx.term_node(t) {
            let kids = self.ctx.children(*args);
            if let Some(&c0) = kids.first() {
                return self.ctx.sort_of(c0) == self.ctx.int_sort();
            }
        }
        false
    }

    /// Distinct over a non-Bool sort.
    ///
    /// BINARY case (len == 2): register the whole `distinct` term as a single
    /// theory atom. This is sound because `Euf::assert` already decodes
    /// `BuiltinOp::Distinct`: a positive distinct literal asserts a disequality;
    /// a negative one merges the two nodes as equal.
    ///
    /// N-ARY case (len > 2): this is unreachable here — n-ary distinct is
    /// lowered to pairwise binary disequalities (each as its own atom) by the
    /// pre-processing pass in Task 14, before the encoder is called.
    fn encode_distinct(&mut self, t: TermId, kids: &[TermId]) -> Lit {
        if kids.len() == 2 {
            // Binary non-Bool distinct: register as a theory atom directly.
            // Euf::assert handles both the positive (assert_diseq) and negative
            // (merge_eq) phases correctly for this atom kind.
            self.atom(t)
        } else {
            // N-ary distinct (len > 2) must be lowered before encoding reaches
            // this point (Task 14). If we arrive here it is a bug in the caller.
            panic!(
                "n-ary distinct (len={}) must be lowered to pairwise binary \
                 atoms before encoding; call lower_distinct() first",
                kids.len()
            );
        }
    }

    fn encode_and(&mut self, kids: &[TermId]) -> Lit {
        let out = self.fresh();
        let mut child_lits = Vec::with_capacity(kids.len());
        for &k in kids {
            child_lits.push(self.encode(k));
        }
        // out -> each child ;  (¬out ∨ ci)
        for &ci in &child_lits {
            self.sat.add_clause(&[out.negate(), ci]);
        }
        // (∧ ci) -> out ;  (out ∨ ¬c1 ∨ ... ∨ ¬cn)
        let mut big = vec![out];
        big.extend(child_lits.iter().map(|l| l.negate()));
        self.sat.add_clause(&big);
        out
    }

    fn encode_or(&mut self, kids: &[TermId]) -> Lit {
        let out = self.fresh();
        let mut child_lits = Vec::with_capacity(kids.len());
        for &k in kids {
            child_lits.push(self.encode(k));
        }
        for &ci in &child_lits {
            self.sat.add_clause(&[out, ci.negate()]);
        }
        let mut big = vec![out.negate()];
        big.extend(child_lits.iter().copied());
        self.sat.add_clause(&big);
        out
    }

    fn or2(&mut self, a: Lit, b: Lit) -> Lit {
        let out = self.fresh();
        self.sat.add_clause(&[out, a.negate()]);
        self.sat.add_clause(&[out, b.negate()]);
        self.sat.add_clause(&[out.negate(), a, b]);
        out
    }

    fn xor2(&mut self, a: Lit, b: Lit) -> Lit {
        let out = self.fresh();
        // out <-> (a xor b)
        self.sat.add_clause(&[out.negate(), a, b]);
        self.sat.add_clause(&[out.negate(), a.negate(), b.negate()]);
        self.sat.add_clause(&[out, a.negate(), b]);
        self.sat.add_clause(&[out, a, b.negate()]);
        out
    }

    fn ite(&mut self, c: Lit, th: Lit, el: Lit) -> Lit {
        let out = self.fresh();
        // c -> (out <-> th)
        self.sat.add_clause(&[c.negate(), out.negate(), th]);
        self.sat.add_clause(&[c.negate(), out, th.negate()]);
        // ¬c -> (out <-> el)
        self.sat.add_clause(&[c, out.negate(), el]);
        self.sat.add_clause(&[c, out, el.negate()]);
        out
    }
}

/// Node-visit budget for `display_term`'s recursion (slice 43 T6 review
/// finding 1). The term DAG is hash-consed and the parser supports `let`
/// (`shinri-parser/src/parser.rs:772`), which binds a name to a TermId
/// without duplicating it — so a LINEAR-size, SMALL-depth script can build a
/// term that shares the same subterm at every level, e.g. a chain of
/// `x_i := (g x_{i-1} x_{i-1})`. This printer has no memoization, so it
/// re-walks a shared child once per occurrence in its parent: rendering that
/// chain costs `2^N` node-visits (and characters) for `N` levels, not `N`.
/// Measured against this rendering (pre-budget) with a 22-level chain
/// (612-byte script): a 29 MB response in ~4.3s; the review's own
/// measurement on an equivalent script found 25 MB/4.1s at N=22 and 100
/// MB/16.5s at N=24 — i.e. it roughly doubles per additional level. The
/// `depth` cap below does NOT bound this: the blowup is already severe at
/// depth 22-24, three orders of magnitude short of the depth-10_000 cap.
/// `DISPLAY_TERM_BUDGET` counts down by one per node visited (checked BEFORE
/// recursing into children, so the budget bounds work done, not just output
/// size) and every remaining subterm renders as `t{index}` once it hits
/// zero. 100_000 is comfortably more nodes than any human-written
/// `get-value` target has (those are a handful of nested applications, not
/// tens of thousands) while still cutting an exponential chain off at
/// roughly its 17th sharing level — far short of the levels in the table
/// above — so the worst case is sub-millisecond instead of double-digit
/// seconds.
///
/// The budget is built ONCE PER `get-value` RESPONSE (in the `Command::GetValue`
/// arm) and threaded through every label in it. `(get-value (t1 … tK))` with a
/// per-term budget would bound each label but not the response. Measured on a
/// 24_635-byte script whose K=40 labels all name the same 25-level `let`-shared
/// term: 14.0 MB in 0.55s with a per-term budget, 350 KB in 0.017s with this
/// shared one — the multiplier is exactly K, and K is only bounded by script
/// length. Sharing the countdown makes the bound this comment describes a
/// property of the whole response.
pub(crate) const DISPLAY_TERM_BUDGET: usize = 100_000;

/// An SMT-LIB rendering of a term, for `get-value` response labels: `x`,
/// `(head l)`. The `t{index}` fallback remains for a term with no printable
/// form; it should be unreachable for anything the user could have written
/// (slice 43 §4.C). Only `Op::Uninterpreted` gets a structural rendering —
/// arithmetic and other builtin ops fall back to `t{index}`, which is out of
/// scope for this slice.
///
/// `budget` is supplied BY THE CALLER and shared across the whole `get-value`
/// response, not minted per term: `(get-value (a b c))` renders K labels, and
/// `let` lets all K name the same deep shared term, so a per-term budget would
/// multiply the bound by K and the size guarantee the constant documents would
/// hold only of one label rather than of the response the user receives.
pub(crate) fn display_term(
    ctx: &shinri_core::Context,
    t: shinri_core::TermId,
    budget: &mut usize,
) -> String {
    display_term_at_depth(ctx, t, 0, budget)
}

/// `depth` mirrors `render_value`'s `depth > 10_000` cap
/// (`crates/shinri-dt/src/lib.rs:645`) for the same reason render_value has
/// it: term depth is attacker-controlled per the threat model, so the
/// recursion needs an explicit, mechanical backstop rather than relying on
/// the input being shallow. It is kept as a fence, not the operative bound
/// here — a term deep enough to trip a 10_000 cap stack-overflows during
/// parse/assert long before `display_term` is ever called. The operative
/// bound against attacker-controlled *output size* is `budget` (see
/// `DISPLAY_TERM_BUDGET` above), which is what actually stops the
/// exponential-sharing blowup this function is otherwise exposed to.
fn display_term_at_depth(
    ctx: &shinri_core::Context,
    t: shinri_core::TermId,
    depth: u32,
    budget: &mut usize,
) -> String {
    if depth > 10_000 || *budget == 0 {
        return format!("t{}", t.index());
    }
    *budget -= 1;
    match ctx.term_node(t) {
        TermNode::App {
            op: Op::Uninterpreted(sym),
            args,
            ..
        } => {
            let sym = *sym;
            let kids = ctx.children(*args).to_vec();
            if kids.is_empty() {
                return ctx.symbol_name(sym).to_string();
            }
            let parts: Vec<String> = kids
                .iter()
                .map(|&k| display_term_at_depth(ctx, k, depth + 1, budget))
                .collect();
            format!("({} {})", ctx.symbol_name(sym), parts.join(" "))
        }
        _ => format!("t{}", t.index()),
    }
}

#[cfg(test)]
mod tests {
    use shinri_core::Op;

    #[test]
    fn encodes_equality_atom_as_registered_var() {
        let mut s = crate::Solver::new();
        let u = s.declare_sort("U");
        let af = s.declare_fun("a", &[], u);
        let a = s.app(Op::Uninterpreted(af), &[]);
        let bf = s.declare_fun("b", &[], u);
        let b = s.app(Op::Uninterpreted(bf), &[]);
        let e = s.eq(a, b);

        let (lit, atom_vars) = s.encode_for_test(e);
        // The equality atom became exactly one registered theory atom.
        assert_eq!(atom_vars.len(), 1);
        assert_eq!(atom_vars[0].1, e);
        // The returned literal is the positive phase of that atom's var.
        assert_eq!(lit.var(), atom_vars[0].0);
        assert!(lit.is_positive());
    }
}
