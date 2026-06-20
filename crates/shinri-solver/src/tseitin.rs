//! Boolean-structure CNF encoding + theory-atom registration.

// The Encoder and its helpers are the public API consumed by Task 14's
// check_sat() implementation; they are intentionally unused until then.
#![allow(dead_code)]

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TermNode, Var};
use shinri_euf::Euf;
use shinri_theory::{Combiner, EmptyTheory};

type Sat = shinri_sat::Solver<Combiner<Euf, EmptyTheory>, shinri_core::NoProof, shinri_sat::Vmtf>;

pub struct Encoder<'a> {
    ctx: &'a Context,
    sat: &'a mut Sat,
    cache: FxHashMap<TermId, Lit>,
    pub atom_vars: Vec<(Var, TermId)>,
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
            t_true,
            t_false,
        }
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
                        // Bool equality = iff.
                        let a = self.encode(kids[0]);
                        let b = self.encode(kids[1]);
                        let nx = self.xor2(a, b);
                        nx.negate()
                    }
                    BuiltinOp::Distinct if self.is_bool(kids[0]) => {
                        // Bool distinct (binary) = xor.
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

    /// A theory atom leaf: one SAT var, registered with the Combiner.
    fn atom(&mut self, t: TermId) -> Lit {
        let v = self.sat.new_var();
        // Refusal (unsupported atom) surfaces as Unknown at the solver layer;
        // register_atom returns Err for those. We record the (var, term) either
        // way; check_sat consults registration success.
        let _ = self.sat.theory_mut().register_atom(v, t);
        self.atom_vars.push((v, t));
        Lit::new(v, true)
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
