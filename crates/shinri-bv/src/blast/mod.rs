use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermId, TermNode};

pub mod structural;
pub mod bitwise;
pub mod arith;
pub mod div;
pub mod shift;
pub mod compare;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BitLit {
    pub var: u32,
    pub pos: bool,
}

impl BitLit {
    pub fn negate(self) -> BitLit {
        BitLit { var: self.var, pos: !self.pos }
    }
}

#[derive(Default)]
pub struct Cnf {
    pub num_vars: u32,
    pub clauses: Vec<Vec<BitLit>>,
}

pub struct Blaster {
    next_var: u32,
    clauses: Vec<Vec<BitLit>>,
    /// Memoized blasted words: TermId -> LSB..MSB bit literals.
    pub(crate) cache: FxHashMap<TermId, Vec<BitLit>>,
}

impl Blaster {
    pub fn new() -> Blaster {
        // var 0 is the pinned-true constant.
        let mut b = Blaster {
            next_var: 1,
            clauses: Vec::new(),
            cache: FxHashMap::default(),
        };
        let t = BitLit { var: 0, pos: true };
        b.add_clause(&[t]); // force var0 = true
        b
    }

    pub fn one(&self) -> BitLit {
        BitLit { var: 0, pos: true }
    }

    pub fn zero(&self) -> BitLit {
        BitLit { var: 0, pos: false }
    }

    pub fn fresh(&mut self) -> BitLit {
        let v = self.next_var;
        self.next_var += 1;
        BitLit { var: v, pos: true }
    }

    pub fn add_clause(&mut self, lits: &[BitLit]) {
        self.clauses.push(lits.to_vec());
    }

    pub fn finish(self) -> Cnf {
        Cnf { num_vars: self.next_var, clauses: self.clauses }
    }

    pub fn not1(&self, a: BitLit) -> BitLit {
        a.negate()
    }

    pub fn and2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // o <-> (a AND b):
        //   o -> a          : (NOT o OR a)
        //   o -> b          : (NOT o OR b)
        //   (a AND b) -> o  : (NOT a OR NOT b OR o)
        self.add_clause(&[o.negate(), a]);
        self.add_clause(&[o.negate(), b]);
        self.add_clause(&[o, a.negate(), b.negate()]);
        o
    }

    pub fn or2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // o <-> (a OR b):
        //   (NOT a) -> NOT o  : (o OR NOT a)
        //   (NOT b) -> NOT o  : (o OR NOT b)
        //   NOT o -> (NOT a AND NOT b) : (NOT o OR a OR b)
        self.add_clause(&[o, a.negate()]);
        self.add_clause(&[o, b.negate()]);
        self.add_clause(&[o.negate(), a, b]);
        o
    }

    pub fn xor2(&mut self, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // o <-> (a XOR b):
        //   o -> (a OR b)           : (NOT o OR a OR b)
        //   o -> NOT(a AND b)       : (NOT o OR NOT a OR NOT b)
        //   NOT o -> (a <-> b):
        //     (NOT a AND NOT b) -> NOT o : (o OR NOT a OR b) — wait, check carefully
        //   NOT o -> (a XNOR b):
        //     NOT o AND a -> b      : (o OR NOT a OR b)
        //     NOT o AND NOT a -> NOT b : (o OR a OR NOT b)
        self.add_clause(&[o.negate(), a, b]);
        self.add_clause(&[o.negate(), a.negate(), b.negate()]);
        self.add_clause(&[o, a.negate(), b]);
        self.add_clause(&[o, a, b.negate()]);
        o
    }

    /// sel ? a : b
    pub fn mux2(&mut self, sel: BitLit, a: BitLit, b: BitLit) -> BitLit {
        let o = self.fresh();
        // sel -> (o <-> a):
        //   NOT sel OR NOT o OR a
        //   NOT sel OR o OR NOT a
        // NOT sel -> (o <-> b):
        //   sel OR NOT o OR b
        //   sel OR o OR NOT b
        self.add_clause(&[sel.negate(), o.negate(), a]);
        self.add_clause(&[sel.negate(), o, a.negate()]);
        self.add_clause(&[sel, o.negate(), b]);
        self.add_clause(&[sel, o, b.negate()]);
        o
    }

    pub fn full_adder(&mut self, a: BitLit, b: BitLit, cin: BitLit) -> (BitLit, BitLit) {
        let axb = self.xor2(a, b);
        let sum = self.xor2(axb, cin);
        let t1 = self.and2(a, b);
        let t2 = self.and2(axb, cin);
        let cout = self.or2(t1, t2);
        (sum, cout)
    }

    /// Recursively bit-blast a BitVec-sorted term. Result is memoized in `self.cache`.
    /// Bits are ordered LSB→MSB (index 0 = least significant).
    pub fn blast_word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) {
            return v.clone();
        }
        let node = ctx.term_node(t).clone();
        let result = match node {
            TermNode::Const { val: ConstVal::BitVec(_), .. } => {
                let (width, value_ref) = ctx.bv_const_value(t).unwrap();
                let mut remaining = value_ref.clone();
                let two = shinri_num::Integer::from(2u64);
                (0..width).map(|_| {
                    let (q, r) = remaining.div_rem(&two);
                    remaining = q;
                    if r.is_zero() { self.zero() } else { self.one() }
                }).collect()
            }
            TermNode::App { op: Op::Uninterpreted(_), args, sort } => {
                let child_ids = ctx.children(args).to_vec();
                debug_assert!(child_ids.is_empty(), "non-nullary uninterpreted BV fn out of scope");
                let width = ctx.bv_width(sort).expect("BV-sorted variable has BV sort");
                (0..width).map(|_| self.fresh()).collect()
            }
            TermNode::App { op: Op::Builtin(bv_op), args, .. } => {
                let child_ids = ctx.children(args).to_vec();
                match bv_op {
                    BuiltinOp::BvNot => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        bitwise::bvnot(self, &a)
                    }
                    BuiltinOp::BvAnd => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        bitwise::bvand(self, &a, &b)
                    }
                    BuiltinOp::BvOr => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        bitwise::bvor(self, &a, &b)
                    }
                    BuiltinOp::BvXor => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        bitwise::bvxor(self, &a, &b)
                    }
                    BuiltinOp::BvNand => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        bitwise::bvnand(self, &a, &b)
                    }
                    BuiltinOp::BvNor => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        bitwise::bvnor(self, &a, &b)
                    }
                    BuiltinOp::BvXnor => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        bitwise::bvxnor(self, &a, &b)
                    }
                    BuiltinOp::BvNeg => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        arith::bvneg(self, &a)
                    }
                    BuiltinOp::BvAdd => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        arith::bvadd(self, &a, &b)
                    }
                    BuiltinOp::BvSub => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        arith::bvsub(self, &a, &b)
                    }
                    BuiltinOp::BvMul => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        arith::bvmul(self, &a, &b)
                    }
                    BuiltinOp::BvUdiv => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        div::bvudiv(self, &a, &b)
                    }
                    BuiltinOp::BvUrem => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        div::bvurem(self, &a, &b)
                    }
                    BuiltinOp::BvSdiv => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        div::bvsdiv(self, &a, &b)
                    }
                    BuiltinOp::BvSrem => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        div::bvsrem(self, &a, &b)
                    }
                    BuiltinOp::BvSmod => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        div::bvsmod(self, &a, &b)
                    }
                    BuiltinOp::BvShl => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        shift::bvshl(self, &a, &b)
                    }
                    BuiltinOp::BvLshr => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        shift::bvlshr(self, &a, &b)
                    }
                    BuiltinOp::BvAshr => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        let b = self.blast_word(ctx, child_ids[1]);
                        shift::bvashr(self, &a, &b)
                    }
                    BuiltinOp::BvConcat => {
                        // SMT-LIB concat(a, b): a is the HIGH bits, b is the LOW bits.
                        let hi = self.blast_word(ctx, child_ids[0]);
                        let lo = self.blast_word(ctx, child_ids[1]);
                        structural::concat(&hi, &lo)
                    }
                    BuiltinOp::BvExtract { hi, lo } => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        structural::extract(&a, hi, lo)
                    }
                    BuiltinOp::BvZeroExtend(k) => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        structural::zero_extend(&a, k, self)
                    }
                    BuiltinOp::BvSignExtend(k) => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        structural::sign_extend(&a, k)
                    }
                    BuiltinOp::BvRotateLeft(k) => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        shift::rotate_left(&a, k)
                    }
                    BuiltinOp::BvRotateRight(k) => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        shift::rotate_right(&a, k)
                    }
                    BuiltinOp::BvRepeat(k) => {
                        let a = self.blast_word(ctx, child_ids[0]);
                        structural::repeat(&a, k)
                    }
                    // Comparison ops are Bool-sorted — must not reach blast_word.
                    BuiltinOp::BvUlt | BuiltinOp::BvUle | BuiltinOp::BvUgt | BuiltinOp::BvUge
                    | BuiltinOp::BvSlt | BuiltinOp::BvSle | BuiltinOp::BvSgt | BuiltinOp::BvSge => {
                        unreachable!("BV comparison op is Bool-sorted; use blast_atom instead");
                    }
                    _ => unreachable!("non-BV builtin reached blast_word"),
                }
            }
            _ => unreachable!("blast_word called on non-BV term"),
        };
        self.cache.insert(t, result.clone());
        result
    }

    /// Return the bits cached for every BV *variable* term: nullary `Op::Uninterpreted`
    /// apps whose sort is a BitVec sort.
    ///
    /// Approach (a): post-hoc filter over `self.cache` — no changes to `blast_word`.
    /// Constants (`TermNode::Const`) and non-nullary or Builtin apps are excluded.
    pub fn exported_var_bits(&self, ctx: &Context) -> FxHashMap<TermId, Vec<BitLit>> {
        self.cache
            .iter()
            .filter(|(&tid, _)| {
                matches!(
                    ctx.term_node(tid),
                    TermNode::App { op: Op::Uninterpreted(_), args, sort }
                    if ctx.children(*args).is_empty() && ctx.bv_width(*sort).is_some()
                )
            })
            .map(|(&tid, bits)| (tid, bits.clone()))
            .collect()
    }

    /// Bit-blast a Bool-sorted BV predicate, returning a single `BitLit`.
    /// Handles: `Eq`/`Distinct` over BV operands, and all `BvUlt..BvSge` ops.
    pub fn blast_atom(&mut self, ctx: &Context, t: TermId) -> BitLit {
        let node = ctx.term_node(t).clone();
        match node {
            TermNode::App { op: Op::Builtin(BuiltinOp::Eq), args, .. } => {
                let child_ids = ctx.children(args).to_vec();
                let a = self.blast_word(ctx, child_ids[0]);
                let b = self.blast_word(ctx, child_ids[1]);
                compare::eq(self, &a, &b)
            }
            TermNode::App { op: Op::Builtin(BuiltinOp::Distinct), args, .. } => {
                let child_ids = ctx.children(args).to_vec();
                // Assume binary Distinct (n-ary is lowered before this stage).
                let a = self.blast_word(ctx, child_ids[0]);
                let b = self.blast_word(ctx, child_ids[1]);
                let eq_lit = compare::eq(self, &a, &b);
                self.not1(eq_lit)
            }
            TermNode::App { op: Op::Builtin(bv_cmp), args, .. } => {
                let child_ids = ctx.children(args).to_vec();
                let a = self.blast_word(ctx, child_ids[0]);
                let b = self.blast_word(ctx, child_ids[1]);
                match bv_cmp {
                    BuiltinOp::BvUlt => compare::ult(self, &a, &b),
                    BuiltinOp::BvUle => compare::ule(self, &a, &b),
                    BuiltinOp::BvUgt => compare::ugt(self, &a, &b),
                    BuiltinOp::BvUge => compare::uge(self, &a, &b),
                    BuiltinOp::BvSlt => compare::slt(self, &a, &b),
                    BuiltinOp::BvSle => compare::sle(self, &a, &b),
                    BuiltinOp::BvSgt => compare::sgt(self, &a, &b),
                    BuiltinOp::BvSge => compare::sge(self, &a, &b),
                    _ => panic!("blast_atom called on non-predicate builtin"),
                }
            }
            _ => panic!("blast_atom called on non-predicate term"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_sat::{Lit, NoProof, NoTheory, Solver, SolveResult, SolverConfig, Var, Vmtf};

    /// Build a shinri_sat::Solver from a finished Cnf, with `num_vars` pre-allocated.
    fn cnf_to_solver(cnf: &Cnf) -> Solver<NoTheory, NoProof, Vmtf> {
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars {
            s.new_var();
        }
        for clause in &cnf.clauses {
            let sat_lits: Vec<Lit> = clause
                .iter()
                .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                .collect();
            s.add_clause(&sat_lits);
        }
        s
    }

    /// Pin a BitLit to a concrete Boolean value by adding a unit assumption clause,
    /// then read the model value of another BitLit after solving.
    fn solve_with_inputs_and_read(
        blaster: Blaster,
        inputs: &[(BitLit, bool)],
        outputs: &[BitLit],
    ) -> Vec<bool> {
        let mut cnf = blaster.finish();
        // Force each input to its assigned value via unit clauses.
        for &(bl, val) in inputs {
            let lit = if val { bl } else { bl.negate() };
            cnf.clauses.push(vec![lit]);
        }
        let mut s = cnf_to_solver(&cnf);
        let result = s.solve();
        assert_eq!(result, SolveResult::Sat, "expected SAT for gate truth-table input");
        outputs
            .iter()
            .map(|bl| s.value_of(Var::new(bl.var)).expect("output var unassigned"))
            // BitLit stores the var index; the actual model value accounts for polarity:
            // a positive BitLit means "the output is this var"; if the var is true, output is true.
            // But `value_of` returns the raw var truth — if pos=true, value IS the bit.
            // If pos=false (negate), the bit is the opposite.
            .zip(outputs.iter())
            .map(|(v, bl)| if bl.pos { v } else { !v })
            .collect()
    }

    #[test]
    fn const_bits_and_fresh_allocate_distinct_vars() {
        let mut b = Blaster::new();
        assert_eq!(b.one().var, 0);
        assert!(b.one().pos);
        assert_eq!(b.zero().var, 0);
        assert!(!b.zero().pos);
        let x = b.fresh();
        let y = b.fresh();
        assert_ne!(x.var, y.var);
        assert!(x.var >= 1 && y.var >= 1);
    }

    #[test]
    fn full_adder_truth_table_structural() {
        // Structural check: full_adder returns two distinct signal lits.
        let mut b = Blaster::new();
        let a = b.fresh();
        let bb = b.fresh();
        let c = b.fresh();
        let (s, co) = b.full_adder(a, bb, c);
        assert_ne!(s.var, co.var);
    }

    /// Helper: build a fresh Blaster, pin 3 input vars, call full_adder,
    /// solve and return (sum_bit, cout_bit).
    fn check_full_adder(av: bool, bv: bool, cinv: bool) -> (bool, bool) {
        let mut bl = Blaster::new();
        let a = bl.fresh();
        let b = bl.fresh();
        let cin = bl.fresh();
        let (sum, cout) = bl.full_adder(a, b, cin);
        let results = solve_with_inputs_and_read(bl, &[(a, av), (b, bv), (cin, cinv)], &[sum, cout]);
        (results[0], results[1])
    }

    #[test]
    fn full_adder_solve_all_8_combinations() {
        for av in [false, true] {
            for bv in [false, true] {
                for cinv in [false, true] {
                    let total = (av as u32) + (bv as u32) + (cinv as u32);
                    let expected_sum = (total & 1) == 1;
                    let expected_cout = total >= 2;
                    let (got_sum, got_cout) = check_full_adder(av, bv, cinv);
                    assert_eq!(
                        got_sum, expected_sum,
                        "full_adder sum wrong for a={av} b={bv} cin={cinv}: expected {expected_sum} got {got_sum}"
                    );
                    assert_eq!(
                        got_cout, expected_cout,
                        "full_adder cout wrong for a={av} b={bv} cin={cinv}: expected {expected_cout} got {got_cout}"
                    );
                }
            }
        }
    }

    #[test]
    fn and2_solve_verify() {
        for (av, bv) in [(false, false), (false, true), (true, false), (true, true)] {
            let mut bl = Blaster::new();
            let a = bl.fresh();
            let b = bl.fresh();
            let o = bl.and2(a, b);
            let results = solve_with_inputs_and_read(bl, &[(a, av), (b, bv)], &[o]);
            let expected = av && bv;
            assert_eq!(
                results[0], expected,
                "and2 wrong for a={av} b={bv}: expected {expected} got {}",
                results[0]
            );
        }
    }

    #[test]
    fn or2_solve_verify() {
        for (av, bv) in [(false, false), (false, true), (true, false), (true, true)] {
            let mut bl = Blaster::new();
            let a = bl.fresh();
            let b = bl.fresh();
            let o = bl.or2(a, b);
            let results = solve_with_inputs_and_read(bl, &[(a, av), (b, bv)], &[o]);
            let expected = av || bv;
            assert_eq!(
                results[0], expected,
                "or2 wrong for a={av} b={bv}: expected {expected} got {}",
                results[0]
            );
        }
    }

    #[test]
    fn xor2_solve_verify() {
        for (av, bv) in [(false, false), (false, true), (true, false), (true, true)] {
            let mut bl = Blaster::new();
            let a = bl.fresh();
            let b = bl.fresh();
            let o = bl.xor2(a, b);
            let results = solve_with_inputs_and_read(bl, &[(a, av), (b, bv)], &[o]);
            let expected = av ^ bv;
            assert_eq!(
                results[0], expected,
                "xor2 wrong for a={av} b={bv}: expected {expected} got {}",
                results[0]
            );
        }
    }

    // ── blast dispatch tests (TDD RED → GREEN) ──────────────────────────────

    #[test]
    fn blast_word_constant_values() {
        use shinri_core::{Context, Op, BuiltinOp};
        use shinri_num::Integer;
        // blast constant 5 -> solve_value == 5
        {
            let mut ctx = Context::new();
            let c = ctx.mk_bv_const(8, Integer::from(5u64));
            let mut b = Blaster::new();
            let bits = b.blast_word(&ctx, c);
            assert_eq!(bits.len(), 8);
            assert_eq!(crate::testkit::solve_value(b, &bits), 5);
        }
        // high bit set: 200
        {
            let mut ctx = Context::new();
            let c = ctx.mk_bv_const(8, Integer::from(200u64));
            let mut b = Blaster::new();
            let bits = b.blast_word(&ctx, c);
            assert_eq!(crate::testkit::solve_value(b, &bits), 200);
        }
        // zero
        {
            let mut ctx = Context::new();
            let c = ctx.mk_bv_const(8, Integer::from(0u64));
            let mut b = Blaster::new();
            let bits = b.blast_word(&ctx, c);
            assert_eq!(crate::testkit::solve_value(b, &bits), 0);
        }
    }

    #[test]
    fn blast_word_bvadd_of_consts() {
        use shinri_core::{Context, Op, BuiltinOp};
        use shinri_num::Integer;
        let mut ctx = Context::new();
        let a = ctx.mk_bv_const(8, Integer::from(3u64));
        let b_c = ctx.mk_bv_const(8, Integer::from(200u64));
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[a, b_c]).unwrap();
        let mut bl = Blaster::new();
        let bits = bl.blast_word(&ctx, add);
        assert_eq!(bits.len(), 8);
        assert_eq!(crate::testkit::solve_value(bl, &bits), (3u64 + 200u64) & 0xFF);
    }

    #[test]
    fn blast_word_variable_memoization() {
        use shinri_core::{Context, Op};
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let mut bl = Blaster::new();
        let bx1 = bl.blast_word(&ctx, x);
        let bx2 = bl.blast_word(&ctx, x);
        assert_eq!(bx1, bx2, "same variable must reuse cached bits");
        assert_eq!(bx1.len(), 8);
    }

    #[test]
    fn blast_atom_ult_true_and_false() {
        use shinri_core::{Context, Op, BuiltinOp};
        use shinri_num::Integer;
        // (bvult #x03 #x05) -> 1
        {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(3u64));
            let b_c = ctx.mk_bv_const(8, Integer::from(5u64));
            let atom = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[a, b_c]).unwrap();
            let mut bl = Blaster::new();
            let lit = bl.blast_atom(&ctx, atom);
            assert_eq!(crate::testkit::solve_value(bl, std::slice::from_ref(&lit)), 1, "bvult(3,5)=1");
        }
        // (bvult #x05 #x03) -> 0
        {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(5u64));
            let b_c = ctx.mk_bv_const(8, Integer::from(3u64));
            let atom = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[a, b_c]).unwrap();
            let mut bl = Blaster::new();
            let lit = bl.blast_atom(&ctx, atom);
            assert_eq!(crate::testkit::solve_value(bl, std::slice::from_ref(&lit)), 0, "bvult(5,3)=0");
        }
    }

    #[test]
    fn blast_atom_eq_true_and_false() {
        use shinri_core::{Context, Op};
        use shinri_num::Integer;
        // (= #x05 #x05) -> 1
        {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(5u64));
            let b_c = ctx.mk_bv_const(8, Integer::from(5u64));
            let atom = ctx.mk_eq(a, b_c).unwrap();
            let mut bl = Blaster::new();
            let lit = bl.blast_atom(&ctx, atom);
            assert_eq!(crate::testkit::solve_value(bl, std::slice::from_ref(&lit)), 1, "eq(5,5)=1");
        }
        // (= #x05 #x06) -> 0
        {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(5u64));
            let b_c = ctx.mk_bv_const(8, Integer::from(6u64));
            let atom = ctx.mk_eq(a, b_c).unwrap();
            let mut bl = Blaster::new();
            let lit = bl.blast_atom(&ctx, atom);
            assert_eq!(crate::testkit::solve_value(bl, std::slice::from_ref(&lit)), 0, "eq(5,6)=0");
        }
    }

    #[test]
    fn blast_word_constant_and_var_and_add() {
        use shinri_core::{Context, Op, BuiltinOp};
        use shinri_num::Integer;
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(1u64));
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, c]).unwrap();
        let mut b = Blaster::new();
        let bits = b.blast_word(&ctx, add);
        assert_eq!(bits.len(), 8);
        let bx1 = b.blast_word(&ctx, x);
        let bx2 = b.blast_word(&ctx, x);
        assert_eq!(bx1, bx2);
    }

    #[test]
    fn blast_atom_eq_is_solvable_true() {
        use shinri_core::{Context, Op, BuiltinOp};
        use shinri_num::Integer;
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let lhs = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, one]).unwrap();
        let yf = ctx.declare_fun("y", &[], s8);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let atom = ctx.mk_eq(lhs, y).unwrap();
        let mut b = Blaster::new();
        let _l = b.blast_atom(&ctx, atom);
    }

    #[test]
    fn mux2_solve_verify() {
        // Check sel=false picks b, sel=true picks a for a few combos.
        for (selv, av, bv) in [
            (false, false, false),
            (false, false, true),
            (false, true, false),
            (false, true, true),
            (true, false, false),
            (true, false, true),
            (true, true, false),
            (true, true, true),
        ] {
            let mut bl = Blaster::new();
            let sel = bl.fresh();
            let a = bl.fresh();
            let b = bl.fresh();
            let o = bl.mux2(sel, a, b);
            let results = solve_with_inputs_and_read(bl, &[(sel, selv), (a, av), (b, bv)], &[o]);
            // mux2(sel, a, b) = sel ? a : b
            let expected = if selv { av } else { bv };
            assert_eq!(
                results[0], expected,
                "mux2 wrong for sel={selv} a={av} b={bv}: expected {expected} got {}",
                results[0]
            );
        }
    }
}
