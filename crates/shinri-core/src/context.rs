use crate::error::SortError;
use crate::ids::{RatId, SortId, SymbolId, TermId};
use crate::sort::SortNode;
use crate::symbol::StringInterner;
use crate::term::{BuiltinOp, ChildSlice, ConstVal, Op, TermNode};
use rustc_hash::FxHashMap;
use shinri_num::Rational;

/// The single owning arena for all interned sorts (and, after Task 4, terms).
#[derive(Clone)]
pub struct Context {
    sorts: Vec<SortNode>,
    sort_interner: FxHashMap<SortNode, SortId>,
    symbols: StringInterner,
    nodes: Vec<TermNode>,
    children: Vec<TermId>,
    nums: Vec<Rational>,
    term_interner: FxHashMap<TermKey, TermId>,
    fun_sigs: FxHashMap<SymbolId, (Vec<SortId>, SortId)>,
    bool_sort: SortId,
    int_sort: SortId,
    real_sort: SortId,
}

impl Default for Context {
    fn default() -> Self {
        Context::new()
    }
}

impl Context {
    pub fn new() -> Context {
        let mut ctx = Context {
            sorts: Vec::new(),
            sort_interner: FxHashMap::default(),
            symbols: StringInterner::default(),
            nodes: Vec::new(),
            children: Vec::new(),
            nums: Vec::new(),
            term_interner: FxHashMap::default(),
            fun_sigs: FxHashMap::default(),
            // placeholders; overwritten immediately below
            bool_sort: SortId::from_index(0),
            int_sort: SortId::from_index(0),
            real_sort: SortId::from_index(0),
        };
        ctx.bool_sort = ctx.intern_sort(SortNode::Bool);
        ctx.int_sort = ctx.intern_sort(SortNode::Int);
        ctx.real_sort = ctx.intern_sort(SortNode::Real);
        ctx
    }

    fn intern_sort(&mut self, node: SortNode) -> SortId {
        if let Some(&id) = self.sort_interner.get(&node) {
            return id;
        }
        let id = SortId::from_index(self.sorts.len());
        self.sorts.push(node.clone());
        self.sort_interner.insert(node, id);
        id
    }

    #[inline]
    pub fn bool_sort(&self) -> SortId {
        self.bool_sort
    }
    #[inline]
    pub fn int_sort(&self) -> SortId {
        self.int_sort
    }
    #[inline]
    pub fn real_sort(&self) -> SortId {
        self.real_sort
    }

    pub fn declare_sort(&mut self, name: &str) -> SortId {
        let sym = self.symbols.intern(name);
        self.intern_sort(SortNode::Uninterpreted(sym))
    }

    pub fn array_sort(&mut self, index: SortId, elem: SortId) -> SortId {
        self.intern_sort(SortNode::Array(index, elem))
    }

    pub fn sort_node(&self, id: SortId) -> &SortNode {
        &self.sorts[id.index()]
    }

    pub fn symbol_name(&self, sym: SymbolId) -> &str {
        self.symbols.resolve(sym)
    }
}

impl Context {
    pub fn sort_of(&self, t: TermId) -> SortId {
        match self.term_node(t) {
            TermNode::App { sort, .. } => *sort,
            TermNode::Const { sort, .. } => *sort,
        }
    }

    pub fn declare_fun(&mut self, name: &str, params: &[SortId], result: SortId) -> SymbolId {
        let sym = self.symbols.intern(name);
        self.fun_sigs.insert(sym, (params.to_vec(), result));
        sym
    }

    /// Build (and intern) `op` applied to `args`, checking well-sortedness.
    pub fn mk_app(&mut self, op: Op, args: &[TermId]) -> Result<TermId, SortError> {
        let result_sort = self.check_app(op, args)?;
        let slice = self.push_children(args);
        let key = TermKey::App {
            op,
            args: args.to_vec(),
            sort: result_sort,
        };
        Ok(self.intern_with_key(
            key,
            TermNode::App {
                op,
                args: slice,
                sort: result_sort,
            },
        ))
    }

    pub fn mk_eq(&mut self, a: TermId, b: TermId) -> Result<TermId, SortError> {
        self.mk_app(Op::Builtin(BuiltinOp::Eq), &[a, b])
    }

    /// Returns the result sort if the application is well-sorted.
    fn check_app(&self, op: Op, args: &[TermId]) -> Result<SortId, SortError> {
        let bool_s = self.bool_sort();
        match op {
            Op::Uninterpreted(sym) => {
                let (params, result) =
                    self.fun_sigs.get(&sym).ok_or(SortError::UndeclaredSymbol)?;
                if args.len() != params.len() {
                    return Err(SortError::Arity {
                        expected: params.len(),
                        found: args.len(),
                    });
                }
                for (&arg, &expected) in args.iter().zip(params.iter()) {
                    let found = self.sort_of(arg);
                    if found != expected {
                        return Err(SortError::Mismatch { expected, found });
                    }
                }
                Ok(*result)
            }
            Op::Builtin(b) => self.check_builtin(b, args, bool_s),
        }
    }

    fn check_builtin(
        &self,
        b: BuiltinOp,
        args: &[TermId],
        bool_s: SortId,
    ) -> Result<SortId, SortError> {
        use BuiltinOp::*;
        let int_s = self.int_sort();
        let real_s = self.real_sort();
        let is_arith = |s: SortId| s == int_s || s == real_s;
        match b {
            // Boolean connectives: all args Bool -> Bool.
            Not => {
                expect_arity(args, 1)?;
                expect_all(self, args, bool_s)?;
                Ok(bool_s)
            }
            And | Or | Implies | Xor => {
                if args.len() < 2 {
                    return Err(SortError::Arity {
                        expected: 2,
                        found: args.len(),
                    });
                }
                expect_all(self, args, bool_s)?;
                Ok(bool_s)
            }
            Ite => {
                expect_arity(args, 3)?;
                if self.sort_of(args[0]) != bool_s {
                    return Err(SortError::Mismatch {
                        expected: bool_s,
                        found: self.sort_of(args[0]),
                    });
                }
                let then_s = self.sort_of(args[1]);
                let else_s = self.sort_of(args[2]);
                if then_s != else_s {
                    return Err(SortError::Mismatch {
                        expected: then_s,
                        found: else_s,
                    });
                }
                Ok(then_s)
            }
            // Equality / distinct: >=2 args of one common sort -> Bool.
            Eq | Distinct => {
                if args.len() < 2 {
                    return Err(SortError::Arity {
                        expected: 2,
                        found: args.len(),
                    });
                }
                let first = self.sort_of(args[0]);
                for &a in &args[1..] {
                    let s = self.sort_of(a);
                    if s != first {
                        return Err(SortError::Mismatch {
                            expected: first,
                            found: s,
                        });
                    }
                }
                Ok(bool_s)
            }
            // Arithmetic: all args one arithmetic sort.
            Neg => {
                expect_arity(args, 1)?;
                let s = self.sort_of(args[0]);
                if !is_arith(s) {
                    return Err(SortError::NotApplicable);
                }
                Ok(s)
            }
            Add | Sub | Mul => {
                if args.len() < 2 {
                    return Err(SortError::Arity {
                        expected: 2,
                        found: args.len(),
                    });
                }
                let s = self.sort_of(args[0]);
                if !is_arith(s) {
                    return Err(SortError::NotApplicable);
                }
                for &a in &args[1..] {
                    if self.sort_of(a) != s {
                        return Err(SortError::NotApplicable);
                    }
                }
                Ok(s)
            }
            Le | Lt | Ge | Gt => {
                expect_arity(args, 2)?;
                let s = self.sort_of(args[0]);
                if !is_arith(s) || self.sort_of(args[1]) != s {
                    return Err(SortError::NotApplicable);
                }
                Ok(bool_s)
            }
            Select => {
                expect_arity(args, 2)?;
                let (idx, elem) = match self.sort_node(self.sort_of(args[0])) {
                    SortNode::Array(i, e) => (*i, *e),
                    _ => return Err(SortError::NotApplicable),
                };
                let found = self.sort_of(args[1]);
                if found != idx {
                    return Err(SortError::Mismatch { expected: idx, found });
                }
                Ok(elem)
            }
            Store => {
                expect_arity(args, 3)?;
                let arr = self.sort_of(args[0]);
                let (idx, elem) = match self.sort_node(arr) {
                    SortNode::Array(i, e) => (*i, *e),
                    _ => return Err(SortError::NotApplicable),
                };
                let fi = self.sort_of(args[1]);
                if fi != idx {
                    return Err(SortError::Mismatch { expected: idx, found: fi });
                }
                let fe = self.sort_of(args[2]);
                if fe != elem {
                    return Err(SortError::Mismatch { expected: elem, found: fe });
                }
                Ok(arr)
            }
        }
    }
}

fn expect_arity(args: &[TermId], n: usize) -> Result<(), SortError> {
    if args.len() == n {
        Ok(())
    } else {
        Err(SortError::Arity {
            expected: n,
            found: args.len(),
        })
    }
}

fn expect_all(ctx: &Context, args: &[TermId], expected: SortId) -> Result<(), SortError> {
    for &a in args {
        let found = ctx.sort_of(a);
        if found != expected {
            return Err(SortError::Mismatch { expected, found });
        }
    }
    Ok(())
}

/// A fully-resolved structural key for term interning. Distinct from `TermNode`
/// because `TermNode::App` stores a `ChildSlice` (offset into the arena); two
/// structurally identical apps built at different times would have different
/// slices but must intern to the same id. The key resolves children to their ids.
#[derive(Clone, PartialEq, Eq, Hash)]
enum TermKey {
    App {
        op: crate::term::Op,
        args: Vec<TermId>,
        sort: SortId,
    },
    Const {
        val: ConstVal,
        sort: SortId,
    },
}

impl Context {
    fn intern_with_key(&mut self, key: TermKey, node: TermNode) -> TermId {
        if let Some(&id) = self.term_interner.get(&key) {
            return id;
        }
        let id = TermId::from_index(self.nodes.len());
        self.nodes.push(node);
        self.term_interner.insert(key, id);
        id
    }

    pub(crate) fn push_children(&mut self, args: &[TermId]) -> ChildSlice {
        let off = self.children.len() as u32;
        self.children.extend_from_slice(args);
        ChildSlice {
            off,
            len: args.len() as u32,
        }
    }

    pub fn mk_const_bool(&mut self, b: bool) -> TermId {
        let sort = self.bool_sort();
        let val = ConstVal::Bool(b);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    pub fn mk_numeral(&mut self, value: Rational, sort: SortId) -> TermId {
        // Intern by numeric value: reuse an existing RatId if the value is present.
        let rat_id = match self.nums.iter().position(|r| *r == value) {
            Some(idx) => RatId::new(idx as u32),
            None => {
                let id = RatId::new(self.nums.len() as u32);
                self.nums.push(value);
                id
            }
        };
        let val = ConstVal::Num(rat_id);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    pub fn term_node(&self, id: TermId) -> &TermNode {
        &self.nodes[id.index()]
    }

    /// Returns `true` if `id` was interned into this context (bounds check).
    pub fn contains_term(&self, id: TermId) -> bool {
        id.index() < self.nodes.len()
    }

    /// The exact `Rational` of a numeral term, or `None` if `t` is not a numeral.
    pub fn numeral_value(&self, t: TermId) -> Option<&Rational> {
        match self.term_node(t) {
            TermNode::Const {
                val: ConstVal::Num(id),
                ..
            } => Some(&self.nums[id.index()]),
            _ => None,
        }
    }

    pub fn children(&self, slice: ChildSlice) -> &[TermId] {
        let start = slice.off as usize;
        let end = start + slice.len as usize;
        &self.children[start..end]
    }

    /// Rebuild `t`, replacing each occurrence of `params[i]` with `args[i]`.
    /// Re-interns the result (maximal sharing preserved).
    pub fn substitute(&mut self, t: TermId, params: &[TermId], args: &[TermId]) -> TermId {
        debug_assert_eq!(
            params.len(),
            args.len(),
            "substitute: param/arg length mismatch"
        );
        // Direct replacement at this node?
        if let Some(pos) = params.iter().position(|&p| p == t) {
            return args[pos];
        }
        match self.term_node(t).clone() {
            TermNode::Const { .. } => t, // constants contain no params
            TermNode::App {
                op, args: slice, ..
            } => {
                let child_ids: Vec<TermId> = self.children(slice).to_vec();
                let mut new_children = Vec::with_capacity(child_ids.len());
                let mut changed = false;
                for c in child_ids {
                    let nc = self.substitute(c, params, args);
                    changed |= nc != c;
                    new_children.push(nc);
                }
                if !changed {
                    return t;
                }
                // A sort-consistent substitution cannot make a well-sorted term
                // ill-sorted, so this rebuild always succeeds.
                self.mk_app(op, &new_children)
                    .expect("substitute: sort-consistent rebuild cannot fail")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::SortError;
    use crate::sort::SortNode;
    use crate::term::{BuiltinOp, ConstVal, Op, TermNode};
    use shinri_num::Rational;

    #[test]
    fn well_known_sorts_distinct_and_stable() {
        let ctx = Context::new();
        assert_ne!(ctx.bool_sort(), ctx.int_sort());
        assert_ne!(ctx.int_sort(), ctx.real_sort());
        assert_eq!(*ctx.sort_node(ctx.bool_sort()), SortNode::Bool);
        assert_eq!(*ctx.sort_node(ctx.int_sort()), SortNode::Int);
        assert_eq!(*ctx.sort_node(ctx.real_sort()), SortNode::Real);
    }

    #[test]
    fn declare_sort_interns() {
        let mut ctx = Context::new();
        let a = ctx.declare_sort("A");
        let b = ctx.declare_sort("B");
        let a2 = ctx.declare_sort("A");
        assert_eq!(a, a2);
        assert_ne!(a, b);
    }

    #[test]
    fn bool_consts_intern() {
        let mut ctx = Context::new();
        let t = ctx.mk_const_bool(true);
        let t2 = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        assert_eq!(t, t2);
        assert_ne!(t, f);
        match ctx.term_node(t) {
            TermNode::Const {
                val: ConstVal::Bool(b),
                sort,
            } => {
                assert!(*b);
                assert_eq!(*sort, ctx.bool_sort());
            }
            _ => panic!("expected bool const"),
        }
    }

    #[test]
    fn numerals_intern_by_value() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let a = ctx.mk_numeral(Rational::from_int(7i128.into()), int);
        let b = ctx.mk_numeral(Rational::from_int(7i128.into()), int);
        let c = ctx.mk_numeral(Rational::from_int(8i128.into()), int);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn mk_app_checks_arithmetic_sorts() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let three = ctx.mk_numeral(shinri_num::Rational::from_int(3i128.into()), int);
        // 2 + 3 : Int
        let sum = ctx
            .mk_app(Op::Builtin(BuiltinOp::Add), &[two, three])
            .unwrap();
        assert_eq!(ctx.sort_of(sum), int);
        // 2 <= 3 : Bool
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[two, three])
            .unwrap();
        assert_eq!(ctx.sort_of(le), ctx.bool_sort());
    }

    #[test]
    fn mk_app_rejects_bool_in_arithmetic() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let t = ctx.mk_const_bool(true);
        let err = ctx
            .mk_app(Op::Builtin(BuiltinOp::Add), &[two, t])
            .unwrap_err();
        assert_eq!(err, SortError::NotApplicable);
    }

    #[test]
    fn mk_eq_requires_matching_sorts() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let t = ctx.mk_const_bool(true);
        assert!(ctx.mk_eq(two, two).is_ok());
        assert!(matches!(ctx.mk_eq(two, t), Err(SortError::Mismatch { .. })));
        let eq_id = ctx.mk_eq(two, two).unwrap();
        assert_eq!(ctx.sort_of(eq_id), ctx.bool_sort());
    }

    #[test]
    fn uninterpreted_application_checks_signature() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let bool_s = ctx.bool_sort();
        // declare-fun p (Int) Bool
        let p = ctx.declare_fun("p", &[int], bool_s);
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let app = ctx.mk_app(Op::Uninterpreted(p), &[two]).unwrap();
        assert_eq!(ctx.sort_of(app), bool_s);
        // wrong arity
        let err = ctx.mk_app(Op::Uninterpreted(p), &[two, two]).unwrap_err();
        assert_eq!(
            err,
            SortError::Arity {
                expected: 1,
                found: 2
            }
        );
    }

    #[test]
    fn substitute_replaces_leaves_and_reinterns() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        // body: x + 1, with x a placeholder param (an uninterpreted Int constant)
        let xsym = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xsym), &[]).unwrap();
        let one = ctx.mk_numeral(shinri_num::Rational::from_int(1i128.into()), int);
        let body = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, one]).unwrap();
        // substitute x := 5  =>  5 + 1
        let five = ctx.mk_numeral(shinri_num::Rational::from_int(5i128.into()), int);
        let result = ctx.substitute(body, &[x], &[five]);
        let expected = ctx
            .mk_app(Op::Builtin(BuiltinOp::Add), &[five, one])
            .unwrap();
        assert_eq!(result, expected); // re-interned to the same id
    }

    #[test]
    fn numeral_value_reads_back_the_rational() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let r = shinri_num::Rational::new(3i128.into(), 4i128.into()); // 3/4
        let t = ctx.mk_numeral(r.clone(), real);
        assert_eq!(ctx.numeral_value(t), Some(&r));
        // A non-numeral term returns None.
        let x = ctx.declare_fun("x", &[], real);
        let xt = ctx.mk_app(crate::term::Op::Uninterpreted(x), &[]).unwrap();
        assert_eq!(ctx.numeral_value(xt), None);
    }

    #[test]
    fn substitute_is_identity_when_no_param_occurs() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let one = ctx.mk_numeral(shinri_num::Rational::from_int(1i128.into()), int);
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let three = ctx.mk_numeral(shinri_num::Rational::from_int(3i128.into()), int);
        let sum = ctx
            .mk_app(Op::Builtin(BuiltinOp::Add), &[one, two])
            .unwrap();
        assert_eq!(ctx.substitute(sum, &[three], &[one]), sum);
    }

    #[test]
    fn array_select_store_sorts() {
        let mut ctx = Context::new();
        let idx = ctx.declare_sort("I");
        let elem = ctx.declare_sort("E");
        let arr_sort = ctx.array_sort(idx, elem);

        let sym_a = ctx_decl(&mut ctx, "a", arr_sort);
        let sym_i = ctx_decl(&mut ctx, "i", idx);
        let sym_e = ctx_decl(&mut ctx, "e", elem);
        let a = ctx.mk_app(Op::Uninterpreted(sym_a), &[]).unwrap();
        let i = ctx.mk_app(Op::Uninterpreted(sym_i), &[]).unwrap();
        let e = ctx.mk_app(Op::Uninterpreted(sym_e), &[]).unwrap();

        // (store a i e) : (Array I E)
        let st = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
        assert_eq!(ctx.sort_of(st), arr_sort);
        // (select (store a i e) i) : E
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, i]).unwrap();
        assert_eq!(ctx.sort_of(sel), elem);
        // wrong index sort is rejected
        let e_as_idx = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, e]);
        assert!(e_as_idx.is_err());
    }

    // helper local to the test module
    fn ctx_decl(ctx: &mut Context, name: &str, s: SortId) -> SymbolId {
        ctx.declare_fun(name, &[], s)
    }
}
