use crate::ids::{RatId, SortId, TermId};
use crate::sort::SortNode;
use crate::symbol::StringInterner;
use crate::term::{ChildSlice, ConstVal, TermNode};
use rustc_hash::FxHashMap;
use shinri_num::Rational;

/// The single owning arena for all interned sorts (and, after Task 4, terms).
pub struct Context {
    sorts: Vec<SortNode>,
    sort_interner: FxHashMap<SortNode, SortId>,
    symbols: StringInterner,
    nodes: Vec<TermNode>,
    children: Vec<TermId>,
    nums: Vec<Rational>,
    term_interner: FxHashMap<TermKey, TermId>,
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

    pub fn sort_node(&self, id: SortId) -> &SortNode {
        &self.sorts[id.index()]
    }
}

/// A fully-resolved structural key for term interning. Distinct from `TermNode`
/// because `TermNode::App` stores a `ChildSlice` (offset into the arena); two
/// structurally identical apps built at different times would have different
/// slices but must intern to the same id. The key resolves children to their ids.
#[derive(Clone, PartialEq, Eq, Hash)]
enum TermKey {
    App { op: crate::term::Op, args: Vec<TermId>, sort: SortId },
    Const { val: ConstVal, sort: SortId },
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
        ChildSlice { off, len: args.len() as u32 }
    }

    pub fn mk_const_bool(&mut self, b: bool) -> TermId {
        let sort = self.bool_sort();
        let val = ConstVal::Bool(b);
        self.intern_with_key(
            TermKey::Const { val, sort },
            TermNode::Const { val, sort },
        )
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
        self.intern_with_key(
            TermKey::Const { val, sort },
            TermNode::Const { val, sort },
        )
    }

    pub fn term_node(&self, id: TermId) -> &TermNode {
        &self.nodes[id.index()]
    }

    pub fn children(&self, slice: ChildSlice) -> &[TermId] {
        let start = slice.off as usize;
        let end = start + slice.len as usize;
        &self.children[start..end]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sort::SortNode;
    use crate::term::{ConstVal, TermNode};
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
            TermNode::Const { val: ConstVal::Bool(b), sort } => {
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
}
