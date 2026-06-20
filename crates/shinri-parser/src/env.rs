use rustc_hash::FxHashMap;
use shinri_core::{SortId, SymbolId, TermId};

/// A non-recursive define-fun macro: `body` was interned against `formals`
/// (fresh placeholder consts); expansion substitutes actual args for formals.
#[derive(Clone)]
pub struct Macro {
    pub formals: Vec<TermId>,
    pub body: TermId,
}

/// Name resolution context. Lookup order at a head/leaf is enforced by the
/// parser (let → macro → fun → builtin); this type just stores the tables.
#[derive(Default)]
pub struct Env {
    sorts: FxHashMap<String, SortId>,
    funs: FxHashMap<String, SymbolId>,
    macros: FxHashMap<String, Macro>,
    let_frames: Vec<FxHashMap<String, TermId>>,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    pub fn add_sort(&mut self, name: &str, s: SortId) {
        self.sorts.insert(name.to_owned(), s);
    }
    pub fn lookup_sort(&self, name: &str) -> Option<SortId> {
        self.sorts.get(name).copied()
    }

    pub fn add_fun(&mut self, name: &str, sym: SymbolId) {
        self.funs.insert(name.to_owned(), sym);
    }
    pub fn lookup_fun(&self, name: &str) -> Option<SymbolId> {
        self.funs.get(name).copied()
    }

    pub fn add_macro(&mut self, name: &str, formals: Vec<TermId>, body: TermId) {
        self.macros.insert(name.to_owned(), Macro { formals, body });
    }
    pub fn lookup_macro(&self, name: &str) -> Option<&Macro> {
        self.macros.get(name)
    }

    pub fn push_let(&mut self, bindings: Vec<(String, TermId)>) {
        self.let_frames.push(bindings.into_iter().collect());
    }
    pub fn pop_let(&mut self) {
        self.let_frames.pop();
    }
    /// Innermost-first lookup of a let-bound name (shadowing).
    pub fn lookup_let(&self, name: &str) -> Option<TermId> {
        self.let_frames
            .iter()
            .rev()
            .find_map(|f| f.get(name).copied())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Context;

    #[test]
    fn let_shadowing_is_innermost_first() {
        let mut ctx = Context::new();
        let b = ctx.real_sort();
        let t1 = ctx.mk_numeral(shinri_core::Rational::one(), b);
        let t2 = ctx.mk_numeral(shinri_core::Rational::zero(), b);
        let mut env = Env::new();
        env.push_let(vec![("x".into(), t1)]);
        assert_eq!(env.lookup_let("x"), Some(t1));
        env.push_let(vec![("x".into(), t2)]);
        assert_eq!(env.lookup_let("x"), Some(t2)); // inner shadows outer
        env.pop_let();
        assert_eq!(env.lookup_let("x"), Some(t1));
    }
}
