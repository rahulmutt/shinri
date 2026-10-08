use rustc_hash::FxHashMap;
use shinri_core::{SortId, SymbolId, TermId};

/// A non-recursive define-fun macro: `body` was interned against `formals`
/// (fresh placeholder consts); expansion substitutes actual args for formals.
#[derive(Clone)]
pub struct Macro {
    pub formals: Vec<TermId>,
    pub body: TermId,
}

/// One entry of the push/pop undo log: the binding a scoped definition
/// replaced (`None` = the name was unbound).
enum Undo {
    Macro(String, Option<Macro>),
    Sort(String, Option<SortId>),
}

/// A run of `levels` consecutive push levels that all share the undo-log
/// length `mark` (no definition was made between them). Run-length encoding
/// keeps `(push 4294967295)` at O(1) memory: the parser's scope stack grows
/// with the number of push *commands*, never with their count argument.
struct ScopeRun {
    mark: usize,
    levels: u64,
}

/// Name resolution context. Lookup order at a head/leaf is enforced by the
/// parser (let → macro → fun → builtin); this type just stores the tables.
///
/// Definitions (`define-fun`, `:named`, `define-sort`) are scoped by
/// push/pop (SMT-LIB 2.6 §4.1.4): a definition made inside a push scope is
/// removed by the matching pop, restoring whatever it shadowed. Declarations
/// (`declare-fun`/`-const`/`-sort`/`-datatype(s)`) are NOT scoped, matching
/// the solver, whose declaration registry and hash-consed symbols also
/// survive a pop.
#[derive(Default)]
pub struct Env {
    sorts: FxHashMap<String, SortId>,
    funs: FxHashMap<String, SymbolId>,
    macros: FxHashMap<String, Macro>,
    /// Push/pop scope stack (run-length encoded) and the undo log its marks
    /// index. Definitions made at depth 0 are never logged: nothing can pop
    /// them, so a top-level script with ~10^5 define-funs costs no extra
    /// memory.
    scopes: Vec<ScopeRun>,
    undo: Vec<Undo>,
    let_frames: Vec<FxHashMap<String, TermId>>,
    /// Slice 64: set by `set-logic`. True for Reals-only logics, where an
    /// integer literal denotes a real (SMT-LIB 2.6 Reals theory). Lives here
    /// because `Env` is the state that persists across commands, on both the
    /// batch and the streaming path.
    numerals_are_real: bool,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }
    pub fn set_numerals_are_real(&mut self, on: bool) {
        self.numerals_are_real = on;
    }
    pub fn numerals_are_real(&self) -> bool {
        self.numerals_are_real
    }

    pub fn add_sort(&mut self, name: &str, s: SortId) {
        self.sorts.insert(name.to_owned(), s);
    }
    pub fn lookup_sort(&self, name: &str) -> Option<SortId> {
        self.sorts.get(name).copied()
    }
    /// Unbind a sort name. Used to unwind a rejected `declare-datatype(s)`.
    pub fn remove_sort(&mut self, name: &str) {
        self.sorts.remove(name);
    }

    pub fn add_fun(&mut self, name: &str, sym: SymbolId) {
        self.funs.insert(name.to_owned(), sym);
    }
    pub fn lookup_fun(&self, name: &str) -> Option<SymbolId> {
        self.funs.get(name).copied()
    }
    /// Unbind a function name. Used to unwind a rejected `declare-datatype(s)`.
    pub fn remove_fun(&mut self, name: &str) {
        self.funs.remove(name);
    }

    /// Bind a nullary sort alias (`define-sort`). Scoped by push/pop.
    pub fn add_sort_alias(&mut self, name: &str, s: SortId) {
        let old = self.sorts.insert(name.to_owned(), s);
        if !self.scopes.is_empty() {
            self.undo.push(Undo::Sort(name.to_owned(), old));
        }
    }

    /// Bind a macro (`define-fun` or `:named`). Scoped by push/pop.
    pub fn add_macro(&mut self, name: &str, formals: Vec<TermId>, body: TermId) {
        let old = self.macros.insert(name.to_owned(), Macro { formals, body });
        if !self.scopes.is_empty() {
            self.undo.push(Undo::Macro(name.to_owned(), old));
        }
    }
    pub fn lookup_macro(&self, name: &str) -> Option<&Macro> {
        self.macros.get(name)
    }

    /// `(push n)`: open `n` scope levels. O(1) time and memory in `n`.
    pub fn push_scopes(&mut self, n: u32) {
        if n == 0 {
            return;
        }
        let mark = self.undo.len();
        match self.scopes.last_mut() {
            // No definition since the last push: extend that run.
            Some(run) if run.mark == mark => run.levels = run.levels.saturating_add(u64::from(n)),
            _ => self.scopes.push(ScopeRun {
                mark,
                levels: u64::from(n),
            }),
        }
    }

    /// `(pop n)`: close `n` scope levels, removing every definition made in
    /// them. Popping more levels than are open closes all of them and is
    /// otherwise a no-op — the solver treats over-pop the same way. Time is
    /// O(definitions undone + runs closed), never O(n).
    pub fn pop_scopes(&mut self, n: u32) {
        let mut n = u64::from(n);
        while n > 0 {
            let Some(run) = self.scopes.last_mut() else {
                return;
            };
            let take = n.min(run.levels);
            run.levels -= take;
            n -= take;
            // Every level of a run shares `mark`, and the log entries past it
            // belong to the run's innermost level, so popping any number of
            // the run's levels unwinds to `mark`.
            let mark = run.mark;
            if run.levels == 0 {
                self.scopes.pop();
            }
            self.unwind_to(mark);
        }
    }

    /// `(reset)`: forget the scope stack (the solver clears its own).
    pub fn reset_scopes(&mut self) {
        self.scopes.clear();
        self.undo.clear();
    }

    fn unwind_to(&mut self, mark: usize) {
        while self.undo.len() > mark {
            match self.undo.pop() {
                Some(Undo::Macro(name, Some(m))) => {
                    self.macros.insert(name, m);
                }
                Some(Undo::Macro(name, None)) => {
                    self.macros.remove(&name);
                }
                Some(Undo::Sort(name, Some(s))) => {
                    self.sorts.insert(name, s);
                }
                Some(Undo::Sort(name, None)) => {
                    self.sorts.remove(&name);
                }
                None => break,
            }
        }
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
