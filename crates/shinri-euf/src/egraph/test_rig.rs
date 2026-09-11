//! Test-only harness and index-invariant checker for `EGraph` (slice 49,
//! spec §4.1). A child module of `egraph`, so it reads private fields.

use super::{AppId, EGraph};
use rustc_hash::FxHashMap;
use shinri_core::{Context, Lit, Op, SortId, SymbolId, TermId, Var};
use shinri_theory::types::{ENodeId, EqJust, EqLeaf};
use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx};

impl EGraph {
    /// Spec §4.1. `Ok` iff, for every indexed app:
    ///
    /// * (I-use) it sits on the use-list of each argument's CURRENT
    ///   representative, exactly as often as that representative occurs among
    ///   its argument representatives, and on no other use-list;
    /// * (I-lookup) `lookup` holds its current signature, naming either the
    ///   app itself or an app in the same class or linked to it through live,
    ///   non-stale `pending` entries.
    ///
    /// Not meaningful between a returned conflict and the `pop` that follows
    /// it: a conflict can consume a `pending` entry whose merge never happened.
    pub(crate) fn check_index(&self, eq: &EqualityEngine) -> Result<(), String> {
        let mut on_lists: FxHashMap<AppId, Vec<usize>> = FxHashMap::default();
        for (idx, list) in self.use_list.iter().enumerate() {
            for &app in list {
                on_lists.entry(app).or_default().push(idx);
            }
        }

        // Classes, plus the links that live, non-stale pending congruences add.
        let mut link: FxHashMap<ENodeId, ENodeId> = FxHashMap::default();
        fn root(link: &FxHashMap<ENodeId, ENodeId>, mut x: ENodeId) -> ENodeId {
            while let Some(&p) = link.get(&x) {
                x = p;
            }
            x
        }
        for (na, nb, pairs) in &self.pending {
            if pairs.iter().all(|&(pa, pb)| eq.find(pa) == eq.find(pb)) {
                let ra = root(&link, eq.find(*na));
                let rb = root(&link, eq.find(*nb));
                if ra != rb {
                    link.insert(ra, rb);
                }
            }
        }
        let linked = |a: ENodeId, b: ENodeId| root(&link, eq.find(a)) == root(&link, eq.find(b));

        for (i, a) in self.apps.iter().enumerate() {
            let app = i as AppId;
            let mut want: Vec<usize> = a.args.iter().map(|&x| eq.find(x).index()).collect();
            want.sort_unstable();
            let mut have = on_lists.get(&app).cloned().unwrap_or_default();
            have.sort_unstable();
            if want != have {
                return Err(format!(
                    "(I-use) app {app} (op {:?}): argument representatives {want:?} but on use-lists {have:?}",
                    a.op
                ));
            }
            let sig = self.signature(eq, app);
            match self.lookup.get(&sig) {
                None => {
                    return Err(format!(
                        "(I-lookup) app {app} (op {:?}): current signature {sig:?} is missing from lookup",
                        a.op
                    ))
                }
                Some(&other) if other != app && !linked(a.node, self.apps[other as usize].node) => {
                    return Err(format!(
                        "(I-lookup) app {app}: lookup[{sig:?}] = app {other}, which is neither in its class nor pending-linked"
                    ))
                }
                Some(_) => {}
            }
        }
        Ok(())
    }
}

/// A scratch EUF world: one uninterpreted sort `U`, a shared equality engine,
/// an `EGraph`, and push/pop in the combiner's order (engine first, then the
/// EGraph — `combiner.rs:500-501`).
pub(crate) struct Rig {
    pub(crate) ctx: Context,
    pub(crate) eq: EqualityEngine,
    pub(crate) atoms: AtomRegistry,
    pub(crate) g: EGraph,
    u: SortId,
    next_lit: u32,
}

impl Rig {
    pub(crate) fn new() -> Rig {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        Rig {
            ctx,
            eq: EqualityEngine::default(),
            atoms: AtomRegistry::default(),
            g: EGraph::default(),
            u,
            next_lit: 1,
        }
    }

    pub(crate) fn konst(&mut self, name: &str) -> TermId {
        let s = self.ctx.declare_fun(name, &[], self.u);
        self.ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    pub(crate) fn fun(&mut self, name: &str, arity: usize) -> SymbolId {
        let params = vec![self.u; arity];
        self.ctx.declare_fun(name, &params, self.u)
    }

    pub(crate) fn app(&mut self, f: SymbolId, args: &[TermId]) -> TermId {
        self.ctx.mk_app(Op::Uninterpreted(f), args).unwrap()
    }

    /// Register `t` and its subterms with the EGraph at the current level.
    pub(crate) fn add(&mut self, t: TermId) {
        let mut cx = TheoryCtx {
            terms: &mut self.ctx,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        self.g.add_term(&mut cx, t);
    }

    fn just(&mut self) -> EqJust {
        let l = Lit::new(Var::new(self.next_lit), true);
        self.next_lit += 1;
        EqJust::Asserted(l)
    }

    /// `merge_eq(a, b)`, then empty the engine's merge-event queue so a later
    /// `pop` is legal (`EqualityEngine::pop` asserts it is drained).
    pub(crate) fn merge(&mut self, a: TermId, b: TermId) -> Option<Vec<EqLeaf>> {
        let (na, nb) = (self.eq.intern(a), self.eq.intern(b));
        let j = self.just();
        let r = self.g.merge_eq(&mut self.eq, na, nb, j);
        self.eq.drain_merges(&mut Vec::new());
        r
    }

    pub(crate) fn push(&mut self) {
        self.eq.push();
        self.g.push();
    }

    pub(crate) fn pop(&mut self, level: usize) {
        self.eq.drain_merges(&mut Vec::new());
        self.eq.pop(level);
        self.g.pop(level);
    }

    pub(crate) fn equal(&mut self, a: TermId, b: TermId) -> bool {
        let (na, nb) = (self.eq.intern(a), self.eq.intern(b));
        self.eq.are_equal(na, nb)
    }

    pub(crate) fn assert_index(&self) {
        if let Err(e) = self.g.check_index(&self.eq) {
            panic!("index invariant violated: {e}");
        }
    }
}
