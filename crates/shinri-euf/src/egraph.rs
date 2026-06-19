//! The congruence-closure machinery layered over `EqualityEngine`.

use rustc_hash::FxHashMap;
use shinri_core::{Op, TermId, TermNode};
use shinri_theory::types::ENodeId;
use shinri_theory::{EqualityEngine, TheoryCtx};

/// Index into `EGraph.apps`.
pub type AppId = u32;

/// A canonicalization key: operator + the representatives of the arguments.
type Signature = (Op, Vec<ENodeId>);

/// An entry in the congruence pending queue: (left node, right node, argument pairs).
type PendingEntry = (ENodeId, ENodeId, Vec<(ENodeId, ENodeId)>);

struct AppNode {
    node: ENodeId,
    op: Op,
    args: Vec<ENodeId>,
}

/// An undo entry for backtracking the EUF-owned indices.
#[allow(dead_code)] // variants exercised in Task 7
enum Undo {
    /// `lookup[sig]` was inserted with no prior value; remove it on undo.
    LookupInsert(Signature),
    /// `lookup[sig]` overwrote `prev`; restore `prev` on undo.
    LookupOverwrite(Signature, AppId),
    /// `count` apps were appended onto `use_list[winner]` from `loser`; move
    /// them back to `loser` on undo.
    UseSplice {
        winner: usize,
        loser: usize,
        count: usize,
    },
}

#[derive(Default)]
pub struct EGraph {
    apps: Vec<AppNode>,
    /// Per-ENodeId apps that use it directly as an argument (by original node id).
    use_list: Vec<Vec<AppId>>,
    lookup: FxHashMap<Signature, AppId>,
    /// Congruence work-queue: pairs of app nodes to merge, with arg pairs.
    pending: Vec<PendingEntry>,
    #[allow(dead_code)] // field exercised in Task 7
    undo: shinri_core::UndoLog<Undo>,
    /// Set when an interned term is a function application (vs a plain leaf).
    is_app: Vec<bool>,
    app_of: FxHashMap<ENodeId, AppId>,
}

impl EGraph {
    #[allow(dead_code)] // used in tests and will be used in Task 7 debugging
    pub fn app_count(&self) -> usize {
        self.apps.len()
    }

    fn ensure_node(&mut self, n: ENodeId) {
        let idx = n.index();
        if idx >= self.use_list.len() {
            self.use_list.resize_with(idx + 1, Vec::new);
        }
        if idx >= self.is_app.len() {
            self.is_app.resize(idx + 1, false);
        }
    }

    /// Recursively intern `t` and all subterms, recording app structure.
    /// Returns the e-node of `t`. Idempotent (interning dedups).
    pub fn add_term(&mut self, cx: &mut TheoryCtx, t: TermId) -> ENodeId {
        let node = cx.eq.intern(t);
        self.ensure_node(node);
        if self.app_of.contains_key(&node) {
            return node; // already registered as an app
        }
        // Note: Const nodes are intentionally not tracked in `app_of` (only App nodes are).
        // Re-visiting Const nodes is harmless and idempotent—interning dedups them.
        // Copy out op and args slice before releasing the borrow on cx.terms.
        let term_info = match cx.terms.term_node(t) {
            TermNode::App { op, args, .. } => Some((*op, *args)),
            TermNode::Const { .. } => None,
        };
        match term_info {
            Some((op, args_slice)) => {
                let child_terms: Vec<TermId> = cx.terms.children(args_slice).to_vec();
                let mut arg_nodes = Vec::with_capacity(child_terms.len());
                for ct in child_terms {
                    arg_nodes.push(self.add_term(cx, ct));
                }
                let app_id = self.apps.len() as AppId;
                for &an in &arg_nodes {
                    self.ensure_node(an);
                    self.use_list[an.index()].push(app_id);
                }
                self.apps.push(AppNode {
                    node,
                    op,
                    args: arg_nodes,
                });
                self.is_app[node.index()] = true;
                self.app_of.insert(node, app_id);
                // Initial signature; a collision means an existing congruent app.
                let sig = self.signature(cx.eq, app_id);
                if let Some(&other) = self.lookup.get(&sig) {
                    if other != app_id {
                        self.enqueue_congruence(cx.eq, other, app_id);
                    }
                } else {
                    self.lookup.insert(sig, app_id);
                }
                node
            }
            None => node,
        }
    }

    fn signature(&self, eq: &EqualityEngine, app: AppId) -> Signature {
        let a = &self.apps[app as usize];
        let reps: Vec<ENodeId> = a.args.iter().map(|&x| eq.find(x)).collect();
        (a.op, reps)
    }

    fn enqueue_congruence(&mut self, _eq: &EqualityEngine, a: AppId, b: AppId) {
        let aa = &self.apps[a as usize];
        let bb = &self.apps[b as usize];
        debug_assert_eq!(aa.args.len(), bb.args.len());
        let pairs: Vec<(ENodeId, ENodeId)> = aa
            .args
            .iter()
            .copied()
            .zip(bb.args.iter().copied())
            .collect();
        let node_a = aa.node;
        let node_b = bb.node;
        self.pending.push((node_a, node_b, pairs));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Context, Op};
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx};

    fn uconst(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> shinri_core::TermId {
        let sym = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn add_term_registers_apps_and_args() {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        let a = uconst(&mut ctx, "a", u);
        let b = uconst(&mut ctx, "b", u);
        let f = ctx.declare_fun("f", &[u], u);
        let fa = ctx.mk_app(Op::Uninterpreted(f), &[a]).unwrap();
        let fb = ctx.mk_app(Op::Uninterpreted(f), &[b]).unwrap();

        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut g = EGraph::default();
        {
            let mut cx = TheoryCtx {
                terms: &ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            g.add_term(&mut cx, fa);
            g.add_term(&mut cx, fb);
        }
        // f(a) and f(b) are distinct apps (a,b in different classes): no congruence.
        let na = eq.intern(fa);
        let nb = eq.intern(fb);
        assert!(!eq.are_equal(na, nb));
        assert_eq!(g.app_count(), 4); // a, b, f(a), f(b) all recorded as apps
    }
}
