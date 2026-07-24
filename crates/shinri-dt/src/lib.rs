//! QF_DT datatype theory: lemma-on-demand over the shared EqualityEngine.
//! Owns no equality state; emits datatype axiom instances as positive-atom
//! clauses via `TCheck::Split` and clashes via `TCheck::Conflict`.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{Context, DtRole, Lit, Op, SymbolId, TermId, TermNode, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::ENodeId;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

/// Datatype theory solver. Holds no union-find: all equality state lives in the
/// shared `EqualityEngine`, and every derived fact is emitted as a lemma or a
/// conflict. Watch sets are monotone (assignment-independent), so `push`/`pop`
/// are no-ops — the `shinri-arrays` pattern.
#[derive(Default)]
pub struct DtSolver {
    /// Constructor applications `C(a1..an)` seen in registered atoms.
    ctor_apps: FxHashSet<TermId>,
    /// Selector applications `sel(t)`.
    sel_apps: FxHashSet<TermId>,
    /// Tester applications `is-C(t)`.
    testers: FxHashSet<TermId>,
    /// Every term (of any role) whose sort is a datatype sort — the superset
    /// Task 8's completeness fence needs, not just selector/tester arguments.
    dt_terms: FxHashSet<TermId>,
    /// Lemmas already emitted, so `check` reaches a fixpoint instead of
    /// re-emitting the same tautology forever.
    emitted: FxHashSet<TermId>,
    /// Slice 40: watched terms whose exhaustiveness disjunction has already
    /// been emitted, so `check` reaches a fixpoint instead of re-offering the
    /// same split. Monotone — the `emitted`/watch-set discipline of slice 39.
    split_done: FxHashSet<TermId>,
    /// Slice 40: tester atoms asserted true — the trigger set for
    /// `instantiate_constructor`. Monotone (never popped): a stale entry from a
    /// backtracked branch only re-emits a GUARDED (hence inert) lemma, never an
    /// unsound one, so retraction is unnecessary and `push`/`pop` stay no-ops.
    /// Populated by `assert`; consumed by `instantiate_constructor`.
    asserted_testers: FxHashSet<TermId>,
    /// Test-only instrumentation: total `collect` invocations (including
    /// early returns on an already-seen term), so a test can pin that the
    /// `seen` guard keeps the walk linear in DAG size instead of exponential
    /// in sharing depth.
    #[cfg(test)]
    collect_calls: u32,
}

impl DtSolver {
    /// Walk an atom's term DAG, indexing every datatype-relevant application
    /// and every datatype-sorted term. `seen` guards against re-walking a
    /// shared subterm reachable via multiple paths — mirroring
    /// `shinri-str::collect::collect` (`crates/shinri-str/src/collect.rs`),
    /// not `shinri-arrays::collect` (which has no such guard). Datatype terms
    /// are the one domain here where deep, naturally-recursive, heavily-shared
    /// structure is the norm (nested lists/trees, `let`-shared subtrees), so
    /// an unmemoized walk is exponential in sharing depth rather than linear
    /// in DAG size.
    fn collect(&mut self, terms: &Context, t: TermId, seen: &mut FxHashSet<TermId>) {
        #[cfg(test)]
        {
            self.collect_calls += 1;
        }
        if !seen.insert(t) {
            return;
        }
        if terms.is_datatype_sort(terms.sort_of(t)) {
            self.dt_terms.insert(t);
        }
        let (op, kids) = match terms.term_node(t) {
            TermNode::App { op, args, .. } => (*op, terms.children(*args).to_vec()),
            TermNode::Const { .. } => return,
        };
        if let Op::Uninterpreted(sym) = op {
            match terms.dt_role(sym) {
                Some(DtRole::Constructor { .. }) => {
                    self.ctor_apps.insert(t);
                }
                Some(DtRole::Selector { .. }) => {
                    self.sel_apps.insert(t);
                }
                Some(DtRole::Tester { .. }) => {
                    self.testers.insert(t);
                }
                None => {}
            }
        }
        for k in kids {
            self.collect(terms, k, seen);
        }
    }

    /// `(symbol, children)` of an uninterpreted application, or `None`.
    fn uapp(terms: &Context, t: TermId) -> Option<(SymbolId, Vec<TermId>)> {
        match terms.term_node(t) {
            TermNode::App {
                op: Op::Uninterpreted(s),
                args,
                ..
            } => Some((*s, terms.children(*args).to_vec())),
            _ => None,
        }
    }

    /// Selector-collapse: for `sel_i(t)` and a constructor app `C(a1..an)` in
    /// the same class as `t`, emit the TAUTOLOGY `sel_i(C(a1..an)) = a_i`.
    ///
    /// Written over the constructor application itself the lemma is
    /// unconditional — congruence supplies `sel_i(t) ≡ sel_i(C(a..))` — so no
    /// guard is needed. Fires only when `sel_i` belongs to `C`: for a foreign
    /// selector SMT-LIB leaves the value unspecified and collapsing is unsound.
    fn collapse_lemma(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        let sels: Vec<TermId> = self.sel_apps.iter().copied().collect();
        let ctors: Vec<TermId> = self.ctor_apps.iter().copied().collect();
        for sel in sels {
            let Some((sel_sym, sel_args)) = Self::uapp(cx.terms, sel) else {
                continue;
            };
            let Some(DtRole::Selector { ctor, index }) = cx.terms.dt_role(sel_sym) else {
                continue;
            };
            let Some(&t) = sel_args.first() else {
                continue;
            };
            let tn = cx.eq.intern(t);
            for &capp in &ctors {
                let Some((csym, cargs)) = Self::uapp(cx.terms, capp) else {
                    continue;
                };
                // Foreign selector: value unspecified, no lemma.
                if csym != ctor {
                    continue;
                }
                let cn = cx.eq.intern(capp);
                if !cx.eq.are_equal(tn, cn) {
                    continue;
                }
                let Some(&arg) = cargs.get(index as usize) else {
                    continue;
                };
                let sel_on_ctor = cx
                    .terms
                    .mk_app(Op::Uninterpreted(sel_sym), &[capp])
                    .expect("selector applies to its own datatype sort");
                let sn = cx.eq.intern(sel_on_ctor);
                let an = cx.eq.intern(arg);
                if cx.eq.are_equal(sn, an) {
                    continue; // already installed — fixpoint
                }
                let lemma = cx
                    .terms
                    .mk_eq(sel_on_ctor, arg)
                    .expect("selector result sort matches the field sort");
                if !self.emitted.insert(lemma) {
                    // Unreachable while unit splits are level-0 pinned (shinri-sat
                    // solver.rs backtracks and pins guard-free unit SplitAtoms). If
                    // installation is ever deferred, exhausting `emitted` makes
                    // `check` return Sat with the fact uninstalled — a spurious-SAT
                    // hazard, not merely a duplicate clause.
                    continue;
                }
                return Some(TCheck::Split {
                    atoms: vec![lemma],
                    guard: None,
                    phases: Vec::new(),
                });
            }
        }
        None
    }

    /// Injectivity, via ON-DEMAND SELECTOR INSTANTIATION. Two SAME-constructor
    /// applications `p = C(a1..an)` and `q = C(b1..bn)` in one class entail
    /// `a_i = b_i` for every field (constructor injectivity) — the pair
    /// `constructor_clash` deliberately skips. Rather than emit that consequence
    /// directly (it is CONDITIONAL on `p ≡ q`, which may hold only on the current
    /// branch, so pinning it as a guard-free level-0 unit would be a wrong-UNSAT
    /// hazard — the same trap `tester_lemma` was fixed for), instantiate the
    /// selector applications `sel_i(p)` and `sel_i(q)` and register them as
    /// watched selector apps.
    ///
    /// The existing, already-proven machinery then closes the loop, and every
    /// fact it pins is unconditional:
    ///   - `collapse_lemma` emits the TAUTOLOGIES `sel_i(p) = a_i` and
    ///     `sel_i(q) = b_i` (the selector axiom, guard-free, sound to pin — Task
    ///     6). Registering those split atoms adds `sel_i(p)`/`sel_i(q)` to EUF's
    ///     egraph (Combiner routes DT atoms to BOTH EUF and DT).
    ///   - EUF congruence over `p ≡ q` derives `sel_i(p) ≡ sel_i(q)`.
    ///   - Transitivity `a_i ≡ sel_i(p) ≡ sel_i(q) ≡ b_i` yields `a_i ≡ b_i`
    ///     INSIDE EUF — so it is retracted automatically when the `p ≡ q` merge
    ///     is retracted on backtrack. No conditional fact is ever level-0 pinned.
    ///
    /// This mutates watch state and returns nothing; `check` falls through to
    /// `collapse_lemma` in the same call to emit the tautologies. Idempotent:
    /// `sel_apps` is a set, so re-running at fixpoint adds nothing.
    fn instantiate_injectivity_selectors(&mut self, cx: &mut TheoryCtx) {
        let ctors: Vec<TermId> = self.ctor_apps.iter().copied().collect();
        for (i, &p) in ctors.iter().enumerate() {
            let Some((psym, _)) = Self::uapp(cx.terms, p) else {
                continue;
            };
            let pn = cx.eq.intern(p);
            let Some(rest) = ctors.get(i + 1..) else {
                continue;
            };
            for &q in rest {
                let Some((qsym, _)) = Self::uapp(cx.terms, q) else {
                    continue;
                };
                // Different constructors in one class are a clash, not
                // injectivity — `constructor_clash` owns that case.
                if psym != qsym {
                    continue;
                }
                let qn = cx.eq.intern(q);
                if !cx.eq.are_equal(pn, qn) {
                    continue;
                }
                // Same constructor, same class: instantiate every field
                // selector on BOTH applications. `collapse_lemma` + congruence
                // then surface `a_i = b_i`.
                // Own the selector list so the immutable borrow of `cx.terms`
                // is released before the `mk_app` mutable borrow below.
                let Some(sels) = cx.terms.dt_selectors(psym).map(<[SymbolId]>::to_vec) else {
                    continue;
                };
                for sel in sels {
                    for capp in [p, q] {
                        let app = cx
                            .terms
                            .mk_app(Op::Uninterpreted(sel), &[capp])
                            .expect("selector applies to its own datatype sort");
                        self.sel_apps.insert(app);
                        // Mirror `collect`: a datatype-sorted selector app is
                        // also a watched dt_term. (Its class always joins an
                        // existing field's — collapse merges `sel_i(p) = a_i` —
                        // so this adds no NEW constructor-undetermined class the
                        // fence could trip on.)
                        if cx.terms.is_datatype_sort(cx.terms.sort_of(app)) {
                            self.dt_terms.insert(app);
                        }
                    }
                }
            }
        }
    }

    /// Two DISTINCT constructor applications in one class are contradictory.
    /// The explanation is the merge path that made them equal.
    fn constructor_clash(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        let ctors: Vec<TermId> = self.ctor_apps.iter().copied().collect();
        for (i, &p) in ctors.iter().enumerate() {
            let Some((psym, _)) = Self::uapp(cx.terms, p) else {
                continue;
            };
            let pn = cx.eq.intern(p);
            let Some(rest) = ctors.get(i + 1..) else {
                continue;
            };
            for &q in rest {
                let Some((qsym, _)) = Self::uapp(cx.terms, q) else {
                    continue;
                };
                if psym == qsym {
                    continue;
                }
                let qn = cx.eq.intern(q);
                if !cx.eq.are_equal(pn, qn) {
                    continue;
                }
                let mut leaves = Vec::new();
                cx.eq.explain(pn, qn, &mut leaves);
                return Some(TCheck::Conflict(leaves));
            }
        }
        None
    }

    /// `is-C(t)` where `t`'s class holds `C(a1..an)` is a valid UNIT tautology
    /// — but ONLY when written over the constructor application itself, the
    /// same rewrite `collapse_lemma` performs. `t ≡ C(..)` may hold only on
    /// the current decision branch, so `is-C(t)` is at most conditionally
    /// true; `is-C(C(..))`, in contrast, is true by construction regardless
    /// of assignment, so it can ride a guard-free unit `Split`. Congruence
    /// then supplies `is-C(t) ≡ is-C(C(..))` on exactly the branches where
    /// `t ≡ C(..)` holds. Emitting `is-C(t)` directly here would launder a
    /// conditional fact into a permanent level-0 one (the SAT layer pins a
    /// guard-free unit `Split` at level 0) — a wrong-UNSAT hazard.
    /// (The negative direction `¬is-D(t)` cannot ride `Split`, whose atoms are
    /// positive; it is handled at assert time instead — see `assert`.)
    fn tester_lemma(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        let testers: Vec<TermId> = self.testers.iter().copied().collect();
        let ctors: Vec<TermId> = self.ctor_apps.iter().copied().collect();
        for tst in testers {
            let Some((tsym, targs)) = Self::uapp(cx.terms, tst) else {
                continue;
            };
            let Some(DtRole::Tester { ctor }) = cx.terms.dt_role(tsym) else {
                continue;
            };
            let Some(&t) = targs.first() else {
                continue;
            };
            let tn = cx.eq.intern(t);
            for &capp in &ctors {
                let Some((csym, _)) = Self::uapp(cx.terms, capp) else {
                    continue;
                };
                if csym != ctor {
                    continue;
                }
                let cn = cx.eq.intern(capp);
                if !cx.eq.are_equal(tn, cn) {
                    continue;
                }
                let is_c_on_ctor = cx
                    .terms
                    .mk_app(Op::Uninterpreted(tsym), &[capp])
                    .expect("tester applies to its own datatype sort");
                if !self.emitted.insert(is_c_on_ctor) {
                    continue;
                }
                return Some(TCheck::Split {
                    atoms: vec![is_c_on_ctor],
                    guard: None,
                    phases: Vec::new(),
                });
            }
        }
        None
    }

    /// Exhaustiveness (slice 40): a watched datatype class with no constructor
    /// application IS some constructor — offer the tester disjunction
    /// `is-C1(t) ∨ … ∨ is-Cn(t)`. Guard-free: it is a T-tautology whose
    /// at-most-one companion is the assert-time tester disjointness (slice 39).
    /// Deduped per watched term. Nullary constructors get a `Some(true)` phase
    /// preference so the SAT search tries finite models first, which bounds the
    /// instantiation descent on recursive types.
    fn exhaustiveness_split(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        for t in self.watched_dt_terms() {
            if self.ctor_of_class(cx, t).is_some() {
                continue; // already constructor-determined
            }
            if !self.split_done.insert(t) {
                continue; // disjunction already offered for this term
            }
            let sort = cx.terms.sort_of(t);
            let Some(ctors) = cx.terms.dt_constructors(sort).map(<[SymbolId]>::to_vec) else {
                continue;
            };
            let mut atoms = Vec::with_capacity(ctors.len());
            let mut phases = Vec::with_capacity(ctors.len());
            for c in ctors {
                let Some(tester) = cx.terms.dt_tester(c) else {
                    continue;
                };
                let is_c_t = cx
                    .terms
                    .mk_app(Op::Uninterpreted(tester), &[t])
                    .expect("tester applies to its own datatype sort");
                let nullary = cx.terms.dt_selectors(c).is_none_or(<[SymbolId]>::is_empty);
                atoms.push(is_c_t);
                phases.push(if nullary { Some(true) } else { None });
            }
            if atoms.is_empty() {
                continue;
            }
            return Some(TCheck::Split {
                atoms,
                guard: None,
                phases,
            });
        }
        None
    }

    /// Constructor instantiation (slice 40): for a tester `is-C(t)` asserted
    /// true whose class holds no constructor application, offer the guarded
    /// definitional lemma  `is-C(t) ⇒ t = C(sel1(t), …, seln(t))`. The guard
    /// `¬is-C(t)` keeps the pinned clause a permanent tautology (sound at
    /// level 0); EUF installs the equality on exactly the branches where
    /// `is-C(t)` holds and retracts it on backtrack. The minted field selectors
    /// are watched, so `collapse_lemma` fires on the new constructor app and any
    /// datatype-sorted field recurses through its own exhaustiveness split —
    /// the lazy descent that terminates recursive types. Gating on ASSERTED
    /// testers (not all watched testers) is the laziness lever: only the
    /// branch's chosen constructor is ever instantiated.
    fn instantiate_constructor(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        let asserted: Vec<TermId> = self.asserted_testers.iter().copied().collect();
        for tst in asserted {
            let Some((tsym, targs)) = Self::uapp(cx.terms, tst) else {
                continue;
            };
            let Some(DtRole::Tester { ctor }) = cx.terms.dt_role(tsym) else {
                continue;
            };
            let Some(&t) = targs.first() else {
                continue;
            };
            if self.ctor_of_class(cx, t).is_some() {
                continue; // class already has a constructor app
            }
            let Some(sels) = cx.terms.dt_selectors(ctor).map(<[SymbolId]>::to_vec) else {
                continue;
            };
            // Mint the field selectors on `t` and the constructor app.
            let mut fields = Vec::with_capacity(sels.len());
            for sel in &sels {
                let app = cx
                    .terms
                    .mk_app(Op::Uninterpreted(*sel), &[t])
                    .expect("selector applies to its own datatype sort");
                self.sel_apps.insert(app);
                if cx.terms.is_datatype_sort(cx.terms.sort_of(app)) {
                    self.dt_terms.insert(app);
                }
                fields.push(app);
            }
            let capp = cx
                .terms
                .mk_app(Op::Uninterpreted(ctor), &fields)
                .expect("constructor applies to its own field sorts");
            self.ctor_apps.insert(capp);
            if cx.terms.is_datatype_sort(cx.terms.sort_of(capp)) {
                self.dt_terms.insert(capp);
            }
            let lemma = cx
                .terms
                .mk_eq(t, capp)
                .expect("t and C(sel(t)…) share the datatype sort");
            // Guard by ¬is-C(t). An asserted tester always has a SAT var; the
            // `else { continue; }` is defensive and simply skips to the next
            // asserted tester rather than abandoning the whole loop if not.
            let Some(var) = cx.atoms.var_of_atom(tst) else {
                continue;
            };
            if !self.emitted.insert(lemma) {
                continue; // already offered on this branch
            }
            return Some(TCheck::Split {
                atoms: vec![lemma],
                guard: Some(Lit::new(var, true).negate()),
                phases: Vec::new(),
            });
        }
        None
    }

    /// The constructor application in `t`'s class, if any: `(symbol, app)`.
    fn ctor_of_class(&self, cx: &mut TheoryCtx, t: TermId) -> Option<(SymbolId, TermId)> {
        let tn = cx.eq.intern(t);
        for &capp in &self.ctor_apps {
            let Some((csym, _)) = Self::uapp(cx.terms, capp) else {
                continue;
            };
            let cn = cx.eq.intern(capp);
            if cx.eq.are_equal(tn, cn) {
                return Some((csym, capp));
            }
        }
        None
    }

    /// For the first registered constructor application in class `rep`, return
    /// `(capp, edges)` where `edges` lists, per datatype-sorted field, the pair
    /// `(field_term, child_class_rep)`. `None` when the class holds no
    /// constructor app (undetermined / leaf). The field `TermId` and `capp`
    /// `TermId` are retained (not reduced to reps) so the acyclicity conflict can
    /// cite the merge-equality `field = next_capp` along each cycle edge.
    fn children_of(
        &self,
        cx: &mut TheoryCtx,
        rep: ENodeId,
    ) -> Option<(TermId, Vec<(TermId, ENodeId)>)> {
        for &capp in &self.ctor_apps {
            let capp_n = cx.eq.intern(capp);
            if cx.eq.find(capp_n) != rep {
                continue;
            }
            let (_, cargs) = Self::uapp(cx.terms, capp)?;
            let kids = cargs
                .iter()
                .copied()
                .filter(|&a| cx.terms.is_datatype_sort(cx.terms.sort_of(a)))
                .map(|a| {
                    let an = cx.eq.intern(a);
                    (a, cx.eq.find(an))
                })
                .collect();
            return Some((capp, kids));
        }
        None
    }

    /// The ordered cycle in the constructor graph over the currently determined
    /// classes, or `None` if it is acyclic. Each edge is `(field_term,
    /// next_capp)`: the datatype-sorted field of one constructor application, and
    /// the constructor application sitting in the class that field points to. A
    /// cycle means the only ground model is an infinite term, so no finite model
    /// exists on this branch: slice 40 answers `Unknown` here (the residual
    /// fence), and slice 41 turns the same detection into a proven `unsat` (the
    /// caller builds the conflict). Iterative (explicit DFS stack), never
    /// recursive: the term graph comes from untrusted input and may be
    /// arbitrarily deep (threat model), matching `dt_first_ill_founded`.
    fn constructor_graph_find_cycle(&self, cx: &mut TheoryCtx) -> Option<Vec<(TermId, TermId)>> {
        struct Frame {
            rep: ENodeId,
            capp: TermId,
            via_field: Option<TermId>, // field of the parent's capp that reached this frame
            kids: Vec<(TermId, ENodeId)>,
        }
        let mut done: FxHashSet<ENodeId> = FxHashSet::default();
        for t in self.watched_dt_terms() {
            let tn = cx.eq.intern(t);
            let root = cx.eq.find(tn);
            if done.contains(&root) {
                continue;
            }
            let Some((capp, kids)) = self.children_of(cx, root) else {
                done.insert(root);
                continue;
            };
            // grey rep -> its index in `stack`, for O(1) back-edge / cycle slicing.
            let mut on_path: FxHashMap<ENodeId, usize> = FxHashMap::default();
            on_path.insert(root, 0);
            let mut stack: Vec<Frame> = vec![Frame {
                rep: root,
                capp,
                via_field: None,
                kids,
            }];
            while let Some(top) = stack.last_mut() {
                let Some((field, child)) = top.kids.pop() else {
                    let f = stack.pop().unwrap();
                    on_path.remove(&f.rep);
                    done.insert(f.rep);
                    continue;
                };
                if let Some(&i) = on_path.get(&child) {
                    // Back-edge: build the cycle stack[i..] plus the closing edge.
                    let mut edges: Vec<(TermId, TermId)> = Vec::new();
                    edges.push((field, stack[i].capp)); // closing: top's field -> child's capp
                    for f in &stack[i + 1..] {
                        edges.push((f.via_field.expect("non-root frame has a via_field"), f.capp));
                    }
                    return Some(edges);
                }
                if done.contains(&child) {
                    continue;
                }
                let Some((ccapp, ckids)) = self.children_of(cx, child) else {
                    done.insert(child);
                    continue;
                };
                on_path.insert(child, stack.len());
                stack.push(Frame {
                    rep: child,
                    capp: ccapp,
                    via_field: Some(field),
                    kids: ckids,
                });
            }
        }
        None
    }

    /// Every datatype-sorted term this theory watches. `dt_terms` (populated
    /// by `collect`, Task 5) is already the full set — every term reachable
    /// while walking a registered atom's DAG whose sort is a datatype sort.
    /// Selector and tester arguments are datatype-sorted themselves, so
    /// `collect`'s unconditional recursion into every child already puts them
    /// in `dt_terms` too (see `new_var_indexes_constructor_selector_and_tester_apps`,
    /// which pins `watches_dt_term(x)` where `x` is both a selector and a
    /// tester argument). There is nothing left to add on top of `dt_terms`.
    fn watched_dt_terms(&self) -> Vec<TermId> {
        self.dt_terms.iter().copied().collect()
    }

    /// True iff some watched datatype term's class has no constructor
    /// application in it — the class is not (yet) constructor-determined.
    /// Spec §5.2: the completeness fence in `check` uses this to keep a
    /// possibly-wrong `Sat` from ever being reported. By the time `check`
    /// reaches this call, `exhaustiveness_split` and `instantiate_constructor`
    /// have already been offered to a fixpoint (slice 40's active case split),
    /// so a `true` here means a class survived that splitting on this branch —
    /// not that the split is unimplemented — and the fence defensively falls
    /// back to `Unknown` rather than `Sat`.
    fn has_undetermined_class(&self, cx: &mut TheoryCtx) -> bool {
        for t in self.watched_dt_terms() {
            if self.ctor_of_class(cx, t).is_some() {
                continue;
            }
            return true;
        }
        false
    }

    /// Render the ground constructor term for `t`'s class as an SMT-LIB string
    /// (e.g. `nil`, `(cons 1 nil)`), or `None` when the class is not
    /// constructor-determined, a cycle is hit, or the overflow backstop trips.
    /// `visited` holds the class reps on the current path: a repeat is a cycle
    /// (no finite ground term), while a rep is removed on the way back up so a
    /// DAG-shared subterm still renders under sibling branches. The visited-set
    /// is the real cycle guard (the principled §5.C occurs-check) and is
    /// unreachable with a cycle once `check` has returned `Sat` — the fence
    /// rejects cyclic states first — but it is kept as fail-safe defense in
    /// depth. `depth` is a SEPARATE, purely mechanical overflow backstop: a
    /// determined, ACYCLIC chain of datatype constructors (e.g. `N` asserts
    /// `x_i = cons(1, x_{i+1})`, ..., `x_{N-1} = nil`) is all distinct
    /// e-classes, so the visited-set never trips, yet the recursion is still
    /// `N` deep. On untrusted `declare-datatypes`/assert input (threat model)
    /// `N` is attacker-controlled, so without a depth cap this recurses without
    /// bound and can stack-overflow. `depth > 10_000` is comfortably above any
    /// realistic model depth and exists ONLY to bound worst-case recursion —
    /// it does not detect cycles and must not be read as doing so.
    fn render_value(
        &self,
        cx: &mut TheoryCtx,
        t: TermId,
        visited: &mut FxHashSet<ENodeId>,
        depth: u32,
    ) -> Option<String> {
        if depth > 10_000 {
            return None; // overflow backstop, not a cycle detector
        }
        let tn = cx.eq.intern(t);
        let rep = cx.eq.find(tn);
        if !visited.insert(rep) {
            return None; // cycle
        }
        let rendered = self.render_value_inner(cx, t, visited, depth);
        visited.remove(&rep);
        rendered
    }

    fn render_value_inner(
        &self,
        cx: &mut TheoryCtx,
        t: TermId,
        visited: &mut FxHashSet<ENodeId>,
        depth: u32,
    ) -> Option<String> {
        let (csym, capp) = self.ctor_of_class(cx, t)?;
        let (_, cargs) = Self::uapp(cx.terms, capp)?;
        let name = cx.terms.symbol_name(csym).to_string();
        if cargs.is_empty() {
            return Some(name);
        }
        // A field failing to render means the whole ground term cannot be
        // rendered either — there is no valid partial result to fall back
        // to. The house style's loop `continue` idiom doesn't apply here:
        // these iterations are not independent candidates where skipping one
        // and trying the next is meaningful, they are mandatory positions in
        // one ground term, so dropping a field would silently print a
        // malformed term rather than a correct partial one. `collect`ing
        // into `Option<Vec<_>>` expresses "abort on the first failure"
        // without a manual `for` loop containing an early `return`/`?`.
        let parts: Option<Vec<String>> = cargs
            .iter()
            .map(|&a| {
                if cx.terms.is_datatype_sort(cx.terms.sort_of(a)) {
                    self.render_value(cx, a, visited, depth + 1)
                } else {
                    // Non-datatype fields are owned by other theories, which
                    // this solver has no visibility into. Render a plain
                    // nullary constant by its symbol name; anything else is
                    // unsupported here (fields of non-nullary, non-datatype
                    // shape are not exercised by slice 39 and are left for
                    // the combined model to fill in).
                    match Self::uapp(cx.terms, a) {
                        Some((s, kids)) if kids.is_empty() => {
                            Some(cx.terms.symbol_name(s).to_string())
                        }
                        _ => Some("?".to_string()),
                    }
                }
            })
            .collect();
        Some(format!("({} {})", name, parts?.join(" ")))
    }

    #[cfg(test)]
    pub(crate) fn watches_ctor(&self, t: TermId) -> bool {
        self.ctor_apps.contains(&t)
    }
    #[cfg(test)]
    pub(crate) fn watches_sel(&self, t: TermId) -> bool {
        self.sel_apps.contains(&t)
    }
    #[cfg(test)]
    pub(crate) fn watches_tester(&self, t: TermId) -> bool {
        self.testers.contains(&t)
    }
    #[cfg(test)]
    pub(crate) fn watches_dt_term(&self, t: TermId) -> bool {
        self.dt_terms.contains(&t)
    }
    #[cfg(test)]
    pub(crate) fn collect_calls(&self) -> u32 {
        self.collect_calls
    }
}

impl TheorySolver for DtSolver {
    const THEORY_ID: u16 = 5;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        let mut seen = FxHashSet::default();
        self.collect(cx.terms, atom, &mut seen);
    }

    /// Tester disjointness: an asserted `is-D(t)` whose class already holds a
    /// `C(..)` with `C != D` is an immediate conflict. Handled here rather
    /// than in `check` because the consequence `¬is-D(t)` is a NEGATIVE
    /// literal and `TCheck::Split` carries only positive atoms.
    ///
    /// `assert` is straight-line, not a loop, so the loop-abandonment hazard
    /// the file's `let..else { continue; }` house style guards against does
    /// not apply here: `?` on each bailout below is exactly the intended
    /// early-return behavior, so it is used directly (unlike the `continue`
    /// idiom used inside the `for` loops elsewhere in this file).
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        if !lit.is_positive() {
            return None; // ¬is-D(t) constrains nothing in slice 39
        }
        let atom = cx.atoms.atom(lit.var());
        let (tsym, targs) = Self::uapp(cx.terms, atom)?;
        let DtRole::Tester { ctor } = cx.terms.dt_role(tsym)? else {
            return None;
        };
        // Slice 40: record the positive tester so `instantiate_constructor`
        // (in `check`) can introduce `t = C(sel(t)…)` on this branch.
        self.asserted_testers.insert(atom);
        let &t = targs.first()?;
        let (csym, capp) = self.ctor_of_class(cx, t)?;
        if csym == ctor {
            return None; // agrees
        }
        let tn = cx.eq.intern(t);
        let cn = cx.eq.intern(capp);
        let mut leaves = vec![EqLeaf::Asserted(lit)];
        cx.eq.explain(tn, cn, &mut leaves);
        Some(leaves)
    }

    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        None
    }

    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        if let Some(conflict) = self.constructor_clash(cx) {
            return conflict;
        }
        // Injectivity: for same-constructor pairs in one class, instantiate the
        // field selectors so `collapse_lemma` (next) emits the selector-axiom
        // tautologies and EUF congruence derives `a_i = b_i`. This MUST precede
        // collapse in the SAME call and MUST precede the fence: the fence would
        // otherwise short-circuit to Sat on a state where a pending injectivity
        // consequence (surfaced only after the collapse tautologies round-trip
        // through EUF) would produce a conflict — the wrong-SAT this rule fixes.
        self.instantiate_injectivity_selectors(cx);
        if let Some(split) = self.collapse_lemma(cx) {
            return split;
        }
        if let Some(split) = self.tester_lemma(cx) {
            return split;
        }
        if let Some(split) = self.instantiate_constructor(cx) {
            return split;
        }
        if let Some(split) = self.exhaustiveness_split(cx) {
            return split;
        }
        // Model-tied residual fence (spec §4). Slice 40 replaces slice 39's
        // coarse "any undetermined class → Unknown" with a finer one: an
        // undetermined class that survived splitting stays Unknown (defensive —
        // SAT satisfies every emitted disjunction before a Full check), and a
        // cyclic constructor graph is Unknown because its only model is
        // infinite. Slice 41 turns the cycle into a proven `unsat`. This MUST
        // be the last step — every rule above must be saturated first, or the
        // fence could fire on a state that a pending lemma (a collapse, a
        // tester tautology, or a clash) would otherwise have resolved on this
        // same call.
        if self.has_undetermined_class(cx) || self.constructor_graph_find_cycle(cx).is_some() {
            return TCheck::Unknown;
        }
        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
        // DT conflicts cite EqLeafs directly; no tags of its own yet.
    }

    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        for t in self.watched_dt_terms() {
            if m.get(t).is_some() {
                continue;
            }
            let mut visited = FxHashSet::default();
            let Some(v) = self.render_value(cx, t, &mut visited, 0) else {
                continue;
            };
            m.assign(t, shinri_theory::types::ModelVal::Datatype(v));
        }
    }

    fn push(&mut self) {}
    fn pop(&mut self, _level: usize) {}
}

#[cfg(test)]
mod tests {
    use crate::DtSolver;
    use shinri_core::{Context, Lit, Op, SortId, SymbolId, TermId, TermNode, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqJust, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    fn tcheck_name(c: &TCheck) -> &'static str {
        match c {
            TCheck::Sat => "Sat",
            TCheck::Conflict(_) => "Conflict",
            TCheck::Split { .. } => "Split",
            TCheck::Unknown => "Unknown",
        }
    }

    /// Declare `List ::= nil | cons(head: Int, tail: List)` and return
    /// `(list_sort, nil, cons, head, tail, is_nil, is_cons)`.
    pub(crate) fn list_dt(
        ctx: &mut Context,
    ) -> (
        SortId,
        SymbolId,
        SymbolId,
        SymbolId,
        SymbolId,
        SymbolId,
        SymbolId,
    ) {
        let list = ctx.declare_datatype_sort("List");
        let int = ctx.int_sort();
        let b = ctx.bool_sort();
        let nil = ctx.declare_fun("nil", &[], list);
        let is_nil = ctx.declare_fun("is-nil", &[list], b);
        ctx.dt_add_constructor(list, nil, &[], is_nil);
        let cons = ctx.declare_fun("cons", &[int, list], list);
        let head = ctx.declare_fun("head", &[list], int);
        let tail = ctx.declare_fun("tail", &[list], list);
        let is_cons = ctx.declare_fun("is-cons", &[list], b);
        ctx.dt_add_constructor(list, cons, &[head, tail], is_cons);
        (list, nil, cons, head, tail, is_nil, is_cons)
    }

    pub(crate) fn uconst(ctx: &mut Context, name: &str, s: SortId) -> TermId {
        let sym = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn new_var_indexes_constructor_selector_and_tester_apps() {
        let mut ctx = Context::new();
        let (list, nil, cons, head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let x = uconst(&mut ctx, "x", list);
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let head_x = ctx.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();
        let atom = ctx.mk_eq(x, cons_t).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), head_x);
        dt.new_var(&mut cx, Var::new(2), is_cons_x);

        assert!(dt.watches_ctor(cons_t), "cons application must be indexed");
        assert!(dt.watches_ctor(nil_t), "nullary nil must be indexed");
        assert!(
            dt.watches_sel(head_x),
            "selector application must be indexed"
        );
        assert!(dt.watches_tester(is_cons_x), "tester must be indexed");
        assert!(dt.watches_dt_term(x), "datatype-sorted var must be indexed");
        assert!(
            dt.watches_dt_term(cons_t),
            "datatype-sorted constructor application must be indexed"
        );

        // Negative assertions: non-datatype-sorted terms must NOT land in
        // dt_terms, and head_x/is_cons_x must not be misclassified into the
        // wrong role set either.
        assert!(
            !dt.watches_dt_term(one),
            "Int-sorted term must not be indexed as a dt_term"
        );
        assert!(
            !dt.watches_dt_term(head_x),
            "Int-sorted selector output must not be indexed as a dt_term"
        );
        assert!(
            !dt.watches_ctor(head_x),
            "selector output must not be a ctor_app"
        );
        assert!(
            !dt.watches_tester(head_x),
            "selector output must not be a tester"
        );
        assert!(
            !dt.watches_dt_term(is_cons_x),
            "Bool-sorted tester application must not be indexed as a dt_term"
        );
    }

    /// The `seen` guard in `collect` must keep the walk linear in DAG size,
    /// not exponential in sharing depth. Build a chain of N `and`-doublings
    /// over `is-cons(x)`: `level_i = and(level_{i-1}, level_{i-1})`. Every
    /// level's two children are literally the SAME term, so each level is a
    /// diamond join. With the guard, `collect` on `level_N` makes exactly
    /// `2 + 2*N` calls (each level contributes one fresh recursive descent
    /// plus one immediate "already seen" return); without it, the same walk
    /// would make on the order of `2^N` calls (verified by hand: N=10 gives
    /// 22 guarded calls vs. 3071 unguarded — see task-5-report.md Fix 1).
    #[test]
    fn collect_seen_guard_keeps_shared_subterm_walk_linear() {
        let mut ctx = Context::new();
        let (list, _nil, _cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        const N: u32 = 10;
        let mut level = is_cons_x;
        for _ in 0..N {
            level = ctx
                .mk_app(
                    shinri_core::Op::Builtin(shinri_core::BuiltinOp::And),
                    &[level, level],
                )
                .unwrap();
        }

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), level);

        assert_eq!(
            dt.collect_calls(),
            2 + 2 * N,
            "seen guard must keep the walk linear (2 + 2N), not exponential in sharing depth"
        );
        // Correctness survives the guard: the shared leaves are still indexed.
        assert!(
            dt.watches_tester(is_cons_x),
            "shared tester subterm still indexed once"
        );
        assert!(
            dt.watches_dt_term(x),
            "shared datatype var still indexed once"
        );
    }

    #[test]
    fn selector_collapse_emits_tautology_for_matching_constructor() {
        let mut ctx = Context::new();
        let (list, nil, cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let head_x = ctx.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
        let atom = ctx.mk_eq(head_x, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), cons_t);

        // Before x ≡ cons(1,nil), x's class is not constructor-determined, so
        // the completeness fence (spec §5.2, Task 8) would return Unknown —
        // NOT a possibly-wrong Sat — but slice 40's exhaustiveness split
        // (Rule 1) fires first on x's undetermined class, offering the
        // tester disjunction `is-nil(x) ∨ is-cons(x)`. Drain that split; the
        // collapse itself has still not fired, which is what this pre-merge
        // check pins: the SECOND check is Unknown (deduped exhaustiveness,
        // class still undetermined), not a collapse Split. After the merge
        // below, collapse fires.
        assert!(matches!(
            dt.check(&mut cx, Effort::Full),
            TCheck::Split { .. }
        ));
        assert!(matches!(dt.check(&mut cx, Effort::Full), TCheck::Unknown));

        // Merge x with the constructor application.
        let xn = cx.eq.intern(x);
        let cn = cx.eq.intern(cons_t);
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Split { atoms, guard, .. } => {
                assert_eq!(guard, None, "collapse is an unconditional tautology");
                assert_eq!(atoms.len(), 1, "collapse emits a unit lemma");
                // The lemma is `head(cons(1,nil)) = 1`.
                let expected_sel = cx.terms.mk_app(Op::Uninterpreted(head), &[cons_t]).unwrap();
                let expected = cx.terms.mk_eq(expected_sel, one).unwrap();
                assert_eq!(atoms[0], expected);
            }
            other => panic!("expected Split, got {}", tcheck_name(&other)),
        }
    }

    #[test]
    fn selector_collapse_does_not_fire_for_foreign_selector() {
        // `head` belongs to `cons`; applying it to a term equal to `nil` leaves
        // the value UNSPECIFIED. Collapsing here would be unsound.
        let mut ctx = Context::new();
        let (list, nil, _cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let head_x = ctx.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let atom = ctx.mk_eq(head_x, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), nil_t);
        let xn = cx.eq.intern(x);
        let nn = cx.eq.intern(nil_t);
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        assert!(
            matches!(dt.check(&mut cx, Effort::Full), TCheck::Sat),
            "head over a nil-class must NOT collapse"
        );
    }

    #[test]
    fn collapse_reaches_fixpoint_after_lemma_is_installed() {
        let mut ctx = Context::new();
        let (_list, nil, cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let head_c = ctx.mk_app(Op::Uninterpreted(head), &[cons_t]).unwrap();
        let atom = ctx.mk_eq(head_c, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        assert!(matches!(
            dt.check(&mut cx, Effort::Full),
            TCheck::Split { .. }
        ));
        // Installing the lemma's equality must silence the rule.
        let hn = cx.eq.intern(head_c);
        let on = cx.eq.intern(one);
        let _ = cx.eq.merge(hn, on, EqJust::Definitional);
        assert!(
            matches!(dt.check(&mut cx, Effort::Full), TCheck::Sat),
            "collapse must reach a fixpoint"
        );
    }

    #[test]
    fn injectivity_is_a_consequence_of_collapse_and_congruence() {
        // cons(a, nil) ≡ cons(b, nil)  ⇒  a ≡ b. The dedicated injectivity rule
        // (`instantiate_injectivity_selectors`) instantiates head/tail on both
        // constructor apps; `collapse_lemma` then emits the selector-axiom
        // tautologies (head(ca)=a, head(cb)=b, tail(ca)=nil, tail(cb)=nil) and
        // congruence on `head` (simulated here) closes a ≡ b. The engine in this
        // bare harness has no congruence closure of its own, so the head-app
        // congruence merge is simulated below; instantiation now creates the
        // head/tail apps, so we drain collapse to a fixpoint rather than a fixed
        // count.
        let mut ctx = Context::new();
        let (_list, nil, cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int = ctx.int_sort();
        let a = uconst(&mut ctx, "a", int);
        let b = uconst(&mut ctx, "b", int);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let ca = ctx.mk_app(Op::Uninterpreted(cons), &[a, nil_t]).unwrap();
        let cb = ctx.mk_app(Op::Uninterpreted(cons), &[b, nil_t]).unwrap();
        let head_ca = ctx.mk_app(Op::Uninterpreted(head), &[ca]).unwrap();
        let head_cb = ctx.mk_app(Op::Uninterpreted(head), &[cb]).unwrap();
        let atom = ctx.mk_eq(ca, cb).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), head_ca);
        dt.new_var(&mut cx, Var::new(2), head_cb);

        // The SAT/EUF layer merges the two constructor apps and, by congruence,
        // their head-applications. Simulate both here.
        let (can, cbn) = (cx.eq.intern(ca), cx.eq.intern(cb));
        let _ = cx.eq.merge(can, cbn, EqJust::Definitional);
        let (hca, hcb) = (cx.eq.intern(head_ca), cx.eq.intern(head_cb));
        let _ = cx.eq.merge(hca, hcb, EqJust::Definitional);

        // Drain every collapse lemma to a fixpoint, installing each as the SAT
        // layer would. The count is bounded (head/tail on ca and cb), so a
        // generous cap guards against a regression looping forever.
        for _ in 0..16 {
            match dt.check(&mut cx, Effort::Full) {
                TCheck::Split { atoms: lemma, .. } => {
                    let (l, r) = match cx.terms.term_node(lemma[0]) {
                        TermNode::App { args, .. } => {
                            let kids = cx.terms.children(*args).to_vec();
                            (kids[0], kids[1])
                        }
                        _ => panic!("lemma must be an equality application"),
                    };
                    let (ln, rn) = (cx.eq.intern(l), cx.eq.intern(r));
                    let _ = cx.eq.merge(ln, rn, EqJust::Definitional);
                }
                // Fixpoint: all collapse tautologies installed. (Unknown is
                // expected here — tail(ca)≡nil is determined, but the harness
                // has no exhaustiveness, so any remaining undetermined class
                // yields Unknown; either Sat or Unknown ends the drain.)
                TCheck::Sat | TCheck::Unknown => break,
                TCheck::Conflict(_) => panic!("no clash expected: same constructor"),
            }
        }

        let (an, bn) = (cx.eq.intern(a), cx.eq.intern(b));
        assert!(
            cx.eq.are_equal(an, bn),
            "injectivity must emerge: a ≡ b after collapse + congruence"
        );
    }

    #[test]
    fn constructor_clash_is_a_conflict() {
        let mut ctx = Context::new();
        let (list, nil, cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let a1 = ctx.mk_eq(x, nil_t).unwrap();
        let a2 = ctx.mk_eq(x, cons_t).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), a1);
        dt.new_var(&mut cx, Var::new(1), a2);

        let (xn, nn, cn) = (cx.eq.intern(x), cx.eq.intern(nil_t), cx.eq.intern(cons_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Conflict(_) => {}
            other => panic!("expected Conflict, got {}", tcheck_name(&other)),
        }
    }

    #[test]
    fn tester_over_constructor_emits_unit_tautology() {
        // `is-cons(cons(1,nil))` is a valid unit lemma.
        let mut ctx = Context::new();
        let (_list, nil, cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let is_cons_c = ctx.mk_app(Op::Uninterpreted(is_cons), &[cons_t]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), is_cons_c);

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Split { atoms, guard, .. } => {
                assert_eq!(guard, None);
                assert_eq!(atoms, vec![is_cons_c]);
            }
            other => panic!("expected Split, got {}", tcheck_name(&other)),
        }
    }

    /// `is-cons(x)` where `x ≡ cons(1,nil)` only *conditionally* (the merge is
    /// asserted, not a syntactic identity) must NOT be emitted as the
    /// unconditional unit lemma. The lemma must instead be rewritten onto the
    /// constructor application itself — `is-cons(cons(1,nil))` — which IS an
    /// unconditional tautology; congruence then supplies `is-cons(x) ≡
    /// is-cons(cons(1,nil))` only on branches where `x ≡ cons(1,nil)` holds.
    /// Emitting `is-cons(x)` directly as a guard-free level-0 unit fact would
    /// launder a conditional fact into a permanent global one — a wrong-UNSAT
    /// hazard (concrete repro: `(or (= x (cons 1 nil)) (= x nil))` together
    /// with `(not (is-cons x))` is SAT via `x = nil`, but a decision that
    /// merges `x` with `cons(1,nil)` first would pin `is-cons(x)` at level 0
    /// and falsely report UNSAT).
    #[test]
    fn tester_lemma_over_class_member_rewrites_onto_constructor_app() {
        let mut ctx = Context::new();
        let (list, nil, cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), is_cons_x);
        dt.new_var(&mut cx, Var::new(1), cons_t);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(cons_t));
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Split { atoms, guard, .. } => {
                assert_eq!(guard, None, "the rewritten lemma is unconditional");
                let expected = cx
                    .terms
                    .mk_app(Op::Uninterpreted(is_cons), &[cons_t])
                    .unwrap();
                assert_eq!(
                    atoms,
                    vec![expected],
                    "lemma must be is-cons(cons(1,nil)), NOT is-cons(x) — \
                     the latter is only conditionally true and cannot ride a \
                     guard-free unit Split"
                );
            }
            other => panic!("expected Split, got {}", tcheck_name(&other)),
        }
    }

    #[test]
    fn asserted_tester_conflicting_with_constructor_is_rejected_at_assert() {
        // is-nil(x) asserted true while x ≡ cons(1,nil) ⇒ conflict.
        let mut ctx = Context::new();
        let (list, nil, cons, _head, _tail, is_nil, _is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let is_nil_x = ctx.mk_app(Op::Uninterpreted(is_nil), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_nil_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_nil_x);
        dt.new_var(&mut cx, Var::new(1), cons_t);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(cons_t));
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        let conflict = dt.assert(&mut cx, Lit::new(v, true));
        assert!(
            conflict.is_some(),
            "is-nil(x) with x ≡ cons(..) must conflict at assert time"
        );
    }

    #[test]
    fn undetermined_datatype_class_yields_unknown_not_sat() {
        // `x` is a List with no constructor in its class and no tester pinning
        // it. Exhaustiveness (slice 40) is what would decide this, so slice 39
        // must fence to Unknown rather than claim Sat — but slice 40's
        // exhaustiveness split (Rule 1) now fires FIRST on `x`'s undetermined
        // class, so the pre-fence signal is a guard-free `Split` (the tester
        // disjunction), not `Unknown` directly. Only `x` is registered (not a
        // second `x = y` var) so there is exactly one watched, undetermined
        // datatype term and thus exactly one split to drain before the fence
        // — see `undetermined_class_emits_exhaustiveness_disjunction` for why
        // two undetermined terms would make this order-dependent.
        let mut ctx = Context::new();
        let (list, _nil, _cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), x);

        // Drain the exhaustiveness split before the fence is reached.
        assert!(
            matches!(dt.check(&mut cx, Effort::Full), TCheck::Split { .. }),
            "exhaustiveness offers the tester disjunction first"
        );
        assert!(
            matches!(dt.check(&mut cx, Effort::Full), TCheck::Unknown),
            "constructor-undetermined class must fence to Unknown"
        );
    }

    #[test]
    fn determined_datatype_class_is_sat() {
        let mut ctx = Context::new();
        let (list, nil, _cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let atom = ctx.mk_eq(x, nil_t).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        let (xn, nn) = (cx.eq.intern(x), cx.eq.intern(nil_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        assert!(
            matches!(dt.check(&mut cx, Effort::Full), TCheck::Sat),
            "constructor-determined class must be Sat"
        );
    }

    #[test]
    fn model_assigns_ground_constructor_term() {
        let mut ctx = Context::new();
        let (list, nil, _cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let atom = ctx.mk_eq(x, nil_t).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        let (xn, nn) = (cx.eq.intern(x), cx.eq.intern(nil_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        let mut m = shinri_theory::ModelBuilder::default();
        dt.model(&mut cx, &mut m);
        match m.get(x) {
            Some(shinri_theory::types::ModelVal::Datatype(s)) => assert_eq!(s, "nil"),
            other => panic!("expected a datatype model value, got {other:?}"),
        }
    }

    #[test]
    fn undetermined_class_emits_exhaustiveness_disjunction() {
        // A bare List var with no constructor and no tester: Rule 1 must offer the
        // exhaustiveness split `is-nil(x) ∨ is-cons(x)`, guard-free (a tautology),
        // biasing the nullary `nil` branch via phase preference.
        //
        // Only ONE List-sorted term (`x`) is registered — deliberately, not
        // `x = y` over two fresh List vars. `exhaustiveness_split` scans
        // `watched_dt_terms()`, which iterates an `FxHashSet`; with two
        // undetermined terms watched, the split could target either one
        // depending on hash order, AND draining it would leave the other
        // still undetermined, so a second `check` would offer THAT term's
        // split instead of falling through to the fence — the "second check
        // is Unknown" assertion below would then depend on hash order too.
        // Registering `x` itself as the atom keeps it the only datatype term
        // the theory watches, so both the split's atoms and the dedup are
        // deterministic.
        let mut ctx = Context::new();
        let (list, _nil, _cons, _head, _tail, is_nil, is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), x);

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Split {
                atoms,
                guard,
                phases,
            } => {
                assert_eq!(guard, None, "exhaustiveness is a tautology");
                let is_nil_x = cx.terms.mk_app(Op::Uninterpreted(is_nil), &[x]).unwrap();
                let is_cons_x = cx.terms.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();
                assert!(atoms.contains(&is_nil_x) && atoms.contains(&is_cons_x));
                assert_eq!(atoms.len(), 2, "one atom per constructor");
                // Nullary `nil` is preferred true; `cons` carries no preference.
                let nil_pos = atoms.iter().position(|&a| a == is_nil_x).unwrap();
                assert_eq!(phases[nil_pos], Some(true), "nullary-first phase bias");
                let cons_pos = atoms.iter().position(|&a| a == is_cons_x).unwrap();
                assert_eq!(
                    phases[cons_pos], None,
                    "non-nullary cons carries no preference"
                );
            }
            other => panic!("expected Split, got {}", tcheck_name(&other)),
        }

        // Deduped: a second check does not re-emit; with no SAT to decide the
        // disjunction the class stays undetermined, so the fence still says Unknown.
        assert!(matches!(dt.check(&mut cx, Effort::Full), TCheck::Unknown));
    }

    #[test]
    fn asserted_tester_agreeing_with_constructor_is_fine() {
        let mut ctx = Context::new();
        let (list, nil, _cons, _head, _tail, is_nil, _is_cons) = list_dt(&mut ctx);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let is_nil_x = ctx.mk_app(Op::Uninterpreted(is_nil), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_nil_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_nil_x);
        dt.new_var(&mut cx, Var::new(1), nil_t);
        let (xn, nn) = (cx.eq.intern(x), cx.eq.intern(nil_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        assert!(dt.assert(&mut cx, Lit::new(v, true)).is_none());
    }

    #[test]
    fn asserted_tester_instantiates_guarded_constructor() {
        // is-cons(x) asserted, x's class holds no constructor: Rule 2 must offer the
        // guarded lemma  ¬is-cons(x) ∨ x = cons(head(x), tail(x)),  and register the
        // minted selector apps as watched (head(x) Int-sorted; tail(x) a dt_term).
        let mut ctx = Context::new();
        let (list, _nil, cons, head, tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_cons_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, v, is_cons_x);

        // Assert the tester true; it must be recorded, not conflict (empty class).
        assert!(dt.assert(&mut cx, Lit::new(v, true)).is_none());

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Split {
                atoms: lemma,
                guard,
                ..
            } => {
                assert_eq!(lemma.len(), 1, "instantiation emits a unit equality");
                let head_x = cx.terms.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
                let tail_x = cx.terms.mk_app(Op::Uninterpreted(tail), &[x]).unwrap();
                let capp = cx
                    .terms
                    .mk_app(Op::Uninterpreted(cons), &[head_x, tail_x])
                    .unwrap();
                let expected = cx.terms.mk_eq(x, capp).unwrap();
                assert_eq!(lemma[0], expected, "x = cons(head(x), tail(x))");
                assert_eq!(
                    guard,
                    Some(Lit::new(v, true).negate()),
                    "guarded by ¬is-cons(x)"
                );
                assert!(
                    dt.watches_sel(head_x) && dt.watches_sel(tail_x),
                    "fields watched"
                );
                assert!(
                    dt.watches_dt_term(tail_x),
                    "datatype field is a watched dt_term"
                );
            }
            other => panic!("expected Split, got {}", tcheck_name(&other)),
        }
    }

    #[test]
    fn cyclic_constructor_graph_fences_to_unknown() {
        // x ≡ cons(h, x): x's class holds a constructor app whose `tail` field is x
        // itself. Determined, so slice-39 rules are satisfied — but the only ground
        // model is infinite. The occurs-check fence must return Unknown, NOT Sat.
        let mut ctx = Context::new();
        let (list, _nil, cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int = ctx.int_sort();
        let h = uconst(&mut ctx, "h", int);
        let x = uconst(&mut ctx, "x", list);
        let cons_hx = ctx.mk_app(Op::Uninterpreted(cons), &[h, x]).unwrap();
        let atom = ctx.mk_eq(x, cons_hx).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(cons_hx));
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        // Drain any collapse tautologies to a fixpoint, then the fence must fire.
        let mut verdict = dt.check(&mut cx, Effort::Full);
        for _ in 0..8 {
            match verdict {
                TCheck::Split { atoms: l, .. } => {
                    if let TermNode::App { args, .. } = cx.terms.term_node(l[0]) {
                        let kids = cx.terms.children(*args).to_vec();
                        let (a, b) = (cx.eq.intern(kids[0]), cx.eq.intern(kids[1]));
                        let _ = cx.eq.merge(a, b, EqJust::Definitional);
                    }
                    verdict = dt.check(&mut cx, Effort::Full);
                }
                _ => break,
            }
        }
        assert!(
            matches!(verdict, TCheck::Unknown),
            "cyclic (infinite-only) model must fence to Unknown, got {}",
            tcheck_name(&verdict)
        );
    }

    #[test]
    fn find_cycle_returns_the_self_edge_for_x_eq_cons_h_x() {
        // x = cons(h, x): one datatype-sorted field (tail = x) points back to x's
        // own class → a single self-edge (field = the x subterm, next_capp = cons(h,x)).
        let mut ctx = Context::new();
        let (list, _nil, cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int = ctx.int_sort();
        let h = uconst(&mut ctx, "h", int);
        let x = uconst(&mut ctx, "x", list);
        let cons_hx = ctx.mk_app(Op::Uninterpreted(cons), &[h, x]).unwrap();
        let atom = ctx.mk_eq(x, cons_hx).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(cons_hx));
        let _ = cx
            .eq
            .merge(xn, cn, EqJust::Asserted(Lit::new(Var::new(0), true)));

        let cycle = dt
            .constructor_graph_find_cycle(&mut cx)
            .expect("cycle expected");
        assert_eq!(cycle.len(), 1, "self-cycle has exactly one edge");
        let (field, next_capp) = cycle[0];
        // the edge's field is in the same class as x, and next_capp is cons(h,x)
        let fieldn = cx.eq.intern(field);
        assert_eq!(cx.eq.find(fieldn), cx.eq.find(xn));
        assert_eq!(next_capp, cons_hx);
    }

    #[test]
    fn determined_acyclic_datatype_child_renders_full_nested_term() {
        // x ≡ cons(one, nil): a determined, ACYCLIC List whose datatype-sorted
        // `tail` field is itself a determined constructor application (nil).
        // This drives the DFS "descend into child, pop back, no back-edge →
        // false" branch of `constructor_graph_find_cycle` AND the recursive
        // descent into a datatype field inside `render_value_inner` — neither
        // of which any other test reaches all the way to `Sat` + `model`.
        let mut ctx = Context::new();
        let (list, nil, cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let atom = ctx.mk_eq(x, cons_t).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), nil_t);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(cons_t));
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        assert!(
            matches!(dt.check(&mut cx, Effort::Full), TCheck::Sat),
            "determined, acyclic datatype term must be Sat — neither the \
             undetermined-class branch nor the cycle branch of the fence \
             should trip"
        );

        let mut m = shinri_theory::ModelBuilder::default();
        dt.model(&mut cx, &mut m);
        match m.get(x) {
            Some(shinri_theory::types::ModelVal::Datatype(s)) => {
                assert_eq!(s, "(cons one nil)")
            }
            other => panic!("expected a datatype model value, got {other:?}"),
        }
    }
}
