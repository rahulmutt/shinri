# Slice 41 — Datatype acyclicity (cycle → proven `unsat`)

**Status:** design
**Date:** 2026-07-24
**Area:** `shinri-dt` (`DtSolver::check`, the constructor-graph occurs-check); no
new crates, no new `Combiner` slot, no new `shinri-core`/`shinri-parser`
surface, no N-O hooks.
**Predecessors:** slice 40 (tester case-splitting) — supplied the model-tied
residual fence this slice sharpens: `constructor_graph_has_cycle` and the
`check` branch that returns `Unknown` on a cyclic determined state.

## 1. Summary

Slice 40 replaced slice 39's coarse completeness fence with a model-tied one:
when every demanded datatype class is constructor-determined, `DtSolver::check`
runs a read-only occurs-check over the runtime constructor graph
(`constructor_graph_has_cycle`, `lib.rs:495`); a cycle means the only ground
model is an infinite term, so slice 40 returns `TCheck::Unknown` — a sound
under-approximation.

Slice 41 converts that **same traversal** into a proven `unsat` carrying a
**minimal cycle-explanation conflict clause**. The datatype acyclicity axiom
("no term is a proper subterm of itself") makes a cycle in the e-class
constructor-argument graph an outright contradiction, not merely a state with no
finite model. This is the documented, adjudicated flip the slice-40 boundary
table promised: `x = cons(h, x)` returns `unknown` in slice 40 and `unsat` in
slice 41.

Nothing else about the theory changes: no new sorts, ops, registry fields,
parser surface, `Combiner` slot, or Nelson–Oppen exchange. `DtSolver` remains a
pure lemma-and-conflict-on-demand theory that owns no equality state.

## 2. Representation — nothing new

Slice 41 reuses everything slices 39–40 built. The only structural change is
internal to `DtSolver`: the cycle detector must return the cycle it finds
instead of a bare `bool`, so the conflict can cite the equalities along it.

- `TCheck::Conflict(Vec<EqLeaf>)` — the existing conflict channel. The cycle
  conflict cites `EqLeaf`s **directly**, exactly as `constructor_clash`
  (`lib.rs:728`) already does. No explanation tag is minted (§4).
- `EqualityEngine::explain(a, b, &mut leaves)` — expands an e-class equality into
  its `EqLeaf` justification (asserted literals + congruence), already used by
  `constructor_clash` and `assert`.
- The static reverse-dependency map (`context.rs:1275`, datatype sort →
  constructors that can recursively contain the sort) remains available to
  *prune* the walk — a sort that cannot recursively contain itself needs no
  traversal — but cycle detection itself is over the live e-class argument
  graph, unchanged from slice 40.

## 3. Detector refactor — return the cycle, not a `bool`

`constructor_graph_has_cycle(&self, cx) -> bool` becomes
`constructor_graph_find_cycle(&self, cx) -> Option<Vec<CycleEdge>>` (name
provisional). It preserves the slice-40 structure exactly — iterative explicit
DFS with grey (`on_path`) / black (`done`) sets, **never recursive** because the
term graph comes from untrusted `declare-datatypes`/assert input and may be
arbitrarily deep (threat model). Two changes:

1. **`ctor_child_class_reps` must carry concrete terms, not reps.** Today it
   returns `Vec<ENodeId>` (child class reps only), which is enough to *detect* a
   cycle but discards which field term and which constructor application formed
   each edge. The explanation needs concrete `TermId`s. It becomes, per
   datatype-sorted field of the traversed constructor application, the pair
   **(field `TermId`, the child class's traversed `capp` `TermId`)** — or an
   equivalent shape that lets the caller recover both endpoints of every edge.

2. **Reconstruct the ordered edge list on the back-edge.** When the DFS hits a
   grey child (`on_path.contains(&child)`), walk the current DFS stack from that
   child up to the current frame to recover the ordered cycle
   `capp_0 → capp_1 → … → capp_0`. Each grey stack frame already holds its node
   and the constructor application it is expanding, so the field/`capp` endpoints
   of every cycle edge are recoverable without a second traversal.

A `CycleEdge` is `{ field: TermId, next_capp: TermId }`: the datatype-sorted
field of one constructor application, and the constructor application sitting in
the class that field points to.

## 4. Conflict construction — the minimal cycle path

For each cycle edge, the single fact that closes it is the merge equality
**`field_i = next_capp_i`**. The constructor applications sit in their e-classes
definitionally (they are the registered `ctor_apps`), and the syntactic
constructor structure — `capp_i = C_i(…, field_i, …)` — needs no citation
because it is inherent in the term, not an asserted fact. So the whole
explanation is the union of those per-edge equalities:

```rust
fn acyclicity_conflict(&self, cx: &mut TheoryCtx, cycle: Vec<CycleEdge>) -> TCheck {
    let mut leaves = Vec::new();
    for edge in cycle {
        let fnode = cx.eq.intern(edge.field);
        let cnode = cx.eq.intern(edge.next_capp);
        cx.eq.explain(fnode, cnode, &mut leaves); // expands congruence → asserted leaves
    }
    dedup(&mut leaves);
    TCheck::Conflict(leaves)
}
```

Worked example — `x = cons(h, x)`: the class of `x` holds `cons(h, x)`; its
datatype-sorted field is the `x` subterm, whose class is `x` itself, so the
single self-edge is `explain(x, cons(h, x))`. That equality is the asserted
literal `x = cons(h, x)`, so `leaves = [Asserted(x = cons(h, x))]` and the
learnt clause is exactly `¬(x = cons(h, x))`. Tight, and structurally identical
to how `constructor_clash` builds its explanation. A longer cycle
`x = cons(1, y) ∧ y = cons(2, x)` yields the two merge equalities whose
conjunction the acyclicity axiom refutes.

**Why the constructor structure needs no citation.** The refutation is: substitute
each edge equality into the constructor chain and `capp_0` becomes a proper
subterm of itself, which acyclicity forbids. The substitution uses only the
merge equalities (cited) plus the syntactic `C_i(…)` shape of terms already in
the formula (not a fact that can be negated away). Citing more — e.g. every
determined class's constructor equality — would only widen the learnt clause and
weaken backjumping, which is why the minimal path was chosen over the
"all determined" and "SCC region" alternatives.

## 5. Fence wiring and `explain`

The last branch of `check` splits the slice-40 combined fence into its two
distinct verdicts:

```rust
// Model-tied residual fence. Slice 41 sharpens slice 40's combined
// `Unknown` into two verdicts: an undetermined class that survived splitting
// stays Unknown (defensive; slice 42 leaves infinite-sort terms free), while a
// cyclic constructor graph over determined classes is now a proven `unsat` by
// datatype acyclicity. MUST be the last step — every lemma rule above must be
// saturated first.
if self.has_undetermined_class(cx) {
    return TCheck::Unknown;                       // unchanged (defensive / slice-42 owned)
}
if let Some(cycle) = self.constructor_graph_find_cycle(cx) {
    return self.acyclicity_conflict(cx, cycle);   // was TCheck::Unknown in slice 40
}
TCheck::Sat
```

Ordering note: `has_undetermined_class` is checked before the cycle walk, so the
cycle detector only ever runs over fully-determined classes — a cycle that
passes through an *undetermined* class is caught as `Unknown` (that class has no
constructor application to traverse), never mis-reported as an acyclicity
conflict. This matches slice 40's traversal semantics: `ctor_child_class_reps`
returns `None` for an undetermined class, terminating that branch of the walk.

`DtSolver::explain` **stays a no-op.** `TCheck::Conflict(Vec<EqLeaf>)` carries
its justification inline; the `mint_eq_tag`/`explain` machinery is the
*propagation* channel (interface equalities resolved lazily), not the conflict
channel. The slice-40 §5.E remark that "slice 41 adds the cycle-explanation tag"
was imprecise against the real `Conflict` protocol — no tag is minted, exactly
as `constructor_clash` mints none.

**Residual `Unknown` after this slice.** The only remaining `Unknown` from
`DtSolver` is the `has_undetermined_class` branch. A determined acyclic state is
`Sat`; a determined cyclic state is now `unsat`. Undetermined classes (the
defensive branch, in practice reachable only via infinite-sort terms SAT never
pinned to a constructor) are slice 42's territory.

## 6. Model and render — unchanged

A cyclic branch can no longer reach `sat` (it conflicts first), so
`DtSolver::model` and `render_value` are untouched. The `depth > 10_000`
overflow backstop and the visited-set occurs-check remain exactly as slice 40
left them — correct defense-in-depth on a path that a sound run never takes.

## 7. Testing

Follows slice-40 §6 and the project's standing gates. All additions are small
and fast; the blocking PR tier budget (10–15 min) is unaffected.

- **Unit tests (`shinri-dt`, hand-built `EqualityEngine`/`TheoryCtx`):**
  - `constructor_graph_find_cycle` returns the ordered cycle for `x = cons(h, x)`
    (a self-edge) and for a 2-node mutual cycle `x = cons(1, y) ∧ y = cons(2, x)`;
  - `acyclicity_conflict` produces the minimal leaf set — for the self-cycle,
    assert the conflict is exactly the single asserted literal `x = cons(h, x)`
    (not a broader set);
  - a determined **acyclic** model still returns `Sat` — no false conflict;
  - a cycle routed through an **undetermined** class is *not* reported as an
    acyclicity conflict — `has_undetermined_class` returns `Unknown` first.
- **End-to-end `.smt2` (`shinri-solver`):**
  - flip the slice-40 pinned `x = cons(h, x)` case from `unknown` → **`unsat`**,
    commented as the adjudicated acyclicity flip;
  - add a longer cycle `x = cons(1, y) ∧ y = cons(2, x)` → **`unsat`**;
  - keep an acyclic `sat` and an exhaustiveness-only `unsat` as regression
    anchors (unchanged verdicts).
- **Oracle differential vs z3 + cvc5** (both support QF_DT), feature-gated:
  `cargo nextest run -p shinri-solver --features oracle`. The cyclic cases now
  agree on `unsat` (no more slice-40 `unknown` under-approximation there).
  **Confirm the discovered test count is non-zero** — a flagless run silently
  compiles to zero tests and proves nothing.
- **Fuzz:** the slice-40 datatype corpus already exercises the split and
  instantiation paths that feed determined cyclic states; no new seed shape is
  required, but confirm no panic / non-termination on cyclic input.
- **Gates:** `script_e2e` runs locally pre-push (this slice shifts completeness —
  the `unknown → unsat` flip is z3/cvc5-confirmed, an adjudicated flip, not a
  regression); `cargo fmt --all` before pushing (CI `fmt --check` fails fast);
  `mise run lint` clean (clippy `-D warnings`).

## 8. Scope — explicitly out of slice 41

| Deferred | Owner |
|---|---|
| Finiteness / cardinality; leaving infinite-sort terms free (removes residual `Unknown`) | 42 |
| Nelson–Oppen exchange for Int/Real datatype fields (QF_UFDTLIA) | 43 |

## 9. Success criteria

- `x = cons(h, x)` and analogous cyclic constraints decide **`unsat`** with a
  minimal cycle-explanation conflict clause, verified by unit test (leaf set)
  and by the oracle differential (agrees with z3/cvc5).
- No wrong-`unsat`: every determined **acyclic** state still decides `sat`; a
  cycle through an undetermined class still decides `unknown` (unit test).
- The learnt clause is the minimal cycle path — for the self-cycle, exactly the
  one asserted literal — not a broad over-approximation.
- Oracle differential over the QF_DT corpus shows no `sat`/`unsat` disagreement
  with z3 or cvc5; the slice-40 residual `unknown` on cyclic cases is gone.
- `mise run ci` green; `script_e2e` and `fmt --check` clean pre-push.
