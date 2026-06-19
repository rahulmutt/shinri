# shinri-sat — Design Specification

**The CDCL(T)-ready SAT core: clause DB, two-watched-literals, 1-UIP analysis, incremental assumptions, and the theory/proof seams**

- **Date:** 2026-06-19
- **Status:** Approved design — ready for implementation planning
- **Scope:** A build-ready specification for the `shinri-sat` crate (Phase 1 component #3, after `shinri-num` and `shinri-core`). Derived from and consistent with the north-star design (`2026-06-18-shinri-design.md`, §5) and the core spec (`2026-06-18-shinri-core-design.md`).

---

## 1. Purpose & Position in the Workspace

`shinri-sat` is the CDCL SAT search engine of shinri. It owns clause storage, Boolean constraint propagation, conflict-driven learning, branching, restarts, clause-database reduction, and incremental solving with assumptions. It is built to be the **CDCL(T)** core that later hosts the theory layer — the theory-integration seam is designed in now, at zero cost when off, exactly as the core crate did for proofs.

**Dependency position** (north-star §3): `num ← core ← sat ← theory ← {euf, arith} ← solver`. `shinri-sat` depends only on `shinri-core` in the shipping build, and is consumed by `shinri-theory`.

### 1.1 Responsibilities (what sat owns)

- The **clause database**: a packed `u32` literal arena addressed by `ClauseRef`, with stable `ClauseId` identity for proofs (§3, §4).
- **Two-watched-literals** propagation with inline blocking literals and an **implicit-binary** fast path (§4, §5).
- **1-UIP conflict analysis** with recursive / self-subsuming minimization (§5).
- **Branching** (VMTF and EVSIDS, selectable) behind a `BranchHeuristic` trait, plus phase saving (§6).
- **Restarts** (Luby + Glucose-EMA, selectable) and **LBD-based clause-DB reduction** (§6).
- **Incremental solving**: assumptions as first decisions, failed-assumption core extraction, and a scoped `push`/`pop` overlay (§7).
- The two cross-cutting **seams**: the `Theory` trait (the T in CDCL(T)) with a zero-cost `NoTheory` default, and `ProofSink` threading from `shinri-core` (§8).

### 1.2 Non-responsibilities (what sat does *not* own)

Congruence closure, simplex, difference logic, theory combination (those live in `shinri-{euf,arith}` / `shinri-theory`); SMT-LIB parsing (`shinri-parser`); the top-level solver API and model assembly across theories (`shinri-solver`). `shinri-sat` provides the Boolean search and the *calling contract* the theory layer implements, not any theory algorithm.

### 1.3 Inherited vocabulary from `shinri-core`

`Var`, `Lit` (packed `var << 1 | sign`), `ClauseId`, the generic `UndoLog<E>` backtracking discipline, and the `ProofSink` / `NoProof` / `TheoryJust` proof seam are all defined in `shinri-core` and reused unchanged.

---

## 2. Design Principles (inherited + sat-specific)

These specialize the north-star principles (§2) for the SAT core:

1. **Soundness is existential.** A wrong `sat`/`unsat` sinks an SMT-COMP division. Every `sat` is internally re-validated against all clauses before it is returned; every `unsat` carries a checkable certificate.
2. **Index/arena over smart pointers.** Clauses, watches, and the trail are `u32`-indexed flat `Vec`s. No `Rc`/`RefCell` on the hot path.
3. **The one-way doors are designed in now.** The `Theory` trait and `ProofSink` threading cost nothing when off (`NoTheory`/`NoProof` ZSTs dead-code-eliminate), but enabling them is a type substitution, not a rewrite.
4. **Monomorphization on the hot path.** Generic over `T: Theory`, `P: ProofSink`, and `H: BranchHeuristic`; no `dyn` dispatch anywhere in the solve loop. The branching heuristic is selected at the type level (construction time), so even `next`/`bump` are monomorphized — chosen over a runtime enum wrapper deliberately for this performance-sensitive core.
5. **Decomposed, independently-testable units.** State lives in focused structures (`Assignment`, `Trail`, `ClauseDb`, `Watches`, …) with narrow interfaces; the thin `Solver` orchestrator runs the loop without re-implementing them.
6. **Deterministic and reproducible.** Integer-only VMTF and a fixed seed make runs bit-reproducible, so differential-test failures replay exactly.

---

## 3. Crate Layout & Module Boundaries

```
crates/shinri-sat/
├── Cargo.toml          # deps: shinri-core. dev: proptest, <pure-Rust oracle>
├── src/
│   ├── lib.rs          # crate root, re-exports, top-level docs
│   ├── solver.rs       # Solver<T, P, H>: the thin orchestrator + main CDCL(T) loop
│   ├── assignment.rs   # Assignment: per-var value / level / reason / phase
│   ├── trail.rs        # Trail: assignment stack + decision-level markers
│   ├── clause.rs       # ClauseDb: packed u32 literal arena + ClauseRef + headers
│   ├── watch.rs        # Watches: 2WL with inline blocking lit + implicit binaries
│   ├── analyze.rs      # 1-UIP conflict analysis + recursive minimization
│   ├── heuristic/
│   │   ├── mod.rs      # BranchHeuristic trait + phase saving
│   │   ├── vmtf.rs     # VMTF impl
│   │   └── evsids.rs   # EVSIDS impl
│   ├── restart.rs      # RestartPolicy: Luby + Glucose-EMA, selectable
│   ├── reduce.rs       # LBD computation + clause-DB reduction
│   ├── theory.rs       # Theory trait (the T seam) + NoTheory ZST default
│   ├── config.rs       # SolverConfig: heuristic choice, restart mode, knobs
│   └── dimacs.rs       # #[cfg(any(test, feature = "dimacs"))] DIMACS reader
└── tests/
    ├── dimacs_oracle.rs      # differential vs pure-Rust reference solver
    ├── model_selfcheck.rs    # every SAT model re-validated against all clauses
    └── props.rs              # proptest invariants
```

**Boundary rules that keep the hot loop legible:**

- `Solver<T: Theory, P: ProofSink, H: BranchHeuristic>` owns the sub-structures and runs the loop; it does *not* re-implement their internals.
- `propagate` is the one place that crosses `Watches` ↔ `ClauseDb` ↔ `Assignment` — the cache-critical crossing is concentrated, not scattered.
- `dimacs.rs` is test/feature-gated so the shipping library carries no parser weight (parsing belongs to `shinri-parser`).
- The generic params `T`, `P`, and `H` are the only seams; everything else is concrete for monomorphization.

---

## 4. Data Model

Everything is `u32`-indexed per the arena mandate; no per-clause heap allocation. Hot side tables are contiguous `Vec`s sized once per `new_var`.

### 4.1 Variables & literals

From `shinri-core`: `Var(u32)`, `Lit(var << 1 | sign)`. The solver indexes side tables by `var.index()` and by `lit` (as `usize`).

### 4.2 `Assignment` — struct-of-arrays, indexed by var

```rust
struct Assignment {
    value:  Vec<LBool>,   // True / False / Unset, 1 byte each
    level:  Vec<u32>,     // decision level at which the var was assigned
    reason: Vec<Reason>,  // antecedent of the assignment
    phase:  Vec<bool>,    // saved phase for phase-saving
}

enum Reason {
    Clause(ClauseRef),    // a longer clause became unit
    Binary(Lit),          // implied by an implicit binary clause (the other literal)
    Theory(TheoryJust),   // theory propagation; explanation recomputed lazily
    Decision,             // a branching decision (or assumption)
    Unit,                 // a top-level unit clause
}
```

`Reason` is the resolution backbone for both conflict analysis *and* the proof chain. `Theory(TheoryJust)` is the seam where theory propagations carry their lazy explanation token, expanded via `Theory::explain` only if analysis touches them.

### 4.3 `Trail` — assigned-literal stack + level markers

```rust
struct Trail {
    lits:         Vec<Lit>,    // assignments in order
    level_starts: Vec<usize>,  // index where each decision level began
    qhead:        usize,       // propagation cursor
}
```

Backtracking pops `lits` above a level marker and unsets each var's `value`. This is the SAT-specific undo; theories unwind through their own `Theory::pop` driven in lockstep with the SAT decision levels (the shared `UndoLog` discipline from core keeps Boolean and theory state consistent).

### 4.4 `ClauseDb` — one flat arena

```rust
struct ClauseDb { arena: Vec<u32> }   // headers + literals, packed
struct ClauseRef(u32);                // offset into the arena
// layout at offset: [header: len + learnt-bit + LBD + activity/flags][lit0][lit1]...
```

`ClauseId` (the stable, proof-facing id from core) maps to the live `ClauseRef`; reduction/relocation updates the `ClauseRef` while `ClauseId` stays stable for `ProofSink`. **Binary clauses are never stored here** (see §4.5).

### 4.5 `Watches` — per-literal watch lists, implicit binaries

```rust
struct Watch { target: WatchTarget, blocker: Lit }  // blocker = inline blocking literal
enum WatchTarget { Clause(ClauseRef), Binary }       // Binary: the clause IS (blocker, watched-lit)
type WatchList = Vec<Watch>;                          // indexed by lit.index()
```

For a binary clause `(a ∨ b)` we store `Watch { Binary, blocker = b }` on `watches[¬a]` and symmetrically `Watch { Binary, blocker = a }` on `watches[¬b]` — binary propagation reads only the watch entry and **never touches the arena** (the implicit-binary fast path). For longer clauses, the inline blocking literal short-circuits the common already-satisfied case before the arena is read.

### 4.6 Size discipline

`Watch` is 8 bytes (`Lit` blocker + tagged `u32`); `LBool` is 1 byte; `Reason` fits in 8 bytes. Side tables grow once per `new_var`; the clause arena grows append-only and is compacted only at reduction.

---

## 5. The CDCL(T) Main Loop, Propagation & Analysis

### 5.1 Main loop (`Solver::search`) — the abstract DPLL(T) spine

```
loop {
    if let Some(conflict) = propagate() {        // BCP to fixpoint, then theory
        if decision_level == 0 { return Unsat }  // (or core extraction under assumptions, §7)
        let (learnt, btlevel) = analyze(conflict);
        backtrack_to(btlevel);
        let asserting = add_learnt(learnt);       // -> ProofSink::learn(chain)
        enqueue(asserting, Reason::Clause | Unit);
        heuristic.on_conflict(); restart.on_conflict(); maybe_reduce();
    } else {
        if all_assigned {
            if theory.check(Full) is clean { return Sat(model) }  // self-checked, §9
            else { continue }                                     // theory lemma -> keep searching
        }
        match decide() {                          // assumptions first, then heuristic
            Some(lit) => { new_level(); enqueue(lit, Decision) }
            None      => { /* all vars assigned -> handled above */ }
        }
    }
}
```

### 5.2 `propagate()` — the hot path, two-phase

1. **Boolean BCP** drains the trail from `qhead`. For each newly-false literal `¬p`, walk `watches[p]`: binary watches propagate or conflict directly from the entry; clause watches check the blocker first, else visit the arena to find a new watch or detect unit/conflict. Standard two-watched-literal maintenance, with `debug_assert!`-guarded watch invariants. Audited `get_unchecked` is permitted in this loop only, in small individually-justified `unsafe` blocks (north-star §5 performance note).
2. **Theory propagation.** When Boolean BCP reaches fixpoint, call `theory.propagate(&mut out)` (a no-op, fully inlined away, for `NoTheory`). Returned `(Lit, TheoryJust)` pairs are enqueued with `Reason::Theory`; a returned conflict clause re-enters analysis. Loop until Boolean and theory propagation reach **joint fixpoint**. `theory.assert(lit)` is fed each Boolean assignment as the trail grows, so the theory tracks the evolving partial model.

### 5.3 `analyze(conflict)` — 1-UIP

- Walk the implication graph backward from the conflict, bumping branching activity, counting literals at the current decision level until exactly one remains (the first UIP).
- `Reason::Theory` antecedents are expanded on demand via `theory.explain(just, &mut out)` — the lazy explanation, recomputed only here.
- **Recursive / self-subsuming minimization** (Sörensson–Biere): drop literals whose reasons are wholly subsumed by other literals already in the learnt clause, using a decision-level bitset plus seen-marks for the redundancy test (~30% clause shrink).
- Emit the learnt clause plus its antecedent `ClauseId` chain to `ProofSink::learn` — the LRAT hint is harvested from the antecedent walk we already perform, so it costs no extra traversal.
- Return the learnt clause and the second-highest decision level in it as the backjump target.

### 5.4 `add_learnt`

Computes LBD (number of distinct decision levels in the clause — its glue), stores it in the header for `reduce`, installs watches, and registers the clause with a fresh stable `ClauseId`. A unit learnt clause backjumps to level 0.

### 5.5 Soundness guard rails

A `decision_level == 0` conflict ⇒ `Unsat`. Analysis touches only assigned literals. Every `enqueue` records a `Reason`, so the implication graph is always fully explainable. `debug_assert!`s on trail consistency, watched-literal invariants, and level monotonicity are compiled out of release but exhaustively checked in test/fuzz (north-star §10).

---

## 6. Branching, Restarts & Reduction

### 6.1 Branching — `BranchHeuristic` trait, VMTF and EVSIDS

```rust
trait BranchHeuristic {
    fn new_var(&mut self, v: Var);
    fn on_conflict(&mut self);              // decay / bump bookkeeping
    fn bump(&mut self, v: Var);             // called during analyze
    fn next(&mut self, assign: &Assignment) -> Option<Var>;  // unassigned var of max priority
    fn on_unassign(&mut self, v: Var);      // re-insert into the order on backtrack
}
```

- **VMTF** (Variable Move-To-Front): integer-only, deterministic, no float decay churn — valuable for SMT replay and differential testing.
- **EVSIDS** (exponential VSIDS): float activities with rescaling; the common industrial default.

Both are implemented from the start and selected at the **type level**: the solver is generic over `H: BranchHeuristic`, the concrete heuristic is fixed at construction (§8.4), and so `next`/`bump` are monomorphized with zero dispatch. **Phase saving** lives alongside the heuristic: `Assignment::phase` records each var's last assigned polarity, and `decide()` re-uses it as the branching sign.

### 6.2 Restarts — `RestartPolicy`, Luby and EMA

Two policies behind one `RestartPolicy`, selectable by config: the **Luby** sequence (deterministic, theory-friendly) and **Glucose-style EMA** (fast/slow LBD moving averages trigger a restart when recent learnt-clause quality drops). Restarts unwind only to the assumption prefix (§7), never below it.

### 6.3 Clause-DB reduction — LBD-based

Learnt clauses carry their LBD (glue). Periodically (`reduce_interval`), the learnt half of the database is sorted by glue and the worst half discarded, **always keeping glue ≤ `lbd_keep_threshold` (default 2)** and never deleting a clause that is currently a reason on the trail. Each deletion calls `ProofSink::delete` with the clause's stable `ClauseId`, then the arena is compacted and live `ClauseRef`s are updated.

---

## 7. Incrementality: Assumptions, Cores, push/pop

Per north-star §8.1, **assumptions are the primary incremental mechanism** (empirically faster on more benchmarks than push/pop, and the native shape of DPLL(T)). push/pop is a thin scoped overlay on one persistent instance — never solver re-creation.

### 7.1 Assumptions — `solve_under(assumptions: &[Lit])`

- Assumption literals become the **first decision literals**, one per decision level, before the heuristic picks anything; each gets its own level so a failed one is isolated.
- If an assumption is already falsified at enqueue time, or a conflict arises at the assumption-prefix levels, control transfers to `analyze_final` (§7.2) rather than normal `analyze`.
- `decide()` therefore pulls from the assumption list first, then defers to the `BranchHeuristic`.

### 7.2 `analyze_final` — failed-assumption core

- Walk the conflict's reason graph collecting the decision-level-0 and assumption literals that jointly entail the conflict (seen-marked).
- Return the minimal set of assumptions that are jointly inconsistent. This is the mechanism `shinri-solver` surfaces as `get-unsat-core` and the failed core for `check-sat-assuming`.
- Result shape: `enum SolveResult { Sat, Unsat { core: Vec<Lit> } }`, where `core` is empty for an unconditional UNSAT.

### 7.3 push/pop — scoped overlay

- `push()` / `pop(n)` mark scopes. A scope records the high-water marks of the `new_var` count, the input-clause count, and the heuristic/phase state needed to restore cleanly.
- `pop` removes clauses added in the popped scope (calling `ProofSink::delete` with their stable `ClauseId`), truncates the var tables, and discards learnt clauses that may depend on popped input clauses. **Phase 1 takes the conservative, obviously-sound route: drop all learnt clauses whose scope tag is ≥ the popped level.** Selective `weaken`/restore is explicitly a Phase 2 item (north-star §13). Correctness over cleverness.
- **This is a deliberate, non-hot-path choice, not deferred performance.** The optimized incremental mechanism in Phase 1 is *assumptions* (§7.1), which retain *all* learnt clauses across solves and are the mechanism the SMT-COMP incremental track (`check-sat-assuming`) exercises. `weaken`/restore only benefits *nested push/pop*-heavy workloads, where it is a known soundness-bug surface (it interacts with the proof chain) — hence its Phase 2 staging.
- One `Solver` instance lives across the whole push/pop session.

### 7.4 Trail interaction

Assumptions and push/pop both compose with the trail's `level_starts`, and the theory's `push`/`pop` (§8) are driven in lockstep with the SAT decision levels so Boolean and theory state unwind together — the load-bearing invariant for CDCL(T) incrementality. Restarts unwind only to the assumption prefix, so assumptions stay fixed across restarts within one `solve_under` call.

---

## 8. The Seams: `Theory`, `ProofSink`, Config

### 8.1 The `Theory` seam (the T in CDCL(T))

`Solver<T: Theory, P: ProofSink, H: BranchHeuristic>`. The `Theory` trait is defined in `shinri-sat` (the SAT crate owns the calling contract); `shinri-theory` implements it. It is the SAT-facing mirror of the richer trait in north-star §6.2.

```rust
pub trait Theory {
    fn assert(&mut self, lit: Lit);                              // a Boolean lit hit the trail
    fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Conflict>;
    fn explain(&mut self, just: TheoryJust, out: &mut Vec<Lit>); // lazy; recomputed in analyze
    fn check(&mut self, effort: Effort) -> TheoryResult;         // Standard | Full (final check)
    fn push(&mut self);
    fn pop(&mut self, n: usize);
    fn new_var(&mut self, v: Var);                               // keep theory var tables in sync
}

pub enum Effort { Standard, Full }
pub enum TheoryResult { Sat, Conflict(Conflict), Lemma(/* clause */) }
```

Key points:

- **Zero-cost when off.** `NoTheory` is a ZST whose every method inlines to nothing; with `Solver<NoTheory, NoProof, _>` the theory branches in `propagate`/`analyze`/`search` dead-code-eliminate, leaving a pure CDCL SAT solver. Same pattern validated by `NoProof` in core.
- **Caller-owned output buffers** (`&mut Vec<…>`) rather than returned `Vec`s, keeping the hot path allocation-free (the lazy-explanation rationale of §6.2).
- **`check(Full)`** is invoked at the all-Boolean-assigned point *before* `Sat` is declared: a theory may reject a Boolean-complete model and return a conflict/lemma, which keeps the search going. This is what makes the "first runnable QF_UF solver" (north-star §12 step 3) a drop-in `Solver<EufTheory, _, _>`.
- **Final-check fixpoint.** `Sat` is returned only when Boolean BCP, theory propagation, and `check(Full)` all reach joint fixpoint with no new lemma.

### 8.2 `ProofSink` threading

`P: ProofSink` (from `shinri-core`) is threaded through exactly three call sites already in the loop: `input` on clause add, `learn(lits, chain)` from `analyze`, and `delete` on reduction/pop. Default `NoProof`. The stable `ClauseId` assigned at clause creation survives arena relocation, so proof identity is stable even as `ClauseRef` moves.

### 8.3 Why the seams are designed in now

Retrofitting a theory-callback interface into a finished CDCL hot loop is the one-way-door rewrite that north-star §14.6 warns about. Threading the (inert) generics through `propagate`/`analyze`/`search` now costs nothing at runtime and avoids that rewrite when `shinri-theory` lands.

### 8.4 Config & heuristic selection

The branching heuristic is the **generic type parameter** `H: BranchHeuristic`, not a runtime field — it is fixed at construction, so `next`/`bump` are fully monomorphized with **zero dispatch on any path**. Selecting a heuristic from a CLI flag is a single **outer `match`** that constructs the right `Solver<_, _, H>` monomorphization; everything inside is specialized. The differential harness constructs `H = Vmtf` and `H = Evsids` directly.

Remaining runtime knobs live in a plain value struct:

```rust
struct SolverConfig {
    restart:             RestartKind,   // Luby | EmaGlucose
    reduce_interval:     u32,
    lbd_keep_threshold:  u32,           // default 2
    random_seed:         u64,
    // …additional tuning knobs added as profiling demands
}
```

*Trade on record:* the generic `H` adds a third type parameter to `Solver`'s signature (cosmetic verbosity + modestly more monomorphized code/compile time) in exchange for **zero heuristic-dispatch cost on every path**. Chosen deliberately for this performance-sensitive core over a runtime enum wrapper. (`RestartKind` stays a runtime enum: the restart policy is consulted only once per conflict — far colder than branching — so it does not warrant a generic.)

---

## 9. Error Handling & Soundness Discipline

- **Conservative by construction.** Resource exhaustion (timeout / memory budget) yields `unknown`, never a guess — safe under SMT-COMP scoring.
- **`Result` for recoverable input errors** (e.g. malformed DIMACS in the test/feature reader); **panics reserved for genuine invariant violations** (broken trail/watch invariants should crash in debug/test, never silently return a wrong answer).
- **Internal self-check.** Every `Sat` is re-validated — the returned assignment is evaluated against *all* clauses before it leaves the solver. Every `Unsat` carries a checkable certificate (resolution/DRAT trace; the failed-assumption core for the incremental case).
- **Debug-only invariant assertions** on trail consistency, watched-literal invariants, and decision-level monotonicity, compiled out of release and exhaustively exercised in test/fuzz.

---

## 10. Testing & Verification Strategy

Differential testing is the spine (north-star §11). A standalone SAT core makes this unusually tractable.

1. **Unit tests (per module).** Watched-literal maintenance (find-new-watch, unit detection, conflict); 1-UIP on hand-built implication graphs with known UIPs; minimization drops exactly the redundant literals; LBD computation; trail backtrack restores `value`/`level`/`phase`; clause-arena pack/relocate round-trips; assumption levels and `analyze_final` core extraction; VMTF and EVSIDS order invariants.

2. **Property tests (`proptest`).**
   - *Model soundness (existential):* every `Sat` result satisfies every clause — re-evaluated independently. Also wired as an always-on internal self-check before any `Sat` is returned (§9).
   - *Learned-clause entailment:* each learnt clause is implied by the current DB (resolution chain re-checked).
   - *UNSAT certificate:* emit a DRAT/resolution trace, checked by a from-scratch checker (no external dep) on small instances.
   - *Core genuineness:* the `analyze_final` assumption core is itself UNSAT, and dropping any one literal makes it SAT (minimality).
   - *Incremental equivalence:* `solve_under(A)` then `solve_under(B)` agrees with two fresh solves; push/pop agrees with rebuild-from-scratch.

3. **Differential / oracle (dev-only).** A `#[cfg(any(test, feature = "dimacs"))]` DIMACS reader feeds: random 3-SAT around the phase transition (clause/var ratio ≈ 4.26), structured CNF (pigeonhole, XOR chains), and SATLIB / competition files. Run shinri-sat vs a pinned pure-Rust reference solver (splr / varisat / batsat) as a dev-dependency; **any SAT/UNSAT disagreement is a P0 bug.** On `sat`, both models are independently validated; on `unsat`, shinri's certificate is checked. Run across all config combinations (VMTF/EVSIDS × Luby/EMA) so a heuristic-specific bug cannot hide.

4. **Fuzzing (`cargo-fuzz`).** (a) the DIMACS reader never panics on malformed input; (b) a structured CNF generator → solver, cross-checked against the oracle to hunt soundness bugs; (c) a randomized incremental command sequence (add / solve / push / pop / assume) cross-checked against rebuild-from-scratch.

5. **Mutation testing (`cargo-mutants`)** on `analyze`, `propagate`, watched-literal maintenance, and `analyze_final` — confirm the suite kills behavioral mutants in the soundness-critical routines.

6. **CI gates** (matching the repo's bar): `cargo nextest`, `cargo deny check` (proves the oracle stayed dev-only and no FFI/native dep crept in), `cargo clippy -D warnings`, `cargo fmt --check`. Differential + fuzz run on a longer scheduled budget.

7. **Determinism.** Integer-only VMTF plus a fixed `random_seed` make runs bit-reproducible — differential-test failures replay exactly.

---

## 11. Build Order (incremental, always-runnable)

Each step leaves a sound, testable artifact. This feeds the implementation plan (writing-plans).

1. **Ids/state scaffolding:** `Assignment`, `Trail`, `ClauseDb` (arena + `ClauseRef`), `Watches` — with unit tests and the test-gated DIMACS reader.
2. **Boolean BCP + decisions + backtracking:** a DPLL loop (no learning yet) that is already differential-testable on satisfiable instances.
3. **Conflict-driven learning:** 1-UIP `analyze`, learnt-clause install, non-chronological backjump → a complete CDCL solver. First differential gate vs the oracle on full SAT/UNSAT.
4. **Minimization + LBD reduction + restarts + phase saving:** the §5–§6 quality machinery; re-run the differential corpus across configs.
5. **Branching heuristics behind the trait:** VMTF then EVSIDS, selected at the type level via the generic `H` (one outer `match` to pick the monomorphization).
6. **Incrementality:** assumptions + `analyze_final` core; then the scoped push/pop overlay.
7. **The seams wired through:** `Theory` trait + `NoTheory`, `ProofSink` threading through add/learn/delete. Confirm `Solver<NoTheory, NoProof, Vmtf>` monomorphizes to a pure CDCL solver with the theory/proof branches eliminated.
8. **Hardening:** fuzz targets, mutation testing, CI gates.

**Gate:** `shinri-sat` is "done" for Phase 1 when it passes the differential/fuzz/mutation regime across all configs as a standalone SAT solver, and `Solver<NoTheory, NoProof, Vmtf>` carries provably zero theory/proof overhead — ready for `shinri-theory` (step 3, the first runnable QF_UF solver) to drop in as `T`.

---

## Appendix A — Key References

- Nieuwenhuis, Oliveras, Tinelli. *Solving SAT and SAT Modulo Theories: From an Abstract DPLL Procedure to DPLL(T).* JACM 2006.
- Moskewicz, Madigan, Zhao, Zhang, Malik. *Chaff: Engineering an Efficient SAT Solver.* DAC 2001. (two-watched-literals)
- Eén, Sörensson. *An Extensible SAT-solver (MiniSat).* SAT 2003. (CDCL architecture, 1-UIP, incremental assumptions)
- Sörensson, Biere. *Minimizing Learned Clauses.* SAT 2009. (recursive / self-subsuming minimization)
- Audemard, Simon. *Predicting Learnt Clauses Quality in Modern SAT Solvers (Glucose).* IJCAI 2009. (LBD, EMA restarts)
- Biere, Fröhlich. *Evaluating CDCL Variable Scoring Schemes.* SAT 2015. (VMTF vs VSIDS/EVSIDS)
- Luby, Sinclair, Zuckerman. *Optimal Speedup of Las Vegas Algorithms.* 1993. (Luby restart sequence)
- Biere. *Two strong restart heuristics: Luby and EMA.* (Glucose-EMA scheduling)
