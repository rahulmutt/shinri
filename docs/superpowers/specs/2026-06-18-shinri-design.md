# shinri — Design Specification

**A modern, pure-Rust, high-performance SMT solver**

- **Date:** 2026-06-18
- **Status:** Approved design — ready for implementation planning
- **Scope of this document:** North-star architecture for the whole solver, plus a build-ready Phase 1 specification.

---

## 1. Vision & Competitive Thesis

shinri is a from-scratch SMT solver written in pure Rust, with no native (C/C++/FFI) dependencies in its shipping build. Its long-term ambition is to compete with Z3, cvc5, Bitwuzla, Yices2, and other major solvers — but it pursues that ambition through a realistic, multi-phase engineering program rather than a day-one frontal assault.

**The competitive landscape is not winner-take-all.** It is a federation of per-logic fiefdoms with one breadth incumbent:

- **Z3** — universal baseline; covers everything, wins few crowns, ~5× slower than Bitwuzla on commonly-solved instances. Beatable per-logic.
- **cvc5** — broadest *winner*; strings, quantifiers, proofs.
- **Bitwuzla** — dominates bit-vectors and floating-point.
- **Yices2** — speed leader on QF_UF and difference logic.
- **OpenSMT** — leads QF_LRA / QF_LIA.

**SMT-COMP scoring is soundness-first and lexicographic:** a single wrong answer (`sat` where `unsat`, or vice-versa) sinks an entire division, while returning `unknown` is always safe. This structurally rewards a young, correct, conservative solver and punishes corner-cutting.

**shinri's competitive thesis:** provable soundness + memory safety + a clean incremental architecture + a fast core, entering where the algorithms are textbook-clean and the incumbents are beatable by engineering quality rather than by reproducing decades of heuristic tuning. First place in a major division is *not* the Phase 1 goal; *sound, complete, competitive coverage* of QF_UF + QF_LRA is.

The pure-Rust mandate is a real constraint: it forbids the fastest bignum (GMP/`rug`) and the fastest SAT backends (Kissat/CaDiCaL via FFI). shinri's answer is not raw-speed parity but **soundness, memory safety, a clean incremental architecture, fast parsing, and being the first credible pure-Rust SMT solver.**

---

## 2. Design Principles

1. **Soundness is existential.** Any internal uncertainty, resource exhaustion, or unsupported construct yields `unknown`, never a guess. Conservative by construction.
2. **Index/arena over smart pointers.** Terms, sorts, clauses are referred to by small copyable `u32`-based ids into central arenas. No `Rc`/`RefCell`/`Arc` on terms — porting C++ refcounting is an anti-pattern (refcount churn, borrow-checker friction, cache-hostility).
3. **Trail + undo-log backtracking.** Never persistent data structures or snapshotting.
4. **Design the one-way doors in now.** Interfaces and hooks for proofs, incrementality, model generation, parallelism, E-matching, and MCSat are designed in Phase 1 so they cost nothing when off but are not a rewrite to enable later. Build full machinery only when its phase arrives.
5. **Clean crate boundaries enforce the architecture.** The crate dependency graph is one-directional; lower layers cannot reach into upper layers. This mechanically prevents the "two overlapping cores" complexity that is Z3's scar tissue.
6. **Pure Rust, enforced.** No native-link dependencies in the shipping build; `cargo deny` enforces it in CI.

---

## 3. System Architecture

A Cargo workspace of focused crates with strictly one-directional dependencies.

```
shinri/                         (workspace root: mise.toml, devenv.nix, deny.toml)
├── crates/
│   ├── shinri-num         # from-scratch SMT-tuned bignum + rational: inline small-value
│   │                      #   storage, schoolbook+Karatsuba mul, binary/Lehmer GCD. No deps.
│   ├── shinri-core        # term/sort interning DAG, ids, arena, trail/undo-log,
│   │                      #   Rational abstraction (over shinri-num), ProofSink trait.
│   ├── shinri-sat         # CDCL SAT core: incremental + assumptions, watched literals,
│   │                      #   1-UIP analysis, VMTF/EVSIDS, restarts. Depends on core.
│   ├── shinri-theory      # Theory trait + DPLL(T) orchestration + Nelson-Oppen combination
│   ├── shinri-euf         # congruence closure + proof forest (the shared equality hub)
│   ├── shinri-arith       # difference logic + Dutertre-de Moura simplex (LRA)
│   ├── shinri-parser      # SMT-LIB 2.6: logos lexer + recursive-descent, interns directly
│   ├── shinri-solver      # top-level Solver API (THE embeddable library crate)
│   └── shinri-cli         # thin binary over shinri-solver: SMT-LIB stdin/file, flags
├── fuzz/                  # cargo-fuzz targets
└── tests/                 # integration + differential harness, benchmark runner
```

**Dependency direction:** `num` ← `core` ← `sat` ← `theory` ← `{euf, arith}` ← `solver` ← `cli`; `parser` depends on `core` and feeds `solver`. No cycles. `shinri-num` has zero dependencies; `shinri-euf` literally cannot reach into the SAT core internals.

**Why crates, not modules:** the crate graph mechanically enforces the architectural one-way doors, gives independent compilation/testing, and makes "is this still pure-Rust?" a `cargo tree` query.

### 3.1 Dependency policy (pure-Rust mandate)

A workspace-level `deny.toml` (cargo-deny) bans native-link crates: `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`, `rustsat-{cadical,kissat,glucose,minisat}`. CI runs `cargo deny check`. The shipping dependency surface is deliberately tiny and fully permissive (MIT/Apache): the bignum/rational stack is the in-house `shinri-num`, so there is **no** `malachite` (LGPL) or `num-bigint` in the shipping build.

**Dev-only oracle exceptions** — permitted **only** as `dev-dependency` behind a feature flag, never in the shipping build:
- `z3.rs` / `easy-smt` — differential-testing oracle for the solver.
- `num-bigint` / `num-rational` — differential-testing oracle for `shinri-num`.

### 3.2 Toolchain

- **`mise.toml`** pins the Rust toolchain (stable channel, pinned version) and dev tools: `cargo-fuzz`, `cargo-mutants`, `cargo-deny`, `cargo-nextest`.
- **`devenv.nix`** provides a reproducible dev shell and anything not cleanly expressible in mise. The solver itself stays pure-Rust.

---

## 4. Core Data Model (`shinri-core`)

### 4.1 Term & sort representation — hash-consed immutable DAG, index-based

One owning `Context` holds the arenas; everything else refers to terms by small copyable ids.

```rust
#[repr(transparent)] struct TermId(NonZeroU32);   // Option<TermId> stays 4 bytes
#[repr(transparent)] struct SortId(NonZeroU32);
#[repr(transparent)] struct SymbolId(u32);

enum TermNode {                       // fixed-size; children stored out-of-line
    Const(SymbolId, SortId),
    App { func: SymbolId, args: ChildSlice, sort: SortId },  // ChildSlice = (offset, len)
    Var(DeBruijn, SortId),            // reserved for later quantifier support
    // Quant(...) reserved for Phase 4
}

struct Context {
    nodes:    Vec<TermNode>,                       // the arena; ids index into this
    children: Vec<TermId>,                         // shared out-of-line child storage (SoA)
    interner: FxHashMap<StructuralKey, TermId>,    // structural dedup -> maximal sharing
    sorts:    Vec<SortNode>,
    sort_interner: FxHashMap<SortKey, SortId>,
    symbols:  StringInterner,                      // symbol text -> SymbolId (u32)
}
```

**Properties this buys:**
- **O(1) structural equality** — compare ids.
- **Maximal sharing** — the interner guarantees one node per distinct subterm.
- **Cache density** — fixed-size nodes, children stored out-of-line (struct-of-arrays), `FxHashMap`/`ahash` (never SipHash). `NonZeroU32` newtypes keep `Option<Id>` at 4 bytes.

Terms are write-once and never individually freed during a solve, so a growable `Vec` *is* the arena — no `bumpalo`/`slotmap` needed for the term core.

**Sorts are interned too** (`SortId`). SMT-LIB sorts form a small algebra (`Bool`, `Int`, `Real`, indexed `(_ BitVec n)`, `(Array I E)`, user-declared) compared constantly during well-sortedness checking.

**Side tables, keyed by id.** Proof metadata, parallel/partition metadata, and (Phase 4) E-matching indices live in side tables keyed by `TermId`/`ClauseId` — never bloating the hot node struct.

**Id-space decision:** `u32` ids cap a solve at ~4 billion distinct terms/clauses — universally sufficient for SMT, deliberately chosen for cache density.

### 4.2 Backtracking — trail + undo-log

A single trail (`Vec`) with decision-level markers. Each theory registers backtrackable mutations as tagged entries on a generic undo-stack (`Vec<UndoAction>` with scope markers) synchronized to SAT decision levels. `pop(n)` replays undos and is O(work-undone). This matches Z3/cvc5/Bitwuzla, is cache-friendly, and sidesteps `RefCell`.

### 4.3 `Rational` abstraction

`Rational` is a trait, not a concrete type, with an **i128 fast-path + overflow→bignum fallback** so the hot arithmetic path stays unboxed until coefficients actually overflow. The bignum/rational fallback is the in-house `shinri-num` crate. See §7.

### 4.4 `ProofSink` trait

A zero-cost generic `ProofSink` trait with a `NoProof` default is threaded through clause add/delete/learn from day one (see §8.2). Costs nothing when proofs are off.

---

## 5. SAT Core (`shinri-sat`)

A CDCL solver built from scratch. No reusable pure-Rust core fits: splr dropped incremental+assumptions (v0.18) and is MPL; batsat is unmaintained and ~20% C; the fast rustsat backends are forbidden FFI. We mine their *ideas* (splr's heuristics, batsat's `Theory` trait, varisat's proof emission) and own the code.

**Phase 1 feature set:**
- **Two-watched-literals with an inline blocking literal** in each watch entry — the single biggest cache-miss reducer.
- **1-UIP conflict analysis** with **recursive / self-subsuming clause minimization** (Sörensson–Biere; ~30% clause shrink).
- **VMTF branching** (integer-only → deterministic and reproducible, valuable for SMT replay; EVSIDS is the alternative), **phase saving**, **LBD-based clause-DB reduction** (keep glue ≤ 2), **Luby + Glucose-EMA restarts**.
- **Incremental solving with assumptions from day one.** Assumptions are the first decision literals; `analyzeFinal` extracts the failed-assumption core.

**Deliberately deferred to Phase 2+:** heavy inprocessing (BVE, vivification), chronological backtracking, stable/focused mode switching — high bug surface, interact badly with incrementality, low payoff on theory-atom-dominated SMT trails. Any future inprocessing is gated behind a **frozen-variables** set so the theory layer can protect its atoms.

**Performance note:** hot propagation/analysis loops may use audited `get_unchecked` (bounds-checking costs 5–15% there), confined to small, individually-justified `unsafe` blocks — never scattered.

---

## 6. DPLL(T) Engine & Theory Solvers

### 6.1 Engine choice — DPLL(T)/CDCL(T), not MCSat

DPLL(T) is the proven industrial spine (Z3, cvc5, MathSAT, Yices2-default) and maps cleanly onto a Rust trait boundary. The abstract DPLL(T) calculus (Nieuwenhuis–Oliveras–Tinelli, JACM 2006) gives rule-level soundness proofs that translate into a small set of validatable invariants. MCSat's only decisive advantage is on nonlinear/algebraic theories (out of Phase 1 scope), and its cost is heavy (per-theory finite-basis `explain` needs real CAD machinery).

**MCSat-hostable later:** the trail abstraction is designed so it can eventually carry first-order value assignments (not just Boolean), and the parser/term layers stay engine-agnostic. MCSat becomes an alternative Phase-5 engine for QF_NRA, hosted behind the same layers — never blended into the CDCL(T) core.

### 6.2 Theory trait (`shinri-theory`)

A closed-set `Theory` trait, **enum-dispatched (not `dyn`)** in Phase 1 for monomorphization and inlining. The theory set is small and known; performance is existential.

```rust
trait Theory {
    fn assert(&mut self, lit: Lit);
    fn check(&mut self, effort: Effort) -> TheoryResult;          // Standard | Full
    fn propagate(&mut self) -> Vec<(Lit, ExplanationToken)>;      // theory propagation
    fn explain(&mut self, tok: ExplanationToken) -> Vec<Lit>;     // lazy: recomputed on conflict
    fn push(&mut self);
    fn pop(&mut self, n: usize);
    fn model(&self, m: &mut ModelBuilder);
}
```

- **Lazy explanations:** `propagate` returns a cheap token; the full explaining clause is reconstructed by `explain` only if conflict analysis touches that propagation. Keeps the hot path allocation-free.
- **Exhaustive theory propagation** is in from the start — it is the first real performance win (cheap, high-value for EUF and difference logic).
- Mirrors OpenSMT's EL/ES/ET separation of concerns.

### 6.3 EUF — congruence closure (`shinri-euf`)

**Nieuwenhuis–Oliveras incremental congruence closure** (*Fast Congruence Closure and Extensions*, Inf. & Comp. 2007): curry to binary `apply`, flatten to depth-2 (`a=b` or `f(a,b)=c`), then the five structures — Pending, Representative, ClassList, UseList, Lookup — with union-by-size. A **proof forest** (edge-labeled, path-reversal on union) gives `Explain` in O(k) for minimal, proof-producing conflict explanations.

- **Disequalities:** store `(Id, Id)` pairs + a per-representative index, watch-list style, checked on each merge.
- **Optimization:** timestamp the Lookup table rather than rolling it back on pop.
- **Merge-event hooks** are exposed from day one — load-bearing for Phase 4 E-matching; retrofitting later is a rewrite. Cost nothing when off.
- We adopt egg's *deferred-rebuild batching* idea internally but do **not** use the egg crate (it is saturation-shaped: no backtracking, no disequality conflicts — wrong abstraction for DPLL(T)).

EUF is also the **shared equality hub** for arrays/strings/E-matching in later phases.

### 6.4 Difference logic (`shinri-arith`, IDL/RDL)

**Incremental negative-cycle detection** (incremental Bellman-Ford / SSSP) on a constraint graph. The cheapest competitive theory and a clean stepping-stone between EUF and full simplex; QF_IDL/QF_RDL are tractable divisions obtained nearly for free once the constraint-graph machinery exists.

### 6.5 Linear real arithmetic — simplex (`shinri-arith`, LRA)

**Dutertre–de Moura general simplex** (*A Fast Linear-Arithmetic Solver for DPLL(T)*, CAV 2006) — the de-facto LRA core in every major solver:

- Tableau `A·x = 0` + per-variable bounds; basic/nonbasic split; pivot-and-update.
- **Bland's rule** anti-cycling (baseline), then **Sum-of-Infeasibilities + heuristic pivoting** (King–Barrett–Dutertre, FMCAD 2013) as a follow-on once the baseline is sound.
- **Delta-rationals `(c, k)`** for strict inequalities. The strict/non-strict encoding is a frequent off-by-one soundness bug site → dedicated property tests.
- **Farkas certificate** from the infeasible row → minimal conflict clause back to the SAT core.

### 6.6 Theory combination — QF_UFLRA

**Nelson–Oppen with model-based equality propagation** (de Moura–Bjørner) over a **central single shared Equality Engine** (cvc5-style) to minimize cross-theory plumbing bugs. General Delayed Theory Combination is deferred.

**Caveats on record (heavy differential testing applies):** Nelson–Oppen requires stable-infiniteness + disjoint signatures; model-based combination is a known soundness-bug source; producing minimal, relevant theory conflict explanations is theory-specific engineering and exactly where naive implementations underperform.

---

## 7. Exact Arithmetic — `shinri-num` (from scratch)

Float in a theory core is a **soundness bug, full stop.** Everything is exact rationals. The pure-Rust mandate forbids GMP (`rug`), and general pure-Rust bignums (`num-bigint`, `malachite`) are either slower, heap-eager, or copyleft. Rather than depend on one, shinri builds **`shinri-num`**: a from-scratch big-integer + rational library tuned for *exactly* the operations this solver performs and nothing else. This is the place the pure-Rust mandate costs the most, so it is the place a focused, workload-specific implementation pays back the most.

### 7.1 Why from scratch is justified here

The SMT arithmetic workload has a narrow, exploitable shape that general libraries do not optimize for:
- **Magnitudes are usually small.** In Dutertre–de Moura simplex, coefficients overwhelmingly fit in 64–128 bits; bignum is the *fallback* for occasional coefficient blowup, rarely astronomically large.
- **GCD dominates, not multiplication.** Rationals normalize on essentially every operation, so GCD is the hot path. General libraries optimize large-operand multiplication we rarely hit.
- **The operation set is tiny and closed:** add, sub, mul, compare, `divrem`, GCD, and rational normalize. No need for the hundreds of functions GMP/FLINT ship.

A library that assumes "mostly small, occasionally medium, rarely huge, GCD-heavy, allocation-averse" can beat general-purpose crates *on this workload* while being a fraction of their code — and it makes the entire shipping stack permissive pure-Rust.

### 7.2 Representation

- **`Integer`:** an inline small-value representation — a sign + a small inline limb buffer (e.g. up to 2 limbs / 128 bits stored inline, **no heap allocation**), spilling to a heap `Vec<u64>` of limbs only when the value genuinely exceeds the inline capacity. This is the single biggest win over `num-bigint` (which heap-allocates eagerly). Normalized (no leading zero limbs; canonical zero).
- **`Rational`:** a `{ numer: Integer, denom: Integer }` kept in canonical form (denominator > 0, `gcd(numer, denom) = 1`). The concrete fallback type behind the `Rational` trait of §4.3; the i128 fast-path in the theory layer means most operations never construct one.
- **`DeltaRational`:** `(Rational, Rational)` pair `(c, k)` for the simplex `c + k·δ` strict-inequality encoding (§6.5), built on the above.

### 7.3 Algorithms (SMT-tuned scope)

- **Addition/subtraction:** limb-wise with carry/borrow via `u128` widening (or `core::arch` add-carry intrinsics where they win), inline fast path for ≤128-bit operands.
- **Multiplication:** schoolbook for small operands; **Karatsuba** above a tuned crossover. Toom-Cook and Schönhage-Strassen/FFT are **deliberately deferred** — the SMT workload rarely reaches their crossover; they are added only if profiling proves a need.
- **Division/remainder:** Knuth Algorithm D (schoolbook long division) with a fast path for single-limb and ≤128-bit divisors. Burnikel-Ziegler divide-and-conquer division deferred (same rationale as Toom-Cook).
- **GCD (the hot path):** **binary GCD** for small operands and **Lehmer's GCD** for larger ones — chosen because rational normalization makes GCD the most-executed bignum routine. Half-GCD deferred.
- **Comparison:** branch-light, limb-count then limb-wise.

### 7.4 Correctness regime (a bignum bug is a soundness bug)

`shinri-num` is held to the strictest testing in the project (see §11): exhaustive property tests of algebraic laws, **differential testing of every operation against `num-bigint`/`num-rational` as a dev-only oracle**, fuzzing of the limb-level routines, and `cargo-mutants` on the core algorithms. It is never trusted to decide a `sat`/`unsat` until it provably agrees with the reference across the fuzz/differential corpus.

### 7.5 Coefficient-blowup mitigation in the simplex

Independently of the bignum: the simplex tableau uses an **integer-rows-with-shared-denominator** representation rather than per-cell rationals, which is the primary defense against rational coefficient blowup during pivoting. `shinri-num` makes the per-row integer operations fast; the representation keeps the operands small.

---

## 8. Cross-Cutting Capabilities

All four are architected from day one (interfaces + hooks cost nothing when off); full machinery is built when its phase arrives.

### 8.1 Incrementality
- **Assumptions + `check-sat-assuming`:** fully implemented in Phase 1 (it is how DPLL(T) works internally). Preferred over push/pop (empirically faster on far more benchmarks).
- **`push`/`pop`:** a thin scoped overlay on one persistent solver instance (level-marked clause DB + theory undo-logs), never solver re-creation.

### 8.2 Proof production
- A zero-cost generic **`ProofSink` trait with a `NoProof` default**, threaded through clause add/delete/learn from day one; stable global **`ClauseId`** on every clause; active/`weaken` flags.
- Theories already produce explanations (EUF proof forest; LRA Farkas certificates).
- **Emission** of proof artifacts (**Alethe** format, checkable by the Rust **Carcara** checker) plus native LRAT hints from the SAT layer is **Phase 2** — but the seams are in now.

### 8.3 Model generation
- Each theory implements `model(&mut ModelBuilder)`; the combination layer assembles a complete assignment. Implemented in Phase 1 (needed for `get-model` / `get-value` and the model-validation track).

### 8.4 Parallelism-readiness
- **Design only** in Phase 1: clean ownership boundaries, assumption/decision-state hooks, global clause provenance.
- Actual orchestration (cube-and-conquer / portfolio as a crate over the sequential API) is **Phase 5**. The sequential SMT-COMP score gives parallelism zero benefit, so it is never a substitute for a good core — only an additive later layer.

---

## 9. Frontend & CLI

### 9.1 SMT-LIB 2.6 frontend (`shinri-parser`)
**`logos` lexer + hand-written recursive-descent** over S-expressions. The parser **interns directly** — symbols become `SymbolId`, terms become interned `TermId` during parsing, with well-sortedness checked inline. (Opportunity: beat cvc5's "unacceptably slow" ANTLR3 parser on large files.)

Phase 1 command set: `set-logic`, `declare-sort`, `declare-fun`, `define-fun`, `assert`, `check-sat`, `check-sat-assuming`, `push`, `pop`, `get-model`, `get-unsat-core`, `get-value`, `set-option`, `exit`.

### 9.2 CLI (`shinri-cli`)
Thin binary over `shinri-solver`: reads SMT-LIB 2 from file or stdin; competition-compatible output (`sat`/`unsat`/`unknown`); flags for proof/model/core emission; resource limits (timeout, memory). The library does the work; the CLI is I/O + a command loop.

---

## 10. Error Handling & Soundness Discipline

- **Conservative by construction:** any internal uncertainty, resource exhaustion, or unsupported construct → `unknown`. Never a guess. `unknown` is always safe under SMT-COMP scoring.
- **`Result`-based handling** for recoverable frontend errors (parse errors, unsupported logic → reported, not panicked).
- **Panics reserved for genuine invariant violations** — a broken internal invariant should crash in debug/test, not silently return a wrong answer.
- **Debug-only invariant assertions** (`debug_assert!`) on hot invariants (trail consistency, watched-literal invariants, tableau well-formedness) — compiled out of release, exhaustively checked in test/fuzz.

---

## 11. Testing & Verification Strategy

The spine is **differential testing against oracle solvers from day one** — the primary mitigation for the from-scratch soundness failure modes (simplex delta-rational off-by-ones, congruence-closure disequality edges, exact-arithmetic bugs).

1. **Unit tests** — per-crate, on tricky invariants: watched-literal maintenance, 1-UIP analysis, congruence-closure merge/explain, simplex pivot correctness, delta-rational strict inequalities, interner dedup, and `shinri-num` limb-level edge cases (carry/borrow boundaries, inline↔heap spill, Karatsuba crossover, GCD with zero/one operands).
2. **Property-based tests (`proptest`):**
   - *Term layer:* structural equality ⇔ id equality; sort-checking soundness.
   - *SAT core:* learned clauses are entailed; returned models satisfy all clauses; UNSAT cores are genuinely unsatisfiable.
   - *Theories:* returned models satisfy every asserted literal; every conflict clause is genuinely theory-inconsistent (certificate independently re-checked).
   - *Round-trip:* parse → print → parse is identity on the term DAG.
3. **Differential / oracle testing** — two layers, both dev-only:
   - *Solver:* random well-typed SMT-LIB in Phase 1 logics, shinri vs Z3/cvc5 (`z3.rs`/`easy-smt`). **Any sat/unsat disagreement is a P0 bug.** `unknown` is never a failure.
   - *`shinri-num`:* every arithmetic operation checked against `num-bigint`/`num-rational` on a large random + fuzz corpus. The bignum is not trusted in the solver until it provably agrees with the reference (§7.4).
4. **Fuzzing (`cargo-fuzz`):** (a) parser/frontend — never panic on malformed input; (b) structured semantic fuzzing — grammar-driven formulas through the solver differential harness to hunt soundness bugs; (c) `shinri-num` limb-level routines — fuzzed operands cross-checked against the `num-bigint` oracle.
5. **Self-checking:** every `sat` result is internally re-validated (model evaluated against all assertions before output); every `unsat` carries a checkable certificate (Farkas/congruence now; Alethe via Carcara from Phase 2).
6. **Integration tests** — SMT-LIB regression suite + curated benchmark families (QF_UF, QF_IDL/RDL, QF_LRA, QF_UFLRA) for correctness and tracked performance.
7. **Mutation testing (`cargo-mutants`)** on core theory code **and `shinri-num`** — confirm the suite catches behavioral changes.
8. **CI gates:** `cargo nextest`, `cargo deny check`, `cargo clippy -D warnings`, `cargo fmt --check`, benchmark-regression job. Differential + fuzz run on a longer scheduled budget.

---

## 12. Phase 1 Deliverable

A sound, complete, single-threaded solver for **QF_UF + QF_IDL/RDL + QF_LRA + QF_UFLRA** with:
- the in-house `shinri-num` bignum/rational library as the only arithmetic backend (**no `num-bigint`/`malachite` in the shipping build** — Phase 1 gate),
- a fast SMT-LIB 2.6 frontend,
- `check-sat`, `check-sat-assuming`, `push`/`pop`,
- `get-model` / `get-value`, `get-unsat-core`,
- an embeddable `shinri-solver` library + `shinri-cli` binary,
- the cross-cutting *seams* (ProofSink, ClauseId, assumptions, merge-event hooks, MCSat-hostable trail) designed in,
- the full testing harness (unit, property, differential, fuzz, mutation, CI).

Implemented incrementally in **QF_UF-first order**, so there is always a sound, runnable solver at each step:
1. `shinri-num` (Integer/Rational/DeltaRational) + Core (term/sort DAG, trail, Rational trait, ProofSink). `shinri-num` is differential-tested against `num-bigint` from the start; `num-bigint` may scaffold the `Rational` fallback *during* development but is removed from the shipping path before the gate below.
2. SAT core (incremental + assumptions).
3. DPLL(T) glue + Theory trait → EUF (congruence closure + proof forest). **First runnable solver: QF_UF.**
4. Difference logic. **QF_IDL/RDL.**
5. Dutertre–de Moura simplex (on `shinri-num`). **QF_LRA.**
6. Nelson–Oppen model-based combination. **QF_UFLRA.**
7. SMT-LIB frontend + CLI hardening; model & unsat-core extraction; full test harness.

**Phase 1 gate:** the deliverable is not "done" until `shinri-num` is the sole arithmetic backend in the shipping build and has passed its differential/fuzz/mutation regime; `num-bigint`/`num-rational` survive only as dev-only oracles.

**Competitive measuring sticks (expect competitive + sound, not faster, initially):** Yices2 (QF_UF), OpenSMT (QF_LRA).

---

## 13. North-Star Roadmap

- **Phase 1 — Clean core (beachhead).** As specified above.
- **Phase 2 — LIA + proofs + production incrementality.** Branch-and-bound + Gomory → **Cuts from Proofs** (Dillig–Dillig–Aiken; targets OpenSMT on QF_LIA). Emit **Alethe** proofs checked by **Carcara**; native LRAT hints. Harden push/pop + `weaken`/restore for the Incremental and Unsat-Core tracks.
- **Phase 3 — Bit-vectors + arrays.** AIG bit-blaster + word-level rewriter (fixpoint) → propagation-based ternary local search portfolio → lemmas-on-demand array procedure (reuses EUF union-find). Opportunity: tighter local-search ↔ bit-blast interleaving than Bitwuzla's coarse portfolio.
- **Phase 4 — Quantifiers + strings.** E-matching (code-trees + path index, using Phase-1 merge hooks) → CEGQI (complete quantified LRA/LIA, reuses simplex) → enumerative/MBQI fallback. Then LRT+14 strings + regex derivatives with an explicit sound-but-incomplete contract.
- **Phase 5 — Nonlinear, FP, MCSat, parallelism.** Incremental linearization for NRA (before CAD); SymFPU-style FP word-blasting; MCSat as an alternative hosted engine for QF_NRA; parallel orchestration crate (cube-and-conquer via the assumption interface).

**Cross-cutting timing:** proofs — interfaces Phase 1, emission Phase 2. Incrementality — assumptions Phase 1, full push/pop+weaken Phase 2. Parallelism — hooks Phase 1, orchestration Phase 5.

---

## 14. Risks & Hard Problems

1. **Incumbents are decades-tuned.** Beating Yices2 (QF_UF), OpenSMT (QF_LRA), or Bitwuzla (QF_BV) outright is unrealistic for v1. The honest Phase 1 goal is sound, complete, competitive *coverage*.
2. **Soundness is existential.** One wrong answer sinks a division. Classic from-scratch failure modes: simplex delta-rational handling, congruence-closure disequality edges, exact-arithmetic correctness. Mitigation: differential testing from day one; conservative `unknown`.
3. **Exact-rational arithmetic is the LRA hot spot — and we are building the bignum ourselves (`shinri-num`).** This is a deliberate bet: a workload-tuned library can beat general pure-Rust crates on our shape (small magnitudes, GCD-heavy, allocation-averse), but a bignum bug is a *silent soundness bug*, the worst kind. Mitigations: the i128 fast-path keeps most operations out of the bignum entirely; integer-rows-with-shared-denominator contains coefficient blowup; and `shinri-num` is held to the strictest test regime in the project (differential vs `num-bigint`, property, fuzz, mutation) and is not trusted until it provably agrees with the reference. Residual risk: it is net-new scope that gates Phase 1 and could absorb more time than budgeted — bounded by the SMT-tuned scope (no Toom-Cook/FFT/Burnikel-Ziegler until profiling demands them).
4. **The SAT core is load-bearing and unforgiving.** Matching Kissat/CaDiCaL raw SAT performance in pure Rust is unrealistic — but for SMT the trail is theory-atom-dominated, so a correct, incremental, well-instrumented MiniSat-class core is the right target.
5. **Incrementality vs inprocessing tension.** Heavy BVE eliminates exactly the variables theories need; chronological backtracking is a bug magnet. Phase 1 defers both deliberately.
6. **Architectural one-way doors.** E-matching merge hooks, `ClauseId`/`ProofSink`, the assumption API, and an MCSat-capable trail must be designed in Phase 1 or retrofitting is a rewrite (as cvc5/CVC4 learned with proofs and BV).
7. **Combination subtleties.** Nelson–Oppen explodes on non-convex theories (LIA, arrays) via arrangement enumeration; model-based combination is a soundness-bug source. Minimal, relevant explanations are where clean implementations quietly win.
8. **The pure-Rust mandate is a real constraint.** It forbids the fastest bignum (GMP) and SAT backends (Kissat/CaDiCaL via FFI). shinri's answer is not raw-speed parity but soundness, memory safety, a clean incremental architecture, fast parsing, an in-house workload-tuned bignum, a fully permissive (MIT/Apache) shipping stack, and being the first credible pure-Rust SMT solver.

---

## Appendix A — Key References

- Nieuwenhuis, Oliveras, Tinelli. *Solving SAT and SAT Modulo Theories: From an Abstract Davis–Putnam–Logemann–Loveland Procedure to DPLL(T).* JACM 2006.
- Nieuwenhuis, Oliveras. *Fast Congruence Closure and Extensions.* Information & Computation 2007 (RTA 2005).
- Dutertre, de Moura. *A Fast Linear-Arithmetic Solver for DPLL(T).* CAV 2006.
- King, Barrett, Dutertre. *Simplex with Sum of Infeasibilities for SMT.* FMCAD 2013.
- Dillig, Dillig, Aiken. *Cuts from Proofs: A Complete and Practical Technique for Solving Linear Inequalities over Integers.* CAV 2009 / FMSD 2011.
- Sörensson, Biere. *Minimizing Learned Clauses.* SAT 2009.
- de Moura, Bjørner. *Model-based Theory Combination.* SMT 2007.
- Brummayer, Biere. *Lemmas on Demand for the Extensional Theory of Arrays.* JSAT 2009.
- Niemetz, Preiner. *Bitwuzla.* CAV 2023.
- Barrett et al. *cvc5: A Versatile and Industrial-Strength SMT Solver.* TACAS 2022.
- Karatsuba, Ofman. *Multiplication of Many-Digital Numbers by Automatic Computers.* 1962.
- Knuth. *The Art of Computer Programming, Vol. 2: Seminumerical Algorithms* (Algorithm D division; Lehmer's GCD). 3rd ed.
- Stein. *Binary GCD algorithm.* 1967.
