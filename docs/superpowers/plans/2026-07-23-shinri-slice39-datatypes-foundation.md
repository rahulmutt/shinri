# Slice 39 — Datatypes Theory Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add algebraic datatypes to shinri — sort representation, `declare-datatypes` parsing, and a new `shinri-dt` theory solver implementing the non-splitting datatype rules — so QF_DT queries are decided end to end behind an explicit completeness fence.

**Architecture:** Constructors, selectors, and testers are ordinary uninterpreted function symbols tagged by a `DatatypeRegistry` side-table on `Context`, so EUF congruence-closes them for free. `shinri-dt` owns no equality state: it is a pure lemma-on-demand theory, structurally identical to `shinri-arrays`, emitting unconditional tautologies via `TCheck::Split` and conflicts via `TCheck::Conflict`. The Combiner gains a fifth theory slot.

**Tech Stack:** Rust 2021 (rust-version 1.96.0), `rustc_hash::FxHashMap`, `cargo nextest`, `mise` tasks, z3/cvc5 for oracle differential tests.

**Spec:** [docs/superpowers/specs/2026-07-23-shinri-slice39-datatypes-foundation-design.md](../specs/2026-07-23-shinri-slice39-datatypes-foundation-design.md)

## Global Constraints

- **Pure-Rust mandate.** No native-link dependencies. `deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`. Add no new third-party dependencies in this slice; `shinri-dt` depends only on `shinri-core`, `shinri-theory`, `shinri-sat`, and `rustc_hash`.
- **Formatting gate.** Run `cargo fmt --all` before every commit. CI gates on `cargo fmt --check` and fails fast.
- **Lint gate.** `cargo clippy --workspace --all-targets -- -D warnings` must be clean. `mise run lint` covers fmt + clippy.
- **Test-tier budget.** Blocking PR tier is 10–15 min wall-clock (CI hard cap 20 min). Every test added by this plan is milliseconds-scale. Add **no** `#[ignore]`d exhaustive suites, and never remove `#[ignore]` from the existing `shinri-fp` exhaustive suites.
- **Oracle tests are feature-gated.** Run them with `cargo nextest run -p shinri-solver --features oracle`. **Without `--features oracle` the suite silently runs 0 tests** — never report that as green coverage. Always confirm a non-zero test count.
- **Parser is the only untrusted edge.** Per [docs/threat-model.md](../../threat-model.md), every malformed `declare-datatypes` shape must produce a `Diagnostic`, never a panic. Sort-graph traversals must be **iterative** (explicit worklist), never recursive descent, so hostile nesting cannot overflow the stack.
- **Branch discipline.** Work on branch `slice39-datatypes-foundation`, PR to `main`, merge with a merge commit when CI is green, then delete the branch remote and local.
- **Naming.** New crate is `shinri-dt`; theory struct is `DtSolver`; `THEORY_ID = 5`; `Owner` variant is `Datatypes`.

---

## File Structure

**Created:**
- `crates/shinri-dt/Cargo.toml` — new crate manifest
- `crates/shinri-dt/src/lib.rs` — `DtSolver`: registration index + rule engine + fence + model
- `crates/shinri-solver/tests/qfdt_e2e.rs` — end-to-end SMT-LIB script witnesses
- `crates/shinri-solver/tests/qfdt_oracle.rs` — differential tests vs z3/cvc5 (feature-gated)

**Modified:**
- `crates/shinri-core/src/sort.rs` — add `SortNode::Datatype(SymbolId)`
- `crates/shinri-core/src/context.rs` — `DatatypeRegistry` field, declaration/query API, well-foundedness fixpoint
- `crates/shinri-core/src/lib.rs` — re-export `DtRole`
- `crates/shinri-frontend/src/lib.rs` — add `Command::DeclareDatatypes`
- `crates/shinri-parser/src/parser.rs` — `declare-datatype`/`declare-datatypes` commands; `((_ is C) x)` tester terms
- `crates/shinri-theory/src/types.rs` — `Owner::Datatypes`, `ModelVal::Datatype(String)`
- `crates/shinri-theory/src/atom.rs` — `classify` routing for datatype atoms
- `crates/shinri-theory/src/combiner.rs` — fifth generic slot `D`, routing at every dispatch site
- `crates/shinri-solver/src/lib.rs` — instantiate the 5-tuple Combiner
- `crates/shinri-solver/src/model.rs` — format `ModelVal::Datatype`
- `crates/shinri-solver/Cargo.toml`, `Cargo.toml` (workspace members), `deny.toml` if needed
- `crates/shinri-parser/fuzz/` — datatype seeds
- `README.md` — crate table row

---

### Task 1: Datatype sort + registry in `shinri-core`

**Files:**
- Modify: `crates/shinri-core/src/sort.rs`
- Modify: `crates/shinri-core/src/context.rs`
- Modify: `crates/shinri-core/src/lib.rs`
- Test: `crates/shinri-core/src/context.rs` (inline `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: nothing (first task).
- Produces:
  - `SortNode::Datatype(SymbolId)`
  - `pub enum DtRole { Constructor { dt: SortId, index: u32 }, Selector { ctor: SymbolId, index: u32 }, Tester { ctor: SymbolId } }`
  - `Context::declare_datatype_sort(&mut self, name: &str) -> SortId`
  - `Context::dt_add_constructor(&mut self, dt: SortId, ctor: SymbolId, selectors: &[SymbolId], tester: SymbolId)`
  - `Context::dt_role(&self, sym: SymbolId) -> Option<DtRole>`
  - `Context::dt_constructors(&self, dt: SortId) -> Option<&[SymbolId]>`
  - `Context::dt_selectors(&self, ctor: SymbolId) -> Option<&[SymbolId]>`
  - `Context::dt_tester(&self, ctor: SymbolId) -> Option<SymbolId>`
  - `Context::is_datatype_sort(&self, s: SortId) -> bool`
  - `Context::fun_params(&self, sym: SymbolId) -> Option<&[SortId]>`

- [ ] **Step 1: Write the failing test**

Add to the existing `#[cfg(test)] mod tests` block at the bottom of `crates/shinri-core/src/context.rs`:

```rust
#[test]
fn datatype_registry_records_roles() {
    let mut ctx = Context::new();
    let list = ctx.declare_datatype_sort("List");
    let int = ctx.int_sort();
    // nil : () List
    let nil = ctx.declare_fun("nil", &[], list);
    let is_nil = ctx.declare_fun("is-nil", &[list], ctx.bool_sort());
    ctx.dt_add_constructor(list, nil, &[], is_nil);
    // cons : (Int, List) List, selectors head/tail
    let cons = ctx.declare_fun("cons", &[int, list], list);
    let head = ctx.declare_fun("head", &[list], int);
    let tail = ctx.declare_fun("tail", &[list], list);
    let is_cons = ctx.declare_fun("is-cons", &[list], ctx.bool_sort());
    ctx.dt_add_constructor(list, cons, &[head, tail], is_cons);

    assert!(ctx.is_datatype_sort(list));
    assert_eq!(ctx.dt_constructors(list), Some(&[nil, cons][..]));
    assert_eq!(ctx.dt_selectors(cons), Some(&[head, tail][..]));
    assert_eq!(ctx.dt_tester(cons), Some(is_cons));
    assert!(matches!(
        ctx.dt_role(cons),
        Some(DtRole::Constructor { dt, index: 1 }) if dt == list
    ));
    assert!(matches!(
        ctx.dt_role(tail),
        Some(DtRole::Selector { ctor, index: 1 }) if ctor == cons
    ));
    assert!(matches!(
        ctx.dt_role(is_cons),
        Some(DtRole::Tester { ctor }) if ctor == cons
    ));
    assert_eq!(ctx.dt_role(head).is_some(), true);
    assert_eq!(ctx.fun_params(cons), Some(&[int, list][..]));
}

#[test]
fn datatype_registry_survives_clone() {
    let mut ctx = Context::new();
    let list = ctx.declare_datatype_sort("List");
    let nil = ctx.declare_fun("nil", &[], list);
    let is_nil = ctx.declare_fun("is-nil", &[list], ctx.bool_sort());
    ctx.dt_add_constructor(list, nil, &[], is_nil);
    let cloned = ctx.clone();
    assert_eq!(cloned.dt_constructors(list), Some(&[nil][..]));
    assert!(cloned.is_datatype_sort(list));
}
```

The clone test matters: `check_sat` clones the context into the Combiner, so the registry must survive.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core datatype_registry -- --nocapture`
Expected: FAIL to compile — `no method named 'declare_datatype_sort' found`, `cannot find type 'DtRole'`.

- [ ] **Step 3: Add the sort variant**

In `crates/shinri-core/src/sort.rs`, add a variant to `SortNode`:

```rust
    /// An algebraic datatype sort declared by `declare-datatypes` (slice 39).
    /// Structurally identical to `Uninterpreted` for sort-checking; kept
    /// distinct so atoms can be routed to the datatype theory and so
    /// cardinality reasoning can identify it.
    Datatype(SymbolId),
```

- [ ] **Step 4: Add the registry to `Context`**

In `crates/shinri-core/src/context.rs`, add near the top (after the imports):

```rust
/// The datatype role of a symbol (slice 39). Constructors, selectors, and
/// testers are ordinary uninterpreted functions; this table is what makes them
/// datatype-aware without new `Op` variants.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DtRole {
    /// `index` is the constructor's position in its datatype's constructor list.
    Constructor { dt: SortId, index: u32 },
    /// `index` is the selector's argument position within `ctor`.
    Selector { ctor: SymbolId, index: u32 },
    Tester { ctor: SymbolId },
}

/// Side-table describing every declared datatype. Lives on `Context` so it is
/// carried by `Context::clone` into the Combiner.
#[derive(Clone, Default)]
pub struct DatatypeRegistry {
    /// datatype sort -> constructors, in declaration order
    ctors: FxHashMap<SortId, Vec<SymbolId>>,
    /// constructor -> its selectors, in argument order
    sels: FxHashMap<SymbolId, Vec<SymbolId>>,
    /// constructor -> its tester
    testers: FxHashMap<SymbolId, SymbolId>,
    /// any datatype-related symbol -> its role
    roles: FxHashMap<SymbolId, DtRole>,
}
```

Add the field to the `Context` struct:

```rust
    /// Datatype declarations (slice 39). Empty for non-datatype queries.
    datatypes: DatatypeRegistry,
```

and initialize it in `Context::new`:

```rust
            datatypes: DatatypeRegistry::default(),
```

- [ ] **Step 5: Add the Context API**

Append a new `impl Context` block in `crates/shinri-core/src/context.rs`:

```rust
impl Context {
    /// Declare (and intern) a fresh datatype sort named `name`.
    pub fn declare_datatype_sort(&mut self, name: &str) -> SortId {
        let sym = self.symbols.intern(name);
        self.intern_sort(SortNode::Datatype(sym))
    }

    /// Register `ctor` as a constructor of datatype sort `dt`, with `selectors`
    /// in argument order and tester `tester`. Signatures must already have been
    /// installed via `declare_fun`.
    pub fn dt_add_constructor(
        &mut self,
        dt: SortId,
        ctor: SymbolId,
        selectors: &[SymbolId],
        tester: SymbolId,
    ) {
        let list = self.datatypes.ctors.entry(dt).or_default();
        let index = list.len() as u32;
        list.push(ctor);
        self.datatypes
            .roles
            .insert(ctor, DtRole::Constructor { dt, index });
        for (i, &sel) in selectors.iter().enumerate() {
            self.datatypes.roles.insert(
                sel,
                DtRole::Selector {
                    ctor,
                    index: i as u32,
                },
            );
        }
        self.datatypes.sels.insert(ctor, selectors.to_vec());
        self.datatypes.roles.insert(tester, DtRole::Tester { ctor });
        self.datatypes.testers.insert(ctor, tester);
    }

    pub fn dt_role(&self, sym: SymbolId) -> Option<DtRole> {
        self.datatypes.roles.get(&sym).copied()
    }

    pub fn dt_constructors(&self, dt: SortId) -> Option<&[SymbolId]> {
        self.datatypes.ctors.get(&dt).map(|v| v.as_slice())
    }

    pub fn dt_selectors(&self, ctor: SymbolId) -> Option<&[SymbolId]> {
        self.datatypes.sels.get(&ctor).map(|v| v.as_slice())
    }

    pub fn dt_tester(&self, ctor: SymbolId) -> Option<SymbolId> {
        self.datatypes.testers.get(&ctor).copied()
    }

    pub fn is_datatype_sort(&self, s: SortId) -> bool {
        matches!(self.sort_node(s), SortNode::Datatype(_))
    }

    /// Declared parameter sorts of `sym`, if it has a signature.
    pub fn fun_params(&self, sym: SymbolId) -> Option<&[SortId]> {
        self.fun_sigs.get(&sym).map(|(p, _)| p.as_slice())
    }

    /// True iff any declared datatype exists (cheap gate for the DT theory).
    pub fn has_datatypes(&self) -> bool {
        !self.datatypes.ctors.is_empty()
    }
}
```

If `sort_node` is named differently in this file, use the existing accessor that maps `SortId -> &SortNode` (see `Context::sort_node` near line 149).

- [ ] **Step 6: Re-export `DtRole`**

In `crates/shinri-core/src/lib.rs`, extend the context re-export line:

```rust
pub use context::{Context, DatatypeRegistry, DtRole};
```

- [ ] **Step 7: Handle the new `SortNode` variant everywhere it is matched**

Run: `cargo build --workspace 2>&1 | grep -A5 "non-exhaustive"`
Expected: a list of `match` sites over `SortNode` that now fail to compile. For each, treat `Datatype(sym)` exactly as `Uninterpreted(sym)` is treated — datatype sorts are uninterpreted as far as sort printing and model-domain construction are concerned in this slice.

Run: `cargo build --workspace`
Expected: clean build.

- [ ] **Step 8: Run the tests**

Run: `cargo test -p shinri-core datatype_registry -- --nocapture`
Expected: PASS, 2 tests.

Run: `cargo test -p shinri-core`
Expected: PASS, no regressions.

- [ ] **Step 9: Commit**

```bash
cargo fmt --all
git add crates/shinri-core/src/sort.rs crates/shinri-core/src/context.rs crates/shinri-core/src/lib.rs
git commit -m "feat(dt): slice39 T1 — datatype sort variant + Context datatype registry"
```

---

### Task 2: Well-foundedness fixpoint

**Files:**
- Modify: `crates/shinri-core/src/context.rs`
- Test: `crates/shinri-core/src/context.rs` (inline tests)

**Interfaces:**
- Consumes: Task 1's `dt_constructors`, `fun_params`, `is_datatype_sort`.
- Produces: `Context::dt_first_ill_founded(&self, group: &[SortId]) -> Option<SortId>` — returns the first sort in `group` with no finite ground term, or `None` if all are inhabited.

A datatype is inhabited iff some constructor has all argument sorts inhabited. Non-datatype sorts are always inhabited. This is a monotone fixpoint, computed with an explicit worklist — **never** recursive descent, because a hostile declaration can nest arbitrarily deep (Global Constraints).

- [ ] **Step 1: Write the failing test**

Add to `#[cfg(test)] mod tests` in `crates/shinri-core/src/context.rs`:

```rust
#[test]
fn well_founded_list_is_inhabited() {
    let mut ctx = Context::new();
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
    assert_eq!(ctx.dt_first_ill_founded(&[list]), None);
}

#[test]
fn non_well_founded_datatype_is_rejected() {
    // (declare-datatype T ((c (f T)))) — every value would be infinite.
    let mut ctx = Context::new();
    let t = ctx.declare_datatype_sort("T");
    let b = ctx.bool_sort();
    let c = ctx.declare_fun("c", &[t], t);
    let f = ctx.declare_fun("f", &[t], t);
    let is_c = ctx.declare_fun("is-c", &[t], b);
    ctx.dt_add_constructor(t, c, &[f], is_c);
    assert_eq!(ctx.dt_first_ill_founded(&[t]), Some(t));
}

#[test]
fn mutually_recursive_datatypes_inhabited_through_partner() {
    // A ::= mkA(B) ; B ::= base | mkB(A)  — both inhabited via B's base case.
    let mut ctx = Context::new();
    let a = ctx.declare_datatype_sort("A");
    let bs = ctx.declare_datatype_sort("B");
    let b = ctx.bool_sort();
    let base = ctx.declare_fun("base", &[], bs);
    let is_base = ctx.declare_fun("is-base", &[bs], b);
    ctx.dt_add_constructor(bs, base, &[], is_base);
    let mk_a = ctx.declare_fun("mkA", &[bs], a);
    let get_b = ctx.declare_fun("getB", &[a], bs);
    let is_mk_a = ctx.declare_fun("is-mkA", &[a], b);
    ctx.dt_add_constructor(a, mk_a, &[get_b], is_mk_a);
    let mk_b = ctx.declare_fun("mkB", &[a], bs);
    let get_a = ctx.declare_fun("getA", &[bs], a);
    let is_mk_b = ctx.declare_fun("is-mkB", &[bs], b);
    ctx.dt_add_constructor(bs, mk_b, &[get_a], is_mk_b);
    assert_eq!(ctx.dt_first_ill_founded(&[a, bs]), None);
}

#[test]
fn mutually_recursive_without_base_case_is_rejected() {
    // A ::= mkA(B) ; B ::= mkB(A) — neither has a base case.
    let mut ctx = Context::new();
    let a = ctx.declare_datatype_sort("A");
    let bs = ctx.declare_datatype_sort("B");
    let b = ctx.bool_sort();
    let mk_a = ctx.declare_fun("mkA", &[bs], a);
    let get_b = ctx.declare_fun("getB", &[a], bs);
    let is_mk_a = ctx.declare_fun("is-mkA", &[a], b);
    ctx.dt_add_constructor(a, mk_a, &[get_b], is_mk_a);
    let mk_b = ctx.declare_fun("mkB", &[a], bs);
    let get_a = ctx.declare_fun("getA", &[bs], a);
    let is_mk_b = ctx.declare_fun("is-mkB", &[bs], b);
    ctx.dt_add_constructor(bs, mk_b, &[get_a], is_mk_b);
    assert!(ctx.dt_first_ill_founded(&[a, bs]).is_some());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core well_founded mutually_recursive non_well_founded -- --nocapture`
Expected: FAIL to compile — `no method named 'dt_first_ill_founded'`.

- [ ] **Step 3: Implement the fixpoint**

Add to the `impl Context` block created in Task 1:

```rust
    /// Iterative inhabitance fixpoint over all declared datatypes. Returns the
    /// first sort in `group` that has no finite ground term (an empty sort),
    /// or `None` when every member is inhabited.
    ///
    /// A non-datatype sort is always inhabited. A datatype is inhabited once
    /// some constructor has all argument sorts inhabited. Marking is monotone,
    /// so iterating to saturation terminates in at most `|datatypes|` rounds.
    ///
    /// Deliberately iterative (worklist, not recursion): the sort graph comes
    /// from untrusted input and may be arbitrarily deep (threat model).
    pub fn dt_first_ill_founded(&self, group: &[SortId]) -> Option<SortId> {
        let mut inhabited: FxHashSet<SortId> = FxHashSet::default();
        let all: Vec<SortId> = self.datatypes.ctors.keys().copied().collect();
        loop {
            let mut changed = false;
            for &dt in &all {
                if inhabited.contains(&dt) {
                    continue;
                }
                let ctors = match self.dt_constructors(dt) {
                    Some(c) => c,
                    None => continue,
                };
                let any_ctor_ok = ctors.iter().any(|&c| {
                    self.fun_params(c).is_some_and(|params| {
                        params
                            .iter()
                            .all(|&p| !self.is_datatype_sort(p) || inhabited.contains(&p))
                    })
                });
                if any_ctor_ok {
                    inhabited.insert(dt);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        group
            .iter()
            .copied()
            .find(|s| self.is_datatype_sort(*s) && !inhabited.contains(s))
    }
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p shinri-core well_founded mutually_recursive non_well_founded -- --nocapture`
Expected: PASS, 4 tests.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-core/src/context.rs
git commit -m "feat(dt): slice39 T2 — iterative well-foundedness fixpoint over datatype group"
```

---

### Task 3: Parse `declare-datatype` / `declare-datatypes`

**Files:**
- Modify: `crates/shinri-frontend/src/lib.rs`
- Modify: `crates/shinri-parser/src/parser.rs:1047-1105` (command dispatch)
- Modify: `crates/shinri-solver/src/lib.rs:314` (command execution)
- Test: `crates/shinri-parser/src/parser.rs` (inline tests)

**Interfaces:**
- Consumes: Task 1's `declare_datatype_sort`, `dt_add_constructor`; Task 2's `dt_first_ill_founded`.
- Produces: `Command::DeclareDatatypes { sorts: Vec<(String, SortId)> }`; parser method `Parser::parse_declare_datatypes(&mut self, ctx: &mut Context, hsp: Span, plural: bool) -> Result<Command, Diagnostic>`. Tester symbols are named `is-<Ctor>` and reserved via `Context::reserve_symbol`.

Both SMT-LIB 2.6 forms are supported:

```
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
```

- [ ] **Step 1: Write the failing tests**

Add to the `#[cfg(test)] mod tests` block in `crates/shinri-parser/src/parser.rs`:

```rust
/// Parse a script and return the first error message, or None if all commands parsed.
fn first_error(src: &str) -> Option<String> {
    let mut ctx = Context::new();
    let mut p = Parser::new(src);
    while let Some(r) = p.next_command(&mut ctx) {
        if let Err(d) = r {
            return Some(d.message);
        }
    }
    None
}

#[test]
fn declare_datatype_singular_registers_constructors() {
    let mut ctx = Context::new();
    let mut p = Parser::new("(declare-datatype List ((nil) (cons (head Int) (tail List))))");
    let cmd = p.next_command(&mut ctx).unwrap().unwrap();
    let sorts = match cmd {
        Command::DeclareDatatypes { sorts } => sorts,
        other => panic!("expected DeclareDatatypes, got {other:?}"),
    };
    assert_eq!(sorts.len(), 1);
    assert_eq!(sorts[0].0, "List");
    let list = sorts[0].1;
    assert!(ctx.is_datatype_sort(list));
    let ctors = ctx.dt_constructors(list).expect("constructors");
    assert_eq!(ctors.len(), 2);
    assert_eq!(ctx.symbol_name(ctors[0]), "nil");
    assert_eq!(ctx.symbol_name(ctors[1]), "cons");
    let sels = ctx.dt_selectors(ctors[1]).expect("selectors");
    assert_eq!(sels.len(), 2);
    assert_eq!(ctx.symbol_name(sels[0]), "head");
    assert_eq!(ctx.dt_tester(ctors[1]).map(|t| ctx.symbol_name(t)), Some("is-cons"));
}

#[test]
fn declare_datatypes_plural_mutually_recursive() {
    let mut ctx = Context::new();
    let src = "(declare-datatypes ((A 0) (B 0)) \
               (((mkA (getB B))) ((base) (mkB (getA A)))))";
    let mut p = Parser::new(src);
    let cmd = p.next_command(&mut ctx).unwrap().unwrap();
    let sorts = match cmd {
        Command::DeclareDatatypes { sorts } => sorts,
        other => panic!("expected DeclareDatatypes, got {other:?}"),
    };
    assert_eq!(sorts.len(), 2);
    assert!(ctx.dt_constructors(sorts[0].1).is_some());
    assert_eq!(ctx.dt_constructors(sorts[1].1).map(|c| c.len()), Some(2));
}

#[test]
fn declare_datatypes_rejects_nonzero_arity() {
    let e = first_error("(declare-datatypes ((L 1)) (((nil))))").expect("must error");
    assert!(e.contains("arity"), "message was: {e}");
}

#[test]
fn declare_datatypes_rejects_zero_constructors() {
    let e = first_error("(declare-datatype E ())").expect("must error");
    assert!(e.contains("at least one constructor"), "message was: {e}");
}

#[test]
fn declare_datatypes_rejects_duplicate_constructor() {
    let e = first_error("(declare-datatype D ((c) (c)))").expect("must error");
    assert!(e.contains("duplicate"), "message was: {e}");
}

#[test]
fn declare_datatypes_rejects_duplicate_selector() {
    let e = first_error("(declare-datatype D ((c (f Int) (f Int))))").expect("must error");
    assert!(e.contains("duplicate"), "message was: {e}");
}

#[test]
fn declare_datatypes_rejects_non_well_founded() {
    let e = first_error("(declare-datatype T ((c (f T))))").expect("must error");
    assert!(e.contains("well-founded"), "message was: {e}");
}

#[test]
fn declare_datatypes_rejects_duplicate_sort_name() {
    let e = first_error(
        "(declare-datatype L ((nil)))(declare-datatype L ((nil2)))",
    )
    .expect("must error");
    assert!(e.contains("already declared"), "message was: {e}");
}

#[test]
fn declare_datatypes_deep_nesting_does_not_overflow() {
    // 5000 nested datatypes, each referring to the next; the last is a base
    // case. Must produce a decision (ok or Diagnostic), never a stack overflow.
    let mut src = String::new();
    src.push_str("(declare-datatype D5000 ((base5000)))");
    for i in (0..5000).rev() {
        src.push_str(&format!("(declare-datatype D{i} ((mk{i} (get{i} D{})))) ", i + 1));
    }
    let _ = first_error(&src); // must return, not crash
}

#[test]
fn declare_datatypes_rejects_unbalanced_input() {
    let e = first_error("(declare-datatype List ((nil) (cons (head Int)");
    assert!(e.is_some(), "truncated input must produce a Diagnostic");
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-parser declare_datatype -- --nocapture`
Expected: FAIL to compile — `no variant named 'DeclareDatatypes'`.

- [ ] **Step 3: Add the Command variant**

In `crates/shinri-frontend/src/lib.rs`, add to `enum Command` (before `Assert`):

```rust
    /// One `declare-datatype`/`declare-datatypes` command. Carries the declared
    /// sorts by name; the constructor/selector/tester symbols and their roles
    /// live in the `Context` datatype registry.
    DeclareDatatypes {
        sorts: Vec<(String, SortId)>,
    },
```

- [ ] **Step 4: Implement the parser**

In `crates/shinri-parser/src/parser.rs`, add two arms to the `match head.as_str()` in `parse_command_body` (alongside `"declare-sort"`):

```rust
            "declare-datatype" => self.parse_declare_datatypes(ctx, hsp, false)?,
            "declare-datatypes" => self.parse_declare_datatypes(ctx, hsp, true)?,
```

Then add the method to the same `impl` block:

```rust
    /// `(declare-datatype T (<ctor>...))` and
    /// `(declare-datatypes ((T 0)...) ((<ctor>...)...))`.
    ///
    /// A `<ctor>` is `(<name> (<sel> <Sort>)...)`. All declared sorts are
    /// interned BEFORE any constructor body is parsed so mutual recursion
    /// resolves. Every malformed shape is rejected with a `Diagnostic`.
    fn parse_declare_datatypes(
        &mut self,
        ctx: &mut Context,
        hsp: Span,
        plural: bool,
    ) -> Result<Command, Diagnostic> {
        // ---- 1. names -------------------------------------------------------
        let mut names: Vec<(String, Span)> = Vec::new();
        if plural {
            self.expect_token(&Token::LParen)?;
            while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                self.expect_token(&Token::LParen)?;
                let (n, nsp) = self.expect_symbol()?;
                let arity = self.expect_numeral_u32()?;
                if arity != 0 {
                    return Err(Diagnostic::new(
                        nsp,
                        "declare-datatypes: parametric datatype arity > 0 unsupported",
                    ));
                }
                self.expect_token(&Token::RParen)?;
                names.push((n, nsp));
            }
            self.bump(); // ')'
        } else {
            let (n, nsp) = self.expect_symbol()?;
            names.push((n, nsp));
        }
        if names.is_empty() {
            return Err(Diagnostic::new(hsp, "declare-datatypes: no sorts declared"));
        }

        // ---- 2. intern every sort first (mutual recursion) ------------------
        let mut sorts: Vec<(String, SortId)> = Vec::new();
        for (n, nsp) in &names {
            if self.env.lookup_sort(n).is_some() {
                return Err(Diagnostic::new(
                    nsp.clone(),
                    format!("sort {n} already declared"),
                ));
            }
            let s = ctx.declare_datatype_sort(n);
            self.env.add_sort(n, s);
            sorts.push((n.clone(), s));
        }

        // ---- 3. constructor bodies -----------------------------------------
        let mut seen_ctor: FxHashSet<String> = FxHashSet::default();
        if plural {
            self.expect_token(&Token::LParen)?;
        }
        for idx in 0..sorts.len() {
            let dt = sorts[idx].1;
            self.expect_token(&Token::LParen)?;
            let mut n_ctors = 0usize;
            while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                self.parse_one_constructor(ctx, dt, &mut seen_ctor)?;
                n_ctors += 1;
            }
            self.bump(); // ')'
            if n_ctors == 0 {
                return Err(Diagnostic::new(
                    hsp,
                    format!("datatype {} must have at least one constructor", sorts[idx].0),
                ));
            }
        }
        if plural {
            self.expect_token(&Token::RParen)?;
        }

        // ---- 4. well-foundedness -------------------------------------------
        let group: Vec<SortId> = sorts.iter().map(|(_, s)| *s).collect();
        if let Some(bad) = ctx.dt_first_ill_founded(&group) {
            let name = sorts
                .iter()
                .find(|(_, s)| *s == bad)
                .map(|(n, _)| n.clone())
                .unwrap_or_else(|| "<datatype>".to_string());
            return Err(Diagnostic::new(
                hsp,
                format!("datatype {name} is not well-founded (no finite value exists)"),
            ));
        }

        Ok(Command::DeclareDatatypes { sorts })
    }

    /// One `(<ctor> (<sel> <Sort>)...)` form, registered into `ctx`.
    fn parse_one_constructor(
        &mut self,
        ctx: &mut Context,
        dt: SortId,
        seen_ctor: &mut FxHashSet<String>,
    ) -> Result<(), Diagnostic> {
        self.expect_token(&Token::LParen)?;
        let (cname, csp) = self.expect_symbol()?;
        reject_reserved(ctx, &cname, &csp)?;
        if !seen_ctor.insert(cname.clone()) {
            return Err(Diagnostic::new(
                csp,
                format!("duplicate constructor {cname}"),
            ));
        }
        let mut sel_names: Vec<(String, Span)> = Vec::new();
        let mut sel_sorts: Vec<SortId> = Vec::new();
        let mut seen_sel: FxHashSet<String> = FxHashSet::default();
        while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
            self.expect_token(&Token::LParen)?;
            let (sname, ssp) = self.expect_symbol()?;
            reject_reserved(ctx, &sname, &ssp)?;
            if !seen_sel.insert(sname.clone()) {
                return Err(Diagnostic::new(
                    ssp,
                    format!("duplicate selector {sname}"),
                ));
            }
            let s = self.parse_sort(ctx)?;
            self.expect_token(&Token::RParen)?;
            sel_names.push((sname, ssp));
            sel_sorts.push(s);
        }
        self.bump(); // ')'

        let ctor = ctx.declare_fun(&cname, &sel_sorts, dt);
        self.env.add_fun(&cname, ctor);
        let mut sels = Vec::with_capacity(sel_names.len());
        for (i, (sname, _)) in sel_names.iter().enumerate() {
            let sym = ctx.declare_fun(sname, &[dt], sel_sorts[i]);
            self.env.add_fun(sname, sym);
            sels.push(sym);
        }
        // The tester is minted, not user-written: reserve it so a later
        // `declare-fun is-C` cannot hash-cons onto the same symbol.
        let tname = format!("is-{cname}");
        let bool_s = ctx.bool_sort();
        let tester = ctx.declare_fun(&tname, &[dt], bool_s);
        ctx.reserve_symbol(tester);
        ctx.dt_add_constructor(dt, ctor, &sels, tester);
        Ok(())
    }
```

Add `use rustc_hash::FxHashSet;` to the parser's imports if absent, and `SortId` to the `shinri_core` import list.

- [ ] **Step 5: Execute the command in the solver**

In `crates/shinri-solver/src/lib.rs`, add `Command::DeclareDatatypes { .. }` to the no-op arm at line 314 (declarations mutate the shared `Context` during parsing, so execution has nothing further to do):

```rust
            | Command::DeclareSort { .. }
            | Command::DeclareDatatypes { .. }
            | Command::DeclareFun { .. }
```

- [ ] **Step 6: Run the tests**

Run: `cargo test -p shinri-parser declare_datatype -- --nocapture`
Expected: PASS, 10 tests.

Run: `cargo build --workspace && cargo test -p shinri-parser -p shinri-frontend -p shinri-solver`
Expected: PASS, no regressions.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add crates/shinri-frontend/src/lib.rs crates/shinri-parser/src/parser.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(dt): slice39 T3 — declare-datatype(s) parsing with rejection table"
```

---

### Task 4: Parse `((_ is C) x)` tester terms

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs:614` (term-position `"_"` arm)
- Test: `crates/shinri-parser/src/parser.rs` (inline tests)

**Interfaces:**
- Consumes: Task 3's registered constructor and tester symbols; `Context::dt_tester`.
- Produces: `((_ is C) x)` parses to `Op::Uninterpreted(tester_sym)` applied to `[x]`.

SMT-LIB writes a tester as the indexed identifier `(_ is C)` in head position: `((_ is C) x)`. Only this form is accepted.

- [ ] **Step 1: Write the failing test**

Add to `#[cfg(test)] mod tests` in `crates/shinri-parser/src/parser.rs`:

```rust
#[test]
fn tester_term_resolves_to_tester_symbol() {
    let mut ctx = Context::new();
    let src = "(declare-datatype List ((nil) (cons (head Int) (tail List))))\
               (declare-fun x () List)\
               (assert ((_ is cons) x))";
    let mut p = Parser::new(src);
    let mut last = None;
    while let Some(r) = p.next_command(&mut ctx) {
        last = Some(r.expect("must parse"));
    }
    let t = match last {
        Some(Command::Assert(t)) => t,
        other => panic!("expected Assert, got {other:?}"),
    };
    // The asserted term is `is-cons` applied to one argument, Bool-sorted.
    assert_eq!(ctx.sort_of(t), ctx.bool_sort());
    match ctx.term_node(t) {
        TermNode::App { op: Op::Uninterpreted(sym), args, .. } => {
            assert_eq!(ctx.symbol_name(*sym), "is-cons");
            assert_eq!(ctx.children(*args).len(), 1);
        }
        other => panic!("expected tester application, got {other:?}"),
    }
}

#[test]
fn tester_rejects_unknown_constructor() {
    let e = first_error(
        "(declare-datatype List ((nil)))(declare-fun x () List)(assert ((_ is bogus) x))",
    )
    .expect("must error");
    assert!(e.contains("not a constructor"), "message was: {e}");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser tester_ -- --nocapture`
Expected: FAIL — the `"_"` arm rejects `is` with "unsupported indexed identifier".

- [ ] **Step 3: Implement**

In the term-position `"_"` match at `crates/shinri-parser/src/parser.rs:614`, add an arm to the `match id.as_str()` before the `bv`-prefix arm:

```rust
                    "is" => {
                        // `((_ is C) x)` — datatype tester. Resolve C to its
                        // constructor symbol and apply that constructor's tester.
                        let (cname, csp) = self.expect_symbol()?;
                        self.expect_token(&Token::RParen)?; // close `(_ is C)`
                        let ctor = self.env.lookup_fun(&cname).ok_or_else(|| {
                            Diagnostic::new(csp.clone(), format!("{cname} is not a constructor"))
                        })?;
                        let tester = ctx.dt_tester(ctor).ok_or_else(|| {
                            Diagnostic::new(csp.clone(), format!("{cname} is not a constructor"))
                        })?;
                        let arg = self.parse_term(ctx)?;
                        self.expect_token(&Token::RParen)?; // close the application
                        return ctx
                            .mk_app(Op::Uninterpreted(tester), &[arg])
                            .map_err(|e| Diagnostic::new(csp, format!("{e:?}")));
                    }
```

The exact shape of the surrounding arm's return type governs whether `return` or a bound value is correct; match the neighbouring `"+oo"` arm's style, which assigns to `result` and falls through to the closing-paren handling. If that arm consumes the closing paren itself, drop the second `expect_token` here — verify against the code before the edit and keep exactly one consumer per paren.

- [ ] **Step 4: Run the tests**

Run: `cargo test -p shinri-parser tester_ -- --nocapture`
Expected: PASS, 2 tests.

Run: `cargo test -p shinri-parser`
Expected: PASS, no regressions.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(dt): slice39 T4 — parse ((_ is C) x) tester terms"
```

---

### Task 5: `shinri-dt` crate skeleton and registration index

**Files:**
- Create: `crates/shinri-dt/Cargo.toml`
- Create: `crates/shinri-dt/src/lib.rs`
- Modify: `Cargo.toml` (workspace members)

**Interfaces:**
- Consumes: Task 1's registry API; `shinri_theory::{TheorySolver, TheoryCtx, TCheck, Explainer, ModelBuilder}`; `shinri_theory::types::EqLeaf`.
- Produces: `pub struct DtSolver` implementing `TheorySolver` with `const THEORY_ID: u16 = 5`, plus internal index fields `ctor_apps: FxHashSet<TermId>`, `sel_apps: FxHashSet<TermId>`, `testers: FxHashSet<TermId>` populated by `new_var`.

`DtSolver` mirrors `shinri-arrays`: monotone, assignment-independent watch sets; `push`/`pop` are no-ops.

- [ ] **Step 1: Create the manifest**

Create `crates/shinri-dt/Cargo.toml`:

```toml
[package]
name = "shinri-dt"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-theory = { path = "../shinri-theory" }
shinri-sat = { path = "../shinri-sat" }
rustc-hash = "2"
```

Match the `rustc-hash` version and the `.workspace = true` keys used by `crates/shinri-arrays/Cargo.toml` exactly — read that file first and mirror it.

Add `"crates/shinri-dt"` to `members` in the workspace `Cargo.toml`, after `"crates/shinri-arrays"`.

- [ ] **Step 2: Write the failing test**

Create `crates/shinri-dt/src/lib.rs` with only the test module and a doc header:

```rust
//! QF_DT datatype theory: lemma-on-demand over the shared EqualityEngine.
//! Owns no equality state; emits datatype axiom instances as positive-atom
//! clauses via `TCheck::Split` and clashes via `TCheck::Conflict`.

#[cfg(test)]
mod tests {
    use crate::DtSolver;
    use shinri_core::{Context, Op, SortId, SymbolId, TermId, Var};
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    /// Declare `List ::= nil | cons(head: Int, tail: List)` and return
    /// `(list_sort, nil, cons, head, tail, is_nil, is_cons)`.
    pub(crate) fn list_dt(
        ctx: &mut Context,
    ) -> (SortId, SymbolId, SymbolId, SymbolId, SymbolId, SymbolId, SymbolId) {
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
        let x = uconst(&mut ctx, "x", list);
        let one = uconst(&mut ctx, "one", ctx.int_sort());
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let head_x = ctx.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();
        let atom = ctx.mk_eq(x, cons_t).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), head_x);
        dt.new_var(&mut cx, Var::new(2), is_cons_x);

        assert!(dt.watches_ctor(cons_t), "cons application must be indexed");
        assert!(dt.watches_ctor(nil_t), "nullary nil must be indexed");
        assert!(dt.watches_sel(head_x), "selector application must be indexed");
        assert!(dt.watches_tester(is_cons_x), "tester must be indexed");
    }
}
```

- [ ] **Step 3: Run test to verify it fails**

Run: `cargo test -p shinri-dt -- --nocapture`
Expected: FAIL to compile — `cannot find struct 'DtSolver'`.

- [ ] **Step 4: Implement the skeleton**

Prepend to `crates/shinri-dt/src/lib.rs` (above the test module):

```rust
use rustc_hash::FxHashSet;
use shinri_core::{Context, DtRole, Lit, Op, TermId, TermNode, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
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
    /// Lemmas already emitted, so `check` reaches a fixpoint instead of
    /// re-emitting the same tautology forever.
    emitted: FxHashSet<TermId>,
}

impl DtSolver {
    /// Walk an atom's term DAG, indexing every datatype-relevant application.
    fn collect(&mut self, terms: &Context, t: TermId) {
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
            self.collect(terms, k);
        }
    }

    /// `(symbol, children)` of an uninterpreted application, or `None`.
    fn uapp(terms: &Context, t: TermId) -> Option<(shinri_core::SymbolId, Vec<TermId>)> {
        match terms.term_node(t) {
            TermNode::App { op: Op::Uninterpreted(s), args, .. } => {
                Some((*s, terms.children(*args).to_vec()))
            }
            _ => None,
        }
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
}

impl TheorySolver for DtSolver {
    const THEORY_ID: u16 = 5;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        self.collect(cx.terms, atom);
    }

    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
        None
    }

    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        None
    }

    fn check(&mut self, _cx: &mut TheoryCtx, _effort: Effort) -> TCheck {
        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
        // DT conflicts cite EqLeafs directly; no tags of its own yet.
    }

    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn push(&mut self) {}
    fn pop(&mut self, _level: usize) {}
}
```

`collect` recurses over the term DAG exactly as `shinri-arrays::collect` does; it runs on interned solver terms, not on untrusted text, so the threat model's iteration requirement does not apply here.

- [ ] **Step 5: Run the test**

Run: `cargo test -p shinri-dt -- --nocapture`
Expected: PASS, 1 test.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add Cargo.toml crates/shinri-dt/
git commit -m "feat(dt): slice39 T5 — shinri-dt crate skeleton with registration index"
```

---

### Task 6: Selector-collapse tautology (and injectivity as its consequence)

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs`
- Test: `crates/shinri-dt/src/lib.rs` (inline tests)

**Interfaces:**
- Consumes: Task 5's `ctor_apps` / `sel_apps` / `emitted`, `uapp`.
- Produces: `DtSolver::check` returns `TCheck::Split { atoms: vec![lemma], guard: None, phases: Vec::new() }` where `lemma` is `mk_eq(sel_i(C(a…)), a_i)`.

The rule: for a selector application `selᵢ(t)` and a constructor application `C(a₁…aₙ)` in the **same class as `t`**, emit `selᵢ(C(a₁…aₙ)) = aᵢ`. This is an unconditional tautology, so `guard: None`. It fires only when `selᵢ` belongs to `C`; a foreign selector leaves the value unspecified and must not collapse.

- [ ] **Step 1: Write the failing tests**

Add to `mod tests` in `crates/shinri-dt/src/lib.rs`:

```rust
    use shinri_core::BuiltinOp;
    use shinri_sat::Effort;
    use shinri_theory::{EqJust, TCheck};

    fn tcheck_name(c: &TCheck) -> &'static str {
        match c {
            TCheck::Sat => "Sat",
            TCheck::Conflict(_) => "Conflict",
            TCheck::Split { .. } => "Split",
            TCheck::Unknown => "Unknown",
        }
    }

    #[test]
    fn selector_collapse_emits_tautology_for_matching_constructor() {
        let mut ctx = Context::new();
        let (list, nil, cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let one = uconst(&mut ctx, "one", ctx.int_sort());
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let head_x = ctx.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
        let atom = ctx.mk_eq(head_x, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), cons_t);

        // Before x ≡ cons(1,nil) there is nothing to collapse.
        assert!(matches!(dt.check(&mut cx, Effort::Full), TCheck::Sat));

        // Merge x with the constructor application.
        let xn = cx.eq.intern(x);
        let cn = cx.eq.intern(cons_t);
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Split { atoms, guard, .. } => {
                assert_eq!(guard, None, "collapse is an unconditional tautology");
                assert_eq!(atoms.len(), 1, "collapse emits a unit lemma");
                // The lemma is `head(cons(1,nil)) = 1`.
                let expected_sel = cx
                    .terms
                    .mk_app(Op::Uninterpreted(head), &[cons_t])
                    .unwrap();
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
        let one = uconst(&mut ctx, "one", ctx.int_sort());
        let atom = ctx.mk_eq(head_x, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
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
        let one = uconst(&mut ctx, "one", ctx.int_sort());
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let head_c = ctx.mk_app(Op::Uninterpreted(head), &[cons_t]).unwrap();
        let atom = ctx.mk_eq(head_c, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, Var::new(0), atom);
        assert!(matches!(dt.check(&mut cx, Effort::Full), TCheck::Split { .. }));
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
        // cons(a, nil) ≡ cons(b, nil)  ⇒  a ≡ b, with NO dedicated injectivity
        // rule: the two collapse lemmas plus congruence on `head` suffice.
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
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), head_ca);
        dt.new_var(&mut cx, Var::new(2), head_cb);

        // The SAT/EUF layer merges the two constructor apps and, by congruence,
        // their head-applications. Simulate both here.
        let (can, cbn) = (cx.eq.intern(ca), cx.eq.intern(cb));
        let _ = cx.eq.merge(can, cbn, EqJust::Definitional);
        let (hca, hcb) = (cx.eq.intern(head_ca), cx.eq.intern(head_cb));
        let _ = cx.eq.merge(hca, hcb, EqJust::Definitional);

        // Drain both collapse lemmas, installing each as the SAT layer would.
        for _ in 0..2 {
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
                other => panic!("expected Split, got {}", tcheck_name(&other)),
            }
        }

        let (an, bn) = (cx.eq.intern(a), cx.eq.intern(b));
        assert!(
            cx.eq.are_equal(an, bn),
            "injectivity must emerge: a ≡ b after collapse + congruence"
        );
    }
```

Add `BuiltinOp` to the test imports only if the equality destructuring needs it; the `mk_eq` term is an `App` whose children are the two sides.

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-dt selector_collapse injectivity collapse_reaches -- --nocapture`
Expected: FAIL — `check` returns `Sat` unconditionally, so the Split assertions fail.

- [ ] **Step 3: Implement the rule**

Replace `DtSolver::check` in `crates/shinri-dt/src/lib.rs`:

```rust
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        if let Some(split) = self.collapse_lemma(cx) {
            return split;
        }
        TCheck::Sat
    }
```

and add to the `impl DtSolver` block:

```rust
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
            let (sel_sym, sel_args) = Self::uapp(cx.terms, sel)?;
            let Some(DtRole::Selector { ctor, index }) = cx.terms.dt_role(sel_sym) else {
                continue;
            };
            let t = sel_args[0];
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
                let arg = cargs[index as usize];
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
                    continue; // emitted before and not yet installed; avoid a loop
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
```

Note the `?` in `let (sel_sym, sel_args) = Self::uapp(...)?;` returns `None` from `collapse_lemma`, which the caller reads as "no lemma" — acceptable because a non-application in `sel_apps` is impossible by construction. If clippy objects, replace with a `let ... else { continue; }`.

- [ ] **Step 4: Run the tests**

Run: `cargo test -p shinri-dt -- --nocapture`
Expected: PASS, 5 tests.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-dt/src/lib.rs
git commit -m "feat(dt): slice39 T6 — selector-collapse tautology; injectivity emerges via congruence"
```

---

### Task 7: Constructor clash, tester tautology, tester disjointness

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs`
- Test: `crates/shinri-dt/src/lib.rs` (inline tests)

**Interfaces:**
- Consumes: Task 6's `check`/`collapse_lemma`; `EqualityEngine::explain(a, b, &mut Vec<EqLeaf>)`.
- Produces: `DtSolver::check` also returns `TCheck::Conflict(leaves)` on a constructor clash and a unit `Split` for `is-C(C(a…))`; `DtSolver::assert` returns conflict leaves when an asserted tester contradicts a constructor in its class.

Tester disjointness lives in `assert`, not `check`, because its consequence `¬is-D(t)` is a **negative** literal and `TCheck::Split` carries only positive atoms.

- [ ] **Step 1: Write the failing tests**

Add to `mod tests`:

```rust
    #[test]
    fn constructor_clash_is_a_conflict() {
        let mut ctx = Context::new();
        let (list, nil, cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let one = uconst(&mut ctx, "one", ctx.int_sort());
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let a1 = ctx.mk_eq(x, nil_t).unwrap();
        let a2 = ctx.mk_eq(x, cons_t).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
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
        let one = uconst(&mut ctx, "one", ctx.int_sort());
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let is_cons_c = ctx.mk_app(Op::Uninterpreted(is_cons), &[cons_t]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, Var::new(0), is_cons_c);

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Split { atoms, guard, .. } => {
                assert_eq!(guard, None);
                assert_eq!(atoms, vec![is_cons_c]);
            }
            other => panic!("expected Split, got {}", tcheck_name(&other)),
        }
    }

    #[test]
    fn asserted_tester_conflicting_with_constructor_is_rejected_at_assert() {
        // is-nil(x) asserted true while x ≡ cons(1,nil) ⇒ conflict.
        let mut ctx = Context::new();
        let (list, nil, cons, _head, _tail, is_nil, _is_cons) = list_dt(&mut ctx);
        let one = uconst(&mut ctx, "one", ctx.int_sort());
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let is_nil_x = ctx.mk_app(Op::Uninterpreted(is_nil), &[x]).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        let v = Var::new(0);
        atoms.register(v, is_nil_x, shinri_theory::types::Owner::Datatypes);
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, v, is_nil_x);
        dt.new_var(&mut cx, Var::new(1), cons_t);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(cons_t));
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        let conflict = dt.assert(&mut cx, Lit::pos(v));
        assert!(
            conflict.is_some(),
            "is-nil(x) with x ≡ cons(..) must conflict at assert time"
        );
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
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, v, is_nil_x);
        dt.new_var(&mut cx, Var::new(1), nil_t);
        let (xn, nn) = (cx.eq.intern(x), cx.eq.intern(nil_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        assert!(dt.assert(&mut cx, Lit::pos(v)).is_none());
    }
```

`AtomRegistry::register` may have a different name or signature — read `crates/shinri-theory/src/atom.rs` and use the actual registration entry point (the Combiner calls it from `register_atom`). `Owner::Datatypes` arrives in Task 9; until then use any existing variant in these two tests and switch to `Datatypes` as part of Task 9's step that updates call sites.

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-dt constructor_clash tester_over asserted_tester -- --nocapture`
Expected: FAIL — `check` returns `Sat`/collapse only and `assert` returns `None`.

- [ ] **Step 3: Implement clash + tester tautology in `check`**

Extend `check`:

```rust
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        if let Some(conflict) = self.constructor_clash(cx) {
            return conflict;
        }
        if let Some(split) = self.collapse_lemma(cx) {
            return split;
        }
        if let Some(split) = self.tester_lemma(cx) {
            return split;
        }
        TCheck::Sat
    }
```

and add both rules to `impl DtSolver`:

```rust
    /// Two DISTINCT constructor applications in one class are contradictory.
    /// The explanation is the merge path that made them equal.
    fn constructor_clash(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        let ctors: Vec<TermId> = self.ctor_apps.iter().copied().collect();
        for (i, &p) in ctors.iter().enumerate() {
            let Some((psym, _)) = Self::uapp(cx.terms, p) else {
                continue;
            };
            let pn = cx.eq.intern(p);
            for &q in &ctors[i + 1..] {
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

    /// `is-C(t)` where `t`'s class holds `C(a1..an)` is a valid UNIT tautology.
    /// (The negative direction `¬is-D(t)` cannot ride `Split`, whose atoms are
    /// positive; it is handled at assert time instead.)
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
            let tn = cx.eq.intern(targs[0]);
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
                if !self.emitted.insert(tst) {
                    continue;
                }
                return Some(TCheck::Split {
                    atoms: vec![tst],
                    guard: None,
                    phases: Vec::new(),
                });
            }
        }
        None
    }

    /// The constructor application in `t`'s class, if any.
    fn ctor_of_class(&self, cx: &mut TheoryCtx, t: TermId) -> Option<(shinri_core::SymbolId, TermId)> {
        let tn = cx.eq.intern(t);
        let ctors: Vec<TermId> = self.ctor_apps.iter().copied().collect();
        for capp in ctors {
            let (csym, _) = Self::uapp(cx.terms, capp)?;
            let cn = cx.eq.intern(capp);
            if cx.eq.are_equal(tn, cn) {
                return Some((csym, capp));
            }
        }
        None
    }
```

- [ ] **Step 4: Implement tester disjointness in `assert`**

Replace `DtSolver::assert`:

```rust
    /// Tester disjointness: an asserted `is-D(t)` whose class already holds a
    /// `C(..)` with `C != D` is an immediate conflict. Handled here rather than
    /// in `check` because the consequence `¬is-D(t)` is a NEGATIVE literal and
    /// `TCheck::Split` carries only positive atoms.
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        if lit.is_neg() {
            return None; // ¬is-D(t) constrains nothing in slice 39
        }
        let atom = cx.atoms.atom(lit.var())?;
        let (tsym, targs) = Self::uapp(cx.terms, atom)?;
        let DtRole::Tester { ctor } = cx.terms.dt_role(tsym)? else {
            return None;
        };
        let (csym, capp) = self.ctor_of_class(cx, targs[0])?;
        if csym == ctor {
            return None; // agrees
        }
        let tn = cx.eq.intern(targs[0]);
        let cn = cx.eq.intern(capp);
        let mut leaves = vec![EqLeaf::Asserted(lit)];
        cx.eq.explain(tn, cn, &mut leaves);
        Some(leaves)
    }
```

`cx.atoms.atom(var)` is the atom lookup on `AtomRegistry` — confirm its real name in `crates/shinri-theory/src/atom.rs` (the Combiner uses `self.atoms.owner(...)` nearby) and use that. `Lit::is_neg` likewise: match the accessor used in `crates/shinri-str/src/lib.rs`'s `assert`.

- [ ] **Step 5: Run the tests**

Run: `cargo test -p shinri-dt -- --nocapture`
Expected: PASS, 9 tests.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-dt/src/lib.rs
git commit -m "feat(dt): slice39 T7 — constructor clash conflict, tester tautology, assert-time disjointness"
```

---

### Task 8: The completeness fence and datatype models

**Files:**
- Modify: `crates/shinri-dt/src/lib.rs`
- Modify: `crates/shinri-theory/src/types.rs` (`ModelVal::Datatype`)
- Modify: `crates/shinri-solver/src/model.rs` (formatting)
- Test: `crates/shinri-dt/src/lib.rs` (inline tests)

**Interfaces:**
- Consumes: Task 7's `ctor_of_class`.
- Produces: `check` returns `TCheck::Unknown` when a datatype term's class is not constructor-determined; `ModelVal::Datatype(String)` carrying a rendered ground constructor term; `DtSolver::model` populating it.

Spec §5.2: slice 39 decides `unsat` fully but must never answer a possibly-wrong `sat`. `Sat` is returned only when every registered datatype-sorted term's class is constructor-determined — it contains a constructor application, or an asserted tester pins its constructor.

`ModelVal::Datatype` carries a **pre-rendered string** rather than a `TermId` because `format_modelval` in `crates/shinri-solver/src/model.rs:87` has no `Context` to render with, and `shinri-theory` cannot depend on `shinri-parser`'s printer.

- [ ] **Step 1: Write the failing tests**

Add to `mod tests`:

```rust
    #[test]
    fn undetermined_datatype_class_yields_unknown_not_sat() {
        // `x` is a List with no constructor in its class and no tester pinning
        // it. Exhaustiveness (slice 40) is what would decide this, so slice 39
        // must fence to Unknown rather than claim Sat.
        let mut ctx = Context::new();
        let (list, _nil, _cons, _head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);
        let y = uconst(&mut ctx, "y", list);
        let atom = ctx.mk_eq(x, y).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, Var::new(0), atom);

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
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
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
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        dt.new_var(&mut cx, Var::new(0), atom);
        let (xn, nn) = (cx.eq.intern(x), cx.eq.intern(nil_t));
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        let mut m = ModelBuilder::default();
        dt.model(&mut cx, &mut m);
        match m.get(x) {
            Some(shinri_theory::types::ModelVal::Datatype(s)) => assert_eq!(s, "nil"),
            other => panic!("expected a datatype model value, got {other:?}"),
        }
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-dt undetermined determined model_assigns -- --nocapture`
Expected: FAIL — `check` returns `Sat` for the undetermined case; `ModelVal::Datatype` does not exist.

- [ ] **Step 3: Add the model value variant**

In `crates/shinri-theory/src/types.rs`, add to `enum ModelVal`:

```rust
    /// A datatype value, pre-rendered as an SMT-LIB ground constructor term
    /// (e.g. `nil`, `(cons 1 nil)`). Rendered by the DT theory, which has the
    /// `Context`; `format_modelval` has none.
    Datatype(std::string::String),
```

In `crates/shinri-solver/src/model.rs`, add to the `format_modelval` match:

```rust
        ModelVal::Datatype(s) => s.clone(),
```

- [ ] **Step 4: Implement the fence and the model**

Extend `check` with the fence as its **last** step (all rules must be saturated before fencing):

```rust
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        if let Some(conflict) = self.constructor_clash(cx) {
            return conflict;
        }
        if let Some(split) = self.collapse_lemma(cx) {
            return split;
        }
        if let Some(split) = self.tester_lemma(cx) {
            return split;
        }
        // Slice-39 completeness fence (spec §5.2): exhaustiveness — that every
        // datatype term IS some constructor — needs the case split that lands in
        // slice 40. Until then, a class whose constructor is undetermined must
        // NOT be reported Sat.
        if self.has_undetermined_class(cx) {
            return TCheck::Unknown;
        }
        TCheck::Sat
    }
```

and add to `impl DtSolver`:

```rust
    /// Every datatype-sorted term this theory watches, from both selector
    /// arguments and tester arguments, plus the constructor apps themselves.
    fn watched_dt_terms(&self, cx: &mut TheoryCtx) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        for &s in &self.sel_apps {
            if let Some((_, args)) = Self::uapp(cx.terms, s) {
                out.push(args[0]);
            }
        }
        for &t in &self.testers {
            if let Some((_, args)) = Self::uapp(cx.terms, t) {
                out.push(args[0]);
            }
        }
        out
    }

    /// True iff some watched datatype term's class has no constructor
    /// application and no tester pinning its constructor.
    fn has_undetermined_class(&mut self, cx: &mut TheoryCtx) -> bool {
        for t in self.watched_dt_terms(cx) {
            if self.ctor_of_class(cx, t).is_some() {
                continue;
            }
            return true;
        }
        false
    }

    /// Render the ground constructor term for `t`'s class, or `None` when the
    /// class is not constructor-determined (the fence keeps this unreachable
    /// on a Sat answer).
    fn render_value(&self, cx: &mut TheoryCtx, t: TermId, depth: u32) -> Option<String> {
        if depth > 64 {
            return None; // defensive: well-foundedness bounds real recursion
        }
        let (csym, capp) = self.ctor_of_class(cx, t)?;
        let (_, cargs) = Self::uapp(cx.terms, capp)?;
        let name = cx.terms.symbol_name(csym).to_string();
        if cargs.is_empty() {
            return Some(name);
        }
        let mut parts = Vec::with_capacity(cargs.len());
        for a in cargs {
            let rendered = if cx.terms.is_datatype_sort(cx.terms.sort_of(a)) {
                self.render_value(cx, a, depth + 1)?
            } else {
                // Non-datatype fields are owned by other theories; print the
                // term's symbol name when it is a plain constant.
                match Self::uapp(cx.terms, a) {
                    Some((s, kids)) if kids.is_empty() => {
                        cx.terms.symbol_name(s).to_string()
                    }
                    _ => "?".to_string(),
                }
            };
            parts.push(rendered);
        }
        Some(format!("({} {})", name, parts.join(" ")))
    }
```

and replace `model`:

```rust
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        for t in self.watched_dt_terms(cx) {
            if m.get(t).is_some() {
                continue;
            }
            if let Some(v) = self.render_value(cx, t, 0) {
                m.assign(t, shinri_theory::types::ModelVal::Datatype(v));
            }
        }
    }
```

`render_value` takes `&self` but `ctor_of_class` takes `&self` too — keep both immutable; if borrow-checking against `cx` forces a signature change, take `&mut self` uniformly.

- [ ] **Step 5: Run the tests**

Run: `cargo test -p shinri-dt -- --nocapture`
Expected: PASS, 12 tests.

Run: `cargo build --workspace`
Expected: clean (the new `ModelVal` variant may require a match arm in `crates/shinri-solver/src/lib.rs` — add one that treats it as opaque).

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-dt/src/lib.rs crates/shinri-theory/src/types.rs crates/shinri-solver/src/model.rs
git commit -m "feat(dt): slice39 T8 — completeness fence (Unknown) and datatype model values"
```

---

### Task 9: Combiner fifth slot and `classify` routing

**Files:**
- Modify: `crates/shinri-theory/src/types.rs` (`Owner::Datatypes`)
- Modify: `crates/shinri-theory/src/atom.rs` (`classify`)
- Modify: `crates/shinri-theory/src/combiner.rs` (generic `D`, all dispatch sites)
- Test: `crates/shinri-theory/src/atom.rs`, `crates/shinri-theory/src/combiner.rs` (inline tests)

**Interfaces:**
- Consumes: Task 8's `DtSolver` (only via the generic parameter — `shinri-theory` does **not** depend on `shinri-dt`).
- Produces: `Owner::Datatypes`; `Combiner<E, A, R, S, D>` with `dt_mut(&mut self) -> &mut D`.

Datatype atoms route to **both** EUF (for congruence over constructor/selector applications) and the DT slot — the `Owner::Arrays` pattern at `combiner.rs:163`.

- [ ] **Step 1: Write the failing test**

Add to `#[cfg(test)] mod tests` in `crates/shinri-theory/src/atom.rs`:

```rust
    #[test]
    fn datatype_equality_and_tester_route_to_datatypes() {
        let mut ctx = Context::new();
        let list = ctx.declare_datatype_sort("List");
        let b = ctx.bool_sort();
        let nil = ctx.declare_fun("nil", &[], list);
        let is_nil = ctx.declare_fun("is-nil", &[list], b);
        ctx.dt_add_constructor(list, nil, &[], is_nil);
        let xs = ctx.declare_fun("x", &[], list);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();

        let eq_atom = ctx.mk_eq(x, nil_t).unwrap();
        assert_eq!(classify(&ctx, eq_atom), Ok(Owner::Datatypes));

        let tester = ctx.mk_app(Op::Uninterpreted(is_nil), &[x]).unwrap();
        assert_eq!(classify(&ctx, tester), Ok(Owner::Datatypes));
    }
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-theory datatype_equality_and_tester -- --nocapture`
Expected: FAIL to compile — `no variant named 'Datatypes'`.

- [ ] **Step 3: Add the Owner variant and classify routing**

In `crates/shinri-theory/src/types.rs`:

```rust
pub enum Owner {
    Euf,
    Arith,
    Shared,
    Arrays,
    String,
    Datatypes,
}
```

In `crates/shinri-theory/src/atom.rs`, inside `classify`, add **before** the EUF fallback and after the array/string routing:

```rust
    // Datatype routing: a tester application, or a (dis)equality over
    // datatype-sorted operands, belongs to the DT theory. EUF still interns the
    // terms for congruence (see the Owner::Datatypes routing in the Combiner).
    if let TermNode::App { op: Op::Uninterpreted(sym), .. } = terms.term_node(atom) {
        if matches!(terms.dt_role(*sym), Some(shinri_core::DtRole::Tester { .. })) {
            return Ok(Owner::Datatypes);
        }
    }
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
        args,
        ..
    } = terms.term_node(atom)
    {
        if terms
            .children(*args)
            .iter()
            .any(|&c| terms.is_datatype_sort(terms.sort_of(c)))
        {
            return Ok(Owner::Datatypes);
        }
    }
```

- [ ] **Step 4: Add the fifth generic slot**

In `crates/shinri-theory/src/combiner.rs`, mechanically extend the generic list. Every occurrence of

```rust
impl<E: TheorySolver, A: TheorySolver, R: TheorySolver, S: TheorySolver>
```

becomes

```rust
impl<E: TheorySolver, A: TheorySolver, R: TheorySolver, S: TheorySolver, D: TheorySolver>
```

and every `Combiner<E, A, R, S>` becomes `Combiner<E, A, R, S, D>`. Add the field:

```rust
    dt: D,
```

initialized in `with_context` as `dt: D::default(),`, and the accessor:

```rust
    /// Mutable access to the datatype theory slot (mirrors `arrays_mut`).
    pub fn dt_mut(&mut self) -> &mut D {
        &mut self.dt
    }
```

- [ ] **Step 5: Route `Owner::Datatypes` at every dispatch site**

Five sites, each mirroring the `Owner::Arrays` arm directly above it:

`register_atom` (near line 163):

```rust
            Owner::Datatypes => {
                let mut cx = TheoryCtx {
                    terms: &mut self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.euf.new_var(&mut cx, v, atom);
                self.dt.new_var(&mut cx, v, atom);
            }
```

`assert` (near line 250):

```rust
            Owner::Datatypes => {
                let e = self.euf.assert(&mut cx, lit);
                let d = self.dt.assert(&mut cx, lit);
                e.or(d)
            }
```

`new_var` split-atom routing (near line 357):

```rust
            Owner::Datatypes => {
                self.euf.new_var(&mut cx, v, atom);
                self.dt.new_var(&mut cx, v, atom);
            }
```

`push`/`pop` (near lines 385/423):

```rust
        self.dt.push();
```
```rust
        self.dt.pop(target);
```

`drive_final_check` — insert **after** the arrays check (near line 556) and before the string check. Unlike arrays, DT **can** return `Unknown` (the §5.2 fence), so it must be propagated, not `unreachable!`:

```rust
                match self.dt.check(&mut cx, Effort::Full) {
                    TCheck::Conflict(cf) => return FinalCheck::Conflict(cf),
                    TCheck::Split { atoms, guard, phases } => {
                        return FinalCheck::Split { atoms, guard, phases }
                    }
                    TCheck::Sat => {}
                    // Slice-39 completeness fence: sound Unknown, never a
                    // possibly-wrong Sat.
                    TCheck::Unknown => return FinalCheck::Unknown,
                }
```

`explain` dispatch (near line 902):

```rust
            } else if j.theory == D::THEORY_ID {
                self.dt.explain(&mut cx, j.tag, exp);
```

`model` (near line 862):

```rust
            let mut dt_m = ModelBuilder::default();
            self.dt.model(&mut cx, &mut dt_m);
```

then absorb it exactly as the arrays model is absorbed a few lines below.

- [ ] **Step 6: Fix the existing Combiner tests**

Every test instantiating a 4-slot `Combiner` now needs a fifth. Use `EmptyTheory` (`shinri_theory::EmptyTheory`, `THEORY_ID = 0`) as the inert fifth slot.

Run: `cargo build --workspace --all-targets 2>&1 | grep -c "^error"`
Expected: a count; fix each `Combiner<...>` instantiation by appending `, EmptyTheory`.

Note: a stub in `combiner.rs` tests already uses `THEORY_ID = 5` (line 1237). If it ends up in the same instantiation as a real `DtSolver`, `explain` dispatch would be ambiguous. It is only used in 4-slot stub tests, so appending `EmptyTheory` is sufficient — but if any test places that stub in the `D` slot, renumber the stub to `6`.

- [ ] **Step 7: Run the tests**

Run: `cargo test -p shinri-theory -- --nocapture`
Expected: PASS, including the new classify test.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
git add crates/shinri-theory/
git commit -m "feat(dt): slice39 T9 — Owner::Datatypes, classify routing, Combiner fifth slot"
```

---

### Task 10: Wire `DtSolver` into the solver, end-to-end

**Files:**
- Modify: `crates/shinri-solver/Cargo.toml`
- Modify: `crates/shinri-solver/src/lib.rs:369,711` (Combiner instantiation)
- Modify: `crates/shinri-solver/src/tseitin.rs:13,273` (type alias + atom routing)
- Create: `crates/shinri-solver/tests/qfdt_e2e.rs`

**Interfaces:**
- Consumes: Task 9's `Combiner<E, A, R, S, D>`; Task 8's `DtSolver`.
- Produces: the concrete solver type `Combiner<Euf, Arith, Arrays, StrSolver, DtSolver>`; end-to-end QF_DT decisions through `Parser` + `Solver::execute`.

- [ ] **Step 1: Write the failing e2e tests**

Create `crates/shinri-solver/tests/qfdt_e2e.rs`:

```rust
//! End-to-end QF_DT witnesses: SMT-LIB text -> parser -> solver.
//! Covers selector-collapse, injectivity (an emergent consequence), constructor
//! disjointness, tester consistency, and the slice-39 completeness fence.

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn run_script(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

const LIST: &str = "(declare-datatype List ((nil) (cons (head Int) (tail List))))";

#[test]
fn selector_over_constructor_unsat() {
    // head(cons(1, nil)) != 1  is UNSAT
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (assert (distinct (head (cons 1 nil)) 1))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn constructor_disjointness_unsat() {
    // x = nil  and  x = cons(1, nil)  is UNSAT
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (= x nil))(assert (= x (cons 1 nil)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn injectivity_unsat() {
    // cons(a, nil) = cons(b, nil)  and  a != b  is UNSAT.
    // No dedicated injectivity rule: collapse lemmas + congruence deliver it.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (declare-fun a () Int)(declare-fun b () Int)\
         (assert (= (cons a nil) (cons b nil)))(assert (distinct a b))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn tester_contradicting_constructor_unsat() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (= x (cons 1 nil)))(assert ((_ is nil) x))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn tester_agreeing_with_constructor_sat() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (= x (cons 1 nil)))(assert ((_ is cons) x))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn uf_over_datatype_congruence_unsat() {
    // f(x) != f(y) with x = y  is UNSAT — datatype sorts under a UF.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (declare-fun x () List)(declare-fun y () List)\
         (declare-fun f (List) Int)\
         (assert (= x y))(assert (distinct (f x) (f y)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn undetermined_constructor_fences_to_unknown() {
    // The slice-39 completeness fence (spec §5.2). Exhaustiveness — that x must
    // be SOME constructor — needs the case split landing in slice 40, so this
    // UNSAT query is reported `unknown` rather than wrongly `sat`.
    // SLICE 40 WILL FLIP THIS PIN TO `unsat`.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (not ((_ is nil) x)))(assert (not ((_ is cons) x)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unknown"], "slice-39 fence: see spec §5.2");
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo nextest run -p shinri-solver -E 'test(qfdt_e2e)'`
Expected: FAIL — DT is not wired in, so queries return `unknown` or the wrong result.

Confirm a non-zero test count in the output before trusting the run.

- [ ] **Step 3: Add the dependency**

In `crates/shinri-solver/Cargo.toml`, add to `[dependencies]`:

```toml
shinri-dt = { path = "../shinri-dt" }
```

- [ ] **Step 4: Instantiate the 5-tuple**

In `crates/shinri-solver/src/tseitin.rs:13`:

```rust
    Combiner<Euf, shinri_arith::Arith, shinri_arrays::Arrays, shinri_str::StrSolver, shinri_dt::DtSolver>,
```

In `crates/shinri-solver/src/lib.rs:369`, make the same substitution.

In `crates/shinri-solver/src/tseitin.rs:273`, add a routing arm mirroring `Owner::Arrays`:

```rust
                Ok(shinri_theory::types::Owner::Datatypes) => {
                    // Datatype atoms are EUF-adjacent (constructors/selectors/
                    // testers are uninterpreted apps); register as a theory atom.
```

Match the body of the neighbouring `Owner::Arrays` arm exactly.

- [ ] **Step 5: Build and fix remaining match sites**

Run: `cargo build --workspace --all-targets`
Expected: errors listing every non-exhaustive `match` over `Owner`. Add a `Datatypes` arm to each, mirroring `Arrays`.

Run: `cargo build --workspace --all-targets`
Expected: clean build.

- [ ] **Step 6: Run the tests**

Run: `cargo nextest run -p shinri-solver -E 'test(qfdt_e2e)'`
Expected: PASS, 7 tests. Confirm the count is 7, not 0.

Run: `cargo nextest run --workspace`
Expected: PASS, no regressions. Pay attention to `script_e2e` — this slice shifts completeness.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/ Cargo.lock
git commit -m "feat(dt): slice39 T10 — wire DtSolver into the solver; QF_DT end-to-end"
```

---

### Task 11: Oracle differential tests, fuzz seeds, docs

**Files:**
- Create: `crates/shinri-solver/tests/qfdt_oracle.rs`
- Modify: `crates/shinri-parser/fuzz/` corpus seeds
- Modify: `README.md`
- Modify: `docs/superpowers/specs/2026-07-23-shinri-slice39-datatypes-foundation-design.md` (measured outcomes)

**Interfaces:**
- Consumes: Task 10's end-to-end path.
- Produces: `#![cfg(feature = "oracle")]` differential suite vs z3.

- [ ] **Step 1: Write the oracle test**

Create `crates/shinri-solver/tests/qfdt_oracle.rs`:

```rust
//! Differential oracle: shinri-solver vs z3 on QF_DT (datatypes + LIA).
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'test(qfdt_oracle)'
//!
//! Requires `z3` on PATH at runtime. Guarded by `#[cfg(feature = "oracle")]` —
//! WITHOUT the feature flag this file compiles to ZERO tests, which must never
//! be reported as passing coverage.
//!
//! SOUNDNESS contract: when shinri returns Sat or Unsat it MUST agree with z3.
//! Shinri `Unknown` (the slice-39 completeness fence, spec §5.2) is a
//! non-disagreement and is skipped.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn shinri_answer(src: &str) -> String {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut last = String::from("none");
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        if let Ok(cmd) = result {
            match solver.execute(cmd) {
                CommandResponse::Sat => last = "sat".into(),
                CommandResponse::Unsat => last = "unsat".into(),
                CommandResponse::Unknown => last = "unknown".into(),
                _ => {}
            }
        }
    }
    last
}
```

Then add the z3 invocation helper. **Copy the existing helper verbatim** from `crates/shinri-solver/tests/qfs_differential.rs` (the function that writes the script to a temp file and runs `z3`), renaming it if needed — do not invent a new subprocess wrapper, so the two suites stay consistent.

Add the cases:

```rust
const LIST: &str = "(declare-datatype List ((nil) (cons (head Int) (tail List))))";

fn agree(body: &str) {
    let src = format!("(set-logic QF_UFDTLIA){LIST}{body}(check-sat)");
    let ours = shinri_answer(&src);
    if ours == "unknown" {
        return; // slice-39 fence — not a disagreement
    }
    let theirs = z3_answer(&src);
    if theirs == "unknown" {
        return; // no ground truth
    }
    assert_eq!(ours, theirs, "disagreement on:\n{src}");
}

#[test]
fn qfdt_oracle_selector_collapse() {
    agree("(assert (distinct (head (cons 1 nil)) 1))");
}

#[test]
fn qfdt_oracle_injectivity() {
    agree(
        "(declare-fun a () Int)(declare-fun b () Int)\
         (assert (= (cons a nil) (cons b nil)))(assert (distinct a b))",
    );
}

#[test]
fn qfdt_oracle_disjointness() {
    agree("(declare-fun x () List)(assert (= x nil))(assert (= x (cons 1 nil)))");
}

#[test]
fn qfdt_oracle_tester_agreement() {
    agree("(declare-fun x () List)(assert (= x (cons 1 nil)))(assert ((_ is cons) x))");
}

#[test]
fn qfdt_oracle_nested_constructors() {
    agree(
        "(assert (distinct (head (tail (cons 1 (cons 2 nil)))) 2))",
    );
}

#[test]
fn qfdt_oracle_uf_over_datatype() {
    agree(
        "(declare-fun x () List)(declare-fun y () List)(declare-fun f (List) Int)\
         (assert (= x y))(assert (distinct (f x) (f y)))",
    );
}
```

- [ ] **Step 2: Run the oracle suite**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfdt_oracle)'`
Expected: PASS, **6 tests**. If the output says `0 tests run`, the feature flag or the filter is wrong — that is a failure, not a pass.

- [ ] **Step 3: Add fuzz corpus seeds**

Add seed files to the `parse_script` fuzz corpus directory (locate it under `crates/shinri-parser/fuzz/`; mirror the existing seed naming):

```
(declare-datatype List ((nil) (cons (head Int) (tail List))))(assert ((_ is nil) nil))(check-sat)
(declare-datatypes ((A 0) (B 0)) (((mkA (getB B))) ((base) (mkB (getA A)))))(check-sat)
(declare-datatype T ((c (f T))))
(declare-datatype E ())
(declare-datatypes ((L 1)) (((nil))))
```

Run: `ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run parse_script -- -runs=20000`
Expected: no crashes. (Local runs need `detect_leaks=0` — no ptrace in this environment; nightly CI is authoritative.)

- [ ] **Step 4: Update the README crate table**

Add a row after `shinri-str`:

```
| `shinri-dt` | QF_DT algebraic datatypes: lemma-on-demand over the shared e-graph |
```

- [ ] **Step 5: Run the full gate**

Run: `mise run lint`
Expected: clean — fmt and clippy both pass.

Run: `mise run test`
Expected: PASS within the 10–15 min blocking budget.

Run: `cargo nextest run -p shinri-solver --features oracle`
Expected: PASS with a non-zero test count.

- [ ] **Step 6: Truth up the spec's measured outcomes**

Append a `## 10. Measured outcomes` section to the design doc recording, with real numbers: which rules fired in the e2e suite, the oracle test count and result, blocking-tier wall-clock before and after, and any success criterion in §9 that was **not** met. Mark each §9 criterion explicitly. Do not claim a criterion passed without the command output that proves it.

- [ ] **Step 7: Commit and open the PR**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfdt_oracle.rs crates/shinri-parser/fuzz/ README.md docs/superpowers/specs/
git commit -m "test+docs(dt): slice39 T11 — QF_DT oracle differential, fuzz seeds, measured outcomes"
git push -u origin slice39-datatypes-foundation
gh pr create --title "slice39: datatypes theory foundation (spine + definitional rules)" --body "Implements docs/superpowers/specs/2026-07-23-shinri-slice39-datatypes-foundation-design.md"
```

---

## Self-Review

**Spec coverage.** §2 representation → T1. §3 parser and the full rejection table → T3 (tester syntax → T4). §4 architecture / `THEORY_ID = 5` → T5. §5.1 selector-collapse and injectivity → T6; clash and tester rules → T7. §5.2 fence → T8. §6 channels table → T6/T7 (Split, Conflict, assert); Combiner routing → T9; models → T8. §7 testing: unit → T6–T8, parser → T3, e2e → T10, oracle → T11. §8 roadmap is forward-looking, no task. §9 success criteria → verified in T11 step 5–6.

**Known soft spots**, flagged rather than hidden — the implementer must verify against the code, and each step says so inline:
- `AtomRegistry`'s atom-lookup method name (T7 step 4) and `Lit::is_neg` — confirm against `crates/shinri-theory/src/atom.rs` and `crates/shinri-str/src/lib.rs`.
- The parser's `"_"` term arm returns via a bound `result` rather than early `return` (T4 step 3); exactly one consumer per closing paren.
- `Context::sort_node` accessor name (T1 step 5).

**Type consistency.** `DtRole` variants, `dt_*` accessor names, `DtSolver` field names (`ctor_apps`/`sel_apps`/`testers`/`emitted`), `ctor_of_class` returning `(SymbolId, TermId)`, and `ModelVal::Datatype(String)` are used identically across T1–T11.
