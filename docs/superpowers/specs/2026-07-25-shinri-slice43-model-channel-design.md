# Slice 43 — The model channel: datatype field values and conformant `get-model`

**Status:** design
**Date:** 2026-07-25
**Area:** `shinri-dt` (`model`, `render_value_inner`), `shinri-theory`
(`Combiner::build_model` ordering; `format_modelval` relocation), `shinri-euf`
(one skip in `model`), `shinri-core` (a new sort printer), `shinri-solver`
(`format_model`, `GetValue`, `display_term`, a declared-symbol registry). No new
crate, no new theory slot, no `shinri-parser` surface change.
**Predecessors:** slice 39 introduced `DtSolver::render_value` and the
`?` placeholder; slice 40 minted the in-search selector applications that make
the placeholder unavoidable today; slice 42 deferred the placeholder fix here.
No lemma, guard, or search path from 39–42 is modified.

## 1. Summary

Slice 39's roadmap (§8 of its design) assigns slice 43 *"Nelson–Oppen with
arithmetic — Int/Real datatype fields ⋈ arith; completes QF_UFDTLIA."* Probing
the release binary shows the **verdict** half of that is already done:

| Query | shinri | Correct |
|---|---|---|
| `((_ is cons) l)` ∧ `(> (head l) 5)` | `sat` | ✓ |
| `a=cons(x,nil)` ∧ `b=cons(y,nil)` ∧ `a=b` ∧ `x≠y` | `unsat` | ✓ (injectivity → arith) |
| `x+1=y+1` ∧ `cons(x,nil)≠cons(y,nil)` | `unsat` | ✓ (arith → congruence) |
| `cons(x,nil)≠cons(y,nil)` ∧ `x=y` | `unsat` | ✓ |

The unfinished half is the **model channel**. Measured output, verbatim:

| Probe | Query shape | `get-model` today |
|---|---|---|
| C1 | `((_ is cons) l)` | `((t3 true)(l (cons ? nil)))` |
| C2 | `l = (cons 1 nil)` | `((l (cons ? nil))(nil nil)(t5 (cons ? nil))(t3 1))` |
| C3 | `((_ is cons) l)` ∧ `(head l) = 42` | `((l (cons ? nil))(t4 42)(t5 42)(t3 true))` |
| C4 | `((_ is cons) l)` ∧ `((_ is cons) (tail l))` | `((l (cons ? (cons ? nil)))(t4 (cons ? nil))(t5 true)(t3 true))` |
| M3 | `l = (cons 1 (cons 2 nil))` | `((t6 (cons ? nil))(t4 2)(l (cons ? (cons ? nil)))(t7 (cons ? (cons ? nil)))(t3 1)(nil nil))` |
| M4 | `(declare-fun p () P)`, `P` has a `U`-sorted field, **no assertions** | `()` |
| M4b | as M4 plus `(declare-fun q () P)` and `(assert (= p q))` | `((p (mk ?))(q (mk ?)))` |
| M4c | `(declare-fun x () Int)`, **no assertions** | `()` |
| M5 | `(declare-datatype B ((mk (b Bool))))`, `(b z)` asserted | `((t3 true)(z (mk ?)))` |

`(get-value ((head l) l))` returns `((t4 7) (l (cons ? nil)))` — right values,
labelled with internal ids instead of the requested terms.

Four defects are visible, with three independent root causes:

1. **Every non-datatype field renders `?`** — including a *literal* field (C2:
   the value `1` is in the same model as `t3 1`) and a field whose value arith
   has pinned (C3: `42` appears twice).
2. **Internal `tN` ids appear as model entry names**, and entries exist for
   terms the user never declared (`nil`, `t5`).
3. **A declared symbol occurring in no assertion is missing entirely** (M4
   returns `()`). This is *not* DT-specific: M4c shows a plain `Int` constant
   vanishing the same way. M4b is the control — once `p` appears in an
   assertion, DT does render it, so the missing entry is about the symbol never
   reaching any theory, not about datatypes.
4. **`get-value` labels responses with `tN`** rather than the requested term.

Defect 1's cause: `DtSolver::model` (`shinri-dt/src/lib.rs:826`) is handed a
**fresh, empty** `ModelBuilder` (`shinri-theory/src/combiner.rs:970`), so its
`m.get(t)` can never observe another theory's assignment; and
`render_value_inner` (`:658`) does not receive the builder at all — it infers
from term *shape* and falls back to `"?"` (`:696`) for anything that is not a
nullary uninterpreted application.

Defect 2's cause: `format_model` (`shinri-solver/src/lib.rs:338`) iterates the
whole theory value map (`:347`) and names each entry with `display_term`
(`shinri-solver/src/tseitin.rs:415`), which renders any compound term as
`t{index}`. Defect 4 is the same cause at the `GetValue` arm (`:291`).

Defect 3's cause is different, and worth separating from its fix: a symbol in no
assertion is in no registered atom, so **no theory ever assigns it a value** and
there is nothing for `format_model` to iterate. Enumerating declared symbols
instead of assigned terms is the fix, and it needs a registry the `Solver` does
not currently keep — `Command::DeclareFun` is discarded
(`shinri-solver/src/lib.rs:316`) — but the registry alone is not sufficient; a
value has to be manufactured. §4.B covers both halves.

The enabling fact for the fix: `Arith::build_model`
(`shinri-arith/src/lib.rs:560`) assigns **every** var it has a term for
(`:566`–`:569`), free vars included at their current β. So the Int field values
already exist in `arith_m` — including for selector applications minted
in-search. Nothing needs to be computed; it needs to be *reachable*.

And there is an exact precedent in the same function: the string solver already
builds **last, directly into `combined`** (`combiner.rs:983`–`:994`) with the
comment *"so it can read the arith-assigned `(str.len ·)` values … A separate
empty builder would hide those."* This slice applies that same resolution to
`DtSolver`.

## 2. Invariant

**This slice cannot change a verdict.** It touches no lemma, no guard, no
propagation, no conflict, and no `check` path; every edit is downstream of
`SolveResult::Sat`. `qfdt_e2e`, `script_e2e`, and the oracle suites must agree
with pre-slice results exactly — including on `unknown`. Any flip in any
direction is a regression, with no adjudicated-flip escape hatch (contrast
slice 42 §4.A, which permitted `unknown` → decided). This is what makes the
slice low-risk relative to 39–42, and it is the first thing to check if
something goes wrong.

## 3. Combiner-side: field value resolution

### 3.A `DtSolver::model` runs last, into `combined`

Move the `self.dt.model` block (`combiner.rs:970`–`:978`) and drop the
`combined.absorb(dt_m)` line (`:982`); run DT into `combined` **after** the
string build (`:994`). The resulting total order is:

```
arith_m ─┐
euf_m   ─┼─► combined ──► string.model(&mut combined) ──► dt.model(&mut combined)
arrays_m ┘
```

Two properties justify this order. Inside the Combiner **every TermId is
valid**, so selector applications minted by `instantiate_constructor` resolve —
this is what sidesteps the ctx-clone isolation hazard rather than fighting it
(the solver-level filter at `shinri-solver/src/lib.rs:888` drops exactly those
terms, which is why C1's field value is unreachable from the solver side).
And **nothing reads DT's values**, so DT is free to go last.

> **Corrected against the shipped branch.** This section originally claimed
> that going after string "additionally makes `String`-sorted fields resolve".
> **Measured false.** The ordering is still right, but it does not buy that:
> a field application like `(s w)` is minted *in-search* by DT, so it never
> enters `StrSolver::str_terms` and the string model never assigns it
> (`shinri-str/src/model.rs:116-126`) no matter when string runs. EUF, which
> treats `String` as uninterpreted, leaves a `ModelVal::Elem` — an opaque class
> token, not a String value — and `render_field`'s sort guard (§3.C) refuses it
> rather than print a sort-mismatched `@elem0`. String-sorted fields therefore
> render `?`; see the new row in §5 and the pin
> `string_field_stays_a_placeholder_rather_than_an_elem_token`.

That second property is a change in what the string solver sees, not just a
reordering: today `string.model` reads a `combined` that already contains
`dt_m`, and afterwards it will not. It is safe because `DtSolver::model` assigns
only datatype-sorted terms (`shinri-dt/src/lib.rs:835`) and no string term is
datatype-sorted — but the plan must **verify** that `StrSolver::model` never
reads a datatype-sorted term's value rather than taking this paragraph's word
for it. If it does, the fix is to keep DT before string and give DT a
`combined`-reading pass instead.

### 3.B EUF stops assigning `Elem` to datatype-sorted terms

`Euf::model` (`shinri-euf/src/solver.rs:185`) assigns
`ModelVal::Elem(sort, id)` (`:218`) to every registered term that is not
Real/Int-sorted — and datatype-sorted terms are registered. It already skips
Real/Int (`:210`–`:215`) with the stated reason that Arith owns those values.
Extend that skip to datatype sorts, for the identical reason: **DT owns them.**

This is **required**, not cosmetic. `DtSolver::model`'s guard
`if m.get(t).is_some() { continue }` (`shinri-dt/src/lib.rs:828`) exists to
avoid clobbering another theory's assignment. Against the now-shared builder it
would see EUF's `Elem(List, 0)` for `l` and **skip every datatype term**,
regressing the model rather than fixing it.

It also removes a real latent fragility. `ModelBuilder::absorb`
(`shinri-theory/src/model.rs:46`–`:50`) is last-write-wins via `insert`, and
today's output is correct *only because* `dt_m` is absorbed after `euf_m`
(`combiner.rs:980` before `:982`). Nothing documents or tests that dependency.
After 3.B the two theories no longer both claim datatype-sorted terms, so the
result no longer depends on absorb order at all.

The Bool branch (`:199`–`:208`) is untouched: it precedes the sort dispatch, so
a datatype-sorted term merged with the truth node — which cannot happen for a
well-sorted problem — is unaffected either way.

### 3.C `render_value_inner` consults the builder

Thread `&ModelBuilder` through `render_value` (`:638`) into
`render_value_inner` (`:658`). Per constructor argument, in order:

1. **Datatype sort** → recurse (unchanged).
2. **Numeral term** → print the literal via `Context::numeral_value`. This case
   alone fixes C2 and M3, where the field is a numeral and no lookup is needed.
3. **Assigned in the builder** → format the `ModelVal`.
4. **Nullary uninterpreted application** → its own symbol name.
5. **Otherwise** → `"?"`, now meaning only "no theory assigned this term".

**The order of 3 before 4 is load-bearing, not stylistic.** The nullary-app
branch is what slice 39 already does, and it prints a *term name*, not a value.
If it ran first, a field that is a declared Int constant `x` with arith value `7`
would render `(cons x nil)` — and worse, two distinct constants in one
equivalence class would render as two different "values", which is a wrong model,
not merely an ugly one. A model maps symbols to values; the symbol's own name is
only admissible when nothing assigned it one. So branch 4 survives strictly as a
fallback below the builder lookup — better than `?` for an enum-like
uninterpreted constant, never a substitute for an assigned value.

Case 3 needs `format_modelval` callable from `shinri-dt`. **Move it — with
`format_rational`, `format_hex_fixed`, `format_bin_fixed` — from
`shinri-solver/src/model.rs:85` into `shinri-theory`, beside the `ModelVal`
type it formats.** Rendering a value belongs with the value type; the BV
extraction in that file stays where it is. `shinri-solver` then calls the
relocated function, so its behaviour is unchanged for every existing caller.

Because `Arith::build_model` assigns every var it knows, Int/Real fields resolve
**unconditionally** after 3.A — including the entirely unconstrained field in
C1, which arith holds at β = 0.

## 4. Solver-side: the output surface

### 4.A Declared-symbol registry

`Solver` gains an ordered registry of user-declared arity-0 symbols with their
sorts, populated where `Command::DeclareFun` is currently discarded
(`shinri-solver/src/lib.rs:316`). Constructor, selector, and tester symbols
introduced by `declare-datatype(s)` are **not** registered — they arrive via
`Command::DeclareDatatypes`, a different arm — so `nil` cannot appear as a model
entry by construction rather than by filtering names after the fact. Internal
mints (`ite!`, `!`-prefixed bridge symbols) are likewise never registered.

Arity > 0 symbols are recorded but not emitted; see §5.

### 4.B `format_model`

Iterate the registry, not the theory value map, emitting

```
(define-fun <name> () <sort> <value>)
```

concatenated on **one line**. Single-line output is a hard constraint, not a
style choice: `qfbv_witnesses.rs:279` asserts `out.len() >= 2` and reads
`out[1]` as the entire model, so a multi-line model would break the
line-oriented response contract.

The `<sort>` position needs a **sort printer, which does not exist yet** — there
is no `display_sort`/`sort_name` anywhere in `shinri-core` or `shinri-solver`.
It is a new component, small but not free, and it must cover every sort the
supported logics can declare: `Int`, `Real`, `Bool`, `String`, an uninterpreted
sort's own name, a datatype's own name, `(_ BitVec n)`,
`(_ FloatingPoint eb sb)`, `RoundingMode`, and `(Array <s> <s>)` recursively. It
belongs in `shinri-core` beside the sort table it reads. Any sort it cannot
print is a bug, not a fallback case — an unprintable sort would emit malformed
SMT-LIB, so it should be exhaustive over the sort representation rather than
ending in a catch-all arm.

Two properties follow for free. `tN` and `nil` can no longer appear. And output
becomes **deterministic** — declaration order instead of `FxHashMap` iteration
order, which is why the §1 probes print their entries jumbled and why any
exact-string test would have been flaky before this change.

A registered symbol that no theory assigned gets a **sort default**: `0` for
Int/Real, `false` for Bool, all-zeros for a BV sort, `""` for String, and
`@elem0` for an uninterpreted sort — matching what `format_modelval` already
emits for `Elem` (`model.rs:95`), so the defaulted and the theory-assigned cases
render in one vocabulary rather than two. Note that an uninterpreted-sorted
*field* of an asserted term already resolves through §3.C via EUF's `Elem`
assignment; only its rendering is non-conformant, and that is §5's row, not this
one.

A datatype-sorted symbol needs a default too, and the reason is worth being
precise about, because the obvious argument is wrong. `check`'s completeness
fence (`shinri-dt/src/lib.rs:610`) does guarantee every **watched** datatype
class is constructor-determined on `Sat`, so §3.C renders anything DT has seen —
that is exactly M4b. But a symbol occurring in no assertion is in no registered
atom, so it is not in `dt_terms` and DT never sees it; M4 and M4c are that case,
and it is not datatype-specific. The default is therefore built structurally
from the sort: **the first nullary constructor if the datatype has one,
otherwise the first constructor with each field filled by its own sort
default, recursively.** Well-founded datatypes — which SMT-LIB requires —
guarantee this terminates; reuse `render_value`'s existing depth backstop
(`:645`) as the fail-safe rather than adding a second one. This closes M4, M4b,
and M4c together.

### 4.C Term printer and `get-value`

Extend `display_term` (`shinri-solver/src/tseitin.rs:408`) to print full
applications recursively — `(head l)` — keeping the `t{index}` fallback
(`:415`) only for terms with no printable form. The `GetValue` arm (`:291`) then
labels each response with the requested term, yielding
`(((head l) 7) (l (cons 7 nil)))`. (Originally written `(cons 1 nil)` here and
in §7 criterion 2 — internally inconsistent with the same expression's
`(head l) = 7`. The binary produces `(cons 7 nil)`, measured.)

## 5. Explicit gaps

Stated here so the spec is not read as promising more than it delivers.

| Gap | Cause | Disposition |
|---|---|---|
| Bool-sorted fields | `Euf::model`'s Bool branch (`solver.rs:199`–`:208`) assigns `ModelVal::Bool` for terms merged with the truth node, so these **may** resolve opportunistically via §3.C — unverified | **Measure in task 1** and pin the observed behaviour either way. Do not assume either outcome. |
| BV-sorted fields | BV values are extracted solver-side from SAT vars and never enter the Combiner's builder. Worse than predicted: with only a *selector* application asserted, the symbol never enters `DtSolver::watched_dt_terms()` either, so DT contributes nothing for it at all — not even a partial `(mk ?)` | `?` — but for the WHOLE symbol, `((define-fun v () W ?))`, not `(mk ?)`: with no channel value there is no evidence of the constructor either. **Release only.** In a dev/debug build the same query panics before `check-sat` returns, on the pre-existing `debug_assert!(child_ids.is_empty(), "non-nullary uninterpreted BV fn out of scope")` in `shinri-bv/src/blast/mod.rs:282` — verified to reproduce on pre-slice `main`, so it is not this slice's doing and is deferred with it. Both halves pinned (`fenced_bv_field_panics_in_debug`, `fenced_bv_field_is_a_placeholder_in_release`). Successor slice. |
| String-sorted fields | `(s w)` is minted in-search by DT, so it never reaches `StrSolver::str_terms` and the string model never assigns it (`shinri-str/src/model.rs:116-126`). EUF leaves a `ModelVal::Elem` class token behind, which is not a String value | `?`. `render_field`'s sort guard deliberately refuses the `Elem`: routing a String field through the shared builder unguarded would print `@elem0` in a String position — a sort-mismatched *wrong* value, strictly worse than a visible placeholder. Corrects §3.A's original claim; pinned by `string_field_stays_a_placeholder_rather_than_an_elem_token`. Successor slice. |
| `get-value` on a builtin-op term | Only `Op::Uninterpreted` gets a structural rendering in `display_term` (`tseitin.rs:441-445`, which says so); and `format_value` has no entry for a compound arithmetic term | Both halves degrade: measured, `(get-value ((+ x 1) b))` → `((t7 ?) (b true))` — the label falls back to the internal `t{index}` and the value to `?`. §4.C's printer work covers applications of *declared* symbols only. Out of scope here, but it is a `tN` name reaching the user, which §7 criterion 1 forbids for `get-model`; a successor slice should close it. |
| Uninterpreted-sort values | `format_modelval` renders `Elem` as `@elem{idx}` (`model.rs:95`), not z3's `(as @U!val!0 U)` | Pre-existing, out of scope, unchanged by the relocation in §3.C. |
| Arity > 0 functions | Need EUF congruence-class enumeration plus a default point to build a function graph | Out of scope. **`get-model` therefore remains an incomplete model for UF queries** — it omits function symbols. Successor slice. |

**The general rule behind most of these rows**, not just their DT instances:
`get-model` enumerates *declarations*, so it must produce an entry for a symbol
whose value no channel supplies. It emits a sort default **only** when the
symbol was never interned — occurs in no assertion, so its constraint set is
empty and any value of its sort is a model value. When the symbol *is* interned
but unvalued, it emits `?`. Defaulting there would fabricate a value for a
symbol the query constrained: the QF_ABV stage populates only
`abv_array_models`, so before this rule `(assert (= i #x3))` still printed
`(define-fun i () (_ BitVec 4) #b0000)` (pinned by
`abv_unvalued_symbol_is_a_placeholder_not_a_fabricated_default`). Pre-slice the
value-map iteration made such symbols simply *absent*; moving the enumeration
axis to declarations is what would otherwise have turned silent incompleteness
into confident falsehood. **The output is incomplete in the rows above, never
false.**

The successor slices — unifying the Bool/BV/String value channels into the
Combiner's builder, function graphs for arity > 0, and structural `get-value`
labels for builtin ops — are independent of each other and of this slice.

## 6. Testing

### The gate goes first

Slice 42 implemented its plan exactly, passed every per-task review, and pruned
nothing, because the plan's premise was wrong; only the end-to-end measured gate
caught it, and it had been scheduled second-to-last. **The exact-model-string
e2e gate is task 1 here**, landing as soon as the plumbing exists. Probes C1–C4,
M3, M4, M5 become exact-output assertions. A wrong premise then shows up
immediately as a `?` that did not disappear, rather than after four tasks of
green reviews. Exact-string assertions are only viable because of §4.B's
determinism.

### Unit — `shinri-dt`

- `render_value` against a builder holding a field value renders the value, not
  `?`; against a builder without one, still `?`.
- **Branch order 3-before-4 (§3.C):** a field that is a declared constant *with*
  an assigned value renders the value, not the constant's name. Two distinct
  constants merged into one class render the *same* value. This is the
  wrong-model fence, not a formatting preference.
- A numeral field renders from the literal with an **empty** builder (case 2 of
  §3.C is independent of any theory).
- Nested and DAG-shared datatype fields still render (the `visited`
  add/remove discipline at `:650`/`:654` is unchanged and must stay unchanged).

### Unit — `shinri-euf`

- `model` assigns no `ModelVal` to a datatype-sorted registered term, and still
  assigns `Elem` to an uninterpreted-sorted one. This is the §3.B fence.

### Unit — `shinri-core`

- The sort printer (§4.B) round-trips every sort shape the supported logics can
  declare, including a nested `(Array (_ BitVec 8) <datatype>)`. This is the one
  new component in the slice with no existing behaviour to regress against, so
  its own test is the only thing standing behind it.

### Unit — `shinri-theory`

- `build_model` runs `dt` last: a datatype term's rendered value survives, and a
  field's arith value is visible to the DT render. Assert on the *combined*
  builder, since the ordering is the whole point.

### End-to-end — `shinri-solver`

- The §1 probe table, as exact expected strings. M4/M4b/M4c are a trio: they pin
  the no-assertion default, the DT-rendered control, and the non-DT case
  respectively, so a fix that only handles the datatype path is caught by M4c.
- `get-value` labels responses with the requested term (§4.C).
- Model entries name only declared symbols: keep the existing
  `!model.contains("ite!")` pin (`ite_e2e.rs:213`) and add a positive pin that
  every entry's name is a declared symbol.
- A declared-but-unasserted symbol of each defaulted sort — Int, Bool, BV,
  String, and a datatype with no nullary constructor — appears with its default
  (§4.B). The last of these is the structural-recursion case.
- The DT⋈arith regression set (`qfdt_e2e.rs:146`–`:231`) stays green with
  verdicts unchanged — the §2 invariant.
- `fp_e2e` / `qfbv_witnesses` model assertions are `contains`-style on value
  text (`(fp #b…`, `#x2a`), which survives being wrapped in a `define-fun`;
  confirm rather than assume, and confirm `qfbv_witnesses.rs:280`'s
  `out.len() >= 2` still holds under single-line output.

### Oracle

The **full unfiltered** run: `cargo nextest run -p shinri-solver --features
oracle`, no `-E` filter, with a **confirmed non-zero discovered test count** (a
flagless run compiles to zero tests and reads as green). Non-negotiable: §3.A
and §3.B change the shared model path used by every logic, and a filtered run on
slice 40 skipped `qfs_differential` and nearly shipped a string
`Sat` → `Unknown` regression.

### `script_e2e`

Run locally pre-push. `script_e2e` has **zero** `get-model` pins, and no verdict
can change (§2), so the expected outcome is **no flips of any kind**. A flip in
any direction is a regression — stop and diagnose, do not adjudicate.

### Standing gates

`cargo fmt --all` before pushing (CI gates on `fmt --check` and fails fast);
`mise run lint` clean (clippy `-D warnings`). Blocking-tier wall-clock
unchanged — this slice adds no search work.

## 7. Success criteria

1. Every probe in the §1 table produces conformant single-line `define-fun`
   output with **no `?` for Int/Real/datatype fields**, no `tN` name, no
   entry for an undeclared symbol, and no declared symbol missing.
   **`String`-sorted fields are excluded**: they render `?` and are a §5 row,
   not a criterion — see the correction to §3.A for why the ordering argument
   that put String on this list does not hold. (The exclusion is narrow: a
   String-sorted *declared symbol* still resolves normally; it is specifically
   the in-search-minted *field* that has no channel.)
2. `get-value ((head l) l)` returns `(((head l) 7) (l (cons 7 nil)))` — requested
   terms as labels.
3. Model output is deterministic across runs, in declaration order.
4. The §2 invariant holds: `qfdt_e2e`, `script_e2e`, and the full unfiltered
   oracle run agree with pre-slice results on every verdict, `unknown` included.
5. §3.B is pinned by a `shinri-euf` unit test, so the correctness of the model no
   longer depends on `absorb` order.
6. The Bool-field question in §5 is **measured**, and whichever way it lands is
   pinned by a test rather than left to inference.
7. The gaps that remain — BV fields, String fields, arity > 0 functions, and
   `get-value` labels for builtin-op terms — are documented in §5 and (except
   the last, which needs no new code path to find) pinned by tests asserting
   the current fenced behaviour, so a later slice can find them.
