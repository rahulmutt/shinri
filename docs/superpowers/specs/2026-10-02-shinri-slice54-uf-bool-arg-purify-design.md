# Slice 54 — Compound Bool arguments: purify into proxy symbols in `word_norm`

Status: design approved in chat 2026-10-02. Picks up the soundness item of
the slice-53 queue
(`docs/superpowers/research/2026-10-02-smtlib-2024-slice53-arith-eq-polarity-report.md`,
`## Queued for the next slice`, "Wrong `sat`: a theory atom used as an
argument of an uninterpreted function"). It is taken ahead of the queue's
first entry (the `Not(Eq)` arm / bare-E / string-order item, now slice 55)
because the baseline priority rule puts `Wrong` first.

**Area:** `shinri-solver` (`word_norm.rs`: a new item 3 in `WordNorm::walk`;
`fresh_var` takes a name prefix). Tests in `shinri-solver` (unit in
`word_norm.rs`, new `slice54_probes`, new oracle binary
`bool_arg_oracle`). No parser, `lower`, Tseitin, EUF, Combiner, fence or
theory-crate change. Housekeeping: the Rust toolchain bump to 1.99.0
(`mise.toml`) rides as the branch's first commit.

## 1. Summary

### 1.1 The defect

EUF ties a Bool-sorted term to its truth value only when that term is itself
an EUF-routed SAT atom: `Euf::assert` merges a predicate atom with the ⊤/⊥
sentinel (`crates/shinri-euf/src/solver.rs`, the `_` arm of `assert`). A bare
Bool constant `q` used as an argument works, because Tseitin encodes `q` as
an atom (`tseitin.rs`, the `TermNode::Const` / nullary arm) and EUF merges
it with ⊤/⊥. A **compound** Bool argument does not: `(and q r)` is a Tseitin
connective, `(= x 1)` is an Arith-owned atom (lowered to `(and E Le Ge)`).
Inside `P(·)` either one is an opaque e-graph node with no link to its truth
value, so `(P t)` and `(P true)` can take different values while `t` holds.

The slice-53 report described this as "a theory atom used as a UF argument".
It is broader: any compound Bool argument, including pure-Boolean ones in
QF_UF and datatype constructor arguments in QF_DT. Slice 10 fixed the same
class of defect for term-level `ite` (which reached EUF as an opaque
application); this slice applies the same remedy.

### 1.2 Reproducers (measured on `61be117`, z3 4.16.0)

| # | logic | assertions | shinri | z3 |
| --- | --- | --- | --- | --- |
| r1 | QF_UFLIA | `(P (= x 1))`, `(not (P true))`, `(= x 1)` | `sat` ✗ | `unsat` |
| r2 | QF_UFLIA | `(distinct (f (= x 1)) (f true))`, `(= x 1)`; `f : Bool → Int` | `sat` ✗ | `unsat` |
| r3 | QF_UFLIA | `(P (<= x 1))`, `(not (P true))`, `(= x 0)` | `sat` ✗ | `unsat` |
| r4 | QF_UF | `(P (= a b))`, `(not (P true))`, `(= a b)`; `a b : U` | `sat` ✗ | `unsat` |
| r5 | QF_UF | `(P (and q q))`, `(not (P true))`, `q` | `sat` ✗ | `unsat` |
| r6 | QF_UF | `(P q)`, `(not (P true))`, `q` | `unsat` ✓ | `unsat` |
| r7 | QF_UFLIA | `(P (= x 1))`, `(not (P false))`, `(not (= x 1))` | `sat` ✗ | `unsat` |
| s5 | QF_DT | `(= (mk (and q r)) (mk true))`, `(not q)`; `mk : Bool → B` | `sat` ✗ | `unsat` |

Shapes already linked or fenced (`61be117`):

| shape as argument | shinri | z3 | status |
| --- | --- | --- | --- |
| `(Q x)`, a Bool-result UF application (s1) | `unsat` | `unsat` | linked |
| `((_ is cons) l)`, a tester (s2) | `unsat` | — | linked |
| `(select a 0)`, `a : (Array Int Bool)` (s3) | `unknown` | `unsat` | fenced, sound |
| `(store a 0 (= x 1))` (s4) | `unknown` | `unsat` | fenced, sound |
| QF_UFBV `(P (= x #x1))` (s6) | `unknown` | `unsat` | fenced, sound |

### 1.3 The remedy, checked by hand

Purifying by hand — adding `b`, `(= b t)` and replacing `t` with `b` — gives
the right answer on HEAD on every affected path:

| # | logic | hand-purified script | shinri | z3 |
| --- | --- | --- | --- | --- |
| t1 | QF_DT | `(= (mk q) (mk true))`, `(not q)` | `unsat` | `unsat` |
| t2 | QF_DT | `(= (mk b) (mk true))`, `(= b (and q r))`, `(not q)` | `unsat` | `unsat` |
| t3 | QF_UF | `(P b)`, `(not (P true))`, `(= b (and q r))`, `q`, `r` | `unsat` | `unsat` |
| t4 | QF_UFLIA | `(P b)`, `(not (P true))`, `(= b (= x 1))`, `(= x 1)` | `unsat` | `unsat` |

The transform therefore only has to produce shapes the solver already
handles.

## 2. Scope

In scope:

- Purify every compound Bool-sorted argument of a non-connective parent
  (§3), on every solve path.
- Probes, unit tests and an oracle family that catch the defect at HEAD.
- Rust 1.99.0 (`mise.toml`): `cargo fmt --all --check` and
  `cargo clippy --workspace --all-targets -- -D warnings` are already clean
  under 1.99.0, so this is a one-line commit.

Out of scope:

- QF_UFBV / FP-path Bool arguments: `bv_stage::uf_args_supported` rejects
  every Bool argument, nullary included (test
  `uf_args_supported_rejects_a_bool_argument_to_a_bool_result_application`).
  They stay a sound `unknown`; blasting a proxy as a 1-bit word is queued.
- Bool-element arrays (s3, s4): stay fenced; queued.
- `get-value` echoing internal names (e.g. `((P t4) 5)` for
  `(get-value ((P (> x 0))))`) — pre-existing, already queued from slice 50.
- Any `wrong` row the base run surfaces that §3 does not resolve: list and
  queue it, do not chase it.

## 3. Design

Approach A from the brainstorm: purification in `word_norm`. Rejected
alternatives: (B) encode each compound argument to a literal in Tseitin and
register the argument term as a second-owner EUF atom — invasive, needs a
second owner for Arith-owned atoms, and misses UF applications in non-Bool
positions such as `(< (f (= x 1)) 3)`, which never reach Tseitin as atoms;
(C) fence the shape to `unknown` — sound but gives up decidable answers.

### 3.1 The rule

In `WordNorm::walk`, after the children are rewritten: if the parent is
**not a Boolean connective**, each Bool-sorted child that is **not** `true`,
`false` or a nullary symbol is replaced by its proxy (§3.2).

Boolean connectives are `and`, `or`, `not`, `=>`, `xor`, Bool-sorted `ite`,
and `=`/`distinct` whose operands are Bool. Every other parent with a
Bool-sorted child triggers the rule; today that is `Op::Uninterpreted`
applications (UF symbols, datatype constructors/selectors/testers) and
`select`/`store`. The rule is stated negatively so a future non-Boolean
operator is covered by default.

Bool-result applications (`(Q x)`, testers) are linked today (§1.2) but are
purified anyway: one iff per distinct term is cheap, and a rule that does not
depend on how each theory owns its atoms is easier to keep sound.

A term-level `ite`'s condition is a Boolean position (the eliminated `ite`'s
definition `(ite c (= w x) (= w y))` keeps it one), so it is not purified.

### 3.2 The proxy

For a child `t` (post-rewrite):

- a fresh Bool symbol `b`, named `bool!<n>`, minted by the existing
  `fresh_var`, which gains a name-prefix parameter (`ite!` for ites). It
  keeps the collision probing, `reserve_symbol` and `internal` membership;
- a definition `(= b t)` appended to `defs` (Tseitin encodes Bool `=` as
  iff), deduplicated through `seen_defs` like ite definitions.

A solver-lifetime map `bool_arg_var: TermId → TermId`, keyed by the
post-rewrite `t` (mirroring `ite_var`), makes the proxy shared:
`(f (= x 1))` and `(g (= x 1))` get one `b`, and repeated `check-sat` calls
reuse it. `defs` is per call, so a later `normalize` that meets `t` again
reuses `b` and re-emits the same hash-consed definition `TermId`, exactly as
ite definitions are re-emitted today.

Nesting is bottom-up because `walk` rewrites children first: in
`(P (Q (and q r)))`, `(and q r)` is purified to `b0`, then `(Q b0)` to `b1`.

### 3.3 Invariants

- A term with no rewritten subterm keeps its original `TermId` (module
  invariant). Formulas without the shape mint nothing.
- Only the argument occurrence is replaced. The same atom in a Boolean
  position elsewhere is untouched, and it is tied to `b` by the definition.
- `bool!` symbols are in `internal`, so every model-surfacing loop filters
  them (slice 10); they never appear in `get-model`.

### 3.4 Why it is sound

`b` is functionally determined by `t`, so the rewrite is equisatisfiable and
model-preserving for user symbols. `b` is a nullary Bool symbol, so it takes
the working `(P q)` path: Tseitin makes it an EUF atom, EUF merges it with
⊤/⊥. The definition puts `t` in a Boolean position, so slice 53's
`arith_eq_atoms` collects an arithmetic `t` and emits its axioms with no
change to `lib.rs`.

### 3.5 Interaction with paths and fences

| path | today | after | evidence |
| --- | --- | --- | --- |
| Combiner (QF_UF, QF_UFLIA, QF_UFLRA) | wrong `sat` | decided correctly | t3, t4 |
| Datatypes | wrong `sat` (s5) | decided correctly | t1, t2 |
| BV / FP / mixed | fenced `unknown` | still fenced (`uf_args_supported` rejects all Bool arguments) | `bv_stage.rs` test |
| ABV, Bool-element arrays | fenced `unknown` | expected still fenced; the bench confirms | s3, s4 |
| Strings | no string operator takes a Bool argument; UF over String is fenced | unaffected | — |

Allowed transitions: `wrong → correct`, `unknown → decided`, unchanged. Any
`decided → unknown` or `* → wrong` stops the slice for a ruling.

Risks, measured rather than assumed:

1. **Search-order noise.** The extra variables and iffs change SAT order on
   instances that contain the shape (slice 53 showed LIA/UFLIA and string
   heuristics are order-sensitive). Instances without it are byte-identical
   (§3.3).
2. **Fence trip-wires.** A new top-level Bool `=` and a new Bool symbol could
   change a routing predicate. The plan checks `has_non_bv_theory_atom`,
   `abv_stage::fenced` and the string-routing fence; the bench catches any
   row that moves.
3. **Model output.** Pinned by a probe (§6.2).

## 4. What this does not change

The parser, `lower`, Tseitin, EUF, the Combiner, every fence predicate, the
theory crates and the string model gate (it evaluates the user's original
assertions). `get-value` output is unchanged.

## 5. Tasks

1. **Toolchain.** Commit the `mise.toml` bump to Rust 1.99.0 on branch
   `slice54-uf-bool-arg-purify`.
2. **Base run.** `slice54-base` on `61be117` over QF_UF, QF_DT, QF_UFLIA,
   QF_UFLRA (§7).
3. **Failing tests first.** `slice54_probes.rs` (§6.2) and the
   `bool_arg_oracle` family (§6.3); confirm the probes fail and the oracle
   reports disagreements at HEAD, and record those counts.
4. **Fix.** §3, with the §6.1 unit tests first; audit the three fences named
   in §3.5 risk 2.
5. **Gates and re-run.** `mise run lint`, `mise run test`, the oracle suite;
   then `slice54`, the report, and §11.

## 6. Testing

### 6.1 Unit (`word_norm.rs` test module)

- `(P (= x 1))` becomes `(P b)` plus `(= b (= x 1))`; `b ∈ internal`.
- Unchanged inputs keep their `TermId`: `(P q)`, `(P true)`, and Bool
  children of connectives (`(and (= x 1) q)` mints nothing).
- One proxy per distinct `t`, within a call and across repeated `normalize`
  calls.
- Nesting is bottom-up: `(P (Q (and q r)))` yields two proxies, inner first.
- Interplay with ite elimination: in `(f (ite c (P (= x 1)) false))` the
  Bool-sorted `ite` is not eliminated (it is Boolean structure), `(= x 1)`
  is purified as `P`'s argument, and the whole `ite` is then purified as
  `f`'s argument — two proxies. In `(g (ite (= x 1) y z))` with Int `y z`,
  the condition is not purified (the ite is eliminated; its condition stays
  in a Boolean position).
- A user-declared `bool!0` is skipped (as
  `fresh_name_skips_user_declared_collision`).

### 6.2 End to end (`crates/shinri-solver/tests/slice54_probes.rs`, blocking tier)

Each `*_unsat` case has a `sat` sibling (one constraint relaxed) so the fix
cannot pass by over-refuting.

- r1, r2, r3, r4, r5, r7 (§1.2); r6 as a regression pin.
- QF_UFLRA versions of r1 and r3.
- s5, and a selector case on the DT path.
- Multi-argument `(F (= x 1) y (and p q))`, and a Bool-argument UF under
  arithmetic, `(< (f (= x 1)) 3)`.
- Fence pins: s3, s4, s6 stay `unknown` (records today's sound behaviour so
  a flip is visible and reviewed).
- Model hygiene: `get-model` after a `sat` sibling contains no `bool!`.

### 6.3 Oracle (feature `oracle`, `tests/bool_arg_oracle.rs`)

New family `differential_bool_arg`. A seeded LCG generator builds small
QF_UF / QF_UFLIA / QF_UFLRA scripts: 1–2 UF symbols with Bool parameters
(Bool or arithmetic result), applied to depth-≤2 Boolean formulas over Bool
variables and Int/Real `=`/`<=` atoms, plus `true`/`false` arguments; the
applications appear under both polarities and in arithmetic comparisons so
congruence matters. A QF_DT sub-family uses a Bool-field constructor.
Compared with z3.

- At HEAD (task 3): at least one disagreement; otherwise strengthen the
  generator until it does.
- After the fix: 0 disagreements; sat and unsat counts recorded, both
  non-zero.
- Runtime target < 30 s.

Run with
`cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)'`
and confirm a non-zero discovered count. The existing
`differential_qf_uflia_compound_args` and `qfdt_oracle` families must stay
at 0 disagreements.

## 7. Measurement

Two runs with `mise run bench-run` at default limits: `slice54-base` on
`61be117` and `slice54` at the slice head, over **QF_UF, QF_DT, QF_UFLIA,
QF_UFLRA**. In the local corpus only QF_UF declares functions with Bool
parameters (105 of 7,503 files); QF_DT can carry the shape through Bool
constructor fields; QF_UFLIA (0 of 659) and QF_UFLRA (0 of 1,284) are
controls that should move only by noise.

QF_LIA, QF_LRA, QF_S, QF_SLIA and QF_BVFP are not run: their logics admit no
UF symbols, datatypes or arrays, so the rule cannot fire, and §3.3 keeps
their encoding identical (pinned by §6.1). The report states this as a
reasoned omission, not as coverage.

### Success criteria

| # | criterion | kind |
| --- | --- | --- |
| 1 | r1–r5, r7, s5 `unsat`; every `sat` sibling stays `sat` | hard |
| 2 | §6.3: disagreements > 0 at HEAD, 0 after; discovered count > 0; existing oracle suite still 0 | hard |
| 3 | 0 rows `* → wrong` in the four benched logics | hard; any hit stops the slice for a ruling |
| 4 | every `correct → unknown/timeout` row triaged; net `correct` ≥ 0 per logic | hard; a net loss stops the slice for a ruling |
| 5 | fence pins hold (s3, s4, s6 `unknown`); no `bool!` in `get-model` | hard |
| 6 | `mise run lint`, `mise run test`, `ci` green | hard |
| 7 | count of QF_UF/QF_DT rows that mint ≥ 1 proxy; median/p90 ms per logic vs `slice54-base` | measured |

## 8. Named reproducers

§1.2 (r1–r7, s5) and §1.3 (t1–t4); the scripts are inlined in
`slice54_probes.rs`.

## 9. Queued for the next slice

- **First:** `get-value` remap for purified arguments (`lib.rs`; §11), with
  the slice-50 internal-name echo.
- Slice 55: the slice-53 queue's first entry — remove the `Not(Eq)` arm,
  together with the bare-E simplification and the string-engine
  search-order sensitivity, and the axiom memory-growth measurement.
- QF_UFBV / FP-path Bool arguments: blast a proxy as a 1-bit word instead of
  fencing.
- Bool-element arrays (s3, s4).
- `get-value` echoing internal names (carried), done together with the
  `get-value` remap for purified arguments (§11), which is the first item.
- Every other item carried in the slice-53 report's queue.

## 10. References

- Slice-53 report: `docs/superpowers/research/2026-10-02-smtlib-2024-slice53-arith-eq-polarity-report.md`
  (§ Queued for the next slice).
- Slice-10 precedent: term-level `ite` elimination in `word_norm`.
- Baseline priority: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Next slices).
- Code:
  - `crates/shinri-solver/src/word_norm.rs` (`walk`, `fresh_var`, `internal`)
  - `crates/shinri-solver/src/lib.rs:772` (the `normalize` call)
  - `crates/shinri-solver/src/tseitin.rs` (Bool `=` as iff; nullary atom arm)
  - `crates/shinri-euf/src/solver.rs` (`assert`, predicate arm)
  - `crates/shinri-solver/src/bv_stage.rs` (`uf_args_supported`)

## 11. Measured outcomes

Run `slice54` (fixture `6212fa5fcf84`, `solver_md5 579f17b3…`) against
`slice54-base` (binary built at `b59f115` with Rust 1.99.0 from sources
identical to `61be117` — the `crates` diff is empty — `solver_md5
84a83b41…`). The harness records the checkout HEAD, not the binary's commit:
the base legs' headers say `b59f115979ab` and `6212fa5fcf84`. Both runs
cover QF_UF, QF_DT, QF_UFLIA and QF_UFLRA: 18,146 rows, 0 missing, 0 extra,
20 s, 3072 MB, 6 jobs, `taskset -c 12-23`. Full report:
`docs/superpowers/research/2026-10-02-smtlib-2024-slice54-uf-bool-arg-report.md`.

| # | criterion | result |
| --- | --- | --- |
| 1 | r1–r5, r7, s5 `unsat`; every `sat` sibling stays `sat` | **PASS**: `slice54_probes` 5/23 at HEAD `bc6d152` (18 failures: 17 wrong `sat`s and the post-mint length check), 23/23 after |
| 2 | §6.3 disagreements > 0 at HEAD, 0 after; discovered > 0; existing oracle families 0 | **PASS**: `bool_arg_oracle` (3 tests) 29 / 20 / 12 disagreements (QF_DT / QF_UFLIA / QF_UFLRA) at HEAD, 0 / 0 / 0 after, sat and unsat both non-zero, 10.8 s; `differential_qf_uflia_compound_args` + `qfdt_oracle` 19/19; full oracle suite 749 run, 749 passed, 3 skipped (752 discovered = slice 53's 720 + 23 probes + 6 unit tests + 3 oracle tests) |
| 3 | 0 rows `* → wrong` | **PASS: 0**; no `ESCALATE`; neither run has a `wrong` row; 0 wrong answers in 934 re-runs (triage 216, minting rows 30, timing sample 688) |
| 4 | every `correct → unknown/timeout` row triaged; net `correct` ≥ 0 per logic | **PASS**: 4 rows (QF_UF QG-classification `correct → timeout`), all noise (3× per binary: same success count or after better, 20 s edge; none can mint a proxy); raw net QF_DT +1, QF_UF +171, QF_UFLIA +6, QF_UFLRA 0; credited net 0 in every logic |
| 5 | fence pins hold; no `bool!` in `get-model` | **PASS**: the three `fence_pin_*` probes stay `unknown`; `get_model_has_no_proxy_symbols` passes |
| 6 | `mise run lint`, `mise run test`, `ci` green | **PASS locally**: lint clean; test 1,652 passed / 7 skipped; deny and secrets rc 0. `ci` was run as its parts; the PR's CI run is the single-command confirmation |
| 7 | rows that mint ≥ 1 proxy; median/p90 per logic vs base | **MEASURED**: upper bound 105 QF_UF files (Goel 59, CLEARSY 46) and 0 QF_DT (no Bool constructor field in the corpus; QF_UFLIA/QF_UFLRA 0); after macro expansion only **5** files (CLEARSY) apply a Bool-parameter function to a compound argument, all `correct` in both runs. Paired interleaved sample: median per-row ratio after/base 0.92 (QF_DT, ~20 ms rows), 0.99 (QF_UF, QF_UFLIA), 1.00 (QF_UFLRA) |

**Credited gain: 0, raw +178.** `correct` went 15,152 → 15,330. None of the
189 changed rows can mint a proxy, so their encoding is unchanged (§3.3).
The interleaved re-runs of the sampled rows (20 of the 173 QG gains, all 4
losses) show both binaries behave the same on them; the unsampled rows follow
from the construction above: the QF_UF
QG-classification `timeout → correct` 173 (sampled 20) and the 4 losses are
rows at the 20 s edge, where the base run's QF_UF section ran slower (median
bench ratio after/base 0.69–1.06 by position, versus 0.99 interleaved). The
mathsat `Hash` 6, blocksworld 1, PEQ 1 and SEQ 1 gains, and the Certora
`oom`/`timeout` swaps, are noise the same way. The local corpus has no row
whose answer the fix changes; the evidence for the fix is criteria 1 and 2.

**Deviations from the spec text:**

- **§6.3:** the oracle is three tests in `tests/bool_arg_oracle.rs`
  (`QF_DT`, `QF_UFLIA`, `QF_UFLRA` families), not one
  `differential_bool_arg`. The generator was not strengthened: it found
  disagreements at HEAD as written.
- **§6.2 / Review Focus 3:** `string_path_bool_arg_is_not_sat` came out
  **`unsat`** (`unknown` was also acceptable); its `(= s "ab")` sibling is
  `sat`.
- **§4, `get-value`:** not unchanged. Every term that contains a compound
  Bool argument, of any sort, now prints `?`: `(get-value ((P (= x 1))))`
  after a `sat` prints `?` where HEAD printed `true`, and with
  `(= (f (= x 1)) 7)` asserted, `(get-value ((f (= x 1))))` prints
  `(((f t4) ?))` where the base binary printed `(((f t4) 7))`. The cause is
  that the assertion is rewritten to `(P bool!n)` and `lib.rs` has no remap
  for it (as it has for eliminated ites, `orig_ite_map` →
  `eliminated_ite_vals`). The fix needs `lib.rs`, outside this slice's file
  scope; it is queued as the first item of the next slice, together with the
  slice-50 internal-name echo (same evaluator path). No verdict changes.
- **§3.5, ABV / Bool-element arrays:** "the bench confirms" is wrong: no
  ABV logic was benched. It is replaced by the probe
  `fence_pin_qf_abv_bool_element_store_stays_unknown` in
  `slice54_probes.rs` (a `store` of a compound Bool value in QF_ABV, pinned
  by a `select`, answers `unknown` on both the base and the fixed binary).
  §3.5's original text is left as written.
- **§7, base run:** two legs with the same frozen binary and limits.
  `slice54-base` (16,735 rows) was killed by the tool's 2 h background
  limit; a resume was refused because the fixture header records the
  checkout sha, which had moved. The remaining 1,411 QF_UFLIA/QF_UFLRA files
  ran as `slice54-base-rest` (`--corpus target/slice54-base/rest-corpus`).
  The base matrix and transitions combine both legs. Leg 1's QF_DT section
  ran next to Tasks 2–3 on cores 0–11.
- **§7:** QF_DT has no Bool constructor field in the local corpus, so it is
  a control on the bench; the DT fix is covered by the probes and the QF_DT
  oracle family.
- Not a gate, queued: `cargo clippy --features oracle` fails on pre-existing
  oracle test files under Rust 1.99: 32 errors in 5 files
  (`qfs_differential.rs` 18, `fp_oracle.rs` 7, `qfbv_oracle.rs` 5,
  `nary_arith_oracle.rs` 1, `nary_oracle.rs` 1; mostly
  `inconsistent_digit_grouping`); `bool_arg_oracle.rs` is clean. Once they
  are cleaned, add the `--features oracle` clippy to `mise run lint`.
