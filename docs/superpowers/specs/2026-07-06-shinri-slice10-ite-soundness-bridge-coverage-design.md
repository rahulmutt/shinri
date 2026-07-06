# Slice 10 design — non-word ite soundness + Array/Str bridge coverage

Date: 2026-07-06
Status: IMPLEMENTED (slice 10 landed). word_norm eliminates ite over every
sort except Bool/String (wrong-SAT closed on LRA/LIA/UF/ABV paths, z3
differential-validated 3×200 @ 0 unknown); arith/EUF ite! model channel
filtered; Array/Str×bridge fences pinned + unknown-tolerant oracles added.
Predecessor: slice 9 (`6555879..055d61f`, PR #2, landed 2026-07-05)

## Goal

Two phases, one slice:

1. **Phase 1 (soundness fix):** close a pre-existing **wrong-SAT** hole — ite
   over Int, Real, uninterpreted, and Array sorts is misrouted to EUF as an
   opaque application, so the condition and branches are never linked. Fix by
   broadening the slice-5 `word_norm` ite-elimination gate to those sorts.
2. **Phase 2 (coverage + spec truth-up):** discharge the slice-9 open
   follow-up — dedicated z3 differential coverage for Array-Real and
   String-Real operands mixed with the `fp.to_real` bridge — and correct the
   slice-9 spec's follow-up note to observed reality.

Non-goals: no fence lift for Array-Real / Str-Real bridge operands (they stay
sound `Unknown`; this slice pins that), no String-sorted-ite change (correct
today), no new FP op admission, no mechanism-B/`to_fp` work.

## 1. Pre-flight findings (probed end-to-end vs z3, 2026-07-06)

The slice-9 Status follow-up said the Real-sorted recognizer "also admits
Array/Str-Real bridge operands (structurally the same shared-Real case as the
validated EUF path)" and they merely lack coverage. Probing corrected this:

- **Str-Real EUF operands never reach the recognizer.** `string_stage::fenced`
  (fence condition 1: non-nullary uninterpreted application with a
  String-sorted argument or result) rejects `(g s)` with `g : String → Real`
  upstream → sound `Unknown` at the string-stage fence, before FP dispatch.
- **Array-Real operands are recognizer-admitted but not decided.**
  `bridge_admissible` returns `true` for `(= (select arr i) (fp.to_real x))`
  over `(Array Int Real)` (verified by unit probe), yet every probed shape —
  select, store/select, SAT- and UNSAT-expected, with and without the bridge —
  returns `Unknown`. Even **pure** `(Array Int Real)` queries with no FP at
  all are `Unknown`: Real-valued arrays are broadly undecided today. Sound,
  but the "structurally the same as the validated EUF path" claim does not
  hold end-to-end.
- **🚨 Wrong-SAT found — core, not bridge.** Hunting bridge intersections
  surfaced ite-shaped disagreements; reduction shows the bug predates slice 9
  and has nothing to do with FP or strings (every reproducer below fully
  parses — per-command `success` verified; see §1.1 for probe-harness
  corrections):
  - pure QF_LRA `(= (ite b 2.5 0.25) 1.0)` → shinri sat, z3 unsat
  - pure QF_LIA `(= (ite b 2 0) 1)` → shinri sat, z3 unsat
  - nested `(= (+ (ite b 2 0) 1) 2)` → shinri sat, z3 unsat
  - U-sort `(distinct u1 u2 u3) ∧ (= (ite b u1 u2) u3)` → shinri sat, z3 unsat
  - QF_ABV `(= (select (ite b a1 a2) i) …)` contradicting both branches →
    shinri sat, z3 unsat (the **validated ABV path** is affected too)
  - `(get-value (b))` on the LRA repro returns `(b @elem0)` — the Bool
    condition is valued as an uninterpreted-sort element, the smoking gun for
    the EUF-opaque misroute.
- **Correct today:** Bool-sorted ite (plain Boolean structure), word-sorted
  ite (BitVec/Float/RoundingMode — slice 5 `word_norm`), String-sorted ite
  (`(= (ite b "aa" "bb") "cc")` → unsat, agrees with z3), and — notably —
  arith ite **on the string path** (see §1.1).
- **No existing oracle fuzzes ite** over the affected sorts; no unit or e2e
  test pins the wrong verdicts (that absence is the bug's survival story).

Consequence for scope: the originally-planned oracle would mostly measure
sound Unknowns, while the one live unsoundness at its intersection is this
core ite bug — hence the two-phase slice.

## 1.1 Plan-time pre-flight corrections (probed 2026-07-06, before planning)

Re-probing with FULL per-command CLI output (the shinri CLI prints
`(error …)` for a failed command and **continues**, so `tail -1` probing
silently drops failed asserts from `check-sat`) corrected three §1/§3/§6
claims and resolved two plan-time decisions:

1. **All `str.prefixof`/`str.suffixof`/`str.contains` findings were probe
   artifacts.** Those three operators are **unimplemented** (parser:
   `unknown operator`); the assert errors out, is dropped, and `check-sat`
   runs on the remainder. There is no "string-predicate polarity" soundness
   hole, and no str-conditioned ite shape using them can even parse. Every §1
   core reproducer re-verified clean (all commands `success`; wrong-SATs are
   real).
2. **The string path already handles arith ite correctly — mechanically.**
   `shinri-str/src/reduce.rs` (`reduce_assertions`, ~line 353) eliminates
   every non-Boolean ite on the string path into a fresh variable + Bool-ite
   defining assertion (built for its own substr guards). Probes:
   `(= (ite (= s "a") 2.5 0.25) 1.0)` → unsat (correct). The §1 wrong-SAT is
   therefore **path-dependent**: every non-string dispatch path. word_norm
   broadening makes elimination uniform and upstream; the string path's own
   reduce-introduced ites are minted after word_norm runs and remain
   self-eliminated (unaffected).
3. **The §3 string∩bridge canary shape is pinned to `Unknown`, decided now.**
   `(= (ite (= s "a") 2.5 0.25) (fp.to_real x))` → `Unknown` today (the
   str-eq atom fails `is_lra_real_atom`, so `bridge_admissible` rejects →
   sound fence), and stays `Unknown` post-fix for the same reason. Probed.
4. **§2 ABV fallback resolved: NOT needed.** The hand-desugared
   post-elimination forms are decided correctly on every affected path — LRA
   `unsat`, U-sort `unsat`, **ABV `unsat`** (`(ite b (= w a1) (= w a2))` +
   selects on `w`), all agreeing with z3. The elimination gate covers Array
   sorts with no fence.
5. **Phase-2 str oracle family must use supported ops only**: string
   equality/disequality, concat, `str.len` arithmetic — not
   prefixof/suffixof/contains (unimplemented, would panic the parse-strict
   test harness).

## 2. Phase 1 — broaden the `word_norm` ite-elimination gate

### Mechanism (approach A, user-selected)

`word_norm.rs` already eliminates word-sorted ites: fresh reserved nullary
symbol `ite!<n>` + one appended defining assertion `(ite c (= w x) (= w y))`
(Bool-sorted ite — plain Boolean structure downstream), with structural dedup
(`ite_var`), get-value maps (`ite_map`/`orig_ite_map`), model filtering
(`internal`), and user-name reservation all built and slice-5/7-validated.

Change: the gate `is_word_sort` (word_norm.rs:65) currently accepts only
`BitVec | Float | RoundingMode`. Broaden the elimination trigger to a
predicate `sort_eliminates_ite`: **every sort except Bool and String** —
i.e. word sorts (unchanged) plus Int, Real, uninterpreted sorts, and Array
sorts. The defining assertion is sort-generic; the introduced equality routes
to Arith (Int/Real), EUF (U-sorts), the ABV controller (Array-over-BV — it
already handles array-eq atoms per the QF_ABV dispatch contract), or stays
inside existing fences (non-BV arrays → sound Unknown, exactly as today).

Exclusions, and why:

- **Bool**: ite over Bool is Boolean structure; Tseitin handles it (probed
  correct). Eliminating it would be pure churn.
- **String**: correct today via the string path. Left untouched and pinned by
  canary; unifying it through word_norm is possible later but is behavior
  change on a working, semi-decidable path — out of scope.

### Model channel (known follow-through, not a risk discovered late)

Word-sorted eliminated ites surface their values through the blast-model
`var_bits` loops. Int/Real/U-sort `w` values live in the EUF/arith model
(`mb`) instead. The `internal` filter set currently only guards the
`var_bits` loops; the `mb`-based loops rely on word `ite!` symbols never
reaching EUF registration. Broadening breaks that invariant **by design** —
arith/EUF `ite!` symbols WILL appear in `mb`. Required follow-through:

- `get-value` on an eliminated arith/U-sort ite must answer via
  `ite_map`/`orig_ite_map` → `mb` (dedicated e2e test).
- `get-model` must NOT leak `ite!` symbols: the `mb`-based model-surfacing
  loops gain the `internal` filter the `var_bits` loops already have.

### ABV fallback — RESOLVED (plan-time probe, §1.1 item 4)

The ABV controller decides the eliminated form correctly
(`(ite b (= w a1) (= w a2))` + selects on fresh `w` → `unsat`, agreeing with
z3). No fence needed; the elimination gate covers Array sorts.

## 3. Phase 2 — Array/Str+bridge coverage & slice-9 spec truth-up

- **Canary pins (flip-markers for a future fence-lift slice):**
  - Array-Real operand + bridge (`(= (select arr i) (fp.to_real x))`) →
    `Unknown` today; pin it.
  - Str-Real EUF operand + bridge (`(= (g s) (fp.to_real x))`,
    `g : String → Real`) → `Unknown` (string-stage fence); pin it.
  - Pure `(Array Int Real)` select/store (no FP) → `Unknown`; pin it.
  - Str-eq-conditioned Real ite + bridge
    (`(= (ite (= s "a") 2.5 0.25) (fp.to_real x))`) → `Unknown` (probed;
    §1.1 item 3 — bridge recognizer rejects the str-eq atom, today and
    post-fix); pin it.
- **Differential oracle families** (fp_oracle.rs, `oracle` feature, following
  `differential_qf_fp_to_real_uflra`'s structure):
  - `differential_qf_fp_to_real_array`: fuzzed select/store over
    `(Array Int Real)` linked to a constant-source `(fp.to_real x)` and a
    random bound, z3-pinned.
  - `differential_qf_fp_to_real_str`: fuzzed `g : String → Real` applications
    + simple str atoms (equality/disequality over literals, concat,
    `str.len` — supported ops only, §1.1 item 5) linked likewise.
  - Contract for BOTH: **zero SAT/UNSAT disagreements; Unknowns tolerated**
    (report counts). Unlike the UFLRA oracle there is NO 0-unknown assertion
    and NO sat>0/unsat>0 coverage assertion — today these families are
    expected to be all-Unknown (the canaries above carry the exact pin). The
    oracle's job is to guard the seam now and remain in place, unchanged, when
    a later slice lifts the fences.
- **Spec truth-up:** rewrite the slice-9 Status follow-up note to the §1
  reality (recognizer admits Array-Real but downstream soundly bails;
  Str-Real is fenced upstream by the string stage; coverage added in slice
  10), and record the ite wrong-SAT as found-and-fixed here.

## 4. Testing

- **E2e regression tests** (fp_e2e.rs / qflra_e2e.rs / lia_e2e.rs /
  qfuf_e2e.rs / qfax_e2e.rs homes as appropriate): the six pre-flight
  wrong-SAT reproducers from §1, each now pinned to the correct verdict
  (`unsat`), plus the §3 canary pins.
- **Unit tests** in `word_norm`: elimination fires for Int/Real/U-sort/Array
  ites; original-TermId preservation on untouched terms; String/Bool ites pass
  through; dedup across shared subterms for the new sorts.
- **Model-channel tests**: `get-value` on an eliminated arith ite returns the
  branch value; `get-model` output contains no `ite!` symbol.
- **Differential oracles** (z3-pinned, `oracle` feature):
  `differential_qf_lra_ite`, `differential_qf_lia_ite`,
  `differential_qf_uf_ite` — fuzzed ite nests over the fixed sorts,
  **0 disagreements AND 0 Unknown** (these fragments are decidable); plus the
  two §3 bridge families (0 disagreements, Unknowns tolerated).
- **Net:** full `cargo test --workspace` (cold-cache clippy per the CI
  lesson), preceded by a front-loaded canary hunt (§5).

## 5. Cross-slice canary risk

Prior slices teach that changing a verdict class breaks canaries pinned to the
old verdict (e2e AND unit). Here the old verdict is wrong-SAT with **no known
pins** (§1: no existing coverage), so breakage risk is lower than a fence
lift — but the hunt is still front-loaded in the plan: grep the test corpus
for `Ite`/`ite` shapes over Int/Real/U-sorts/Arrays and for tests consuming
`get-model` output that would see new-vs-absent `ite!` entries, before any
code change. Word-sorted ite behavior must be byte-identical (its gate arm is
unchanged); the slice-5/6/7 ite tests are the guard.

## 6. Risks

- **`mb` model-leak invariant flip (§2 model channel)** — the one deliberate
  invariant change; owned by the get-model/get-value tests.
- **ABV eliminated-form handling** — RESOLVED sound by probe (§1.1 item 4).
- **String-path interaction**: word_norm now eliminates user arith ites
  BEFORE the string path's own `reduce_assertions` elimination (which keeps
  handling its self-introduced substr-guard ites, minted post-word_norm).
  Probed sound (§1.1 item 2), and the combined shape gets its own e2e pins
  (SAT- and UNSAT-expected) rather than trust.
- **Fresh-symbol volume**: one symbol + one defining assertion per distinct
  ite — same cost profile slice 5 already accepted for words; no new
  mechanism.
