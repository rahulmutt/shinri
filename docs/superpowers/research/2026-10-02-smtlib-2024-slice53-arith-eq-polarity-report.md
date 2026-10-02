# SMT-LIB 2024 re-run — slice 53 (arithmetic `=` under non-positive polarity; ramalho BVFP row) — shinri @ 07ac180fe984

**Measured outcome: all five corpus `wrong` rows are now `correct`, and no
row moved into `wrong`.** The run `slice53` (slice head `07ac180`) is compared
with `slice53-base` (the `2ceef06` sources) over QF_LIA, QF_LRA, QF_BVFP,
QF_UFLIA, QF_UFLRA, QF_S and QF_SLIA (137,586 instances).

```
# base (Task 1; ruling R1: launched directly and detached with setsid, frozen binary copies)
taskset -c 12-23 target/slice53-base/shinri-bench run \
  --logics QF_LIA,QF_LRA,QF_BVFP,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA \
  --timeout 20 --mem-mb 3072 --jobs 6 --solver target/slice53-base/shinri --run-id slice53-base

# after (Task 4)
cargo build --release -p shinri-cli -p shinri-bench
md5sum target/release/shinri   # 50af1137a8c94fe0eac78cea3947cda8 = fixture solver_md5
BENCH_LOGICS=QF_LIA,QF_LRA,QF_BVFP,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA BENCH_RUN_ID=slice53 \
  taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice53 mise run bench-report
```

Both runs used the default limits: 20 s, 3072 MB, 6 jobs, cgroup `cpu.max`
`800000 100000`, `memory.max` 34359738368, pinned with `taskset -c 12-23`.

| run | solver | `solver_md5` | started | finished | wall-clock |
| --- | --- | --- | --- | --- | --- |
| `slice53` (after) | `target/release/shinri` @ `07ac180` | `50af1137a8c94fe0eac78cea3947cda8` | 2026-10-01T18:54:12Z | 2026-10-02T00:48:10Z | ~5 h 54 min |
| `slice53-base` | `target/slice53-base/shinri` (built from `2ceef06` sources) | `d2daafb33df381b379a47c15afb167ed` | 2026-10-01T12:51:32Z | 18:52:14Z | ~6 h 01 min |

**Fixture sha.** The harness records the checkout HEAD, not the binary's
commit. `slice53` says `07ac180fe984`, and that is also the binary's commit.
`slice53-base` says `807ec5b42502` (the plan commit checked out when the run
started), but its binary was built from the `2ceef06` sources:
`git diff --stat 2ceef06 807ec5b -- crates` is empty (docs only). That binary
was frozen at `target/slice53-base/shinri`, md5 `d2daafb3…`.

**Baseline validity.** QF_LIA, QF_LRA and QF_BVFP have had no run since the
2026-09-09 baseline, so `slice53-base` is the comparison, not the baseline
(spec §7). It had exactly 5 `wrong` rows, the five in spec §1.1. No other
`wrong` row surfaced.

**Load disclosure.** `slice53-base` was **not** run on an idle machine. While
it ran on cores 12–23, Task 2's takeover verification, Task 3's suites (the
`shinri-fp` crate, `fp_oracle` ~29 min, `fp_add_tiny_exhaustive_all_modes`
~31 min) and the Step 1 gates (ruling R9: `mise run test` 407 s, the oracle
suite 2,012 s; finished 15:09Z) all ran on cores 0–11. The after-run ran with
no other cargo work. This shows in the bench-level timing: the QF_BVFP
median was 18 ms in the base run and 6 ms in the after run, but a controlled
interleaved re-run gives 6 ms for both (see *Timing*). It also makes most
`timeout → correct` rows timing noise, because the base binary solves them
within 20 s when re-run unloaded (see *Credited gain*). The triage re-runs
(below) ran with nothing else on the machine.

**How the transitions were computed.** A scratch script (not committed) loads
each `results.jsonl` keyed by `path`, asserts identical key sets
(**137,586 common paths, 0 missing, 0 extra**), and tallies
`(logic, before, after)` with per-family counts. It prints `ESCALATE` for any
row that moves into `wrong` and `LOSS` for any `correct → unknown*/timeout`
row. **It printed no `ESCALATE` and 105 `LOSS` lines.** The per-logic counts
below close under `new = old − outbound + inbound`.

## Headline

- **`wrong` 5 → 0.** calypto ×2 and keymaera ×2 (Task 2, the
  `E ⇔ (Le ∧ Ge)` axioms) and ramalho ×1 (Task 3, the `fp.add` signed-zero
  fix) are now `wrong → correct` (`unsat`). In the triage re-run (3× per
  binary, 20 s), all five give `sat` 3/3 with the base binary and `unsat` 3/3
  with the after binary.
- **0 rows `* → wrong`** in all 7 logics. There is no `ESCALATE`.
- **Raw `correct` +178** (63,271 → 63,449): QF_BVFP +40, QF_LIA +61,
  QF_LRA +2, QF_S 0, QF_SLIA +32, QF_UFLIA +43, QF_UFLRA 0.
- **Credited gain is +91, not +178.** Every changed row that can be
  re-checked was re-run 3× with each binary. Reynolds was sampled; see
  *Triage method*. The base-run load made 96 `timeout → correct` rows look
  like gains, 8 `correct → timeout` rows are the same noise the other way,
  and the z3-oracle `unverified` flips net −1 (+4 / −5). Without those (87
  rows net),
  each logic's credited net `correct` is ≥ 0: QF_BVFP +5, QF_LIA +4,
  QF_LRA +3, QF_S 0, QF_SLIA +37, QF_UFLIA +42, QF_UFLRA 0.
- **105 `correct → unknown/timeout` rows, all triaged.** 97 are
  solver-attributable and deterministic, and 8 are noise. The main loss
  mechanism is new and is evidenced on the rows themselves. The **base**
  binary reached these `unsat` answers on an *under-constrained* encoding,
  because an arithmetic `E` under Bool `=` / `not` / `ite` was a free EUF
  atom. Rewrite the file so the base binary encodes the same atom faithfully,
  and the base binary loses the row too (rings, Reynolds; below). Those
  `unsat` answers were sound, because an unsat relaxation implies unsat. They
  were cheap only because the encoding dropped constraints.
- **The cost is concentrated in QF_SLIA Reynolds `kaluza/unsat/big`.** 86
  rows went `correct → unknown:sat-budget`, while 101 rows in the same
  directory went the other way (`unknown:sat-budget → correct`). The family
  nets +15.
- `unknown:sat-budget` QF_S 1,384 → 1,385 (+1), QF_SLIA 4,401 → 4,247 (−154).
  `unknown:str-model-rejected` QF_S 968 → 967, QF_SLIA 3,009 → 3,123 (+114).
- Timing (criterion 6): the controlled paired sample is neutral (median
  ratio 1.0) in QF_BVFP, QF_LRA, QF_S, QF_SLIA and QF_UFLRA, about −1 % in
  QF_LIA, and −18 % in QF_UFLIA (faster).

## What changed versus the spec

1. **`lower` keeps `(and E Le Ge)` (ruling R6).** Spec §3.3 said the
   positive arm should return the bare `E`, with the axioms carrying `Le` and
   `Ge`. That lowering exposed a pre-existing order sensitivity in the string
   engine: `slice33_probes::probe_c_len_zero_var` (unsat → unknown) and
   `script_e2e::user_pfx_name_declared_before_any_mint_still_works`
   (sat → unknown) regressed, both to `fence=str-model-rejected`. The string
   engine's completeness on these inputs depends on the SAT decision order
   over its split atoms, and the bare-E change altered the Tseitin variable
   numbering. A temporary trace showed identical theory-assert sequences up to
   the first string split, and divergence after it. Soundness comes from the
   three axioms, not from the shape of the conjunction. The §3.3
   simplification is queued together with the order sensitivity.
2. **The oracle family is in `tests/arith_polarity_oracle.rs`**, not in
   `oracle.rs` (spec §5/§6.3). The test is `differential_qf_lia_lra_polarity`,
   feature `oracle`.
3. **`term_ite_condition` uses `1.0`/`0.0` in the Real case (ruling R7).**
   With Int-literal branches `(ite c 1 0)` under a QF_LRA header, shinri
   answers `unknown`, both before and after the fix. That is a pre-existing
   gap and is queued.
4. **Run procedure.** The base run was launched directly and detached with
   `setsid`, because the tool's 2 h background cap would have killed it
   (R1). The gates ran before the after-run, on cores 0–11, while the base
   run was live (R9; see *Load disclosure*).
5. **Unexpected probe passes at HEAD.** `nary_eq_under_implication`,
   `uflia_congruence_under_implication` and `slia_len_eq_under_demorgan`
   already passed at `2ceef06`. They are kept as regression pins.

## Success criteria (spec §7)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | keymaera ×2, calypto ×2 `wrong → correct` (`unsat`) | **PASS** | all four `unsat` in `slice53` (keymaera 4 ms, calypto 2.0 s / 4.0 s); triage re-run: base `sat` 3/3, after `unsat` 3/3 |
| 2 | ramalho `wrong → correct`, or marker + queued cause | **PASS (fixed branch, 4a)** | `wrong → correct` (796 ms); base `sat` 3/3, after `unsat` 3/3; cause: `fp.add` zero sign under RTN (*Ramalho*) |
| 3 | 0 rows `* → wrong` in all 7 logics | **PASS: 0** | no changed cell ends in `wrong`; no `ESCALATE`; the 1,566 triage re-runs of the after binary contain 0 wrong answers |
| 4 | every `correct → unknown/timeout` row listed and triaged; net `correct` ≥ 0 per logic | **PASS** | 105 rows, all triaged (97 attributable, 8 noise); raw net ≥ 0 in every logic (+40, +61, +2, 0, +32, +43, 0), and credited net ≥ 0 in every logic (+5, +4, +3, 0, +37, +42, 0) |
| 5 | §6.3 catches the defect at HEAD and shows 0 after; oracle discovered count non-zero; lint, test, `ci` green | **PASS** | before: QF_LIA 3, QF_LRA 4 disagreements; after: 0 / 0; oracle suite 720 discovered (717 passed, 3 skipped); see *Gates* |
| 6 | median/p90 ms per logic reported against `slice53-base` | **REPORTED** | *Timing*: neutral, except QF_UFLIA faster |

## Per-logic matrix

From each run's `report.md`, with `slice53-base` above `slice53`:

| logic | run | total | correct | wrong | parse-error | panic | oom | timeout | unknown | unverified | decided% | median ms | p90 ms |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_BVFP | base | 17249 | 17014 | 1 | 0 | 0 | 0 | 232 | 0 | 2 | 98.6 | 18 | 59 |
| QF_BVFP | **slice53** | 17249 | **17054** | **0** | 0 | 0 | 0 | 193 | 0 | 2 | 98.9 | 6 | 31 |
| QF_LIA | base | 13306 | 4769 | 2 | 0 | 57 | 474 | 3237 | 4764 | 3 | 35.8 | 66 | 2295 |
| QF_LIA | **slice53** | 13306 | **4830** | **0** | 0 | 57 | 595 | 3058 | 4764 | 2 | 36.3 | 51 | 2705 |
| QF_LRA | base | 1753 | 412 | 2 | 1064 | 0 | 2 | 179 | 94 | 0 | 23.5 | 5 | 1338 |
| QF_LRA | **slice53** | 1753 | **414** | **0** | 1064 | 0 | 1 | 180 | 94 | 0 | 23.6 | 7 | 1422 |
| QF_S | base | 18940 | 16061 | 0 | 0 | 0 | 0 | 6 | 2775 | 98 | 84.8 | 4 | 12 |
| QF_S | **slice53** | 18940 | **16061** | **0** | 0 | 0 | 0 | 6 | 2775 | 98 | 84.8 | 5 | 14 |
| QF_SLIA | base | 84395 | 24867 | 0 | 195 | 0 | 0 | 43 | 58032 | 1258 | 29.5 | 5 | 14 |
| QF_SLIA | **slice53** | 84395 | **24899** | **0** | 195 | 0 | 0 | 46 | 57992 | 1263 | 29.5 | 5 | 16 |
| QF_UFLIA | base | 659 | 104 | 0 | 0 | 0 | 5 | 533 | 17 | 0 | 15.8 | 2209 | 15094 |
| QF_UFLIA | **slice53** | 659 | **147** | **0** | 0 | 0 | 7 | 488 | 17 | 0 | 22.3 | 1813 | 13483 |
| QF_UFLRA | base | 1284 | 44 | 0 | 1229 | 0 | 6 | 5 | 0 | 0 | 3.4 | 6 | 97 |
| QF_UFLRA | **slice53** | 1284 | **44** | **0** | 1229 | 0 | 10 | 1 | 0 | 0 | 3.4 | 4 | 72 |
| all | base | 137586 | 63271 | 5 | 2488 | 57 | 487 | 4235 | 65682 | 1361 | 46.0 | 7 | 44 |
| all | **slice53** | 137586 | **63449** | **0** | 2488 | 57 | 613 | 3972 | 65642 | 1365 | 46.1 | 6 | 35 |

`status-suspect` and `malformed` are 0 in every row. These are the verdict
sub-buckets that moved:

| logic | bucket | base | slice53 | delta |
| --- | --- | ---: | ---: | ---: |
| QF_S | `unknown:sat-budget` | 1384 | 1385 | +1 |
| QF_S | `unknown:str-model-rejected` | 968 | 967 | −1 |
| QF_SLIA | `unknown:sat-budget` | 4401 | 4247 | −154 |
| QF_SLIA | `unknown:str-model-rejected` | 3009 | 3123 | +114 |

The parse-error, panic and theory-refused buckets are unchanged.

## Transition matrices (changed cells only)

| logic | before | after | count | families |
| --- | --- | --- | ---: | --- |
| QF_BVFP | `wrong` | `correct` | 1 | ramalho 1 |
| QF_BVFP | `timeout` | `correct` | 38 | 20170428-Liew-KLEE 32, 20190429-UltimateAutomizerSvcomp2019 6 |
| QF_BVFP | `timeout` | `unverified` | 1 | 20230321-UltimateAutomizerSvcomp2023 1 |
| QF_BVFP | `unverified` | `correct` | 1 | 20210301-Alive2 1 |
| QF_LIA | `wrong` | `correct` | 2 | calypto 2 |
| QF_LIA | `correct` | `timeout` | 13 | 20220307-SMPT 1, calypto 2, mathsat 5, rings 5 |
| QF_LIA | `timeout` | `correct` | 69 | 2019-cmodelsdiff 3, 2019-ezsmt 4, 20220307-SMPT 53, CIRC 1, RWS 1, nec-smt 3, rings 4 |
| QF_LIA | `timeout` | `oom` | 121 | 2019-cmodelsdiff 6, 20210219-Dartagnan 5, 20220307-SMPT 83, arctic-matrix 1, nec-smt 26 |
| QF_LIA | `timeout` | `unverified` | 2 | 2019-cmodelsdiff 2 |
| QF_LIA | `unverified` | `correct` | 3 | 2019-cmodelsdiff 3 |
| QF_LRA | `wrong` | `correct` | 2 | keymaera 2 |
| QF_LRA | `correct` | `timeout` | 3 | 2019-ezsmt 1, TM 1, sc 1 |
| QF_LRA | `timeout` | `correct` | 3 | 2019-ezsmt 1, sc 2 |
| QF_LRA | `oom` | `timeout` | 1 | 2019-ezsmt 1 |
| QF_LRA | `parse-error` | `timeout` | 1 | 2019-ezsmt 1 |
| QF_LRA | `timeout` | `parse-error` | 1 | 2019-ezsmt 1 |
| QF_S | `unknown:str-model-rejected` | `unknown:sat-budget` | 1 | 20240318-omark 1 |
| QF_SLIA | `correct` | `unknown:sat-budget` | 86 | 20180523-Reynolds 86 |
| QF_SLIA | `correct` | `unknown:str-model-rejected` | 3 | 20230327-stringfuzz-lu 3 |
| QF_SLIA | `correct` | `unverified` | 5 | 20230327-stringfuzz-lu 4, 20230329-denghang 1 |
| QF_SLIA | `unknown:sat-budget` | `correct` | 117 | 20180523-Reynolds 101, 2019-Leetcode 16 |
| QF_SLIA | `unknown:sat-budget` | `timeout` | 3 | 2019-Leetcode 3 |
| QF_SLIA | `unknown:sat-budget` | `unknown:str-model-rejected` | 133 | 2015-Norn 2, 2019-Jiang 110, 20230327-stringfuzz-lu 21 |
| QF_SLIA | `unknown:str-model-rejected` | `correct` | 9 | 20230327-stringfuzz-lu 9 |
| QF_SLIA | `unknown:str-model-rejected` | `unknown:sat-budget` | 13 | 2015-Norn 3, 2019-Jiang 6, 20230327-stringfuzz-lu 4 |
| QF_UFLIA | `timeout` | `correct` | 43 | mathsat 43 |
| QF_UFLIA | `timeout` | `oom` | 2 | 20230314-Jaroslav-Bendik-Certora 2 |
| QF_UFLRA | `timeout` | `oom` | 4 | cpachecker-induction-svcomp14 4 |

Closure, `new = old − outbound + inbound`:

- QF_BVFP `correct` 17,014 + 40 = 17,054; `wrong` 1 − 1 = 0; `timeout`
  232 − 39 = 193; `unverified` 2 − 1 + 1 = 2.
- QF_LIA `correct` 4,769 − 13 + 74 = 4,830; `wrong` 2 − 2 = 0; `timeout`
  3,237 − 192 + 13 = 3,058; `oom` 474 + 121 = 595; `unverified` 3 − 3 + 2 = 2.
- QF_LRA `correct` 412 − 3 + 5 = 414; `wrong` 2 − 2 = 0; `timeout`
  179 − 4 + 5 = 180; `oom` 2 − 1 = 1; parse-error 1,064 − 1 + 1 = 1,064.
- QF_SLIA `correct` 24,867 − 94 + 126 = 24,899; `timeout` 43 + 3 = 46;
  `unverified` 1,258 + 5 = 1,263; `sat-budget` 4,401 − 253 + 99 = 4,247;
  `str-model-rejected` 3,009 − 22 + 136 = 3,123.
- QF_UFLIA `correct` 104 + 43 = 147; `timeout` 533 − 45 = 488; `oom` 5 + 2 = 7.
- QF_UFLRA `timeout` 5 − 4 = 1; `oom` 6 + 4 = 10.

The `unknown → unknown` SLIA flips (133 + 13) and the QF_S omark flip stay
`unknown` before and after. They are fence relabelings, the same kind of
movement as slice 52's 213. The QF_LRA `2019-ezsmt` parse-error/oom/timeout
swaps are rows at the 20 s edge: those files sit near the time limit while
still parsing.

## Triage method

Each re-run used the bench's own command line,
`prlimit --as=3072MiB timeout -s KILL 21 timeout 20 <bin> --stats <file>`,
with up to 6 jobs in parallel under `taskset -c 12-23` and nothing else
running. Each row was re-run **3 times with each binary**, base
(`target/slice53-base/shinri`, md5 `d2daafb3…`) and after
(`target/release/shinri`, md5 `50af1137…` = the `slice53` fixture). Base and
after runs were interleaved, so both binaries shared the same conditions. In
total there were 261 rows and 1,566 runs.

- **Coverage.** Every changed row that ends in or starts from `correct` was
  re-run in full, except Reynolds. That covers all 19 non-Reynolds `LOSS`
  rows, the 5 `correct → unverified` rows, and every gain group (BVFP 38 +
  1 + 1, LIA 69 + 3 + 2, LRA 3 + 2, SLIA Leetcode 16 + stringfuzz 9, UFLIA
  43). Reynolds was handled by a **stratified sample of 16 of the 86 losses
  and 16 of the 101 gains**, plus a deterministic-cause investigation on 4
  losses and 5 gains (below). Six oom transition groups were sampled with 3
  rows each, 18 rows in all.
- **Disposition.** If the row's base-run status reproduces 3/3 with the base
  binary and its after-run status reproduces 3/3 with the after binary, it is
  **solver-attributable**. If both binaries give the same result, or the row
  flips both ways, it is **noise**. A row at the 20 s edge that splits 2/3
  is noise unless the other binary is 0/3.
- Loss sample, Reynolds `kaluza/unsat/big` (ids): 17928 17933 17943 17968
  19299 19304 19310 21762 21768 21773 21778 21784 21790 21795 21859 21864.
  Gain sample: 12235 12241 12248 14023 14030 14036 14085 14092 17762 17768
  17775 18750 18756 18779 19238 19244.
- **No wrong answer from the after binary in 1,566 runs.** The only `wrong`
  answers in the re-runs are the base binary on the five §1.1 rows.

## Every formerly `wrong` row

| row | `:status` | base (bench) | after (bench) | z3 | re-run base / after |
| --- | --- | --- | --- | --- | --- |
| `QF_LRA/keymaera/simple_example_2-node2074.smt2` | unsat | `sat` 3 ms | `unsat` 4 ms | unsat | `sat` ×3 / `unsat` ×3 |
| `QF_LRA/keymaera/simple_example_2-node2406.smt2` | unsat | `sat` 3 ms | `unsat` 4 ms | unsat | `sat` ×3 / `unsat` ×3 |
| `QF_LIA/calypto/problem-001542.cvc.1.smt2` | unsat | `sat` 1,459 ms | `unsat` 4,023 ms | unsat | `sat` ×3 / `unsat` ×3 (2.2 s) |
| `QF_LIA/calypto/problem-001553.cvc.1.smt2` | unsat | `sat` 858 ms | `unsat` 1,975 ms | unsat | `sat` ×3 / `unsat` ×3 (1.2 s) |
| `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2` | unsat | `sat` 1,355 ms | `unsat` 796 ms | unsat | `sat` ×3 / `unsat` ×3 |

The base run had no `wrong` rows beyond these five, so there are no extra
dispositions.

## Every `correct → unknown/timeout` row, triaged

105 rows: QF_LIA 13, QF_LRA 3, QF_SLIA 89. **97 are solver-attributable and
8 are noise.** The 5 `correct → unverified` rows (not `LOSS` lines) are
also triaged below; all are noise.

### The mechanism: base `unsat` on an under-constrained encoding

On `2ceef06`, an arithmetic `(= a b)` under a Bool `=` (iff), or in some
other non-positive position, was an EUF atom with no arithmetic meaning. The
SAT solver could choose its value freely. For `sat` that is the slice's
wrong-answer bug. For `unsat` it is a **relaxation**: if the relaxed problem
is already unsat, the answer is sound, and often cheaper, because the
arithmetic search over that atom is skipped. The slice's axioms restore the
missing constraints, so these rows now face the real, harder problem. Two
rewrite experiments show this. Each changes only the syntax of the arithmetic
`=` atoms, from `(= t c)` to the equivalent `(and (<= t c) (>= t c))`, so that
the **base** binary also encodes them faithfully.

- **rings** (all 17 `=` atoms are `(= o_k 1)` inside `(= (> t 4096) (= o_k 1))`):

  | file | base, original | base, rewritten | after, original |
  | --- | --- | --- | --- |
  | `ring_2exp12_4vars_2ite_unsat` | `unsat` 3.8 s | `unsat` 13.0 s | timeout |
  | `ring_2exp14_3vars_0ite_unsat` | `unsat` 46 ms | **timeout** | timeout |

- **Reynolds `kaluza/unsat/big`**: the row has the shape
  `(= T_SELECT_k (not (= PCTEMP_LHS_k (- 1))))`, and the two such atoms in
  each file were rewritten. On loss rows 17928, 19300, 21760 and 21869, the
  base binary gives `unsat` on the original file and
  `unknown fence=sat-budget` on the rewritten one, which is what the after
  binary gives on both.

**The gains run the same way.** On gain rows 12235, 14030 and 17770, the base
binary given the rewritten file answers `unsat`, like the after binary. On
gain rows 18763 and 19250, it stays `sat-budget`, and the after binary given
the rewritten file also falls back to `sat-budget`. The Reynolds family
therefore sits on the string engine's search-order cliff, the same
sensitivity Task 2 hit with the bare-E lowering. Which side a row lands on
depends on the exact encoding. In this family the slice moved 101 rows up and
86 rows down, a net of +15.

### Per-group dispositions

| logic | group | n | re-run (base ✓/3, after ✓/3) | disposition |
| --- | --- | ---: | --- | --- |
| QF_LIA | rings `ring_2exp{12,14,16}_*` → timeout | 5 | 5 × (3, 0); base 40 ms – 3.6 s | **attributable**: relaxation (rewrite experiment above) |
| QF_LIA | calypto `problem-006045.cvc.1` → timeout | 1 | (3, 0); base ~16.9 s | **attributable** (deterministic; base is near the edge, and the faithful encoding is slower. Mechanism not traced beyond that) |
| QF_LIA | calypto `problem-002666.cvc.1` → timeout | 1 | (3, 3); 17.7 s / 17.1 s | noise (20 s edge, base-run load) |
| QF_LIA | mathsat `FISCHER{10-8,6-10,7-12,8-9,9-8}-fair` → timeout | 5 | 5 × (3, 3); 15–17 s both | noise |
| QF_LIA | SMPT `Referendum-PT-0050/RC-06` → timeout | 1 | (3, 3); 16.7 s / 16.3 s | noise |
| QF_LRA | sc `sc-15.induction.cvc` → timeout | 1 | (3, 0); base ~8 s | **attributable** (deterministic slowdown) |
| QF_LRA | TM `p5-driverlogNumeric_s8` → timeout | 1 | (2, 0); base 19.0–20 s | **attributable, at the edge** (counted against the slice, conservatively) |
| QF_LRA | 2019-ezsmt `blending/13` → timeout | 1 | (2, 3) | noise (flips both ways) |
| QF_SLIA | Reynolds `kaluza/unsat/big` → `sat-budget` | 86 | sample 16 × (3, 0); bench 11–68 ms | **attributable**: relaxation plus the string-engine order cliff (above). All `:status unknown`, base `unsat`, z3 `unsat` |
| QF_SLIA | stringfuzz-lu `regex-050-{multiply-reverse-fuzz, translate-graft-translate, translate-rotate-fuzz}` → `str-model-rejected` | 3 | 3 × (3, 0); ≤ 12 ms | **attributable**: string-engine order sensitivity (below) |
| QF_SLIA | `correct → unverified`: stringfuzz-lu 4, denghang `instance` 1 | 5 | 5 × (3, 3), same answer | noise (z3 oracle side; not a `LOSS` line) |

**The stringfuzz trio** is the smallest reproducer of the order sensitivity.
`regex-050-translate-rotate-fuzz.smt2` is three assertions,
`(= (str.len x) 3)`, `(= x y)` and `(str.in_re y (re.+ (re.range "a" "b")))`,
and its `(= (str.len x) 3)` sits only in a positive top-level position. The
lowering is unchanged there (`(and E Le Ge)`, R6). The only difference is the
three axiom clauses for `E`, yet the answer moves from `unsat` (base, z3
agrees) to `unknown fence=str-model-rejected`: the string engine stops at a
premature SAT that the model gate rejects. `multiply-reverse-fuzz` moves
from `sat` to `str-model-rejected`. Nine rows in the same family went the
other way (`str-model-rejected → correct`, all 3/3 deterministic).

The 105 `LOSS` lines, by path (prefix `QF_SLIA/20180523-Reynolds/kaluza/unsat/big/<id>.corecstrs.readable.smt2`
for the Reynolds ids):

- QF_LIA: `20220307-SMPT/Referendum-PT-0050/RC-06.smt2`,
  `calypto/problem-002666.cvc.1.smt2`, `calypto/problem-006045.cvc.1.smt2`,
  `mathsat/FISCHER10-8-fair.smt2`, `mathsat/FISCHER6-10-fair.smt2`,
  `mathsat/FISCHER7-12-fair.smt2`, `mathsat/FISCHER8-9-fair.smt2`,
  `mathsat/FISCHER9-8-fair.smt2`, `rings/ring_2exp12_4vars_2ite_unsat.smt2`,
  `rings/ring_2exp14_3vars_0ite_unsat.smt2`,
  `rings/ring_2exp14_4vars_2ite_unsat.smt2`,
  `rings/ring_2exp16_3vars_0ite_unsat.smt2`,
  `rings/ring_2exp16_4vars_2ite_unsat.smt2` (all `timeout`).
- QF_LRA: `2019-ezsmt/blending/13.smt2`, `TM/p5-driverlogNumeric_s8.smt2`,
  `sc/sc-15.induction.cvc.smt2` (all `timeout`).
- QF_SLIA `unknown:str-model-rejected`:
  `20230327-stringfuzz-lu/transformed/z3str2/regex-050-multiply-reverse-fuzz.smt2`,
  `…/regex-050-translate-graft-translate.smt2`,
  `…/regex-050-translate-rotate-fuzz.smt2`.
- QF_SLIA Reynolds `unknown:sat-budget` (86 ids): 17928 17929 17930 17931
  17932 17933 17934 17935 17937 17942 17943 17954 17958 17961 17965 17967
  17968 19295 19296 19297 19298 19299 19300 19301 19302 19303 19304 19305
  19306 19307 19308 19309 19310 19311 19312 21760 21761 21762 21763 21764
  21765 21766 21767 21768 21769 21770 21771 21772 21773 21774 21775 21776
  21777 21778 21779 21780 21781 21782 21783 21784 21785 21786 21787 21789
  21790 21791 21792 21793 21794 21795 21851 21853 21855 21856 21858 21859
  21860 21861 21862 21863 21864 21865 21866 21867 21868 21869.

### `timeout → oom` (not a `correct` change, checked anyway)

QF_LIA has 121 such rows, QF_UFLIA 2 and QF_UFLRA 4. Of the 18 sampled rows,
12 run out of memory with **both** binaries (SMPT, cmodelsdiff, Dartagnan,
cpachecker). On those rows the loaded base run simply timed out before it
reached the memory wall, which is noise. The other 6 are deterministic:
`arctic-matrix/constraint-2050620`, `nec-smt/large/handler_sigchld/prp-{0,16,24}-48`
and the two Certora rows. The base binary times out 3/3 at 20 s, while the
after binary runs out of memory 3/3 at about 4 s (nec-smt, arctic) or
11–13 s (Certora). The slice therefore makes some large instances use memory
faster. This is not a `correct` loss, because both outcomes are undecided,
but it is queued.

## Credited gain

| logic | raw net | noise rows (gain / loss) | attributable gains | attributable losses | **credited net** |
| --- | ---: | --- | --- | --- | ---: |
| QF_BVFP | +40 | KLEE 31 + UA2019 3 `timeout → correct` (3, 3); Alive2 `unverified → correct` 1 | ramalho 1; KLEE `imperial_synthetic_interval_klee_bug/query.21` 1, UA2019 `double_req_bl_0250a…_0`, `float_req_bl_0250b…_2`, `float_req_bl_0470…_10` 3 (all (0, 3)) | 0 | **+5** |
| QF_LIA | +61 | gains: SMPT 53, ezsmt 4, cmodelsdiff 3, RWS 1, `unverified → correct` 3 (= 64); losses: SMPT 1, calypto 1, mathsat 5 (= 7) | calypto `wrong → correct` 2, rings 4, nec-smt 3, CIRC 1 (= 10) | rings 5, calypto 1 (= 6) | **+4** |
| QF_LRA | +2 | loss: ezsmt blending/13 1 | keymaera 2, ezsmt `blending/4` 1, sc `sc-13/14.induction2` 2 (= 5) | sc-15 1, TM 1 (= 2) | **+3** |
| QF_S | 0 | – | – | – | **0** |
| QF_SLIA | +32 | loss: 5 `correct → unverified` | Reynolds 101, Leetcode 16, stringfuzz 9 (= 126) | Reynolds 86, stringfuzz 3 (= 89) | **+37** |
| QF_UFLIA | +43 | mathsat 1 | mathsat 42 (EufLaArithmetic `medium5–20` timeout → 45–580 ms; Hash, Wisa) | 0 | **+42** |
| QF_UFLRA | 0 | – | – | – | **0** |
| **all** | **+178** | **−87 net noise** | **+188** | **−97** | **+91** |

Notes:

- **The SMPT 53 `timeout → correct` rows are noise.** 50 are (3, 3), with the
  base binary solving them unloaded. The other 3 sit at the 20 s edge:
  `RwMutex-PT-r0020w0010/RF-05`, `RF-07` (0, 2) and `RF-10` (1, 3). The same
  holds for 31 of the 32 KLEE rows. The base run's load (see *Load
  disclosure*) explains them.
- **The QF_BVFP attributable gains are plausibly the fp.add fix.** The 4 rows
  are deterministic (base 3/3 timeout, after 11–18.5 s). QF_BVFP has no
  Int/Real, so Task 2's axioms are empty there, and the only change that
  reaches these rows is `07ac180`'s rewired zero-sign circuit. The link is
  not traced further.
- **The QF_LIA CIRC and nec-smt gains are near the edge** (after 18.5–19.7 s,
  but 3/3 both ways). If they were counted as noise, the QF_LIA credited net
  would be 0, still ≥ 0. The same goes for the TM loss in QF_LRA (counted
  against the slice).
- **Reynolds is extrapolated.** The +101 / −86 split comes from the bench,
  and the 16 + 16 stratified sample was 100 % deterministic in both
  directions.
- The UFLIA mathsat gains (42) and the Leetcode `sat-budget → correct` gains
  (16) are deterministic and large-margin, and they agree with the axioms'
  purpose. The axioms tie `E` to arithmetic, so the search no longer
  explores assignments that arithmetic would have refuted. Their mechanism is
  not traced row by row.

## Timing (criterion 6)

The bench-level medians are confounded by the base-run load, so a controlled
paired sample was also taken. In each logic, 100 random rows (seed 53) that
are `correct` in both runs were chosen: all 100 of QF_UFLIA's 104 and all 44
of QF_UFLRA's. Each was run once per binary, interleaved, under the same
`prlimit`/`timeout`, `taskset -c 12-23`, 6 jobs, on an otherwise idle
machine. Wall time is measured in ms around the process, including startup.

| logic | bench base med / p90 | bench slice53 med / p90 | paired sample n | sample base med / p90 | sample after med / p90 | median per-row ratio after/base |
| --- | --- | --- | ---: | --- | --- | ---: |
| QF_BVFP | 18 / 59 | 6 / 31 | 100 | 6 / 25 | 6 / 22 | 1.00 |
| QF_LIA | 66 / 2295 | 51 / 2705 | 100 | 64 / 1185 | 64 / 1160 | 0.99 |
| QF_LRA | 5 / 1338 | 7 / 1422 | 100 | 5 / 1115 | 5 / 1315 | 1.00 |
| QF_S | 4 / 12 | 5 / 14 | 100 | 6 / 15 | 5 / 16 | 1.00 |
| QF_SLIA | 5 / 14 | 5 / 16 | 100 | 5 / 13 | 5 / 12 | 1.00 |
| QF_UFLIA | 2209 / 15094 | 1813 / 13483 | 100 | 2199 / 14562 | 1514 / 8333 | 0.82 |
| QF_UFLRA | 6 / 97 | 4 / 72 | 44 | 3.5 / 86 | 4 / 92 | 1.00 |

The bench columns are over all rows, from each `report.md`. Over rows that
are `correct` in both runs, the bench medians are BVFP 18 → 6, LIA 66 → 49,
LRA 5 → 7, S 4 → 5, SLIA 5 → 5, UFLIA 2,192 → 1,407 and UFLRA 6 → 4 ms. The
paired sample gave the same answer from both binaries on all 644 rows.

**Reading.** The three extra clauses per arithmetic `=` cost nothing
measurable at the median. QF_LRA's p90 is higher in the sample (1,115 →
1,315 ms; the 10th-largest of 100 rows, so a noisy statistic), but its median
and per-row ratio are flat. QF_UFLIA is faster. The real costs are not at the
median: they are the deterministic losses and the memory growth listed
above.

## Oracle and probe evidence

- **Probes** (`tests/slice53_probes.rs`, blocking tier, 14 tests). At HEAD
  (`2ceef06`, Task 2 Step 2; 13 discovered then) these 7 failed:
  `demorgan_negated_or`, `negated_implication`, `bool_iff_over_arith_eq`,
  `negated_ite_branches`, `real_fractional_eq_under_demorgan`,
  `keymaera_rows`, and `term_ite_condition` (the last for the separate
  Int-literal reason, R7). After Task 2 all 13 pass. Task 3 added
  `ramalho_min_core`, which was red with the fix stashed and is now green:
  14/14.
- **Oracle family `differential_qf_lia_lra_polarity`**
  (`tests/arith_polarity_oracle.rs`, 200 scripts per sort, z3 4.16.0):

  | | QF_LIA sat / unsat / unknown / disagreements | QF_LRA sat / unsat / unknown / disagreements |
  | --- | --- | --- |
  | before (HEAD `2ceef06`, Task 2 Step 4) | 174 / 26 / 0 / **3** (first: iter 51, shinri `sat`, z3 `unsat`) | 168 / 32 / 0 / **4** (first: iter 60, nested `ite`/`xor`/Bool-`=`) |
  | after (`d9188f3`, Task 2 Step 10, final) | 171 / 29 / 0 / **0** | 164 / 36 / 0 / **0** |

  Both sat and unsat counts are non-zero. The test runtime is 6.3 s, under
  the 30 s target.
- **Unit tests** (`lib.rs`): 4/4, including
  `arith_eq_atoms_splits_nary_like_lower` and
  `binary_arith_eq_lowers_to_conj_with_three_axioms`, which pins `(and E Le Ge)`
  plus exactly three axioms (R6).
- **fp evidence (Task 3):** `fp_add_signed_zero_sums_all_modes` went red to
  green; `shinri-fp` 85 passed / 5 skipped; `fp_oracle` 20/20;
  `fp_add_tiny_exhaustive_all_modes` was spot-run once (`--run-ignored only`),
  1/1, 31 min. It stays `#[ignore]`d. An RTN `fp.add`/`fp.sub` corpus sweep
  of 59 rows gave 0 wrong.

## Ramalho

- **Row:** `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2` (203,638 B,
  587 asserts). At `d9188f3` it was still `sat` (1.7 s), with z3 `unsat`
  (0.04 s): Task 2 did not touch it.
- **Minimized core: 12 asserts, 17 declarations, 1,362 B.** Raw ddmin output
  was 2,456 B; dead `let` bindings of the final claim were then pruned by
  hand. ddmin needed a stage 0 that collapses the final 82-way `or` of negated
  ESBMC claims to one disjunct. Plain assert-ddmin stalled at 587, because
  z3's unsat needs every disjunct refuted. The core is pinned as
  `slice53_probes::ramalho_min_core` (`unsat`, with a `sat` sibling).
- **Cause:** the `fp.add` signed-zero rule. `special_case`
  (`crates/shinri-fp/src/blast/add.rs`) set
  `zero_neg = (sign_a ∧ sign_b) ∨ RTN`, so `(+0)+(+0)` under
  roundTowardNegative came out as −0. IEEE 754 §6.3 keeps the sign of a
  same-sign zero sum in every mode; only an opposite-sign exact-zero sum is −0
  under RTN. The golden `ref_add` (`reference.rs`) had the identical rule, so
  the exhaustive tiny suite and the Float32 random test agreed with the bug.
  In the row, ESBMC computes `signbit(0.0 + 0.0)` under a symbolic rounding
  mode. shinri picked RTN and got −0, which satisfied the negated claim. Its
  model, checked with z3 `eval`, violates asserts #309/#310
  (`(= (fp.add rm +0 +0) f_plus_g@9)` with `f_plus_g@9 = −0`).
- **Fix (branch 4a, `07ac180`):**
  `zero_neg = both_neg ∨ (opp_sign ∧ RTN)`, applied both in `add.rs` and in
  `ref_add`. `fp.sub` reuses `fp_add`, so it is fixed too. `fma` already had
  the correct rule. The row is now `unsat` (796 ms in the bench).

## Gates

Run at `07ac180` before the after-run, on cores 0–11 (R9).

- `cargo fmt --all -- --check`: OK.
- `mise run lint` (fmt `--check` and `clippy --workspace --all-targets -D warnings`): clean.
- `mise run test`: **1,623 tests run, 1,623 passed (8 slow), 7 skipped** (407 s).
- Unfiltered oracle suite, `cargo nextest run -p shinri-solver --features oracle`:
  **720 discovered (717 run + 3 skipped), 717 passed, 0 failed** (2,012 s). The
  count is non-zero: 701 at slice 52, plus 19 from this slice (14 probes,
  4 unit tests and 1 oracle family). Log: `target/slice53-oracle.log`.
- The remaining `ci` dependencies were run separately at `07ac180` (Task 4):
  `mise run deny` gave advisories, bans, licenses and sources all ok
  (rc 0), and `mise run secrets` (gitleaks) found no leaks (rc 0). With lint
  and test above, that covers every dependency of `mise run ci`.

## Queued for the next slice

New from this slice:

- **Remove the redundant `Not(Eq) → (or Lt Gt)` arm.** The timing above shows
  the axioms are not slower at the median, which was spec §10's condition.
  Do it together with the next item, because it changes the encoding the
  string engine is sensitive to.
- **The bare-E §3.3 simplification, together with the string-engine order
  sensitivity.** Returning bare `E` from `lower` regressed
  `probe_c_len_zero_var` and `user_pfx_name_declared_before_any_mint_still_works`
  to `str-model-rejected` (R6). In this run the same sensitivity cost
  Reynolds 86 and stringfuzz 3 rows, and gained Reynolds 101 and stringfuzz 9.
  The smallest reproducer is
  `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-translate-rotate-fuzz.smt2`
  (3 assertions; `unsat` at `2ceef06`, `unknown:str-model-rejected` at
  `07ac180`; z3 `unsat`). The string engine accepts a premature SAT that
  depends on the SAT decision order over its split atoms. Fix that first,
  then the bare-E simplification is safe.
- **Losses from the faithful encoding** (base answers came from a relaxation;
  see *The mechanism*). The reproducers are
  `QF_LIA/rings/ring_2exp14_3vars_0ite_unsat.smt2` (46 ms at `2ceef06`;
  timeout now, and timeout on `2ceef06` too once the `(= o_k 1)` atoms are
  encoded faithfully) and
  `QF_SLIA/20180523-Reynolds/kaluza/unsat/big/21760.corecstrs.readable.smt2`
  (`unsat` → `unknown:sat-budget`). Also `calypto/problem-006045`,
  `sc/sc-15.induction.cvc` and `TM/p5-driverlogNumeric_s8`. These are
  arithmetic search-performance items (an `ite`/iff-heavy LIA mod-ring
  encoding) and string-budget items, not soundness items.
- **Memory growth on large LIA/UFLIA instances.** On
  `nec-smt/large/handler_sigchld/prp-0-48.smt2` the after binary runs out of
  memory at about 4 s (3/3), while `2ceef06` times out at 20 s. The same
  holds for `arctic-matrix/constraint-2050620` and the two Certora rows.
  Measure the axiom pass's term/clause growth on these instances.
- **QF_LRA `ite` with Int-literal branches answers `unknown`** (R7): for
  example `(ite c 1 0)` in a Real context under a QF_LRA header. It is
  pre-existing and independent of this slice. `term_ite_condition` uses
  `1.0`/`0.0` until it is fixed.
- **`(get-model)` does not `|…|`-quote symbols that need it** (names with `#`
  or `:`, as in ESBMC's `__ESBMC_rounding_mode&0#10`), so the printed model is
  not re-parseable SMT-LIB. This was found during the ramalho triage.
- Harness nit: the fixture header records the checkout HEAD, not the binary's
  commit. For `slice53-base` they differ (`807ec5b` vs the `2ceef06`
  sources, docs-only diff).

Ramalho is fixed (branch 4a), so it is not queued.

Carried verbatim from the slice-52 report:

- **H3 needs narrowing.** The word-equation gate own-literal/diseq
  exemption took the Noetzli pair to `unsat` but cost 313 correct `sat`
  rows (309 bisected to Task 4, the rest Norn), `sat-budget` +497 (QF_SLIA) in the H3
  run; reproducer `Reynolds/kaluza/sat/small/1708.corecstrs.readable.smt2`
  (`sat` at `c91e221`, `unknown:sat-budget` at `8ee8f00`). Narrow the gate
  or find why the extra resolution exhausts the SAT budget. The reverted
  commits are `4fb0dab`, `18b1e36`, `8ee8f00` (revert commits `a78895e`,
  `c25fbd2`, `c5cd62c`).
- **4 Norn HammingDistance rows lost to Task 3 (H1).** `norn-benchmark-1190`,
  `-147`, `-151`, `-828`: `sat` at `e61e81c`, `unknown:sat-budget` at
  `c91e221`. Cause: H1 also acts on regex-membership-minted equations
  (the split path skips them, D-wordeq-skip); skipping them in H1 restores
  these 4 but loses 6 Norn gains. **Decide deliberately whether H1 should act
  on membership-minted equations.**
- **`bool_proxy` wrong `sat`** (pre-existing; pinned as a passing known-bug
  marker asserting `sat`, R16), with
  `distinct_form` and `xor_form` (sound `unknown`): a minted-branch
  completeness gap. Needs a deep-nf re-resolve that emits only a cited
  `Propagate` (R11).
- **Deep-nf propagate (R11)** and the `eval_bool` audit, which together
  retire the `bool_proxy` wrong `sat` and the `distinct_form`/`xor_form`
  `unknown`s. The Noetzli `unsat` also needs H3 (above).
- **Evidence limit.** Every unsat in the congruence family is decided at
  level 0; the level > 0 `Split` exposure is covered only by the E1 fuzz
  (measured with H3 present).
- **Search-order fragility (R12)**, which applied to the H3 run: the Noetzli
  pair passed by search order. Worth remembering when H3 returns.
- Single-atom `[] = [y]` merge after H1 leaves `len(y)` unlinked (R10; sound,
  the gate backstops).
- Congruence and minted merges are not in the H3 contributor map (Split-only
  exposure).
- The combiner computes shared terms once per final check, so `len`/`0`
  terms minted mid-check reach arithmetic only on a later final check.
- Deferred minors: `empty_merged` is monotone and never restored on pop
  (perf only); the conflict path of the `len(v) ≈ 0` merge (`lib.rs` ~986)
  has no test; no unit test pins `eval` of a Bool constant `p` under Bool
  `=`; Bool `=` against literal `true`/`false` may return `None` if the
  literals are not `TermNode::App` (conservative); the diseq-test assertion
  message is copied from its sibling.

From spec §10 (slice 52):

- H2 (the AB prefix case; z3 says `sat`, so it is a model-soundness check
  rather than an `unsat` target) and the `eval_bool` audit (spec §9).
- Carried from slice 51: the 4 denghang `unknown:str-model-rejected` rows
  (`instance46836`, `51681`, `52132`, `55189`); premature string SAT on
  decoded control-character regexes (68 rows, reproducer
  `automatark-lu/instance06924.smt2` assertions {1, 2, 3, 5}); surrogate
  support; `str.replace_re`/`str.replace_re_all` (195 parse-error rows).
- Carried from slice 50: the QF_SLIA `STRING_PATH_PIVOT_BUDGET` cliff; the
  Wisa final-check blow-up; `get-value` echoing purification names; the
  `Owner::Shared` definitional merge; `pending` is not backtracked; the
  blocksworld re-index churn measurement; the `blast_word` panic bucket.
- ~~Not re-measured since the baseline: `wrong` rows in QF_LIA (calypto, 2),
  QF_LRA (keymaera, 2), QF_BVFP (ramalho, 1).~~ **Closed by this slice**
  (all five `wrong → correct`).
- Harness nit (carried): the fixture header records the checkout HEAD, not
  the binary's commit. Here they differ for the base run (above).

Test-tier note (carried): the unfiltered oracle suite is dominated by
`fp_oracle differential_qf_fp_rem` (~25–33 min), over the 5 min rule; it is an
existing test, not part of this slice.

## References

- Spec: `docs/superpowers/specs/2026-10-01-shinri-slice53-arith-eq-polarity-design.md`
  (§7 criteria, §10 queue, §12 measured outcomes).
- Plan: `docs/superpowers/plans/2026-10-01-shinri-slice53-arith-eq-polarity.md`.
- Slice-52 report: `docs/superpowers/research/2026-10-01-smtlib-2024-slice52-str-bool-eq-report.md`.
- Baseline: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`.
- Commits: `d9188f3` (axioms, Task 2), `07ac180` (fp.add zero sign, Task 3).
- Runs (git-ignored): `bench/results/slice53/`, `bench/results/slice53-base/`.
