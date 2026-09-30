# SMT-LIB 2024 re-run — slice 52 (Bool `=` in the string model gate; word-equation holes H1/H3) — shinri @ fec6fb9dc574

Run-id `slice52` (branch), compared against `slice51` (fixture sha
`924ecc98cd06`), restricted to QF_S and QF_SLIA:

```
cargo build --release -p shinri-cli
BENCH_LOGICS=QF_S,QF_SLIA BENCH_RUN_ID=slice52 taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice52 mise run bench-report
md5sum target/release/shinri   # bc7ee313398b43ef342af0dfb78856f5 = fixture solver_md5
```

Both runs used the baseline limits: 20 s, 3072 MB, 6 jobs, cgroup `cpu.max`
`800000 100000`, `memory.max` 34359738368, pinned with `taskset -c 12-23`.
Each covers the same 103,335 QF_S + QF_SLIA instances.

| run | solver | `solver_md5` | started | finished | wall-clock |
| --- | --- | --- | --- | --- | --- |
| `slice52` | `target/release/shinri` @ `fec6fb9` (branch head) | `bc7ee313398b43ef342af0dfb78856f5` | 2026-09-30T19:44:39Z | 21:09:39Z | ~1 h 25 min |
| `slice51` (comparison) | `target/release/shinri` @ `924ecc9` | `4347bd57aa6542e0b8567be63c5c0a9b` | 2026-09-30T10:31:04Z | 12:05:11Z | ~1 h 34 min |

**Fixture sha** `fec6fb9dc574` is the branch head the binary was built from.
**Baseline validity.** `slice51` was run at `924ecc9`; `main` at the slice-52
branch point (`434d692`) only adds docs since, so `slice51` is the pre-slice
baseline and no separate base run was made.

**Load disclosure.** `mise run lint` and `mise run test` finished before the
bench started; `mise run ci` and the oracle suite ran after it finished. The
bench ran with no other cargo work on the machine (the z3 oracle
subprocesses of the harness itself aside). The one place noise shows is 55
`unverified → correct` rows (oracle-side flips, below), the reverse of slice
51's 62 `correct → unverified` noise rows.

**How the transitions were computed.** A scratch script (not committed)
loads each `results.jsonl` keyed by `path`, asserts identical key sets
(**103,335 common paths, 0 missing, 0 extra**), and tallies
`(logic, before, after)` with per-family counts. It prints `ESCALATE` for any
row that moves into `wrong`. **It printed none.** Every per-logic count
below closes under `new = old − outbound + inbound`.

Final log line:

```
slice52  103335/103335  correct=40623 wrong=0 status-suspect=0 parse-error=195 panic=0 oom=0 timeout=49 unknown=61114 unverified=1354 malformed=0
```

## Headline

- **`wrong` fell 2 → 0** across QF_S + QF_SLIA. Both Noetzli rows are now
  `unsat` (correct): `str-pred-small-rw_370` in 7 ms, `_458` in 6 ms.
- **0 rows moved into `wrong`** from any verdict. There is no `ESCALATE`.
- **`correct` moved the wrong way overall: QF_S 16,058 → 16,061 (+3),
  QF_SLIA 24,815 → 24,562 (−253).** The QF_SLIA drop is 313 rows
  `correct → unknown` (298 `unknown:sat-budget`, 15
  `unknown:str-model-rejected`), offset by +60 inbound (2 Noetzli, 52 + 3
  oracle-noise `unverified → correct`, 6 `unknown:* → correct`). This is
  criterion 4 and is triaged below. **It is not gated by the spec, but it is
  the main cost of the slice and it is larger than the slice's own gain.**
- All 313 outbound rows have `:status unknown`, answered `sat` on `slice51`,
  and z3 confirmed `sat`. They are lost `sat` answers, not lost `unsat`
  answers. 309 of the 313 were re-run on the per-task heads: they answer
  `sat` at Task 3 (`c91e221`) and `unknown` at Task 4 (`8ee8f00`), so the
  regression arrives with Task 4's H3 gate change. The other 4 (Norn
  HammingDistance) are already `unknown` at Task 3 and were not bisected
  further.
- **`unknown:sat-budget`: QF_S 1,379 → 1,384 (+5), QF_SLIA 4,199 → 4,696
  (+497).**
- parse-error 195 → 195, same paths (`str.replace_re`/`str.replace_re_all`).
  `status-suspect`, `panic`, `oom`, `malformed` are 0; `timeout` is unchanged
  (QF_S 6, QF_SLIA 43).

## What changed versus the plan

These four items differ from the spec text and are stated plainly.

1. **The AB (H2) probe.** Spec §1.2/§8 said z3 answers `unsat` for the AB
   script. **z3 answers `sat`** (x = "A", y = "B"). The probe `ab_prefix_h2`
   is therefore a soundness check (Ruling R5): the verdict must not be
   `unsat`, and if `sat` the model must satisfy the assertion.
2. **H1 needed a length link.** An H1 merge (`v ≈ ""`) left arithmetic
   unaware that `len(v) = 0`, so the model builder sliced the anchor word
   wrongly. The fix is that H1 merges also merge `str.len(v) ≈ 0` in the
   shared EUF (Rulings R7–R10), under the same Interface justification. It
   is gated to H1 only (`Propagate.link_len`). A model-builder override was
   tried first and **reverted**: it produced a wrong `sat` on
   `"A" = y++x, len y + 1 = 1, x ≠ "A"` (z3 `unsat`).
3. **Three red pins.** `distinct_form` and `xor_form` give a sound `unknown`
   and are re-pinned to "not sat". `bool_proxy` is a **known wrong `sat`**,
   `#[ignore]`d with a reason. The cause is a minted-branch completeness
   gap: the single-level nf saturates on the opaque concat head, so no
   `[] = [k, x]` is derived. The fix is a deep-nf re-resolve that accepts
   only a cited `Propagate`, queued (R11). No corpus row depends on the
   three forms.
4. **The Noetzli pair passes by search order.** Swapping the disjuncts gives
   `unknown` (R12). Sound either way; fragile to a heuristic change.

## Success criteria (spec §7)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | `_370` and `_458` go `wrong → correct` (`unsat`) | **PASS** | `_370`: wrong `sat` → `unsat` 7 ms. `_458`: wrong `sat` → `unsat` 6 ms. Both `correct` |
| 2 | QF_S + QF_SLIA `wrong` 2 → 0 | **PASS** | QF_S 0 → 0, QF_SLIA 2 → 0; no `wrong` row in `slice52/results.jsonl` |
| 3 | 0 rows `* → wrong` | **PASS: 0** | no changed cell ends in `wrong`; no `ESCALATE` line |
| 4 | every `correct → unknown/timeout` row listed and triaged; `sat-budget` delta reported | **DONE (not gated)** | 313 rows, all `unknown` (298 `sat-budget`, 15 `str-model-rejected`), 0 `timeout`; `sat-budget` +5 (QF_S), +497 (QF_SLIA); table and triage below |
| 5 | gates green, non-zero counts | **PASS** | *Gates* below |

## Per-logic matrix

From `bench/results/slice52/report.md`, with the `slice51` row above it:

| logic | run | total | correct | wrong | parse-error | timeout | unknown | unverified | decided% |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_S | slice51 | 18940 | 16058 | 0 | 0 | 6 | 2775 | 101 | 84.8 |
| QF_S | **slice52** | 18940 | **16061** | **0** | 0 | 6 | 2775 | 98 | 84.8 |
| QF_SLIA | slice51 | 84395 | 24815 | 2 | 195 | 43 | 58032 | 1308 | 29.4 |
| QF_SLIA | **slice52** | 84395 | **24562** | **0** | 195 | 43 | 58339 | 1256 | 29.1 |

Verdict sub-buckets that moved:

| logic | bucket | slice51 | slice52 | delta |
| --- | --- | ---: | ---: | ---: |
| QF_S | `unknown:sat-budget` | 1379 | 1384 | +5 |
| QF_S | `unknown:str-model-rejected` | 973 | 968 | −5 |
| QF_SLIA | `unknown:sat-budget` | 4199 | 4696 | +497 |
| QF_SLIA | `unknown:str-model-rejected` | 3211 | 3021 | −190 |

status-suspect, panic, oom and malformed are 0 in every row.

## Transition matrices (changed cells only)

| logic | before | after | count | families |
| --- | --- | --- | ---: | --- |
| QF_S | `unknown:str-model-rejected` | `unknown:sat-budget` | 5 | 2019-Jiang 5 |
| QF_S | `unverified` | `correct` | 3 | 20230329-automatark-lu 3 |
| QF_SLIA | `wrong` | `correct` | 2 | 20190311-str-small-rw-Noetzli 2 |
| QF_SLIA | `correct` | `unknown:sat-budget` | 298 | 20180523-Reynolds 278, 2019-Jiang 16, 2015-Norn 4 |
| QF_SLIA | `correct` | `unknown:str-model-rejected` | 15 | 2019-Jiang 15 |
| QF_SLIA | `unknown:sat-budget` | `correct` | 5 | 2015-Norn 5 |
| QF_SLIA | `unknown:sat-budget` | `unknown:str-model-rejected` | 10 | 2015-Norn 10 |
| QF_SLIA | `unknown:str-model-rejected` | `correct` | 1 | 2015-Norn 1 |
| QF_SLIA | `unknown:str-model-rejected` | `unknown:sat-budget` | 214 | 2015-Norn 97, 2019-Jiang 117 |
| QF_SLIA | `unverified` | `correct` | 52 | 20230327-stringfuzz-lu 52 |

Closure, `new = old − outbound + inbound`:

- QF_S `correct` 16,058 + 3 = 16,061; `unverified` 101 − 3 = 98;
  `str-model-rejected` 973 − 5 = 968; `sat-budget` 1,379 + 5 = 1,384.
- QF_SLIA `correct` 24,815 − 313 + 60 = 24,562; `wrong` 2 − 2 = 0;
  `unverified` 1,308 − 52 = 1,256; `sat-budget` 4,199 − 15 + 512 = 4,696;
  `str-model-rejected` 3,211 − 215 + 25 = 3,021.

**Oracle-side flips (55 rows, noise).** The 52 + 3 `unverified → correct`
rows have the same shinri answer on both runs; the z3 oracle timed out on
`slice51` (concurrent load there) and confirmed on `slice52`. They are the
reverse of the 62 rows slice 51 disclosed, not a solver change.

**Other movers.** The 5 `Norn sat-budget → correct` and 1
`str-model-rejected → correct` rows and the 214 + 10 `unknown → unknown`
reshuffles are all in the same two families that lose `sat` answers
(2015-Norn, 2019-Jiang `slent`): the solver reaches the budget fence in
places where it used to reach the model-rejected fence. Nothing else changes
verdict.

## parse-error triage (195 rows)

The same 195 QF_SLIA `20230403-webapp` rows as `slice51`: identical path
set, `str.replace_re` / `str.replace_re_all` unsupported operators.
`first_error` changed on 0 rows. No parser regression.

## Criterion 4: every `correct → unknown/timeout` row

313 rows, all to `unknown`, none to `timeout`. Every row: `:status unknown`,
`slice51` answer `sat` (z3 oracle `sat`), so each is a lost `sat` answer.
Branch wall times are 3 ms to 477 ms (all 278 Reynolds rows under 20 ms); the
slowest are the four Norn rows (387–477 ms). There is no near-20 s row.

| family | rows | branch verdict | rows |
| --- | ---: | --- | --- |
| 20180523-Reynolds `kaluza/sat/small` | 214 | `unknown:sat-budget` | 214 |
| 20180523-Reynolds `kaluza/unsat/big` | 64 | `unknown:sat-budget` | 64 |
| 2019-Jiang `slent` | 31 | `sat-budget` 16, `str-model-rejected` 15 | 31 |
| 2015-Norn `HammingDistance` | 4 | `unknown:sat-budget` | 4 |

Row identifiers (paths are `QF_SLIA/<family>/<dir>/<name>.smt2`):

- **Reynolds `kaluza/sat/small`** (`<id>.corecstrs.readable`, 214 rows):
  1708 1731 1740 1794 1812 1830 1854 1855 1856 1859 1875 1878 2050 2051 2055
  2056 2062 2074 2076 2077 2080 2081 2096 2308 2309 2310 2314 2315 2324 2325
  2326 2329 2330 2332 2334 2337 2338 2339 2349 2350 2351 2352 2353 2371 2372
  2373 2392 2393 2395 2413 2414 2419 2433 2439 2470 2475 2500 2501 2511 2516
  2517 2519 2520 2522 2523 2524 2528 2531 2532 2534 2537 2538 2539 2540 2542
  2546 2547 2549 2550 2551 2552 2553 2554 2555 2556 2557 2558 2559 2560 2582
  2583 2584 2586 2591 2592 2595 2604 2607 2610 2611 2613 2614 2615 2616 2617
  2618 2619 2620 2621 2622 2623 2624 2625 2626 2628 2633 2635 2636 2637 2638
  2640 2641 2642 2643 2644 2645 2646 2647 2648 2649 2650 2652 2653 2656 2657
  2659 2660 2661 2662 2663 2664 2665 2666 2673 2675 2676 2681 2682 2684 2685
  2686 2687 2689 2690 2691 2692 2693 2694 2695 2697 2698 2699 2700 2702 2704
  2706 2707 2708 2709 2710 2711 2712 2713 2714 2715 2716 2717 2719 2720 2721
  2722 2723 2724 2745 2760 2770 2774 2778 2781 2784 2786 2790 2791 `indexof`,
  `new.25412` `new.25994` `new.25998` `new.25999` `new.26002` `new.26017`
  `new.26269` `new.26270` `new.26272` `new.26277` `new.26284` `new.26332`
  `new.26333` `new.26334` `new.26335` `new.26398` `new.26400` `new.26457`
  `new.26458` `new.26461`.
- **Reynolds `kaluza/unsat/big`** (64 rows, `<id>.corecstrs.readable`):
  20868 20869 20871 22045 22046 22047 22079 22080, and 22273 through 22328
  (every id in that range).
- **Jiang `slent/slent_kaluza_<n>_sink`**, `sat-budget` (16): 103 1155 1285
  1294 1384 138 170 1762 197 238 677 694 805 821 824 996. `str-model-rejected`
  (15): 1036 107 1461 1574 162 17 276 278 318 609 826 83 8 903 963.
- **Norn `HammingDistance/norn-benchmark-<n>`** (4): 1190 147 151 828.

### Triage

**Attribution: Task 4.** All 313 rows were re-run on the local per-task
heads (20 s limit). 309 answer `sat` at Task 3 (`c91e221`, H1 with the
length link) and `unknown` at Task 4 (`8ee8f00`, the H3 gate change: the
word-equation gate exempts its own literal and ignores disequalities). The
other 4 are the Norn HammingDistance rows, already `unknown` at Task 3; the
cause was not bisected further (Task 2 or Task 3). This is the cost spec §7
criterion 4 anticipated ("§3.3 enables resolution, and so splits, on
equations it used to skip"): H3 lets the gate reach word equations that used
to be skipped, and on these rows the extra resolution and splitting hits the
SAT step budget instead of the model the solver used to find.

**Representative:** `QF_SLIA/20180523-Reynolds/kaluza/sat/small/1708.corecstrs.readable.smt2`
(`:status unknown`, slice 51 `sat` 14 ms, z3 `sat`; branch
`unknown:sat-budget` 7 ms). The shape is the Kudzu/Kaluza encoding: Bool
proxies (`(= T_1 (= "" v))`, `T_2 = (not T_1)`) and an `ite` whose branches
are conjunctions of word equations (`v = T0 ++ T1`, `T1 = T2 ++ T3`,
`T2 = T4 ++ "GASO="`) with `(= 0 (str.len T0))` and negated `str.in_re`. On
the assertion subset {`T_2`, `T_4`, the `ite`, `T_6`}, `unknown` persists. The
assertion subset was found by greedy assertion-level deletion. Three
hand-made smaller sketches of the `ite` (fewer conjuncts, a shorter
`T2 = T4 ++ ...` chain, a one-letter regex) all answered `sat`, so no
smaller reproducer is claimed. The mechanism is not traced beyond the
commit-level attribution above.

**What this is not.** These are lost `sat` answers, not wrong answers: the
gate and the post-solve self-check are sound here (z3 says `sat`; shinri says
`unknown`). No row is `wrong`.

**What it costs.** QF_SLIA `correct` −253 net (24,815 → 24,562), about 1 %
of QF_SLIA `correct`. The slice gains 2 rows (Noetzli) and loses 313.
Whether this is acceptable, or whether H3 should be narrowed so the gate
skips these shapes, is a controller decision; nothing was reverted in this
task.

## Oracle and fuzz evidence

From the Task 5 report (`E1_BOOLEQ=1`, iters 4000, seed `0xe100000001`). The
before run is a scratch worktree at `c91e221` with the same generator change;
the after run is the branch head.

Before (`c91e221`):

```
==== E1 CORPUS SUMMARY ====
iters=4000 seed=0xe100000001
raw disagreements: wrong-sat=0 wrong-unsat=0 bad-model=0
distinct minimized shapes: 0
bool-eq coverage: 2265 of 4000 instances contained >=1 Bool-eq assertion; decided by both shinri and z3: 1652 (658 sat / 994 unsat)
distinct-by-class: wrong-sat=0 wrong-unsat=0 bad-model=0
(corpus empty = engine sound over this fragment/sample)
```

After (branch head):

```
==== E1 CORPUS SUMMARY ====
iters=4000 seed=0xe100000001
raw disagreements: wrong-sat=0 wrong-unsat=0 bad-model=0
distinct minimized shapes: 0
bool-eq coverage: 2265 of 4000 instances contained >=1 Bool-eq assertion; decided by both shinri and z3: 1638 (644 sat / 994 unsat)
distinct-by-class: wrong-sat=0 wrong-unsat=0 bad-model=0
(corpus empty = engine sound over this fragment/sample)
```

- Zero disagreements before and after. Decided-by-both drops by 14, all on
  the sat side (658 → 644): Task 4 turning some `sat` answers into sound
  `unknown`; the same direction as the bench regression above, on a far
  smaller sample.
- Default sample (no `E1_BOOLEQ`) vs `main`: 0 shapes both, no new
  `WrongUnsat`.
- `qfs_bool_eq_word_eqs_match_z3` (seed `0x5252_0000_0001`): 200 iters — 127
  sat / 14 unsat / 59 shinri-unknown / 0 z3-unknown; 127 witnesses; 0
  disagreements.
- `qfs_congruence_linked_word_eqs_match_z3` (Ruling R13, seed
  `0x5252_0000_0002`, after the fix round): 200 iters — 49 sat / 37 unsat /
  114 shinri-unknown / 0 z3-unknown; 49 witnesses; 0 disagreements (was 3
  unsat before retuning).
- **Evidence limit.** Every unsat in the congruence family is decided at
  level 0 (unit wrappers), so that family does not exercise H3's level > 0
  `Split` exposure. The 4000-iteration `E1_BOOLEQ` fuzz (2265 Bool-eq
  instances, 1638 decided, 0 wrong) is the broader net. The fuzz sample
  did not surface `bool_proxy`'s known wrong `sat`, so it is silent on that
  queued issue. The congruence family is best-effort, not a discrimination
  test: there is no known failing instance for the hole it targets (R14).

## Gates

- `mise run lint`: clean (fmt `--check` and `clippy --workspace
  --all-targets -D warnings`).
- `mise run test`: **1,611 tests run: 1,611 passed, 8 skipped** (5 slow; 235 s).
- `mise run ci`: green (lint, test 1,611 passed / 8 skipped in 318 s with 9
  slow, secrets scan no leaks).
- Unfiltered oracle suite, `cargo nextest run -p shinri-solver --features
  oracle`: **701 discovered, 697 run and passed (8 slow), 0 failed, 4 skipped** (the ignored exhaustive and fuzz tests; 1,124 s). Non-zero discovered count.

## Queued for the next slice

New from this slice:

- **The 313 lost `sat` rows (criterion 4).** H3's gate change makes 309
  Reynolds/Jiang rows `sat → unknown:sat-budget/str-model-rejected`;
  reproducer `Reynolds/kaluza/sat/small/1708.corecstrs.readable.smt2`
  (`sat` at `c91e221`, `unknown` at `8ee8f00`). Options: narrow the gate, or
  find why the extra resolution exhausts the SAT budget. The 4 Norn
  HammingDistance rows need their own bisect (already `unknown` at Task 3).
- **`bool_proxy` wrong `sat`** (pre-existing, `#[ignore]`d), with
  `distinct_form` and `xor_form` (sound `unknown`): a minted-branch
  completeness gap. Needs a deep-nf re-resolve that emits only a cited
  `Propagate` (R11).
- **Search-order fragility (R12).** The Noetzli pair passes by search order;
  swapping the disjuncts gives `unknown`. A later heuristic change could
  flip `_370`/`_458` to `unknown` (never wrong).
- **Evidence limit.** Every unsat in the congruence family is decided at
  level 0; the level > 0 `Split` exposure is covered only by the E1 fuzz.
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

From spec §10:

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
- Not re-measured since the baseline: `wrong` rows in QF_LIA (calypto, 2),
  QF_LRA (keymaera, 2), QF_BVFP (ramalho, 1).
- Harness nit (carried): the fixture header records the checkout HEAD, not
  the binary's commit. Here they agree (`fec6fb9`).

Test-tier note: the unfiltered oracle suite is dominated by the existing
`fp_oracle differential_qf_fp_rem` (~25 min), over the 5 min rule; it is an
existing test, not part of this slice.

## References

- Spec: `docs/superpowers/specs/2026-09-30-shinri-slice52-str-bool-eq-wordeq-design.md`
  (§7 criteria, §10 queue, §12 measured outcomes).
- Slice 51 report: `docs/superpowers/research/2026-09-30-smtlib-2024-slice51-escapes-report.md`.
- Runs (git-ignored): `bench/results/slice52/`, `bench/results/slice51/`.
