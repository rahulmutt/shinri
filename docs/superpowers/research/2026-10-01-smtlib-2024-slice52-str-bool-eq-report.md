# SMT-LIB 2024 re-run — slice 52 (Bool `=` in the string model gate; word-equation hole H1) — fallback, shinri @ fe686cb33776

**Measured outcome of the slice: the fallback (Ruling R15, H3 dropped).** The
first run (`slice52`, with H3, branch head `fec6fb9`) lost 313 correct `sat`
rows and was reverted at Task 4; it stays on disk as evidence and is reported
in *H3 measured and dropped*. The slice's final measured run is
`slice52-fallback`, compared against `slice51` (fixture sha `924ecc98cd06`),
restricted to QF_S and QF_SLIA:

```
cargo build --release -p shinri-cli
BENCH_LOGICS=QF_S,QF_SLIA BENCH_RUN_ID=slice52-fallback taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice52-fallback mise run bench-report
md5sum target/release/shinri   # 0c5a4ea477c6f4f8d0a643c831b1b2b6 = fixture solver_md5
```

Both runs used the baseline limits: 20 s, 3072 MB, 6 jobs, cgroup `cpu.max`
`800000 100000`, `memory.max` 34359738368, pinned with `taskset -c 12-23`.
Each covers the same 103,335 QF_S + QF_SLIA instances.

| run | solver | `solver_md5` | started | finished | wall-clock |
| --- | --- | --- | --- | --- | --- |
| `slice52-fallback` (final) | `target/release/shinri` @ `fe686cb` (Task 4 reverted) | `0c5a4ea477c6f4f8d0a643c831b1b2b6` | 2026-10-01T09:35:00Z | 11:02:54Z | ~1 h 28 min |
| `slice52` (H3 included, evidence) | `target/release/shinri` @ `fec6fb9` | `bc7ee313398b43ef342af0dfb78856f5` | 2026-09-30T19:44:39Z | 21:09:39Z | ~1 h 25 min |
| `slice51` (comparison) | `target/release/shinri` @ `924ecc9` | `4347bd57aa6542e0b8567be63c5c0a9b` | 2026-09-30T10:31:04Z | 12:05:11Z | ~1 h 34 min |

**Fixture sha** `fe686cb33776` is the branch head the binary was built from
(three reverts of Task 4 plus the probe re-pin on top of `fec6fb9`).
**Baseline validity.** `slice51` was run at `924ecc9`; the slice-52 branch
point (`434d692`) only adds docs since, so `slice51` is the pre-slice
baseline.

**Load disclosure.** `mise run lint` and `mise run test` finished before the
fallback bench started; `mise run ci` and the oracle suite ran after it
finished. The bench ran with no other cargo work (the z3 oracle subprocesses
of the harness itself aside). Noise shows in two places, both below: 9
`correct → unverified` rows (z3 oracle timeout, same shinri answer) and one
Leetcode row at the 20 s boundary.

**How the transitions were computed.** A scratch script (not committed)
loads each `results.jsonl` keyed by `path`, asserts identical key sets
(**103,335 common paths, 0 missing, 0 extra**), and tallies
`(logic, before, after)` with per-family counts. It prints `ESCALATE` for any
row that moves into `wrong`. **It printed none.** Every per-logic count
below closes under `new = old − outbound + inbound`.

Final log line:

```
slice52-fallback  103335/103335  correct=40913 wrong=0 status-suspect=0 parse-error=195 panic=0 oom=0 timeout=50 unknown=60806 unverified=1371 malformed=0
```

## Headline

- **`wrong` fell 2 → 0** across QF_S + QF_SLIA. The Noetzli pair
  (`str-pred-small-rw_370`, `_458`) is now `unknown:str-model-rejected`
  (5 ms, 4 ms): the T2 gate catches the bogus model and answers a sound
  `unknown` instead of a wrong `sat`. This is the fallback outcome; the
  `unsat` the first spec wanted needs H3, which is dropped (below).
- **0 rows moved into `wrong`** from any verdict. There is no `ESCALATE`.
- **Credited gain, stated plainly: the solver's own `correct` gain is +2,
  not +40.** About 35 of QF_SLIA's +37 are z3-timeout oracle noise
  (+44 / −9 between `unverified` and `correct`), and all of QF_S's +3 are
  noise. What the solver earned is the Norn rows, +6 −4 = **+2**, plus the
  Noetzli pair moving from `wrong` to `unknown`.
- **Raw deltas (kept): `correct` QF_S 16,058 → 16,061 (+3), QF_SLIA 24,815 → 24,852 (+37).**
  The gains are oracle-noise rows (3 + 44 `unverified → correct`) and 6
  Norn `unknown → correct`. Losses: 4 Norn `correct → unknown:sat-budget`
  and 9 `correct → unverified` (z3 oracle timeouts, same shinri answer).
- **`unknown:sat-budget`: QF_S 1,379 → 1,384 (+5), QF_SLIA 4,199 → 4,400
  (+201).** `str-model-rejected` moves the other way (QF_S −5, QF_SLIA −202):
  the same Norn/Jiang rows reach the budget fence now instead of the
  model-rejected fence (213 + 5 `unknown → unknown` flips, plus 10 the other
  way). These are `unknown` both before and after.
- **No `correct` row lost to H3.** The only `correct → unknown` rows are 4
  Norn HammingDistance rows (triaged below), caused by Task 3 (H1), not Task 4.
- parse-error 195 → 195, same paths. `status-suspect`, `panic`, `oom`,
  `malformed` are 0; `timeout` 49 → 50 (one Leetcode row at the 20 s edge,
  below).

## What changed versus the plan

1. **The AB (H2) probe.** Spec §1.2/§8 said z3 answers `unsat` for the AB
   script. **z3 answers `sat`** (x = "A", y = "B"). The probe `ab_prefix_h2`
   is therefore a soundness check (Ruling R5): the verdict must not be
   `unsat`, and if `sat` the model must satisfy the assertion.
2. **H1 needed a length link.** An H1 merge (`v ≈ ""`) left arithmetic
   unaware that `len(v) = 0`, so the model builder sliced the anchor word
   wrongly. The fix is that H1 merges also merge `str.len(v) ≈ 0` in the
   shared EUF (Rulings R7–R10), gated to H1 only (`Propagate.link_len`). A
   model-builder override was tried first and **reverted**: it produced a
   wrong `sat` on `"A" = y++x, len y + 1 = 1, x ≠ "A"` (z3 `unsat`).
3. **H3 dropped (Ruling R15).** Task 4 (the word-equation gate own-literal /
   disequality exemption) is reverted as three revert commits; see *H3
   measured and dropped*.
4. **Pins after the fallback.** `noetzli_370`, `noetzli_458`,
   `not_distinct_form`, `distinct_form` and `xor_form` are pinned "not sat"
   (z3 says `unsat`; the T2 gate gives a sound `unknown:str-model-rejected`).
   `bool_proxy` is a known wrong `sat` (z3: `unsat`), pinned as a passing
   known-bug marker that asserts `sat` with a message naming the `eval_bool`
   audit and the queued H3 plus the deep-nf propagate (R11, R16); flip it to
   `unsat` when that work lands.
5. **The Noetzli pair, under the fallback, is not search-order fragile**: it
   is `unknown` by construction (no H3). The R12 fragility applied to the
   dropped H3 run only.

## Success criteria (spec §7, fallback wording)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | `_370` and `_458` go `wrong → unknown:str-model-rejected` (fallback) | **PASS** | both `wrong` `sat` → `unknown:str-model-rejected` (5 ms, 4 ms). The first-choice `wrong → correct (unsat)` was reached in the H3 run (7 ms, 6 ms) and is not kept |
| 2 | QF_S + QF_SLIA `wrong` 2 → 0 | **PASS** | QF_S 0 → 0, QF_SLIA 2 → 0 |
| 3 | 0 rows `* → wrong` | **PASS: 0** | no changed cell ends in `wrong`; no `ESCALATE` |
| 4 | every `correct → unknown/timeout` row listed and triaged; `sat-budget` delta | **DONE (not gated)** | 4 rows, all Norn, all `unknown:sat-budget`; 0 `timeout`; `sat-budget` +5 (QF_S), +201 (QF_SLIA) |
| 5 | gates green, oracle count non-zero | **PASS** | *Gates* below |

## Per-logic matrix

From `bench/results/slice52-fallback/report.md`, with the `slice51` row above it:

| logic | run | total | correct | wrong | parse-error | timeout | unknown | unverified | decided% |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_S | slice51 | 18940 | 16058 | 0 | 0 | 6 | 2775 | 101 | 84.8 |
| QF_S | **slice52-fallback** | 18940 | **16061** | **0** | 0 | 6 | 2775 | 98 | 84.8 |
| QF_SLIA | slice51 | 84395 | 24815 | 2 | 195 | 43 | 58032 | 1308 | 29.4 |
| QF_SLIA | **slice52-fallback** | 84395 | **24852** | **0** | 195 | 44 | 58031 | 1273 | 29.4 |

Verdict sub-buckets that moved:

| logic | bucket | slice51 | slice52-fallback | delta |
| --- | --- | ---: | ---: | ---: |
| QF_S | `unknown:sat-budget` | 1379 | 1384 | +5 |
| QF_S | `unknown:str-model-rejected` | 973 | 968 | −5 |
| QF_SLIA | `unknown:sat-budget` | 4199 | 4400 | +201 |
| QF_SLIA | `unknown:str-model-rejected` | 3211 | 3009 | −202 |

status-suspect, panic, oom and malformed are 0 in every row.

## Transition matrices (changed cells only)

| logic | before | after | count | families |
| --- | --- | --- | ---: | --- |
| QF_S | `unknown:str-model-rejected` | `unknown:sat-budget` | 5 | 2019-Jiang 5 |
| QF_S | `unverified` | `correct` | 3 | 20230329-automatark-lu 3 |
| QF_SLIA | `wrong` | `unknown:str-model-rejected` | 2 | 20190311-str-small-rw-Noetzli 2 |
| QF_SLIA | `correct` | `unknown:sat-budget` | 4 | 2015-Norn 4 |
| QF_SLIA | `correct` | `unverified` | 9 | 20230327-stringfuzz-lu 8, 20230329-denghang 1 |
| QF_SLIA | `unknown:sat-budget` | `correct` | 5 | 2015-Norn 5 |
| QF_SLIA | `unknown:sat-budget` | `timeout` | 1 | 2019-Leetcode 1 |
| QF_SLIA | `unknown:sat-budget` | `unknown:str-model-rejected` | 10 | 2015-Norn 10 |
| QF_SLIA | `unknown:str-model-rejected` | `correct` | 1 | 2015-Norn 1 |
| QF_SLIA | `unknown:str-model-rejected` | `unknown:sat-budget` | 213 | 2015-Norn 97, 2019-Jiang 116 |
| QF_SLIA | `unverified` | `correct` | 44 | 20230327-stringfuzz-lu 44 |

Closure, `new = old − outbound + inbound`:

- QF_S `correct` 16,058 + 3 = 16,061; `unverified` 101 − 3 = 98;
  `str-model-rejected` 973 − 5 = 968; `sat-budget` 1,379 + 5 = 1,384.
- QF_SLIA `correct` 24,815 − 13 + 50 = 24,852; `wrong` 2 − 2 = 0;
  `unverified` 1,308 + 9 − 44 = 1,273; `sat-budget` 4,199 − 16 + 217 =
  4,400; `str-model-rejected` 3,211 − 214 + 12 = 3,009; `timeout` 43 + 1 = 44.

**Oracle-side flips (noise).** All 9 `correct → unverified` rows (8
stringfuzz regexpair/regexsmall, denghang `instance46328`) have the same
shinri answer on both runs and a `slice52-fallback` oracle record
`{"z3": "timeout"}`; `slice51` had z3 confirming. The 47 `unverified →
correct` rows are the reverse (z3 timed out on `slice51`, confirmed here).

**The Leetcode timeout.** `2019-Leetcode/findAnagrams/136a65bc….smt2` was
`unknown:sat-budget` at 19,487 ms on `slice51` and is `timeout` at 20,007 ms:
a row at the 20 s boundary, not a verdict change of substance.

## parse-error triage (195 rows)

The same 195 QF_SLIA `20230403-webapp` rows as `slice51`: identical path set
(`str.replace_re` / `str.replace_re_all` unsupported). No parser regression.

## Criterion 4: every `correct → unknown/timeout` row

4 rows, all QF_SLIA, all to `unknown:sat-budget`, none to `timeout`:
`2015-Norn/HammingDistance/norn-benchmark-{1190,147,151,828}.smt2`
(`:status unknown`, `slice51` `sat` 25–32 ms, z3 `sat`; now
`unknown:sat-budget` 408–473 ms).

**Triage.** These four are lost `sat` answers, not wrong answers. Bisecting
with per-task release binaries (20 s limit): `sat` at `434d692` (branch
point) and at Task 2 (`e61e81c`), `unknown` at Task 3 (`c91e221`). So they
come from Task 3 (H1 and its length link), not from H3.

**Mechanism (traced in the final review).** H1's propagate also fires on
equations minted by the regex-membership pass. The split path deliberately
skips those (`crates/shinri-str/src/lib.rs` ~843, the D-wordeq-skip rule);
H1 does not. A patch that skips membership-minted equations in H1 restores
the 4 lost rows (`1190`, `147`, `151`, `828`) but loses the 6 Norn gains
(`1172`, `1173`, `1178`, `1185`, `1188`, `453`). The mechanism nets +2, so
the code is kept as is. Queued: decide deliberately whether H1 should act on
membership-minted equations. The 213 `unknown:str-model-rejected →
unknown:sat-budget` moves are probably the same mechanism (unverified).

## H3 measured and dropped

The first full run (`slice52`, with H3, `fec6fb9`, `solver_md5`
`bc7ee313…`) is kept at `bench/results/slice52/` (git-ignored).

| logic | slice51 `correct` | slice52 (H3) | slice52-fallback |
| --- | ---: | ---: | ---: |
| QF_S | 16,058 | 16,061 | 16,061 |
| QF_SLIA | 24,815 | 24,562 | 24,852 |

- **wrong 2 → 0 with `unsat`:** the Noetzli pair went `wrong → correct`
  (`unsat`, 7 ms, 6 ms), with 0 `* → wrong`. This is what H3 bought: **2 rows**.
- **It cost 313 rows `correct → unknown` in QF_SLIA** (298
  `unknown:sat-budget`, 15 `unknown:str-model-rejected`): Reynolds kaluza 278
  (214 `sat/small`, 64 `unsat/big`), Jiang slent 31, Norn HammingDistance 4.
  All `:status unknown`, `slice51` answer `sat`, z3 `sat`.
- **309 of the 313 bisect to Task 4:** `sat` at `c91e221`, `unknown` at
  `8ee8f00` (the H3 gate change). The other 4 are the Norn rows, already
  `unknown` at Task 3.
- **`sat-budget` delta in the H3 run:** QF_S +5, QF_SLIA +497 (QF_SLIA
  +201 in the fallback: the other +296 is H3).
- **Reproducer:** `QF_SLIA/20180523-Reynolds/kaluza/sat/small/1708.corecstrs.readable.smt2`
  (assertions `T_2`, `T_4`, the `ite`, `T_6`: Kudzu/Kaluza Bool proxies and
  an `ite` over `v = T0 ++ T1`, `T1 = T2 ++ T3`, `T2 = T4 ++ "GASO="` with
  `(= 0 (str.len T0))` and a negated `str.in_re`). `sat` at `c91e221`,
  `unknown:sat-budget` at `8ee8f00` and in the H3 run, `sat` in the fallback
  run. Three hand-made smaller sketches answered `sat`, so no smaller
  reproducer is claimed. The mechanism is not traced beyond the
  commit-level attribution: H3 lets the gate reach word equations it used to
  skip, and the extra resolution/splitting hits the SAT step budget.
- **Why dropped:** −313 correct `sat` rows for +2 rows. Net QF_SLIA
  `correct` −253. The fallback keeps the soundness win (wrong 2 → 0) at no
  loss.

Row identifiers lost in the H3 run (paths `QF_SLIA/<family>/<dir>/<name>.smt2`):

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


## Oracle and fuzz evidence

The fuzz and oracle evidence below was measured at Task 5 (`fec6fb9`,
**with H3**). The fallback is the Task 3 engine (H1 only) plus the Task 5
test additions; the oracle suite and gates were re-run on it (see *Gates*).
The `E1_BOOLEQ` fuzz "before" run at `c91e221` already exercises the shipped
engine (the shinri-str and shinri-solver sources there are byte-identical to
HEAD): 0 wrong verdicts, 1,652 decided. So "not re-run on the fallback" is no
longer an evidence limit.

**Fallback re-run of the two new oracle families** (final review, and re-run
at the fix wave with the same numbers; `--features oracle`):
`qfs_bool_eq_word_eqs_match_z3` 118 sat / 14 unsat / 68 unknown, 0
disagreements; `qfs_congruence_linked_word_eqs_match_z3` 55 sat / 36 unsat /
109 unknown, 0 disagreements.

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

## Gates (fallback head `fe686cb`)

- `mise run lint`: clean (fmt `--check` and `clippy --workspace
  --all-targets -D warnings`).
- `cargo nextest run -p shinri-solver -E 'binary(slice52_probes)'`: 15 run,
  15 passed, 0 skipped (`bool_proxy` runs as a passing known-bug marker).
  After the final-review fixes, `mise run test` is 1,604 passed, 7 skipped.
- `mise run test`: **1,603 tests run: 1,603 passed, 8 skipped** (7 slow, 268 s).
  The H3 head had 1,611: the difference is the 8 Task 4 tests removed by the
  revert.
- `mise run ci`: green (lint; test 1,603 passed / 8 skipped in 348 s with 9 slow; secrets scan no leaks).
- Unfiltered oracle suite, `cargo nextest run -p shinri-solver --features
  oracle`: **701 discovered (697 run + 4 skipped), 697 passed, 0 failed, 4 skipped** (the ignored exhaustive and fuzz tests; 1,215 s). Non-zero discovered count.

## Queued for the next slice

New from this slice:

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
  the binary's commit. Here they agree (`fe686cb`).

Test-tier note: the unfiltered oracle suite is dominated by the existing
`fp_oracle differential_qf_fp_rem` (~25 min), over the 5 min rule; it is an
existing test, not part of this slice.

## References

- Spec: `docs/superpowers/specs/2026-09-30-shinri-slice52-str-bool-eq-wordeq-design.md`
  (§7 criteria, §10 queue, §12 measured outcomes).
- Slice 51 report: `docs/superpowers/research/2026-09-30-smtlib-2024-slice51-escapes-report.md`.
- Runs (git-ignored): `bench/results/slice52-fallback/` (final),
  `bench/results/slice52/` (H3, evidence), `bench/results/slice51/`.
