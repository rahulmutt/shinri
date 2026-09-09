<!-- Verbatim artefact: bench/results/baseline-8de004d44944/report.md (run-id baseline-8de004d44944). -->
# shinri-bench report

## Fixture

| field | value |
| --- | --- |
| sha | 8de004d44944 |
| version | shinri 0.1.0 |
| timeout_s | 20 |
| mem_mb | 3072 |
| jobs | 6 |
| cpu_max | 800000 100000 |
| memory_max | 34359738368 |
| corpus | 10.5281/zenodo.11061097 |
| started | 2026-09-08T13:02:55Z |

Rows: 257671 across 15 logic(s).

## Per-logic matrix

| logic | total | correct | wrong | status-suspect | parse-error | panic | oom | timeout | unknown | unverified | malformed | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_ABV | 15148 | 8454 | 359 | 0 | 26 | 5787 | 98 | 361 | 62 | 1 | 0 | 55.8 | 12 | 173 |
| QF_AUFBV | 75 | 18 | 0 | 0 | 13 | 5 | 6 | 19 | 14 | 0 | 0 | 24.0 | 195 | 783 |
| QF_AX | 551 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 551 | 0 | 0 | 0.0 | n/a | n/a |
| QF_BV | 46191 | 35840 | 0 | 0 | 1401 | 0 | 3597 | 5351 | 0 | 2 | 0 | 77.6 | 84 | 3394 |
| QF_BVFP | 17249 | 17032 | 1 | 0 | 0 | 0 | 0 | 215 | 0 | 1 | 0 | 98.7 | 15 | 51 |
| QF_DT | 8700 | 7849 | 328 | 0 | 0 | 0 | 0 | 507 | 11 | 5 | 0 | 90.2 | 6 | 11 |
| QF_FP | 40407 | 218 | 0 | 0 | 39998 | 0 | 15 | 173 | 0 | 3 | 0 | 0.5 | 51 | 2091 |
| QF_LIA | 13306 | 4787 | 2 | 0 | 0 | 0 | 576 | 3174 | 4764 | 3 | 0 | 36.0 | 68 | 2227 |
| QF_LRA | 1753 | 411 | 2 | 0 | 1063 | 0 | 2 | 181 | 94 | 0 | 0 | 23.4 | 4 | 1413 |
| QF_S | 18940 | 16025 | 2 | 0 | 0 | 0 | 0 | 8 | 2809 | 96 | 0 | 84.6 | 5 | 19 |
| QF_SLIA | 84395 | 24799 | 37 | 0 | 195 | 0 | 0 | 41 | 58063 | 1260 | 0 | 29.4 | 4 | 16 |
| QF_UF | 7503 | 7106 | 0 | 0 | 34 | 0 | 0 | 363 | 0 | 0 | 0 | 94.7 | 71 | 4349 |
| QF_UFBV | 1510 | 1208 | 0 | 0 | 50 | 0 | 80 | 141 | 31 | 0 | 0 | 80.0 | 101 | 664 |
| QF_UFLIA | 659 | 103 | 11 | 0 | 0 | 0 | 5 | 523 | 17 | 0 | 0 | 15.6 | 2497 | 13196 |
| QF_UFLRA | 1284 | 44 | 0 | 0 | 1229 | 0 | 10 | 1 | 0 | 0 | 0 | 3.4 | 4 | 76 |
| all | 257671 | 123894 | 742 | 0 | 44009 | 5792 | 4389 | 11058 | 66416 | 1371 | 0 | 48.1 | 11 | 675 |

## Ranked gaps

### parse-error:- — 44009

QF_ABV: 26, QF_AUFBV: 13, QF_BV: 1401, QF_FP: 39998, QF_LRA: 1063, QF_SLIA: 195, QF_UF: 34, QF_UFBV: 50, QF_UFLRA: 1229

- `QF_FP/schanda/spark/discrete.smt2` (428 bytes)
- `QF_UF/20170829-Rodin/smt4027072204816894856.smt2` (459 bytes)
- `QF_UF/20170829-Rodin/smt3809952321495040629.smt2` (555 bytes)

### unknown:str-indexof-replace — 26363

QF_S: 80, QF_SLIA: 26283

- `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/lib_int-distutils_get_build_version/8.smt2` (479 bytes)
- `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/lib_int-wsgiref_check_status/3.smt2` (524 bytes)
- `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/lib_int-email__parsedate_tz/18.smt2` (557 bytes)

### unknown:str-predicate-polarity — 16016

QF_SLIA: 16016

- `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/leetcode_int-validIPAddress/13.smt2` (456 bytes)
- `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/lib_int-http_parse_request/6.smt2` (470 bytes)
- `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/leetcode_int-validIPAddress/19.smt2` (491 bytes)

### timeout — 11058

QF_ABV: 361, QF_AUFBV: 19, QF_BV: 5351, QF_BVFP: 215, QF_DT: 507, QF_FP: 173, QF_LIA: 3174, QF_LRA: 181, QF_S: 8, QF_SLIA: 41, QF_UF: 363, QF_UFBV: 141, QF_UFLIA: 523, QF_UFLRA: 1

- `QF_LIA/check/int_incompleteness1.smt2` (342 bytes)
- `QF_LIA/check/int_incompleteness3.smt2` (411 bytes)
- `QF_LIA/check/int_incompleteness2.smt2` (442 bytes)

### panic:crates/shinri-bv/src/blast/mod.rs: internal error: entered unreachable code: non-BV builtin reached blast_word — 5792

QF_ABV: 5787, QF_AUFBV: 5

- `QF_ABV/bench_ab/b334test0001.smt2` (722 bytes)
- `QF_ABV/bench_ab/a284test0003.smt2` (723 bytes)
- `QF_ABV/egt/egt-2292.smt2` (735 bytes)

### unknown:sat-budget — 5548

QF_DT: 11, QF_S: 1353, QF_SLIA: 4184

- `QF_SLIA/20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_135.smt2` (731 bytes)
- `QF_S/20240318-omark/noodles-unsat-4.smt2` (734 bytes)
- `QF_SLIA/2018-Kepler/quad-002-1-unsat.smt2` (734 bytes)

### unknown:theory-refused — 5425

QF_AX: 551, QF_LIA: 4764, QF_LRA: 58, QF_SLIA: 35, QF_UFLIA: 17

- `QF_LIA/pb2010/normalized-1096.cudf.paranoid.smt2` (316 bytes)
- `QF_LIA/prime-cone/prime_cone_sat_2.smt2` (330 bytes)
- `QF_LIA/cut_lemmas/10-vars/cut_lemma_01_001.smt2` (434 bytes)

### oom — 4389

QF_ABV: 98, QF_AUFBV: 6, QF_BV: 3597, QF_FP: 15, QF_LIA: 576, QF_LRA: 2, QF_UFBV: 80, QF_UFLIA: 5, QF_UFLRA: 10

- `QF_BV/brummayerbiere4/unconstrained10.smt2` (631 bytes)
- `QF_ABV/brummayerbiere3/unconstrained01.smt2` (645 bytes)
- `QF_BV/brummayerbiere4/unconstrained07.smt2` (656 bytes)

### unknown:str-model-rejected — 4290

QF_S: 1033, QF_SLIA: 3257

- `QF_S/20240318-omark/parikh.smt2` (435 bytes)
- `QF_S/20240318-omark/cyclic-xy.smt2` (614 bytes)
- `QF_SLIA/2018-Kepler/quad-003-2-sat.smt2` (652 bytes)

### unknown:str-substr-at — 3359

QF_SLIA: 3359

- `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/leetcode_int-validWordAbbreviation/18.smt2` (522 bytes)
- `QF_SLIA/2019-Leetcode/longestCommonPrefix/2584ab3c646317d42d9857d7f042b6b3c2dbdce601ba2b8018ae9ea6.smt2` (523 bytes)
- `QF_SLIA/2019-Leetcode/myAtoi/3e2b270dd2410311f820e64ee9bde41c2c3ea2a5420c40d14b40a6b2.smt2` (526 bytes)

### unknown:reglan-decl — 3287

QF_SLIA: 3287

- `QF_SLIA/20240411-redos_attack_detection/sat/2816_attack.smt2` (1151 bytes)
- `QF_SLIA/20240411-redos_attack_detection/sat/3066_attack.smt2` (1151 bytes)
- `QF_SLIA/20240411-redos_attack_detection/sat/309_attack.smt2` (1151 bytes)

### unknown:str-int-conv — 1616

QF_SLIA: 1616

- `QF_SLIA/20190311-str-small-rw-Noetzli/str-term-small-rw/str-term-small-rw_326.smt2` (729 bytes)
- `QF_SLIA/20190311-str-small-rw-Noetzli/str-term-small-rw/str-term-small-rw_335.smt2` (729 bytes)
- `QF_SLIA/20190311-str-small-rw-Noetzli/str-term-small-rw/str-term-small-rw_343.smt2` (730 bytes)

### unverified — 1371

QF_ABV: 1, QF_BV: 2, QF_BVFP: 1, QF_DT: 5, QF_FP: 3, QF_LIA: 3, QF_S: 96, QF_SLIA: 1260

- `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00001-2.smt2` (840 bytes)
- `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00001-19.smt2` (866 bytes)
- `QF_SLIA/20230329-denghang/instance46350.smt2` (985 bytes)

### unknown:str-regex — 369

QF_S: 343, QF_SLIA: 26

- `QF_S/2020-sygus-qgen/queries/query3308.smt2` (666 bytes)
- `QF_S/2020-sygus-qgen/queries/query3331.smt2` (666 bytes)
- `QF_S/2020-sygus-qgen/queries/query3392.smt2` (666 bytes)

### unknown:abv-fenced — 62

QF_ABV: 62

- `QF_ABV/20230321-UltimateAutomizerSvcomp2023/s3_srvr.blast.06.i.cil-1.c_4.smt2` (20658 bytes)
- `QF_ABV/20230321-UltimateAutomizerSvcomp2023/s3_srvr.blast.07.i.cil-2.c_3.smt2` (20658 bytes)
- `QF_ABV/20230321-UltimateAutomizerSvcomp2023/s3_srvr.blast.11.i.cil-1.c_2.smt2` (20658 bytes)

### unknown:theory-lira — 36

QF_LRA: 36

- `QF_LRA/sc/sc-5.induction3.cvc.smt2` (13078 bytes)
- `QF_LRA/sc/sc-6.induction3.cvc.smt2` (15444 bytes)
- `QF_LRA/sc/sc-7.induction3.cvc.smt2` (17820 bytes)

### unknown:bv-uf-budget — 23

QF_UFBV: 23

- `QF_UFBV/20210312-Bouvier/vlsat3_j55.smt2` (9221880 bytes)
- `QF_UFBV/20210312-Bouvier/vlsat3_j56.smt2` (9932079 bytes)
- `QF_UFBV/20210312-Bouvier/vlsat3_j57.smt2` (10063882 bytes)

### unknown:abv-uf-args — 13

QF_AUFBV: 13

- `QF_AUFBV/2019-Wolf-fmbench/2018E/VexRiscv-regch0-15-compact-mem.smt2` (126947 bytes)
- `QF_AUFBV/2019-Wolf-fmbench/2018E/VexRiscv-regch0-20-compact-mem.smt2` (128192 bytes)
- `QF_AUFBV/2019-Wolf-fmbench/2018E/zipcpu-zipmmu-compact-mem.smt2` (130506 bytes)

### unknown:bv-uf-args — 9

QF_AUFBV: 1, QF_UFBV: 8

- `QF_UFBV/2019-Wolf-fmbench/2018E/zipcpu-busdelay-compact-nomem.smt2` (110325 bytes)
- `QF_AUFBV/2019-Wolf-fmbench/2018E/zipcpu-busdelay-compact-mem.smt2` (113110 bytes)
- `QF_UFBV/2019-Wolf-fmbench/2018E/zipcpu-zipmmu-compact-nomem.smt2` (133522 bytes)

## Wrong answers

| path | :status | shinri | z3 | cvc5 |
| --- | --- | --- | --- | --- |
| `QF_ABV/brummayerbiere/binarysearch32s016.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/binarysearch32s032.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/binarysearch32s064.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/binarysearch32s128.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/binarysearch32s256.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort002un.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/bubsort003un.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/bubsort004un.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/bubsort005un.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/bubsort006un.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/bubsort007un.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/bubsort008un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort009un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort010un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort012un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort014un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort016un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort018un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort020un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort025un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort030un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort035un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort040un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort045un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/bubsort050un.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains002ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains003ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains004ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains005ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains006ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains007ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains008ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains009ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains010ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains011ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains012ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains013ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains014ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains015ue.smt2` | unsat | sat | unsat | - |
| `QF_ABV/brummayerbiere/wchains016ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains017ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains018ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains019ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains020ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains022ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains024ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains026ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains028ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains030ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains032ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains034ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains036ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains038ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains040ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains042ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains044ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains046ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains048ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains050ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains055ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains060ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains065ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains070ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains075ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains080ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains085ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains090ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains095ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere/wchains100ue.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere2/countbitstable016.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere2/countbitstable032.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere2/countbitstable064.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere2/countbitstable128.smt2` | unsat | sat | timeout | - |
| `QF_ABV/brummayerbiere2/countbitstable256.smt2` | unsat | sat | timeout | - |
| `QF_ABV/calc2/calc2_sec2_shifter_bmc10.atlas.smt2` | unsat | sat | unsat | - |
| `QF_ABV/calc2/calc2_sec2_shifter_mult_bmc10.atlas.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_cut.hash_compare_ints.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_expr.looks_like_integer.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_expr.looks_like_integer.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_expr.nomoreargs.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fmt.same_para.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fmt.same_para.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fmt.same_para.il.disjunctions_2.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fmt.same_para.il.disjunctions_3.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fmt.set_other_indent.il.disjunctions_4.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fmt.set_other_indent.il.disjunctions_6.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fold.adjust_column.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fold.adjust_column.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fold.adjust_column.il.disjunctions_2.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fold.adjust_column.il.disjunctions_3.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fold.adjust_column.il.disjunctions_4.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_fold.adjust_column.il.disjunctions_5.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_mv.dev_info_compare.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_od.simple_strtoul.il.disjunctions_2.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_pathchk.component_len.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_pathchk.component_len.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_pathchk.component_len.il.disjunctions_2.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_pathchk.component_len.il.disjunctions_3.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_pr.cols_ready_to_print.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_pr.reset_status.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_rmdir.errno_rmdir_non_empty.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_shuf.input_numbers_option_used.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_shuf.randperm_bound.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_shuf.randperm_bound.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_stty.baud_to_value.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_stty.baud_to_value.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_stty.baud_to_value.il.disjunctions_2.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_stty.baud_to_value.il.disjunctions_3.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_stty.visible.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_tac.re_node_set_compare.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_tac.re_node_set_compare.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_tac.re_node_set_contains.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_touch.time_zone_hhmm.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_touch.time_zone_hhmm.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_touch.time_zone_hhmm.il.disjunctions_2.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_tsort.walk_tree.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_10.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_100.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_17.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_22.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_25.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_38.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_43.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_48.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_5.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_9.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.get_type_indicator.il.disjunctions_95.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.initialize_ordering_vector.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.is_colored.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.is_colored.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.is_directory.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.set_exit_status.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.stophandler.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_vdir.unsigned_file_size.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_yes.get_quoting_style.il.disjunctions_0.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try4_difret_functions_disjunctions_yes.get_quoting_style.il.disjunctions_1.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_base64.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_base64.isbase64.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_basename.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cat.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.AD_compare.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.chopt_free.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.hash_get_max_bucket_length.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.hash_get_n_buckets.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.hash_get_n_buckets_used.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.hash_get_n_entries.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.hash_string.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.hash_table_ok.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chgrp.i_ring_empty.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_chroot.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cksum.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_comm.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_csplit.find_subexp_node.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_csplit.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_csplit.re_node_set_contains.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_csplit.search_cur_bkref_entry.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.compare_ranges.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.hash_compare_ints.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.hash_get_max_bucket_length.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.hash_get_n_buckets.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.hash_get_n_buckets_used.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.hash_get_n_entries.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.hash_int.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.hash_string.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_cut.hash_table_ok.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_date.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_date.time_zone_hhmm.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_date.yydestruct.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_date.yyerror.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_dd.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_df.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_dirname.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_echo.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_env.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_expand.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_expr.find_subexp_node.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_expr.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_expr.looks_like_integer.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_expr.nomoreargs.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_expr.re_node_set_contains.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_expr.search_cur_bkref_entry.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_factor.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_fmt.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_fmt.same_para.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_fold.adjust_column.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_fold.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_head.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_hostid.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_hostname.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_id.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_join.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_kill.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_link.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_ln.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_logname.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_md5sum.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mkdir.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mkfifo.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mknod.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.buffer_lcm.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.dev_info_compare.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.hash_get_max_bucket_length.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.hash_get_n_buckets.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.hash_get_n_buckets_used.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.hash_get_n_entries.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.hash_pjw.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.hash_string.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.hash_table_ok.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.set_author.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.src_to_dest_compare.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_nice.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_nl.find_subexp_node.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_nl.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_nl.re_node_set_contains.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_nl.search_cur_bkref_entry.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_nohup.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_od.format_address_none.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_od.get_lcm.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_od.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_paste.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_pathchk.component_len.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_pathchk.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_pinky.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_pr.cols_ready_to_print.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_pr.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_printenv.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_printf.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_ptx.compare_words.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_ptx.find_subexp_node.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_ptx.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_ptx.re_node_set_contains.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_ptx.search_cur_bkref_entry.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_pwd.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_readlink.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_rmdir.errno_rmdir_non_empty.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_rmdir.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_seq.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_setuidgid.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_sha1sum.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_sha256sum.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_sha512sum.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_shred.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_shred.randint_get_source.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_shuf.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_shuf.input_numbers_option_used.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_shuf.randint_get_source.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_shuf.randperm_bound.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_sleep.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_split.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_stat.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_stty.baud_to_value.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_stty.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_su.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_sum.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_sync.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tac.find_subexp_node.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tac.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tac.re_node_set_contains.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tac.search_cur_bkref_entry.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tail.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tail.pretty_name.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tee.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_test.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_touch.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_touch.time_zone_hhmm.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_touch.yydestruct.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_touch.yyerror.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tr.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_true.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tsort.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tsort.walk_tree.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tty.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_uname.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_unexpand.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_uniq.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_unlink.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_uptime.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_users.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.dev_ino_compare.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.get_type_indicator.il.dwp.smt2` | unsat | sat | timeout | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.hash_get_max_bucket_length.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.hash_get_n_buckets.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.hash_get_n_buckets_used.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.hash_get_n_entries.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.hash_string.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.hash_table_ok.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.is_directory.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.rev_strcmp_atime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.rev_strcmp_ctime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.rev_strcmp_mtime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.rev_strcmp_size.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.rev_xstrcoll_atime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.rev_xstrcoll_ctime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.rev_xstrcoll_mtime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.rev_xstrcoll_size.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.strcmp_atime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.strcmp_ctime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.strcmp_mtime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.strcmp_size.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.unsigned_file_size.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.xstrcoll_atime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.xstrcoll_ctime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.xstrcoll_mtime.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.xstrcoll_size.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_wc.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_who.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_whoami.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_yes.get_quoting_style.il.dwp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_cut.hash_compare_ints.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_cut.hash_int.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_expr.looks_like_integer.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_expr.nomoreargs.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_fmt.same_para.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_fold.adjust_column.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_mv.buffer_lcm.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_mv.dev_info_compare.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_pathchk.component_len.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_rmdir.errno_rmdir_non_empty.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_shuf.input_numbers_option_used.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_shuf.randperm_bound.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_stty.baud_to_value.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_tac.re_node_set_compare.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_touch.time_zone_hhmm.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_touch.yyerror.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_tsort.walk_tree.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_vdir.get_type_indicator.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_vdir.hash_get_n_entries.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_vdir.is_directory.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_vdir.unsigned_file_size.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_fse-bfs_yes.get_quoting_style.il.fse-bfs.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_chgrp.i_ring_empty.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_cut.hash_compare_ints.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_cut.hash_int.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_expr.looks_like_integer.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_expr.nomoreargs.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_fmt.same_para.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_fold.adjust_column.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_mv.buffer_lcm.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_mv.dev_info_compare.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_pathchk.component_len.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_rmdir.errno_rmdir_non_empty.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_sha512sum.get_quoting_style.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_shred.randint_get_source.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_shuf.input_numbers_option_used.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_shuf.randperm_bound.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_stty.baud_to_value.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_touch.time_zone_hhmm.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_touch.yyerror.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_tsort.walk_tree.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_vdir.get_type_indicator.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_vdir.hash_get_n_buckets_used.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_vdir.is_directory.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_vdir.unsigned_file_size.il.wp.smt2` | unsat | sat | unsat | - |
| `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30014.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30072.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30082.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l40097.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l70084.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l80029.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l90080.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v10/v10l70096.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v10/v10l80031.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l20032.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l60008.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l60052.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l70004.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l70054.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l70094.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l90037.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l90066.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v3/v3l40023.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v3/v3l50030.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v3/v3l60017.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v3/v3l60025.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v3/v3l60026.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v3/v3l60047.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v3/v3l80045.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v3/v3l80064.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l20052.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l30041.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l30065.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l40071.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l40092.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l70035.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l70044.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l70073.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l80039.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l80076.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l90001.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v5/v5l90026.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l20016.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l20058.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l20061.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l20084.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l30046.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l30069.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l30072.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l40024.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l40028.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l40043.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l40047.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l40088.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l40091.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l50021.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l50037.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l50060.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60011.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60030.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60064.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60089.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l70003.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l70069.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l80008.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l80086.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l80088.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l90047.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l30009.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l30054.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l40015.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l40082.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l50015.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l50053.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l60032.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l70034.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l70059.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l70068.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l90018.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l90029.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l90056.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v10/typed_v10l90099.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l20028.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l20042.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l20049.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l20050.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l20080.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l20081.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l30005.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l30043.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l30092.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l40007.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l40036.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l40052.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l40072.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l50013.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l50020.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l50099.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l60036.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l60047.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l60082.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70005.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70043.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70046.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70064.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70072.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70075.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70078.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l80015.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l80081.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l90022.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l90067.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l90088.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l90099.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20002.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20027.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20036.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20053.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20068.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20095.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l30007.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l40002.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l40071.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l40079.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l50021.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l50023.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l50027.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l50043.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l50060.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l70019.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l70043.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l70048.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l70058.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l80030.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l80051.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l80055.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l90036.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l90045.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l90081.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l90094.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l20092.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l30006.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l30064.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l30087.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l40005.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l40047.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l40087.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l50059.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l50083.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l60006.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l60022.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l60055.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l70002.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l70003.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l70014.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l70020.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l70045.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l70061.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l80012.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l80046.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l80059.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l80064.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90006.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90035.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90044.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90061.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90070.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90077.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90079.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90094.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90100.cvc.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_1_15_to_13_1_2_negated_goal_bmc_13.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_1_19_to_6_3_11_negated_goal_bmc_11.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_1_19_to_6_3_11_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_1_19_to_6_3_11_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_3_6_to_2_0_7_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_6_0_to_5_0_1_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_7_3_to_8_1_1_negated_goal_bmc_11.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_7_3_to_8_1_1_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_7_3_to_8_1_1_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_9_0_to_1_6_2_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_9_4_to_3_3_7_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_10_0_0_to_7_3_0_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_10_4_3_to_1_14_2_negated_goal_bmc_10.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_10_5_6_to_13_6_2_negated_goal_bmc_9.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_11_0_10_to_18_1_2_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_11_4_8_to_17_1_5_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_11_6_0_to_8_0_9_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_0_7_to_18_0_1_negated_goal_bmc_10.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_0_7_to_18_0_1_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_0_7_to_18_0_1_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_1_0_to_11_1_1_negated_goal_bmc_13.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_1_0_to_1_12_0_negated_goal_bmc_10.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_1_1_to_5_7_2_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_1_3_to_11_1_4_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_7_0_to_14_5_0_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_12_7_0_to_14_5_0_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_13_1_5_to_8_4_7_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_13_1_5_to_8_4_7_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_13_2_4_to_13_3_3_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_13_2_4_to_13_3_3_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_14_0_3_to_12_4_1_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_14_0_3_to_12_4_1_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_14_1_0_to_5_1_9_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_15_2_6_to_18_3_2_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_15_6_4_to_10_2_13_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_16_2_1_to_12_6_1_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_16_4_2_to_16_3_3_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_16_4_2_to_16_3_3_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_16_4_2_to_16_3_3_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_17_0_1_to_1_10_7_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_17_2_1_to_19_1_0_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_17_2_3_to_8_7_7_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_18_0_3_to_4_13_4_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_18_1_7_to_7_17_2_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_18_5_3_to_18_1_7_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_0_2_to_1_0_2_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_0_2_to_1_0_2_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_14_5_to_17_3_0_negated_goal_bmc_10.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_14_5_to_17_3_0_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_1_7_to_3_0_6_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_1_7_to_3_0_6_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_21_4_to_17_7_2_negated_goal_bmc_14.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_24_0_to_9_16_0_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_2_10_to_13_0_0_negated_goal_bmc_12.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_2_10_to_13_0_0_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_2_10_to_13_0_0_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_5_0_to_5_1_0_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_5_5_to_1_1_9_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_6_3_to_9_0_1_negated_goal_bmc_12.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_7_5_to_6_4_3_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_9_5_to_13_2_0_negated_goal_bmc_11.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_20_0_0_to_17_2_1_negated_goal_bmc_10.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_20_2_0_to_8_7_7_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_21_0_4_to_10_10_5_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_21_1_2_to_14_3_7_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_21_1_2_to_14_3_7_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_21_4_1_to_0_23_3_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_22_0_2_to_9_12_3_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_23_1_0_to_8_9_7_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_0_11_to_11_1_1_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_0_19_to_2_8_11_negated_goal_bmc_11.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_0_5_to_2_1_4_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_0_5_to_2_1_4_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_0_7_to_1_1_7_negated_goal_bmc_12.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_12_9_to_0_10_13_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_1_11_to_9_3_2_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_1_3_to_6_0_0_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_1_9_to_0_9_3_negated_goal_bmc_9.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_2_14_to_14_4_0_negated_goal_bmc_10.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_4_0_to_0_3_3_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_5_13_to_12_7_1_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_2_6_2_to_3_4_3_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_3_0_3_to_1_2_3_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_3_1_18_to_3_16_3_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_3_1_20_to_23_0_1_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_3_4_6_to_1_9_3_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_3_5_0_to_8_0_0_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_3_5_10_to_17_0_1_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_0_5_to_8_0_1_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_0_5_to_8_0_1_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_10_4_to_15_0_3_negated_goal_bmc_13.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_10_4_to_15_0_3_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_19_1_to_0_8_16_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_19_1_to_0_8_16_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_1_4_to_1_0_8_negated_goal_bmc_11.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_2_4_to_3_2_5_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_3_0_to_5_1_1_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_4_3_to_4_3_4_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_0_0_to_5_0_0_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_0_1_to_1_1_4_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_0_1_to_1_1_4_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_0_8_to_7_5_1_negated_goal_bmc_12.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_0_8_to_7_5_1_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_1_10_to_4_9_3_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_1_10_to_4_9_3_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_21_0_to_20_6_0_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_21_0_to_20_6_0_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_21_0_to_20_6_0_negated_goal_bmc_9.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_2_3_to_9_0_1_negated_goal_bmc_10.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_2_3_to_9_0_1_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_3_8_to_14_1_1_negated_goal_bmc_10.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_4_17_to_12_6_8_negated_goal_bmc_13.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_4_17_to_12_6_8_negated_goal_bmc_16.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_4_17_to_12_6_8_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_5_0_to_10_0_0_negated_goal_bmc_13.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_5_0_to_7_0_3_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_7_12_to_9_3_12_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_7_12_to_9_3_12_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_9_3_to_13_1_3_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_5_9_3_to_13_1_3_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_0_0_to_3_2_1_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_1_0_to_7_0_0_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_1_11_to_6_0_12_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_1_11_to_6_0_12_negated_goal_bmc_10.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_1_1_to_1_5_2_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_1_1_to_4_2_2_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_20_0_to_1_12_13_negated_goal_bmc_11.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_20_0_to_1_12_13_negated_goal_bmc_12.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_2_14_to_12_6_4_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_2_1_to_9_0_0_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_3_5_to_9_4_1_negated_goal_bmc_10.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_9_0_to_14_0_1_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_9_0_to_14_0_1_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_2_0_to_7_0_2_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_7.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_9.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_3_1_to_5_6_0_negated_goal_bmc_13.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_3_1_to_5_6_0_negated_goal_bmc_9.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_4_13_to_4_14_6_negated_goal_bmc_15.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_4_13_to_4_14_6_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_7_4_13_to_4_14_6_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_10_1_to_5_9_5_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_10_1_to_5_9_5_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_1_2_to_6_2_3_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_2_1_to_10_1_0_negated_goal_bmc_11.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_2_1_to_10_1_0_negated_goal_bmc_8.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_6_1_to_8_1_6_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_6_9_to_13_1_9_negated_goal_bmc_12.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_8_1_to_9_4_4_negated_goal_bmc_2.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_8_1_to_9_4_4_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_8_8_1_to_9_4_4_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_9_0_3_to_11_0_1_negated_goal_bmc_5.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_9_10_3_to_1_0_21_negated_goal_bmc_14.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_9_4_1_to_0_13_1_negated_goal_bmc_11.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_9_4_4_to_14_1_2_negated_goal_bmc_3.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_9_7_0_to_9_6_1_negated_goal_bmc_9.smt2` | unsat | sat | timeout | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_9_9_2_to_12_5_3_negated_goal_bmc_1.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_9_9_2_to_12_5_3_negated_goal_bmc_4.smt2` | unsat | sat | unsat | - |
| `QF_DT/20230720-blocksworld/blocksworld_from_9_9_2_to_12_5_3_negated_goal_bmc_6.smt2` | unsat | sat | unsat | - |
| `QF_LIA/calypto/problem-001542.cvc.1.smt2` | unsat | sat | unsat | - |
| `QF_LIA/calypto/problem-001553.cvc.1.smt2` | unsat | sat | unsat | - |
| `QF_LRA/keymaera/simple_example_2-node2074.smt2` | unsat | sat | unsat | - |
| `QF_LRA/keymaera/simple_example_2-node2406.smt2` | unsat | sat | unsat | - |
| `QF_S/20230329-automatark-lu/instance09174.smt2` | unsat | sat | unsat | - |
| `QF_S/20230329-automatark-lu/instance10773.smt2` | sat | unsat | sat | - |
| `QF_SLIA/20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_370.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_458.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance45200.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance45227.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance45785.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance46026.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance46836.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance47584.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance48039.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance48102.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance48454.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance48730.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance49393.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance50454.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance50525.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance50706.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance50900.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance51681.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance51784.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance52132.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance52173.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance52209.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance52910.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance54389.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance54856.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance55060.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance55189.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance55497.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance55750.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance55946.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance56119.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance56382.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance56567.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance56674.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance57114.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance57574.smt2` | unknown | sat | unsat | - |
| `QF_SLIA/20230329-denghang/instance57679.smt2` | unknown | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-05-08-4-2-5-4.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-05-12-1-4-2-1.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-05-16-1-5-4-3.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-05-20-5-1-4-2.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-06-15-4-1-4-1.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-06-19-3-3-4-4.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-07-10-2-4-5-3.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-07-14-1-1-1-1.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/mathsat/Wisa/xs-07-18-1-1-4-1.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/wisas/xs_6_11.smt2` | unsat | sat | unsat | - |
| `QF_UFLIA/wisas/xs_8_13.smt2` | unsat | sat | unsat | - |

## Perf tail

### timeout+oom by logic

| logic | timeout | oom | timeout+oom | total |
| --- | ---: | ---: | ---: | ---: |
| QF_ABV | 361 | 98 | 459 | 15148 |
| QF_AUFBV | 19 | 6 | 25 | 75 |
| QF_AX | 0 | 0 | 0 | 551 |
| QF_BV | 5351 | 3597 | 8948 | 46191 |
| QF_BVFP | 215 | 0 | 215 | 17249 |
| QF_DT | 507 | 0 | 507 | 8700 |
| QF_FP | 173 | 15 | 188 | 40407 |
| QF_LIA | 3174 | 576 | 3750 | 13306 |
| QF_LRA | 181 | 2 | 183 | 1753 |
| QF_S | 8 | 0 | 8 | 18940 |
| QF_SLIA | 41 | 0 | 41 | 84395 |
| QF_UF | 363 | 0 | 363 | 7503 |
| QF_UFBV | 141 | 80 | 221 | 1510 |
| QF_UFLIA | 523 | 5 | 528 | 659 |
| QF_UFLRA | 1 | 10 | 11 | 1284 |
| all | 11058 | 4389 | 15447 | 257671 |

### timeout+oom by size decile

| decile | bytes | rows | timeout+oom |
| ---: | --- | ---: | ---: |
| 1 | 240–859 | 25767 | 300 |
| 2 | 859–993 | 25767 | 24 |
| 3 | 993–1300 | 25767 | 47 |
| 4 | 1300–1498 | 25767 | 39 |
| 5 | 1498–2347 | 25767 | 107 |
| 6 | 2347–5009 | 25767 | 258 |
| 7 | 5009–14122 | 25767 | 921 |
| 8 | 14123–33653 | 25767 | 1492 |
| 9 | 33654–99988 | 25767 | 2431 |
| 10 | 99988–2044326719 | 25768 | 9828 |

### 20 slowest correct instances per logic

#### QF_ABV

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_ABV/ecc/com.galois.ecc.P384ECC64.ec_mul_init4.short.smt2` | 17922 | 169777 |
| `QF_ABV/ecc/com.galois.ecc.P384ECC64.ec_mul_init3.short.smt2` | 17577 | 169781 |
| `QF_ABV/platania/no_init_multi_member/no_init_multi_member3.smt2` | 16558 | 19996 |
| `QF_ABV/dwp_formulas/try3_sameret_functions_dwp_mkfifo.mode_adjust.il.dwp.smt2` | 15258 | 73555 |
| `QF_ABV/dwp_formulas/try3_sameret_functions_dwp_ptx.peek_token_bracket.il.dwp.smt2` | 15193 | 81386 |
| `QF_ABV/dwp_formulas/try3_sameret_functions_dwp_mkdir.mode_adjust.il.dwp.smt2` | 14725 | 73570 |
| `QF_ABV/dwp_formulas/try3_sameret_functions_dwp_mknod.mode_adjust.il.dwp.smt2` | 14638 | 73570 |
| `QF_ABV/dwp_formulas/try3_sameret_functions_dwp_nl.peek_token_bracket.il.dwp.smt2` | 14465 | 81348 |
| `QF_ABV/platania/no_init_multi_member/no_init_multi_member4.smt2` | 14340 | 32647 |
| `QF_ABV/platania/strcmp/strcmp47.c.smt2` | 14044 | 31910 |
| `QF_ABV/platania/strcmp/strcmp37.c.smt2` | 13763 | 25230 |
| `QF_ABV/dwp_formulas/try3_sameret_functions_dwp_tac.peek_token_bracket.il.dwp.smt2` | 13089 | 80934 |
| `QF_ABV/dwp_formulas/try3_sameret_functions_dwp_csplit.peek_token_bracket.il.dwp.smt2` | 12957 | 81386 |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_vdir.strmode.il.dwp.smt2` | 12836 | 103230 |
| `QF_ABV/dwp_formulas/try3_sameret_functions_dwp_expr.peek_token_bracket.il.dwp.smt2` | 12779 | 81348 |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_tsort.scan_zeros.il.dwp.smt2` | 12250 | 12409 |
| `QF_ABV/platania/prim/Prim_7.c.smt2` | 11307 | 1457898 |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_stat.strmode.il.dwp.smt2` | 10572 | 102400 |
| `QF_ABV/ecc/com.galois.ecc.P384ECC64.ec_mul_init2.short.smt2` | 10408 | 169373 |
| `QF_ABV/dwp_formulas/try5_small_difret_functions_dwp_mv.strmode.il.dwp.smt2` | 9856 | 103230 |

#### QF_AUFBV

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_AUFBV/20210301-Alive2/gzip/250_gzip.smt2` | 1163 | 20008 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_twin_mul_aux12.short.smt2` | 783 | 99908 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_twin_mul_aux1.short.smt2` | 648 | 100340 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_twin_mul_aux11.short.smt2` | 634 | 100196 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_mul_aux4.short.smt2` | 483 | 300047 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_mul_aux3.short.smt2` | 466 | 300071 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_mul_aux2.short.smt2` | 365 | 300083 |
| `QF_AUFBV/2019-Gonzalvez/opStructure_NPT_2.smt2` | 223 | 13319 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_full_add4.short.smt2` | 195 | 31336 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.mul_inner4.short.smt2` | 152 | 7737 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_full_add2.short.smt2` | 144 | 27029 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.mul_inner3.short.smt2` | 138 | 10408 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.mod_div10.short.smt2` | 131 | 20160 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.sq_inner22.short.smt2` | 127 | 6199 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.sq_inner23.short.smt2` | 96 | 4154 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.ec_full_add1.short.smt2` | 60 | 14552 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.sq_inner12.short.smt2` | 39 | 5681 |
| `QF_AUFBV/ecc/com.galois.ecc.P384ECC64.sq_inner13.short.smt2` | 22 | 3340 |

#### QF_AX

_none_

#### QF_BV

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_BV/Sage2/bench_17197.smt2` | 19988 | 1018065 |
| `QF_BV/Sage2/bench_2178.smt2` | 19986 | 19174 |
| `QF_BV/asp/Hanoi/mgs_towers-hanoi.30_7.smt2` | 19919 | 1796150 |
| `QF_BV/asp/MazeGeneration/maze-generation-width=15-height=15-density=0.01-run=1.smt2` | 19909 | 347625 |
| `QF_BV/Sage2/bench_2879.smt2` | 19901 | 359647 |
| `QF_BV/Sage2/bench_15034.smt2` | 19897 | 168267 |
| `QF_BV/Sage2/bench_7397.smt2` | 19883 | 568810 |
| `QF_BV/20190311-bv-term-small-rw-Noetzli/bv-term-small-rw_1245.smt2` | 19869 | 744 |
| `QF_BV/Sage2/bench_14706.smt2` | 19849 | 361943 |
| `QF_BV/Sage2/bench_6691.smt2` | 19832 | 19128 |
| `QF_BV/Sage2/bench_2699.smt2` | 19768 | 16651 |
| `QF_BV/Sage2/bench_1638.smt2` | 19767 | 17355 |
| `QF_BV/Sage2/bench_1581.smt2` | 19690 | 551656 |
| `QF_BV/Sage2/bench_7094.smt2` | 19655 | 15674 |
| `QF_BV/Sage2/bench_1250.smt2` | 19641 | 23471 |
| `QF_BV/Sage2/bench_11956.smt2` | 19608 | 548662 |
| `QF_BV/Sage2/bench_3312.smt2` | 19605 | 102669 |
| `QF_BV/bruttomesso/core/ext_con_060_016_0064.smt2` | 19592 | 160436 |
| `QF_BV/Sage2/bench_8169.smt2` | 19576 | 691312 |
| `QF_BV/bruttomesso/core/ext_con_056_002_0256.smt2` | 19535 | 21582 |

#### QF_BVFP

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_BVFP/20170428-Liew-KLEE/aachen_real_wxpro_tostr.x86_64/query.39.smt2` | 19816 | 2219 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_real_wxpro_tostr.x86_64/query.40.smt2` | 19274 | 2250 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_real_numerical_recipes_gaussj.x86_64/query.20.smt2` | 19040 | 3048 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_syn_inf_float.x86_64/query.32.smt2` | 18705 | 1318 |
| `QF_BVFP/20190429-UltimateAutomizerSvcomp2019/double_req_bl_0270a_true-unreach-call.c_1.smt2` | 18393 | 5487 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_syn_inf_float.x86_64/query.28.smt2` | 18341 | 1252 |
| `QF_BVFP/20170428-Liew-KLEE/imperial_synthetic_sqrt_klee_bug.x86_64/query.15.smt2` | 18180 | 3915 |
| `QF_BVFP/20190429-UltimateAutomizerSvcomp2019/float_req_bl_0250b_true-unreach-call.c_3.smt2` | 18175 | 4433 |
| `QF_BVFP/20190429-UltimateAutomizerSvcomp2019/float_req_bl_0250b_true-unreach-call.c_0.smt2` | 18061 | 5425 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_real_gmp_gmp_klee_mpqload.x86_64/query.121.smt2` | 16693 | 2303 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_syn_inf_double.x86_64/query.28.smt2` | 16001 | 1164 |
| `QF_BVFP/20170428-Liew-KLEE/imperial_svcomp_float-benchs_svcomp_sqrt_householder_interval.x86_64/query.6.smt2` | 15984 | 2423 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_syn_inf_float.x86_64/query.33.smt2` | 15632 | 1341 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_syn_inf_double.x86_64/query.22.smt2` | 15592 | 1085 |
| `QF_BVFP/20170428-Liew-KLEE/imperial_svcomp_float-benchs_svcomp_filter1.x86_64/query.06.smt2` | 15462 | 1950 |
| `QF_BVFP/20170428-Liew-KLEE/imperial_svcomp_float-benchs_svcomp_rlim_invariant.x86_64/query.547.smt2` | 15335 | 12341 |
| `QF_BVFP/20170428-Liew-KLEE/imperial_svcomp_float-benchs_svcomp_rlim_invariant.x86_64/query.574.smt2` | 14896 | 10566 |
| `QF_BVFP/20170428-Liew-KLEE/imperial_svcomp_float-benchs_svcomp_rlim_invariant.x86_64/query.465.smt2` | 14673 | 9539 |
| `QF_BVFP/20170428-Liew-KLEE/aachen_syn_inf_double.x86_64/query.29.smt2` | 14025 | 1213 |
| `QF_BVFP/20170428-Liew-KLEE/imperial_svcomp_float-benchs_svcomp_rlim_invariant.x86_64/query.497.smt2` | 13302 | 11818 |

#### QF_DT

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_0_8_to_1_3_4_negated_goal_bmc_9.smt2` | 8331 | 35968 |
| `QF_DT/20230720-blocksworld/blocksworld_from_3_5_0_to_8_0_0_negated_goal_bmc_14.smt2` | 4368 | 56634 |
| `QF_DT/20230720-blocksworld/blocksworld_from_4_0_1_to_1_1_3_negated_goal_bmc_7.smt2` | 1891 | 28000 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l50016.cvc.smt2` | 1691 | 41689723 |
| `QF_DT/20230720-blocksworld/blocksworld_from_3_0_0_to_1_1_1_negated_goal_bmc_4.smt2` | 146 | 16651 |
| `QF_DT/20230720-blocksworld/blocksworld_from_0_2_0_to_2_0_0_negated_goal_bmc_3.smt2` | 82 | 12951 |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_2_1_to_1_3_0_negated_goal_bmc_3.smt2` | 63 | 13350 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60098.cvc.smt2` | 59 | 1170564 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90037.cvc.smt2` | 53 | 1439 |
| `QF_DT/20230720-blocksworld/blocksworld_from_1_0_1_to_0_1_1_negated_goal_bmc_3.smt2` | 48 | 13066 |
| `QF_DT/20230720-blocksworld/blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` | 47 | 9814 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l70006.cvc.smt2` | 46 | 699761 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l30050.cvc.smt2` | 42 | 381995 |
| `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l60099.cvc.smt2` | 37 | 1310 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l70100.cvc.smt2` | 35 | 8273 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l70024.cvc.smt2` | 35 | 4738 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60059.cvc.smt2` | 34 | 698379 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v1/typed_v1l80037.cvc.smt2` | 34 | 6384 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v2/typed_v2l60081.cvc.smt2` | 34 | 1268 |
| `QF_DT/20172804-Barrett/barrett-jsat/typed/v3/typed_v3l80037.cvc.smt2` | 34 | 1663 |

#### QF_FP

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_FP/griggio/fmcad12/test_v3_r3_vr10_c1_s29304.smt2` | 19023 | 4106 |
| `QF_FP/griggio/fmcad12/test_v3_r3_vr1_c1_s5578.smt2` | 16603 | 4108 |
| `QF_FP/griggio/fmcad12/test_v3_r8_vr1_c1_s23752.smt2` | 15382 | 8455 |
| `QF_FP/20190429-UltimateAutomizerSvcomp2019/double_req_bl_0876_true-unreach-call.c_0.smt2` | 14820 | 5988 |
| `QF_FP/20170501-Heizmann-UltimateAutomizer/water_pid_true-unreach-call.c_14.smt2` | 13899 | 3570 |
| `QF_FP/griggio/fmcad12/sine.1.0.i.smt2` | 13234 | 2505 |
| `QF_FP/griggio/fmcad12/sin2.c.2.smt2` | 10455 | 5245 |
| `QF_FP/griggio/fmcad12/sqrt.c.2.smt2` | 10118 | 5073 |
| `QF_FP/20190429-UltimateAutomizerSvcomp2019/double_req_bl_0240a_true-unreach-call.c_5.smt2` | 10089 | 3113 |
| `QF_FP/20190429-UltimateAutomizerSvcomp2019/double_req_bl_0240a_true-unreach-call.c_7.smt2` | 9873 | 3066 |
| `QF_FP/griggio/fmcad12/test_v3_r3_vr1_c1_s10392.smt2` | 7948 | 4106 |
| `QF_FP/griggio/fmcad12/test_v3_r3_vr5_c1_s16641.smt2` | 6093 | 4106 |
| `QF_FP/griggio/fmcad12/test_v3_r3_vr10_c1_s14052.smt2` | 5889 | 4106 |
| `QF_FP/ramalho/esbmc/Float8-main.smt2` | 4972 | 1202 |
| `QF_FP/ramalho/esbmc/Float_div-main.smt2` | 4522 | 121458 |
| `QF_FP/griggio/fmcad12/div3.c.50.smt2` | 3332 | 18801 |
| `QF_FP/griggio/fmcad12/div.c.40.smt2` | 3320 | 15160 |
| `QF_FP/griggio/fmcad12/div3.c.40.smt2` | 2570 | 15120 |
| `QF_FP/schanda/spark/shapes.smt2` | 2554 | 1521 |
| `QF_FP/20190429-UltimateAutomizerSvcomp2019/double_req_bl_0882_true-unreach-call.c_0.smt2` | 2173 | 5976 |

#### QF_LIA

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_LIA/20220307-SMPT/SharedMemory-PT-000200/RF-04.smt2` | 19759 | 22201054 |
| `QF_LIA/20220307-SMPT/SharedMemory-PT-000010/RC-13.smt2` | 19758 | 34880 |
| `QF_LIA/20220307-SMPT/Referendum-PT-0100/RC-15.smt2` | 19751 | 37828 |
| `QF_LIA/20220307-SMPT/SharedMemory-PT-000200/RF-05.smt2` | 19650 | 19063346 |
| `QF_LIA/20220307-SMPT/SharedMemory-PT-000200/RF-00.smt2` | 19549 | 19156295 |
| `QF_LIA/20220307-SMPT/RwMutex-PT-r0010w0020/RC-04.smt2` | 19548 | 22469 |
| `QF_LIA/mathsat/FISCHER10-8-fair.smt2` | 19540 | 328760 |
| `QF_LIA/20220307-SMPT/RwMutex-PT-r0010w0020/RF-15.smt2` | 19486 | 22467 |
| `QF_LIA/20220307-SMPT/SharedMemory-PT-000010/RF-14.smt2` | 19453 | 34988 |
| `QF_LIA/20220307-SMPT/Referendum-PT-0100/RC-12.smt2` | 19423 | 37767 |
| `QF_LIA/mathsat/FISCHER8-9-fair.smt2` | 19413 | 291981 |
| `QF_LIA/calypto/problem-006045.cvc.1.smt2` | 19302 | 4012 |
| `QF_LIA/20220307-SMPT/IOTPpurchase-PT-C01M01P01D01/RC-02.smt2` | 19183 | 17806 |
| `QF_LIA/20220307-SMPT/Referendum-PT-0100/RC-08.smt2` | 19179 | 37746 |
| `QF_LIA/20220307-SMPT/Referendum-PT-0100/RC-00.smt2` | 19155 | 37751 |
| `QF_LIA/20220307-SMPT/RwMutex-PT-r0010w0020/RF-10.smt2` | 19109 | 22473 |
| `QF_LIA/mathsat/FISCHER6-10-fair.smt2` | 19108 | 240004 |
| `QF_LIA/20220307-SMPT/RwMutex-PT-r0010w0020/RC-03.smt2` | 19106 | 22474 |
| `QF_LIA/20220307-SMPT/RwMutex-PT-r0010w0020/RF-07.smt2` | 19015 | 22473 |
| `QF_LIA/20220307-SMPT/SharedMemory-PT-000200/RC-06.smt2` | 18867 | 15006663 |

#### QF_LRA

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_LRA/2019-ezsmt/blending/13.smt2` | 18881 | 47217 |
| `QF_LRA/sc/sc-8.base.cvc.smt2` | 16402 | 17701 |
| `QF_LRA/TM/p-0-bucket_s10.smt2` | 16205 | 120888 |
| `QF_LRA/clock_synchro/clocksynchro_2clocks.worst_case_skew.induct.smt2` | 14741 | 4671 |
| `QF_LRA/sc/sc-12.induction2.cvc.smt2` | 13769 | 30580 |
| `QF_LRA/TM/p2-driverlogNumeric_s10.smt2` | 13228 | 354860 |
| `QF_LRA/2019-ezsmt/blending/9.smt2` | 13154 | 47247 |
| `QF_LRA/2019-ezsmt/blending/1.smt2` | 13146 | 47241 |
| `QF_LRA/DTP-Scheduling/constraints-tempo-matrix7x7.pddl.smt2` | 12344 | 251784 |
| `QF_LRA/sc/sc-11.induction2.cvc.smt2` | 11279 | 28060 |
| `QF_LRA/2019-ezsmt/blending/8.smt2` | 10857 | 47259 |
| `QF_LRA/2019-ezsmt/blending/5.smt2` | 10789 | 47235 |
| `QF_LRA/2019-ezsmt/blending/16.smt2` | 10521 | 47235 |
| `QF_LRA/sc/sc-14.induction.cvc.smt2` | 10493 | 30500 |
| `QF_LRA/sc/sc-7.base.cvc.smt2` | 10164 | 15567 |
| `QF_LRA/2019-ezsmt/blending/3.smt2` | 8858 | 47247 |
| `QF_LRA/sc/sc-15.induction.cvc.smt2` | 7826 | 32653 |
| `QF_LRA/sc/sc-10.induction2.cvc.smt2` | 7417 | 25563 |
| `QF_LRA/2019-ezsmt/blending/14.smt2` | 7130 | 47229 |
| `QF_LRA/sc/sc-12.induction.cvc.smt2` | 6997 | 26196 |

#### QF_S

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_S/20230329-automatark-lu/instance10357.smt2` | 13913 | 4552 |
| `QF_S/20230329-automatark-lu/instance09611.smt2` | 12200 | 2127 |
| `QF_S/20230329-automatark-lu/instance07868.smt2` | 10163 | 1809 |
| `QF_S/20230329-automatark-lu/instance09796.smt2` | 7997 | 2297 |
| `QF_S/20230329-automatark-lu/instance02667.smt2` | 7942 | 2502 |
| `QF_S/20230329-automatark-lu/instance04969.smt2` | 7511 | 3413 |
| `QF_S/20230329-automatark-lu/instance08690.smt2` | 6514 | 1909 |
| `QF_S/20230329-automatark-lu/instance09775.smt2` | 4698 | 1795 |
| `QF_S/20230329-automatark-lu/instance10269.smt2` | 4539 | 3072 |
| `QF_S/20230329-automatark-lu/instance05276.smt2` | 4322 | 2203 |
| `QF_S/20230329-automatark-lu/instance08356.smt2` | 3858 | 2787 |
| `QF_S/20230329-automatark-lu/instance09077.smt2` | 3300 | 5836 |
| `QF_S/20230329-automatark-lu/instance12154.smt2` | 2679 | 5808 |
| `QF_S/20230329-automatark-lu/instance00825.smt2` | 2642 | 1695 |
| `QF_S/20230329-automatark-lu/instance11542.smt2` | 2536 | 3258 |
| `QF_S/20230329-automatark-lu/instance06032.smt2` | 2048 | 4280 |
| `QF_S/20230329-automatark-lu/instance09590.smt2` | 1942 | 2785 |
| `QF_S/20230329-automatark-lu/instance12089.smt2` | 1926 | 4112 |
| `QF_S/20230329-automatark-lu/instance10223.smt2` | 1761 | 1794 |
| `QF_S/20230329-automatark-lu/instance14525.smt2` | 1723 | 6308 |

#### QF_SLIA

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_SLIA/20230329-denghang/instance41232.smt2` | 10240 | 1236 |
| `QF_SLIA/20230329-denghang/instance48481.smt2` | 7222 | 2264 |
| `QF_SLIA/20230329-denghang/instance52636.smt2` | 3754 | 3198 |
| `QF_SLIA/20230329-denghang/instance48810.smt2` | 3472 | 1814 |
| `QF_SLIA/20230329-denghang/instance54650.smt2` | 2998 | 2217 |
| `QF_SLIA/20230329-denghang/instance56659.smt2` | 2188 | 2132 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00031-7.smt2` | 1950 | 4362 |
| `QF_SLIA/20230329-denghang/instance53843.smt2` | 1704 | 1514 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00036-9.smt2` | 1644 | 4542 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00031-14.smt2` | 1441 | 4213 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00026-14.smt2` | 1357 | 3762 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00031-26.smt2` | 1294 | 4323 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00031-11.smt2` | 1291 | 4441 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00031-16.smt2` | 1283 | 4327 |
| `QF_SLIA/20230329-denghang/instance58430.smt2` | 1238 | 2228 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00031-18.smt2` | 1235 | 4448 |
| `QF_SLIA/20230329-denghang/instance50680.smt2` | 1197 | 2675 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00031-13.smt2` | 1148 | 4316 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexsmall/regex-small-00039-7.smt2` | 1115 | 2772 |
| `QF_SLIA/20230327-stringfuzz-lu/generated/regexpair/regex-pair-00031-20.smt2` | 1113 | 4218 |

#### QF_UF

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_UF/QG-classification/qg5/gensys_brn875.smt2` | 19870 | 37504 |
| `QF_UF/NEQ/NEQ048_size6.smt2` | 19800 | 31423 |
| `QF_UF/QG-classification/qg5/gensys_icl088.smt2` | 19744 | 46353 |
| `QF_UF/QG-classification/qg5/gensys_icl828.smt2` | 19662 | 54581 |
| `QF_UF/QG-classification/qg5/gensys_icl586.smt2` | 19540 | 52848 |
| `QF_UF/QG-classification/qg7/gensys_icl_sk005.smt2` | 19479 | 811092 |
| `QF_UF/QG-classification/qg5/gensys_icl987.smt2` | 19439 | 39995 |
| `QF_UF/2018-Goel-hwbench/QF_UF_rushhour.2.prop1_ab_br_max.smt2` | 19366 | 1218044 |
| `QF_UF/SEQ/SEQ038_size9.smt2` | 19188 | 94413 |
| `QF_UF/QG-classification/qg5/gensys_icl807.smt2` | 19136 | 46565 |
| `QF_UF/2018-Goel-hwbench/QF_UF_sokoban.3.prop1_ab_br_max.smt2` | 19070 | 1391629 |
| `QF_UF/QG-classification/qg5/gensys_icl152.smt2` | 18950 | 38688 |
| `QF_UF/QG-classification/qg5/gensys_icl806.smt2` | 18727 | 46731 |
| `QF_UF/QG-classification/qg5/gensys_icl533.smt2` | 18642 | 52687 |
| `QF_UF/QG-classification/qg5/gensys_icl694.smt2` | 18322 | 43631 |
| `QF_UF/QG-classification/qg5/gensys_icl829.smt2` | 18162 | 55487 |
| `QF_UF/QG-classification/qg5/gensys_brn752.smt2` | 18067 | 42273 |
| `QF_UF/QG-classification/qg5/gensys_icl664.smt2` | 18027 | 48725 |
| `QF_UF/QG-classification/qg5/gensys_icl776.smt2` | 17980 | 39943 |
| `QF_UF/QG-classification/qg5/gensys_icl690.smt2` | 17970 | 40921 |

#### QF_UFBV

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_UFBV/20210312-Bouvier/vlsat3_j79.smt2` | 18879 | 383408 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j88.smt2` | 17267 | 319304 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j68.smt2` | 16761 | 245966 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j70.smt2` | 16592 | 816070 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j93.smt2` | 15667 | 1258438 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j01.smt2` | 14757 | 95579 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j69.smt2` | 14232 | 275695 |
| `QF_UFBV/20210312-Bouvier/vlsat3_d46.smt2` | 10770 | 26844 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j80.smt2` | 10685 | 587560 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j06.smt2` | 9975 | 965735 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j05.smt2` | 9685 | 440996 |
| `QF_UFBV/20210312-Bouvier/vlsat3_d57.smt2` | 9121 | 9861 |
| `QF_UFBV/2018-Goel-hwbench/QF_UFBV_bv_bv_sokoban.3.prop1_ab_cti_max.smt2` | 6891 | 1141417 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j84.smt2` | 6837 | 895352 |
| `QF_UFBV/2018-Goel-hwbench/QF_UFBV_bv_bv_sokoban.3.prop1_ab_reg_max.smt2` | 6538 | 1163933 |
| `QF_UFBV/20210312-Bouvier/vlsat3_j78.smt2` | 6519 | 452478 |
| `QF_UFBV/2018-Goel-hwbench/QF_UFBV_bv_bv_rushhour.4.prop1_ab_cti_max.smt2` | 4066 | 1493298 |
| `QF_UFBV/2018-Goel-hwbench/QF_UFBV_bv_bv_rushhour.3.prop1_ab_cti_max.smt2` | 4025 | 1440128 |
| `QF_UFBV/2018-Goel-hwbench/QF_UFBV_bv_bv_rushhour.4.prop1_ab_reg_max.smt2` | 3979 | 1435444 |
| `QF_UFBV/2018-Goel-hwbench/QF_UFBV_bv_bv_rushhour.3.prop1_ab_reg_max.smt2` | 3833 | 1435658 |

#### QF_UFLIA

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_UFLIA/mathsat/Hash/hash_uns_04_20.smt2` | 19059 | 12155 |
| `QF_UFLIA/mathsat/Hash/hash_uns_05_14.smt2` | 18796 | 12981 |
| `QF_UFLIA/mathsat/Hash/hash_sat_04_11.smt2` | 18779 | 6965 |
| `QF_UFLIA/mathsat/Hash/hash_sat_04_14.smt2` | 18496 | 8711 |
| `QF_UFLIA/mathsat/Hash/hash_uns_05_16.smt2` | 17573 | 14745 |
| `QF_UFLIA/mathsat/Hash/hash_uns_05_12.smt2` | 16415 | 11217 |
| `QF_UFLIA/mathsat/Hash/hash_sat_05_10.smt2` | 14975 | 9501 |
| `QF_UFLIA/mathsat/Hash/hash_uns_05_09.smt2` | 13846 | 8571 |
| `QF_UFLIA/mathsat/Hash/hash_sat_08_03.smt2` | 13830 | 7741 |
| `QF_UFLIA/mathsat/Hash/hash_uns_04_19.smt2` | 13498 | 11573 |
| `QF_UFLIA/mathsat/Wisa/xs-07-06-4-1-5-3.smt2` | 13196 | 4577 |
| `QF_UFLIA/mathsat/Hash/hash_uns_04_18.smt2` | 12938 | 10991 |
| `QF_UFLIA/mathsat/Hash/hash_sat_07_05.smt2` | 12538 | 9401 |
| `QF_UFLIA/mathsat/Hash/hash_sat_09_03.smt2` | 12171 | 9648 |
| `QF_UFLIA/mathsat/Hash/hash_sat_03_09.smt2` | 11897 | 3589 |
| `QF_UFLIA/mathsat/Wisa/xs-06-07-4-5-4-2.smt2` | 11732 | 4102 |
| `QF_UFLIA/mathsat/Hash/hash_sat_08_04.smt2` | 11279 | 9904 |
| `QF_UFLIA/mathsat/Hash/hash_sat_07_04.smt2` | 10928 | 7732 |
| `QF_UFLIA/mathsat/Hash/hash_uns_05_11.smt2` | 10846 | 10335 |
| `QF_UFLIA/mathsat/Hash/hash_uns_04_16.smt2` | 10639 | 9827 |

#### QF_UFLRA

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.test_locks_14_false-unreach-call.c.smt2` | 10549 | 14443 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.test_locks_5_true-unreach-call_false-termination.c.smt2` | 3063 | 10933 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.1_3.c_false-unreach-call.i.smt2` | 220 | 4449 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.trex03_false-unreach-call_true-termination.i.smt2` | 101 | 3829 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.trex03_true-unreach-call.i.smt2` | 76 | 4121 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.alt_test.c_false-unreach-call.i.smt2` | 33 | 3863 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.fo_test.c_false-unreach-call.i.smt2` | 15 | 1982 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.mutex_lock_struct.c_false-unreach-call.i.smt2` | 7 | 1917 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.terminator_03_false-unreach-call_true-termination.i.smt2` | 7 | 1924 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--input--misc--pcap_keys.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 6 | 716 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--input--touchscreen--dynapro.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 6 | 1371 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.mutex_lock_int.c_false-unreach-call.i.smt2` | 6 | 1897 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--input--misc--ab8500-ponkey.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 5 | 710 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--input--misc--mpu3050.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 5 | 706 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--input--touchscreen--hampshire.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 5 | 1383 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--input--touchscreen--mtouch.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 5 | 1365 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--input--touchscreen--touchit213.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 5 | 1389 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--net--arcnet--rfc1051.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 5 | 877 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--rtc--rtc-ds1390.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2` | 5 | 696 |
| `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.while_infinite_loop_3_true-unreach-call_false-termination.i.smt2` | 4 | 458 |

