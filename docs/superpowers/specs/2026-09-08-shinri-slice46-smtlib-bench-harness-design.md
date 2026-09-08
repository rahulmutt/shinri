# Slice 46 — SMT-LIB benchmark harness and the 2024 baseline

**Status:** approved design, not yet implemented
**Date:** 2026-09-08
**Area:** new crate `shinri-bench` (workspace binary); `shinri-cli` gains a
`--stats` flag; `shinri-solver` records which `Unknown` fence fired; three new
mise tasks (`bench-fetch`, `bench-run`, `bench-report`); one new committed
manifest (`bench/manifest.toml`) and two git-ignored directories
(`bench/corpus/`, `bench/results/`). No solver-behaviour change, no new
dependency, no change to the blocking CI tier.
**Predecessors:** none — this is the first slice that measures shinri against
the official corpus. Slices 1–45 were each driven by hand-written probe
queries and the z3/cvc5 oracle generators; this slice replaces "what should we
build next?" guesswork with a ranked, reproducible gap list.

## 1. Summary

shinri claims ~15 quantifier-free logics but has never been run on the
official SMT-LIB benchmarks. Nothing in the repo fetches them, runs them under
resource limits, judges the answers, or summarises the result. This slice
builds that harness as a workspace binary, adds the one solver-side hook the
harness needs (a tag naming which fence produced an `unknown`), runs the full
QF corpus once at a fixed budget, and commits the resulting report as the
baseline that later slices cite and move.

Two things come out of the baseline:

1. **Missing feature sets** — parse failures, panics, and `unknown` answers,
   bucketed by cause and ranked by instance count per logic.
2. **Optimisation targets** — timeouts and OOMs by logic and instance size,
   and the slowest correctly-decided instances.

Any wrong answer found is a soundness bug and outranks both lists.

## 2. Scope and decisions taken

Decisions made during design (each was a question with alternatives; the
alternative is recorded so it is not re-litigated):

| Decision | Chosen | Rejected |
|---|---|---|
| Logic scope | every QF logic shinri claims: QF_BV, QF_ABV, QF_AUFBV, QF_UFBV, QF_FP, QF_BVFP, QF_LRA, QF_LIA, QF_UF, QF_UFLIA, QF_UFLRA, QF_AX, QF_S, QF_SLIA, QF_DT | bit-blasting stack only; strings+DT only; a sampled subset |
| Corpus source | harness fetches pinned archives from the SMT-LIB Zenodo release, resumable, checksummed | user-provided tree; GitLab clones |
| Adjudication | `:status` first; z3 then cvc5 only on demand (§5) | z3 on every instance; `:status` only |
| Budget | 20 s wall / 3 GB address space / 6 workers | 5 s fast triage; 60 s competition-like |
| Implementation | Rust workspace binary, zero runtime deps | Python scripts; in-process runner inside `shinri-cli` |

The budget is sized for the **pod's cgroup**, not the host: `cpu.max` is
`800000/100000` (8 cores of quota, 24 visible) and `memory.max` is 32 GiB.
Six workers at 3 GB is 18 GB peak, leaving room for the oracle and a build.

**Out of scope, deliberately:** fixing anything the baseline finds. A solver
change in this slice would contaminate the baseline it is meant to establish.
Every finding becomes its own slice, whose spec cites the baseline row it
moves and re-runs `bench-run` on the affected logic to show the delta.

Also out of scope: the incremental benchmark release (multiple `check-sat`
per script), quantified logics, model validation (`get-model` output is not
checked — a later slice can add a model-checking verdict), and any CI
integration of the full run.

## 3. Components

New crate `crates/shinri-bench`, binary `shinri-bench`, `[dependencies]`
intentionally empty like the rest of the workspace. It orchestrates system
tools — `curl`, `tar` (zstd), `timeout`, `prlimit`, `z3`, `cvc5` — via
`std::process`; the workspace's native-link ban is untouched and `deny.toml`
does not change.

```
crates/shinri-bench/src/
  main.rs        subcommands: fetch | run | rerun | report
  corpus.rs      manifest parsing; download / verify / extract; local layout
  instance.rs    one .smt2 file: logic, `:status` header scan, byte size
  runner.rs      6-worker pool; spawns the limited solver process; captures rc/stdout/stderr/wall
  oracle.rs      on-demand z3 → cvc5 adjudication at the same limit
  verdict.rs     `Verdict` enum and the pure classifier
  results.rs     JSONL append/read, resume, fixture line
  report.rs      Markdown summary and ranked gap tables
crates/shinri-bench/tests/
  corpus/        6-file mini-corpus + stub solver script (§7)
bench/
  manifest.toml  COMMITTED: Zenodo record, per-logic archive names, sha256, expected .smt2 counts
  corpus/        git-ignored: bench/corpus/<LOGIC>/… extracted trees; bench/corpus/.dl/ archives
  results/       git-ignored: bench/results/<run-id>/{results.jsonl,report.md}
```

`mise.toml` gains:

| Task | Runs |
|---|---|
| `bench-fetch` | `shinri-bench fetch` (all manifest logics, or `BENCH_LOGICS`) |
| `bench-run` | `shinri-bench run` with `BENCH_LOGICS`, `BENCH_TIMEOUT` (20), `BENCH_MEM_MB` (3072), `BENCH_JOBS` (6), `BENCH_RUN_ID` (default: UTC timestamp) |
| `bench-report` | `shinri-bench report bench/results/<run-id>` |

None of these are dependencies of the `ci` task.

### 3.1 The one solver-side hook: fence tags and `--stats`

`Solver::check_sat` (`crates/shinri-solver/src/lib.rs`) has twelve
`return SolveOutcome::Unknown` sites in the ~`764–918` range, each guarded by a
named predicate (`string_stage::fenced`, `has_unsupported_regex`,
`abv_stage::fenced`, `uf_args_supported`, `uf_congruence_cost`, …), plus the
SAT step-budget exhaustion. From the outside they are indistinguishable.

Change: each site sets `self.last_fence = Some("<tag>")` before returning,
where the tag is a short `&'static str` naming the predicate
(`str-fenced`, `str-regex-unsupported`, `abv-fenced`, `bv-uf-args`,
`bv-uf-budget`, `sat-step-budget`, …). `last_fence` is cleared at the top of
`check_sat` and is `None` on `Sat`/`Unsat`. `SolveOutcome` itself does not
change; no existing test can observe the difference. A public
`Solver::last_fence(&self) -> Option<&'static str>` exposes it.

`shinri-cli` gains `--stats`. After every `check-sat` response it writes one
line to **stderr**:

```
stats: cmd=check-sat wall_ms=<u64> outcome=<sat|unsat|unknown> fence=<tag|->
```

Stdout is byte-identical with and without the flag (asserted in `script_e2e`).
`wall_ms` is measured in the driver around `Solver::execute`, so it excludes
parse time — the harness's own wall clock covers the whole process.

## 4. Run pipeline

### 4.1 `fetch`

1. Parse `bench/manifest.toml` (hand-rolled reader: `[[archive]]` tables with
   `logic`, `url`, `sha256`, `smt2_count`).
2. For each archive not already marked verified: `curl -L --retry 5 -C -` into
   `bench/corpus/.dl/<name>`, then sha256 (own implementation, ~100 lines,
   unit-tested against the FIPS vectors). Mismatch → rename to `<name>.bad`,
   report, continue with the next archive, exit non-zero at the end. Never
   silently re-download a mismatch.
3. Extract with `tar --zstd -xf` into `bench/corpus/<LOGIC>/`; count `.smt2`
   files and compare with `smt2_count`. Mismatch is an error.
4. Write `bench/corpus/<LOGIC>/.verified` containing the archive sha256 so
   re-runs skip it.

`fetch --dry-run` validates the manifest and prints the URLs without network.

**Pinning rule:** the manifest pins the *SMT-LIB 2024 non-incremental release*
on Zenodo by record DOI, one archive per logic, with sha256 taken from the
Zenodo file metadata. Zenodo returned `504` from the pod during design, so the
real DOI and hashes are filled in by the implementation plan's first task, not
guessed here. If Zenodo stays unreachable the fallback is a user-supplied
mirror path (`BENCH_MIRROR=<dir-or-url>` substituted for the record base URL);
the checksums still apply.

### 4.2 `run`

1. Walk `bench/corpus/<LOGIC>/` for the selected logics; sort paths for
   determinism. Load `results.jsonl` for the run-id if present and **skip
   paths already recorded** — a killed run resumes.
2. If the results file exists, its fixture line must match the current
   fixture (shinri git sha, timeout, mem, jobs); otherwise refuse and tell the
   user to pick a new run-id. Timings from different fixtures are never merged.
3. Otherwise write the fixture line first: sha, `shinri --version`, limits,
   cgroup `cpu.max` and `memory.max` (read from `/sys/fs/cgroup`, `-` if
   absent), corpus release, start time (UTC).
4. Worker pool: `BENCH_JOBS` std threads consuming a channel of paths. Each
   spawns

   ```
   prlimit --as=<mem_bytes> timeout -s KILL <t+1> timeout <t> shinri --stats <file>
   ```

   with stdin closed, stdout and stderr piped and read on two threads (so a
   solver that floods one pipe cannot deadlock the other), wall time measured
   around the child. `timeout` at `t` sends TERM; the outer one KILLs at `t+1`.
5. Each result is appended as one JSONL row by a single writer thread and
   flushed; row schema in §4.4.
6. Progress line to the terminal every N rows: done/total, per-verdict counts.

### 4.3 `rerun`

`shinri-bench rerun <results.jsonl> --verdict <v>[,<v>…] --timeout <t> …`
selects rows by verdict from an existing run and runs just those paths into a
**new** run-id with the new fixture. This is the 60 s tier for timeouts, or a
targeted re-run after a fix, without re-walking the corpus.

### 4.4 Row schema

One JSON object per line, hand-serialised; all strings escaped per RFC 8259.

```
{"path":"QF_BV/sage/app1/bench_1.smt2","logic":"QF_BV","bytes":1234,
 "status":"unsat","rc":0,"wall_ms":812,"answers":["unsat"],
 "fence":null,"stderr_head":"","verdict":"correct",
 "oracle":null}
```

- `status`: `sat` / `unsat` / `unknown` / `null` (absent).
- `answers`: every `sat`/`unsat`/`unknown` line on stdout, in order.
- `fence`: the `--stats` tag for the last `check-sat`, or `null`.
- `stderr_head`: first 2 KiB of stderr, minus the `stats:` lines.
- `oracle`: `null` or `{"z3":"…","cvc5":"…"}` with each value
  `sat`/`unsat`/`unknown`/`timeout`; only present when consulted.
- `verdict`: §5, lower-case with the fence tag folded into `unknown:<tag>`.

The first line of the file is the fixture object: `{"fixture":{…}}`.

## 5. Adjudication and verdicts

`verdict::classify(rc, answers, stderr, status, oracle) -> Verdict` is a pure
function; the oracle is consulted by `runner` only when `classify` returns
`NeedsOracle` in a first pass, then `classify` is called again with the oracle
answers.

| Verdict | Trigger | Priority |
|---|---|---|
| `Wrong` | shinri decided and contradicts `:status`, and the oracle does not side with shinri; or shinri decided and contradicts the oracle where `:status` is absent | soundness — immediate slice |
| `StatusSuspect` | shinri contradicts `:status` but **both** z3 and cvc5 agree with shinri | reported, not counted against shinri |
| `ParseError` | an `(error …)` line on stdout before the first answer, or rc≠0 with a parser diagnostic on stderr | hard blocker |
| `Panic` | rc 101 or `panicked at` on stderr | hard blocker |
| `Oom` | `memory allocation of N bytes failed` on stderr (Rust abort under `prlimit --as`, rc 134), or rc 137 before `t` | perf |
| `Timeout` | killed by `timeout`: rc 124 (TERM at `t`) or rc 137 at/after `t+1` | perf |
| `Unknown(tag)` | one `unknown` answer; keyed by the `--stats` fence tag | feature gap |
| `Correct` | one decided answer equal to `:status`, or `:status` absent/`unknown` and z3 agrees | — |
| `Unverified` | decided, `:status` absent/`unknown`, z3 (and cvc5) timed out or answered `unknown` | flagged, **not** counted as correct |
| `Malformed` | `answers.len() ≠ 1` and none of the above, file unreadable, spawn failure, invalid UTF-8 output | excluded from rates |

**Oracle rule.** z3 is run at the same wall limit only when
(a) `:status` is absent/`unknown` and shinri decided, or
(b) shinri's answer contradicts `:status`.
In (b), if z3 agrees with shinri, cvc5 is run; only if both agree with shinri
is the row `StatusSuspect`. Every `Wrong` row therefore has at least one
independent solver on record, and the JSONL stores the oracle answers so the
list reproduces with `z3 <file>`. Oracle processes run under the same
`prlimit`/`timeout` wrapper and count against the worker's slot, so the
6-worker memory bound still holds.

Priority order for the baseline's "next slices" section is fixed:
`Wrong` > `Panic` > `ParseError` > `Unknown` (by count) > `Timeout`/`Oom`.

## 6. Report

`shinri-bench report <run-dir>` reads `results.jsonl` and writes `report.md`:

1. **Fixture header** — sha, version, limits, cgroup quota, corpus release,
   run start, rows total / per logic.
2. **Per-logic matrix** — rows = logics; columns = each verdict count,
   decided-rate (`Correct / (total − Malformed)`), median and p90 `wall_ms`
   over `Correct` rows.
3. **Ranked gap list** — every non-`Correct` verdict bucketed and sorted by
   count. `Unknown` is split per fence tag; `ParseError`/`Panic` are split by
   the **normalised** first diagnostic line: decimal/hex literals → `N`,
   quoted symbols → `S`, so `unknown symbol foo` and `unknown symbol bar`
   merge. Each bucket lists its per-logic split and three example paths
   (smallest by bytes — the cheapest reproducers).
4. **Wrong-answer table** — every `Wrong` and `StatusSuspect` row: path,
   `:status`, shinri, z3, cvc5. Empty table is printed explicitly.
5. **Perf tail** — `Timeout`+`Oom` by logic and by file-size decile; the 20
   slowest `Correct` instances per logic with wall time and bytes.

The per-logic matrix and every table are plain Markdown so the report reads
in `git diff` when a later slice's re-run is compared against the baseline.

### 6.1 The committed deliverable

After the first full run, `report.md` is copied to
`docs/superpowers/research/<date>-smtlib-2024-baseline.md` with a hand-written
section on top:

- the run-id, shinri sha, and the exact `bench-run` invocation;
- the top ~5 gaps in §5 priority order, each with the row it cites and a
  one-line proposed slice.

Raw JSONL stays git-ignored (size); the run-id + sha + manifest make it
reproducible.

## 7. Testing

**Blocking tier (all fast):**

- `verdict.rs` — table-driven tests, one per row of §5's table, plus: the
  oracle escalation to cvc5, `StatusSuspect` vs `Wrong`, two `check-sat`
  answers → `Malformed`, `unknown` with no fence tag → `Unknown("-")`.
- `instance.rs` — `:status` scan fixtures: present, absent, `unknown`,
  appearing after `check-sat`, CRLF line endings, inside a comment (ignored),
  `(set-info :status sat)` with extra whitespace.
- `results.rs` — JSONL round-trip of a row with `"`, `\n`, `\\` and non-ASCII
  in `path` and `stderr_head`; resume skips recorded paths; fixture mismatch
  refuses to append.
- `corpus.rs` — sha256 against the FIPS 180-4 vectors (`abc`, the 56-byte
  string, the million-`a` string); manifest parse of a fixture with a
  malformed entry.
- `report.rs` — golden `report.md` from a committed 30-row JSONL fixture that
  exercises every verdict; diagnostic normalisation cases; ranking is stable
  under row permutation.
- `shinri-cli` `script_e2e` — with `--stats`, stderr has exactly one
  `stats:` line per `check-sat` in the documented shape; a known-fenced query
  (a `str.<` over two free variables, slice 31) reports the expected tag; a
  decided query reports `fence=-`; stdout is byte-identical with and without
  the flag.
- `shinri-solver` — `last_fence()` is `None` after `Sat`/`Unsat` and `Some`
  after each of the twelve fences, using the smallest probe already in the
  test suite for each fence (existing tests, one extra assertion each).

**Integration (blocking tier, seconds):** `runner` end-to-end on
`crates/shinri-bench/tests/corpus/` — six files driven through a stub solver
script (`--solver <path>` override, so the test never depends on shinri's
answers): one sat, one unsat, one whose `:status` the stub contradicts, one
where the stub sleeps past the limit, one where the stub allocates past
`prlimit`, one where the stub exits 101 with `panicked at`. Asserts six rows
with the six expected verdicts and that the run finishes within `2·t`. Skips
with a printed reason if `prlimit` or `timeout` is not on PATH.

**Not in CI:** `fetch` (network) and the full run. `fetch --dry-run` is unit
tested.

## 8. Error handling

- A worker never aborts the run: spawn failure, unreadable file, invalid UTF-8
  → a `Malformed` row carrying the reason in `stderr_head`.
- `fetch` checksum mismatch → archive renamed `.bad`, loud message, non-zero
  exit after all archives are attempted.
- `run` with a fixture mismatch → refuse before spawning anything.
- Ctrl-C: the writer flushes the current row; the resume rule makes the
  partial file usable as-is.
- Report on a file with zero `Correct` rows for a logic prints `n/a` for the
  timing columns rather than dividing by zero.

## 9. Success criteria

1. `mise run bench-fetch && mise run bench-run` completes over the full QF
   manifest on the pod without operator intervention beyond restarting after
   a network failure (resume proves itself).
2. `docs/superpowers/research/<date>-smtlib-2024-baseline.md` is committed
   with a non-empty per-logic matrix for every manifest logic and a ranked
   gap list.
3. The `Wrong` table is either empty or every row is reproduced by hand with
   `z3`/`cvc5` and filed as a named follow-up slice in the doc.
4. `cargo nextest run -p shinri-bench` and the `script_e2e` additions pass on
   the blocking tier; `mise run ci` wall-clock is not measurably changed.
5. `shinri-cli` stdout is byte-identical with and without `--stats`.
