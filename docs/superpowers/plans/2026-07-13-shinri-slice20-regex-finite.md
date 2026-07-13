# Slice 20 — Symbolic str.in_re over Finite/Co-finite Constant Languages Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decide `str.in_re(t, R)` for ANY String-sorted term `t` and constant regex `R` whose language is structurally finite or co-finite, by rewriting the atom to a full equivalence over word equations (`⋁ t = wᵢ`, negated over the exception set for co-finite) — any polarity, zero engine changes; everything else keeps fencing to sound `Unknown`.

**Architecture:** Two cap-bounded enumerators over the existing private `Rex` AST in `crates/shinri-str/src/regex.rs` — `enum_lang` (words of a structurally finite language) and `enum_comp` (exception set of a structurally co-finite language) — feed a new symbolic fallback in the slice-19 rewrite pass: when the ground fold declines, the atom rewrites to a disjunction of string equalities (wrapped in `Not` for co-finite). The produced equalities/disequalities are word equations the existing engine already owns; the Boolean structure goes through Tseitin. Nothing else changes: same `lib.rs` seam, same presence fence, no parser/model/engine work.

**Tech Stack:** Rust workspace (only `crates/shinri-str` and `crates/shinri-solver/tests` change). Differential testing against z3 (installed via mise) behind `--features oracle`.

**Spec:** `docs/superpowers/specs/2026-07-13-shinri-slice20-regex-finite-design.md`.

## Global Constraints

- Every rewrite is a **full logical equivalence** at any polarity, any occurrence count. NO demotion flags, NO model repair, NO fresh variables.
- Enumeration fuel: `ENUM_WORD_CAP: usize = 256` (max cardinality of any intermediate word set) AND `ENUM_TOTAL_BYTES_CAP: usize = 4096` (max sum of word lengths of any intermediate set). Crossing either aborts → no rewrite → presence fence → sound `Unknown`.
- **Surrogate guard:** `enum_lang` returns `None` for any `Range` intersecting `0xD800..=0xDFFF` (SMT-LIB alphabet chars unrepresentable as Rust chars — enumerating would silently miss words).
- **Above-alphabet string side:** if `t` contains ANY literal character `> 0x2FFFF` (bare literal or inside a concat), the symbolic rewrite is skipped (→ fence) — slice-18/19 posture.
- `eval_membership` fuel exhaustion (`None`) inside an `Inter`/`Union` filter aborts the WHOLE enumeration — never guesses.
- The slice-19 ground fold runs FIRST; the symbolic fallback fires only when it declines.
- **ASCII-only differential scripts:** shinri's parser does not decode `\u{...}` escapes and z3 reads raw UTF-8 byte-wise. Scripts shared with z3 stay ASCII; non-ASCII coverage lives in unit tests and shinri-only `Unknown` pins.
- Never perturb existing differential-oracle families or their seeds. New family seed: `0x52_00_0000_0001`.
- `cargo fmt` before EVERY commit (CI hard-fails on `cargo fmt --check`; subagents do not auto-format).
- Run oracle tests FOREGROUND with captured output — never claim a tally you didn't see.
- Commit messages follow repo convention: `feat(str): … (slice 20)`, `test(str): … (slice 20)`, `docs: …`.
- Do NOT run `cargo test --workspace` locally (~50 min); test per-crate as instructed. CI runs the full workspace.
- No new dependencies (`std::collections::BTreeSet` is std).
- Branch `slice20-regex-finite` already exists with the spec committed — do NOT create a new branch; work on it.

---

### Task 1: Finite / co-finite language enumerators on `Rex`

Pure functions + caps, unit-tested, not yet called by the solver (transient `#[allow(dead_code)]`, removed in Task 2 — the slice-19 Task-2/Task-3 pattern).

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (new code after `eval_membership`/`lit_to_rex`, ~line 254; tests at the end of the existing `mod tests`)

**Interfaces:**
- Consumes (already in `regex.rs`): `enum Rex`, smart constructors `concat/union/inter/star/comp/loop_`, `nullable`, `eval_membership(s: &str, r: &Rex) -> Option<bool>`, `MAX_CODE: u32`, test helpers `chr`, `lit`.
- Produces (Task 2 depends on these EXACT names):
  - `type Words = std::collections::BTreeSet<String>;` (private)
  - `const ENUM_WORD_CAP: usize = 256;`
  - `const ENUM_TOTAL_BYTES_CAP: usize = 4096;`
  - `fn enum_lang(r: &Rex) -> Option<Words>`
  - `fn enum_comp(r: &Rex) -> Option<Words>`

- [ ] **Step 1: Write the failing tests**

Append inside `mod tests` in `crates/shinri-str/src/regex.rs` (after `untouched_subtrees_keep_their_termids`):

```rust
    // ── Task 1 (slice 20): finite / co-finite enumeration ────────────────

    fn words(xs: &[&str]) -> Words {
        xs.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn enum_lang_per_operator() {
        // Leaves.
        assert_eq!(enum_lang(&Rex::Empty), Some(words(&[])));
        assert_eq!(enum_lang(&Rex::Eps), Some(words(&[""])));
        assert_eq!(
            enum_lang(&Rex::Range('a' as u32, 'c' as u32)),
            Some(words(&["a", "b", "c"]))
        );
        // Concat: cross product.
        assert_eq!(
            enum_lang(&concat(vec![union(vec![lit("a"), lit("b")]), lit("x")])),
            Some(words(&["ax", "bx"]))
        );
        // Union: set union, deduped (BTreeSet order = determinism).
        assert_eq!(
            enum_lang(&union(vec![lit("b"), lit("a"), lit("b")])),
            Some(words(&["a", "b"]))
        );
        // Inter: filter the finite side through the other (comp!) sides.
        assert_eq!(
            enum_lang(&inter(vec![union(vec![lit("a"), lit("b")]), comp(lit("a"))])),
            Some(words(&["b"]))
        );
        // Loop: bounded powers, including the ε floor at lo = 0.
        assert_eq!(
            enum_lang(&loop_(lit("a"), 1, 3)),
            Some(words(&["a", "aa", "aaa"]))
        );
        assert_eq!(
            enum_lang(&loop_(union(vec![lit("a"), lit("b")]), 0, 1)),
            Some(words(&["", "a", "b"]))
        );
        // Star / Comp: never structurally finite.
        assert_eq!(enum_lang(&star(lit("a"))), None);
        assert_eq!(enum_lang(&comp(lit("a"))), None);
    }

    #[test]
    fn enum_lang_loop_degenerate_inner_terminates() {
        // L(inner) = ∅ (Inter of disjoint literals) — invisible to the smart
        // constructors, so the Loop node survives; the enumerator must
        // early-out instead of iterating toward the huge bound.
        let empty_lang = inter(vec![lit("a"), lit("b")]);
        assert_eq!(
            enum_lang(&loop_(empty_lang.clone(), 1, u32::MAX)),
            Some(words(&[]))
        );
        assert_eq!(
            enum_lang(&loop_(empty_lang, 0, u32::MAX)),
            Some(words(&[""]))
        );
        // L(inner) = {""}: Inter of two opt-shapes — again invisible to the
        // constructors. Without the early-out this loop would spin ~2^32
        // no-growth iterations.
        let eps_lang = inter(vec![
            union(vec![lit("a"), Rex::Eps]),
            union(vec![lit("b"), Rex::Eps]),
        ]);
        assert_eq!(
            enum_lang(&loop_(eps_lang, 5, u32::MAX)),
            Some(words(&[""]))
        );
    }

    #[test]
    fn enum_caps_and_surrogates_abort() {
        // Cardinality cap: 3^6 = 729 words > 256.
        let abc = union(vec![lit("a"), lit("b"), lit("c")]);
        assert_eq!(enum_lang(&loop_(abc, 6, 6)), None);
        // Byte cap: ONE word of 100·60 = 6000 bytes > 4096 — the shape the
        // cardinality cap cannot see.
        let a100 = lit(&"a".repeat(100));
        assert_eq!(enum_lang(&loop_(a100, 60, 60)), None);
        // Huge-bound loop over a single word: aborts via the caps, fast.
        assert_eq!(enum_lang(&loop_(lit("a"), 1, u32::MAX)), None);
        // Range wider than the cardinality cap.
        assert_eq!(enum_lang(&Rex::Range(0, 300)), None);
        // Surrogate-crossing range: explicit guard.
        assert_eq!(enum_lang(&Rex::Range(0xD000, 0xE000)), None);
    }

    #[test]
    fn enum_comp_per_operator() {
        let sigma_star = star(Rex::Range(0, MAX_CODE));
        // re.all: co-finite with zero exceptions.
        assert_eq!(enum_comp(&sigma_star), Some(words(&[])));
        // comp(finite): exceptions are exactly the finite words.
        assert_eq!(
            enum_comp(&comp(union(vec![lit("a"), lit("b")]))),
            Some(words(&["a", "b"]))
        );
        // Inter of co-finites: union of exceptions (Σ*\⋂ = ⋃ complements).
        assert_eq!(
            enum_comp(&inter(vec![comp(lit("a")), comp(lit("b"))])),
            Some(words(&["a", "b"]))
        );
        // The extracted re.diff(re.all, X) shape: inter(Σ*, comp(X)).
        assert_eq!(
            enum_comp(&inter(vec![sigma_star.clone(), comp(lit("a"))])),
            Some(words(&["a"]))
        );
        // Union with a co-finite part: its exceptions filtered by
        // NON-membership in the other parts ("b" rejoins via to_re "b").
        assert_eq!(
            enum_comp(&union(vec![comp(union(vec![lit("a"), lit("b")])), lit("b")])),
            Some(words(&["a"]))
        );
        // Not structurally co-finite: finite shapes, star, bare ranges.
        assert_eq!(enum_comp(&lit("a")), None);
        assert_eq!(enum_comp(&Rex::Eps), None);
        assert_eq!(enum_comp(&Rex::Empty), None);
        assert_eq!(enum_comp(&star(lit("a"))), None);
        assert_eq!(enum_comp(&Rex::Range('a' as u32, 'c' as u32)), None);
    }
```

- [ ] **Step 2: Run tests to verify they fail to compile**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -20`
Expected: compile error — `Words`, `enum_lang`, `enum_comp` not found.

- [ ] **Step 3: Implement the enumerators**

In `crates/shinri-str/src/regex.rs`: add to the imports at the top (line 23 area):

```rust
use std::collections::BTreeSet;
```

Then insert after `lit_to_rex` (~line 254), before `extract_const_regex`:

```rust
// ─── Slice 20: finite / co-finite language enumeration ──────────────────

/// Max cardinality of any intermediate word set in either enumerator.
const ENUM_WORD_CAP: usize = 256;
/// Max total bytes (sum of word lengths) of any intermediate word set.
/// The cardinality cap alone does not bound work: `(_ re.loop n n)` over a
/// one-word language has exactly ONE word of unbounded length.
const ENUM_TOTAL_BYTES_CAP: usize = 4096;

type Words = BTreeSet<String>;

/// `None` iff the set crosses either enumeration cap (→ caller aborts).
fn check_caps(ws: Words) -> Option<Words> {
    if ws.len() > ENUM_WORD_CAP {
        return None;
    }
    if ws.iter().map(|w| w.len()).sum::<usize>() > ENUM_TOTAL_BYTES_CAP {
        return None;
    }
    Some(ws)
}

/// Pairwise concatenation of two finite languages, cap-checked.
fn concat_words(a: &Words, b: &Words) -> Option<Words> {
    let mut out = Words::new();
    for x in a {
        for y in b {
            out.insert(format!("{x}{y}"));
            if out.len() > ENUM_WORD_CAP {
                return None;
            }
        }
    }
    check_caps(out)
}

/// The words of `L(r)` when STRUCTURALLY finite and within the caps; `None`
/// otherwise. A `None` is never wrong — it only means "not recognized"
/// (→ the atom survives to the presence fence).
fn enum_lang(r: &Rex) -> Option<Words> {
    match r {
        Rex::Empty => Some(Words::new()),
        Rex::Eps => Some(Words::from([String::new()])),
        Rex::Range(lo, hi) => {
            // Surrogates (0xD800..=0xDFFF) are SMT-LIB alphabet characters
            // but not Rust chars — a range touching them cannot be
            // enumerated faithfully (words would be silently MISSED,
            // breaking the equivalence). Any such range spans >= 2050
            // chars (endpoints are Rust chars, hence non-surrogate), so
            // the cardinality cap also rejects it — this guard makes the
            // soundness argument local instead of an accident of the cap.
            if *lo <= 0xDFFF && *hi >= 0xD800 {
                return None;
            }
            if (*hi - *lo) as usize + 1 > ENUM_WORD_CAP {
                return None;
            }
            let ws: Words = (*lo..=*hi)
                .map(|c| {
                    char::from_u32(c)
                        .expect("non-surrogate in-alphabet code point")
                        .to_string()
                })
                .collect();
            check_caps(ws)
        }
        Rex::Concat(ps) => {
            let mut acc = Words::from([String::new()]);
            for p in ps {
                acc = concat_words(&acc, &enum_lang(p)?)?;
            }
            Some(acc)
        }
        Rex::Union(ps) => {
            let mut acc = Words::new();
            for p in ps {
                acc.extend(enum_lang(p)?);
            }
            check_caps(acc)
        }
        Rex::Inter(ps) => {
            // Some part must enumerate finite; filter its words through
            // the remaining parts by ground evaluation (comp/star parts
            // are fine — eval_membership is total up to fuel).
            let (i, base) = ps
                .iter()
                .enumerate()
                .find_map(|(i, p)| Some((i, enum_lang(p)?)))?;
            let mut out = Words::new();
            for w in base {
                let mut keep = true;
                for (j, p) in ps.iter().enumerate() {
                    if j == i {
                        continue;
                    }
                    match eval_membership(&w, p) {
                        Some(true) => {}
                        Some(false) => {
                            keep = false;
                            break;
                        }
                        // Derivative fuel — abort the WHOLE enumeration,
                        // never guess.
                        None => return None,
                    }
                }
                if keep {
                    out.insert(w);
                }
            }
            Some(out)
        }
        Rex::Loop(inner, lo, hi) => {
            let s = enum_lang(inner)?;
            // Early-outs the smart constructors cannot see (they only
            // collapse SYNTACTIC Empty/Eps arguments): L(inner) = ∅ or
            // {""} would otherwise spin up to `hi` no-growth iterations.
            if s.is_empty() {
                return Some(if *lo == 0 {
                    Words::from([String::new()])
                } else {
                    Words::new()
                });
            }
            if s.len() == 1 && s.contains("") {
                return Some(Words::from([String::new()]));
            }
            // cur = S^n from n = 0; acc collects S^lo ∪ … ∪ S^hi.
            // Termination: S now has a nonempty word, so every power
            // either grows `cur`'s total bytes (single-word S) or `acc`'s
            // cardinality — one of the caps fires within ~max(cap) steps
            // unless the fixpoint breaks first.
            let mut cur = Words::from([String::new()]);
            let mut acc = Words::new();
            let mut n: u32 = 0;
            loop {
                if n >= *lo {
                    let before = acc.len();
                    acc.extend(cur.iter().cloned());
                    acc = check_caps(acc)?;
                    if acc.len() == before && n > *lo {
                        // S^n ⊆ (union of lower powers ≥ lo) implies
                        // S^(n+1) = S^n·S ⊆ acc·S ⊆ acc, inductively for
                        // all higher powers — nothing new can appear.
                        break;
                    }
                }
                if n == *hi {
                    break;
                }
                cur = concat_words(&cur, &s)?;
                n += 1;
            }
            Some(acc)
        }
        Rex::Star(_) | Rex::Comp(_) => None,
    }
}

/// The EXCEPTION set `Σ* \ L(r)` when `L(r)` is STRUCTURALLY co-finite and
/// within the caps; `None` otherwise.
fn enum_comp(r: &Rex) -> Option<Words> {
    match r {
        Rex::Comp(inner) => enum_lang(inner),
        // Σ* itself (re.all's extraction): co-finite, zero exceptions.
        Rex::Star(inner) if **inner == Rex::Range(0, MAX_CODE) => Some(Words::new()),
        // Σ* \ ⋂ps = ⋃(Σ* \ p): EVERY part must be co-finite.
        Rex::Inter(ps) => {
            let mut acc = Words::new();
            for p in ps {
                acc.extend(enum_comp(p)?);
            }
            check_caps(acc)
        }
        // Σ* \ ⋃ps = ⋂(Σ* \ p): SOME part must be co-finite; its
        // exceptions, filtered by NON-membership in every other part.
        Rex::Union(ps) => {
            let (i, base) = ps
                .iter()
                .enumerate()
                .find_map(|(i, p)| Some((i, enum_comp(p)?)))?;
            let mut out = Words::new();
            for w in base {
                let mut keep = true;
                for (j, p) in ps.iter().enumerate() {
                    if j == i {
                        continue;
                    }
                    match eval_membership(&w, p) {
                        Some(false) => {}
                        Some(true) => {
                            keep = false;
                            break;
                        }
                        None => return None,
                    }
                }
                if keep {
                    out.insert(w);
                }
            }
            Some(out)
        }
        // Complements of Empty/Eps/Range/Concat/Loop and other Stars are
        // infinite (or rare enough not to chase) — not recognized.
        _ => None,
    }
}
```

Until Task 2 wires these into the rewrite, silence dead-code lints by adding (transient — REMOVED in Task 2):

```rust
#[allow(dead_code)]
```

directly above `fn check_caps`, `fn concat_words`, `fn enum_lang`, and `fn enum_comp` (the consts are used by the functions; if clippy still flags them, put `#[allow(dead_code)]` above each const too).

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -20`
Expected: PASS — all pre-existing regex tests plus the 4 new tests.

- [ ] **Step 5: Format, lint, commit**

```bash
cd /workspace && cargo fmt && cargo clippy -p shinri-str --all-targets 2>&1 | tail -5
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): finite/co-finite Rex language enumerators + caps (slice 20)"
```

---

### Task 2: Symbolic `str.in_re` rewrite fallback, wired into the pass

The equivalence rewrite: when the ground fold declines, enumerate and emit `⋁ t = wᵢ` (finite) or `¬⋁ t = wᵢ` (co-finite). Removes the Task-1 `#[allow(dead_code)]`s. After this task the solver DECIDES the new fragment end-to-end.

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (module doc lines 1–21; the `rewrite` dispatch ~line 365; new functions after `try_fold_in_re` ~line 341; tests)

**Interfaces:**
- Consumes (Task 1): `enum_lang`, `enum_comp`, `Words`. Existing: `extract_const_regex`, `try_fold_in_re`, `MAX_CODE`, `Context::{mk_string_const, mk_eq, mk_app, mk_const_bool, string_const_value, term_node, children}`, `BuiltinOp::{Or, Not, StrInRe, StrConcat}`.
- Produces: `fn try_rewrite_symbolic_in_re(ctx: &mut Context, kids: &[TermId]) -> Option<TermId>` (private; Tasks 3–5 depend only on solver behavior, not names).

- [ ] **Step 1: Write the failing tests**

Append inside `mod tests` in `regex.rs`:

```rust
    // ── Task 2 (slice 20): symbolic rewrite fallback ─────────────────────

    /// Collect the string-literal RHS values of an Or-of-equalities term.
    fn eq_disjunct_values(ctx: &Context, t: TermId) -> Vec<String> {
        let TermNode::App { op, args, .. } = ctx.term_node(t) else {
            panic!("expected app");
        };
        let kids: Vec<TermId> = ctx.children(*args).to_vec();
        let eqs: Vec<TermId> = match op {
            Op::Builtin(BuiltinOp::Or) => kids,
            Op::Builtin(BuiltinOp::Eq) => vec![t],
            other => panic!("expected Or/Eq, got {other:?}"),
        };
        eqs.iter()
            .map(|&e| {
                let TermNode::App { args, .. } = ctx.term_node(e) else {
                    panic!("expected Eq app");
                };
                let ch = ctx.children(*args).to_vec();
                ctx.string_const_value(ch[1]).expect("literal RHS").to_owned()
            })
            .collect()
    }

    #[test]
    fn symbolic_finite_atom_rewrites_to_eq_disjunction() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let b = slit(&mut ctx, "b");
        let re_a = to_re(&mut ctx, a);
        let re_b = to_re(&mut ctx, b);
        let un = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[re_a, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, s, un);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(!has_unreduced_regex(&ctx, &out), "atom must be rewritten");
        let mut vals = eq_disjunct_values(&ctx, out[0]);
        vals.sort();
        assert_eq!(vals, vec!["a".to_owned(), "b".to_owned()]);

        // Singleton language: a bare equality, no Or wrapper.
        let atom = in_re(&mut ctx, s, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert_eq!(eq_disjunct_values(&ctx, out[0]), vec!["a".to_owned()]);
    }

    #[test]
    fn symbolic_cofinite_atom_rewrites_to_negated_disjunction() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let cmp = ctx.mk_app(Op::Builtin(BuiltinOp::ReComp), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, s, cmp);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(!has_unreduced_regex(&ctx, &out));
        // Shape: (not (= s "a")).
        let TermNode::App {
            op: Op::Builtin(BuiltinOp::Not),
            args,
            ..
        } = ctx.term_node(out[0]).clone()
        else {
            panic!("expected Not, got {:?}", ctx.term_node(out[0]));
        };
        let inner = ctx.children(args).to_vec()[0];
        assert_eq!(eq_disjunct_values(&ctx, inner), vec!["a".to_owned()]);
    }

    #[test]
    fn symbolic_zero_word_languages_fold_to_bool_consts() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        // s ∈ re.none → false.
        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let atom = in_re(&mut ctx, s, none);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // s ∈ re.all → true (co-finite, zero exceptions).
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let atom = in_re(&mut ctx, s, all);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
    }

    #[test]
    fn symbolic_out_of_fragment_shapes_still_fence() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        // Star: neither finite nor co-finite.
        let st = ctx.mk_app(Op::Builtin(BuiltinOp::ReStar), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, s, st);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Over-cap: (_ re.loop 1 300) over one char = 300 words > 256.
        let l = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: 1, hi: 300 }), &[re_a])
            .unwrap();
        let atom = in_re(&mut ctx, s, l);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Symbolic regex leaf still fences (extraction fails).
        let re_s = to_re(&mut ctx, s);
        let atom = in_re(&mut ctx, s, re_s);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn above_alphabet_string_side_skips_symbolic_rewrite() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        // Bare above-alphabet literal side (ground path already declines;
        // the symbolic path must decline too, not "decide" it).
        let hi = slit(&mut ctx, "\u{30000}");
        let atom = in_re(&mut ctx, hi, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Concat-embedded above-alphabet literal.
        let cc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[s, hi])
            .unwrap();
        let atom = in_re(&mut ctx, cc, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn symbolic_rewrite_keeps_unrelated_termids() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let lit_xy = slit(&mut ctx, "xy");
        let eq = ctx.mk_eq(s, lit_xy).unwrap();
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, s, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[eq, atom]);
        assert_eq!(out[0], eq, "unrelated assertion must keep its TermId");
        assert_ne!(out[1], atom, "membership atom must be rewritten");
    }
```

- [ ] **Step 2: Run tests to verify the new ones fail**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -20`
Expected: the 6 new tests FAIL (`has_unreduced_regex` still true / `fold_of` returns None for symbolic sides); pre-existing tests still pass.

- [ ] **Step 3: Implement the rewrite fallback**

In `regex.rs`, remove every `#[allow(dead_code)]` added in Task 1. Insert after `try_fold_in_re` (~line 341):

```rust
/// Slice 20: `t ∈ R` for ANY string term `t` when `L(R)` is structurally
/// finite (⇒ `⋁ t = wᵢ`) or co-finite (⇒ `¬⋁ t = wᵢ` over the exception
/// set). Full equivalences at any polarity — no fresh variables, no
/// repair. Skipped (→ fence) when the string side contains an
/// above-alphabet literal character (slice-18/19 posture: don't guess
/// semantics outside Σ) or when neither enumerator recognizes `R`.
fn try_rewrite_symbolic_in_re(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    if str_term_mentions_above_alphabet(ctx, kids[0]) {
        return None;
    }
    let rex = extract_const_regex(ctx, kids[1])?;
    if let Some(ws) = enum_lang(&rex) {
        return Some(mk_eq_disjunction(ctx, kids[0], &ws, false));
    }
    let exceptions = enum_comp(&rex)?;
    Some(mk_eq_disjunction(ctx, kids[0], &exceptions, true))
}

/// `⋁ᵢ (= t wᵢ)` — 0-ary folds straight to a Bool const (`negate` for the
/// co-finite reading), 1-ary is the bare equality, and `negate` wraps the
/// result in Not.
fn mk_eq_disjunction(ctx: &mut Context, t: TermId, words: &Words, negate: bool) -> TermId {
    if words.is_empty() {
        return ctx.mk_const_bool(negate);
    }
    let disj: Vec<TermId> = words
        .iter()
        .map(|w| {
            let lit = ctx.mk_string_const(w);
            ctx.mk_eq(t, lit).expect("well-sorted equality")
        })
        .collect();
    let core = if disj.len() == 1 {
        disj[0]
    } else {
        ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disj)
            .expect("well-sorted disjunction")
    };
    if negate {
        ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[core])
            .expect("well-sorted negation")
    } else {
        core
    }
}

/// Any literal character above the SMT-LIB alphabet anywhere in `t`?
fn str_term_mentions_above_alphabet(ctx: &Context, t: TermId) -> bool {
    if let Some(s) = ctx.string_const_value(t) {
        return s.chars().any(|c| c as u32 > MAX_CODE);
    }
    match ctx.term_node(t) {
        TermNode::App { args, .. } => {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            kids.iter()
                .any(|&k| str_term_mentions_above_alphabet(ctx, k))
        }
        TermNode::Const { .. } => false,
    }
}
```

Then change the `StrInRe` dispatch inside `fn rewrite` (~line 364) from:

```rust
            let special = match op {
                Op::Builtin(BuiltinOp::StrInRe) => try_fold_in_re(ctx, &new_children),
                _ => None,
            };
```

to:

```rust
            let special = match op {
                // Ground fold first (cheaper; also decides INFINITE
                // languages for literal strings), then the slice-20
                // finite/co-finite equivalence rewrite.
                Op::Builtin(BuiltinOp::StrInRe) => {
                    match try_fold_in_re(ctx, &new_children) {
                        Some(r) => Some(r),
                        None => try_rewrite_symbolic_in_re(ctx, &new_children),
                    }
                }
                _ => None,
            };
```

Finally update the module doc (lines 1–21): change the title line to
`//! Slice 19+20 pre-pass: `str.in_re` over SMT-LIB regular expressions —`
and extend the "Decided fragment" paragraph with:

```rust
//! Slice 20 adds: `str.in_re(t, R)` for ANY String term `t` when `L(R)` is
//! STRUCTURALLY finite (rewrites to `⋁ t = wᵢ`) or co-finite (rewrites to
//! `¬⋁ t = wᵢ` over the exception set) within the enumeration caps
//! (`ENUM_WORD_CAP`, `ENUM_TOTAL_BYTES_CAP`) — full equivalences at any
//! polarity; the produced (dis)equalities are word equations the engine
//! already owns. Surrogate-crossing ranges and above-alphabet string
//! sides are skipped (→ fence), never guessed.
```

- [ ] **Step 4: Run the module tests**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -20`
Expected: PASS (all old + all new).

- [ ] **Step 5: Run the full shinri-str + solver unit suites (no oracle)**

Run: `cargo test -p shinri-str -p shinri-solver 2>&1 | tail -15`
Expected: PASS — no existing test regresses (the only behavior change is Unknown→decided for the new fragment, which no non-oracle test pins).

- [ ] **Step 6: Format, lint, commit**

```bash
cd /workspace && cargo fmt && cargo clippy -p shinri-str -p shinri-solver --all-targets 2>&1 | tail -5
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): symbolic str.in_re equivalence rewrite for finite/co-finite languages (slice 20)"
```

---

### Task 3: E2e verdict pins for the decided fragment

Solver-level pins in the oracle test file (the file is `#![cfg(feature = "oracle")]` but these pins are shinri-only — no z3 involved). Also truth-up the stale slice-19 pin comment.

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (new tests after `targeted_regex_fences_unknown` ~line 2520; comment fix inside `targeted_regex_fences_unknown` ~line 2481)

**Interfaces:**
- Consumes: existing helpers `expect(src, Verdict)`, `shinri_verdict`, `Verdict`.
- Produces: test names `targeted_regex_symbolic_decided_sat`, `targeted_regex_symbolic_decided_unsat`, `targeted_regex_symbolic_fences_unknown` (Task 5's gates run them).

- [ ] **Step 1: Update the slice-19 pin comment**

In `targeted_regex_fences_unknown`, replace the first case's comment
`// Symbolic string side.` with:

```rust
    // Symbolic string side over re.allchar: STILL fenced after slice 20 —
    // Σ has 0x30000 single-char words, far over ENUM_WORD_CAP, and Σ's
    // complement ({""} ∪ longer words) is not co-finite.
```

- [ ] **Step 2: Write the new pins (failing on `Unknown` before Task 2 — now expected to pass; they pin the just-landed behavior)**

Insert after `targeted_regex_fences_unknown`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 20: symbolic str.in_re over finite / co-finite constant languages.
// The atom rewrites to a FULL equivalence over word equations (⋁ t = wᵢ,
// negated over the exception set for co-finite) — any polarity, any string
// term. Neither-finite-nor-co-finite and over-cap shapes keep fencing.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn targeted_regex_symbolic_decided_sat() {
    // Finite: s ∈ {ab, c} minus "ab" → s = "c".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.union (str.to_re \"ab\") (str.to_re \"c\"))))\
         (assert (not (= s \"ab\")))(check-sat)",
        Verdict::Sat,
    );
    // Co-finite: s ≠ \"a\" with length 1 — e.g. s = \"b\".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.comp (str.to_re \"a\"))))\
         (assert (= (str.len s) 1))(check-sat)",
        Verdict::Sat,
    );
    // re.all over a fully symbolic term folds to true.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s re.all))(check-sat)",
        Verdict::Sat,
    );
    // Concat string side: (s ++ \"b\") ∈ {ab} forces s = \"a\".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re (str.++ s \"b\") (str.to_re \"ab\")))\
         (assert (= s \"a\"))(check-sat)",
        Verdict::Sat,
    );
    // Bounded loop over a range: 1–2 chars of {a,b,c}, length pinned to 2.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s ((_ re.loop 1 2) (re.range \"a\" \"c\"))))\
         (assert (= (str.len s) 2))(check-sat)",
        Verdict::Sat,
    );
    // Under Boolean structure (term ite): forces the membership true.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (ite (str.in_re s (str.to_re \"a\")) \"x\" \"y\") \"x\"))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_regex_symbolic_decided_unsat() {
    // Finite: s constrained away from every word of the language.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.union (str.to_re \"a\") (str.to_re \"b\"))))\
         (assert (not (= s \"a\")))(assert (not (= s \"b\")))(check-sat)",
        Verdict::Unsat,
    );
    // re.none over a symbolic term folds to false.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s re.none))(check-sat)",
        Verdict::Unsat,
    );
    // Negated re.all membership folds to (not true).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (not (str.in_re s re.all)))(check-sat)",
        Verdict::Unsat,
    );
    // Co-finite vs pin: s ∈ comp({a}) conflicts with s = \"a\".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.comp (str.to_re \"a\"))))\
         (assert (= s \"a\"))(check-sat)",
        Verdict::Unsat,
    );
    // Both polarities of one membership atom.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (str.to_re \"a\")))\
         (assert (not (str.in_re s (str.to_re \"a\"))))(check-sat)",
        Verdict::Unsat,
    );
    // re.diff(re.all, {a}): the co-finite Inter/Comp extraction shape.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.diff re.all (str.to_re \"a\"))))\
         (assert (= s \"a\"))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_regex_symbolic_fences_unknown() {
    // Star over a range: neither finite nor co-finite.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.* (re.range \"a\" \"b\"))))(check-sat)",
        Verdict::Unknown,
    );
    // Cardinality cap: 300 words > ENUM_WORD_CAP = 256.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s ((_ re.loop 1 300) (str.to_re \"a\"))))(check-sat)",
        Verdict::Unknown,
    );
    // Byte cap: one 9000-byte word ((_ re.^ 300) over a 30-char literal).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s ((_ re.^ 300) (str.to_re \"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"))))(check-sat)",
        Verdict::Unknown,
    );
}
```

NOTE: the raw string escapes above are shown as they must appear in the
Rust source (backslash-quote inside normal string literals, exactly like
the neighboring slice-19 tests).

- [ ] **Step 3: Run the three pin tests + the slice-19 pins**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_regex 2>&1 | tail -15`
Expected: PASS — 6 tests (3 slice-19 + 3 new). This does NOT run the z3 families (name filter).

- [ ] **Step 4: Format, commit**

```bash
cd /workspace && cargo fmt
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): slice-20 e2e verdict pins for finite/co-finite symbolic str.in_re (slice 20)"
```

---

### Task 4: `qfs_regex_symbolic_matches_z3` differential oracle family

A fresh generator biased toward finite/co-finite regexes with VARIABLE string sides, mirroring the slice-19 family harness. Requires z3 on PATH (mise provides it).

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (generator methods after `finish_regex_ground` ~line 795; `gen_regex_symbolic_body` after `gen_regex_ground_body` ~line 887; family test after `qfs_regex_ground_matches_z3` ~line 1755)

**Interfaces:**
- Consumes: `Gen` (fields `rng`, `body`; methods `var()`, `lit()`, `assertion()`), `Lcg`, `Verdict`, `shinri_lines_counting_bailouts`, `z3_verdict`, `z3_with_model`, `parse_string_values`, `N_VARS`.
- Produces: test `qfs_regex_symbolic_matches_z3`; constants `RS_N_ITERS`, `RS_MAX_GUARD_BAILOUTS`; seed `0x52_00_0000_0001`.

- [ ] **Step 1: Add the generator methods** (inside `impl Gen`, after `finish_regex_ground`)

```rust
    /// A random constant regex biased to be STRUCTURALLY finite: literal /
    /// small-range leaves; union/concat/inter/diff/opt/small-loop/pow
    /// combinators. One star arm intentionally falls outside the decided
    /// fragment — fence coverage (tolerated unknown).
    fn rex_finite_sexpr(&mut self, depth: u64) -> String {
        if depth == 0 {
            return match self.rng.below(5) {
                0 => "re.none".to_owned(),
                1 => format!("(str.to_re {})", self.lit()),
                2 => "(str.to_re \"\")".to_owned(),
                3 => "(re.range \"a\" \"c\")".to_owned(),
                _ => "(re.range \"b\" \"c\")".to_owned(),
            };
        }
        let d = depth - 1;
        match self.rng.below(9) {
            0 => format!(
                "(re.++ {} {})",
                self.rex_finite_sexpr(d),
                self.rex_finite_sexpr(d)
            ),
            1 | 2 => format!(
                "(re.union {} {})",
                self.rex_finite_sexpr(d),
                self.rex_finite_sexpr(d)
            ),
            3 => format!(
                "(re.inter {} {})",
                self.rex_finite_sexpr(d),
                self.rex_finite_sexpr(d)
            ),
            4 => format!(
                "(re.diff {} {})",
                self.rex_finite_sexpr(d),
                self.rex_finite_sexpr(d)
            ),
            5 => format!("(re.opt {})", self.rex_finite_sexpr(d)),
            6 => format!(
                "((_ re.loop {} {}) {})",
                self.rng.below(2),
                1 + self.rng.below(3),
                self.rex_finite_sexpr(d)
            ),
            7 => format!("((_ re.^ {}) {})", self.rng.below(3), self.rex_finite_sexpr(d)),
            // Star — usually outside the decided fragment (fence coverage).
            _ => format!("(re.* {})", self.rex_finite_sexpr(d)),
        }
    }

    /// One slice-20 membership assertion: VARIABLE string side (sometimes
    /// var ++ literal) × finite-biased constant regex; ~1/4 comp-wrapped
    /// (the co-finite path), ~1/4 negated (the rewrite is polarity-free).
    fn regex_symbolic_assertion(&mut self) {
        let depth = 1 + self.rng.below(2); // 1..=2
        let mut r = self.rex_finite_sexpr(depth);
        if self.rng.below(4) == 0 {
            r = format!("(re.comp {r})");
        }
        let t = if self.rng.below(4) == 0 {
            format!("(str.++ {} {})", self.var(), self.lit())
        } else {
            self.var()
        };
        let atom = format!("(str.in_re {t} {r})");
        let atom = if self.rng.below(4) == 0 {
            format!("(not {atom})")
        } else {
            atom
        };
        self.body.push_str(&format!("(assert {atom})\n"));
    }

    /// Instance body for the slice-20 family: 1–2 symbolic membership
    /// assertions + 0–1 general assertions (equalities/lengths keep the
    /// word-equation path and the SAT witness path exercised).
    fn finish_regex_symbolic(mut self) -> String {
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.regex_symbolic_assertion();
        }
        if self.rng.below(2) == 0 {
            self.assertion();
        }
        self.body
    }
```

And after `gen_regex_ground_body` (~line 887):

```rust
fn gen_regex_symbolic_body(seed: u64) -> String {
    Gen::new(seed).finish_regex_symbolic()
}
```

- [ ] **Step 2: Add the family test** (after `qfs_regex_ground_matches_z3`, before "Targeted explicit cases")

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Symbolic-regex differential oracle (slice 20): VARIABLE-string × constant-
// regex str.in_re atoms whose language is structurally finite or co-finite
// are DECIDED via the equivalence rewrite to word equations (both verdicts,
// any polarity). Sat AND Unsat must agree with z3; Sat models are
// z3-verified. Out-of-fragment shapes — star arms, over-cap loops — fence
// (tolerated unknown). ASCII-only scripts (see the slice-19/20 plans).
// Fresh seed — never perturb existing families' seeds.
// ─────────────────────────────────────────────────────────────────────────────

const RS_N_ITERS: usize = 200;
const RS_MAX_GUARD_BAILOUTS: usize = RS_N_ITERS / 10;

#[test]
fn qfs_regex_symbolic_matches_z3() {
    let mut rng = Lcg(0x52_00_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness, mut n_guard_bailout) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..RS_N_ITERS {
        let seed = rng.next();
        let body = gen_regex_symbolic_body(seed);

        let (lines, bailouts) = shinri_lines_counting_bailouts(&format!("{body}(check-sat)\n"));
        if bailouts > 0 {
            n_guard_bailout += 1;
            continue;
        }
        let ours = match lines.first().map(String::as_str) {
            Some("sat") => Verdict::Sat,
            Some("unsat") => Verdict::Unsat,
            _ => Verdict::Unknown,
        };
        if ours == Verdict::Unknown {
            n_unknown += 1;
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S REGEX_SYMBOLIC SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{body}(check-sat)"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let get = format!(
                    "{body}(check-sat)\n(get-value ({}))\n",
                    (0..N_VARS)
                        .map(|k| format!("s{k}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                let (lines, _b) = shinri_lines_counting_bailouts(&get);
                if let Some(resp) = lines.get(1) {
                    let model = parse_string_values(resp);
                    if !model.is_empty() {
                        let w = z3_with_model(&body, &model);
                        assert_eq!(
                            w,
                            Verdict::Sat,
                            "WITNESS FAILURE (iter {it}, seed {seed}): model {model:?}\n{body}"
                        );
                        n_witness += 1;
                    }
                }
            }
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    println!(
        "qfs_regex_symbolic_matches_z3: {RS_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown / \
         {n_guard_bailout} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "regex-symbolic family produced zero SAT instances");
    assert!(
        n_unsat > 0,
        "regex-symbolic family produced zero UNSAT instances"
    );
    assert!(
        n_witness > 0,
        "no witnesses checked — model path not exercised"
    );
    assert!(
        n_guard_bailout <= RS_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailout} exceed bound {RS_MAX_GUARD_BAILOUTS}"
    );
}
```

- [ ] **Step 3: Run the new family FOREGROUND with captured output**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential qfs_regex_symbolic_matches_z3 -- --nocapture 2>&1 | tail -10`
Expected: PASS with a printed tally line (`N sat / M unsat / … 0 disagreements`), `n_sat > 0`, `n_unsat > 0`, `n_witness > 0`. RECORD THE EXACT TALLY — Task 5's truth-up quotes it. If the family trips a disagreement, STOP and debug (systematic-debugging skill); do not weaken the assertion.

- [ ] **Step 4: Re-run ALL string families + pins FOREGROUND (regression: identical tallies for existing families)**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture 2>&1 | tail -40`
Expected: PASS; every pre-existing family prints a tally IDENTICAL to its committed value (e.g. `qfs_regex_ground_matches_z3: 200 iters — 50 sat / 88 unsat / 62 shinri-unknown …`); the new family's tally matches Step 3.

- [ ] **Step 5: Format, lint, commit**

```bash
cd /workspace && cargo fmt && cargo clippy -p shinri-solver --all-targets 2>&1 | tail -5
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_regex_symbolic_matches_z3 differential oracle family (slice 20)"
```

---

### Task 5: Full gates, spec truth-up, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-07-13-shinri-slice20-regex-finite-design.md` (Status header)

**Interfaces:**
- Consumes: Task 4's recorded oracle tally.
- Produces: the merged slice.

- [ ] **Step 1: Run the full local gates**

```bash
cd /workspace
cargo test -p shinri-core -p shinri-parser -p shinri-str -p shinri-solver --features oracle 2>&1 | tail -20
cargo fmt --check
cargo clippy --workspace --all-targets 2>&1 | tail -5
```

Expected: all tests pass, fmt clean, clippy clean. (Do NOT run `cargo test --workspace` — CI covers it.)

- [ ] **Step 2: Truth-up the spec**

In the spec header, replace `Status: DESIGNED — implementation pending.` with `Status: IMPLEMENTED (slice 20 landed 2026-07-13).` followed by a short oracle-tally paragraph quoting the EXACT Task-4 tally (mirror the slice-19 spec's header: seed, iters, sat/unsat/unknown/witness counts, "0 disagreements", plus "all pre-existing string families re-ran unperturbed with identical tallies") and a `**Deviations from the spec.**` paragraph listing any (or "None." with the transient-allow note, as slice 19 did).

- [ ] **Step 3: Commit the truth-up, push, open the PR**

```bash
cd /workspace && git add docs/superpowers/specs/2026-07-13-shinri-slice20-regex-finite-design.md
git commit -m "docs: slice-20 spec truth-up — IMPLEMENTED + oracle tally"
git push -u origin slice20-regex-finite
gh pr create --title "Slice 20: symbolic str.in_re over finite/co-finite constant languages" \
  --body "Decides str.in_re(t, R) for any String term t and constant regex R whose language is structurally finite or co-finite, via a full-equivalence rewrite to word equations. Zero engine changes; everything else keeps fencing. Spec: docs/superpowers/specs/2026-07-13-shinri-slice20-regex-finite-design.md. Plan: docs/superpowers/plans/2026-07-13-shinri-slice20-regex-finite.md. New oracle family qfs_regex_symbolic_matches_z3: <paste Task-4 tally>."
```

Expected: PR URL printed. Report it and STOP — the user merges.

---

## Summary

| Task | Deliverable | Commit |
|---|---|---|
| 1 | `enum_lang`/`enum_comp` + caps + surrogate guard, unit-tested | `feat(str): finite/co-finite Rex language enumerators + caps (slice 20)` |
| 2 | Symbolic equivalence rewrite wired into the pass | `feat(str): symbolic str.in_re equivalence rewrite for finite/co-finite languages (slice 20)` |
| 3 | E2e verdict pins (sat/unsat/unknown) | `test(str): slice-20 e2e verdict pins for finite/co-finite symbolic str.in_re (slice 20)` |
| 4 | `qfs_regex_symbolic_matches_z3` oracle family, 0 disagreements | `test(str): qfs_regex_symbolic_matches_z3 differential oracle family (slice 20)` |
| 5 | Gates + spec truth-up + PR | `docs: slice-20 spec truth-up — IMPLEMENTED + oracle tally` |
