# str.replace_all (Slice 14) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add SMT-LIB `str.replace_all` to shinri as a value-sorted function, decided by fold + symbolic-`u` partial-eval, with everything else fenced to a sound `Unknown`.

**Architecture:** Mirror slice 13's `str.replace` machinery in `shinri-str/src/indexof_replace.rs`: bottom-up memoized rewrite that folds all-literal applications to a literal and partial-evals a literal-haystack + symbolic-`u` application into an N-way concat `pre ++ u ++ mid ++ u ++ … ++ post` around the **non-overlapping** occurrences. Surviving applications (symbolic haystack/needle, over-cap occurrence count) fence pre-solve to `Unknown`. Zero fresh variables; polarity-free.

**Tech Stack:** Rust (workspace crates `shinri-core`, `shinri-parser`, `shinri-str`, `shinri-solver`); `cargo test`; differential oracle vs `z3` (feature `oracle`, `z3` on PATH via mise).

## Global Constraints

- **Soundness contract (project invariant):** anything out of the decided fragment returns `unknown` — NEVER a wrong `sat`/`unsat`. Symbolic haystack/needle and over-cap `replace_all` fence to `Unknown`.
- **Zero fresh variables:** the rewrite introduces no new declarations; untouched subtrees keep their `TermId`.
- **Code points, not bytes:** all string indexing is over `Vec<char>` (Unicode scalar values), matching `eval_substr_const` / slice 13. Never byte offsets.
- **Empty-needle semantics:** `(str.replace_all s "" u)` = `s` (`u` dropped) — DIFFERS from `str.replace` (which gives `u ++ s`). This is the correctness trap.
- **Non-overlapping, left-to-right:** after a match at `p`, scanning resumes at `p + |t|` in the original haystack.
- **Oracle discipline:** a new op family gets a NEW oracle family with a FRESH seed; never perturb existing seeds. New seed for this slice: `0x51_4A_0000_0001`.
- **Arg order:** haystack-first — `(str.replace_all s t u)`.

---

### Task 1: Core op + sort rule

**Files:**
- Modify: `crates/shinri-core/src/term.rs:96` (add enum variant after `StrReplace`)
- Modify: `crates/shinri-core/src/context.rs:521` (extend the `StrReplace` sort-rule arm)
- Test: `crates/shinri-core/src/context.rs` (tests module, near the existing slice-13 sort tests around line 1372)

**Interfaces:**
- Produces: `BuiltinOp::StrReplaceAll` — sort rule `String × String × String → String` (arity 3, all operands String, result String).

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod tests` block in `crates/shinri-core/src/context.rs` (alongside the slice-13 sort tests):

```rust
#[test]
fn str_replace_all_sort_rule() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let x = {
        let f = ctx.declare_fun("x", &[], str_s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    };
    let lit = ctx.mk_string_const("a");
    // Well-sorted: String × String × String → String.
    let app = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[x, lit, lit])
        .unwrap();
    assert_eq!(ctx.sort_of(app), str_s);
    // Wrong arity → error.
    assert!(ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[x, lit])
        .is_err());
    // Int replacement operand → error.
    let i = ctx.mk_numeral(shinri_core::Rational::zero(), ctx.int_sort());
    assert!(ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[x, lit, i])
        .is_err());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core str_replace_all_sort_rule`
Expected: FAIL — `no variant named StrReplaceAll` (compile error).

- [ ] **Step 3: Add the enum variant**

In `crates/shinri-core/src/term.rs`, after line 96 (`StrReplace, // String × String × String → String`):

```rust
    StrReplace, // String × String × String → String
    // Slice 14: replace ALL non-overlapping occurrences (leftmost-first).
    StrReplaceAll, // String × String × String → String
```

- [ ] **Step 4: Extend the sort-rule arm**

In `crates/shinri-core/src/context.rs`, change the arm at line 521 from:

```rust
            StrReplace => {
```

to:

```rust
            StrReplace | StrReplaceAll => {
```

(The body — `expect_arity(args, 3)`, `expect_all(self, args, str_s)`, `Ok(str_s)` — is unchanged.)

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-core str_replace_all_sort_rule`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): StrReplaceAll builtin op + sort rule (slice 14)"
```

---

### Task 2: Parser + printer

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs:329` (name map), `crates/shinri-parser/src/parser.rs:891-895` (routing arm)
- Modify: `crates/shinri-parser/src/print.rs:198` (op name)
- Test: `crates/shinri-parser/src/parser.rs` (tests module, near `parses_indexof_and_replace` ~line 1875) and `crates/shinri-parser/src/print.rs` (tests near `prints_indexof_and_replace` ~line 255)

**Interfaces:**
- Consumes: `BuiltinOp::StrReplaceAll` (Task 1).
- Produces: `"str.replace_all"` token parses to `BuiltinOp::StrReplaceAll`; `print_term` emits `str.replace_all`.

- [ ] **Step 1: Write the failing parser test**

Add to the tests module in `crates/shinri-parser/src/parser.rs`:

```rust
#[test]
fn parses_and_rejects_replace_all() {
    let src = r#"(declare-fun x () String)
(assert (= (str.replace_all x "a" "b") x))"#;
    let cs = commands(src);
    let (ctx, cmd) = cs[1].as_ref().expect("replace_all parses");
    // The asserted term is (= (str.replace_all …) x): result sort String.
    let TermNode::App { args, .. } = ctx.term_node(*cmd_term(cmd)) else {
        panic!("expected eq app");
    };
    let lhs = ctx.children(*args).to_vec()[0];
    let TermNode::App { op, .. } = ctx.term_node(lhs) else {
        panic!("expected replace_all app");
    };
    assert!(matches!(op, Op::Builtin(BuiltinOp::StrReplaceAll)));
    assert_eq!(ctx.sort_of(lhs), ctx.string_sort());
    // Int replacement operand → parse diagnostic.
    let bad = commands(r#"(declare-fun x () String)(assert (= (str.replace_all x "a" 1) x))"#);
    assert!(bad[1].is_err(), "Int replacement must be a diagnostic");
}
```

> Note: reuse the existing test helpers (`commands`, `cmd_term`) already present in this module and used by `parses_indexof_and_replace`. If the local helper for extracting the asserted term differs, follow the exact shape of `parses_indexof_and_replace` (it inspects `cs[1]`), adapting only the op check to `StrReplaceAll`.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser parses_and_rejects_replace_all`
Expected: FAIL — `"str.replace_all"` is not recognized (parser returns an unknown-symbol error), so the `matches!` / `cs[1]` expectation fails.

- [ ] **Step 3: Wire the parser name map**

In `crates/shinri-parser/src/parser.rs`, after line 329 (`"str.replace" => StrReplace,`):

```rust
            "str.replace" => StrReplace,
            "str.replace_all" => StrReplaceAll,
```

- [ ] **Step 4: Wire the routing arm**

In `crates/shinri-parser/src/parser.rs`, extend the slice-13 delegation arm (lines 891-895) to include the new op:

```rust
            BuiltinOp::StrPrefixOf
            | BuiltinOp::StrSuffixOf
            | BuiltinOp::StrContains
            | BuiltinOp::StrIndexOf
            | BuiltinOp::StrReplace
            | BuiltinOp::StrReplaceAll => Self::mk(ctx, Op::Builtin(op), &args, &sp),
```

- [ ] **Step 5: Run parser test to verify it passes**

Run: `cargo test -p shinri-parser parses_and_rejects_replace_all`
Expected: PASS.

- [ ] **Step 6: Write the failing printer test**

Add to the tests module in `crates/shinri-parser/src/print.rs`:

```rust
#[test]
fn prints_replace_all() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let x = {
        let f = ctx.declare_fun("x", &[], str_s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    };
    let a = ctx.mk_string_const("a");
    let b = ctx.mk_string_const("b");
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[x, a, b])
        .unwrap();
    assert_eq!(print_term(&ctx, rep), r#"(str.replace_all x "a" "b")"#);
}
```

- [ ] **Step 7: Run printer test to verify it fails**

Run: `cargo test -p shinri-parser prints_replace_all`
Expected: FAIL — `StrReplaceAll` prints as the fallback/`Debug` name, not `str.replace_all`.

- [ ] **Step 8: Wire the printer**

In `crates/shinri-parser/src/print.rs`, after line 198 (`StrReplace => "str.replace".to_owned(),`):

```rust
        StrReplace => "str.replace".to_owned(),
        StrReplaceAll => "str.replace_all".to_owned(),
```

- [ ] **Step 9: Run printer test to verify it passes**

Run: `cargo test -p shinri-parser prints_replace_all`
Expected: PASS.

- [ ] **Step 10: Commit**

```bash
git add crates/shinri-parser/src/parser.rs crates/shinri-parser/src/print.rs
git commit -m "feat(parser): parse + print str.replace_all (slice 14)"
```

---

### Task 3: Concrete evaluators + all-literal fold

**Files:**
- Modify: `crates/shinri-str/src/indexof_replace.rs` (add helpers + wire the fold path; extend `rewrite`'s `special` match and `has_unreduced_indexof_replace`)
- Test: `crates/shinri-str/src/indexof_replace.rs` (tests module)

**Interfaces:**
- Consumes: existing private `occurrences`, `rewrite`, `partial_eval_indexof_replace`, `has_unreduced_indexof_replace`; `ctx.string_const_value`, `ctx.mk_string_const`, `ctx.mk_app`.
- Produces (private): `fn nonoverlapping_occurrences(hay: &[char], needle: &[char]) -> Vec<usize>`, `fn eval_replace_all(hay: &[char], t: &[char], u: &str) -> String`, `fn rewrite_replace_all(ctx: &mut Context, kids: &[TermId]) -> Option<TermId>`, `const REPLACE_ALL_CONCAT_CAP: usize`.

- [ ] **Step 1: Write the failing evaluator tests**

Add to the tests module in `crates/shinri-str/src/indexof_replace.rs` (the `chars` helper already exists there):

```rust
#[test]
fn nonoverlapping_occurrences_are_greedy_left_to_right() {
    // Overlaps are NOT taken: "aaa"/"aa" matches only at 0 (resume at 2).
    assert_eq!(nonoverlapping_occurrences(&chars("aaa"), &chars("aa")), vec![0]);
    // Adjacent matches: "abab"/"ab" → {0, 2}.
    assert_eq!(nonoverlapping_occurrences(&chars("abab"), &chars("ab")), vec![0, 2]);
    // Single-char needle repeated.
    assert_eq!(nonoverlapping_occurrences(&chars("aaa"), &chars("a")), vec![0, 1, 2]);
    // Empty needle → NO positions (u dropped downstream).
    assert_eq!(nonoverlapping_occurrences(&chars("ab"), &chars("")), Vec::<usize>::new());
    // Code points, not bytes: 'l' in "héllo" at 2 and 3.
    assert_eq!(nonoverlapping_occurrences(&chars("héllo"), &chars("l")), vec![2, 3]);
}

#[test]
fn eval_replace_all_pinned_semantics() {
    // All non-overlapping occurrences replaced.
    assert_eq!(eval_replace_all(&chars("abab"), &chars("ab"), "Z"), "ZZ");
    // Non-overlapping only: "aaa"/"aa" → "Xa" (NOT "XX").
    assert_eq!(eval_replace_all(&chars("aaa"), &chars("aa"), "X"), "Xa");
    // Needle absent → haystack unchanged (u dropped).
    assert_eq!(eval_replace_all(&chars("abc"), &chars("z"), "X"), "abc");
    // EMPTY needle → haystack unchanged, u DROPPED (contrast str.replace → "Xab").
    assert_eq!(eval_replace_all(&chars("ab"), &chars(""), "X"), "ab");
    // Code points.
    assert_eq!(eval_replace_all(&chars("héllo"), &chars("l"), "L"), "héLLo");
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str nonoverlapping_occurrences_are_greedy_left_to_right eval_replace_all_pinned_semantics`
Expected: FAIL — `cannot find function nonoverlapping_occurrences` / `eval_replace_all` (compile error).

- [ ] **Step 3: Add the concrete evaluators**

In `crates/shinri-str/src/indexof_replace.rs`, after `eval_replace` (ends ~line 68), add:

```rust
/// Non-overlapping occurrence positions of `needle` in `hay`, greedy
/// left-to-right: after a match at `j`, scanning resumes at `j + |needle|`.
/// The empty needle yields NO positions — SMT-LIB `str.replace_all` leaves `s`
/// unchanged on an empty needle (unlike `str.replace`/`str.indexof`).
fn nonoverlapping_occurrences(hay: &[char], needle: &[char]) -> Vec<usize> {
    let m = needle.len();
    if m == 0 {
        return Vec::new();
    }
    let n = hay.len();
    let mut out = Vec::new();
    let mut j = 0;
    while j + m <= n {
        if hay[j..j + m] == *needle {
            out.push(j);
            j += m;
        } else {
            j += 1;
        }
    }
    out
}

/// Concrete `(str.replace_all s t u)`: replace ALL non-overlapping occurrences
/// of `t` by `u`, left-to-right. Empty `t` or absent `t` → `s` unchanged
/// (`u` dropped).
fn eval_replace_all(hay: &[char], t: &[char], u: &str) -> String {
    let positions = nonoverlapping_occurrences(hay, t);
    if positions.is_empty() {
        return hay.iter().collect();
    }
    let m = t.len();
    let mut out = String::new();
    let mut cursor = 0usize;
    for &p in &positions {
        out.extend(&hay[cursor..p]);
        out.push_str(u);
        cursor = p + m;
    }
    out.extend(&hay[cursor..]);
    out
}
```

- [ ] **Step 4: Run evaluator tests to verify they pass**

Run: `cargo test -p shinri-str nonoverlapping_occurrences_are_greedy_left_to_right eval_replace_all_pinned_semantics`
Expected: PASS.

- [ ] **Step 5: Write the failing fold test**

Add to the tests module (the `int_lit`, `str_var` helpers already exist there):

```rust
#[test]
fn folds_all_literal_replace_all() {
    let mut ctx = Context::new();
    let abab = ctx.mk_string_const("abab");
    let ab = ctx.mk_string_const("ab");
    let z = ctx.mk_string_const("Z");
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[abab, ab, z])
        .unwrap();
    let want_lit = ctx.mk_string_const("ZZ");
    let atom = ctx.mk_eq(rep, want_lit).unwrap();
    let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
    // (= "ZZ" "ZZ") — both sides the SAME TermId, and no replace_all survives.
    let want = ctx.mk_eq(want_lit, want_lit).unwrap();
    assert_eq!(out, vec![want]);
    assert!(!has_unreduced_indexof_replace(&ctx, &out));
}

#[test]
fn folds_empty_needle_replace_all_drops_u() {
    // Empty needle: result is the haystack, u dropped (contrast str.replace).
    let mut ctx = Context::new();
    let ab = ctx.mk_string_const("ab");
    let empty = ctx.mk_string_const("");
    let x = ctx.mk_string_const("X");
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[ab, empty, x])
        .unwrap();
    let r = str_var(&mut ctx, "r");
    let atom = ctx.mk_eq(rep, r).unwrap();
    let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
    let want = ctx.mk_eq(ab, r).unwrap(); // (= "ab" r)
    assert_eq!(out, vec![want]);
}
```

- [ ] **Step 6: Run fold tests to verify they fail**

Run: `cargo test -p shinri-str folds_all_literal_replace_all folds_empty_needle_replace_all_drops_u`
Expected: FAIL — the `StrReplaceAll` app is left in place (no `special` handler), so `out` still contains the application and the equality does not collapse.

- [ ] **Step 7: Add the fold/partial-eval rewrite (fold path only for now)**

In `crates/shinri-str/src/indexof_replace.rs`, add the cap constant next to `INDEXOF_CHAIN_CAP` (~line 29):

```rust
/// Cap on the number of non-overlapping occurrences spliced into the
/// symbolic-`u` `str.replace_all` concat. Over-cap applications are left in
/// place and fence. Folding (all-literal) has NO cap.
const REPLACE_ALL_CONCAT_CAP: usize = 64;
```

Add the rewrite function after `rewrite_replace` (~line 215):

```rust
/// `(str.replace_all s t u)`, children already rewritten. Some(_) iff haystack
/// and needle are literals — EXACT for any `u` (all split points are concrete).
/// None (symbolic haystack/needle, or over-cap occurrence count) leaves the app
/// in place (→ fence).
fn rewrite_replace_all(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let hay: Vec<char> = ctx.string_const_value(kids[0])?.chars().collect();
    let t: Vec<char> = ctx.string_const_value(kids[1])?.chars().collect();
    let u = kids[2];
    let positions = nonoverlapping_occurrences(&hay, &t);
    if positions.is_empty() {
        // Needle absent or empty: result is the haystack; `u` is irrelevant.
        return Some(kids[0]);
    }
    if let Some(uv) = ctx.string_const_value(u).map(str::to_owned) {
        // Fully literal: fold to a single literal.
        return Some(ctx.mk_string_const(&eval_replace_all(&hay, &t, &uv)));
    }
    // Symbolic u: bound the concat width by the occurrence count.
    if positions.len() > REPLACE_ALL_CONCAT_CAP {
        return None; // over-cap: leave in place → fence
    }
    // (str.++ pre u mid1 u … u post), empty literal gaps/flanks dropped.
    let m = t.len();
    let mut parts: Vec<TermId> = Vec::new();
    let mut cursor = 0usize;
    for &p in &positions {
        let gap: String = hay[cursor..p].iter().collect();
        if !gap.is_empty() {
            parts.push(ctx.mk_string_const(&gap));
        }
        parts.push(u);
        cursor = p + m;
    }
    let tail: String = hay[cursor..].iter().collect();
    if !tail.is_empty() {
        parts.push(ctx.mk_string_const(&tail));
    }
    Some(if parts.len() == 1 {
        parts[0]
    } else {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &parts)
            .expect("pre ++ u ++ … ++ post")
    })
}
```

Wire it into `rewrite`'s `special` match (the `match op { … }` around line 92-96): add the arm

```rust
                Op::Builtin(BuiltinOp::StrReplace) => rewrite_replace(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrReplaceAll) => rewrite_replace_all(ctx, &new_children),
```

- [ ] **Step 8: Extend the fence walk**

In `has_unreduced_indexof_replace`, change the `matches!` (around line 227-230) from:

```rust
                matches!(
                    op,
                    Op::Builtin(BuiltinOp::StrIndexOf | BuiltinOp::StrReplace)
                ) || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
```

to:

```rust
                matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::StrIndexOf | BuiltinOp::StrReplace | BuiltinOp::StrReplaceAll
                    )
                ) || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
```

- [ ] **Step 9: Run fold tests to verify they pass**

Run: `cargo test -p shinri-str folds_all_literal_replace_all folds_empty_needle_replace_all_drops_u`
Expected: PASS.

- [ ] **Step 10: Commit**

```bash
git add crates/shinri-str/src/indexof_replace.rs
git commit -m "feat(str): replace_all pre-pass — nonoverlap evaluators + all-literal fold (slice 14)"
```

---

### Task 4: Symbolic-`u` partial-eval + cap + fence unit coverage

**Files:**
- Test only: `crates/shinri-str/src/indexof_replace.rs` (tests module)

(The implementation in Task 3 already covers the symbolic path and cap; this task pins its behavior with tests. The `concat_parts` helper already exists in the tests module.)

**Interfaces:**
- Consumes: `partial_eval_indexof_replace`, `has_unreduced_indexof_replace`, `rewrite_replace_all` behavior from Task 3; `concat_parts`, `str_var` helpers.

- [ ] **Step 1: Write the failing symbolic-`u` / cap / fence tests**

```rust
#[test]
fn replace_all_symbolic_u_two_occurrences_concat() {
    // (str.replace_all "aza" "a" u) → (str.++ u "z" u): matches at 0 and 2.
    let mut ctx = Context::new();
    let aza = ctx.mk_string_const("aza");
    let a = ctx.mk_string_const("a");
    let u = str_var(&mut ctx, "u");
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[aza, a, u])
        .unwrap();
    let out_s = str_var(&mut ctx, "r");
    let atom = ctx.mk_eq(rep, out_s).unwrap();
    let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
    let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
        panic!("eq app");
    };
    let lhs = ctx.children(args).to_vec()[0];
    let parts = concat_parts(&ctx, lhs);
    assert_eq!(parts.len(), 3);
    assert_eq!(parts[0], u);
    assert_eq!(ctx.string_const_value(parts[1]), Some("z"));
    assert_eq!(parts[2], u);
    assert!(!has_unreduced_indexof_replace(&ctx, &out));
}

#[test]
fn replace_all_symbolic_u_all_needle_collapses_to_bare_u_repeats() {
    // (str.replace_all "aa" "a" u) → (str.++ u u): both flanks/gaps empty.
    let mut ctx = Context::new();
    let aa = ctx.mk_string_const("aa");
    let a = ctx.mk_string_const("a");
    let u = str_var(&mut ctx, "u2");
    let r = str_var(&mut ctx, "r2");
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[aa, a, u])
        .unwrap();
    let atom = ctx.mk_eq(rep, r).unwrap();
    let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
    let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
        panic!("eq app");
    };
    let lhs = ctx.children(args).to_vec()[0];
    let parts = concat_parts(&ctx, lhs);
    assert_eq!(parts, vec![u, u]);
}

#[test]
fn replace_all_needle_absent_drops_symbolic_u() {
    let mut ctx = Context::new();
    let abc = ctx.mk_string_const("abc");
    let z = ctx.mk_string_const("z");
    let u = str_var(&mut ctx, "u3");
    let r = str_var(&mut ctx, "r3");
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[abc, z, u])
        .unwrap();
    let atom = ctx.mk_eq(rep, r).unwrap();
    let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
    let want = ctx.mk_eq(abc, r).unwrap(); // (= "abc" r): u irrelevant
    assert_eq!(out, vec![want]);
}

#[test]
fn replace_all_over_cap_symbolic_u_fences() {
    // 65 single-char occurrences with symbolic u → over cap (64) → left in place.
    let mut ctx = Context::new();
    let big = ctx.mk_string_const(&"a".repeat(65));
    let a = ctx.mk_string_const("a");
    let u = str_var(&mut ctx, "u4");
    let r = str_var(&mut ctx, "r4");
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[big, a, u])
        .unwrap();
    let atom = ctx.mk_eq(rep, r).unwrap();
    let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
    assert_eq!(out, vec![atom], "over-cap symbolic-u must survive unchanged");
    assert!(has_unreduced_indexof_replace(&ctx, &out), "→ fence");
    // At exactly the cap (64 occurrences) it rewrites.
    let at_cap = ctx.mk_string_const(&"a".repeat(64));
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[at_cap, a, u])
        .unwrap();
    let atom = ctx.mk_eq(rep, r).unwrap();
    let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
    assert!(!has_unreduced_indexof_replace(&ctx, &out), "at cap → rewritten");
}

#[test]
fn replace_all_symbolic_haystack_fences() {
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "sf2");
    let a = ctx.mk_string_const("a");
    let x = ctx.mk_string_const("X");
    let r = str_var(&mut ctx, "rf2");
    let rep = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[s, a, x])
        .unwrap();
    let atom = ctx.mk_eq(rep, r).unwrap();
    let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
    assert_eq!(out, vec![atom], "symbolic haystack survives unchanged");
    assert!(has_unreduced_indexof_replace(&ctx, &out));
}
```

- [ ] **Step 2: Run tests to verify they pass**

Run: `cargo test -p shinri-str replace_all_`
Expected: PASS (all five — the Task-3 implementation already supports these paths).

> If `replace_all_symbolic_u_all_needle_collapses_to_bare_u_repeats` or any concat-shape test fails, the bug is in `rewrite_replace_all`'s flank-drop / single-part-collapse logic — fix it there, not in the test.

- [ ] **Step 3: Run the full shinri-str suite (no regressions)**

Run: `cargo test -p shinri-str`
Expected: PASS — all slice-13 `indexof_replace` tests still green.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-str/src/indexof_replace.rs
git commit -m "test(str): replace_all symbolic-u concat, cap boundary, fence (slice 14)"
```

---

### Task 5: Solver fence wiring + e2e script pins

**Files:**
- Modify: `crates/shinri-solver/src/string_stage.rs:51` (add `StrReplaceAll` to `is_string_op`)
- Test: `crates/shinri-solver/tests/script_e2e.rs` (new tests after the slice-13 block ~line 730)

**Interfaces:**
- Consumes: `run_script(src: &str) -> Vec<String>` (existing e2e helper); the string-path pre-pass wiring in `lib.rs` (already invokes `partial_eval_indexof_replace` + `has_unreduced_indexof_replace`).
- Produces: `str.replace_all` now routes onto the string path (`uses_strings` true) and is decided/fenced end-to-end.

- [ ] **Step 1: Write the failing e2e tests**

Add to `crates/shinri-solver/tests/script_e2e.rs`:

```rust
// ── Slice 14: str.replace_all ────────────────────────────────────────────────

#[test]
fn str_replace_all_literal_folds_decide_any_polarity() {
    // All non-overlapping occurrences replaced.
    let out = run_script(r#"(set-logic QF_S)(assert (= (str.replace_all "abab" "ab" "Z") "ZZ"))(check-sat)"#);
    assert_eq!(out, vec!["sat"]);
    // Non-overlapping only: "aaa"/"aa" → "Xa", so "=…\"XX\"" is unsat.
    let out = run_script(r#"(set-logic QF_S)(assert (= (str.replace_all "aaa" "aa" "X") "XX"))(check-sat)"#);
    assert_eq!(out, vec!["unsat"]);
    let out = run_script(r#"(set-logic QF_S)(assert (= (str.replace_all "aaa" "aa" "X") "Xa"))(check-sat)"#);
    assert_eq!(out, vec!["sat"]);
    // Negated literal fold (polarity-free).
    let out = run_script(
        r#"(set-logic QF_S)(assert (not (= (str.replace_all "abc" "b" "X") "aXc")))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // EMPTY-needle trap: u DROPPED, result is the haystack (contrast str.replace).
    let out = run_script(r#"(set-logic QF_S)(assert (= (str.replace_all "ab" "" "X") "ab"))(check-sat)"#);
    assert_eq!(out, vec!["sat"]);
    let out = run_script(r#"(set-logic QF_S)(assert (= (str.replace_all "ab" "" "X") "Xab"))(check-sat)"#);
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn str_replace_all_symbolic_replacement_decides() {
    // (str.replace_all "aza" "a" u) → (str.++ u "z" u); "=…\"bzb\"" forces u="b".
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun u () String)
           (assert (= (str.replace_all "aza" "a" u) "bzb"))(check-sat)(get-value (u))"#,
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"));
    assert!(
        out.get(1).is_some_and(|v| v.contains("\"b\"")),
        "u must be \"b\", got {out:?}"
    );
    // Repeated-variable contradiction: u="b" ∧ u="c" required → unsat.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun u () String)
           (assert (= (str.replace_all "aza" "a" u) "bzc"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn str_replace_all_symbolic_haystack_fences_unknown() {
    // Symbolic haystack (z3: sat) → sound Unknown, canary flip-marker.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (= (str.replace_all s "a" "X") "XbX"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
    // Symbolic needle also fences.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun t () String)
           (assert (= (str.replace_all "abc" t "X") "aXc"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}
```

- [ ] **Step 2: Run e2e tests to verify they fail**

Run: `cargo test -p shinri-solver --test script_e2e str_replace_all_`
Expected: FAIL — `str.replace_all` is not yet in `is_string_op`, so `uses_strings` is false, the string pre-pass never runs, and the folds/fences don't happen (verdicts wrong, e.g. `sat`-with-uninterpreted instead of the decided answer, or the symbolic-haystack case not fencing).

- [ ] **Step 3: Add the op to `is_string_op`**

In `crates/shinri-solver/src/string_stage.rs`, extend `is_string_op` (line 51 area):

```rust
                | BuiltinOp::StrIndexOf
                | BuiltinOp::StrReplace
                | BuiltinOp::StrReplaceAll
```

Update the module doc comment (lines 4-5) to mention `str.replace_all` alongside the other listed `str.*` ops.

- [ ] **Step 4: Run e2e tests to verify they pass**

Run: `cargo test -p shinri-solver --test script_e2e str_replace_all_`
Expected: PASS.

- [ ] **Step 5: Run the full solver test suite (no regressions)**

Run: `cargo test -p shinri-solver`
Expected: PASS — slice-13 and all existing string-path tests still green.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/src/string_stage.rs crates/shinri-solver/tests/script_e2e.rs
git commit -m "feat(str): route + fence str.replace_all, e2e pins + canaries (slice 14)"
```

---

### Task 6: Differential oracle family `qfs_replace_all_matches_z3`

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (add generator methods + a `gen_replace_all_body` free fn + the test)
- Test: the new `#[test] fn qfs_replace_all_matches_z3` (feature-gated `oracle`)

**Interfaces:**
- Consumes: `Gen` (with `ir_haystack`, `lit`, `atom_term`, `assertion`), `Lcg`, `shinri_lines_counting_bailouts`, `z3_verdict`, `z3_with_model`, `parse_string_values`, `Verdict`, `N_VARS` — all existing in this file.
- Produces: `fn gen_replace_all_body(seed: u64) -> String`; new seed `0x51_4A_0000_0001`.

- [ ] **Step 1: Add the generator methods**

In `crates/shinri-solver/tests/qfs_differential.rs`, inside `impl Gen`, after `finish_indexof_replace` (~line 384):

```rust
    /// One str.replace_all assertion. MAY be negated (the rewrite is exact at
    /// any polarity). Needle is a literal (the decided fragment); the
    /// replacement `u` and the target are atomic terms. The literal-heavy
    /// haystack (via `ir_haystack`) drives the fold / partial-eval paths; a
    /// variable haystack (1 in 4) fences to sound Unknown (tolerated).
    fn replace_all_assertion(&mut self) {
        let hay = self.ir_haystack();
        let needle = self.lit();
        let u = self.atom_term();
        let target = self.atom_term();
        let atom = format!("(= (str.replace_all {hay} {needle} {u}) {target})");
        let atom = if self.rng.below(4) == 0 {
            format!("(not {atom})")
        } else {
            atom
        };
        self.body.push_str(&format!("(assert {atom})\n"));
    }

    /// Instance body for the slice-14 family: shared string vars, 1-2
    /// replace_all assertions, 0-1 general assertions (word eqs / lengths) for
    /// cross-theory mixing.
    fn finish_replace_all(mut self) -> String {
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.replace_all_assertion();
        }
        if self.rng.below(2) == 0 {
            self.assertion();
        }
        self.body
    }
```

Add the free function next to `gen_indexof_replace_body` (~line 454):

```rust
fn gen_replace_all_body(seed: u64) -> String {
    Gen::new(seed).finish_replace_all()
}
```

- [ ] **Step 2: Add the oracle test**

After `qfs_indexof_replace_matches_z3` (ends ~line 830), add:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// str.replace_all differential oracle (slice 14): fold + partial-eval + fence.
// Rewrites are polarity-free, so atoms MAY be negated. Symbolic-u at ≥2
// occurrences yields a repeated-variable concat — the semi-decidable case,
// sound via the step budget (Unknown on exhaustion, tolerated & counted).
// Symbolic haystack/needle fence to sound Unknown. Guard bailouts: same
// tolerated slice-11 retraction-leak class as the other string families.
// ─────────────────────────────────────────────────────────────────────────────

const RA_N_ITERS: usize = 200;
const RA_MAX_GUARD_BAILOUTS: usize = RA_N_ITERS / 10;

#[test]
fn qfs_replace_all_matches_z3() {
    let mut rng = Lcg(0x51_4A_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness, mut n_guard_bailout) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..RA_N_ITERS {
        let seed = rng.next();
        let body = gen_replace_all_body(seed);

        let (lines, bailouts) = shinri_lines_counting_bailouts(&format!("{body}(check-sat)\n"));
        if bailouts > 0 {
            n_guard_bailout += 1;
            continue; // sound bail-to-unknown: tolerated, counted
        }
        let ours = match lines.first().map(String::as_str) {
            Some("sat") => Verdict::Sat,
            Some("unsat") => Verdict::Unsat,
            _ => Verdict::Unknown,
        };
        if ours == Verdict::Unknown {
            n_unknown += 1; // sound fence/fuel: tolerated, counted
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S REPLACE_ALL SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
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
                let (lines, _bailouts) = shinri_lines_counting_bailouts(&get);
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
        "qfs_replace_all_matches_z3: {RA_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown / \
         {n_guard_bailout} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "replace_all family produced zero SAT instances");
    assert!(n_unsat > 0, "replace_all family produced zero UNSAT instances");
    assert!(n_witness > 0, "no witnesses checked — model path not exercised");
    assert!(
        n_guard_bailout <= RA_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailout} exceed bound {RA_MAX_GUARD_BAILOUTS} — \
         the tolerated slice-11 retraction leak may have widened (investigate, do not raise the bound blindly)"
    );
}
```

- [ ] **Step 3: Run the new oracle family to verify 0 disagreements**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential qfs_replace_all_matches_z3 -- --nocapture`
Expected: PASS — prints the `{n_sat} sat / {n_unsat} unsat / … 0 disagreements` line with `n_sat > 0`, `n_unsat > 0`, `n_witness > 0`.

> Requires `z3` on PATH (via mise). If z3 is unavailable the feature-gated test is skipped by the build config — arrange the toolchain per `mise.toml` before running.

- [ ] **Step 4: Run the whole oracle suite (existing families untouched)**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture`
Expected: PASS — `qfs_matches_z3`, `qfs_predicates_matches_z3`, `qfs_indexof_replace_matches_z3` unchanged (their seeds/iters were not touched), plus the new family green.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_replace_all_matches_z3 differential oracle family (slice 14)"
```

---

### Task 7: Spec truth-up + full workspace verification

**Files:**
- Modify: `docs/superpowers/specs/2026-07-10-shinri-slice14-str-replace-all-design.md` (Status → IMPLEMENTED + oracle stats)

**Interfaces:** none (documentation + verification).

- [ ] **Step 1: Run the full workspace test suite**

Run: `cargo test --workspace`
Expected: PASS — all crates green, zero failures.

- [ ] **Step 2: Run clippy (lint gate)**

Run: `cargo clippy --workspace --all-targets -- -D warnings`
Expected: PASS — no warnings.

- [ ] **Step 3: Update the spec Status block**

In `docs/superpowers/specs/2026-07-10-shinri-slice14-str-replace-all-design.md`, change the `Status:` line to `IMPLEMENTED (slice 14 landed 2026-07-10)` and append a one-line note recording the observed oracle stats from Task 6 Step 3 (the printed `{n_sat} sat / {n_unsat} unsat / … 0 disagreements @ 200 iters` line). Match the truth-up style of the slice-13 spec's Status block.

- [ ] **Step 4: Commit**

```bash
git add docs/superpowers/specs/2026-07-10-shinri-slice14-str-replace-all-design.md
git commit -m "docs: slice-14 spec truth-up — status IMPLEMENTED + oracle stats (slice 14)"
```

- [ ] **Step 5: Push the branch and open a PR**

```bash
git push -u origin slice14-str-replace-all
gh pr create --title "Slice 14: str.replace_all (fold + partial-eval + fence)" \
  --body "Adds str.replace_all as a value-sorted function: folds all-literal applications, partial-evals literal-haystack + symbolic-u into an N-way non-overlapping concat (capped at 64 occurrences), fences symbolic haystack/needle to sound Unknown. New differential oracle family qfs_replace_all_matches_z3 (fresh seed, 0-disagreement gate @ 200 iters). Mirrors slice 13's str.replace half; empty-needle drops u (contrast str.replace)."
```

---

## Self-Review

**Spec coverage:**
- §1 Surface changes (core op + sort rule) → Task 1; (parser + printer) → Task 2. ✓
- §2 Pre-pass: `nonoverlapping_occurrences` + `eval_replace_all` → Task 3; `rewrite_replace_all` fold path → Task 3; symbolic-`u` concat + `REPLACE_ALL_CONCAT_CAP` + fence-walk wiring → Task 3/4. ✓
- §3 Fence / solver wiring (`is_string_op`, no new lib.rs stage) → Task 5. ✓
- §4 Testing: unit → Tasks 3-4; e2e pins + canaries → Task 5; differential oracle family → Task 6. ✓
- §5 Out of scope (symbolic haystack/needle fenced; no regex) → covered by fence tests in Tasks 4-5; regex not implemented. ✓
- Risks R1 (empty-needle trap) → `folds_empty_needle_replace_all_drops_u` + e2e contrast; R2 (overlap) → `nonoverlapping_*`, `eval_replace_all`, `"aaa"/"aa"→"Xa"` e2e; R3 (repeated-var completeness) → cap + unknown-tolerant oracle. ✓

**Placeholder scan:** No TBD/TODO/"add error handling"/"similar to Task N". Every code step shows complete code. ✓

**Type consistency:** `nonoverlapping_occurrences(&[char], &[char]) -> Vec<usize>`, `eval_replace_all(&[char], &[char], &str) -> String`, `rewrite_replace_all(&mut Context, &[TermId]) -> Option<TermId>`, `REPLACE_ALL_CONCAT_CAP: usize = 64`, `gen_replace_all_body(u64) -> String`, seed `0x51_4A_0000_0001` — used consistently across Tasks 3-6. The `rewrite` `special` arm and `has_unreduced_indexof_replace` `matches!` both reference `BuiltinOp::StrReplaceAll` from Task 1. ✓
