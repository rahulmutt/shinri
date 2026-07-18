# Slice 30 — Constant-Word Lexicographic Order — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generalize `shinri-str`'s single-character constant `str.<`/`str.<=` rewrite to any-length constant words, so a comparison against a multi-char literal decides end-to-end instead of fencing to `Unknown`.

**Architecture:** Pure preprocessing rewrite in `crates/shinri-str/src/order.rs`. Lexicographic comparison against a fixed word `w` is a regular language; replace the atom with `(str.in_re s R)` and let the existing membership engine decide. No word-equation engine, no `Fuel` change, no fresh vars, no polarity fence — the exact slice-24 mold. The two-free-var symbolic-pair case stays fenced (banked hard core).

**Tech Stack:** Rust; `cargo nextest`; z3 (via `mise`) for the oracle differential tier.

## Global Constraints

- **Pure-Rust mandate:** no native-link deps (`deny.toml` bans `rug`, `z3-sys`, …). This slice adds none.
- **`cargo fmt --all` before pushing** — CI gates on `fmt --check` and fails fast; subagents do not auto-format.
- **`cargo clippy --workspace --all-targets -- -D warnings`** must be clean.
- **Oracle differential tests are feature-gated:** `crates/shinri-solver/tests/qfs_differential.rs` is `#![cfg(feature = "oracle")]`. Run with `cargo nextest run -p shinri-solver --features oracle`. **Without `--features oracle` the whole file silently runs 0 tests** — never report that as green. The `expect()` helper cross-checks z3, so it also needs the feature and `z3` on PATH.
- **`shinri-str` unit tests are NOT oracle-gated** — run with `cargo nextest run -p shinri-str`.
- Alphabet fences: `MAX_CODE = 0x2FFFF`; surrogate block `0xD800..=0xDFFF` (only the edges `0xD800`/`0xDFFF` are expressible as `Range` endpoints — `range_rex` returns `None` on an interior surrogate).
- Regex helper contracts (all already imported in `order.rs` via `use crate::regex::{concat, range_rex, rex_to_term, star, union, Rex, MAX_CODE};`):
  - `concat(Vec<Rex>) -> Rex` — flattens, drops `Eps`, short-circuits `Empty`, folds len-1.
  - `union(Vec<Rex>) -> Rex` — coalesces `Range` members first, then non-range members in first-appearance order (deduped), folds len-1, empty ⇒ `Empty`.
  - `range_rex(lo: i128, hi: i128) -> Option<Rex>` — `lo > hi ⇒ Some(Empty)`; interior surrogate endpoint ⇒ `None`; else `Some(Range(lo,hi))`.
  - `star(Rex) -> Rex`; `Rex::{Empty, Eps, Range(u32,u32), Concat, Union, Star}`.

---

### Task 1: Constant-word rewrite + unit tests (`order.rs`)

**Files:**
- Modify: `crates/shinri-str/src/order.rs` (replace `single_char_code`; generalize `order_const_right`/`order_const_left`; update the two constant arms of `try_order_atom`; add `word_rex` + `ORDER_CONST_LEN_CAP`)
- Test: `crates/shinri-str/src/order.rs` (`#[cfg(test)] mod tests` at the bottom of the same file)

**Interfaces:**
- Consumes: existing `sigma()`, `sigma_star()`, `membership(ctx, TermId, Rex)`, and the imported regex helpers above.
- Produces (all private to `order.rs`):
  - `const ORDER_CONST_LEN_CAP: usize = 256;`
  - `fn word_codes(s: &str) -> Option<Vec<i128>>`
  - `fn word_rex(cs: &[i128]) -> Rex`
  - `fn order_const_right(ctx: &mut Context, s: TermId, cs: &[i128], reflexive: bool) -> Option<TermId>`
  - `fn order_const_left(ctx: &mut Context, s: TermId, cs: &[i128], reflexive: bool) -> Option<TermId>`

---

- [ ] **Step 1: Flip the fence unit test to expect a rewrite (failing test)**

In `crates/shinri-str/src/order.rs`, replace the existing test `multi_char_const_right_survives_to_fence` (currently asserting `(str.< s "bc")` survives to the fence) with:

```rust
    #[test]
    fn multi_char_const_right_now_rewrites() {
        // Slice 30: a length-≥2 constant on the RIGHT now rewrites to membership
        // (was fenced pre-slice-30). (str.< s "bc") ≡
        //   s ∈ Eps ∪ "b" ∪ Range(0,'a')·Σ* ∪ "b"·Range(0,'b')·Σ*.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let bc = ctx.mk_string_const("bc"); // codes 98, 99
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, bc);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        let want_lang = union(vec![
            Rex::Eps,           // proper prefix j=0 (ε)
            Rex::Range(98, 98), // proper prefix j=1 ("b")
            concat(vec![Rex::Range(0, 97), star(Rex::Range(0, MAX_CODE))]), // differ i=0
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(0, 98),
                star(Rex::Range(0, MAX_CODE)),
            ]), // differ i=1: "b"·Range(0,'b')·Σ*
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));

        // (str.<= s "bc") additionally admits the word "bc" itself.
        let le = order(&mut ctx, BuiltinOp::StrLeq, s, bc);
        let out = rewrite_str_order(&mut ctx, &[le]);
        let want_lang = union(vec![
            Rex::Eps,
            Rex::Range(98, 98),
            concat(vec![Rex::Range(0, 97), star(Rex::Range(0, MAX_CODE))]),
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(0, 98),
                star(Rex::Range(0, MAX_CODE)),
            ]),
            concat(vec![Rex::Range(98, 98), Rex::Range(99, 99)]), // word "bc"
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
    }
```

- [ ] **Step 2: Run it to confirm it fails**

Run: `cargo nextest run -p shinri-str order::tests::multi_char_const_right_now_rewrites`
Expected: FAIL — the current code returns `None` for a multi-char constant, so the atom survives and `out == vec![lt]`, not the membership term.

- [ ] **Step 3: Add the cap constant and `word_codes`**

In `order.rs`, add near the top of the module (after the imports) the cap, and **replace** `fn single_char_code` with `fn word_codes`:

```rust
/// Max constant-word length that gets the order→membership rewrite. A length-k
/// word builds an O(k)-branch regex; SMT-LIB literal text is untrusted input
/// (threat model), so cap the blow-up. Above the cap ⇒ fence (sound Unknown).
/// Mirrors `regex::ENUM_WORD_CAP`.
const ORDER_CONST_LEN_CAP: usize = 256;

/// The code points of a constant word, each within the SMT-LIB alphabet, or
/// `None` if the word is empty, contains a char above `MAX_CODE`, or exceeds
/// `ORDER_CONST_LEN_CAP` (all of which fall through to the fence — sound
/// Unknown, never wrong). Generalizes slice 24's `single_char_code` to any
/// length; the k=1 result reproduces the single-char arms exactly.
fn word_codes(s: &str) -> Option<Vec<i128>> {
    if s.is_empty() || s.chars().count() > ORDER_CONST_LEN_CAP {
        return None;
    }
    s.chars()
        .map(|c| ((c as u32) <= MAX_CODE).then_some(c as u32 as i128))
        .collect()
}
```

(The empty-string guard never fires in practice — the empty-boundary arms of `try_order_atom` match first — but keeps `word_codes` total, so `order_const_*` never see a zero-length `cs`.)

- [ ] **Step 4: Add `word_rex` and generalize the two constant builders**

In `order.rs`, add `word_rex` and **replace** the bodies of `order_const_right` and `order_const_left` (change their signatures from `m: i128` to `cs: &[i128]`):

```rust
/// The exact-word language `word(w) = Range(c₀,c₀)·…·Range(c_{k-1},c_{k-1})`
/// as a `Rex` (empty slice ⇒ `Eps`). Every code is in-alphabet (guaranteed by
/// `word_codes`), so each `Range` is expressible.
fn word_rex(cs: &[i128]) -> Rex {
    concat(cs.iter().map(|&c| Rex::Range(c as u32, c as u32)).collect())
}

/// `(str.< s w)` / `(str.<= s w)` for a constant word `w` (codes `cs`, k = |w| ≥ 1)
/// and symbolic `s`. `reflexive` = the `<=` case (adds the word `w` itself).
///
/// `s <  w` ≡ s ∈  ⋃_{j<k} word(w[0..j])                      (proper prefixes: ε, w[0..1], …)
///                ∪ ⋃_{i<k} word(w[0..i])·Range(0, cᵢ-1)·Σ*   (first differ at i, sᵢ < cᵢ)
/// `s <= w` ≡  … ∪ word(w)                                    (… or s = w)
///
/// k = 1 reproduces slice 24's `Eps ∪ Range(0,c₀-1)·Σ*` (+ word for `<=`).
/// `None` only if a `range_rex` interior endpoint is an inexpressible surrogate
/// — unreachable for an in-alphabet word (a valid char's neighbour is at worst a
/// block edge), but propagated for totality.
fn order_const_right(ctx: &mut Context, s: TermId, cs: &[i128], reflexive: bool) -> Option<TermId> {
    let mut branches: Vec<Rex> = Vec::new();
    for j in 0..cs.len() {
        branches.push(word_rex(&cs[..j])); // proper prefix (j = 0 ⇒ Eps)
    }
    for i in 0..cs.len() {
        branches.push(concat(vec![
            word_rex(&cs[..i]),
            range_rex(0, cs[i] - 1)?,
            sigma_star(),
        ]));
    }
    if reflexive {
        branches.push(word_rex(cs)); // word(w)
    }
    Some(membership(ctx, s, union(branches)))
}

/// `(str.< w s)` / `(str.<= w s)` for a constant word `w` (codes `cs`, k ≥ 1)
/// and symbolic `s`. `reflexive` = the `<=` case.
///
/// `w <  s` ≡ s ∈  ⋃_{i<k} word(w[0..i])·Range(cᵢ+1, MAX)·Σ*  (first differ at i, sᵢ > cᵢ)
///                ∪ word(w)·Σ·Σ*                              (w a PROPER prefix of s)
/// `w <= s` ≡  ⋃ (differ) ∪ word(w)·Σ*                        (… or w a prefix incl. = w)
///
/// k = 1 reproduces slice 24's `Range(c₀+1,MAX)·Σ* ∪ word(c₀)·(Σ·Σ* | Σ*)`.
fn order_const_left(ctx: &mut Context, s: TermId, cs: &[i128], reflexive: bool) -> Option<TermId> {
    let mut branches: Vec<Rex> = Vec::new();
    for i in 0..cs.len() {
        branches.push(concat(vec![
            word_rex(&cs[..i]),
            range_rex(cs[i] + 1, MAX_CODE as i128)?,
            sigma_star(),
        ]));
    }
    let word_w = word_rex(cs);
    let prefix = if reflexive {
        concat(vec![word_w, sigma_star()]) // word(w)·Σ*
    } else {
        concat(vec![word_w, sigma(), sigma_star()]) // word(w)·Σ·Σ*
    };
    branches.push(prefix);
    Some(membership(ctx, s, union(branches)))
}
```

- [ ] **Step 5: Point `try_order_atom` at the word builders**

In `try_order_atom`, replace the two single-char match arms (the `(None, Some(y))` and `(Some(x), None)` arms that currently call `single_char_code` / `order_const_right` / `order_const_left`) with:

```rust
        // Constant word on the RIGHT: (str.< s w) / (str.<= s w).
        // (Empty y is handled by the empty-boundary arm above, so y is non-empty.)
        (None, Some(y)) => match word_codes(&y) {
            Some(cs) => order_const_right(ctx, a, &cs, reflexive),
            None => None, // above-alphabet char or over cap ⇒ fence
        },
        // Constant word on the LEFT: (str.< w s) / (str.<= w s).
        (Some(x), None) => match word_codes(&x) {
            Some(cs) => order_const_left(ctx, b, &cs, reflexive),
            None => None,
        },
        _ => None,
```

- [ ] **Step 6: Run the flipped test — now passes**

Run: `cargo nextest run -p shinri-str order::tests::multi_char_const_right_now_rewrites`
Expected: PASS.

- [ ] **Step 7: Run the full `order` test module — single-char k=1 tests unchanged**

Run: `cargo nextest run -p shinri-str order::`
Expected: PASS, including the untouched `single_char_const_right_rewrites`, `single_char_const_left_rewrites`, `single_char_const_right_null_char_collapses_to_empty`, `single_char_const_left_max_char_drops_range_branch`, `above_alphabet_const_survives_to_fence`, `max_code_char_still_decides`, `single_char_const_block_edge_does_not_fence` — the strict-generalization regression guard (k=1 collapses to the old arms).

- [ ] **Step 8: Add the left-side, cap-fence, and block-edge unit tests**

Append to `mod tests` in `order.rs`:

```rust
    #[test]
    fn multi_char_const_left_now_rewrites() {
        // (str.< "bc" s) ≡ s ∈ Range(99,MAX)·Σ* ∪ "b"·Range(100,MAX)·Σ* ∪ "bc"·Σ·Σ*.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let bc = ctx.mk_string_const("bc"); // codes 98, 99
        let lt = order(&mut ctx, BuiltinOp::StrLt, bc, s);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        let want_lang = union(vec![
            concat(vec![Rex::Range(99, MAX_CODE), star(Rex::Range(0, MAX_CODE))]), // differ i=0
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(100, MAX_CODE),
                star(Rex::Range(0, MAX_CODE)),
            ]), // differ i=1
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(99, 99),
                Rex::Range(0, MAX_CODE),
                star(Rex::Range(0, MAX_CODE)),
            ]), // "bc"·Σ·Σ*
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn const_word_over_cap_survives_to_fence() {
        // A constant word longer than ORDER_CONST_LEN_CAP is banked ⇒ fence.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let long = ctx.mk_string_const(&"a".repeat(ORDER_CONST_LEN_CAP + 1));
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, long);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        assert_eq!(out, vec![lt]);
        assert!(has_unreduced_str_order(&ctx, &out));
        // Exactly at the cap still rewrites (does not fence).
        let at = ctx.mk_string_const(&"a".repeat(ORDER_CONST_LEN_CAP));
        let lt2 = order(&mut ctx, BuiltinOp::StrLt, s, at);
        let out2 = rewrite_str_order(&mut ctx, &[lt2]);
        assert!(
            !has_unreduced_str_order(&ctx, &out2),
            "at-cap word must rewrite"
        );
    }

    #[test]
    fn const_word_block_edge_interior_does_not_fence() {
        // Multi-char word with a char at the surrogate block boundary: the interior
        // class Range(0, 0xE000-1) = Range(0, 0xDFFF) is a block EDGE (expressible),
        // so the word rewrites without fencing (generalizes
        // single_char_const_block_edge_does_not_fence to an interior position).
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let w = ctx.mk_string_const("\u{E000}b"); // codes 0xE000, 98
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, w);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        assert!(
            !has_unreduced_str_order(&ctx, &out),
            "block-edge interior must not fence"
        );
    }
```

- [ ] **Step 9: Run the full `order` module + fmt + clippy**

Run: `cargo nextest run -p shinri-str order::`
Expected: PASS (all old + 4 new/flipped tests).
Run: `cargo fmt --all && cargo clippy -p shinri-str --all-targets -- -D warnings`
Expected: no diff from fmt, 0 clippy warnings.

- [ ] **Step 10: Commit**

```bash
git add crates/shinri-str/src/order.rs
git commit -m "feat(str): slice30 — constant-word lexicographic order rewrite

Generalize order_const_right/left from a single-char constant to any-length
constant word (reduce str.</str.<= vs a fixed word to regex membership).
word_codes replaces single_char_code; ORDER_CONST_LEN_CAP=256 fences over-long
untrusted literals. k=1 collapses to slice 24's arms (single-char tests
unchanged). Two-free-var symbolic pair still fenced."
```

---

### Task 2: Targeted e2e decision pins (`qfs_differential.rs`)

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (add one targeted test near the other `targeted_str_order_*` pins, ~line 3900–3960)

**Interfaces:**
- Consumes: `expect(src: &str, want: Verdict)` (asserts shinri's verdict AND cross-checks z3 when `want != Unknown`), `Verdict::{Sat, Unsat}`.
- Produces: nothing consumed downstream.

- [ ] **Step 1: Add the constant-word decision pins**

Insert after `targeted_str_order_symbolic_pair_known_gap` (the two-free-var pin, which stays **unchanged** as the non-regression that this slice does *not* cash the symbolic pair):

```rust
/// Slice 30: constant-word (length ≥ 2) lexicographic comparison against a
/// symbolic var now DECIDES end-to-end (generalizes slice 24's single-char
/// arms; was fenced to Unknown). z3 cross-checked by `expect`.
#[test]
fn targeted_str_order_const_word_decides() {
    // Right constant, strict — "bd" ≮ "bc" (differ at pos 1, 'd' > 'c').
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.< s \"bc\"))(assert (= s \"bd\"))(check-sat)",
        Verdict::Unsat,
    );
    // Right constant, decided Sat — "az" < "bc" ('a' < 'b' at pos 0).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.< s \"bc\"))(assert (= s \"az\"))(check-sat)",
        Verdict::Sat,
    );
    // Left constant, strict — "bc" ≮ "ba" (differ at pos 1, 'c' > 'a').
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.< \"bc\" s))(assert (= s \"ba\"))(check-sat)",
        Verdict::Unsat,
    );
    // Left constant, proper-prefix Sat — "bc" < "bca".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.< \"bc\" s))(assert (= s \"bca\"))(check-sat)",
        Verdict::Sat,
    );
    // `<=` admits equality — s = "bc" satisfies (str.<= s "bc") …
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.<= s \"bc\"))(assert (= s \"bc\"))(check-sat)",
        Verdict::Sat,
    );
    // … but strict `<` excludes it.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.< s \"bc\"))(assert (= s \"bc\"))(check-sat)",
        Verdict::Unsat,
    );
}
```

- [ ] **Step 2: Run the targeted pins under the oracle feature (foreground, captured)**

Run: `cargo nextest run -p shinri-solver --features oracle qfs_differential::targeted_str_order_const_word_decides --no-capture`
Expected: PASS — shinri and z3 agree on all six.

- [ ] **Step 3: Confirm the two-free-var non-regression still holds**

Run: `cargo nextest run -p shinri-solver --features oracle qfs_differential::targeted_str_order_symbolic_pair_known_gap`
Expected: PASS — `(str.< s u)` over two free vars still returns `Unknown` (this slice does not cash it; it remains the oldest live `_known_gap` pin).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): slice30 e2e pins — constant-word order decides both polarities

Six z3-cross-checked pins (right/left constant, </<=, Sat+Unsat, proper-prefix,
equality boundary). Two-free-var symbolic_pair_known_gap left unchanged as the
non-regression that slice 30 does not cash the symbolic pair."
```

---

### Task 3: Oracle differential family (`qfs_differential.rs`)

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (add `Gen::finish_str_order_const_word`; add `gen_str_order_const_word_body` + the `qfs_str_order_const_word_matches_z3` family, after the slice-24 single-char family ~line 2541)

**Interfaces:**
- Consumes: `Gen` (`self.var()`, `self.rng.below(n)`, `self.body`), `ALPHABET` (`&["a","b","c"]`), `Lcg`, `shinri_lines_counting_bailouts`, `z3_verdict`, `Verdict`.
- Produces: nothing consumed downstream (a `#[test]`).

**Note (deliberate refinement of spec §4):** the spec said "extend the `qfs_str_order_matches_z3` generator." A dedicated multi-char family — mirroring slice 24's `qfs_str_order_single_char_matches_z3` exactly — is the house pattern (one family per decided fragment) and gives forced Sat+Unsat coverage the general family cannot target. The general family *also* shows unknowns-down for free, because its `lit()` already emits 2-char literals that now decide; that is a bonus signal, not the primary check.

- [ ] **Step 1: Add the multi-char generator body on `Gen`**

Add this method in the `impl Gen { … }` block, next to `finish_str_order_single_char`:

```rust
    /// A conjunction of MULTI-char-constant-vs-symbolic `str.<` / `str.<=` atoms
    /// (constant on either side, length 2–4), plus a forcing equality/length
    /// constraint on a symbolic var to drive both Sat and Unsat — slice 30's
    /// decided fragment. ASCII-only (z3-CLI byte-parse safety); some atoms
    /// negated. Mirrors `finish_str_order_single_char` with longer literals.
    fn finish_str_order_const_word(mut self) -> String {
        // A 2–4 char ASCII constant literal (quoted), drawn from ALPHABET.
        fn word(g: &mut Gen) -> String {
            let k = 2 + g.rng.below(3); // 2..=4
            let mut s = String::new();
            for _ in 0..k {
                s.push_str(ALPHABET[g.rng.below(ALPHABET.len() as u64) as usize]);
            }
            format!("\"{s}\"")
        }
        let n_atoms = 1 + self.rng.below(2); // 1..=2
        for _ in 0..n_atoms {
            let op = if self.rng.below(2) == 0 {
                "str.<"
            } else {
                "str.<="
            };
            let v = self.var();
            let c = word(&mut self);
            let atom = if self.rng.below(2) == 0 {
                format!("({op} {v} {c})") // constant on the right
            } else {
                format!("({op} {c} {v})") // constant on the left
            };
            let atom = if self.rng.below(4) == 0 {
                format!("(not {atom})")
            } else {
                atom
            };
            self.body.push_str(&format!("(assert {atom})\n"));
        }
        // Force decisions on a symbolic var (some SAT, some UNSAT).
        let v = self.var();
        match self.rng.below(3) {
            0 => {
                let c = word(&mut self);
                self.body.push_str(&format!("(assert (= {v} {c}))\n"));
            }
            1 => {
                let k = self.rng.below(4);
                self.body
                    .push_str(&format!("(assert (= (str.len {v}) {k}))\n"));
            }
            _ => {}
        }
        self.body
    }
```

- [ ] **Step 2: Add the differential family**

Add after the slice-24 single-char family block (after `qfs_str_order_single_char_matches_z3`):

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 30: constant-word (length 2–4) str.< / str.<= vs a symbolic var
// ─────────────────────────────────────────────────────────────────────────────

fn gen_str_order_const_word_body(seed: u64) -> String {
    Gen::new(seed).finish_str_order_const_word()
}

const SOCW_SEED: u64 = 0x53_00_0000_0005;
const SOCW_N_ITERS: usize = 200;

#[test]
fn qfs_str_order_const_word_matches_z3() {
    let mut rng = Lcg(SOCW_SEED);
    let (mut n_sat, mut n_unsat, mut n_shinri_unknown, mut n_z3_unknown, mut n_guard_bailouts) =
        (0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..SOCW_N_ITERS {
        let seed = rng.next();
        let body = gen_str_order_const_word_body(seed);

        let (lines, bailouts) = shinri_lines_counting_bailouts(&format!("{body}(check-sat)\n"));
        if bailouts > 0 {
            n_guard_bailouts += 1;
            continue;
        }
        let ours = match lines.first().map(String::as_str) {
            Some("sat") => Verdict::Sat,
            Some("unsat") => Verdict::Unsat,
            _ => Verdict::Unknown,
        };
        if ours == Verdict::Unknown {
            n_shinri_unknown += 1;
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3_unknown += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S STR_ORDER CONST-WORD SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{body}(check-sat)"
        );
        match ours {
            Verdict::Sat => n_sat += 1,
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    println!(
        "qfs_str_order_const_word_matches_z3: {SOCW_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_shinri_unknown} shinri-unknown / {n_z3_unknown} z3-unknown / {n_guard_bailouts} guard-bailout; \
         0 disagreements"
    );
    assert!(
        n_sat > 0,
        "const-word str-order family produced zero SAT instances"
    );
    assert!(
        n_unsat > 0,
        "const-word str-order family produced zero UNSAT instances"
    );
}
```

- [ ] **Step 3: Run the new family foreground with captured output**

Run: `cargo nextest run -p shinri-solver --features oracle qfs_differential::qfs_str_order_const_word_matches_z3 --no-capture`
Expected: PASS — prints `… sat / … unsat / … shinri-unknown / … z3-unknown / … guard-bailout; 0 disagreements`, with `n_sat > 0` and `n_unsat > 0`. **0 disagreements is the soundness gate.**

- [ ] **Step 4: Run the sibling order families — tallies must not regress**

Run: `cargo nextest run -p shinri-solver --features oracle qfs_str_order --no-capture`
Expected: PASS for `qfs_str_order_matches_z3`, `qfs_str_order_single_char_matches_z3`, and the new family — **0 disagreements** everywhere. In `qfs_str_order_matches_z3` the `shinri-unknown` count should be **lower** than pre-slice-30 (its 2-char `lit()` comparisons now decide); that drop is expected, not a regression. Any *disagreement* is a finding to adjudicate.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): slice30 oracle family — constant-word order vs z3

New qfs_str_order_const_word_matches_z3 (2–4 char constants either side, forced
Sat+Unsat), mirroring the slice-24 single-char family. 0 disagreements; the
general str_order family's shinri-unknown count drops as 2-char lits now decide."
```

---

### Task 4: Oracle dump-and-diff, full gate, truth-up, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-07-18-shinri-slice30-const-word-order-design.md` (append an "Implementation notes (truth-up)" section, matching the slice-29 spec's closing section)

**Interfaces:** none (verification + docs + merge).

- [ ] **Step 1: Verdict-monotonicity dump-and-diff (base vs fix)**

The soundness invariant (spec §3): every flip is `Unknown → decided`; **zero** `decided → Unknown`, **zero** `sat ↔ unsat`. Capture both sides with `--no-capture` (**required** — Rust's harness swallows `eprintln!`/`DIFFDUMP` from passing tests otherwise; a run can pass 0/0 yet print 0 dump lines):

```bash
BASE=$(git rev-parse HEAD~3)   # the commit before Task 1 (spec/plan tip)
FIX=$(git rev-parse HEAD)
SP="/tmp/claude-1000/-workspace/925fe2ea-1a8c-4507-9a5b-b728fe61f63e/scratchpad"
# If this repo's qfs_differential emits DIFFDUMP lines only under an env flag,
# set it here (grep the file for DIFFDUMP to confirm the exact var); then:
git stash --include-untracked  # park the working tree if needed
git checkout "$BASE" && cargo nextest run -p shinri-solver --features oracle qfs_str_order --no-capture 2>&1 | tee "$SP/base.txt"
git checkout "$FIX"  && cargo nextest run -p shinri-solver --features oracle qfs_str_order --no-capture 2>&1 | tee "$SP/fix.txt"
```

Compare the printed tallies (base vs fix) for the three `qfs_str_order*` families. Expected: `shinri-unknown` **down** in `qfs_str_order_matches_z3`; new family `n_sat>0`/`n_unsat>0`; **0 disagreements** on both sides. If the file has a per-iteration src-hash-keyed DIFFDUMP recipe (as slice 29 used), diff `base.txt` vs `fix.txt` and confirm every hash-keyed flip is `unknown → {sat,unsat}`, none the reverse. Record the numbers for the truth-up.

- [ ] **Step 2: Full local gate**

Run each and confirm green:

```bash
cargo nextest run -p shinri-str
cargo nextest run -p shinri-solver --features oracle --test qfs_differential --no-capture
cargo nextest run -p shinri-solver --test script_e2e
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --check
```

Expected: `shinri-str` all pass; `qfs_differential` all pass, 0 disagreements; `script_e2e` all pass. Per the standing rule, a completeness-shifting string change *can* flip a `script_e2e` string pin — any z3-confirmed `Unknown → decided` flip is an **adjudicated flip, not a blocker** (slice-25/26/28/29 precedent); investigate and pin-flip if it occurs, and note it in the truth-up. clippy 0 warnings; fmt clean.

- [ ] **Step 3: Write the spec truth-up**

Append an `## Implementation notes (truth-up)` section to the slice-30 spec recording: the commits and what landed as designed; any deviations (e.g. the dedicated-family testing refinement noted in Task 3); the dump-and-diff numbers (flips all `Unknown → decided`, zero regressions); the full-gate results (`shinri-str` N/N, oracle family tallies, `script_e2e` N/N, clippy/fmt); and the explicit note that the two-free-var `_known_gap` pin stays banked and is now the oldest live gap. Mark `Status:` `IMPLEMENTED (2026-07-18)`.

- [ ] **Step 4: Commit the truth-up**

```bash
git add docs/superpowers/specs/2026-07-18-shinri-slice30-const-word-order-design.md
git commit -m "docs: slice30 truth-up"
```

- [ ] **Step 5: Push, open PR, merge on green, delete branch**

```bash
git push -u origin slice30-const-word-order
gh pr create --title "slice30: constant-word lexicographic order" \
  --body "Generalizes slice 24's single-char str.</str.<= constant arms to any-length constant words (pure rewrite to regex membership). Cashes slice 24 §5's multi-char-constant bank. Two-free-var symbolic pair stays banked. See docs/superpowers/specs/2026-07-18-shinri-slice30-const-word-order-design.md."
```

When CI is green, merge with a merge commit, then delete the branch remote + local and prune (standing "merge on green" rule):

```bash
gh pr merge --merge --delete-branch
git checkout main && git pull && git remote prune origin
```

---

## Self-Review

**Spec coverage:**
- §2 construction (right/left, `<`/`<=`, proper-prefix + differ branches, k=1 collapse) → Task 1 Steps 3–5, verified by Steps 1/6/8.
- §2 cap + above-alphabet fence → Task 1 Step 3 (`word_codes`, `ORDER_CONST_LEN_CAP`), tested Step 8 (`const_word_over_cap_survives_to_fence`).
- §3 soundness (no surrogate fence for in-alphabet words) → `const_word_block_edge_interior_does_not_fence` (Task 1 Step 8); verdict-monotonicity → Task 4 Step 1.
- §4 unit tests → Task 1 Steps 1/8; e2e pins (all six routes + non-regression) → Task 2; oracle differential → Task 3; gate list → Task 4 Step 2.
- §6 non-goal (two-free-var stays banked) → Task 2 Step 3 (non-regression pin unchanged) + truth-up note (Task 4 Step 3).

**Placeholder scan:** every code step shows complete code; every run step gives an exact command + expected output. Task 4 Step 1 flags that the exact DIFFDUMP env var / recipe must be confirmed by grepping the file (the repo's mechanism, not inventable here) — the implementer greps `DIFFDUMP` and follows slice 29's recipe; the invariant to check is fully specified.

**Type consistency:** `word_codes -> Option<Vec<i128>>`; `order_const_right`/`order_const_left(ctx, TermId, &[i128], bool) -> Option<TermId>` used consistently in Task 1 Steps 4–5; `word_rex(&[i128]) -> Rex`; `range_rex(i128, i128) -> Option<Rex>` (propagated via `?`); `ORDER_CONST_LEN_CAP: usize`. Generator `finish_str_order_const_word(self) -> String` consumes `self` (matches `finish_str_order_single_char`); family constants `SOCW_SEED`/`SOCW_N_ITERS` unique.
