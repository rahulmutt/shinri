//! Slice 19 pre-pass: `str.in_re` over SMT-LIB regular expressions —
//! ground evaluation by Brzozowski derivatives + presence fence.
//!
//! Decided fragment: `str.in_re(s, R)` where `s` is a string literal and `R`
//! is a CONSTANT regex (every `str.to_re` argument and every `re.range`
//! endpoint is a literal). The atom folds to true/false — evaluation, a full
//! logical equivalence at any polarity, any occurrence count. No model
//! repair, no fresh variables.
//!
//! Stages (run by the solver's string-path seam, right after code_conv):
//! 1. [`rewrite_ground_in_re`] — bottom-up memoized pass folding every ground
//!    membership atom. (Lands in Task 3.)
//! 2. [`has_unreduced_regex`] — presence fence: any surviving `str.in_re`
//!    application or RegLan-sorted subterm ⇒ the solver returns a sound
//!    `Unknown`. The solver additionally fences any query that DECLARES a
//!    RegLan-sorted symbol (`Context::any_fun_sig_mentions`).
//!
//! Above-alphabet fence: Rust literals can hold chars in
//! `0x30000..=0x10FFFF`, outside the SMT-LIB alphabet — if the ground string
//! or a range endpoint contains one, the fold is skipped (→ fence) rather
//! than guessing semantics.

use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// Largest SMT-LIB string character (inclusive): U+2FFFF.
#[allow(dead_code)] // used by Task 2/3's ground-evaluation engine
const MAX_CODE: u32 = 0x2FFFF;

/// Derivative-size fuel: if any intermediate derivative exceeds this many
/// AST nodes the fold is abandoned (→ presence fence → sound Unknown).
#[allow(dead_code)] // used by Task 3's rewrite pass
const FUEL_NODE_CAP: usize = 10_000;

/// Canonical regex AST for ground evaluation. Invariants (enforced by the
/// smart constructors, NEVER by direct construction of compound nodes):
/// - `Range(lo, hi)`: `lo <= hi <= MAX_CODE` where produced from user syntax;
///   derivatives never mint new ranges.
/// - `Concat`/`Union`/`Inter`: >= 2 elements, flattened, no identity/absorber
///   elements; `Union`/`Inter` deduped.
/// - `Star`: argument is not `Empty`/`Eps`/`Star`.
/// - `Comp`: argument is not `Comp`.
/// - `Loop(r, lo, hi)`: `lo <= hi`, `hi >= 1`, `r` not `Empty`/`Eps`.
#[allow(dead_code)] // used by Task 3's rewrite pass
#[derive(Clone, PartialEq, Eq, Debug)]
enum Rex {
    /// ∅ — matches nothing.
    Empty,
    /// {ε} — matches exactly the empty string.
    Eps,
    /// One char with code point in `[lo, hi]` (inclusive).
    Range(u32, u32),
    Concat(Vec<Rex>),
    Union(Vec<Rex>),
    Inter(Vec<Rex>),
    Star(Box<Rex>),
    /// Complement w.r.t. Σ* (Σ = the SMT-LIB alphabet).
    Comp(Box<Rex>),
    /// `r{lo..=hi}` — between lo and hi copies of r.
    Loop(Box<Rex>, u32, u32),
}

#[allow(dead_code)] // used by Task 3's rewrite pass
fn concat(parts: Vec<Rex>) -> Rex {
    let mut out = Vec::new();
    for p in parts {
        match p {
            Rex::Empty => return Rex::Empty,
            Rex::Eps => {}
            Rex::Concat(inner) => out.extend(inner),
            other => out.push(other),
        }
    }
    match out.len() {
        0 => Rex::Eps,
        1 => out.pop().expect("len 1"),
        _ => Rex::Concat(out),
    }
}

#[allow(dead_code)] // used by Task 3's rewrite pass
fn union(parts: Vec<Rex>) -> Rex {
    let mut out: Vec<Rex> = Vec::new();
    for p in parts {
        match p {
            Rex::Empty => {}
            Rex::Union(inner) => {
                for q in inner {
                    if !out.contains(&q) {
                        out.push(q);
                    }
                }
            }
            other => {
                if !out.contains(&other) {
                    out.push(other);
                }
            }
        }
    }
    match out.len() {
        0 => Rex::Empty,
        1 => out.pop().expect("len 1"),
        _ => Rex::Union(out),
    }
}

#[allow(dead_code)] // used by Task 3's rewrite pass
fn inter(parts: Vec<Rex>) -> Rex {
    let mut out: Vec<Rex> = Vec::new();
    for p in parts {
        match p {
            Rex::Empty => return Rex::Empty,
            Rex::Inter(inner) => {
                for q in inner {
                    if !out.contains(&q) {
                        out.push(q);
                    }
                }
            }
            other => {
                if !out.contains(&other) {
                    out.push(other);
                }
            }
        }
    }
    match out.len() {
        // Unreachable from user syntax (arity >= 2, Empty short-circuits),
        // but be safe: the intersection of no languages is Σ*.
        0 => star(Rex::Range(0, MAX_CODE)),
        1 => out.pop().expect("len 1"),
        _ => Rex::Inter(out),
    }
}

#[allow(dead_code)] // used by Task 3's rewrite pass
fn star(r: Rex) -> Rex {
    match r {
        Rex::Empty | Rex::Eps => Rex::Eps,
        s @ Rex::Star(_) => s,
        other => Rex::Star(Box::new(other)),
    }
}

#[allow(dead_code)] // used by Task 3's rewrite pass
fn comp(r: Rex) -> Rex {
    match r {
        Rex::Comp(inner) => *inner,
        other => Rex::Comp(Box::new(other)),
    }
}

#[allow(dead_code)] // used by Task 3's rewrite pass
fn loop_(r: Rex, lo: u32, hi: u32) -> Rex {
    if lo > hi {
        return Rex::Empty;
    }
    if hi == 0 {
        return Rex::Eps; // r{0,0} = ε
    }
    match r {
        // ∅ has no words: ∅{lo..hi} = ε iff lo == 0, else ∅.
        Rex::Empty => {
            if lo == 0 {
                Rex::Eps
            } else {
                Rex::Empty
            }
        }
        Rex::Eps => Rex::Eps,
        other => Rex::Loop(Box::new(other), lo, hi),
    }
}

/// ε ∈ L(r)?
#[allow(dead_code)] // used by Task 3's rewrite pass
fn nullable(r: &Rex) -> bool {
    match r {
        Rex::Empty | Rex::Range(..) => false,
        Rex::Eps | Rex::Star(_) => true,
        Rex::Concat(ps) | Rex::Inter(ps) => ps.iter().all(nullable),
        Rex::Union(ps) => ps.iter().any(nullable),
        Rex::Comp(inner) => !nullable(inner),
        Rex::Loop(inner, lo, _) => *lo == 0 || nullable(inner),
    }
}

/// The Brzozowski derivative of `r` w.r.t. the char with code point `c`:
/// `L(deriv(c, r)) = { w | c·w ∈ L(r) }`. Total — every operator (comp,
/// inter, loop included) has a native rule; no automaton is built.
#[allow(dead_code)] // used by Task 3's rewrite pass
fn deriv(c: u32, r: &Rex) -> Rex {
    match r {
        Rex::Empty | Rex::Eps => Rex::Empty,
        Rex::Range(lo, hi) => {
            if *lo <= c && c <= *hi {
                Rex::Eps
            } else {
                Rex::Empty
            }
        }
        Rex::Concat(ps) => {
            // d(r1·rest) = d(r1)·rest  ∪  (if ε ∈ r1) d(rest)
            let head = &ps[0];
            let rest = concat(ps[1..].to_vec());
            let first = concat(vec![deriv(c, head), rest.clone()]);
            if nullable(head) {
                union(vec![first, deriv(c, &rest)])
            } else {
                first
            }
        }
        Rex::Union(ps) => union(ps.iter().map(|p| deriv(c, p)).collect()),
        Rex::Inter(ps) => inter(ps.iter().map(|p| deriv(c, p)).collect()),
        Rex::Star(inner) => concat(vec![deriv(c, inner), Rex::Star(inner.clone())]),
        Rex::Comp(inner) => comp(deriv(c, inner)),
        Rex::Loop(inner, lo, hi) => {
            // Consume one char from `inner`; the remainder completes `inner`,
            // then loops lo-1..hi-1 more times (hi >= 1 by the invariant).
            // Bounds decrement lazily — huge hi costs nothing.
            let tail = loop_((**inner).clone(), lo.saturating_sub(1), hi - 1);
            concat(vec![deriv(c, inner), tail])
        }
    }
}

#[allow(dead_code)] // used by Task 3's rewrite pass
fn node_count(r: &Rex) -> usize {
    1 + match r {
        Rex::Empty | Rex::Eps | Rex::Range(..) => 0,
        Rex::Concat(ps) | Rex::Union(ps) | Rex::Inter(ps) => ps.iter().map(node_count).sum(),
        Rex::Star(i) | Rex::Comp(i) | Rex::Loop(i, ..) => node_count(i),
    }
}

/// Ground membership by |s| derivative steps + nullability. `None` iff an
/// intermediate derivative exceeds `cap` nodes (→ caller fences).
#[allow(dead_code)] // used by Task 3's rewrite pass
fn eval_membership_capped(s: &str, r: &Rex, cap: usize) -> Option<bool> {
    let mut cur = r.clone();
    for c in s.chars() {
        cur = deriv(c as u32, &cur);
        if node_count(&cur) > cap {
            return None;
        }
    }
    Some(nullable(&cur))
}

#[allow(dead_code)] // used by Task 3's rewrite pass
fn eval_membership(s: &str, r: &Rex) -> Option<bool> {
    eval_membership_capped(s, r, FUEL_NODE_CAP)
}

/// Presence fence: true iff any `str.in_re` application or RegLan-sorted
/// subterm survives in `assertions`. Any hit ⇒ sound `Unknown`.
pub fn has_unreduced_regex(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        if ctx.sort_of(t) == ctx.reglan_sort() {
            return true;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrInRe))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A nullary uninterpreted constant of the given sort (codebase pattern).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn in_re(ctx: &mut Context, s: TermId, r: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, r])
            .unwrap()
    }

    fn to_re(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToRe), &[s]).unwrap()
    }

    #[test]
    fn fence_detects_in_re_and_reglan_subterms() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let re_s = ctx.reglan_sort();
        let s = nullary(&mut ctx, "s", str_s);

        // str.in_re app → fenced.
        let lit = ctx.mk_string_const("a");
        let r = to_re(&mut ctx, lit);
        let atom = in_re(&mut ctx, s, r);
        assert!(has_unreduced_regex(&ctx, &[atom]));

        // Bare RegLan equality → fenced (RegLan-sorted subterms).
        let rv = nullary(&mut ctx, "r", re_s);
        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let eq = ctx.mk_eq(rv, none).unwrap();
        assert!(has_unreduced_regex(&ctx, &[eq]));

        // Plain string assertion → NOT fenced.
        let b = ctx.mk_string_const("b");
        let seq = ctx.mk_eq(s, b).unwrap();
        assert!(!has_unreduced_regex(&ctx, &[seq]));
    }

    // ── Task 2: pure derivative engine ───────────────────────────────────

    /// (regex, string, expected membership) — one row per operator + the
    /// boundary lattice from the spec.
    fn chr(c: char) -> Rex {
        Rex::Range(c as u32, c as u32)
    }

    fn lit(s: &str) -> Rex {
        concat(s.chars().map(chr).collect())
    }

    #[test]
    fn smart_constructors_canonicalize() {
        // Concat: Empty absorbs, Eps drops, nested flattens, 0/1-ary collapse.
        assert_eq!(concat(vec![lit("a"), Rex::Empty]), Rex::Empty);
        assert_eq!(concat(vec![Rex::Eps, Rex::Eps]), Rex::Eps);
        assert_eq!(concat(vec![Rex::Eps, chr('a')]), chr('a'));
        assert_eq!(
            concat(vec![concat(vec![chr('a'), chr('b')]), chr('c')]),
            Rex::Concat(vec![chr('a'), chr('b'), chr('c')])
        );
        // Union: Empty drops, duplicates dedupe, nested flattens.
        assert_eq!(union(vec![Rex::Empty, chr('a')]), chr('a'));
        assert_eq!(union(vec![chr('a'), chr('a')]), chr('a'));
        assert_eq!(union(vec![Rex::Empty, Rex::Empty]), Rex::Empty);
        // Inter: Empty annihilates, duplicates dedupe.
        assert_eq!(inter(vec![chr('a'), Rex::Empty]), Rex::Empty);
        assert_eq!(inter(vec![chr('a'), chr('a')]), chr('a'));
        // Star: ∅* = ε* = ε; (r*)* = r*.
        assert_eq!(star(Rex::Empty), Rex::Eps);
        assert_eq!(star(Rex::Eps), Rex::Eps);
        assert_eq!(star(star(chr('a'))), star(chr('a')));
        // Comp: comp(comp(r)) = r.
        assert_eq!(comp(comp(chr('a'))), chr('a'));
        // Loop: lo > hi = ∅; r{0,0} = ε; ∅{0,k} = ε; ∅{1,k} = ∅.
        assert_eq!(loop_(chr('a'), 3, 2), Rex::Empty);
        assert_eq!(loop_(chr('a'), 0, 0), Rex::Eps);
        assert_eq!(loop_(Rex::Empty, 0, 4), Rex::Eps);
        assert_eq!(loop_(Rex::Empty, 1, 4), Rex::Empty);
    }

    #[test]
    fn nullability_per_operator() {
        assert!(!nullable(&Rex::Empty));
        assert!(nullable(&Rex::Eps));
        assert!(!nullable(&chr('a')));
        assert!(nullable(&star(chr('a'))));
        assert!(!nullable(&concat(vec![chr('a'), star(chr('b'))])));
        assert!(nullable(&union(vec![chr('a'), Rex::Eps])));
        assert!(!nullable(&inter(vec![Rex::Eps, chr('a')])));
        assert!(nullable(&comp(chr('a')))); // "" ∉ {a} ⇒ "" ∈ comp
        assert!(!nullable(&comp(star(chr('a')))));
        assert!(nullable(&loop_(chr('a'), 0, 3)));
        assert!(!nullable(&loop_(chr('a'), 1, 3)));
        assert!(nullable(&loop_(union(vec![chr('a'), Rex::Eps]), 2, 3)));
    }

    #[test]
    fn ground_membership_per_operator() {
        let sigma = Rex::Range(0, MAX_CODE);
        let all = star(sigma.clone());
        let cases: Vec<(Rex, &str, bool)> = vec![
            // to_re / literal word.
            (lit("ab"), "ab", true),
            (lit("ab"), "ba", false),
            (lit(""), "", true),
            (lit(""), "a", false),
            // none / all / allchar.
            (Rex::Empty, "", false),
            (all.clone(), "", true),
            (all.clone(), "xyz", true),
            (sigma.clone(), "a", true),
            (sigma.clone(), "", false),
            (sigma.clone(), "ab", false),
            // concat / union / inter.
            (concat(vec![lit("a"), lit("b")]), "ab", true),
            (union(vec![lit("a"), lit("b")]), "b", true),
            (union(vec![lit("a"), lit("b")]), "c", false),
            (inter(vec![lit("ab"), all.clone()]), "ab", true),
            (inter(vec![lit("a"), lit("b")]), "a", false),
            // star / plus (plus = r·r*) / opt (union with ε).
            (star(lit("ab")), "", true),
            (star(lit("ab")), "ababab", true),
            (star(lit("ab")), "aba", false),
            (concat(vec![lit("a"), star(lit("a"))]), "", false),
            (concat(vec![lit("a"), star(lit("a"))]), "aaa", true),
            (union(vec![lit("a"), Rex::Eps]), "", true),
            // comp / diff (diff = inter with comp).
            (comp(lit("a")), "b", true),
            (comp(lit("a")), "a", false),
            (comp(lit("a")), "", true),
            (comp(Rex::Empty), "", true),
            (comp(Rex::Empty), "anything", true),
            (comp(all.clone()), "x", false),
            (comp(all.clone()), "", false),
            (inter(vec![sigma.clone(), comp(lit("a"))]), "b", true),
            (inter(vec![sigma.clone(), comp(lit("a"))]), "a", false),
            // range (incl. equal endpoints).
            (Rex::Range('a' as u32, 'c' as u32), "b", true),
            (Rex::Range('a' as u32, 'c' as u32), "d", false),
            (Rex::Range('a' as u32, 'a' as u32), "a", true),
            (Rex::Range('a' as u32, 'a' as u32), "b", false),
            // loop / pow.
            (loop_(lit("a"), 1, 2), "a", true),
            (loop_(lit("a"), 1, 2), "aa", true),
            (loop_(lit("a"), 1, 2), "aaa", false),
            (loop_(lit("a"), 1, 2), "", false),
            (loop_(lit("a"), 0, 2), "", true),
            (loop_(lit("ab"), 2, 2), "abab", true),
            (loop_(lit("ab"), 2, 2), "ab", false),
            // huge lazy bounds cost nothing.
            (loop_(lit("a"), 0, u32::MAX), "aaaa", true),
        ];
        for (rex, s, want) in cases {
            assert_eq!(
                eval_membership(s, &rex),
                Some(want),
                "membership of {s:?} in {rex:?}"
            );
        }
    }

    #[test]
    fn fuel_cap_aborts_instead_of_diverging() {
        // A tiny cap forces an abort on a regex whose derivative grows.
        let r = inter(vec![
            star(union(vec![lit("aa"), lit("aaa")])),
            star(union(vec![lit("aa"), lit("aaa")])),
            comp(star(lit("aaaa"))),
        ]);
        assert_eq!(eval_membership_capped("aaaaaaaa", &r, 1), None);
        // The real cap decides this easily (and correctly).
        assert!(eval_membership("aaaaaaaa", &r).is_some());
    }
}
