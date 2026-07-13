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

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// Largest SMT-LIB string character (inclusive): U+2FFFF.
const MAX_CODE: u32 = 0x2FFFF;

/// Derivative-size fuel: if any intermediate derivative exceeds this many
/// AST nodes the fold is abandoned (→ presence fence → sound Unknown).
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

fn star(r: Rex) -> Rex {
    match r {
        Rex::Empty | Rex::Eps => Rex::Eps,
        s @ Rex::Star(_) => s,
        other => Rex::Star(Box::new(other)),
    }
}

fn comp(r: Rex) -> Rex {
    match r {
        Rex::Comp(inner) => *inner,
        other => Rex::Comp(Box::new(other)),
    }
}

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

fn node_count(r: &Rex) -> usize {
    1 + match r {
        Rex::Empty | Rex::Eps | Rex::Range(..) => 0,
        Rex::Concat(ps) | Rex::Union(ps) | Rex::Inter(ps) => ps.iter().map(node_count).sum(),
        Rex::Star(i) | Rex::Comp(i) | Rex::Loop(i, ..) => node_count(i),
    }
}

/// Ground membership by |s| derivative steps + nullability. `None` iff an
/// intermediate derivative exceeds `cap` nodes (→ caller fences).
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

fn eval_membership(s: &str, r: &Rex) -> Option<bool> {
    eval_membership_capped(s, r, FUEL_NODE_CAP)
}

/// A literal word as a Rex (concat of single-char ranges). None if any char
/// is above the SMT-LIB alphabet (→ fence).
fn lit_to_rex(s: &str) -> Option<Rex> {
    let mut parts = Vec::new();
    for c in s.chars() {
        let code = c as u32;
        if code > MAX_CODE {
            return None;
        }
        parts.push(Rex::Range(code, code));
    }
    Some(concat(parts)) // "" → Eps
}

/// Structural translation of a CONSTANT RegLan term. None on any
/// non-constant leaf (symbolic `str.to_re` argument, non-literal `re.range`
/// endpoint, RegLan variable / non-builtin application) or an
/// above-alphabet literal char (→ fence).
fn extract_const_regex(ctx: &Context, t: TermId) -> Option<Rex> {
    let TermNode::App { op, args, .. } = ctx.term_node(t) else {
        return None;
    };
    let Op::Builtin(b) = *op else {
        return None; // RegLan variable or uninterpreted application.
    };
    let kids: Vec<TermId> = ctx.children(*args).to_vec();
    let sub = |ctx: &Context, ids: &[TermId]| -> Option<Vec<Rex>> {
        ids.iter().map(|&k| extract_const_regex(ctx, k)).collect()
    };
    match b {
        BuiltinOp::StrToRe => lit_to_rex(ctx.string_const_value(kids[0])?),
        BuiltinOp::ReNone => Some(Rex::Empty),
        BuiltinOp::ReAll => Some(star(Rex::Range(0, MAX_CODE))),
        BuiltinOp::ReAllChar => Some(Rex::Range(0, MAX_CODE)),
        BuiltinOp::ReConcat => Some(concat(sub(ctx, &kids)?)),
        BuiltinOp::ReUnion => Some(union(sub(ctx, &kids)?)),
        BuiltinOp::ReInter => Some(inter(sub(ctx, &kids)?)),
        BuiltinOp::ReDiff => {
            // Left-associative difference: a \ b \ c = inter(a, comp(b), comp(c)).
            let mut rs = sub(ctx, &kids)?.into_iter();
            let first = rs.next().expect("arity >= 2");
            let mut parts = vec![first];
            for r in rs {
                parts.push(comp(r));
            }
            Some(inter(parts))
        }
        BuiltinOp::ReStar => Some(star(extract_const_regex(ctx, kids[0])?)),
        BuiltinOp::RePlus => {
            // r+ = r · r*.
            let r = extract_const_regex(ctx, kids[0])?;
            Some(concat(vec![r.clone(), star(r)]))
        }
        BuiltinOp::ReOpt => {
            let r = extract_const_regex(ctx, kids[0])?;
            Some(union(vec![r, Rex::Eps]))
        }
        BuiltinOp::ReComp => Some(comp(extract_const_regex(ctx, kids[0])?)),
        BuiltinOp::ReRange => {
            let a = ctx.string_const_value(kids[0])?;
            let b = ctx.string_const_value(kids[1])?;
            let single = |s: &str| -> Option<Option<u32>> {
                // Outer None = fence (above alphabet); inner None = not a
                // single char (⇒ empty range per SMT-LIB).
                let mut it = s.chars();
                match (it.next(), it.next()) {
                    (Some(c), None) => {
                        let code = c as u32;
                        if code > MAX_CODE {
                            None // fence
                        } else {
                            Some(Some(code))
                        }
                    }
                    _ => Some(None), // empty range, decided
                }
            };
            match (single(a)?, single(b)?) {
                (Some(lo), Some(hi)) if lo <= hi => Some(Rex::Range(lo, hi)),
                _ => Some(Rex::Empty), // multi-char endpoint or lo > hi
            }
        }
        BuiltinOp::ReLoop { lo, hi } => Some(loop_(extract_const_regex(ctx, kids[0])?, lo, hi)),
        BuiltinOp::RePow(n) => Some(loop_(extract_const_regex(ctx, kids[0])?, n, n)),
        _ => None, // not a RegLan constructor
    }
}

/// `(str.in_re s R)`, children already rewritten. Some(bool-const) iff the
/// string side is a literal with no above-alphabet chars, `R` extracts as a
/// constant regex, and evaluation stays within fuel.
fn try_fold_in_re(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let s = ctx.string_const_value(kids[0])?.to_owned();
    if s.chars().any(|c| c as u32 > MAX_CODE) {
        return None; // above-alphabet fence
    }
    let rex = extract_const_regex(ctx, kids[1])?;
    let v = eval_membership(&s, &rex)?; // None = fuel → fence
    Some(ctx.mk_const_bool(v))
}

/// Bottom-up memoized pass folding every GROUND `str.in_re` atom to a Bool
/// constant. Untouched subtrees keep their TermIds. Mirrors
/// `code_conv::rewrite_code_conv`.
pub fn rewrite_ground_in_re(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect()
}

fn rewrite(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> =
                children.iter().map(|&c| rewrite(ctx, c, memo)).collect();
            let special = match op {
                Op::Builtin(BuiltinOp::StrInRe) => try_fold_in_re(ctx, &new_children),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(n, o)| n != o);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("regex: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
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

    // ── Task 3: extraction + ground rewrite pass ─────────────────────────

    /// Build a str.in_re atom over a LITERAL string from an SMT-LIB-shaped
    /// term tree, run the rewrite pass, and expect a Bool fold.
    fn fold_of(ctx: &mut Context, atom: TermId) -> Option<bool> {
        let out = rewrite_ground_in_re(ctx, &[atom]);
        match ctx.term_node(out[0]) {
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(b),
                ..
            } => Some(*b),
            _ => None,
        }
    }

    fn slit(ctx: &mut Context, s: &str) -> TermId {
        ctx.mk_string_const(s)
    }

    #[test]
    fn ground_atoms_fold_per_operator() {
        let mut ctx = Context::new();

        // ("ab", to_re("ab")) → true; ("ab", re.none) → false.
        let ab = slit(&mut ctx, "ab");
        let re_ab = to_re(&mut ctx, ab);
        let atom = in_re(&mut ctx, ab, re_ab);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, none);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // re.all / re.allchar.
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, all);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let allchar = ctx.mk_app(Op::Builtin(BuiltinOp::ReAllChar), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, allchar);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        let a = slit(&mut ctx, "a");
        let atom = in_re(&mut ctx, a, allchar);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        // (_ re.loop 1 2) over to_re("a"): "aa" in, "aaa" out.
        let re_a = to_re(&mut ctx, a);
        let loop12 = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: 1, hi: 2 }), &[re_a])
            .unwrap();
        let aa = slit(&mut ctx, "aa");
        let aaa = slit(&mut ctx, "aaa");
        let atom = in_re(&mut ctx, aa, loop12);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, aaa, loop12);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // (_ re.^ 2): exactly two copies.
        let pow2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::RePow(2)), &[re_a])
            .unwrap();
        let atom = in_re(&mut ctx, aa, pow2);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, pow2);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // re.comp / re.diff / re.inter / re.union / re.opt / re.+ / re.range.
        let b = slit(&mut ctx, "b");
        let re_b = to_re(&mut ctx, b);
        let comp_a = ctx.mk_app(Op::Builtin(BuiltinOp::ReComp), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, b, comp_a);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, comp_a);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let diff = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[allchar, re_a])
            .unwrap();
        let atom = in_re(&mut ctx, b, diff);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, diff);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let un = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[re_a, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, b, un);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let it = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReInter), &[un, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, b, it);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, it);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let empty = slit(&mut ctx, "");
        let opt = ctx.mk_app(Op::Builtin(BuiltinOp::ReOpt), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, empty, opt);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let plus = ctx.mk_app(Op::Builtin(BuiltinOp::RePlus), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, empty, plus);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        let atom = in_re(&mut ctx, aaa, plus);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let z = slit(&mut ctx, "c");
        let range = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, z])
            .unwrap();
        let atom = in_re(&mut ctx, b, range);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let d = slit(&mut ctx, "d");
        let atom = in_re(&mut ctx, d, range);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
    }

    #[test]
    fn degenerate_range_and_loop_are_decided_empty() {
        let mut ctx = Context::new();
        let a = slit(&mut ctx, "a");
        // Multi-char endpoint ⇒ empty range (decided, NOT fenced).
        let ab = slit(&mut ctx, "ab");
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, ab])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Reversed endpoints ⇒ empty.
        let c = slit(&mut ctx, "c");
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[c, a])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Loop lo > hi ⇒ empty.
        let re_a = to_re(&mut ctx, a);
        let l = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: 3, hi: 1 }), &[re_a])
            .unwrap();
        let atom = in_re(&mut ctx, a, l);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Empty-string membership of ε-shapes: "" in to_re("") → true.
        let empty = slit(&mut ctx, "");
        let re_empty = to_re(&mut ctx, empty);
        let atom = in_re(&mut ctx, empty, re_empty);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
    }

    #[test]
    fn atoms_fold_under_boolean_structure() {
        // Equivalences need no polarity tracking: fold under not/or/ite too.
        let mut ctx = Context::new();
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, a, re_a); // true
        let not = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[atom]).unwrap();
        let out = rewrite_ground_in_re(&mut ctx, &[not]);
        // not(true) — the pass does NOT simplify Boolean structure, only the
        // atom folds; check the child became const true.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("expected Not app");
        };
        let child = ctx.children(args).to_vec()[0];
        assert!(matches!(
            ctx.term_node(child),
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(true),
                ..
            }
        ));
        assert!(!has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn non_ground_shapes_survive_to_fence() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");

        // Symbolic string side.
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, s, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert_eq!(out[0], atom, "must not rewrite");
        assert!(has_unreduced_regex(&ctx, &out));

        // Symbolic to_re argument.
        let re_s = to_re(&mut ctx, s);
        let atom = in_re(&mut ctx, a, re_s);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));

        // Symbolic range endpoint.
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, s])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));

        // RegLan variable in the regex.
        let reglan = ctx.reglan_sort();
        let rv = nullary(&mut ctx, "r", reglan);
        let atom = in_re(&mut ctx, a, rv);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn above_alphabet_literals_fence() {
        let mut ctx = Context::new();
        // Ground string containing U+30000 (> MAX_CODE) — no fold.
        let hi = slit(&mut ctx, "\u{30000}");
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let atom = in_re(&mut ctx, hi, all);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Range endpoint above the alphabet — no fold.
        let a = slit(&mut ctx, "a");
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, hi])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // to_re over an above-alphabet literal — no fold.
        let re_hi = to_re(&mut ctx, hi);
        let atom = in_re(&mut ctx, a, re_hi);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn untouched_subtrees_keep_their_termids() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let lit = slit(&mut ctx, "xy");
        let eq = ctx.mk_eq(s, lit).unwrap();
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, a, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[eq, atom]);
        assert_eq!(out[0], eq, "unrelated assertion must keep its TermId");
        assert!(matches!(
            ctx.term_node(out[1]),
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(true),
                ..
            }
        ));
    }
}
