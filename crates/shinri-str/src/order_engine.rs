//! Slice 31: the online head-peel engine for two-symbolic-var `str.<`/`str.<=`.
//! The character-order comparison uses a dedicated UNINTERPRETED
//! `!strcode : String -> Int` function so EUF congruence-closes it
//! (`shinri-euf` congruences only `Op::Uninterpreted` apps). Range + on-demand
//! constant folding (Task 6) supply its semantics; nothing here uses
//! `str.to_code` (a Builtin, which EUF would not congruence).

use crate::{collect, wordeq, StrSolver};
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Integer, Lit, Op, Rational, SymbolId, TermId, TermNode};
use shinri_theory::types::ENodeId;
use shinri_theory::{TCheck, TheoryCtx};

/// Arith-facing largest code point (mirror of `code_conv::MAX_CODE`).
#[allow(dead_code)] // used in Task 4/6
pub const MAX_CODE_I128: i128 = 0x2FFFF;

/// Declare-or-fetch the single `!strcode : String -> Int` symbol.
#[allow(dead_code)] // used in Task 4
pub fn code_fun(terms: &mut Context) -> SymbolId {
    let str_s = terms.string_sort();
    let int_s = terms.int_sort();
    terms.declare_fun("!strcode", &[str_s], int_s)
}

/// Build `(!strcode h)`.
#[allow(dead_code)] // used in Task 4
pub fn code_of(terms: &mut Context, h: TermId) -> TermId {
    let f = code_fun(terms);
    terms
        .mk_app(Op::Uninterpreted(f), &[h])
        .expect("!strcode well-sorted")
}

#[allow(dead_code)] // used in Task 4
fn int_lit(terms: &mut Context, k: i128) -> TermId {
    let int_s = terms.int_sort();
    terms.mk_numeral(Rational::from_int(Integer::from(k)), int_s)
}

/// `[ (>= code_h 0), (<= code_h MAX_CODE) ]`.
#[allow(dead_code)] // used in Task 4
pub fn range_atoms(terms: &mut Context, code_h: TermId) -> Vec<TermId> {
    let zero = int_lit(terms, 0);
    let hi = int_lit(terms, MAX_CODE_I128);
    let ge = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[code_h, zero])
        .expect("ge");
    let le = terms
        .mk_app(Op::Builtin(BuiltinOp::Le), &[code_h, hi])
        .expect("le");
    vec![ge, le]
}

/// The surrogate-hole disjunction `(<= code_h 0xD7FF) ∨ (>= code_h 0xE000)`,
/// returned as the two disjunct atoms of a single split.
#[allow(dead_code)] // used in Task 4
pub fn surrogate_hole_atoms(terms: &mut Context, code_h: TermId) -> Vec<TermId> {
    let lo = int_lit(terms, 0xD7FF);
    let hi = int_lit(terms, 0xE000);
    let below = terms
        .mk_app(Op::Builtin(BuiltinOp::Le), &[code_h, lo])
        .expect("le");
    let above = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[code_h, hi])
        .expect("ge");
    vec![below, above]
}

/// `(< ca cb)`.
#[allow(dead_code)] // used in Task 4
pub fn code_lt(terms: &mut Context, ca: TermId, cb: TermId) -> TermId {
    terms
        .mk_app(Op::Builtin(BuiltinOp::Lt), &[ca, cb])
        .expect("lt")
}

/// A memoized `str.<`/`str.<=` head-peel clause family for one polarity-
/// normalized operand pair `(A, B)`. The fresh heads `hA/hB` and their code
/// handles are minted ONCE (here) and reused every round via the memo in
/// `StrSolver::order_clauses`, so EUF congruence relates the SAME head terms
/// across rounds — the code-bridge soundness premise (Task 7's congruence
/// gate depends on it).
pub(crate) struct OrderFamily {
    pub clauses: Vec<Vec<TermId>>,
    pub code_ha: TermId,
    pub code_hb: TermId,
}

/// Build the ordered head-peel clause family for the POSITIVE relation `R` on
/// operands `(a, b)` (`use_lt` ⟹ `str.<`, else `str.<=`). Returns the clause
/// list in the fixed order
/// `[NEQ|BNE_cond], [BNE], DEC_A, LEN_HA(ge), LEN_HA(le), LEN_HB(ge),
/// LEN_HB(le), DEC_B, RNG_HA×3, RNG_HB×3, CMP1, CMP2`
/// plus the two code-point handles for shared-arith registration. Each clause
/// is a flat disjunct atom-list; the caller emits it as a guarded `Split`.
/// See docs `.superpowers/sdd/clause-family-reference.md`.
///
/// Nuances (per the reference): the A-side decomposition/length/range/compare
/// clauses carry the `(= A EPS)` guard-disjunct (`hA` exists only when `A≠""`);
/// the B-side length/range clauses are UNCONDITIONAL. `str.<` adds the strict
/// `NEQ`/`BNE` singletons; `str.<=` instead uses the conditional `BNE_cond`
/// and omits `NEQ`. `R_tail` is `str.<` for `<`, `str.<=` for `<=`.
pub(crate) fn build_order_family(
    terms: &mut Context,
    a: TermId,
    b: TermId,
    use_lt: bool,
    ctr: &mut u32,
) -> OrderFamily {
    let eps = terms.mk_string_const("");
    let a_eps = terms.mk_eq(a, eps).expect("(= A eps) well-sorted");

    // Fresh heads/tails + code handles, minted ONCE per family.
    let ha = wordeq::fresh_str(terms, ctr);
    let ta = wordeq::fresh_str(terms, ctr);
    let hb = wordeq::fresh_str(terms, ctr);
    let tb = wordeq::fresh_str(terms, ctr);
    let code_ha = code_of(terms, ha);
    let code_hb = code_of(terms, hb);
    let one = int_lit(terms, 1);

    let mut clauses: Vec<Vec<TermId>> = Vec::new();

    // Relation-specific leading clause(s).
    if use_lt {
        // NEQ : [ (distinct A B) ]
        let neq = terms
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b])
            .expect("distinct well-sorted");
        clauses.push(vec![neq]);
        // BNE : [ (distinct B EPS) ]
        let bne = terms
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[b, eps])
            .expect("distinct well-sorted");
        clauses.push(vec![bne]);
    } else {
        // BNE_cond : [ (= A EPS), (distinct B EPS) ]  (no NEQ; `<=` allows A=B)
        let bne = terms
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[b, eps])
            .expect("distinct well-sorted");
        clauses.push(vec![a_eps, bne]);
    }

    // DEC_A : [ (= A EPS), (= A (str.++ hA tA)) ]
    let cat_a = terms
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ha, ta])
        .expect("str.++ well-sorted");
    let dec_a = terms.mk_eq(a, cat_a).expect("(= A hA·tA) well-sorted");
    clauses.push(vec![a_eps, dec_a]);

    // LEN_HA(ge) / LEN_HA(le) : [ (= A EPS), (>=|<= (str.len hA) 1) ]
    let lha = wordeq::len_of(terms, ha);
    let lha_ge = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[lha, one])
        .expect("ge");
    clauses.push(vec![a_eps, lha_ge]);
    let lha_le = terms
        .mk_app(Op::Builtin(BuiltinOp::Le), &[lha, one])
        .expect("le");
    clauses.push(vec![a_eps, lha_le]);

    // LEN_HB(ge) / LEN_HB(le) : [ (>=|<= (str.len hB) 1) ] — UNCONDITIONAL
    let lhb = wordeq::len_of(terms, hb);
    let lhb_ge = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[lhb, one])
        .expect("ge");
    clauses.push(vec![lhb_ge]);
    let lhb_le = terms
        .mk_app(Op::Builtin(BuiltinOp::Le), &[lhb, one])
        .expect("le");
    clauses.push(vec![lhb_le]);

    // DEC_B : [ (= A EPS), (= B (str.++ hB tB)) ]  (B decomposes whenever A≠"")
    let cat_b = terms
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[hb, tb])
        .expect("str.++ well-sorted");
    let dec_b = terms.mk_eq(b, cat_b).expect("(= B hB·tB) well-sorted");
    clauses.push(vec![a_eps, dec_b]);

    // RNG_HA×3 : A-side range/surrogate-hole, each guarded by (= A EPS).
    let ra = range_atoms(terms, code_ha); // [ (>= codeHA 0), (<= codeHA MAX) ]
    clauses.push(vec![a_eps, ra[0]]);
    clauses.push(vec![a_eps, ra[1]]);
    let sha = surrogate_hole_atoms(terms, code_ha); // [ (<= 0xD7FF), (>= 0xE000) ]
    clauses.push(vec![a_eps, sha[0], sha[1]]);

    // RNG_HB×3 : B-side range/surrogate-hole, UNCONDITIONAL.
    let rb = range_atoms(terms, code_hb);
    clauses.push(vec![rb[0]]);
    clauses.push(vec![rb[1]]);
    let shb = surrogate_hole_atoms(terms, code_hb);
    clauses.push(vec![shb[0], shb[1]]);

    // CMP1 : [ (= A EPS), (< codeHA codeHB), (= hA hB) ]
    let clt = code_lt(terms, code_ha, code_hb);
    let ha_eq_hb = terms.mk_eq(ha, hb).expect("(= hA hB) well-sorted");
    clauses.push(vec![a_eps, clt, ha_eq_hb]);

    // CMP2 : [ (= A EPS), (< codeHA codeHB), R_tail ]
    let r_tail = if use_lt {
        terms
            .mk_app(Op::Builtin(BuiltinOp::StrLt), &[ta, tb])
            .expect("str.< well-sorted")
    } else {
        terms
            .mk_app(Op::Builtin(BuiltinOp::StrLeq), &[ta, tb])
            .expect("str.<= well-sorted")
    };
    clauses.push(vec![a_eps, clt, r_tail]);

    OrderFamily {
        clauses,
        code_ha,
        code_hb,
    }
}

/// The `(str.< a b)` clause list (thin wrapper over [`build_order_family`];
/// exercised by the clause-shape unit test and Task 7's e2e — the check()
/// path itself calls `build_order_family` so it can memoize the code handles).
#[allow(dead_code)] // used by the clause-shape test + Task 7 e2e
pub fn build_strlt_clauses(
    terms: &mut Context,
    a: TermId,
    b: TermId,
    ctr: &mut u32,
) -> Vec<Vec<TermId>> {
    build_order_family(terms, a, b, true, ctr).clauses
}

/// The `(str.<= a b)` sibling of [`build_strlt_clauses`].
#[allow(dead_code)] // deliverable sibling; core path uses build_order_family; exercised by tests
pub fn build_strleq_clauses(
    terms: &mut Context,
    a: TermId,
    b: TermId,
    ctr: &mut u32,
) -> Vec<Vec<TermId>> {
    build_order_family(terms, a, b, false, ctr).clauses
}

/// Stable 64-bit hash of a clause's atom-list, for the per-atom dedup key.
/// A hash collision can only SKIP a distinct clause (fewer guarded lemmas —
/// a completeness loss, never a soundness one), so the 64-bit key is safe.
fn hash_atoms(atoms: &[TermId]) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    atoms.hash(&mut h);
    h.finish()
}

/// The check()-side order emitter (slice 31). For one asserted order literal:
/// normalize polarity to a positive relation on `(a, b)`, get-or-build the
/// memoized clause family (fresh heads reused across rounds), then emit the
/// FIRST clause not yet in `emitted_order` as a GUARDED `Split`. Returns
/// `None` when every clause of the family is already emitted.
///
/// Polarity normalization (args = the atom's two operands):
/// `(pos, <)→A<B`, `(pos, <=)→A<=B`, `(neg, <)→ B<=A` (`¬(A<B)`),
/// `(neg, <=)→ B<A` (`¬(A<=B)`). The guard is ALWAYS `lit.negate()`, so every
/// emitted clause is the valid implication `assertedLit → body`.
pub(crate) fn order_check(
    s: &mut StrSolver,
    cx: &mut TheoryCtx,
    atom: TermId,
    lit: Lit,
    is_lt: bool,
) -> Option<TCheck> {
    // The atom's two operands.
    let (arg0, arg1) = match cx.terms.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq),
            args,
            ..
        } => {
            let ch = cx.terms.children(*args);
            (ch[0], ch[1])
        }
        _ => return None,
    };

    // Full 4-case polarity normalization to a positive relation on (a, b).
    let (a, b, use_lt) = match (lit.is_positive(), is_lt) {
        (true, true) => (arg0, arg1, true),   //  A <  B
        (true, false) => (arg0, arg1, false), //  A <= B
        (false, true) => (arg1, arg0, false), // ¬(A<B)  ≡ B <= A
        (false, false) => (arg1, arg0, true), // ¬(A<=B) ≡ B <  A
    };

    // Get-or-build the memoized family. Keyed by the NORMALIZED (a, b, use_lt)
    // so the SAME atom asserted at the opposite polarity across backtracking
    // gets its own (correct) fresh heads, while two atoms that normalize to the
    // same relation share heads (their guards still differ per-atom below).
    let key = (a, b, use_lt);
    if !s.order_clauses.contains_key(&key) {
        let fam = build_order_family(cx.terms, a, b, use_lt, &mut s.fresh_ctr);
        s.order_clauses.insert(key, fam);
    }
    let (clauses, code_ha, code_hb) = {
        let fam = &s.order_clauses[&key];
        (fam.clauses.clone(), fam.code_ha, fam.code_hb)
    };

    // Emit the FIRST not-yet-emitted clause of this atom's family.
    for clause in &clauses {
        let dedup_key = (atom, hash_atoms(clause));
        if s.emitted_order.contains(&dedup_key) {
            continue;
        }
        // Fuel BEFORE emitting (Global Constraint).
        if !s.fuel.spend() {
            return Some(TCheck::Unknown);
        }
        // Register each atom's len/str subterms so the length seam shares them.
        let mut seen = FxHashSet::default();
        for &ai in clause {
            collect::collect(cx.terms, ai, &mut s.len_terms, &mut s.str_terms, &mut seen);
        }
        // Expose the code-point handles as shared arith vars (N-O seam —
        // `shared_arith_terms` reads `code_terms`).
        s.code_terms.insert(code_ha);
        s.code_terms.insert(code_hb);
        // Dedup, then emit the guarded implication `assertedLit → clause`.
        s.emitted_order.insert(dedup_key);
        return Some(TCheck::Split {
            atoms: clause.clone(),
            guard: Some(lit.negate()),
        });
    }
    None
}

/// Extract the argument `h` of a `(!strcode h)` application (an entry of
/// `code_terms`). `None` for anything that is not a unary uninterpreted app.
fn arg_of_code(terms: &Context, code_t: TermId) -> Option<TermId> {
    match terms.term_node(code_t) {
        TermNode::App {
            op: Op::Uninterpreted(_),
            args,
            ..
        } => {
            let ch = terms.children(*args);
            (ch.len() == 1).then(|| ch[0])
        }
        _ => None,
    }
}

/// On-demand CODE-CONSTANT FOLD (slice 31 Task 6, SOUNDNESS-critical).
///
/// For the order literal `lit` on `atom`, look up its (already-built) head-peel
/// family and, for each minted head `h` whose code handle `code(h)=(!strcode h)`
/// is a shared arith var, check whether `h` is currently EUF-equal to a
/// SINGLE-CHARACTER string constant `c`. If so, emit the pin
/// `code(h) = eval_to_code(c)` — the REAL code point — split into its arith
/// `Ge`/`Le` companions (never a bare Int `Eq`, which would route to EUF not
/// Arith), one companion per call, deduped in `emitted_code_folds`, fuel-spent,
/// GUARDED by `lit.negate()` (the valid implication `L → code(h)=k`).
///
/// ## Why this is sound (self-review against the Task-6 invariants)
/// * **Single-char gate.** `code_conv::eval_to_code` returns `Some(-1)` for the
///   empty / multi-char case (NOT `None`), so we FIRST require `c` to be a
///   single char and only then trust `eval_to_code`'s `Some(k)`. A head
///   EUF-equal to a multi-char constant is left to the `|h|=1` length clause,
///   which contradicts it via arith — folding must NOT fire (safe fallthrough).
/// * **Domain / surrogate consistency.** `c` is a `Box<str>`-backed constant, so
///   its one char is a valid Unicode scalar value: never a surrogate
///   (`0xD800..=0xDFFF`), and `eval_to_code` returns `None` above
///   `MAX_CODE=0x2FFFF`. Hence `k ∈ [0, MAX_CODE] \ surrogates` — exactly the
///   set the family's range / surrogate-hole clauses admit, so the pin can never
///   contradict them (which would be a spurious UNSAT).
/// * **Merge is not branch-local.** The pin is a global clause `¬L ∨ code(h)=k`
///   that READS the `h≈c` merge; per this file's E1 discipline we emit it only
///   when `side_clean(h, input_cond_roots)` holds — i.e. `h`'s class was not
///   merged by a CONDITIONAL (dl>0) INPUT (dis)equality. The family's own
///   decomposition merges (minted, `¬L`-guarded) are deliberately NOT in
///   `input_cond_roots`, so the intended dl0-constant case still folds.
pub(crate) fn order_fold_check(
    s: &mut StrSolver,
    cx: &mut TheoryCtx,
    atom: TermId,
    lit: Lit,
    is_lt: bool,
    input_cond_roots: &FxHashSet<ENodeId>,
) -> Option<TCheck> {
    // Re-derive the polarity-normalized family key (identical to order_check).
    let (arg0, arg1) = match cx.terms.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq),
            args,
            ..
        } => {
            let ch = cx.terms.children(*args);
            (ch[0], ch[1])
        }
        _ => return None,
    };
    let (a, b, use_lt) = match (lit.is_positive(), is_lt) {
        (true, true) => (arg0, arg1, true),
        (true, false) => (arg0, arg1, false),
        (false, true) => (arg1, arg0, false),
        (false, false) => (arg1, arg0, true),
    };
    let key = (a, b, use_lt);
    // Fold only over an ALREADY-BUILT family (order_check mints/memoizes it).
    let (code_ha, code_hb) = {
        let fam = s.order_clauses.get(&key)?;
        (fam.code_ha, fam.code_hb)
    };

    // Candidate constants to probe against a head's EUF class.
    let str_terms: Vec<TermId> = s.str_terms.iter().copied().collect();

    for code_h in [code_ha, code_hb] {
        let Some(h) = arg_of_code(cx.terms, code_h) else {
            continue;
        };
        // Find a single-char string constant `c` EUF-equal to `h`.
        let hn = cx.eq.intern(h);
        let mut hit: Option<(TermId, Integer)> = None;
        for c in &str_terms {
            let Some(cs) = cx.terms.string_const_value(*c).map(str::to_owned) else {
                continue;
            };
            // Single-char gate FIRST (eval_to_code returns Some(-1) for
            // empty/multi-char, which must never be folded).
            let mut chit = cs.chars();
            if !matches!((chit.next(), chit.next()), (Some(_), None)) {
                continue;
            }
            let cn = cx.eq.intern(*c);
            if !cx.eq.are_equal(hn, cn) {
                continue;
            }
            // Genuine single char: eval_to_code yields the REAL code point in
            // [0, MAX_CODE]\surrogates (None above the alphabet ⇒ no fold).
            if let Some(k) = crate::code_conv::eval_to_code(&cs) {
                hit = Some((*c, k));
                break;
            }
        }
        let Some((_c, k)) = hit else {
            continue;
        };
        // SOUNDNESS gate: the `h≈c` merge must not be branch-local w.r.t. a
        // conditional INPUT disjunction (else the global `¬L ∨ code(h)=k` clause
        // is unsound on a sibling branch → spurious UNSAT).
        if !crate::side_clean(cx.eq, cx.terms, h, input_cond_roots) {
            continue;
        }

        // Build `(= code(h) k)` and split into arith Ge/Le companions.
        let int_s = cx.terms.int_sort();
        let kt = cx.terms.mk_numeral(Rational::from_int(k), int_s);
        let eqn = cx
            .terms
            .mk_eq(code_h, kt)
            .expect("(= code(h) k) well-sorted");
        let (ge, le) = crate::length::arith_eq_companions(cx.terms, eqn)
            .expect("code(h)=k is an Int equality");

        for comp in [ge, le] {
            if s.emitted_code_folds.contains(&comp) {
                continue;
            }
            // Fuel BEFORE marking emitted (deliver-only accounting).
            if !s.fuel.spend() {
                return Some(TCheck::Unknown);
            }
            s.emitted_code_folds.insert(comp);
            let mut seen = FxHashSet::default();
            collect::collect(
                cx.terms,
                comp,
                &mut s.len_terms,
                &mut s.str_terms,
                &mut seen,
            );
            return Some(TCheck::Split {
                atoms: vec![comp],
                guard: Some(lit.negate()),
            });
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, TermNode};

    fn str_var(ctx: &mut Context, n: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn code_of_is_congruent_uninterpreted_int_app() {
        let mut ctx = Context::new();
        let h1 = str_var(&mut ctx, "h1");
        let c1 = code_of(&mut ctx, h1);
        // Same argument → same hash-consed term (functional at the term level).
        let c1b = code_of(&mut ctx, h1);
        assert_eq!(c1, c1b);
        // It is Int-sorted and headed by an Uninterpreted op (so EUF congruences it).
        assert_eq!(ctx.sort_of(c1), ctx.int_sort());
        assert!(matches!(
            ctx.term_node(c1),
            TermNode::App {
                op: Op::Uninterpreted(_),
                ..
            }
        ));
    }

    fn is_distinct(ctx: &Context, t: TermId, x: TermId, y: TermId) -> bool {
        if let TermNode::App {
            op: Op::Builtin(BuiltinOp::Distinct),
            args,
            ..
        } = ctx.term_node(t)
        {
            let ch = ctx.children(*args);
            ch.len() == 2 && ((ch[0] == x && ch[1] == y) || (ch[0] == y && ch[1] == x))
        } else {
            false
        }
    }

    fn is_strlt_app(ctx: &Context, t: TermId) -> bool {
        matches!(
            ctx.term_node(t),
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrLt),
                ..
            }
        )
    }

    fn is_strleq_app(ctx: &Context, t: TermId) -> bool {
        matches!(
            ctx.term_node(t),
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrLeq),
                ..
            }
        )
    }

    #[test]
    fn strlt_family_emits_neq_bne_and_decomposition() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let u = str_var(&mut ctx, "u");
        let mut ctr = 0u32;
        let clauses = build_strlt_clauses(&mut ctx, s, u, &mut ctr);
        // NEQ: a singleton (distinct s u).
        assert!(clauses
            .iter()
            .any(|c| c.len() == 1 && is_distinct(&ctx, c[0], s, u)));
        // BNE: a singleton (distinct u "").
        let eps = ctx.mk_string_const("");
        assert!(clauses
            .iter()
            .any(|c| c.len() == 1 && is_distinct(&ctx, c[0], u, eps)));
        // CMP2 recursion tail is a fresh (str.< tA tB) order atom.
        assert!(clauses.iter().flatten().any(|&a| is_strlt_app(&ctx, a)));
    }

    #[test]
    fn strleq_family_has_no_neq_and_leq_recursion_tail() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let u = str_var(&mut ctx, "u");
        let mut ctr = 0u32;
        let clauses = build_strleq_clauses(&mut ctx, s, u, &mut ctr);
        // `str.<=` admits equality: no NEQ singleton `(distinct s u)`.
        assert!(
            !clauses
                .iter()
                .any(|c| c.len() == 1 && is_distinct(&ctx, c[0], s, u)),
            "str.<= family must not contain a NEQ singleton"
        );
        // BNE_cond : [ (= s eps), (distinct u eps) ] — the conditional sibling of
        // strlt's unconditional BNE singleton.
        let eps = ctx.mk_string_const("");
        let s_eps = ctx.mk_eq(s, eps).expect("(= s eps) well-sorted");
        assert!(
            clauses
                .iter()
                .any(|c| c.len() == 2 && c[0] == s_eps && is_distinct(&ctx, c[1], u, eps)),
            "must contain BNE_cond [(= s eps), (distinct u eps)]"
        );
        // CMP2 recursion tail is a fresh (str.<= tA tB) order atom, never str.<.
        assert!(
            clauses.iter().flatten().any(|&a| is_strleq_app(&ctx, a)),
            "CMP2 recursion tail must be str.<="
        );
        assert!(
            !clauses.iter().flatten().any(|&a| is_strlt_app(&ctx, a)),
            "str.<= family must not contain any str.< atom"
        );
    }

    /// Discriminates the `(neg, lt)` arm of `order_check`'s polarity
    /// normalization: `¬(str.< s u)` must build the `str.<=` family on the
    /// SWAPPED pair `(u, s)`, not the `str.<` family on `(s, u)`. Drives
    /// `order_check` directly with a synthesized NEGATIVE `Lit` (mirroring the
    /// scaffold of `assert_records_order_atoms` in lib.rs, but calling
    /// `order_check` directly rather than going through `assert`/`check`).
    ///
    /// This would FAIL if the `(false, true)` arm built `build_order_family`
    /// on `(arg0, arg1, true)` (StrLt on the un-swapped pair) instead of
    /// `(arg1, arg0, false)` (StrLeq on the swapped pair): the memo would then
    /// be keyed `(s, u, true)` instead of `(u, s, false)`, and the family
    /// would contain a NEQ singleton and a `str.<` recursion tail instead of
    /// neither.
    #[test]
    fn negative_lt_maps_to_swapped_leq() {
        let mut ctx = Context::new();
        let s_var = str_var(&mut ctx, "s");
        let u_var = str_var(&mut ctx, "u");
        let lt_atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLt), &[s_var, u_var])
            .unwrap();
        let mut solver = StrSolver::default();
        let mut eq = shinri_theory::EqualityEngine::default();
        let atoms = shinri_theory::AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        // NEGATIVE literal over the (str.< s u) atom: ¬(s < u) ≡ (u <= s).
        let neg_lit = Lit::new(shinri_core::Var::new(0), false);
        let res = order_check(&mut solver, &mut cx, lt_atom, neg_lit, /*is_lt=*/ true);
        assert!(
            res.is_some(),
            "order_check must emit a split for a fresh family"
        );

        let swapped_leq_key = (u_var, s_var, false);
        let wrong_lt_key = (s_var, u_var, true);
        assert!(
            solver.order_clauses.contains_key(&swapped_leq_key),
            "¬(str.< s u) must build the str.<= family on the swapped (u, s) pair"
        );
        assert!(
            !solver.order_clauses.contains_key(&wrong_lt_key),
            "¬(str.< s u) must NOT build the str.< family on the un-swapped (s, u) pair"
        );

        let fam = &solver.order_clauses[&swapped_leq_key];
        // No NEQ singleton `[(distinct u s)]` — str.<= admits equality.
        assert!(
            !fam.clauses
                .iter()
                .any(|c| c.len() == 1 && is_distinct(&ctx, c[0], u_var, s_var)),
            "swapped family must not contain a NEQ singleton"
        );
        // Recursion tail is (str.<= ...), never (str.< ...).
        assert!(
            fam.clauses
                .iter()
                .flatten()
                .any(|&a| is_strleq_app(&ctx, a)),
            "swapped family's CMP2 recursion tail must be str.<="
        );
        assert!(
            !fam.clauses.iter().flatten().any(|&a| is_strlt_app(&ctx, a)),
            "swapped family must not contain any str.< atom"
        );
    }

    /// Task 6 folding mechanism (runs GREEN pre-fence). Build an order family,
    /// force its A-head `hA` EUF-equal to the single-char constant `"b"`, then
    /// drive `order_fold_check` directly and assert it emits BOTH `Ge`/`Le`
    /// companions pinning `code(hA)` to `98` (the code point of `'b'`), each
    /// guarded by `¬L`. This is the SOUNDNESS pin that stops arith from picking a
    /// bogus `code("b") < code("a")`.
    #[test]
    fn fold_pins_code_of_head_equal_to_single_char_constant() {
        use shinri_theory::types::EqJust;

        let mut ctx = Context::new();
        let s_var = str_var(&mut ctx, "s");
        let u_var = str_var(&mut ctx, "u");
        let b_const = ctx.mk_string_const("b");
        let lt_atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLt), &[s_var, u_var])
            .unwrap();

        let mut solver = StrSolver::default();
        let mut eq = shinri_theory::EqualityEngine::default();
        let areg = shinri_theory::AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };

        // Positive `(str.< s u)` literal → family key (s, u, true). One
        // order_check call mints hA/hB + their code handles and memoizes the
        // family (the fold consumes an ALREADY-BUILT family).
        let pos_lit = Lit::new(shinri_core::Var::new(0), true);
        let _ = order_check(&mut solver, &mut cx, lt_atom, pos_lit, /*is_lt=*/ true);

        let key = (s_var, u_var, true);
        let code_ha = solver.order_clauses[&key].code_ha;
        let ha = arg_of_code(cx.terms, code_ha).expect("code_ha is (!strcode hA)");

        // Force hA ≈ "b" in EUF and expose "b" as a candidate constant.
        let hn = cx.eq.intern(ha);
        let cn = cx.eq.intern(b_const);
        cx.eq
            .merge(hn, cn, EqJust::Definitional)
            .expect("merge hA≈\"b\"");
        solver.test_force_str_term(b_const);

        // Expected companions of `(= code(hA) 98)` ('b' = 98).
        let int_s = cx.terms.int_sort();
        let k98 = cx
            .terms
            .mk_numeral(Rational::from_int(Integer::from(98i128)), int_s);
        let expected_ge = cx
            .terms
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[code_ha, k98])
            .unwrap();
        let expected_le = cx
            .terms
            .mk_app(Op::Builtin(BuiltinOp::Le), &[code_ha, k98])
            .unwrap();

        let empty_roots: FxHashSet<ENodeId> = FxHashSet::default();
        let (mut saw_ge, mut saw_le) = (false, false);
        for _ in 0..8 {
            match order_fold_check(&mut solver, &mut cx, lt_atom, pos_lit, true, &empty_roots) {
                Some(TCheck::Split { atoms, guard }) => {
                    assert_eq!(
                        guard,
                        Some(pos_lit.negate()),
                        "fold split must be guarded by ¬L (the valid implication L → code(h)=k)"
                    );
                    for a in atoms {
                        if a == expected_ge {
                            saw_ge = true;
                        } else if a == expected_le {
                            saw_le = true;
                        } else {
                            panic!("fold emitted a non-companion atom");
                        }
                    }
                }
                None => break,
                Some(_) => panic!("fold must return a Split or None, never a verdict"),
            }
        }
        assert!(
            saw_ge && saw_le,
            "fold must emit BOTH Ge/Le companions pinning code(hA) to 98"
        );
    }

    #[test]
    fn range_atoms_are_arith_inequalities() {
        let mut ctx = Context::new();
        let h = str_var(&mut ctx, "h");
        let code_h = code_of(&mut ctx, h);
        let atoms = range_atoms(&mut ctx, code_h);
        assert_eq!(atoms.len(), 2);
        for a in atoms {
            assert!(matches!(
                ctx.term_node(a),
                TermNode::App {
                    op: Op::Builtin(BuiltinOp::Ge | BuiltinOp::Le),
                    ..
                }
            ));
        }
    }
}
