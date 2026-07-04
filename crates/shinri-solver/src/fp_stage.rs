//! FP lowering stage: detect QF_FP queries, collect FP atoms, enforce the
//! mixed-theory fence. Mirrors bv_stage.rs. BV and FP terms share one unified
//! Lowerer/Blaster (slice 4a/4b), so a query can mix BV and FP atoms without
//! fencing. Assertions arrive already normalized by word_norm (slice 5): no
//! word-sorted ite, and any n-ary =/distinct over BV/Float/RoundingMode
//! operands has already been expanded to binary. RoundingMode (RM) content
//! also routes through here (slice 5).

use shinri_core::{BuiltinOp, ConstVal, Context, Op, SortNode, TermId, TermNode};

fn is_fp_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::Float(_, _))
}

fn is_rm_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::RoundingMode)
}

/// True if `op` is any FP builtin (word op, predicate, classification, or conversion).
fn is_fp_op(op: &Op) -> bool {
    use BuiltinOp::*;
    matches!(op, Op::Builtin(
        FpAbs | FpNeg | FpAdd | FpSub | FpMul | FpDiv | FpFma | FpSqrt | FpRem
        | FpRoundToIntegral | FpMin | FpMax | FpLeq | FpLt | FpGeq | FpGt | FpEq
        | FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite | FpIsNaN
        | FpIsNegative | FpIsPositive | FpFromBits
        | ToFp { .. } | ToFpUnsigned { .. } | FpToUbv(_) | FpToSbv(_) | FpToReal
    ))
}

/// FP PREDICATES (Bool-sorted FP atoms): comparisons + classifications.
fn is_fp_predicate(op: &Op) -> bool {
    use BuiltinOp::*;
    matches!(op, Op::Builtin(
        FpLeq | FpLt | FpGeq | FpGt | FpEq
        | FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite | FpIsNaN
        | FpIsNegative | FpIsPositive
    ))
}

/// True if any subterm has a Float or RoundingMode sort or an FP builtin op.
/// RoundingMode counts as FP content so RM-only scripts (e.g. `(= r RNE)`)
/// route here instead of leaking to EUF, which would treat RM as an unbounded
/// uninterpreted sort (confirmed wrong-SAT, design doc §1).
pub fn solver_uses_fp(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return false; }
        if is_fp_sorted(ctx, t) || is_rm_sorted(ctx, t) { return true; }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                if is_fp_op(op) { return true; }
                ctx.children(*args).to_vec().into_iter().any(|c| walk(ctx, c, seen))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a, &mut seen))
}

/// True if any subterm is a BV↔FP CROSSING conversion (or the Real bridge) —
/// the ops no slice has yet admitted. These must fence to `Unknown` BEFORE
/// lowering so `blast_bv_word`/`blast_fp_word`'s crossing `unreachable!` arms
/// stay internal invariants. This is the single authoritative crossing-op list:
/// later slices delete an entry here as each conversion is admitted.
///
/// Crossing set (post slice 4e — PERMANENT, modulo the v2 Real-combination plan):
/// - `FpToReal` — the permanent Real bridge (v1 non-goal).
/// - `ToFp` — crossing ONLY in its symbolic-Real face. The 3a-supported
///   FP→FP and constant-Real faces, the 4c-supported 1-arg BV bitcast face,
///   and the 4d-supported 2-arg BV-source (signed int→FP) face are NOT
///   crossing.
///
/// `FpToUbv`/`FpToSbv` (FP→BV) are also NOT crossing — admitted in slice 4e.
/// `FpFromBits` (the `fp` sign/exp/sig constructor from BV words) is also
/// NOT crossing — admitted in slice 4c alongside the 1-arg `to_fp` bitcast.
/// `ToFpUnsigned` (unsigned int→FP) is also NOT crossing — admitted in
/// slice 4d alongside the `ToFp` 2-arg BV-source face.
pub fn uses_crossing_conversion(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) {
            return false;
        }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            let is_crossing = match op {
                // fp.to_real is admitted (slice 9) for eb<=8 (Float16/32); larger
                // formats stay crossing (Real bridge deferred for eb>8).
                Op::Builtin(BuiltinOp::FpToReal) => match ctx.fp_widths(ctx.sort_of(kids[0])) {
                    Some((eb, _)) if eb <= 8 => false,
                    _ => true,
                },
                Op::Builtin(BuiltinOp::ToFp { .. }) => match kids.len() {
                    1 => false, // 1-arg BV bitcast — admitted in slice 4c
                    2 => match ctx.sort_node(ctx.sort_of(kids[1])) {
                        SortNode::BitVec(_) => false, // signed int→FP — admitted in slice 4d
                        // symbolic Real is crossing; a constant Real is 3a-supported.
                        SortNode::Real => ctx.const_real_value(kids[1]).is_none(),
                        _ => false, // Float → FP (3a-supported)
                    },
                    _ => true, // defensive: unexpected arity
                },
                _ => false,
            };
            if is_crossing {
                return true;
            }
            return kids.into_iter().any(|c| walk(ctx, c, seen));
        }
        false
    }
    assertions.iter().any(|&a| walk(ctx, a, &mut seen))
}

/// Collect Bool-sorted FP atoms: FP predicates, plus Eq/Distinct over Float operands.
/// SOUNDNESS-CRITICAL: FP (dis)equalities ARE included (else they route to EUF).
pub fn collect_fp_atoms(ctx: &Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    let mut in_set: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, out: &mut Vec<TermId>,
            in_set: &mut rustc_hash::FxHashSet<TermId>,
            visited: &mut rustc_hash::FxHashSet<TermId>) {
        if !visited.insert(t) { return; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            let is_atom = match op {
                _ if is_fp_predicate(op) => true,
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) =>
                    kids.iter().any(|&k| is_fp_sorted(ctx, k) || is_rm_sorted(ctx, k)),
                _ => false,
            };
            if is_atom && in_set.insert(t) { out.push(t); return; }
            for k in kids { walk(ctx, k, out, in_set, visited); }
        }
    }
    for &a in assertions { walk(ctx, a, &mut out, &mut in_set, &mut visited); }
    out
}

/// Shared walk: collect every Bool-sorted atom that is NEITHER in `allow_set`
/// NOR pure Boolean structure (Not/And/Or/Implies/Xor/Ite, or Bool-sorted
/// Eq/Distinct) NOR a bare nullary Bool constant. This is the single walk
/// factored out of the old `has_non_fp_theory_atom` body so the bool fence
/// predicate and the `Vec`-returning `non_bvfp_atoms` enumerator (added in
/// slice 9 for `bridge_admissible`) share one implementation (DRY) instead of
/// two copies of the same recursion that could drift apart.
fn foreign_theory_atoms(
    ctx: &Context,
    assertions: &[TermId],
    allow_set: &rustc_hash::FxHashSet<TermId>,
) -> Vec<TermId> {
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    let mut out: Vec<TermId> = Vec::new();
    fn walk(
        ctx: &Context,
        t: TermId,
        allow_set: &rustc_hash::FxHashSet<TermId>,
        visited: &mut rustc_hash::FxHashSet<TermId>,
        out: &mut Vec<TermId>,
    ) {
        if allow_set.contains(&t) { return; }
        if !visited.insert(t) { return; }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids: Vec<TermId> = ctx.children(*args).to_vec();
                let is_bool_structure = matches!(op, Op::Builtin(
                    BuiltinOp::Not | BuiltinOp::And | BuiltinOp::Or
                    | BuiltinOp::Implies | BuiltinOp::Xor | BuiltinOp::Ite));
                let is_bool_eq = matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct))
                    && kids.first().is_some_and(|&k| ctx.sort_of(k) == ctx.bool_sort());
                if is_bool_structure || is_bool_eq {
                    for k in kids { walk(ctx, k, allow_set, visited, out); }
                    return;
                }
                // A bare declared Bool constant (0-ary uninterpreted symbol,
                // Bool-sorted) needs NO theory reasoning: a nullary symbol has
                // no arguments for congruence to act on, so it is Tseitin-
                // encoded as a plain SAT variable regardless of which theories
                // are otherwise in play. It is skeleton, not a foreign theory
                // atom — exempt it from the fence (slice 5: word_norm's
                // ite-elimination exposes bare condition variables like `c`
                // here that were previously buried, unreachable, inside a
                // single opaque FP atom leaf). See bv_stage.rs's identical
                // exemption in `has_non_bv_theory_atom`.
                if matches!(op, Op::Uninterpreted(_))
                    && kids.is_empty()
                    && ctx.sort_of(t) == ctx.bool_sort()
                {
                    return;
                }
                if ctx.sort_of(t) == ctx.bool_sort() {
                    // Bool-sorted, not in the allow-set, not Boolean structure
                    // → a foreign theory atom.
                    out.push(t);
                    return;
                }
                for k in kids { walk(ctx, k, allow_set, visited, out); }
            }
            TermNode::Const { .. } => {}
        }
    }
    for &a in assertions { walk(ctx, a, allow_set, &mut visited, &mut out); }
    out
}

/// Mixed-theory fence (conservative). True if any Bool-sorted atom outside the
/// FP set is not pure Boolean structure — including BV atoms (BVFP waits for
/// Plan 4) and arith/EUF/array atoms. When true, the caller returns Unknown.
pub fn has_non_fp_theory_atom(ctx: &Context, assertions: &[TermId], fp_atoms: &[TermId]) -> bool {
    let fp_set: rustc_hash::FxHashSet<TermId> = fp_atoms.iter().copied().collect();
    !foreign_theory_atoms(ctx, assertions, &fp_set).is_empty()
}

/// Third-theory fence for the lifted mixed BV+FP path (slice 4b). Returns true
/// if any Bool-sorted atom is NEITHER a collected FP atom NOR a collected BV
/// atom NOR pure Boolean structure (i.e. an arrays/LIA/EUF atom) — such a query
/// still fences to `Unknown`. Generalizes `has_non_fp_theory_atom` from the FP
/// set to the BV∪FP allow-set by delegating to it with the union.
pub fn has_non_bvfp_theory_atom(
    ctx: &Context,
    assertions: &[TermId],
    fp_atoms: &[TermId],
    bv_atoms: &[TermId],
) -> bool {
    let mut union: Vec<TermId> = Vec::with_capacity(fp_atoms.len() + bv_atoms.len());
    union.extend_from_slice(fp_atoms);
    union.extend_from_slice(bv_atoms);
    has_non_fp_theory_atom(ctx, assertions, &union)
}

/// `Vec`-returning sibling of `has_non_bvfp_theory_atom`: every Bool-sorted
/// atom NEITHER a collected FP atom NOR a collected BV atom NOR pure Boolean
/// structure, returned so the caller (`bridge_admissible`) can further classify
/// each one (e.g. accept pure-LRA-Real atoms) instead of just fencing. Shares
/// the `foreign_theory_atoms` walk with `has_non_fp_theory_atom` (DRY).
fn non_bvfp_atoms(
    ctx: &Context,
    assertions: &[TermId],
    fp_atoms: &[TermId],
    bv_atoms: &[TermId],
) -> Vec<TermId> {
    let mut allow: rustc_hash::FxHashSet<TermId> =
        rustc_hash::FxHashSet::with_capacity_and_hasher(
            fp_atoms.len() + bv_atoms.len(),
            Default::default(),
        );
    allow.extend(fp_atoms.iter().copied());
    allow.extend(bv_atoms.iter().copied());
    foreign_theory_atoms(ctx, assertions, &allow)
}

/// True iff every crossing conversion present is an admitted `fp.to_real`
/// (operand Float with eb ≤ 8) — i.e. NO symbolic-Real `to_fp`, and no
/// `fp.to_real` over a too-large format. NOTE: this is vacuously true when NO
/// crossing conversion is present at all (including when there is no
/// `fp.to_real` term whatsoever) — callers must NOT treat this alone as
/// evidence that a `fp.to_real` bridge is in play; see
/// `has_admitted_to_real_term` in `bridge_admissible` for that.
fn only_crossing_is_admitted_to_real(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return true; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            match op {
                Op::Builtin(BuiltinOp::FpToReal) => {
                    // admitted iff operand is Float with eb <= 8
                    match ctx.fp_widths(ctx.sort_of(kids[0])) {
                        Some((eb, _sb)) if eb <= 8 => {}
                        _ => return false,
                    }
                }
                Op::Builtin(BuiltinOp::ToFp { .. }) => {
                    // any symbolic-Real to_fp face is NOT admitted here.
                    if kids.len() == 2
                        && matches!(ctx.sort_node(ctx.sort_of(kids[1])), SortNode::Real)
                        && ctx.const_real_value(kids[1]).is_none()
                    {
                        return false;
                    }
                }
                _ => {}
            }
            return kids.into_iter().all(|c| walk(ctx, c, seen));
        }
        true
    }
    assertions.iter().all(|&a| walk(ctx, a, &mut seen))
}

/// True iff at least one `fp.to_real` term with an admitted operand (eb ≤ 8)
/// is actually present. SCOPE-TIGHTENING (slice 9 pre-flight finding):
/// `only_crossing_is_admitted_to_real` alone is vacuously true when there is
/// no crossing conversion at all — including when there is no `fp.to_real`
/// term whatsoever. Combined with "every non-BVFP atom is pure-LRA-Real",
/// `bridge_admissible` would otherwise wrongly accept an FP+BV query that
/// merely happens to have a bare-Real LRA atom alongside it but never
/// actually uses the `fp.to_real` bridge — a shape outside this slice's
/// intended scope ("fp.to_real freely mixed with LRA"). Requiring at least
/// one admitted `fp.to_real` term closes that gap; every shape this slice
/// intends to admit already contains one, so this never rejects an in-scope
/// query.
fn has_admitted_to_real_term(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return false; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            if matches!(op, Op::Builtin(BuiltinOp::FpToReal))
                && matches!(ctx.fp_widths(ctx.sort_of(kids[0])), Some((eb, _)) if eb <= 8)
            {
                return true;
            }
            return kids.into_iter().any(|c| walk(ctx, c, seen));
        }
        false
    }
    assertions.iter().any(|&a| walk(ctx, a, &mut seen))
}

/// A Bool atom that is a pure LRA (Real) arith relation: Le/Lt/Ge/Gt/Eq/Distinct
/// whose operands are Real-sorted (so it routes to Arith, not Int/EUF/arrays).
fn is_lra_real_atom(ctx: &Context, t: TermId) -> bool {
    if let TermNode::App { op, args, .. } = ctx.term_node(t) {
        use BuiltinOp::*;
        if matches!(op, Op::Builtin(Le | Lt | Ge | Gt | Eq | Distinct)) {
            let kids = ctx.children(*args);
            return kids.iter().all(|&k| matches!(ctx.sort_node(ctx.sort_of(k)), SortNode::Real));
        }
    }
    false
}

/// The exact shape QF_FP slice 9 admits for the fp.to_real bridge: FP present,
/// only crossing is an admitted fp.to_real, at least one such admitted
/// fp.to_real term is actually present (scope-tightening: see
/// `has_admitted_to_real_term`), and every atom outside (fp_atoms ∪ bv_atoms)
/// is a pure-LRA-Real arith atom. Anything else → false (caller keeps fencing
/// to sound Unknown). NOT YET WIRED into dispatch — no behavior change.
/// Used by unit tests only for now; dispatch wiring lands in a later slice-9
/// task (same convention as `abv_stage::solve_qfabv`).
pub fn bridge_admissible(ctx: &Context, assertions: &[TermId]) -> bool {
    if !solver_uses_fp(ctx, assertions) { return false; }
    if !only_crossing_is_admitted_to_real(ctx, assertions) { return false; }
    if !has_admitted_to_real_term(ctx, assertions) { return false; }
    let fp_atoms = collect_fp_atoms(ctx, assertions);
    let bv_atoms = crate::bv_stage::collect_bv_atoms(ctx, assertions);
    // Every non-BVFP Bool atom must be a pure-LRA-Real atom. Reuse the existing
    // atom-walk used by has_non_bvfp_theory_atom (via non_bvfp_atoms) but
    // accept is_lra_real_atom instead of unconditionally fencing.
    non_bvfp_atoms(ctx, assertions, &fp_atoms, &bv_atoms)
        .into_iter()
        .all(|t| is_lra_real_atom(ctx, t))
}

/// Collect every distinct `(fp.to_real _)` application term reachable from the
/// assertions (dedup by TermId). Used by the dispatch to drive the Real-bridge
/// emitter (slice 9). Order is deterministic (first-seen DAG walk).
pub fn collect_fp_to_real_terms(ctx: &Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, out: &mut Vec<TermId>,
            visited: &mut rustc_hash::FxHashSet<TermId>) {
        if !visited.insert(t) { return; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            if matches!(op, Op::Builtin(BuiltinOp::FpToReal)) {
                out.push(t);
            }
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            for k in kids { walk(ctx, k, out, visited); }
        }
    }
    for &a in assertions { walk(ctx, a, &mut out, &mut visited); }
    out
}

/// Positively-enumerated check: is an FP-sorted `word` term one that
/// `shinri_fp::FpBlaster::blast_word` can handle in slice 1 (FpAbs/FpNeg),
/// slice 2a (FpAdd/FpSub), slice 2b (FpMul), slice 2c (FpDiv), slice 2c′ (FpSqrt),
/// slice 2e (FpRoundToIntegral/FpMin/FpMax), slice 2f (FpFma), slice 2g (FpRem),
/// slice 3a (non-BV ToFp: FP->FP re-round, const-Real fold), or slice 4d
/// (int→FP: ToFp 2-arg BV-source / ToFpUnsigned)?
///
/// Supported: FP constants, nullary FP variables, FpAbs/FpNeg applied
/// (recursively) to supported words, FpAdd/FpSub/FpMul/FpDiv where the RM operand is a
/// RoundingMode term (literal const or nullary RM variable) and both FP operands
/// are recursively supported, FpSqrt where the RM operand is a RoundingMode
/// term and the single FP operand is recursively supported, FpRoundToIntegral with
/// RM and FP operand both recursively supported, FpMin/FpMax with both FP operands
/// recursively supported, FpFma with RM and all three FP operands recursively
/// supported, FpRem (no RM operand) with both FP operands recursively
/// supported, ToFp (RM, X) where X is a recursively supported FP word, a
/// constant Real, or a BV-sorted term (signed int→FP, slice 4d), and
/// ToFpUnsigned (RM, BV) (unsigned int→FP, slice 4d). EVERYTHING else is NOT
/// supported (any unknown/future FP op defaults to unsupported, including
/// ToFp with a symbolic-Real operand). This ensures that adding a new FP op
/// to the core does not silently route through blast_word and panic.
fn is_supported_fp_word(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        // FP constant → supported.
        TermNode::Const { val: ConstVal::Float(_), .. } => true,
        // Nullary uninterpreted symbol of Float sort (FP variable) → supported.
        // The explicit sort check matters now that `is_supported_fp_word` can be
        // called on a non-FP operand (ToFp's second argument may be Real-sorted);
        // without it a symbolic Real variable would wrongly pass as "supported".
        TermNode::App { op: Op::Uninterpreted(_), args, .. } => {
            matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::Float(_, _))
                && ctx.children(*args).is_empty()
        }
        // FpAbs / FpNeg: supported if the single child is supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpAbs | BuiltinOp::FpNeg), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 1 && is_supported_fp_word(ctx, kids[0])
        }
        // FpAdd / FpSub / FpMul / FpDiv: (RM, F, F). RM operand must be a RoundingMode term
        // (literal const or nullary RM variable); both FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpAdd | BuiltinOp::FpSub | BuiltinOp::FpMul | BuiltinOp::FpDiv), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 3
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
                && is_supported_fp_word(ctx, kids[2])
        }
        // FpSqrt / FpRoundToIntegral: (RM, F). RM operand must be a RoundingMode
        // term; FP operand supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpSqrt | BuiltinOp::FpRoundToIntegral), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // fp.min / fp.max: (F, F) -> F. No RM operand; both FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpMin | BuiltinOp::FpMax), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_supported_fp_word(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // FpFma: (RM, F, F, F) -> F. RM operand must be a RoundingMode term;
        // all three FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpFma), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 4
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
                && is_supported_fp_word(ctx, kids[2])
                && is_supported_fp_word(ctx, kids[3])
        }
        // fp.rem: (F, F) -> F. No RM operand; both FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpRem), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_supported_fp_word(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // to_fp: 1-arg (X) or 2-arg (RM, X). The 1-arg face is the BV bitcast
        // (slice 4c): a single BV-sorted source. The 2-arg faces are the
        // 3a-supported FP->FP re-round (X is a supported FP word), constant-Real
        // fold, or the 4d-supported signed int→FP (X is a BV-sorted source).
        // Symbolic Real stays unsupported (later Real combination). Fence and
        // folder share Context::const_real_value so the admit-set is identical
        // (soundness).
        TermNode::App { op: Op::Builtin(BuiltinOp::ToFp { .. }), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            match kids.len() {
                // 1-arg BV bitcast: single BV-sorted source (slice 4c). Since 4e
                // the BV source can itself embed FP subterms (fp.to_ubv/to_sbv),
                // so a sort check alone no longer suffices — walk it too.
                1 => matches!(ctx.sort_node(ctx.sort_of(kids[0])), SortNode::BitVec(_))
                    && bv_subtree_fp_supported(ctx, kids[0]),
                // 2-arg faces: FP→FP re-round / constant-Real fold (3a), or
                // signed int→FP from a BV source (4d). BV children need a sort
                // check AND (since 4e) the embedded-FP walk — nested still-crossing
                // ops are separately caught by `uses_crossing_conversion`.
                2 => is_rounding_mode_term(ctx, kids[0])
                    && (is_supported_fp_word(ctx, kids[1])
                        || ctx.const_real_value(kids[1]).is_some()
                        || (matches!(ctx.sort_node(ctx.sort_of(kids[1])), SortNode::BitVec(_))
                            && bv_subtree_fp_supported(ctx, kids[1]))),
                _ => false,
            }
        }
        // to_fp_unsigned: (RM, bv) — unsigned int→FP (slice 4d). BV-sort check
        // plus (since 4e) the embedded-FP walk over the BV source.
        TermNode::App { op: Op::Builtin(BuiltinOp::ToFpUnsigned { .. }), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_rounding_mode_term(ctx, kids[0])
                && matches!(ctx.sort_node(ctx.sort_of(kids[1])), SortNode::BitVec(_))
                && bv_subtree_fp_supported(ctx, kids[1])
        }
        // fp constructor (fp sign exp sig): three BV-sorted children. Each needs
        // a sort check plus (since 4e) the embedded-FP walk, since a BV child can
        // now embed fp.to_ubv/to_sbv; any still-crossing op nested in a child is
        // separately caught by `uses_crossing_conversion` before lowering.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpFromBits), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 3
                && kids.iter().all(|&k| {
                    matches!(ctx.sort_node(ctx.sort_of(k)), SortNode::BitVec(_))
                        && bv_subtree_fp_supported(ctx, k)
                })
        }
        // Anything else (a not-yet-implemented FP op, non-nullary UF,
        // symbolic-Real to_fp, fp.to_real, etc.) is not in scope. Word-sorted
        // ite can no longer reach this arm: word_norm (slice 5) eliminates it
        // into a fresh-symbol definition before atom collection ever runs;
        // this arm stays as the defensive catch-all for genuinely unsupported
        // shapes. Note: fp.to_ubv/fp.to_sbv never appear here — they are
        // BV-sorted, so they can't BE an FP word; they are handled by
        // `is_supported_fp_to_bv`/`bv_subtree_fp_supported`.
        _ => false,
    }
}

/// A RoundingMode operand we can blast: a RoundingMode literal constant, or a
/// nullary uninterpreted symbol of RoundingMode sort.
fn is_rounding_mode_term(ctx: &Context, t: TermId) -> bool {
    if !matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::RoundingMode) {
        return false;
    }
    match ctx.term_node(t) {
        TermNode::Const { val: ConstVal::Rm(_), .. } => true,
        TermNode::App { op: Op::Uninterpreted(_), args, .. } => ctx.children(*args).is_empty(),
        _ => false,
    }
}

/// A supported FP→BV application (slice 4e): (RM, F) with a blastable RM and a
/// recursively supported FP operand. Unlike int→FP's BV child (4d), the FP
/// operand DOES need the recursive check — the FP blaster is not total.
fn is_supported_fp_to_bv(ctx: &Context, t: TermId) -> bool {
    let TermNode::App { op: Op::Builtin(BuiltinOp::FpToUbv(_) | BuiltinOp::FpToSbv(_)), args, .. } =
        ctx.term_node(t)
    else {
        return false;
    };
    let kids = ctx.children(*args).to_vec();
    kids.len() == 2
        && is_rounding_mode_term(ctx, kids[0])
        && is_supported_fp_word(ctx, kids[1])
}

/// Walk a BV-sorted subtree hunting embedded FP→BV applications; each must be
/// fully supported. Mutually recursive with `is_supported_fp_word`: since 4e a
/// BV subtree can contain FP subtrees (via fp.to_ubv/to_sbv) and vice versa
/// (via int→FP / bitcast / fp-constructor BV children), so the old 4c/4d
/// argument — that a bare sort check on a BV-sorted subtree is enough to
/// guarantee it blasts cleanly — holds only modulo this walk.
fn bv_subtree_fp_supported(ctx: &Context, root: TermId) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return true; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            if matches!(op, Op::Builtin(BuiltinOp::FpToUbv(_) | BuiltinOp::FpToSbv(_))) {
                // The FP operand is checked by is_supported_fp_word (which
                // re-enters this walk for ITS BV children); no further descent.
                return is_supported_fp_to_bv(ctx, t);
            }
            return ctx.children(*args).to_vec().into_iter().all(|k| walk(ctx, k, seen));
        }
        true
    }
    walk(ctx, root, &mut seen)
}

/// Solver-facing: every collected BV atom's operands must pass the embedded-FP
/// support walk. Until 4e BV atoms could not contain FP subterms, so this is
/// the first slice that support-checks the BV side at all.
pub fn bv_atoms_fp_supported(ctx: &Context, bv_atoms: &[TermId]) -> bool {
    bv_atoms.iter().all(|&a| {
        let TermNode::App { args, .. } = ctx.term_node(a) else { return true; };
        ctx.children(*args).to_vec().into_iter().all(|k| bv_subtree_fp_supported(ctx, k))
    })
}

/// Soundness fence: true iff EVERY collected FP atom is fully supported by the
/// slice-1 blaster. An atom is supported iff:
/// - Its op is one of the 7 classifications, FpEq, or core Eq/Distinct with
///   Float-sorted operands, AND
/// - Every FP-sorted operand subtree is a `is_supported_fp_word`.
///
/// Call this BEFORE `shinri_fp::lower` so that `blast_atom`/`blast_word`'s
/// `unreachable!` arms remain true internal invariants rather than user-triggered
/// panics. Returns false if ANY atom is out of scope.
pub fn fp_atoms_fully_supported(ctx: &Context, fp_atoms: &[TermId]) -> bool {
    fp_atoms.iter().all(|&atom| fp_atom_is_supported(ctx, atom))
}

fn fp_atom_is_supported(ctx: &Context, atom: TermId) -> bool {
    use BuiltinOp::*;
    let TermNode::App { op, args, .. } = ctx.term_node(atom) else {
        return false;
    };
    let kids = ctx.children(*args).to_vec();
    match op {
        // 7 classification predicates: single FP-sorted operand required.
        Op::Builtin(FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite
                    | FpIsNaN | FpIsNegative | FpIsPositive) => {
            kids.len() == 1 && is_supported_fp_word(ctx, kids[0])
        }
        // fp.eq: two FP-sorted operands.
        Op::Builtin(FpEq) => {
            kids.len() == 2
                && is_supported_fp_word(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // core = or distinct over Float-sorted operands (all supported words),
        // or over RoundingMode-sorted operands (slice 5: all RM literals or
        // nullary RM variables — post-word_norm, no other RM shapes exist).
        Op::Builtin(Eq | Distinct) => {
            if kids.iter().all(|&k| is_rm_sorted(ctx, k)) {
                kids.iter().all(|&k| is_rounding_mode_term(ctx, k))
            } else {
                kids.iter().all(|&k| {
                    matches!(ctx.sort_node(ctx.sort_of(k)), SortNode::Float(_, _))
                        && is_supported_fp_word(ctx, k)
                })
            }
        }
        // fp.lt / fp.leq / fp.gt / fp.geq: two supported FP operands.
        Op::Builtin(FpLt | FpLeq | FpGt | FpGeq) => {
            kids.len() == 2
                && is_supported_fp_word(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // Any other op is not handled.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Op;
    use shinri_num::Integer;

    fn fp_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.fp_sort(8, 24);
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn detects_fp_and_collects_eq_and_predicate() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        let pz = ctx.mk_fp_const(8, 24, Integer::zero());
        let eq = ctx.mk_eq(x, pz).unwrap();
        let assertions = vec![isnan, eq];
        assert!(solver_uses_fp(&ctx, &assertions));
        let atoms = collect_fp_atoms(&ctx, &assertions);
        assert!(atoms.contains(&isnan), "FP predicate collected");
        assert!(atoms.contains(&eq), "FP equality collected (soundness)");
        assert_eq!(atoms.len(), 2);
        assert!(!has_non_fp_theory_atom(&ctx, &assertions, &atoms));
    }

    /// Unit test of the FP-ONLY building-block predicate `has_non_fp_theory_atom`:
    /// given ONLY the FP allow-set, a BV atom is outside it, so the predicate
    /// reports a foreign atom. NOTE (slice 4b): the SOLVER no longer fences a mixed
    /// BV+FP query end-to-end — it routes through the BV∪FP union predicate
    /// `has_non_bvfp_theory_atom` (see `bvfp_union_passes_but_third_theory_fences`).
    /// This test pins the narrower FP-only predicate that the union delegates to.
    #[test]
    fn fp_only_fence_predicate_rejects_bv_atom() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        // a BV atom alongside FP
        let bvs = ctx.bv_sort(8);
        let bf = ctx.declare_fun("b", &[], bvs);
        let bvar = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let ult = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[bvar, one]).unwrap();
        let assertions = vec![isnan, ult];
        let atoms = collect_fp_atoms(&ctx, &assertions);
        assert!(atoms.contains(&isnan));
        assert!(has_non_fp_theory_atom(&ctx, &assertions, &atoms),
                "FP-only predicate: a BV atom is outside the FP allow-set");
    }

    #[test]
    fn fp_add_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[add]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.add inside a predicate is supported");
    }

    #[test]
    fn fp_add_with_symbolic_rm_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rms = ctx.rm_sort();
        let rmf = ctx.declare_fun("rm", &[], rms);
        let rm = ctx.mk_app(Op::Uninterpreted(rmf), &[]).unwrap();
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rm, x, y]).unwrap();
        let z = fp_var(&mut ctx, "z");
        let eq = ctx.mk_eq(add, z).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[eq]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "symbolic RM operand is supported");
    }

    #[test]
    fn fp_mul_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let mul = ctx.mk_app(Op::Builtin(BuiltinOp::FpMul), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[mul]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.mul is in scope as of slice 2b");
    }

    #[test]
    fn fp_div_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let div = ctx.mk_app(Op::Builtin(BuiltinOp::FpDiv), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[div]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.div is in scope as of slice 2c");
    }

    #[test]
    fn fp_sqrt_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let sqrt = ctx.mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[rne, x]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[sqrt]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.sqrt is in scope as of slice 2c'");
    }

    #[test]
    fn fp_roundtointegral_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let rti = ctx.mk_app(Op::Builtin(BuiltinOp::FpRoundToIntegral), &[rne, x]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[rti]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.roundToIntegral is in scope as of slice 2e");
        // Malformed (missing RM operand) must NOT be admitted.
        let bad = ctx.mk_app(Op::Builtin(BuiltinOp::FpRoundToIntegral), &[x]);
        if let Ok(bad) = bad {
            assert!(!super::is_supported_fp_word(&ctx, bad), "arity-1 roundToIntegral rejected");
        }
    }

    #[test]
    fn fp_fma_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let z = fp_var(&mut ctx, "z");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let fma = ctx.mk_app(Op::Builtin(BuiltinOp::FpFma), &[rne, x, y, z]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[fma]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.fma is in scope as of slice 2f");
        // Malformed (missing the third FP operand) must NOT be admitted.
        let bad = ctx.mk_app(Op::Builtin(BuiltinOp::FpFma), &[rne, x, y]);
        if let Ok(bad) = bad {
            assert!(!super::is_supported_fp_word(&ctx, bad), "arity-3 fp.fma rejected");
        }
    }

    #[test]
    fn fp_rem_word_is_supported() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let yf = ctx.declare_fun("y", &[], f32);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let rem = ctx.mk_app(Op::Builtin(BuiltinOp::FpRem), &[x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[rem]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.rem is in scope as of slice 2g");
    }

    #[test]
    fn fence_admits_relations_and_minmax() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        // relation atom
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::FpLt), &[x, y]).unwrap();
        assert!(fp_atoms_fully_supported(&ctx, &[lt]), "fp.lt admitted");
        // min/max nested inside fp.eq (word support)
        let mn = ctx.mk_app(Op::Builtin(BuiltinOp::FpMin), &[x, y]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::FpEq), &[mn, x]).unwrap();
        assert!(fp_atoms_fully_supported(&ctx, &[eq]), "fp.min inside fp.eq admitted");
    }

    #[test]
    fn bitcast_ops_are_not_crossing_but_others_still_are() {
        let mut ctx = Context::new();
        let bv1 = ctx.bv_sort(1);
        let bv8 = ctx.bv_sort(8);
        let bv23 = ctx.bv_sort(23);
        let bv32 = ctx.bv_sort(32);
        let mk = |ctx: &mut Context, s| {
            let f = ctx.declare_fun("v", &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let s = mk(&mut ctx, bv1);
        let e = mk(&mut ctx, bv8);
        let m = mk(&mut ctx, bv23);
        let fp_from_bits = ctx.mk_app(Op::Builtin(BuiltinOp::FpFromBits), &[s, e, m]).unwrap();
        let b32 = mk(&mut ctx, bv32);
        let bitcast = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b32]).unwrap();

        // Newly admitted — NOT crossing.
        assert!(!super::uses_crossing_conversion(&ctx, &[fp_from_bits]), "FpFromBits admitted");
        assert!(!super::uses_crossing_conversion(&ctx, &[bitcast]), "1-arg to_fp admitted");

        // fp.to_real over Float32 (eb=8): admitted (slice 9).
        let x = fp_var(&mut ctx, "x");
        let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
        assert!(!super::uses_crossing_conversion(&ctx, &[toreal]),
                "fp.to_real over F32 is admitted (slice 9)");
        // Float64 (eb=11): STILL crossing — pins the eb<=8 boundary.
        let f64s = ctx.fp_sort(11, 53);
        let xf64 = ctx.declare_fun("x64", &[], f64s);
        let x64 = ctx.mk_app(Op::Uninterpreted(xf64), &[]).unwrap();
        let toreal64 = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x64]).unwrap();
        assert!(super::uses_crossing_conversion(&ctx, &[toreal64]),
                "fp.to_real over F64 (eb>8) stays crossing");
    }

    #[test]
    fn is_supported_fp_word_admits_bitcast() {
        let mut ctx = Context::new();
        let bv1 = ctx.bv_sort(1);
        let bv8 = ctx.bv_sort(8);
        let bv23 = ctx.bv_sort(23);
        let bv32 = ctx.bv_sort(32);
        let mk = |ctx: &mut Context, s| {
            let f = ctx.declare_fun("v", &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let s = mk(&mut ctx, bv1);
        let e = mk(&mut ctx, bv8);
        let m = mk(&mut ctx, bv23);
        let fp_from_bits = ctx.mk_app(Op::Builtin(BuiltinOp::FpFromBits), &[s, e, m]).unwrap();
        let b32 = mk(&mut ctx, bv32);
        let bitcast = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b32]).unwrap();

        assert!(super::is_supported_fp_word(&ctx, fp_from_bits), "FpFromBits word supported");
        assert!(super::is_supported_fp_word(&ctx, bitcast), "1-arg to_fp word supported");
    }

    #[test]
    fn crossing_conversions_detected_supported_faces_not() {
        use shinri_num::Rational;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let bvs = ctx.bv_sort(32);
        let bvf = ctx.declare_fun("bv", &[], bvs);
        let bv = ctx.mk_app(Op::Uninterpreted(bvf), &[]).unwrap();

        // fp.to_sbv (FP→BV) → NOT crossing (admitted in slice 4e).
        let sbv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToSbv(32)), &[rne, x]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[sbv]), "fp.to_sbv admitted (slice 4e)");
        // to_fp from BV (2-arg, BV source) → NOT crossing (admitted in slice 4d).
        let from_bv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[from_bv]), "signed int→FP admitted (slice 4d)");
        // 1-arg BV bitcast to_fp (width 32 == eb+sb) → NOT crossing (admitted in slice 4c).
        let bitcast = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[bv]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[bitcast]), "1-arg bitcast to_fp admitted (slice 4c)");
        // to_fp_unsigned → NOT crossing (admitted in slice 4d).
        let uns = ctx.mk_app(Op::Builtin(BuiltinOp::ToFpUnsigned { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[uns]), "unsigned int→FP admitted (slice 4d)");

        // to_fp FP→FP (3a-supported) → NOT crossing.
        let widen = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 11, sb: 53 }), &[rne, x]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[widen]), "FP->FP to_fp is not crossing");
        // to_fp const-Real (3a-supported) → NOT crossing.
        let real = ctx.real_sort();
        let third = ctx.mk_numeral(Rational::new(1i128.into(), 3i128.into()), real);
        let creal = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, third]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[creal]), "const-Real to_fp is not crossing");
        // symbolic-Real to_fp → crossing (durably fenced).
        let rf = ctx.declare_fun("r", &[], real);
        let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
        let sreal = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, r]).unwrap();
        assert!(uses_crossing_conversion(&ctx, &[sreal]), "symbolic-Real to_fp is crossing");
        // pure FP predicate → NOT crossing.
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[isnan]), "pure FP is not crossing");
    }

    #[test]
    fn int_to_fp_faces_admitted_nested_crossing_still_caught() {
        let mut ctx = Context::new();
        let f32s = ctx.fp_sort(8, 24);
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let bvs = ctx.bv_sort(32);
        let bvf = ctx.declare_fun("bv", &[], bvs);
        let bv = ctx.mk_app(Op::Uninterpreted(bvf), &[]).unwrap();

        // Both int→FP faces: NOT crossing, supported (slice 4d).
        let signed = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        let unsigned =
            ctx.mk_app(Op::Builtin(BuiltinOp::ToFpUnsigned { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[signed]), "signed int→FP admitted");
        assert!(!uses_crossing_conversion(&ctx, &[unsigned]), "unsigned int→FP admitted");
        assert!(super::is_supported_fp_word(&ctx, signed), "signed int→FP word supported");
        assert!(super::is_supported_fp_word(&ctx, unsigned), "unsigned int→FP word supported");

        // Safety net: a still-crossing op nested INSIDE the BV child is caught
        // by the same DAG walk.
        let xf = ctx.declare_fun("x", &[], f32s);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let ubv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(32)), &[rne, x]).unwrap();
        let nested = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, ubv]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[nested]), "to_fp over fp.to_ubv fully admitted (4d+4e)");
    }

    #[test]
    fn to_fp_faces_supported_symbolic_real_not() {
        use shinri_num::Rational;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        // FP->FP widen supported.
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let widen = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 11, sb: 53 }), &[rne, x]).unwrap();
        let isn1 = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[widen]).unwrap();
        assert!(fp_atoms_fully_supported(&ctx, &collect_fp_atoms(&ctx, &[isn1])),
                "to_fp FP->FP is in scope as of slice 3a");
        // const-Real supported.
        let real = ctx.real_sort();
        let third = ctx.mk_numeral(Rational::new(1i128.into(), 3i128.into()), real);
        let conv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, third]).unwrap();
        let isn2 = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[conv]).unwrap();
        assert!(fp_atoms_fully_supported(&ctx, &collect_fp_atoms(&ctx, &[isn2])),
                "const-Real to_fp is in scope as of slice 3a");
        // symbolic-Real to_fp NOT supported (durably fenced).
        let rf = ctx.declare_fun("r", &[], real);
        let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
        let sym = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, r]).unwrap();
        let isn3 = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[sym]).unwrap();
        assert!(!fp_atoms_fully_supported(&ctx, &collect_fp_atoms(&ctx, &[isn3])),
                "symbolic-Real to_fp must stay fenced");
        // BV-operand to_fp IS supported (signed-int→FP, admitted in slice 4d).
        let bvs = ctx.bv_sort(32);
        let bvf = ctx.declare_fun("bv", &[], bvs);
        let bv = ctx.mk_app(Op::Uninterpreted(bvf), &[]).unwrap();
        let bv_conv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        let isn4 = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[bv_conv]).unwrap();
        assert!(fp_atoms_fully_supported(&ctx, &collect_fp_atoms(&ctx, &[isn4])),
                "BV-operand to_fp (signed int->FP) is in scope as of slice 4d");
    }

    #[test]
    fn bvfp_union_passes_but_third_theory_fences() {
        let mut ctx = Context::new();
        // FP atom.
        let x = fp_var(&mut ctx, "x");
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        // BV atom.
        let bvs = ctx.bv_sort(8);
        let bf = ctx.declare_fun("b", &[], bvs);
        let bvar = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let ult = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[bvar, one]).unwrap();

        let fp_atoms = collect_fp_atoms(&ctx, &[isnan, ult]);
        let bv_atoms = crate::bv_stage::collect_bv_atoms(&ctx, &[isnan, ult]);
        // Mixed BV+FP (no crossing op) is NOT fenced by the union predicate.
        assert!(!has_non_bvfp_theory_atom(&ctx, &[isnan, ult], &fp_atoms, &bv_atoms),
                "pure-BV + pure-FP atoms are allowed together");

        // Add a Real (arith) atom → fenced.
        let real = ctx.real_sort();
        let rf = ctx.declare_fun("r", &[], real);
        let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
        let zero = ctx.mk_numeral(shinri_core::Rational::zero(), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[r, zero]).unwrap();
        let asserts = vec![isnan, ult, gt];
        let fp2 = collect_fp_atoms(&ctx, &asserts);
        let bv2 = crate::bv_stage::collect_bv_atoms(&ctx, &asserts);
        assert!(has_non_bvfp_theory_atom(&ctx, &asserts, &fp2, &bv2),
                "a Real arith atom alongside BV+FP must fence");
    }

    #[test]
    fn fp_to_bv_faces_admitted_real_bridge_still_crossing() {
        // Slice 4e: fp.to_ubv/fp.to_sbv are no longer crossing; the PERMANENT
        // fence is fp.to_real + symbolic-Real to_fp.
        let mut ctx = Context::new();
        let f32s = ctx.fp_sort(8, 24);
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let xf = ctx.declare_fun("x", &[], f32s);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let ubv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, x]).unwrap();
        let sbv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToSbv(32)), &[rne, x]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[ubv]), "fp.to_ubv admitted (slice 4e)");
        assert!(!uses_crossing_conversion(&ctx, &[sbv]), "fp.to_sbv admitted (slice 4e)");
        // fp.to_real over Float32 (eb=8): admitted (slice 9).
        let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[toreal]), "fp.to_real F32 admitted (slice 9)");
        // Float64 (eb=11): STILL crossing — pins the eb<=8 boundary.
        let f64s = ctx.fp_sort(11, 53);
        let xf64 = ctx.declare_fun("x64", &[], f64s);
        let x64 = ctx.mk_app(Op::Uninterpreted(xf64), &[]).unwrap();
        let toreal64 = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x64]).unwrap();
        assert!(uses_crossing_conversion(&ctx, &[toreal64]),
                "fp.to_real over F64 (eb>8) stays crossing");
        // Symbolic-Real to_fp nested INSIDE an admitted to_ubv: the DAG walk still nets it.
        let real = ctx.real_sort();
        let rf = ctx.declare_fun("r", &[], real);
        let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
        let sreal = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, r]).unwrap();
        let nested = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, sreal]).unwrap();
        assert!(uses_crossing_conversion(&ctx, &[nested]), "nested symbolic-Real to_fp still crossing");
    }

    #[test]
    fn bv_atoms_embedded_fp_support_walk() {
        // First slice where a BV atom can legally contain FP subterms. A supported
        // to_ubv under a BV atom passes; an UNSUPPORTED FP shape under the to_ubv
        // must fence. Post-word_norm (slice 5) a raw FP-sorted ite can no longer
        // reach this walk via the normal pipeline — word_norm eliminates it
        // upstream — but this test constructs the shape directly (bypassing
        // word_norm) to pin the defensive `is_supported_fp_word` catch-all arm.
        let mut ctx = Context::new();
        let f32s = ctx.fp_sort(8, 24);
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let xf = ctx.declare_fun("x", &[], f32s);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let ubv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, x]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(3u64));
        let atom_ok = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[ubv, c]).unwrap();
        assert!(bv_atoms_fp_supported(&ctx, &[atom_ok]), "supported FP operand under BV atom passes");
        // Raw FP-sorted ite: unreachable via the normal pipeline post-word_norm,
        // but is_supported_fp_word must still correctly reject it as a
        // defense-in-depth invariant.
        let bs = ctx.bool_sort();
        let pf = ctx.declare_fun("p", &[], bs);
        let p = ctx.mk_app(Op::Uninterpreted(pf), &[]).unwrap();
        let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[p, x, x]).unwrap();
        let ubv_bad = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, ite]).unwrap();
        let atom_bad = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[ubv_bad, c]).unwrap();
        assert!(!bv_atoms_fp_supported(&ctx, &[atom_bad]), "unsupported FP shape under BV atom fences");
    }

    #[test]
    fn rm_content_triggers_fp_path_and_collection() {
        let mut ctx = Context::new();
        let rms = ctx.rm_sort();
        let rf = ctx.declare_fun("r", &[], rms);
        let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[r, rne]).unwrap();
        // Routing: an RM-only script must enter the FP path (the EUF leak fix).
        assert!(solver_uses_fp(&ctx, &[atom]), "RM content routes to the FP path");
        // Collection: the RM equality is an FP atom.
        let atoms = collect_fp_atoms(&ctx, &[atom]);
        assert_eq!(atoms, vec![atom]);
        // Support: RM =/distinct over RM literals/variables is admitted.
        assert!(fp_atoms_fully_supported(&ctx, &atoms));
    }

    #[test]
    fn bridge_admissible_accepts_to_real_plus_lra() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
        let real = ctx.real_sort();
        let c = ctx.mk_numeral(shinri_num::Rational::new(Integer::from(1i64), Integer::from(1i64)), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[toreal, c]).unwrap();
        assert!(super::bridge_admissible(&ctx, &[gt]), "to_real(F32)+LRA is admissible");
    }

    #[test]
    fn bridge_admissible_rejects_symbolic_to_fp() {
        // symbolic-Real to_fp must NOT be admitted (stays fenced elsewhere).
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let rf = ctx.declare_fun("r", &[], real);
        let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let z = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, r]).unwrap();
        assert!(!super::bridge_admissible(&ctx, &[z]));
    }

    #[test]
    fn bridge_admissible_rejects_large_format() {
        let mut ctx = Context::new();
        let f64 = ctx.fp_sort(11, 53);
        let xf = ctx.declare_fun("x", &[], f64);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
        let real = ctx.real_sort();
        let c = ctx.mk_numeral(shinri_num::Rational::zero(), real);
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[toreal, c]).unwrap();
        assert!(!super::bridge_admissible(&ctx, &[eq]), "eb>=11 stays fenced");
    }

    /// Scope-tightening canary: FP+BV plus a bare-Real LRA atom but ZERO
    /// fp.to_real terms must NOT be admitted. Without this guard,
    /// `only_crossing_is_admitted_to_real` is vacuously true (no crossing op to
    /// reject) and every non-BVFP atom here IS pure-LRA, so `bridge_admissible`
    /// would wrongly lift the fence on a shape this slice never intended to
    /// admit (design scope is "fp.to_real freely mixed with LRA", not "any FP
    /// query with an incidental bare-Real atom").
    #[test]
    fn bridge_admissible_requires_a_to_real_term() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        let bvs = ctx.bv_sort(8);
        let bf = ctx.declare_fun("b", &[], bvs);
        let bvar = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let ult = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[bvar, one]).unwrap();
        let real = ctx.real_sort();
        let rf = ctx.declare_fun("r", &[], real);
        let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
        let zero = ctx.mk_numeral(shinri_num::Rational::zero(), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[r, zero]).unwrap();
        let assertions = vec![isnan, ult, gt];
        assert!(!super::bridge_admissible(&ctx, &assertions),
                "no fp.to_real term present: bridge is not admissible, fence still governs");
    }
}
