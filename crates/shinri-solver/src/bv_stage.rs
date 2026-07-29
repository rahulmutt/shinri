//! BV lowering stage: detect QF_BV queries, collect the atoms the blaster owns,
//! enforce the mixed-theory fence, and carry the CNF→SAT surrogate maps.
//!
//! ## What `collect_bv_atoms` collects (slice 45: no longer just "BV atoms")
//!
//! The name is historical. Since slice 45 the set is **"the Bool-sorted atoms
//! the bit-blaster owns"**, which is strictly larger than "atoms with a BV
//! operator on top". The name was kept rather than changed to
//! `collect_blastable_atoms` (spec §4.1 permits either): the alternative is a
//! 28-occurrence mechanical rename spanning three crates and the committed
//! slice-44 spec, landing in the same diff as this slice's soundness-relevant
//! fence edits, where it would swamp them for a reviewer. The precision goes
//! here instead. Three subtleties, each load-bearing in a different direction:
//!
//! **1. BV (dis)equalities are INCLUDED — for soundness.** The theory's
//! `classify_equality` routes any `(= a b)` whose operand sort is neither Int
//! nor Real to `Owner::Euf`, where BV operators are treated as UNINTERPRETED
//! functions. So `(= (bvadd x #x01) x)` would be answered SAT by EUF when the
//! true BV answer is UNSAT. Therefore EVERY BV atom — including BV
//! (dis)equalities — MUST be surrogated (intercepted by the Encoder and mapped
//! to a pre-blasted SAT literal) so it never reaches `register_atom`/`classify`.
//!
//! **2. NON-NULLARY Bool-result uninterpreted applications are INCLUDED — for
//! completeness (slice 45).** `(p x)` with `p : (_ BitVec 8) → Bool` used to
//! fall through to `has_non_bv_theory_atom`'s conservative "any other
//! Bool-sorted App is a foreign atom" arm and fence the whole query to
//! `unknown`. It is now a collected atom, so the blaster owns it
//! (`blast_bv_atom`'s `Op::Uninterpreted` arm, at result width 1) and every
//! fence's walk returns at it.
//!
//! **3. NULLARY Bool applications are EXCLUDED — for soundness, on the ABV
//! path.** This is the one that is easy to read as tidiness and is not: a bare
//! Bool constant handed to the blaster would get a FRESH unconstrained literal
//! per call, with nothing registered in `uf_apps` to pair the occurrences. The
//! ABV driver calls `blast_atom` unmemoized, so one constant would get two
//! independent literals — a wrong `sat`. Full argument at the arm itself.
//!
//! Consequence of (2) worth stating once here, because it is the mechanism
//! behind the `arg_term_blastable` check further down: a collected atom is a
//! **leaf** to `has_non_bv_theory_atom`, which does not descend into it. So
//! collecting a Bool UF application also HIDES its argument subtrees from the
//! foreign-theory fence. Fence 1 (`uf_args_supported`) is what must catch a
//! foreign term hiding there, and — as slice 45 measured — an argument *sort*
//! check alone was not enough.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Lit, Op, SortId, SortNode, TermId, TermNode, Var};

/// Surrogate maps produced by lowering BV atoms to CNF and replaying that CNF
/// into the SAT solver. The Encoder consults `atom_to_lit` so a BV atom returns
/// its pre-blasted representative literal instead of being registered as a
/// theory atom. `var_bits` is stashed for model extraction (Task 18).
pub struct BvSurrogates {
    pub atom_to_lit: FxHashMap<TermId, Lit>,
    pub var_bits: FxHashMap<TermId, Vec<Var>>,
    /// First SAT `Var` index of this CNF's contiguous var block (slice 6:
    /// lets callers remap other blaster-namespace `BitLit`s, e.g. RM
    /// selectors, to SAT `Lit`s without re-deriving the block start).
    pub base: u32,
}

/// True if `t`'s sort is a `(_ BitVec n)`.
fn is_bv_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::BitVec(_))
}

/// True if `op` is a bitvector builtin (any BV operator, predicate or not).
fn is_bv_op(op: &Op) -> bool {
    matches!(
        op,
        Op::Builtin(
            BuiltinOp::BvNot
                | BuiltinOp::BvAnd
                | BuiltinOp::BvOr
                | BuiltinOp::BvXor
                | BuiltinOp::BvNand
                | BuiltinOp::BvNor
                | BuiltinOp::BvXnor
                | BuiltinOp::BvNeg
                | BuiltinOp::BvAdd
                | BuiltinOp::BvSub
                | BuiltinOp::BvMul
                | BuiltinOp::BvUdiv
                | BuiltinOp::BvUrem
                | BuiltinOp::BvSdiv
                | BuiltinOp::BvSrem
                | BuiltinOp::BvSmod
                | BuiltinOp::BvShl
                | BuiltinOp::BvLshr
                | BuiltinOp::BvAshr
                | BuiltinOp::BvUlt
                | BuiltinOp::BvUle
                | BuiltinOp::BvUgt
                | BuiltinOp::BvUge
                | BuiltinOp::BvSlt
                | BuiltinOp::BvSle
                | BuiltinOp::BvSgt
                | BuiltinOp::BvSge
                | BuiltinOp::BvConcat
                | BuiltinOp::BvExtract { .. }
                | BuiltinOp::BvZeroExtend(_)
                | BuiltinOp::BvSignExtend(_)
                | BuiltinOp::BvRotateLeft(_)
                | BuiltinOp::BvRotateRight(_)
                | BuiltinOp::BvRepeat(_)
        )
    )
}

/// True if `op` is a bitvector PREDICATE (Bool-sorted result).
fn is_bv_predicate(op: &Op) -> bool {
    matches!(
        op,
        Op::Builtin(
            BuiltinOp::BvUlt
                | BuiltinOp::BvUle
                | BuiltinOp::BvUgt
                | BuiltinOp::BvUge
                | BuiltinOp::BvSlt
                | BuiltinOp::BvSle
                | BuiltinOp::BvSgt
                | BuiltinOp::BvSge
        )
    )
}

/// True if any subterm of any assertion has a BitVec sort or a BV builtin op.
pub fn solver_uses_bv(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) {
            return false;
        }
        if is_bv_sorted(ctx, t) {
            return true;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                if is_bv_op(op) {
                    return true;
                }
                ctx.children(*args)
                    .to_vec()
                    .into_iter()
                    .any(|c| walk(ctx, c, seen))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a, &mut seen))
}

/// Collect the Bool-sorted atoms the BIT-BLASTER OWNS. Despite the name this is
/// no longer "atoms with a BV operator on top": subterms whose top op is a BV
/// predicate, an Eq/Distinct whose operands are BV-sorted, OR — since slice 45
/// — a NON-NULLARY uninterpreted application with a Bool result sort.
///
/// SOUNDNESS-CRITICAL in both directions: BV (dis)equalities ARE included and
/// nullary Bool applications are EXCLUDED. Both reasons, plus the leaf-rule
/// consequence of the slice-45 widening, are in the module doc; the nullary
/// argument is restated in full at its arm below.
pub fn collect_bv_atoms(ctx: &Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    let mut in_set: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(
        ctx: &Context,
        t: TermId,
        out: &mut Vec<TermId>,
        in_set: &mut rustc_hash::FxHashSet<TermId>,
        visited: &mut rustc_hash::FxHashSet<TermId>,
    ) {
        if !visited.insert(t) {
            return;
        }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            let is_atom = match op {
                _ if is_bv_predicate(op) => true,
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) => {
                    kids.iter().any(|&k| is_bv_sorted(ctx, k))
                }
                // Slice 45: a NON-NULLARY Bool-result uninterpreted
                // application. The blaster owns it (`blast_bv_atom`'s
                // `Op::Uninterpreted` arm), so collecting it here is what lets
                // the foreign-theory fences pass it: a collected atom is in
                // `bv_set` and each fence's walk returns at it.
                //
                // The `!kids.is_empty()` conjunct is LOAD-BEARING FOR
                // SOUNDNESS, not tidiness. `blast_bv_atom` is uncached by
                // contract, and `blast_uf_app`'s nullary branch mints a FRESH
                // unconstrained literal while registering nothing in `uf_apps`
                // — so nothing pairs two occurrences of one nullary Bool
                // application and forces their literals equal, the rescue a
                // non-nullary repeat gets from congruence. Whether a repeat
                // call happens is the driver's business and the drivers do NOT
                // agree: tseitin memoizes by TermId before interception
                // (`tseitin.rs`'s `encode`) and `shinri_bv::lower` memoizes by
                // rewritten TermId, but the ARRAY path does not —
                // `abv_stage::RealBridge::new` loops `blast_atom` over the
                // collected atoms unmemoized (`abv_stage.rs:357-363`) and
                // `ensure_atom_lit` (`:307-313`) calls it again on demand.
                // There, collecting a nullary Bool application would give one
                // Bool constant two INDEPENDENT literals, true in one
                // occurrence and false in another: a wrong `sat`. The
                // `debug_assert!` in the blaster's arm is a development
                // tripwire that vanishes in the shipping profile; THIS
                // exclusion is the guard.
                //
                // That array-path hazard IS LIVE as of slice 45 Task 5. It was
                // previously masked: `abv_stage::fenced` fenced every
                // non-nullary Bool-sorted application at `lib.rs:903`, before
                // `RealBridge::new` collected anything, so no Bool-result
                // application reached that driver and this exclusion was
                // defence in depth. Task 5 widened that fence (authorized after
                // measurement), so the ABV path now calls this collector for
                // real and THIS CONJUNCT IS LOAD-BEARING FOR SOUNDNESS THERE:
                // collecting a nullary Bool application would hand one Bool
                // constant two independent literals and permit a wrong `sat`.
                //
                // What keeps the nullary case out on that path is this line and
                // nothing else. `abv_stage::fenced` cannot help: its widened
                // branch returns `kids.iter().any(walk_fence)`, which for a
                // nullary application is `Iterator::any` over an EMPTY iterator
                // — `false` by definition, i.e. bit-identical to the `return
                // false` it replaced. So the fence admits nullary Bool
                // applications exactly as it always did, and it is this
                // collector that must decline to hand them to the blaster. A
                // nullary Bool application instead reaches
                // `abv_stage::encode_skeleton`'s catch-all → `bool_leaf`
                // (`abv_stage.rs:505`), which memoizes one SAT var per TermId in
                // `proxy_var` — one constant, one literal, sound.
                //
                // Excluding it costs nothing: a bare Bool constant keeps its
                // existing Tseitin path (`tseitin.rs`'s
                // `Op::Uninterpreted(_) => self.atom(t)`), and
                // `has_non_bv_theory_atom` already exempts it explicitly.
                Op::Uninterpreted(_) => !kids.is_empty() && ctx.sort_of(t) == ctx.bool_sort(),
                _ => false,
            };
            if is_atom && in_set.insert(t) {
                out.push(t);
                // A BV atom is a leaf for theory purposes: do NOT descend into its
                // BV operands looking for more atoms (they are not Bool-sorted
                // atoms anyway). Descending is harmless but unnecessary.
                return;
            }
            for k in kids {
                walk(ctx, k, out, in_set, visited);
            }
        }
    }
    for &a in assertions {
        walk(ctx, a, &mut out, &mut in_set, &mut visited);
    }
    out
}

/// Mixed-theory fence (SOUNDNESS-CRITICAL, conservative).
///
/// Given a BV query, returns true if it ALSO contains any NON-BV theory atom —
/// i.e. an atom (Eq/Distinct/arith-relation/uninterpreted-predicate/array op)
/// that is NOT one of the collected BV atoms and is not pure Boolean structure.
/// Such atoms would route to EUF/Arith/Arrays, which cannot be combined with the
/// eager BV bit-blaster here. When true, the caller returns Unknown.
///
/// Conservative bias: any non-Boolean-structure atom outside the BV set that
/// `classify` recognizes as a theory atom (EUF/Arith/Arrays/Shared) — OR that
/// `classify` refuses (Unsupported) — triggers the fence. Only pure Boolean
/// connectives over BV atoms pass.
pub fn has_non_bv_theory_atom(ctx: &Context, assertions: &[TermId], bv_atoms: &[TermId]) -> bool {
    let bv_set: rustc_hash::FxHashSet<TermId> = bv_atoms.iter().copied().collect();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(
        ctx: &Context,
        t: TermId,
        bv_set: &rustc_hash::FxHashSet<TermId>,
        visited: &mut rustc_hash::FxHashSet<TermId>,
    ) -> bool {
        if bv_set.contains(&t) {
            // A BV atom is surrogated and is a leaf — do not descend.
            return false;
        }
        if !visited.insert(t) {
            return false;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids: Vec<TermId> = ctx.children(*args).to_vec();
                // Pure Boolean structure: recurse into children, not an atom itself.
                let is_bool_structure = matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::Not
                            | BuiltinOp::And
                            | BuiltinOp::Or
                            | BuiltinOp::Implies
                            | BuiltinOp::Xor
                            | BuiltinOp::Ite
                    )
                );
                // Bool-sorted Eq/Distinct over Bool operands is also Boolean
                // structure (iff/xor), handled by the SAT skeleton.
                let is_bool_eq = matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct))
                    && kids
                        .first()
                        .is_some_and(|&k| ctx.sort_of(k) == ctx.bool_sort());
                if is_bool_structure || is_bool_eq {
                    return kids.iter().any(|&k| walk(ctx, k, bv_set, visited));
                }
                // A bare declared Bool constant (0-ary uninterpreted symbol,
                // Bool-sorted — e.g. a `declare-const c Bool` used directly or
                // as an `ite`/`and` condition) needs NO theory reasoning: a
                // nullary symbol has no arguments for congruence to act on, so
                // it is Tseitin-encoded as a plain SAT variable regardless of
                // which theories are otherwise in play (see tseitin.rs's
                // `Op::Uninterpreted(_) => self.atom(t)` arm, used uniformly).
                // It is skeleton, not a foreign theory atom — exempt it from
                // the fence (slice 5: word_norm's ite-elimination exposes bare
                // condition variables like `c` here that were previously
                // buried, unreachable, inside a single opaque BV atom leaf).
                if matches!(op, Op::Uninterpreted(_))
                    && kids.is_empty()
                    && ctx.sort_of(t) == ctx.bool_sort()
                {
                    return false;
                }
                // Any other App node that is Bool-sorted is a candidate atom.
                // (Non-Bool subterms — e.g. arith terms inside a relation — are
                // reached only as operands; we only fence on Bool-sorted atoms,
                // and arith terms are caught via their enclosing relation.)
                if ctx.sort_of(t) == ctx.bool_sort() {
                    // It is not a BV atom (checked above) and not Boolean
                    // structure: a non-BV theory atom. Conservative → fence.
                    // (classify may accept it as EUF/Arith/Arrays or refuse it;
                    // either way it must not coexist with the BV path.)
                    let _ = shinri_theory::atom::classify(ctx, t);
                    return true;
                }
                // Non-Bool App (a term, e.g. arith subexpression): descend so we
                // still find any embedded Bool atoms, but it is not itself one.
                kids.iter().any(|&k| walk(ctx, k, bv_set, visited))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions
        .iter()
        .any(|&a| walk(ctx, a, &bv_set, &mut visited))
}

/// Fence 1 (slice 44 §4, SOUNDNESS-CRITICAL). Every non-nullary uninterpreted
/// application with a **BitVec result sort** — or, since slice 45, a **Bool
/// result sort** — reachable from `atoms` must have arguments the blaster can
/// turn into words, because `blast_uf_app`'s congruence arm compares argument
/// words pairwise, whichever of `blast_bv_word` / `blast_bv_atom` reached it.
///
/// BV-sorted arguments always qualify. FP-sorted arguments qualify only when
/// `allow_fp_args` — that is, on the FP/mixed path, where a `Lowerer` exists
/// with a `core_eq`-based `word_eq`. A `Blaster` alone cannot compare an FP
/// word (`core_eq` lives in `shinri-fp`, which depends on `shinri-bv` and not
/// the reverse).
///
/// Everything else — Int, Bool, Array, String, uninterpreted sorts,
/// RoundingMode — fences the caller to a sound `Unknown`. Without this,
/// `Lowerer::word` reaches its `unreachable!("Lowerer::word on non-BV/non-FP
/// sort")` (`crates/shinri-fp/src/lower.rs:69`) and `Blaster::word` reaches
/// `blast_bv_word`'s builtin dispatch on a non-BV term.
///
/// Walks the ATOM set rather than the assertion list: that is exactly what
/// reaches the blaster, and it stays a superset of what survives `rewrite`
/// (rewriting can fold applications away but never create them), so the
/// conservative bias every other fence in this stage has is preserved.
pub fn uf_args_supported(ctx: &Context, atoms: &[TermId], allow_fp_args: bool) -> bool {
    let mut seen = rustc_hash::FxHashSet::default();
    let mut arg_clean = rustc_hash::FxHashSet::default();
    atoms
        .iter()
        .all(|&a| walk_uf_args(ctx, a, allow_fp_args, &mut seen, &mut arg_clean))
}

/// True if `t`'s sort is an array whose index AND element sorts are both
/// BitVec — the only array shape `shinri-abv` abstracts. Mirrors
/// `abv_stage::is_bv_array`; duplicated rather than shared because
/// `bv_stage` must not depend on the ABV stage's module for a fence that runs
/// on all three paths.
fn is_bv_array(ctx: &Context, t: TermId) -> bool {
    match ctx.sort_node(ctx.sort_of(t)) {
        SortNode::Array(i, e) => ctx.bv_width(*i).is_some() && ctx.bv_width(*e).is_some(),
        _ => false,
    }
}

/// Fence 1's BLASTABILITY half (slice 45 Task 6, SOUNDNESS-CRITICAL).
///
/// A BitVec-sorted argument is necessary but NOT sufficient. `blast_uf_app`'s
/// congruence arm calls `word` on each argument, and `blast_bv_word`'s builtin
/// dispatch has arms only for BV operators: everything else falls into
/// `unreachable!("non-BV builtin reached blast_word")`
/// (`crates/shinri-bv/src/blast/mod.rs:624`). `(select a i)` over
/// `(Array Int (_ BitVec 8))` is BitVec-8-**sorted** and passes the sort check,
/// then panics there — measured on both profiles, slice 45 Task 6.
///
/// Enumerating `BuiltinOp` (`crates/shinri-core/src/term.rs`) against
/// `blast_bv_word`'s dispatch (`blast/mod.rs:448-628`), the BV-sorted heads
/// with no arm are exactly four: `Select`, `Ite`, `FpToUbv`, `FpToSbv`.
///
/// - `Ite` is excluded upstream and unconditionally: `word_norm.normalize`
///   (`lib.rs:759`) eliminates every BV-sorted `ite` BEFORE any fence or
///   routing decision runs, so it cannot reach any path.
/// - `Select`/`Store` is handled below, by array sort.
/// - `FpToUbv`/`FpToSbv` is handled below, by `allow_fp_args`.
///
/// # The two conditional exemptions
///
/// **`select`/`store` over a BV-indexed, BV-valued array is ADMITTED**, and
/// that exemption is load-bearing, not laxity:
/// `abv_stage::uses_arrays_over_bv` (`lib.rs:902`) routes any query containing
/// one to the ABV path, where `shinri_abv::abstract_arrays` substitutes a
/// fresh BV read symbol for every `select` — including those buried in a UF
/// application's arguments, since `shinri-abv`'s `collect`/`subst` walk
/// children generically — BEFORE `collect_bv_atoms` sees the abstraction. So
/// nothing unblastable survives to the blaster there. Rejecting it instead
/// would fence `(f (select a i))` over a BV array to `unknown`, a decided →
/// unknown regression against slice 44's shipped behaviour.
///
/// Conversely, reaching the pure-BV path (`lib.rs:1007`) or the FP/mixed path
/// (`lib.rs:1095`) means `uses_arrays_over_bv` was FALSE, so no BV-array
/// `select` can occur there at all — on those paths this predicate rejects
/// every array access, which is exactly right.
///
/// **`fp.to_ubv`/`fp.to_sbv` is admitted only when `allow_fp_args`** — that
/// is, only where a `shinri_fp::Lowerer` is the sink. `Lowerer::word`
/// intercepts exactly these two ops and routes them to `blast_fp_to_bv`
/// (`crates/shinri-fp/src/lower.rs:52-73`); a bare `shinri_bv::Blaster` has no
/// such interception and sends them straight to `blast_bv_word`'s
/// `unreachable!`. `allow_fp_args` is already precisely "an FP sink exists",
/// so it is the correct discriminator and not a proxy for one.
///
/// The gating is REQUIRED IN BOTH DIRECTIONS, and the review round that found
/// this measured both:
///
/// - Rejecting unconditionally would fence `(= (f ((_ fp.to_ubv 8) RNE x))
///   #x2a)` to `unknown`, where the FP/mixed path decides it `sat` today — a
///   forbidden decided → unknown flip, the same trap the `select` exemption
///   avoids.
/// - Admitting unconditionally leaves the **ABV path** panicking. An earlier
///   revision of this comment claimed these ops "force `solver_uses_fp`, which
///   routes to the FP/mixed path"; that is TRUE of the pure-BV path
///   (`lib.rs:1007` is guarded by `uses_bv && !uses_fp`) and FALSE of the ABV
///   path, whose gate at `lib.rs:902` runs BEFORE any FP routing and `return`s
///   in every arm. `abv_stage` blasts with a bare `Blaster` and passes
///   `allow_fp_args = false` (`lib.rs:910`, and see the Fence-1 comment at
///   `lib.rs:905-908` which states the no-FP-sink property), so this predicate
///   correctly rejects there.
///
/// `abv_stage::fenced` cannot substitute: `(fp.to_ubv rm x)` is not Bool-sorted,
/// so `walk_fence` reaches only its "descend into a non-Bool term" arm
/// (`abv_stage.rs:201-203`) and its kids — `rm` and `x` — are themselves
/// non-Bool-sorted, so each takes that same arm over an EMPTY child list, and
/// `Iterator::any` on an empty iterator is `false`. (Careful: they bottom out
/// via that empty-`kids` `any`, not via the `TermNode::Const` arm — a nullary
/// uninterpreted symbol is an `App` with no children, not a `Const` node.
/// A citation of `:198-200` here would be the wrong arm: that is the "any
/// other Bool-sorted application → `true`" arm, which `(fp.to_ubv rm x)`
/// never reaches. The conclusion is unchanged; it was traced independently.)
///
/// Only positive results are memoized in `clean`: a negative short-circuits
/// the whole `uf_args_supported` call, so it is never revisited. `clean` is
/// minted per `uf_args_supported` call, where `allow_fp_args` is fixed, so the
/// memo cannot leak across a differing flag value.
fn arg_term_blastable(
    ctx: &Context,
    t: TermId,
    allow_fp_args: bool,
    clean: &mut rustc_hash::FxHashSet<TermId>,
) -> bool {
    if clean.contains(&t) {
        return true;
    }
    let ok = match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            let foreign_array_op = matches!(op, Op::Builtin(BuiltinOp::Select | BuiltinOp::Store))
                && !kids.first().is_some_and(|&k| is_bv_array(ctx, k));
            let sinkless_fp_conversion = matches!(
                op,
                Op::Builtin(BuiltinOp::FpToUbv(_) | BuiltinOp::FpToSbv(_))
            ) && !allow_fp_args;
            !foreign_array_op
                && !sinkless_fp_conversion
                && kids
                    .iter()
                    .all(|&k| arg_term_blastable(ctx, k, allow_fp_args, clean))
        }
        TermNode::Const { .. } => true,
    };
    if ok {
        clean.insert(t);
    }
    ok
}

fn walk_uf_args(
    ctx: &Context,
    t: TermId,
    allow_fp_args: bool,
    seen: &mut rustc_hash::FxHashSet<TermId>,
    arg_clean: &mut rustc_hash::FxHashSet<TermId>,
) -> bool {
    if !seen.insert(t) {
        return true; // already validated on another path
    }
    let TermNode::App { op, args, sort } = ctx.term_node(t) else {
        return true; // a constant has no arguments
    };
    let kids = ctx.children(*args).to_vec();
    // Slice 45: BitVec-result (slice 44) OR Bool-result applications. Both are
    // lowered by `blast_uf_app`, whose congruence arm compares argument words
    // pairwise, so both need arguments the blaster can turn into words. The
    // argument-admissibility rule below is unchanged.
    let result_is_blastable = ctx.bv_width(*sort).is_some() || *sort == ctx.bool_sort();
    if matches!(op, Op::Uninterpreted(_)) && !kids.is_empty() && result_is_blastable {
        for &k in &kids {
            let ks = ctx.sort_of(k);
            let wordable =
                ctx.bv_width(ks).is_some() || (allow_fp_args && ctx.fp_widths(ks).is_some());
            if !wordable {
                return false;
            }
            // Slice 45 Task 6: the sort check above is necessary but NOT
            // sufficient — the argument TERM must also be one THIS PATH's sink
            // has an arm for. See `arg_term_blastable`.
            if !arg_term_blastable(ctx, k, allow_fp_args, arg_clean) {
                return false;
            }
        }
    }
    kids.iter()
        .all(|&k| walk_uf_args(ctx, k, allow_fp_args, seen, arg_clean))
}

/// Fence 2 (slice 44 §4). Gate-equivalent cost of the Ackermann encoding for
/// every non-nullary uninterpreted BV-result — or, since slice 45, Bool-result
/// — application reachable from `atoms`: for symbol `s` with `kₛ`
/// applications, total argument width `Aₛ` and result width `wₛ`, the encoding
/// emits `pairs(kₛ) × (Aₛ + wₛ)` gates, where `pairs(k) = k(k−1)/2`. A Bool
/// result counts as `wₛ = 1`: `blast_bv_atom` blasts it at result width 1.
///
/// Nullary applications contribute zero: they emit no congruence at all.
///
/// FP-sorted arguments are counted at `FP_ARG_COST_MULTIPLIER × (eb + sb)`
/// rather than the raw word width `eb + sb`, because a per-pair FP argument
/// comparison goes through `core_eq` (`crates/shinri-fp/src/blast/compare.rs`),
/// not the plain bitwise chain the BV proxy below implicitly models. `core_eq`
/// unpacks BOTH operands (`unpack`, `crates/shinri-fp/src/unpack.rs`: ~`3*eb +
/// 2*sb` gates each, for the all-ones/all-zero exponent and significand scans
/// behind `is_nan`/`is_inf`/`is_zero`) and then still runs a full `bits_eq`
/// bitwise-equality chain (~`3*(eb+sb)` gates) plus a handful of NaN-routing
/// combinators — roughly `9*eb + 7*sb + 10` gates total, against the
/// `3*(eb+sb)` gates a same-width bitwise BV comparison costs. The multiplier
/// below is a ROUNDED-UP REASONED ESTIMATE from that gate count, NOT a
/// measurement — no FP calibration instance has been run.
///
/// Cross-checked against the sources rather than measured: `bits_eq` is 3
/// gates/bit (`crates/shinri-fp/src/blast/compare.rs:7-16`) and `unpack` is
/// `3*eb + 2*sb + 2` (`crates/shinri-fp/src/unpack.rs:18-58`), which puts the
/// true ratio at ~2.60x (Float32), ~2.50x (Float64) and ~2.75x (eb=5/sb=11).
/// Rounding up gives 3, which is what spec §7.3 states. The rounding keeps
/// this the safe (over-counting) direction for FP arguments regardless of when
/// a real calibration eventually happens.
pub fn uf_congruence_cost(ctx: &Context, atoms: &[TermId]) -> u64 {
    let mut per_sym: FxHashMap<UfShapeKey, (u64, u64, u64)> = FxHashMap::default();
    let mut seen = rustc_hash::FxHashSet::default();
    for &a in atoms {
        collect_uf_apps(ctx, a, &mut per_sym, &mut seen);
    }
    let mut total: u64 = 0;
    for (_, (k, arg_bits, res_bits)) in per_sym {
        let pairs = k.saturating_mul(k.saturating_sub(1)) / 2;
        total = total.saturating_add(pairs.saturating_mul(arg_bits.saturating_add(res_bits)));
    }
    total
}

/// See `uf_congruence_cost`'s doc comment: a reasoned (not measured) upper
/// bound on how much more `core_eq` costs per FP argument bit than a plain
/// bitwise BV comparison costs per bit, rounded up from the ~2.5–2.75x gate-
/// count ratio derived there. Keeps the FP-argument cost over-counting, the
/// safe direction for a budget fence.
const FP_ARG_COST_MULTIPLIER: u64 = 3;

/// The grouping key for congruence counting: `(symbol, argument sorts, result
/// sort)`.
///
/// MUST mirror the blaster's pairing predicate (`shape_compatible`,
/// `crates/shinri-bv/src/blast/mod.rs`). A `SymbolId` alone is NOT a function:
/// `Context::declare_fun` interns by name and overwrites the signature, and a
/// redeclaration is accepted silently, so one symbol can carry applications of
/// two different functions in one assertion list. The blaster only relates applications
/// within a shape group; keying this map by symbol alone would merge those
/// groups and OVER-count `pairs(k)` — but it also locked `arg_bits`/`res_bits`
/// to the FIRST application seen (`or_insert`), which for a wider second shape
/// UNDER-counts, and under-counting is the unsafe direction for a budget fence.
/// Keying by shape removes both: within a group every application has the same
/// argument and result widths by construction.
type UfShapeKey = (shinri_core::SymbolId, Vec<shinri_core::SortId>, SortId);

fn collect_uf_apps(
    ctx: &Context,
    t: TermId,
    per_sym: &mut FxHashMap<UfShapeKey, (u64, u64, u64)>,
    seen: &mut rustc_hash::FxHashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    let TermNode::App { op, args, sort } = ctx.term_node(t) else {
        return;
    };
    let kids = ctx.children(*args).to_vec();
    if let Op::Uninterpreted(sym) = op {
        if !kids.is_empty() {
            // Slice 45: a Bool-result application costs `res_bits = 1` — the
            // width-1 congruence emits one clause per prior pair rather than
            // one per result bit. `UfShapeKey` already keys on the result
            // SortId, so Bool and BitVec groups stay separate, mirroring
            // `shape_compatible`'s result-sort discrimination.
            //
            // Counting them at all is what keeps this fence in the SAFE
            // direction: `collect_bv_atoms` now hands Bool-result
            // applications to the blaster, so leaving them out of the cost
            // would UNDER-count, which this function's doc calls the unsafe
            // direction for a budget fence.
            let res_bits = if *sort == ctx.bool_sort() {
                Some(1u32)
            } else {
                ctx.bv_width(*sort)
            };
            if let Some(res_bits) = res_bits {
                let arg_bits: u64 = kids
                    .iter()
                    .map(|&k| {
                        let ks = ctx.sort_of(k);
                        ctx.bv_width(ks)
                            .map(u64::from)
                            .or_else(|| {
                                ctx.fp_widths(ks)
                                    .map(|(eb, sb)| u64::from(eb + sb) * FP_ARG_COST_MULTIPLIER)
                            })
                            .unwrap_or(0)
                    })
                    .sum();
                let key: UfShapeKey = (*sym, kids.iter().map(|&k| ctx.sort_of(k)).collect(), *sort);
                let e = per_sym
                    .entry(key)
                    .or_insert((0, arg_bits, u64::from(res_bits)));
                e.0 += 1;
            }
        }
    }
    for &k in &kids {
        collect_uf_apps(ctx, k, per_sym, seen);
    }
}

/// Calibrated 2026-07-28: the largest encoding that solves in under 30 s on
/// the release binary, measured on a width-32 arity-2 symbol (Aₛ + wₛ = 96,
/// `(set-logic QF_UFBV) (declare-fun g ((_ BitVec 32) (_ BitVec 32)) (_
/// BitVec 32))`, k fresh BV32 vars, k applications `g(vᵢ,vᵢ)` chained
/// `g(v0,v0)=g(v1,v1), g(v1,v1)=g(v2,v2), ...`) with k applications. Chosen so
/// a single fenced query cannot consume the 10–15 min PR-tier budget on its
/// own. Recorded here rather than in the spec because it is a measurement,
/// not a design choice.
///
/// FULL measured k -> wall-clock table (single run each, release binary,
/// foreground `bash time`):
///   k=10  -> 0.013 s
///   k=20  -> 0.050 s
///   k=40  -> 0.206 s
///   k=80  -> 0.843 s
///   k=160 -> 3.484 s
///   k=320 -> 15.429 s
///   k=400 -> 25.140 s
///   k=420 -> 26.920 s
///   k=440 -> 29.203 s   <- largest measured k still under 30 s
///   k=460 -> 32.086 s   <- first measured k over 30 s; true crossing is
///                          between k=440 and k=460
///
/// UF_CONGRUENCE_BUDGET = pairs(440) * 96 = 96,580 * 96 = 9_271_680.
pub const UF_CONGRUENCE_BUDGET: u64 = 9_271_680;

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Op;
    use shinri_num::Integer;

    fn bv_var(ctx: &mut Context, name: &str, w: u32) -> TermId {
        let s = ctx.bv_sort(w);
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn detects_bv_and_collects_eq_and_predicate() {
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let five = ctx.mk_bv_const(8, Integer::from(5u64));
        let add = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, one])
            .unwrap();
        let eq = ctx.mk_eq(add, one).unwrap(); // BV equality
        let ult = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvUlt), &[x, five])
            .unwrap();
        let assertions = vec![eq, ult];
        assert!(solver_uses_bv(&ctx, &assertions));
        let atoms = collect_bv_atoms(&ctx, &assertions);
        // Both the BV equality and the BV predicate must be collected.
        assert!(
            atoms.contains(&eq),
            "BV equality must be collected (soundness)"
        );
        assert!(atoms.contains(&ult), "BV predicate must be collected");
        assert_eq!(atoms.len(), 2);
        // No non-BV theory atom present.
        assert!(!has_non_bv_theory_atom(&ctx, &assertions, &atoms));
    }

    #[test]
    fn mixed_with_real_atom_is_fenced() {
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let eq = ctx.mk_eq(x, one).unwrap();
        let real = ctx.real_sort();
        let yf = ctx.declare_fun("y", &[], real);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let zero = ctx.mk_numeral(shinri_core::Rational::zero(), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[y, zero]).unwrap();
        let assertions = vec![eq, gt];
        let atoms = collect_bv_atoms(&ctx, &assertions);
        assert!(atoms.contains(&eq));
        assert!(
            has_non_bv_theory_atom(&ctx, &assertions, &atoms),
            "Real Gt atom must trigger the mixed fence"
        );
    }

    #[test]
    fn uf_args_supported_admits_bv_arguments() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fx, c]).unwrap();
        assert!(uf_args_supported(&ctx, &[atom], false));
    }

    #[test]
    fn uf_args_supported_rejects_an_int_argument() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let int_s = ctx.int_sort();
        let h = ctx.declare_fun("h", &[int_s], s8);
        let nf = ctx.declare_fun("n", &[], int_s);
        let n = ctx.mk_app(Op::Uninterpreted(nf), &[]).unwrap();
        let hn = ctx.mk_app(Op::Uninterpreted(h), &[n]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[hn, c]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "an Int-sorted argument has no blastable word — must fence"
        );
    }

    #[test]
    fn uf_args_supported_leaves_nullary_applications_alone() {
        // A nullary uninterpreted BV symbol has no arguments to check and must
        // never be fenced — it is the ordinary BV variable case.
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, c]).unwrap();
        assert!(uf_args_supported(&ctx, &[atom], false));
    }

    /// An FP-sorted argument to a BV-result uninterpreted application
    /// qualifies ONLY when `allow_fp_args` — i.e. only on the FP/mixed path,
    /// where a `Lowerer` exists with a `core_eq`-based `word_eq`. This is the
    /// entire reason the parameter exists; without this pair, inverting the
    /// guard (`!allow_fp_args && ...`) or dropping it (admitting FP args
    /// unconditionally, which would crash the ABV path's bare `Blaster`)
    /// would both pass silently.
    #[test]
    fn uf_args_supported_admits_fp_arguments_only_when_allowed() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let s8 = ctx.bv_sort(8);
        let g = ctx.declare_fun("g", &[f32], s8);
        let nf = ctx.declare_fun("n", &[], f32);
        let n = ctx.mk_app(Op::Uninterpreted(nf), &[]).unwrap();
        let gn = ctx.mk_app(Op::Uninterpreted(g), &[n]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[gn, c]).unwrap();
        assert!(
            uf_args_supported(&ctx, &[atom], true),
            "an FP-sorted argument qualifies when allow_fp_args is true"
        );
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "an FP-sorted argument must NOT qualify when allow_fp_args is false \
             (no Lowerer sink exists to compare FP words, e.g. on the ABV path)"
        );
    }

    /// A RoundingMode-sorted argument has no blastable word in EITHER sink —
    /// neither a `Blaster` nor a `Lowerer` can turn it into a word — so it
    /// must fence even when `allow_fp_args` is true.
    #[test]
    fn uf_args_supported_rejects_a_roundingmode_argument_even_when_fp_allowed() {
        let mut ctx = Context::new();
        let rm_s = ctx.rm_sort();
        let s8 = ctx.bv_sort(8);
        let k = ctx.declare_fun("k", &[rm_s], s8);
        let r = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let kr = ctx.mk_app(Op::Uninterpreted(k), &[r]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[kr, c]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[atom], true),
            "a RoundingMode-sorted argument has no blastable word in any sink — must fence"
        );
    }

    #[test]
    fn uf_congruence_cost_is_quadratic_in_application_count() {
        // Three applications of one 1-ary 8-bit symbol: pairs(3) = 3, each
        // costing 8 argument bits + 8 result bits = 16. Expect 3 * 16 = 48.
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let mut atoms = Vec::new();
        let mut apps = Vec::new();
        for name in ["x", "y", "z"] {
            let vf = ctx.declare_fun(name, &[], s8);
            let v = ctx.mk_app(Op::Uninterpreted(vf), &[]).unwrap();
            apps.push(ctx.mk_app(Op::Uninterpreted(f), &[v]).unwrap());
        }
        atoms.push(
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[apps[0], apps[1]])
                .unwrap(),
        );
        atoms.push(
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[apps[1], apps[2]])
                .unwrap(),
        );
        assert_eq!(uf_congruence_cost(&ctx, &atoms), 48);
    }

    #[test]
    fn uf_congruence_cost_ignores_nullary_applications() {
        // Nullary symbols emit no congruence, so they must contribute zero.
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let yf = ctx.declare_fun("y", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        assert_eq!(uf_congruence_cost(&ctx, &[atom]), 0);
    }

    /// Pins the FP-argument width branch: an FP argument costs
    /// `FP_ARG_COST_MULTIPLIER * (eb + sb)`, not the raw `eb + sb`. Three
    /// applications of one 1-ary `Float32 (eb=8, sb=24) -> BV8` symbol:
    /// `pairs(3) = 3`, each pair costing `3 * (8 + 24) = 96` argument
    /// "bits" + `8` result bits = `104`. Expect `3 * 104 = 312`. A test that
    /// used the raw (unmultiplied) width would instead expect `3 * 40 = 120`
    /// — this must NOT pass.
    #[test]
    fn uf_congruence_cost_applies_the_fp_argument_multiplier() {
        let mut ctx = Context::new();
        let f32s = ctx.fp_sort(8, 24);
        let s8 = ctx.bv_sort(8);
        let g = ctx.declare_fun("g", &[f32s], s8);
        let mut atoms = Vec::new();
        let mut apps = Vec::new();
        for name in ["x", "y", "z"] {
            let vf = ctx.declare_fun(name, &[], f32s);
            let v = ctx.mk_app(Op::Uninterpreted(vf), &[]).unwrap();
            apps.push(ctx.mk_app(Op::Uninterpreted(g), &[v]).unwrap());
        }
        atoms.push(
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[apps[0], apps[1]])
                .unwrap(),
        );
        atoms.push(
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[apps[1], apps[2]])
                .unwrap(),
        );
        assert_eq!(uf_congruence_cost(&ctx, &atoms), 312);
    }

    /// A keying bug that merged two DISTINCT symbols under one bucket would
    /// pass a single-symbol fixture but not this: `f` (2 applications,
    /// `pairs(2) = 1`) and `h` (3 applications, `pairs(3) = 3`), both 1-ary
    /// `BV8 -> BV8`. Correct per-symbol total is `1*16 + 3*16 = 64`; a
    /// symbol-blind merge would instead see 5 applications of one bucket,
    /// `pairs(5) = 10`, cost `10*16 = 160`.
    #[test]
    fn uf_congruence_cost_does_not_merge_distinct_symbols() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let h = ctx.declare_fun("h", &[s8], s8);
        let a = bv_var(&mut ctx, "a", 8);
        let b = bv_var(&mut ctx, "b", 8);
        let c = bv_var(&mut ctx, "c", 8);
        let d = bv_var(&mut ctx, "d", 8);
        let e = bv_var(&mut ctx, "e", 8);
        let fa = ctx.mk_app(Op::Uninterpreted(f), &[a]).unwrap();
        let fb = ctx.mk_app(Op::Uninterpreted(f), &[b]).unwrap();
        let hc = ctx.mk_app(Op::Uninterpreted(h), &[c]).unwrap();
        let hd = ctx.mk_app(Op::Uninterpreted(h), &[d]).unwrap();
        let he = ctx.mk_app(Op::Uninterpreted(h), &[e]).unwrap();
        let atoms = vec![
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fa, fb]).unwrap(),
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[hc, hd]).unwrap(),
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[hd, he]).unwrap(),
        ];
        assert_eq!(uf_congruence_cost(&ctx, &atoms), 64);
    }

    /// The counting key must MIRROR the blaster's pairing predicate: one
    /// `SymbolId` can carry two different functions, because `declare_fun`
    /// interns by name and overwrites the signature. Here `f` is applied once
    /// at `BV8 -> BV8` and twice at `BV16 -> BV16`; the blaster pairs only
    /// within a shape, so the true cost is `pairs(1)*16 + pairs(2)*32 = 0 + 32
    /// = 32`.
    ///
    /// Keying by `SymbolId` alone gave `pairs(3) = 3` against whichever
    /// `arg_bits`/`res_bits` the FIRST application happened to install
    /// (`or_insert`): `3 * 16 = 48` for this ordering. That is over-counting
    /// here, but reversing the declaration order installs the WIDE widths for
    /// the narrow group and the same bug under-counts — and under-counting is
    /// the unsafe direction for a budget fence.
    #[test]
    fn uf_congruence_cost_does_not_merge_two_shapes_of_one_symbol() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let s16 = ctx.bv_sort(16);
        let f8 = ctx.declare_fun("f", &[s8], s8);
        let a = bv_var(&mut ctx, "a", 8);
        let fa = ctx.mk_app(Op::Uninterpreted(f8), &[a]).unwrap();
        // Redeclaring `f` returns the SAME SymbolId — interned by name.
        let f16 = ctx.declare_fun("f", &[s16], s16);
        assert_eq!(f8, f16, "declare_fun interns by name");
        let p = bv_var(&mut ctx, "p", 16);
        let q = bv_var(&mut ctx, "q", 16);
        let fp = ctx.mk_app(Op::Uninterpreted(f16), &[p]).unwrap();
        let fq = ctx.mk_app(Op::Uninterpreted(f16), &[q]).unwrap();
        let z8 = bv_var(&mut ctx, "z", 8);
        let atoms = vec![
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fa, z8]).unwrap(),
            ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fp, fq]).unwrap(),
        ];
        assert_eq!(uf_congruence_cost(&ctx, &atoms), 32);
    }

    /// The walk must not stop at the first uninterpreted application whose
    /// OWN arguments check out — it must continue past a passing node to
    /// catch an unwordable argument further down. `f : BV8 -> BV8` applied to
    /// `g(n)` (`g : Int -> BV8`) passes `f`'s own check (its argument `g(n)`
    /// is BV-sorted) but must still be rejected because `g`'s argument `n` is
    /// Int-sorted. A "return as soon as this node's own args check out"
    /// regression would pass this atom.
    ///
    /// The shared `gn` operand is incidental, NOT extra coverage: the walk's
    /// `kids.iter().all(..)` short-circuits on `fgn`'s `false` and never
    /// reaches the sibling `gn`. The memo needs no case of its own — a `false`
    /// propagates out of every enclosing `.all()` immediately, so a `true`
    /// later returned by an already-`seen` node can never overwrite it.
    #[test]
    fn uf_args_supported_rejects_an_unwordable_argument_below_a_passing_application() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let int_s = ctx.int_sort();
        let f = ctx.declare_fun("f", &[s8], s8);
        let g = ctx.declare_fun("g", &[int_s], s8);
        let nf = ctx.declare_fun("n", &[], int_s);
        let n = ctx.mk_app(Op::Uninterpreted(nf), &[]).unwrap();
        let gn = ctx.mk_app(Op::Uninterpreted(g), &[n]).unwrap();
        let fgn = ctx.mk_app(Op::Uninterpreted(f), &[gn]).unwrap();
        // `gn` shared on both sides of the Eq exercises the `seen` memo.
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fgn, gn]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "f's own argument (g(n)) is BV-sorted and passes, but the walk must \
             continue into g(n) and catch g's Int-sorted argument n underneath"
        );
    }

    // ── Slice 45: Bool-result uninterpreted applications ─────────────────────

    /// The collection widening AND its nullary exclusion, pinned in ONE
    /// fixture so neither half can pass vacuously: an empty result would fail
    /// the first assertion, and a "collect every Bool-sorted uninterpreted
    /// app" regression would fail the second.
    ///
    /// The exclusion is the soundness half. `blast_bv_atom` is uncached by
    /// contract and `blast_uf_app`'s nullary branch mints a fresh
    /// unconstrained literal registering nothing, so on a driver that
    /// re-blasts a collected atom — `abv_stage::RealBridge::new` +
    /// `ensure_atom_lit`, which have no by-rewritten memo — a collected
    /// nullary Bool application would get two INDEPENDENT literals for one
    /// Bool constant: a wrong `sat`. The blaster's `debug_assert!` cannot
    /// catch that in the shipping profile; THIS is the guard.
    #[test]
    fn collect_bv_atoms_takes_non_nullary_bool_applications_and_leaves_nullary_ones() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let bool_s = ctx.bool_sort();
        let p = ctx.declare_fun("p", &[s8], bool_s);
        let cf = ctx.declare_fun("c", &[], bool_s);
        let x = bv_var(&mut ctx, "x", 8);
        let px = ctx.mk_app(Op::Uninterpreted(p), &[x]).unwrap();
        let c = ctx.mk_app(Op::Uninterpreted(cf), &[]).unwrap();
        let assertions = vec![ctx.mk_app(Op::Builtin(BuiltinOp::And), &[px, c]).unwrap()];
        let atoms = collect_bv_atoms(&ctx, &assertions);
        assert!(
            atoms.contains(&px),
            "a non-nullary Bool-result uninterpreted application must be collected"
        );
        assert!(
            !atoms.contains(&c),
            "a NULLARY Bool application must NOT be collected — the exclusion is \
             the only guard against two independent literals for one Bool constant \
             on the unmemoized array driver"
        );
        // And the collected app must satisfy the foreign-theory fence, which is
        // the whole point of collecting it: `c` stays exempt via the fence's own
        // nullary carve-out, so nothing here fences.
        assert!(!has_non_bv_theory_atom(&ctx, &assertions, &atoms));
    }

    /// A Bool-RESULT uninterpreted application whose argument has no blastable
    /// word must fence exactly like the BitVec-result case. Before the Fence-1
    /// widening the result-sort guard was `ctx.bv_width(*sort).is_some()`, so
    /// this application was skipped entirely and `uf_args_supported` returned
    /// `true` — which, now that collection hands the app to the blaster, would
    /// reach `Blaster::word` on an Int-sorted term.
    #[test]
    fn uf_args_supported_rejects_an_int_argument_to_a_bool_result_application() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let bool_s = ctx.bool_sort();
        let p = ctx.declare_fun("p", &[int_s], bool_s);
        let nf = ctx.declare_fun("n", &[], int_s);
        let n = ctx.mk_app(Op::Uninterpreted(nf), &[]).unwrap();
        let pn = ctx.mk_app(Op::Uninterpreted(p), &[n]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[pn], false),
            "an Int-sorted argument to a Bool-result application has no blastable \
             word — must fence"
        );
    }

    /// A Bool ARGUMENT is out of scope in EITHER sink (a Bool child can be an
    /// arbitrary formula and the blaster has no Tseitin encoder), so it fences
    /// even with `allow_fp_args`.
    #[test]
    fn uf_args_supported_rejects_a_bool_argument_to_a_bool_result_application() {
        let mut ctx = Context::new();
        let bool_s = ctx.bool_sort();
        let p = ctx.declare_fun("p", &[bool_s], bool_s);
        let cf = ctx.declare_fun("c", &[], bool_s);
        let c = ctx.mk_app(Op::Uninterpreted(cf), &[]).unwrap();
        let pc = ctx.mk_app(Op::Uninterpreted(p), &[c]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[pc], true),
            "a Bool-sorted argument has no blastable word in any sink — must fence"
        );
    }

    /// Fence 2 must COUNT Bool-result applications, at `wₛ = 1`. Three
    /// applications of one 1-ary `BV8 -> Bool` symbol: `pairs(3) = 3`, each
    /// costing 8 argument bits + 1 result bit = 9. Expect `3 * 9 = 27`.
    ///
    /// Before the widening `ctx.bv_width(Bool)` was `None` and the whole group
    /// was skipped — 0. Under-counting is the UNSAFE direction for a budget
    /// fence (this module's `uf_congruence_cost` doc says so), and it became
    /// reachable the moment collection started handing these to the blaster.
    #[test]
    fn uf_congruence_cost_counts_a_bool_result_at_one_bit() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let bool_s = ctx.bool_sort();
        let p = ctx.declare_fun("p", &[s8], bool_s);
        let mut atoms = Vec::new();
        for name in ["x", "y", "z"] {
            let v = bv_var(&mut ctx, name, 8);
            atoms.push(ctx.mk_app(Op::Uninterpreted(p), &[v]).unwrap());
        }
        assert_eq!(uf_congruence_cost(&ctx, &atoms), 27);
    }

    /// `UfShapeKey`'s result-`SortId` component must keep a `Bool` result and a
    /// `(_ BitVec 1)` result of ONE redeclared symbol in separate groups —
    /// the counting-side mirror of the `shape_compatible` result-sort check
    /// slice 45 Task 2 had to add, where `result.len()` alone could not tell
    /// them apart at width 1.
    ///
    /// Two `BV8 -> Bool` applications (`pairs(2) = 1`, cost `8 + 1 = 9`) and
    /// two `BV8 -> (_ BitVec 1)` applications (`pairs(2) = 1`, cost `8 + 1 =
    /// 9`) total 18. A merge would see `pairs(4) = 6` and report 54.
    #[test]
    fn uf_congruence_cost_separates_a_bool_result_from_a_one_bit_bv_result() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let s1 = ctx.bv_sort(1);
        let bool_s = ctx.bool_sort();
        let a = bv_var(&mut ctx, "a", 8);
        let b = bv_var(&mut ctx, "b", 8);
        let f_bool = ctx.declare_fun("f", &[s8], bool_s);
        let fa = ctx.mk_app(Op::Uninterpreted(f_bool), &[a]).unwrap();
        let fb = ctx.mk_app(Op::Uninterpreted(f_bool), &[b]).unwrap();
        // Redeclaring `f` returns the SAME SymbolId — interned by name.
        let f_bv1 = ctx.declare_fun("f", &[s8], s1);
        assert_eq!(f_bool, f_bv1, "declare_fun interns by name");
        let ga = ctx.mk_app(Op::Uninterpreted(f_bv1), &[a]).unwrap();
        let gb = ctx.mk_app(Op::Uninterpreted(f_bv1), &[b]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ga, gb]).unwrap();
        assert_eq!(uf_congruence_cost(&ctx, &[fa, fb, eq]), 18);
    }

    // ── Slice 45 Task 6: Fence 1's blastability half ─────────────────────────

    fn arr(ctx: &mut Context, index: SortId, elem: SortId) -> TermId {
        let s = ctx.array_sort(index, elem);
        let f = ctx.declare_fun("arr", &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    /// The audit's finding (slice 45 Task 6). `(select a i)` over
    /// `(Array Int (_ BitVec 8))` is BitVec-8-SORTED, so the sort check alone
    /// admits it — and the blaster then reaches
    /// `unreachable!("non-BV builtin reached blast_word")`. Measured: before
    /// this check, `(= (f (select a i)) #x2a)` PANICKED on both the release and
    /// the debug binary.
    #[test]
    fn uf_args_supported_rejects_a_foreign_array_read_argument() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let int = ctx.int_sort();
        let a = arr(&mut ctx, int, s8);
        let idxf = ctx.declare_fun("i", &[], int);
        let i = ctx.mk_app(Op::Uninterpreted(idxf), &[]).unwrap();
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        assert_eq!(ctx.sort_of(sel), s8, "the read IS BitVec-sorted");
        let f = ctx.declare_fun("f", &[s8], s8);
        let fs = ctx.mk_app(Op::Uninterpreted(f), &[sel]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fs, c]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "a BV-sorted read over a NON-BV array has no blaster arm"
        );
    }

    /// Same shape with a Bool result — slice 45's new arm. Before Task 6 this
    /// query panicked where PRE-slice-45 it returned a sound `unknown`
    /// (Task 3's widening of `collect_bv_atoms` made the application a
    /// collected atom, so `has_non_bv_theory_atom` stopped descending into it
    /// and no longer saw the foreign `select`). This is the check that
    /// restores that `unknown`.
    #[test]
    fn uf_args_supported_rejects_a_foreign_array_read_under_a_bool_result() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let int = ctx.int_sort();
        let bool_s = ctx.bool_sort();
        let a = arr(&mut ctx, int, s8);
        let idxf = ctx.declare_fun("i", &[], int);
        let i = ctx.mk_app(Op::Uninterpreted(idxf), &[]).unwrap();
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let p = ctx.declare_fun("p", &[s8], bool_s);
        let ps = ctx.mk_app(Op::Uninterpreted(p), &[sel]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[ps], false),
            "the Bool-result arm needs the same blastability check"
        );
    }

    /// The exemption is load-bearing, not laxity: a read over a BV-indexed,
    /// BV-valued array MUST still pass. `uses_arrays_over_bv` (`lib.rs:902`)
    /// routes such a query to the ABV path, where `abstract_arrays` replaces
    /// every `select` — including one buried in a UF argument — with a fresh
    /// BV symbol before `collect_bv_atoms` runs. Rejecting it would fence
    /// `(f (select a i))` to `unknown`, a decided → unknown regression against
    /// slice 44's shipped behaviour (measured `sat`, z3 and cvc5 agreeing).
    #[test]
    fn uf_args_supported_still_admits_a_bv_array_read_argument() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let s4 = ctx.bv_sort(4);
        let bool_s = ctx.bool_sort();
        let a = arr(&mut ctx, s4, s8);
        let i = bv_var(&mut ctx, "i", 4);
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let f = ctx.declare_fun("f", &[s8], s8);
        let fs = ctx.mk_app(Op::Uninterpreted(f), &[sel]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fs, c]).unwrap();
        let p = ctx.declare_fun("p", &[s8], bool_s);
        let ps = ctx.mk_app(Op::Uninterpreted(p), &[sel]).unwrap();
        assert!(
            uf_args_supported(&ctx, &[atom, ps], false),
            "a BV-array read is abstracted away before blasting — must pass"
        );
    }

    /// The check looks at the whole argument SUBTREE, not just its head: a
    /// foreign read buried under BV operators is still unblastable.
    #[test]
    fn uf_args_supported_rejects_a_foreign_array_read_nested_under_bv_ops() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let int = ctx.int_sort();
        let a = arr(&mut ctx, int, s8);
        let idxf = ctx.declare_fun("i", &[], int);
        let i = ctx.mk_app(Op::Uninterpreted(idxf), &[]).unwrap();
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let add = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvAdd), &[sel, one])
            .unwrap();
        let f = ctx.declare_fun("f", &[s8], s8);
        let fa = ctx.mk_app(Op::Uninterpreted(f), &[add]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fa, c]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "the walk must descend the whole argument subtree"
        );
    }

    /// Review round 1's Critical. `((_ fp.to_ubv 8) RNE x)` is BitVec-8-SORTED,
    /// so the sort check admits it, and it contains no `select`, so the array
    /// half of `arg_term_blastable` admits it too — yet only a
    /// `shinri_fp::Lowerer` has an arm for it (`Lowerer::word` intercepts
    /// `FpToUbv`/`FpToSbv` and routes to `blast_fp_to_bv`,
    /// `crates/shinri-fp/src/lower.rs:52-73`). A bare `shinri_bv::Blaster` —
    /// which is what the ABV path uses — sends it to `blast_bv_word`'s
    /// `unreachable!`.
    ///
    /// This must be gated on `allow_fp_args` in BOTH directions and this test
    /// is the discriminating case for the `allow_fp_args = true` call site:
    ///
    /// - drop the gate (admit unconditionally) → the `false` assertion fails,
    ///   and the ABV path panics again (measured: `(= (select a i)
    ///   (f ((_ fp.to_ubv 8) RNE x)))` panicked at `blast/mod.rs:624` on both
    ///   profiles at commit 4a3701e8);
    /// - invert it, or reject unconditionally → the `true` assertion fails, and
    ///   `(= (f ((_ fp.to_ubv 8) RNE x)) #x2a)` flips from `sat` to `unknown`,
    ///   a forbidden decided → unknown regression.
    ///
    /// Note this is a strictly stronger claim than
    /// `uf_args_supported_admits_fp_arguments_only_when_allowed`: there the
    /// argument's SORT is FP, so the sort check alone discriminates. Here the
    /// argument's sort is BitVec and only `arg_term_blastable` can catch it.
    #[test]
    fn uf_args_supported_admits_an_fp_to_bv_argument_only_when_allowed() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let rm = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let conv = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rm, x])
            .unwrap();
        assert_eq!(
            ctx.sort_of(conv),
            s8,
            "the conversion IS BitVec-sorted — the sort check cannot catch it"
        );
        let f = ctx.declare_fun("f", &[s8], s8);
        let fc = ctx.mk_app(Op::Uninterpreted(f), &[conv]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fc, c]).unwrap();
        assert!(
            uf_args_supported(&ctx, &[atom], true),
            "with an FP sink (the FP/mixed path) `Lowerer::word` has the arm — \
             rejecting here would be a decided (sat) -> unknown regression"
        );
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "without an FP sink (the ABV path, `lib.rs:910`) a bare Blaster \
             reaches blast_bv_word's unreachable! — must fence"
        );
    }

    /// The signed twin, so a fix that special-cases only `FpToUbv` is caught.
    #[test]
    fn uf_args_supported_gates_fp_to_sbv_the_same_way() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let rm = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let conv = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToSbv(8)), &[rm, x])
            .unwrap();
        let p = ctx.declare_fun("p", &[s8], ctx.bool_sort());
        let pc = ctx.mk_app(Op::Uninterpreted(p), &[conv]).unwrap();
        assert!(uf_args_supported(&ctx, &[pc], true));
        assert!(
            !uf_args_supported(&ctx, &[pc], false),
            "fp.to_sbv needs the same gate as fp.to_ubv"
        );
    }

    /// Buried under BV operators, so the check must descend rather than only
    /// inspect the argument's head — the FP-conversion twin of
    /// `uf_args_supported_rejects_a_foreign_array_read_nested_under_bv_ops`.
    #[test]
    fn uf_args_supported_rejects_a_nested_fp_to_bv_without_an_fp_sink() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let rm = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let conv = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rm, x])
            .unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let add = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvAdd), &[conv, one])
            .unwrap();
        let f = ctx.declare_fun("f", &[s8], s8);
        let fa = ctx.mk_app(Op::Uninterpreted(f), &[add]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fa, c]).unwrap();
        assert!(uf_args_supported(&ctx, &[atom], true));
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "the walk must descend the whole argument subtree"
        );
    }
}
