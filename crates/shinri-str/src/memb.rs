//! Slice 21: the membership pass — lazy guarded derivative unfolding of
//! `str.in_re` atoms into word equations, run at the end of every Full check.

use crate::regex::{self, Rex};
use crate::{collect, normalize, side_clean, wordeq, StrSolver};
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::{ENodeId, EqLeaf};
use shinri_theory::{TCheck, TheoryCtx};

const RULE_E: u8 = 0;
const RULE_S1: u8 = 1;
// RULE tag 2 (the old one-shot S2 gate) retired: S2's witness-length axiom is
// now emitted through its two arith companions, deduped via
// `emitted_len_axioms` (see the S2 block).
const RULE_S3: u8 = 3;
const RULE_S4: u8 = 4;

/// The two children of a `str.in_re` atom: (string side, regex side).
pub(crate) fn memb_sides(terms: &Context, atom: TermId) -> (TermId, TermId) {
    match terms.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrInRe),
            args,
            ..
        } => {
            let ch = terms.children(*args);
            (ch[0], ch[1])
        }
        _ => panic!("memb_sides: expected str.in_re atom"),
    }
}

/// `str.++` of `atoms` (1 atom → itself; 0 → the empty literal).
fn mk_concat(terms: &mut Context, atoms: &[TermId]) -> TermId {
    match atoms.len() {
        0 => terms.mk_string_const(""),
        1 => atoms[0],
        _ => terms
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), atoms)
            .expect("str.++ well-sorted"),
    }
}

/// Register a freshly-minted split atom exactly like the F-split path does:
/// collect its len/str terms and mark any string equality as minted so the
/// length seam skips it. Additionally recorded in `memb_minted_eqs`
/// (D-wordeq-skip): these equalities are DEFINITIONAL — the S-rules are their
/// resolution — so the word-equation loop defers F-split emission over them
/// (see the gate at the wordeq loop's Split arm in `lib.rs::check`).
fn register_atom(s: &mut StrSolver, terms: &mut Context, atom: TermId) {
    let mut seen = FxHashSet::default();
    collect::collect(terms, atom, &mut s.len_terms, &mut s.str_terms, &mut seen);
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
        args,
        ..
    } = terms.term_node(atom)
    {
        let kids = terms.children(*args).to_vec();
        if !kids.is_empty() && terms.sort_of(kids[0]) == terms.string_sort() {
            s.minted_eqs.insert(atom);
            s.memb_minted_eqs.insert(atom);
        }
    }
}

/// Spend fuel and emit one guarded/unguarded split, registering every atom.
///
/// D-satfuel: fuel availability is guaranteed by the per-atom peek at the top
/// of `memb_check`'s loop (each loop iteration emits at most ONE split and
/// spends nothing before it), so the spend here cannot fail — the membership
/// pass never hard-`Unknown`s on fuel; exhaustion SATURATES at the loop top,
/// before any dedup key or witness is minted. Debug-assert the invariant.
fn emit_split(
    s: &mut StrSolver,
    terms: &mut Context,
    atoms: Vec<TermId>,
    guard: Option<shinri_core::Lit>,
) -> TCheck {
    for &a in &atoms {
        register_atom(s, terms, a);
    }
    let had_fuel = s.fuel.spend();
    debug_assert!(
        had_fuel,
        "emit_split without fuel — memb_check's per-atom peek must run first"
    );
    TCheck::Split { atoms, guard }
}

/// Length link for a PASS-MINTED string equality `l = r`: the pure tautology
/// `l = r → len(l) = len(r)`, emitted through its `(>=)`/`(<=)` arith
/// companions (a bare theory-emitted Int equality routes to EUF, not Arith —
/// the `length::next_axiom` seam note), one per round, in the pass's own
/// unguarded `[distinct(l,r), companion]` clause shape (Rule S2's posture;
/// the E1 note in `lib.rs::check` blesses "`¬eq ∨ len(l)=len(r)` over the
/// equality's OWN sides" as "a pure tautology").
///
/// CONTRACT MATCH (Task 4 adjudication — why the pass emits these itself
/// instead of unmarking its equalities from `minted_eqs`): the generic
/// per-equality link in `lib.rs::check` skips `minted_eqs` because F-split /
/// char-peel disjuncts are "re-minted with a FRESH skolem z every round" (the
/// seam-flood + skolem-interaction rationale documented there); memb-pass
/// equalities are minted ONCE per `(x, cur_t)` (deduped via `emitted_memb`,
/// witnesses memoized in `memb_wits`), so the finite-emission premise holds
/// and the pass carries its own length axioms — the same posture as the
/// F-split, whose `fsplit_atoms` carries its `len_eq` inside its own split.
/// Unmarking instead would put the pass's own decided disjuncts into
/// `input_cond_roots`, and the `side_clean` gate below would then stall
/// unfolding at the first decision (the stall documented at that gate), while
/// also un-gating the GLOBAL same-word conflicts over pass-skolem merges (the
/// `all_cond_roots` wrong-UNSAT channel).
///
/// Dedup rides `emitted_len_axioms`, exactly like the `lib.rs` link block.
/// Returns `Some(split)` for the first unemitted companion; `None` when both
/// are already out.
fn len_link_split(s: &mut StrSolver, terms: &mut Context, eq_atom: TermId) -> Option<TCheck> {
    let (l, r) = wordeq::sides(terms, eq_atom);
    let ll = wordeq::len_of(terms, l);
    let lr = wordeq::len_of(terms, r);
    let len_eq = terms.mk_eq(ll, lr).expect("(= len(l) len(r)) well-sorted");
    let (ge, le) =
        crate::length::arith_eq_companions(terms, len_eq).expect("len equality has Int sides");
    let dist = terms
        .mk_app(Op::Builtin(BuiltinOp::Distinct), &[l, r])
        .expect("distinct well-sorted");
    for comp in [ge, le] {
        if s.emitted_len_axioms.contains(&comp) {
            continue;
        }
        s.emitted_len_axioms.insert(comp);
        return Some(emit_split(s, terms, vec![dist, comp], None));
    }
    None
}

/// The slice-21 membership pass. `Some(tcheck)` = a verdict or an emission
/// this round; `None` = nothing to do (all memberships discharged, deduped,
/// or skipped as unclean — the caller falls through to Sat, backstopped by
/// the post-solve self-check).
pub(crate) fn memb_check(
    s: &mut StrSolver,
    cx: &mut TheoryCtx,
    known: &[TermId],
    input_cond_roots: &FxHashSet<ENodeId>,
) -> Option<TCheck> {
    let membs: Vec<(TermId, shinri_core::Lit, bool)> = s.memb_true.clone();
    for (atom, lit, pos) in membs {
        // ── D-satfuel (owner-authorized): saturate on fuel exhaustion ────
        // With the shared budget exhausted no lemma can be emitted this
        // round: SATURATE — return None so `check()` falls through to
        // `TCheck::Sat` and the model build + membership repair + post-solve
        // self-check decide the verdict — rather than a hard
        // `TCheck::Unknown`. Spec basis (Saturation paragraph): the pass
        // "must not report Sat on its own authority; the model build + the
        // extended self-check are the only path to Sat" — every Sat is
        // gated, so exhaustion can only cost decisiveness, never soundness.
        // Peeked BEFORE any dedup key / witness is minted, so a
        // never-emitted lemma is never recorded as emitted (which would
        // silently drop it forever). Each loop iteration emits at most ONE
        // split and spends nothing before it, so `remaining ≥ 1` here
        // guarantees the iteration's single `emit_split` succeeds. The
        // `Unknown` fences below (const-regex extraction, non-convergent
        // NF, node caps, CLASS_SPLIT_CAP) are per-atom SOUNDNESS fences,
        // not fuel, and stay. The wordeq/length passes' own fuel behavior
        // is unchanged.
        if s.fuel.remaining == 0 {
            return None;
        }
        let (t, re_t) = memb_sides(cx.terms, atom);
        // Constant by the solver fence (input) or by construction (minted);
        // a failure here is a seam break — fence to Unknown, never guess.
        let Some(mut rex) = regex::extract_const_regex(cx.terms, re_t) else {
            return Some(TCheck::Unknown);
        };
        if !pos {
            rex = regex::comp(rex); // t ∉ R ≡ t ∈ comp(R)
        }

        // ── Rule G: consume the ground NF prefix ─────────────────────────
        // Fully-cited NF (the diseq Case-2 pattern): expansion antecedents
        // are collected so a ground Conflict can cite them and stay UNGATED.
        let mut expand_ante: Vec<EqLeaf> = Vec::new();
        let Some(nf) =
            normalize::deep_normal_form_cited(cx.terms, cx.eq, known, t, &mut expand_ante)
        else {
            return Some(TCheck::Unknown); // non-convergent merge — sound bail
        };
        let mut cur = rex;
        let mut i = 0usize;
        let mut fenced = false;
        while i < nf.len() {
            let Some(w) = cx.terms.string_const_value(nf[i]).map(str::to_owned) else {
                break;
            };
            for c in w.chars() {
                cur = regex::deriv(c as u32, &cur);
                if regex::node_count(&cur) > regex::FUEL_NODE_CAP {
                    fenced = true;
                    break;
                }
            }
            if fenced {
                break;
            }
            i += 1;
        }
        if fenced {
            return Some(TCheck::Unknown);
        }
        if i == nf.len() {
            // Fully ground: nullability decides the atom.
            if regex::nullable(&cur) {
                continue; // discharged this round
            }
            let mut just = vec![EqLeaf::Asserted(lit)];
            just.extend(expand_ante.iter().copied());
            return Some(TCheck::Conflict(just));
        }

        // ── Bare-range LEAF: leave for Rule G + model repair ─────────────
        // Spec (design §Rule S): "the `x = h·z` branch grounds out once
        // search or the model pins `h` (a `M(h, C)` atom with `len(h) = 1`
        // is decided by Rule G the moment `h`'s class acquires a literal,
        // and is realised by model repair otherwise)" — a bare single-class
        // membership is the GROUND-OUT point of the unfolding, not another
        // S target. Recursing S on it (a bare `Rex::Range` head-forces to
        // `(C, ε)`) mints a fresh concat into the witness's own class,
        // which destroys the leaf's repair eligibility (`memb_seeds`
        // repairs only a leaf whose class holds no constant and no concat)
        // — the Task-4 wrong-witness channel. Skip: the atom stays in
        // `memb_true`; Rule G decides it whenever the class grounds;
        // `memb_seeds` realises it otherwise; the self-check backstops.
        //
        // Slice 25 task 5b, Part 2: before skipping, emit the GUARDED
        // tautology `lit → len(residual) = 1` (through its arith companions,
        // deduped via `emitted_len_axioms` — same posture as the S2 witness
        // axiom) so an independently-asserted `len(residual)` conflicts with
        // the single-char class instead of silently falling to model repair
        // (which can never produce Unsat). Mints NO concat — `residual`
        // itself, not a fresh witness, carries the length fact, so the
        // leaf's repair eligibility is untouched. Soundness: a single-char
        // class matches exactly length-1 words, so the implication is a
        // tautology — guarded, it can only ADD a fact arith lacked, never
        // flip a verdict.
        if matches!(cur, Rex::Range(..)) {
            // Guarded like the variable-head arm below: `residual` is an NF
            // read (`nf[i..]`), and the clause this emits is persisted
            // GLOBALLY (`emitted_len_axioms`, not scoped to this branch) —
            // so if the `t = prefix·residual` decomposition came from a
            // CONDITIONAL (dl>0) merge, the global clause would only be
            // branch-locally valid. `side_clean` is the same branch-
            // independence gate the sibling arm applies at the `!side_clean`
            // check just below (memb.rs:301) — mirrored here, same
            // arguments, same semantics. When it fails, fall through to the
            // pre-existing `continue` (repair-eligibility untouched).
            //
            // Known decisiveness limitation (documented, not fixed): the
            // dedup key `emitted_len_axioms` is keyed on the arith companion
            // alone, not on this guard — so if two membership literals with
            // different `lit`s share the same `residual`, only the FIRST
            // one's guard is emitted. Still sound (each guarded clause is a
            // tautology on its own), just less decisive than emitting one
            // per literal.
            if !side_clean(cx.eq, cx.terms, t, input_cond_roots) {
                continue;
            }
            let residual = mk_concat(cx.terms, &nf[i..]);
            let lr = wordeq::len_of(cx.terms, residual);
            let one = cx.terms.mk_numeral(
                shinri_core::Rational::from_int(1i128.into()),
                cx.terms.int_sort(),
            );
            let len1 = cx.terms.mk_eq(lr, one).expect("eq well-sorted");
            let (ge, le) = crate::length::arith_eq_companions(cx.terms, len1)
                .expect("len(residual)=1 has Int sides");
            let guard = Some(lit.negate());
            for comp in [ge, le] {
                if s.emitted_len_axioms.contains(&comp) {
                    continue;
                }
                s.emitted_len_axioms.insert(comp);
                return Some(emit_split(s, cx.terms, vec![comp], guard));
            }
            continue;
        }

        // ── Slice 26: general const-Rex LEAF carve-out ───────────────────
        // A LONE repair-eligible leaf residual (single NF atom, nullary
        // uninterpreted — the same shape `memb_seeds` requires; a class
        // holding a constant or concat never reaches here, deep NF resolves
        // it and Rule G consumes it) with any const `cur` is the GROUND-OUT
        // point of the unfolding, exactly like the bare-`Range` arm above:
        // Rule S/E on it mints fresh skolems whose `str.len` companions
        // flood the string↔arith seam every round until the shared fuel
        // dies in the length-axiom loop (`lib.rs::check`) — a hard Unknown
        // BEFORE model repair can ever search a witness (the slice-26 root
        // cause). Skip unfolding: emit the guarded tautology
        // `lit → min_len(cur) ≤ len(residual) [≤ max_len(cur) if finite]`
        // (bounds are sound by construction — `regex::min_len`/`max_len`
        // doc), deduped via `emitted_len_axioms`, one clause per round, same
        // posture as the sibling arm; then leave the atom in `memb_true`
        // for Rule G / `memb_seeds` / the post-solve self-check. `Empty`
        // and `Eps` are excluded so the existing decisive paths (Rule-E
        // conflict on ∅, ε-forcing) keep firing; `Range` took the sibling
        // arm. Mints NO concat — repair eligibility untouched.
        let lone_leaf = nf.len() - i == 1
            && matches!(
                cx.terms.term_node(nf[i]),
                shinri_core::TermNode::App { op: Op::Uninterpreted(_), args, .. }
                    if cx.terms.children(*args).is_empty()
            );
        if lone_leaf && !matches!(cur, Rex::Empty | Rex::Eps) {
            if !side_clean(cx.eq, cx.terms, t, input_cond_roots) {
                continue;
            }
            let residual = nf[i];
            let lr = wordeq::len_of(cx.terms, residual);
            let guard = Some(lit.negate());
            let mut bounds: Vec<TermId> = Vec::new();
            let lo = regex::min_len(&cur);
            if lo > 0 {
                let k = cx.terms.mk_numeral(
                    shinri_core::Rational::from_int(i128::from(lo).into()),
                    cx.terms.int_sort(),
                );
                bounds.push(
                    cx.terms
                        .mk_app(Op::Builtin(BuiltinOp::Ge), &[lr, k])
                        .expect("(>= len k) well-sorted"),
                );
            }
            if let Some(hi) = regex::max_len(&cur) {
                let k = cx.terms.mk_numeral(
                    shinri_core::Rational::from_int(i128::from(hi).into()),
                    cx.terms.int_sort(),
                );
                bounds.push(
                    cx.terms
                        .mk_app(Op::Builtin(BuiltinOp::Le), &[lr, k])
                        .expect("(<= len k) well-sorted"),
                );
            }
            for b in bounds {
                if s.emitted_len_axioms.contains(&b) {
                    continue;
                }
                s.emitted_len_axioms.insert(b);
                return Some(emit_split(s, cx.terms, vec![b], guard));
            }
            continue;
        }

        // Residual: nf[i..] with a variable head. Guarded lemmas read the
        // NF, so they fire only when it is branch-independent w.r.t. EXTERNAL
        // disjunctions — `side_clean(input_cond_roots)`, the SAME gate the
        // word-equation loop uses for F-SPLIT emission (spec: "the same
        // gating F-splits use today"). The engine's OWN minted disjuncts are
        // deliberately NOT in this set, so unfolding keeps stepping over its
        // previously-emitted splits (else a dl0 membership stalls at
        // Unknown). Sound for the same reason F-splits are: these lemmas add
        // only GUARDED branches (guard ¬lit; fresh lone witnesses), never a
        // global fact — verdicts stay with the fully-cited Rule-G/E
        // conflicts, and any admitted SAT is re-validated by the post-solve
        // model self-check. Skipped ⟹ revisited when clean; never a verdict.
        if !side_clean(cx.eq, cx.terms, t, input_cond_roots) {
            continue;
        }
        let residual_atoms: Vec<TermId> = nf[i..].to_vec();
        let residual = mk_concat(cx.terms, &residual_atoms);
        let x = residual_atoms[0];
        let cur_t = regex::rex_to_term(cx.terms, &cur);
        let guard = Some(lit.negate());

        // ── Rule S: head-forced `C · R''` — peel one char off `x` ────────
        if let Some(((lo, hi), tail_rex)) = regex::head_forced(&cur) {
            // S1: lit → x = "" ∨ x = h·z (fresh h, z; the F-split argument).
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S1)) {
                s.emitted_memb.insert((x, cur_t, RULE_S1));
                let h = wordeq::fresh_str(cx.terms, &mut s.fresh_ctr);
                let z = wordeq::fresh_str(cx.terms, &mut s.fresh_ctr);
                s.memb_wits.insert((x, cur_t), (h, z));
                let hz = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[h, z])
                    .expect("str.++ well-sorted");
                let e = cx.terms.mk_string_const("");
                let x_eps = cx.terms.mk_eq(x, e).expect("eq well-sorted");
                let x_hz = cx.terms.mk_eq(x, hz).expect("eq well-sorted");
                return Some(emit_split(s, cx.terms, vec![x_eps, x_hz], guard));
            }
            let &(h, z) = s
                .memb_wits
                .get(&(x, cur_t))
                .expect("S1 emitted ⟹ witnesses recorded");
            let hz = cx
                .terms
                .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[h, z])
                .expect("str.++ well-sorted");
            let dist = cx
                .terms
                .mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, hz])
                .expect("distinct well-sorted");
            // Length link for the S1-minted equality `x = h·z` — without it
            // the equality never reaches the length seam (it is
            // `minted_eqs`-skipped there), so `len(z)` never links to
            // `len(x)` and an asserted `len(x) = k` cannot drive the
            // unfolding depth. See `len_link_split` for the contract note.
            // The sibling ε equality `x = ""` deliberately gets NO link: a
            // head-forced `cur` (`C·R''`) is never nullable, so Rule G
            // conflicts the ε branch on membership grounds alone the moment
            // `x ≈ ""` merges — a link there is dead fuel. (Rule E's ε
            // disjunct, whose regex IS nullable, gets its link below.)
            {
                let x_hz = cx.terms.mk_eq(x, hz).expect("eq well-sorted");
                if let Some(tc) = len_link_split(s, cx.terms, x_hz) {
                    return Some(tc);
                }
            }
            // S2 (unguarded fresh-witness canonicalization): x=h·z →
            // len(h)=1, emitted through its `(>=)`/`(<=)` arith companions —
            // a bare theory-emitted Int equality routes to EUF, not Arith
            // (the `length::next_axiom` seam note), so the witness length
            // must take the companion form to reach the ARITH model (which
            // both the model builder's class-length read and `memb_seeds`'
            // capped word search consult). Dedup rides `emitted_len_axioms`,
            // exactly like `len_link_split`.
            {
                let lh = wordeq::len_of(cx.terms, h);
                let one = cx.terms.mk_numeral(
                    shinri_core::Rational::from_int(1i128.into()),
                    cx.terms.int_sort(),
                );
                let len1 = cx.terms.mk_eq(lh, one).expect("eq well-sorted");
                let (ge, le) = crate::length::arith_eq_companions(cx.terms, len1)
                    .expect("len(h)=1 has Int sides");
                for comp in [ge, le] {
                    if s.emitted_len_axioms.contains(&comp) {
                        continue;
                    }
                    s.emitted_len_axioms.insert(comp);
                    return Some(emit_split(s, cx.terms, vec![dist, comp], None));
                }
            }
            // S3: lit ∧ x=h·z → h ∈ C.
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S3)) {
                s.emitted_memb.insert((x, cur_t, RULE_S3));
                let c_t = regex::rex_to_term(cx.terms, &Rex::Range(lo, hi));
                let m_h = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[h, c_t])
                    .expect("str.in_re well-sorted");
                return Some(emit_split(s, cx.terms, vec![dist, m_h], guard));
            }
            // S4: lit ∧ x=h·z → z·γ ∈ R''.
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S4)) {
                s.emitted_memb.insert((x, cur_t, RULE_S4));
                let mut tail_atoms = vec![z];
                tail_atoms.extend_from_slice(&residual_atoms[1..]);
                let tail_t = mk_concat(cx.terms, &tail_atoms);
                let tail_re = regex::rex_to_term(cx.terms, &tail_rex);
                let m_tail = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[tail_t, tail_re])
                    .expect("str.in_re well-sorted");
                return Some(emit_split(s, cx.terms, vec![dist, m_tail], guard));
            }
            continue; // fully unfolded at this level — wait for SAT/merges
        }

        // ── Rule E: class expansion (fundamental derivative equivalence)
        //    L(cur) = [ε if ν] ∪ ⋃_C C·L(∂_C cur) — single-atom disjuncts. ──
        if !s.emitted_memb.contains(&(residual, cur_t, RULE_E)) {
            s.emitted_memb.insert((residual, cur_t, RULE_E));
            let Some(classes) = regex::next_classes(&cur) else {
                return Some(TCheck::Unknown); // CLASS_SPLIT_CAP — fence
            };
            let mut disj: Vec<TermId> = Vec::new();
            if regex::nullable(&cur) {
                let e = cx.terms.mk_string_const("");
                disj.push(cx.terms.mk_eq(residual, e).expect("eq well-sorted"));
            }
            for (lo, hi) in classes {
                // ∂ at the class representative — exact across the class
                // (u32 space: surrogate classes included, never dropped).
                let d = regex::deriv(lo, &cur);
                if regex::node_count(&d) > regex::FUEL_NODE_CAP {
                    return Some(TCheck::Unknown);
                }
                if matches!(d, Rex::Empty) {
                    continue; // C·∅ = ∅ — a dead disjunct, dropping is exact
                }
                let shape = regex::concat(vec![Rex::Range(lo, hi), d]);
                let shape_t = regex::rex_to_term(cx.terms, &shape);
                disj.push(
                    cx.terms
                        .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[residual, shape_t])
                        .expect("str.in_re well-sorted"),
                );
            }
            if disj.is_empty() {
                // No ε, no live class: L(cur) = ∅ — the membership is
                // unsatisfiable. Fully-cited conflict (trigger + NF merges).
                let mut just = vec![EqLeaf::Asserted(lit)];
                just.extend(expand_ante.iter().copied());
                return Some(TCheck::Conflict(just));
            }
            return Some(emit_split(s, cx.terms, disj, guard));
        }
        // Rule E already expanded: emit the ε-disjunct equality's length
        // links (`residual = "" → len(residual) = 0` via companions plus the
        // `len("")` defining axiom) — same contract note as the S1 links
        // (see `len_link_split`). Without this the minted ε equality never
        // reaches the length seam and an asserted `len ≥ k` cannot close the
        // ε branch.
        if regex::nullable(&cur) {
            let e = cx.terms.mk_string_const("");
            let eps_eq = cx.terms.mk_eq(residual, e).expect("eq well-sorted");
            if let Some(tc) = len_link_split(s, cx.terms, eps_eq) {
                return Some(tc);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use crate::regex::{self, Rex};
    use crate::StrSolver;
    use shinri_core::{BuiltinOp, Context, Op, TermId};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    fn var(ctx: &mut Context, n: &str) -> TermId {
        let str_s = ctx.string_sort();
        let s = ctx.declare_fun(n, &[], str_s);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    fn memb_atom(ctx: &mut Context, t: TermId, r: &Rex) -> TermId {
        let re_t = regex::rex_to_term_test(ctx, r);
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[t, re_t])
            .unwrap()
    }

    // Sanctioned deviation from the brief's verbatim snippet: the `ctx`
    // param was unused (warning) — renamed `_ctx`.
    fn harness(_ctx: &mut Context) -> (StrSolver, EqualityEngine, AtomRegistry) {
        (
            StrSolver::default(),
            EqualityEngine::default(),
            AtomRegistry::default(),
        )
    }

    /// Drive check() to a fixpoint, collecting every emitted Split; panics on
    /// Unknown. Returns the terminal TCheck (Sat or Conflict).
    fn run_rounds(
        s: &mut StrSolver,
        cx: &mut TheoryCtx,
        max: usize,
    ) -> (Vec<(Vec<TermId>, bool)>, TCheck) {
        let mut splits = Vec::new();
        for _ in 0..max {
            match s.check(cx, Effort::Full) {
                TCheck::Split { atoms, guard } => splits.push((atoms, guard.is_some())),
                other => return (splits, other),
            }
        }
        panic!("no fixpoint within {max} rounds");
    }

    #[test]
    fn rule_g_ground_conflict_and_discharge() {
        // x = "ab" merged, x ∈ a*  ⇒ Conflict (ground eval false).
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let ab = ctx.mk_string_const("ab");
        let eq = ctx.mk_eq(x, ab).unwrap();
        let m = memb_atom(&mut ctx, x, &regex::star_lit_test("a"));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), eq);
        s.new_var(&mut cx, shinri_core::Var::new(1), m);
        s.test_force_eq_true(eq);
        // Unit tests drive the eq engine EXPLICITLY (the Combiner does this
        // in production) — same incantation as the wordeq.rs tests.
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(ab));
        let _ = cx
            .eq
            .merge(xn, cn, shinri_theory::types::EqJust::Definitional);
        s.test_force_memb_true(m, true);
        let (_, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(
            matches!(terminal, TCheck::Conflict(_)),
            "ground violation must conflict"
        );

        // Same shape, x ∈ (str.to_re "ab") ⇒ discharged, Sat fixpoint.
        let mut ctx2 = Context::new();
        let x2 = var(&mut ctx2, "x");
        let ab2 = ctx2.mk_string_const("ab");
        let eq2 = ctx2.mk_eq(x2, ab2).unwrap();
        let m2 = memb_atom(&mut ctx2, x2, &regex::lit_test("ab"));
        let (mut s2, mut eq_e2, atoms2) = harness(&mut ctx2);
        let mut cx2 = TheoryCtx {
            terms: &mut ctx2,
            eq: &mut eq_e2,
            atoms: &atoms2,
        };
        s2.new_var(&mut cx2, shinri_core::Var::new(0), eq2);
        s2.new_var(&mut cx2, shinri_core::Var::new(1), m2);
        s2.test_force_eq_true(eq2);
        let (xn2, cn2) = (cx2.eq.intern(x2), cx2.eq.intern(ab2));
        let _ = cx2
            .eq
            .merge(xn2, cn2, shinri_theory::types::EqJust::Definitional);
        s2.test_force_memb_true(m2, true);
        let (_, terminal2) = run_rounds(&mut s2, &mut cx2, 16);
        assert!(
            matches!(terminal2, TCheck::Sat),
            "satisfied ground membership discharges"
        );
    }

    #[test]
    fn negative_polarity_uses_complement() {
        // x = "ab" merged, ¬(x ∈ a*) ⇒ discharged (comp semantics); and
        // ¬(x ∈ (str.to_re "ab")) ⇒ Conflict.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let ab = ctx.mk_string_const("ab");
        let eq = ctx.mk_eq(x, ab).unwrap();
        let m_astar = memb_atom(&mut ctx, x, &regex::star_lit_test("a"));
        let m_ab = memb_atom(&mut ctx, x, &regex::lit_test("ab"));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), eq);
        s.test_force_eq_true(eq);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(ab));
        let _ = cx
            .eq
            .merge(xn, cn, shinri_theory::types::EqJust::Definitional);
        s.test_force_memb_true(m_astar, false); // "ab" ∉ a* — true, discharges
        let (_, t1) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(t1, TCheck::Sat));
        s.test_force_memb_true(m_ab, false); // "ab" ∉ {ab} — false, conflicts
        let (_, t2) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(t2, TCheck::Conflict(_)));
    }

    #[test]
    fn rule_e_expansion_shape() {
        // x ∈ [a-c]* (not head-forced, nullable): ONE guarded clause whose
        // atoms are the ε equality + one membership per class with a
        // non-empty derivative (here exactly one: [a-c]·[a-c]*).
        //
        // Slice 26 carrier truth-up: a LONE leaf x now takes the leaf
        // carve-out (no Rule-E expansion), so pin Rule E's shape on a
        // two-atom carrier x·y, which is not repair-eligible.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let y = var(&mut ctx, "y");
        let xy = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let r = regex::star_range_test('a', 'c');
        let m = memb_atom(&mut ctx, xy, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        // Rounds may interleave length axioms; find the ONE expansion split
        // (the guarded split containing a str.in_re disjunct). Terminal Sat
        // proves the expansion dedups (no re-emission).
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(
            matches!(terminal, TCheck::Sat),
            "expansion must dedup to a fixpoint"
        );
        let is_memb = |t: &TermId| {
            matches!(
                cx.terms.term_node(*t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        let expansions: Vec<_> = splits
            .iter()
            .filter(|(atoms, _)| atoms.iter().any(is_memb))
            .collect();
        assert_eq!(
            expansions.len(),
            1,
            "exactly one Rule-E expansion for [a-c]*"
        );
        let (disj, guarded) = expansions[0];
        assert!(*guarded, "expansion must be guarded by ¬lit");
        assert_eq!(disj.len(), 2, "ε disjunct + one live class disjunct");
        // One disjunct is x = "" and the other a str.in_re atom on x.
        let memb_disj = disj.iter().find(|t| is_memb(t)).unwrap();
        let (mt, _) = super::memb_sides(cx.terms, *memb_disj);
        assert_eq!(mt, xy);
        let eq_disj = disj.iter().find(|t| !is_memb(t)).unwrap();
        let (l, rr) = crate::wordeq::sides(cx.terms, *eq_disj);
        assert!(
            cx.terms.string_const_value(l) == Some("")
                || cx.terms.string_const_value(rr) == Some("")
        );
    }

    #[test]
    fn rule_s_head_split_clause_sequence() {
        // x·y ∈ [a-c]·"b" — head-forced with a non-ε residual: S1..S4 in
        // order, then fixpoint. (Shape changed for the Task-4 bare-range
        // leaf skip: the original `[a-c]` — the smart constructor collapses
        // `[a-c]·(str.to_re "")` to a bare `Rex::Range` — is now a repair
        // LEAF on which Rule S deliberately never fires; a concat with a
        // non-ε tail remains genuinely head-forced.)
        //
        // Slice 26 carrier truth-up: a LONE leaf x over this same regex now
        // takes the general leaf carve-out (see
        // `lone_leaf_finite_concat_emits_both_bounds`), so pin Rule S's
        // clause-sequence shape on a two-atom carrier x·y, which is not
        // repair-eligible. Rule S still peels `residual_atoms[0] = x`, so
        // every existing assertion below holds verbatim.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let y = var(&mut ctx, "y");
        let xy = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let r = regex::concat(vec![
            Rex::Range('a' as u32, 'c' as u32),
            regex::lit_test("b"),
        ]);
        let m = memb_atom(&mut ctx, xy, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 24);
        assert!(matches!(terminal, TCheck::Sat));
        // Rounds may interleave length axioms (len(h) enters the length seam).
        // Identify the S-clauses by SHAPE, order-independent:
        let is_memb = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        let is_dist = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Distinct),
                    ..
                }
            )
        };
        // S1: guarded, two string EQUALITIES on x (one against "").
        let s1 = splits.iter().filter(|(a, g)| {
            *g && a.len() == 2
                && a.iter()
                    .all(|&t| !is_memb(cx.terms, t) && !is_dist(cx.terms, t))
        });
        assert_eq!(s1.count(), 1, "exactly one S1 head split");
        // Task 4: the pass's own length axioms are now emitted as unguarded
        // [distinct(x,h·z), arith-companion] clauses (see `len_link_split`
        // and the S2 block): ge+le companions of the `x = h·z` length link
        // `len(x)=len(h·z)` PLUS ge+le companions of the S2 witness
        // canonicalization `len(h)=1` — four unguarded [dist, cmp] clauses,
        // all sharing the S1 witnesses' distinct atom, and NO other
        // unguarded clause. (Formerly S2 was a single unguarded
        // [dist, len(h)=1] clause; the bare Int equality routed to EUF, not
        // Arith, so the witness length never reached the arith model.)
        let is_cmp = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Ge | BuiltinOp::Le),
                    ..
                }
            )
        };
        // (The single-atom `guard: None` splits from the generic length-axiom
        // fixpoint — `≥0` / defining companions — also interleave; the pass's
        // own clauses are the unguarded ones carrying the distinct atom.)
        let unguarded: Vec<_> = splits
            .iter()
            .filter(|(a, g)| !*g && a.iter().any(|&t| is_dist(cx.terms, t)))
            .collect();
        assert_eq!(
            unguarded.len(),
            4,
            "link (2) + S2 witness-length (2) companion clauses"
        );
        for (a, _) in &unguarded {
            assert_eq!(a.len(), 2, "companion clause is [dist, cmp]");
            assert!(
                a.iter().any(|&t| is_cmp(cx.terms, t)),
                "every unguarded [dist, _] clause is a [distinct, arith-companion] pair"
            );
        }
        // S3 + S4: guarded [distinct, str.in_re] clauses.
        let s34: Vec<_> = splits
            .iter()
            .filter(|(a, g)| {
                *g && a.iter().any(|&t| is_dist(cx.terms, t))
                    && a.iter().any(|&t| is_memb(cx.terms, t))
            })
            .collect();
        assert_eq!(
            s34.len(),
            2,
            "head-class (S3) + tail-membership (S4) clauses"
        );
        // Their membership atoms sit on fresh terms (h resp. z·γ), not on x,
        // and their regex sides re-extract as constant regexes.
        for (atoms, _) in &s34 {
            let mt = atoms
                .iter()
                .copied()
                .find(|&t| is_memb(cx.terms, t))
                .unwrap();
            let (side, re_side) = super::memb_sides(cx.terms, mt);
            assert_ne!(side, x, "S3/S4 memberships are on fresh witnesses");
            assert!(crate::regex::extract_const_regex(cx.terms, re_side).is_some());
        }
    }

    #[test]
    fn bare_range_leaf_emits_guarded_len1_axiom() {
        // Slice 25 task 5b, Part 2: x ∈ [a-z] is a bare-range LEAF (no ground
        // prefix, not head-forced past itself) — before the leaf skip, the
        // pass must emit `lit → len(x) = 1` through its two arith companions
        // (deduped via `emitted_len_axioms`, same shape as the S2 witness
        // axiom), guarded by ¬lit, and mint NO concat on x (repair
        // eligibility preserved) — then leave the atom for model repair.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let m = memb_atom(&mut ctx, x, &Rex::Range('a' as u32, 'z' as u32));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(
            matches!(terminal, TCheck::Sat),
            "leaf saturates to the model-repair path"
        );
        let is_cmp = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Ge | BuiltinOp::Le),
                    ..
                }
            )
        };
        let len_axiom_splits: Vec<_> = splits
            .iter()
            .filter(|(a, g)| *g && a.len() == 1 && is_cmp(cx.terms, a[0]))
            .collect();
        assert_eq!(
            len_axiom_splits.len(),
            2,
            "ge + le companions of len(x)=1, each its own guarded [comp] split"
        );
        // No str.++ concat was minted on x — the leaf's repair eligibility
        // (memb_seeds requires a witness class with no constant, no concat)
        // is untouched.
        let is_memb = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        assert!(
            splits
                .iter()
                .all(|(a, _)| !a.iter().any(|&t| is_memb(cx.terms, t))),
            "bare-range leaf must never emit its own S-rule split"
        );
    }

    #[test]
    fn lone_leaf_star_tail_carves_out_with_min_len_axiom() {
        // Slice 26: x ∈ "b"·Σ·Σ* over a lone free leaf — the general LEAF
        // carve-out. NO Rule-S/E split ever fires (no skolems, no seam
        // churn); exactly ONE guarded [(>= (str.len x) 2)] clause (star
        // tail ⇒ no finite upper bound); then saturate to the model-repair
        // path.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let sigma = Rex::Range(0, regex::MAX_CODE);
        let r = regex::concat(vec![
            Rex::Range('b' as u32, 'b' as u32),
            sigma.clone(),
            regex::star(sigma),
        ]);
        let m = memb_atom(&mut ctx, x, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(
            matches!(terminal, TCheck::Sat),
            "leaf saturates to the model-repair path"
        );
        let is_memb = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        assert!(
            splits
                .iter()
                .all(|(a, _)| !a.iter().any(|&t| is_memb(cx.terms, t))),
            "leaf carve-out must never emit an S/E membership split"
        );
        let is_ge = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Ge),
                    ..
                }
            )
        };
        let is_le = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Le),
                    ..
                }
            )
        };
        let ge_splits: Vec<_> = splits
            .iter()
            .filter(|(a, g)| *g && a.len() == 1 && is_ge(cx.terms, a[0]))
            .collect();
        assert_eq!(
            ge_splits.len(),
            1,
            "exactly one guarded [(>= len 2)] lower-bound clause"
        );
        assert!(
            !splits
                .iter()
                .any(|(a, g)| *g && a.len() == 1 && is_le(cx.terms, a[0])),
            "star tail has no finite upper bound — no guarded le clause"
        );
    }

    #[test]
    fn lone_leaf_finite_concat_emits_both_bounds() {
        // Slice 26: x ∈ [a-c]·"b" — the shape the old Rule-S clause test
        // used. Now a LEAF: two guarded single-atom bound clauses
        // ([(>= len 2)] and [(<= len 2)]) across successive rounds, no
        // S-splits, terminal Sat.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let r = regex::concat(vec![
            Rex::Range('a' as u32, 'c' as u32),
            regex::lit_test("b"),
        ]);
        let m = memb_atom(&mut ctx, x, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(terminal, TCheck::Sat));
        let is_memb = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        assert!(
            splits
                .iter()
                .all(|(a, _)| !a.iter().any(|&t| is_memb(cx.terms, t))),
            "finite lone-leaf membership must not unfold either"
        );
        let is_cmp = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Ge | BuiltinOp::Le),
                    ..
                }
            )
        };
        let bound_splits: Vec<_> = splits
            .iter()
            .filter(|(a, g)| *g && a.len() == 1 && is_cmp(cx.terms, a[0]))
            .collect();
        assert_eq!(bound_splits.len(), 2, "ge + le bound clauses, one each");
    }

    #[test]
    fn empty_language_residual_conflicts() {
        // x ∈ re.none survives the pre-pass only when minted mid-search, but
        // the rule must still conflict on it directly.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let m = memb_atom(&mut ctx, x, &Rex::Empty);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (_, terminal) = run_rounds(&mut s, &mut cx, 8);
        assert!(matches!(terminal, TCheck::Conflict(_)));
    }

    #[test]
    fn fuel_exhaustion_saturates_to_model_path() {
        // D-satfuel (owner-authorized rework — this test formerly pinned a
        // hard `TCheck::Unknown` on fuel exhaustion): at fuel 0 the
        // membership pass SATURATES — `check()` falls through to
        // `TCheck::Sat` so the model build + membership repair + post-solve
        // self-check decide the final verdict (spec Saturation paragraph:
        // the pass "must not report Sat on its own authority; the model
        // build + the extended self-check are the only path to Sat" — the
        // SOLVER-level self-check still downgrades an unrealised Sat to
        // Unknown; that end-to-end posture is pinned at the solver level,
        // not here). Critically, saturation must not pollute the dedup
        // keys: a key minted for a never-emitted lemma would silently drop
        // that lemma forever.
        //
        // Slice 26 carrier truth-up: a LONE leaf `x` now takes the general
        // leaf carve-out (and, for `[a-c]*`, `min_len=0`/`max_len=None`
        // yields an empty bounds set, so the carve-out silently continues
        // forever — see `lone_leaf_star_zero_bounds_carves_out_silently`),
        // so this fuel/dedup-saturation pin rides a two-atom carrier `x·y`,
        // which is not repair-eligible and still routes through Rule E.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let y = var(&mut ctx, "y");
        let xy = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let m = memb_atom(&mut ctx, xy, &regex::star_range_test('a', 'c'));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        s.test_set_fuel(0);
        assert!(
            matches!(s.check(&mut cx, Effort::Full), TCheck::Sat),
            "fuel exhaustion saturates (falls through to the model path)"
        );
        // No dedup-key / witness pollution for the never-emitted expansion.
        assert!(
            s.emitted_memb.is_empty(),
            "no emitted_memb key for a never-emitted lemma"
        );
        assert!(
            s.memb_wits.is_empty(),
            "no witness pair for a never-emitted S1"
        );
        assert!(
            s.emitted_len_axioms.is_empty(),
            "no length-axiom key for a never-emitted companion"
        );
        // With fuel restored, the exact same expansion is still emittable
        // (nothing was dropped by the saturated round).
        s.test_set_fuel(40);
        assert!(
            matches!(s.check(&mut cx, Effort::Full), TCheck::Split { .. }),
            "the saturated round dropped nothing — the expansion now emits"
        );
    }

    #[test]
    fn lone_leaf_star_zero_bounds_carves_out_silently() {
        // Slice 26: pins the EMPTY-bounds branch of the general leaf
        // carve-out. x ∈ [a-c]* is a lone leaf whose `cur` is
        // `Star(Range('a','c'))`: `min_len == 0` (no `Ge` bound) and
        // `max_len == None` (no `Le` bound, unbounded tail) — so the
        // carve-out's `bounds` vec is empty and it silently `continue`s
        // every round, contributing NO fact and never falling through to
        // Rule S/E. The atom is left entirely for model repair, and
        // "" is nullable so the repair witness is immediate: terminal Sat,
        // with NO splits of any kind and no length-axiom keys minted.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let m = memb_atom(&mut ctx, x, &regex::star_range_test('a', 'c'));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(
            matches!(terminal, TCheck::Sat),
            "empty-bounds leaf carve-out saturates straight to the model-repair path"
        );
        assert!(
            splits.is_empty(),
            "no bound to contribute (min_len=0, max_len=None) ⇒ no split of any kind"
        );
        assert!(
            s.emitted_len_axioms.is_empty(),
            "no length-axiom key minted when bounds is empty"
        );
    }

    #[test]
    fn memb_minted_eq_defers_wordeq_fsplit() {
        // D-wordeq-skip (owner-authorized): an equality MINTED BY THE
        // MEMBERSHIP PASS sitting in eq_true must NOT trigger the
        // word-equation F-split — the S-rules are its resolution, and the
        // redundant Nielsen skolemization minted leaf-destroying concats
        // (`h = x·z2'`) into the repair witnesses' classes. A USER-INPUT
        // equation of the same shape still F-splits.
        let mk = |ctx: &mut Context| -> (TermId, TermId) {
            let x = var(ctx, "x");
            let y = var(ctx, "y");
            let z = var(ctx, "z");
            let yz = ctx
                .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[y, z])
                .unwrap();
            let eq = ctx.mk_eq(x, yz).unwrap();
            (eq, x)
        };

        // Case 1: memb-minted (as `register_atom` records it) — no split at
        // all; the equality is definitional and waits on the S-rules.
        let mut ctx = Context::new();
        let (eq, _) = mk(&mut ctx);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), eq);
        s.minted_eqs.insert(eq);
        s.memb_minted_eqs.insert(eq);
        s.test_force_eq_true(eq);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 8);
        assert!(matches!(terminal, TCheck::Sat));
        assert!(
            splits.is_empty(),
            "no wordeq lemma over a memb-minted definitional equality"
        );

        // Case 2: the SAME shape as user input — the Nielsen F-split
        // [len_eq, a_pref, b_pref] still fires.
        let mut ctx2 = Context::new();
        let (eq2, _) = mk(&mut ctx2);
        let (mut s2, mut eq_e2, atoms2) = harness(&mut ctx2);
        let mut cx2 = TheoryCtx {
            terms: &mut ctx2,
            eq: &mut eq_e2,
            atoms: &atoms2,
        };
        s2.new_var(&mut cx2, shinri_core::Var::new(0), eq2);
        s2.test_force_eq_true(eq2);
        let (splits2, _) = run_rounds(&mut s2, &mut cx2, 16);
        assert!(
            splits2.iter().any(|(a, g)| *g && a.len() == 3),
            "user-input concat equation still emits the 3-disjunct F-split"
        );
    }
}
