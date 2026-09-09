//! Slice 47: the post-solve array-model gate. See
//! `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md` §3.
//!
//! The refinement loop in `crate::driver` reaches a fixpoint on the LEMMA SET,
//! not on the array axioms, so it can report `Sat` on a model that no real
//! array realises. This module re-derives the array pins from that model and
//! rejects the ones that DEFINITELY break an axiom.
//!
//! The governing invariant is that arrays are PARTIAL: only indices touched by
//! a read or a store are pinned, every other entry is FREE, and a free entry
//! can be given any value, so it can never witness a violation. Rejecting an
//! underdetermined entry would turn correct `sat` answers into fenced
//! `Unknown`s, which is a regression, not a fix.

use std::collections::BTreeMap;

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};
use shinri_num::Integer;

use crate::abstraction::Abstraction;
use crate::check::{select_parts, store_parts};
use crate::collect::Collected;
use crate::driver::SatBridge;

/// Why a model was rejected. Carried out of the gate so the caller can report
/// WHICH axiom the model breaks — this is the bisect instrument, not decoration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rejection {
    /// Two reads on the same array at the same index value disagree.
    ReadConflict { array: TermId, index: Integer },
    /// A read disagrees with the pin its store chain forces at that index.
    ReadMismatch { select: TermId },
    /// A TRUE array-eq proxy contradicted by pins defined on both sides.
    EqPinsDiffer { atom: TermId },
    /// A FALSE array-eq proxy on two arrays the pins force to be equal.
    DiseqPinsForceEqual { atom: TermId },
    /// An array-eq proxy with no value in the model.
    ProxyUnassigned { atom: TermId },
    /// An array-sorted term outside the grammar of §3.4.
    Unsupported { term: TermId, why: &'static str },
}

/// The pinned entries of an array term: `base` is the declared array constant
/// at the bottom of the store chain, `points` the indices the model pins.
/// PARTIAL by construction — an index absent from `points` is FREE, and a free
/// entry can never witness a violation.
struct Pins {
    base: TermId,
    points: BTreeMap<Integer, Integer>,
}

/// True if `t` is a nullary uninterpreted constant — a DECLARED array.
fn is_declared_const(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            matches!(op, Op::Uninterpreted(_)) && ctx.children(*args).is_empty()
        }
        TermNode::Const { .. } => false,
    }
}

/// One `validate` pass over one model.
///
/// It exists to hold two caches. `reads_by_base` buckets `abs.read_of` by the
/// array term each select reads from, and `base_memo` holds the read pins of
/// each declared base array once they have been derived. Without them the base
/// read-scan reruns for every select, which is quadratic in the number of
/// selects (ruling R7) — the caches change no verdict, only the cost of
/// reaching it.
struct Gate<'a> {
    ctx: &'a Context,
    bridge: &'a dyn SatBridge,
    reads_by_base: FxHashMap<TermId, Vec<(TermId, TermId)>>,
    base_memo: FxHashMap<TermId, BTreeMap<Integer, Integer>>,
}

impl<'a> Gate<'a> {
    fn new(ctx: &'a Context, abs: &Abstraction, bridge: &'a dyn SatBridge) -> Self {
        let mut reads_by_base: FxHashMap<TermId, Vec<(TermId, TermId)>> = FxHashMap::default();
        for (&sel, &r) in &abs.read_of {
            if let Some((base, idx)) = select_parts(ctx, sel) {
                reads_by_base.entry(base).or_default().push((idx, r));
            }
        }
        Gate {
            ctx,
            bridge,
            reads_by_base,
            base_memo: FxHashMap::default(),
        }
    }

    /// Pins contributed by the READS on one array term, derived once and cached.
    ///
    /// This is where functional consistency is checked, and it is why the gate
    /// must NOT reuse `crate::model::array_model`: that function dedups
    /// first-wins (`model.rs:136`) and would silently swallow the conflict this
    /// detects. A conflict is returned rather than cached, so the first scan of
    /// a conflicting base still reports it — memoization must not swallow it.
    fn base_pins(&mut self, arr: TermId) -> Result<&BTreeMap<Integer, Integer>, Rejection> {
        if !self.base_memo.contains_key(&arr) {
            let reads: &[(TermId, TermId)] = self
                .reads_by_base
                .get(&arr)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let mut points: BTreeMap<Integer, Integer> = BTreeMap::new();
            for &(idx, r) in reads {
                let (Some((_, iv)), Some((_, rv))) = (
                    self.bridge.value_bv(self.ctx, idx),
                    self.bridge.value_bv(self.ctx, r),
                ) else {
                    // No value ⇒ nothing pinned. Not a violation.
                    continue;
                };
                match points.get(&iv) {
                    Some(prev) if prev != &rv => {
                        return Err(Rejection::ReadConflict {
                            array: arr,
                            index: iv,
                        });
                    }
                    Some(_) => {}
                    None => {
                        points.insert(iv, rv);
                    }
                }
            }
            self.base_memo.insert(arr, points);
        }
        Ok(&self.base_memo[&arr])
    }

    /// Compute the pins of an array-sorted term, walking its store chain down to
    /// a declared constant. Anything outside that grammar is a conservative
    /// reject.
    ///
    /// The walk is iterative rather than recursive so a long store chain (BMC
    /// instances build them thousands deep) cannot overflow the stack. It
    /// descends WITHOUT reading any value first, so the order in which failures
    /// are reported matches a bottom-up evaluation: a malformed base before any
    /// missing store value, and an inner store before an outer one.
    fn pins(&mut self, t: TermId) -> Result<Pins, Rejection> {
        let mut frames: Vec<TermId> = Vec::new(); // store terms, outermost first
        let mut cur = t;
        let base = loop {
            if is_declared_const(self.ctx, cur) {
                break cur;
            }
            match store_parts(self.ctx, cur) {
                Some((inner, _, _)) => {
                    frames.push(cur);
                    cur = inner;
                }
                None => {
                    return Err(Rejection::Unsupported {
                        term: cur,
                        why: "array term is neither a declared constant nor a store chain",
                    })
                }
            }
        };

        let mut points = self.base_pins(base)?.clone();
        for &frame in frames.iter().rev() {
            let (_, i, e) = store_parts(self.ctx, frame).expect("frame was matched as a store");
            let (Some((_, iv)), Some((_, ev))) = (
                self.bridge.value_bv(self.ctx, i),
                self.bridge.value_bv(self.ctx, e),
            ) else {
                return Err(Rejection::Unsupported {
                    term: frame,
                    why: "store index or element has no value in the model",
                });
            };
            // A later write to the same index WINS.
            points.insert(iv, ev);
        }
        Ok(Pins { base, points })
    }
}

/// Extract the two operands of an array equality atom.
///
/// ONLY a binary `Eq` is accepted (ruling R5). The proxy carries EQUALITY
/// semantics, so reading a `distinct` atom as an `Eq` would invert C2-pos and
/// C2-neg, and taking the first two operands of an n-ary `Eq` would silently
/// drop the rest. `crate::normalize::normalize_array_atoms` desugars every
/// n-ary and every `distinct` array atom into binary `Eq`s before `collect`
/// runs, so both branches are unreachable in the pipeline today; rejecting
/// keeps them unreachable AND sound if normalization ever changes.
fn array_pair(ctx: &Context, atom: TermId) -> Result<(TermId, TermId), Rejection> {
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Eq),
        args,
        ..
    } = ctx.term_node(atom)
    {
        let k = ctx.children(*args);
        if k.len() == 2 {
            return Ok((k[0], k[1]));
        }
        return Err(Rejection::Unsupported {
            term: atom,
            why: "array equality atom is not binary; normalization should have split it",
        });
    }
    Err(Rejection::Unsupported {
        term: atom,
        why: "array atom is not an `=`; the proxy carries equality semantics only",
    })
}

/// Index/element widths of an array-sorted term.
fn array_widths(ctx: &Context, arr: TermId) -> Option<(u32, u32)> {
    match ctx.sort_node(ctx.sort_of(arr)) {
        SortNode::Array(i, e) => Some((ctx.bv_width(*i)?, ctx.bv_width(*e)?)),
        _ => None,
    }
}

/// The post-solve array-model gate (spec §3).
///
/// Returns `Ok(())` when the model is a genuine QF_ABV witness, and
/// `Err(Rejection)` when it DEFINITELY is not. Underdetermination is NOT a
/// rejection: where the pins leave an entry free the model has real freedom,
/// and rejecting there would turn correct answers into fenced unknowns.
pub fn validate(
    ctx: &Context,
    abs: &Abstraction,
    c: &Collected,
    bridge: &dyn SatBridge,
) -> Result<(), Rejection> {
    let mut gate = Gate::new(ctx, abs, bridge);

    // C1 — read soundness. Covers functional consistency (conflicting reads on
    // a bare constant, caught inside `base_pins`) and read-over-write (a read
    // through a chain that disagrees with the chain's pin), in one pass.
    for (&sel, &r) in &abs.read_of {
        let Some((arr, idx)) = select_parts(ctx, sel) else {
            continue;
        };
        let p = gate.pins(arr)?;
        let (Some((_, iv)), Some((_, rv))) = (bridge.value_bv(ctx, idx), bridge.value_bv(ctx, r))
        else {
            // An index or read with no value pins nothing, so nothing can be
            // contradicted here.
            continue;
        };
        if let Some(pinned) = p.points.get(&iv) {
            if pinned != &rv {
                return Err(Rejection::ReadMismatch { select: sel });
            }
        }
    }

    // C2 / C3 — the array equality atoms.
    for &atom in &c.array_eqs {
        let (a, b) = array_pair(ctx, atom)?;
        let Some(&proxy) = abs.eq_proxy.get(&atom) else {
            continue;
        };
        // §3.4: mismatched widths are outside the grammar.
        match (array_widths(ctx, a), array_widths(ctx, b)) {
            (Some(wa), Some(wb)) if wa == wb => {}
            _ => {
                return Err(Rejection::Unsupported {
                    term: atom,
                    why: "array-eq operands have mismatched or non-BV index/element widths",
                })
            }
        }

        // C3 — proxy totality.
        let Some(pv) = bridge.value_bool(proxy) else {
            return Err(Rejection::ProxyUnassigned { atom });
        };

        let pa = gate.pins(a)?;
        let pb = gate.pins(b)?;

        if pv {
            // C2-pos: reject only where BOTH sides are pinned and differ.
            for (k, va) in &pa.points {
                if let Some(vb) = pb.points.get(k) {
                    if va != vb {
                        return Err(Rejection::EqPinsDiffer { atom });
                    }
                }
            }
        } else {
            // C2-neg: reject only when the arrays are DEFINITELY equal, i.e.
            // they share a base AND every index in the union of the two pin
            // sets is pinned on both sides with equal values. A one-sided pin
            // leaves that entry free on the other side, so the disequality is
            // still satisfiable and the gate must stay silent.
            if pa.base == pb.base
                && pa.points.len() == pb.points.len()
                && pa.points.iter().all(|(k, va)| pb.points.get(k) == Some(va))
            {
                return Err(Rejection::DiseqPinsForceEqual { atom });
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abstraction::abstract_arrays;
    use crate::collect::collect;
    use crate::driver::fake::FakeBridge;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    fn arr_sort(ctx: &mut Context) -> shinri_core::SortId {
        let i = ctx.bv_sort(8);
        let e = ctx.bv_sort(8);
        ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, n: &str, s: shinri_core::SortId) -> shinri_core::TermId {
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    fn bv(v: u64) -> (u32, Integer) {
        (8, Integer::from(v))
    }

    /// C1: two selects on the SAME array at the SAME index value with
    /// DIFFERENT read values is a definite functional-consistency violation.
    #[test]
    fn c1_rejects_two_reads_same_index_different_values() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let si = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let sj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let atom = ctx.mk_eq(si, sj).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(7));
        b.bv.insert(j, bv(7)); // same index value
        b.bv.insert(abs.read_of[&si], bv(1));
        b.bv.insert(abs.read_of[&sj], bv(2)); // different read values

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::ReadConflict { .. })
        ));
    }

    /// C1 stays SILENT when the index values differ — nothing is pinned twice.
    #[test]
    fn c1_silent_when_indices_differ() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let si = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let sj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let atom = ctx.mk_eq(si, sj).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(7));
        b.bv.insert(j, bv(8)); // different index values
        b.bv.insert(abs.read_of[&si], bv(1));
        b.bv.insert(abs.read_of[&sj], bv(2));

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C1 stays SILENT when the read var has NO value: an unassigned read pins
    /// nothing, so no index is claimed twice.
    #[test]
    fn c1_silent_when_a_read_is_unassigned() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let si = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let sj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let atom = ctx.mk_eq(si, sj).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(7));
        b.bv.insert(j, bv(7)); // same index value
        b.bv.insert(abs.read_of[&si], bv(1));
        // `sj`'s read var is deliberately left with no value.

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C1: a read through a store chain must match the chain's pin (ROW).
    #[test]
    fn c1_rejects_read_disagreeing_with_store_pin() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        let other = uconst(&mut ctx, "o", s8);
        let atom = ctx.mk_eq(sel, other).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(3));
        b.bv.insert(e, bv(9));
        b.bv.insert(abs.read_of[&sel], bv(4)); // must be 9
        b.bv.insert(other, bv(4));

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::ReadMismatch { .. })
        ));
    }

    /// C1 stays SILENT on a read through a chain that writes a DIFFERENT index:
    /// the base is free at the read's index, so no pin is contradicted.
    #[test]
    fn c1_silent_on_read_past_a_store_to_another_index() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let e = uconst(&mut ctx, "e", s8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, j])
            .unwrap();
        let other = uconst(&mut ctx, "o", s8);
        let atom = ctx.mk_eq(sel, other).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(3));
        b.bv.insert(j, bv(4)); // reads past the write
        b.bv.insert(e, bv(9));
        b.bv.insert(abs.read_of[&sel], bv(42)); // free entry: anything goes
        b.bv.insert(other, bv(42));

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C2-neg: two chains over the SAME base writing the SAME index set with
    /// the SAME values are definitely equal, so a FALSE proxy is a violation.
    /// This is the `wchains002ue` shape.
    #[test]
    fn c2_neg_rejects_false_proxy_on_commuting_chains() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let e = uconst(&mut ctx, "e", s8);
        let f = uconst(&mut ctx, "f", s8);
        // chain1 = store(store(a,i,e),j,f); chain2 = store(store(a,j,f),i,e)
        let c1a = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let c1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[c1a, j, f])
            .unwrap();
        let c2a = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, j, f])
            .unwrap();
        let c2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[c2a, i, e])
            .unwrap();
        let atom = ctx.mk_eq(c1, c2).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(j, bv(2)); // distinct indices ⇒ the writes commute
        b.bv.insert(e, bv(10));
        b.bv.insert(f, bv(20));
        b.boolv.insert(abs.eq_proxy[&atom], false); // claims they differ

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::DiseqPinsForceEqual { .. })
        ));
    }

    /// C2-neg stays SILENT when the chains have DIFFERENT bases: the two base
    /// arrays are free and can be separated at an unpinned index.
    #[test]
    fn c2_neg_silent_on_different_bases() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let a2 = uconst(&mut ctx, "a2", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let c1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let c2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a2, i, e])
            .unwrap();
        let atom = ctx.mk_eq(c1, c2).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(10));
        b.boolv.insert(abs.eq_proxy[&atom], false);

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C2-neg stays SILENT when one side pins an index the other leaves free:
    /// the free entry can be given a different value, so the two arrays are
    /// still separable and the disequality is satisfiable.
    #[test]
    fn c2_neg_silent_when_one_side_pins_an_extra_index() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let c1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let atom = ctx.mk_eq(c1, a).unwrap(); // rhs pins nothing
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(10));
        b.boolv.insert(abs.eq_proxy[&atom], false);

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C2-pos: a TRUE proxy contradicted by pins that are defined on BOTH
    /// sides and differ.
    #[test]
    fn c2_pos_rejects_true_proxy_when_both_sides_pinned_and_differ() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let f = uconst(&mut ctx, "f", s8);
        let c1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let c2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, f])
            .unwrap();
        let atom = ctx.mk_eq(c1, c2).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(10));
        b.bv.insert(f, bv(11)); // same index, different value
        b.boolv.insert(abs.eq_proxy[&atom], true);

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::EqPinsDiffer { .. })
        ));
    }

    /// C2-pos stays SILENT when only ONE side is pinned at the index: the
    /// other side is free there and can be made to agree.
    #[test]
    fn c2_pos_silent_when_only_one_side_pinned() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let c1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let atom = ctx.mk_eq(c1, a).unwrap(); // rhs pins nothing
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(10));
        b.boolv.insert(abs.eq_proxy[&atom], true);

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }

    /// C3: an unassigned proxy is a rejection, not a don't-care.
    #[test]
    fn c3_rejects_unassigned_proxy() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let a = uconst(&mut ctx, "a", a_s);
        let b_arr = uconst(&mut ctx, "b", a_s);
        let atom = ctx.mk_eq(a, b_arr).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let b = FakeBridge::default(); // no proxy value at all

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::ProxyUnassigned { .. })
        ));
    }

    /// §3.4: an array-sorted `ite` is outside the grammar ⇒ conservative reject.
    #[test]
    fn unsupported_array_ite_is_rejected() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let b_arr = uconst(&mut ctx, "b", a_s);
        let bool_s = ctx.bool_sort();
        let p = uconst(&mut ctx, "p", bool_s);
        let ite = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[p, a, b_arr])
            .unwrap();
        let i = uconst(&mut ctx, "i", s8);
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[ite, i])
            .unwrap();
        let other = uconst(&mut ctx, "o", s8);
        let atom = ctx.mk_eq(sel, other).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(abs.read_of[&sel], bv(1));
        b.bv.insert(other, bv(1));

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::Unsupported { .. })
        ));
    }

    /// Ruling R5: the proxy carries EQUALITY semantics, so a raw `distinct`
    /// atom must NOT be read as an `Eq` — that would invert C2-pos and C2-neg.
    /// `normalize_array_atoms` desugars every `distinct` before the gate runs,
    /// so this shape is unreachable in the pipeline; the conservative reject
    /// keeps it unreachable AND sound if normalization ever changes.
    #[test]
    fn distinct_array_atom_is_unsupported_not_read_as_eq() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let a = uconst(&mut ctx, "a", a_s);
        let b_arr = uconst(&mut ctx, "b", a_s);
        // Deliberately NOT run through `normalize_array_atoms`.
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b_arr])
            .unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);
        assert_eq!(c.array_eqs, vec![atom]);

        let mut b = FakeBridge::default();
        // Give the proxy a value so `ProxyUnassigned` cannot be what fires.
        b.boolv.insert(abs.eq_proxy[&atom], true);

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::Unsupported { .. })
        ));
    }

    /// Ruling R5: an n-ary `Eq` is not a pair, so taking `k[0], k[1]` would
    /// silently ignore the remaining operands. Conservative reject instead.
    #[test]
    fn nary_array_eq_is_unsupported() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let a = uconst(&mut ctx, "a", a_s);
        let b_arr = uconst(&mut ctx, "b", a_s);
        let c_arr = uconst(&mut ctx, "c", a_s);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[a, b_arr, c_arr])
            .unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);
        assert_eq!(c.array_eqs, vec![atom]);

        let mut b = FakeBridge::default();
        b.boolv.insert(abs.eq_proxy[&atom], true);

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::Unsupported { .. })
        ));
    }

    /// The gate must NOT be vacuously rejecting: a genuine model passes.
    #[test]
    fn genuine_model_passes_every_check() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(3));
        b.bv.insert(e, bv(9));
        b.bv.insert(abs.read_of[&sel], bv(9)); // agrees with the store pin

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }
}
