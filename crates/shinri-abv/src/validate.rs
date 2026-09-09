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
//!
//! The pass order matters and is fixed: EVERY pin is derived first
//! (`Gate::derive_base_pins`), and only then does any check run. Reads through
//! a store chain contribute pins to the chain's BASE array (see
//! `derive_base_pins`), so a check that ran while pins were still being
//! discovered could consult an incomplete pin set.

use std::collections::hash_map::Entry;
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

/// An array-sorted term resolved against the model: the declared constant its
/// store chain bottoms out in, and the writes that chain lays over it.
///
/// `overlay` is keyed by the model's INDEX VALUES, with a later (more outward)
/// write to the same value winning, so it is the chain's own contribution to
/// the term's extension and nothing else.
struct Chain {
    base: TermId,
    overlay: BTreeMap<Integer, Integer>,
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
///
/// Arity > 0 is deliberately NOT accepted: an array-sorted uninterpreted
/// application is outside the §3.4 grammar, because its extension is not
/// determined by the model's BV assignments the way a declared constant's is.
fn is_declared_const(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            matches!(op, Op::Uninterpreted(_)) && ctx.children(*args).is_empty()
        }
        TermNode::Const { .. } => false,
    }
}

/// Resolve an array-sorted term against the model. Anything outside the §3.4
/// grammar — a store chain over a declared constant — is a conservative reject.
///
/// The walk is iterative rather than recursive so a long store chain (BMC
/// instances build them thousands deep) cannot overflow the stack. It descends
/// WITHOUT reading any value first, so failures are reported in the order a
/// bottom-up evaluation would report them: a malformed base before any missing
/// store value, and an inner store before an outer one. Each frame carries the
/// index and element terms it was matched with, so no frame is re-decoded (and
/// the gate holds no `expect` that a re-decode will succeed).
fn resolve_chain(ctx: &Context, bridge: &dyn SatBridge, t: TermId) -> Result<Chain, Rejection> {
    let mut frames: Vec<(TermId, TermId, TermId)> = Vec::new(); // (store, index, elem)
    let mut cur = t;
    let base = loop {
        if is_declared_const(ctx, cur) {
            break cur;
        }
        match store_parts(ctx, cur) {
            Some((inner, i, e)) => {
                frames.push((cur, i, e));
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

    let mut overlay: BTreeMap<Integer, Integer> = BTreeMap::new();
    for &(frame, i, e) in frames.iter().rev() {
        let (Some((_, iv)), Some((_, ev))) = (bridge.value_bv(ctx, i), bridge.value_bv(ctx, e))
        else {
            // Ruling R9. A SELECT with no value is silence (see
            // `Gate::derive_base_pins`) but a STORE with no value MUST reject,
            // and the reason is stronger than "be conservative": a silently
            // dropped store pin CORRUPTS the pin set, and C2-neg's definiteness
            // argument reads that set. Two chains differing only at an index
            // whose value is unknown would then look pinned-identically and
            // `DiseqPinsForceEqual` would fire on a model that is NOT
            // definitely equal. Under-pinning a store therefore turns into
            // OVER-rejection elsewhere, which is the failure mode this slice
            // cannot afford. Spec §3.4 lists the select and store cases
            // together; that is loose wording, and this is the asymmetry.
            return Err(Rejection::Unsupported {
                term: frame,
                why: "store index or element has no value in the model",
            });
        };
        // A later write to the same index WINS.
        overlay.insert(iv, ev);
    }
    Ok(Chain { base, overlay })
}

/// One `validate` pass over one model: the derived pin state plus its caches.
///
/// `chains` memoizes the resolution of each array term. `base_pins` holds the
/// entries the model FORCES on each declared base array; deriving it once,
/// up front, is both the correctness requirement (see `derive_base_pins`) and
/// ruling R7's cost requirement — the alternative is re-deriving a base's pins
/// once per select, which is quadratic in the number of selects.
struct Gate<'a> {
    ctx: &'a Context,
    bridge: &'a dyn SatBridge,
    chains: FxHashMap<TermId, Chain>,
    base_pins: FxHashMap<TermId, BTreeMap<Integer, Integer>>,
}

impl<'a> Gate<'a> {
    fn new(ctx: &'a Context, bridge: &'a dyn SatBridge) -> Self {
        Gate {
            ctx,
            bridge,
            chains: FxHashMap::default(),
            base_pins: FxHashMap::default(),
        }
    }

    /// The resolved chain of an array term, derived once and cached.
    fn chain(&mut self, t: TermId) -> Result<&Chain, Rejection> {
        match self.chains.entry(t) {
            Entry::Occupied(o) => Ok(o.into_mut()),
            Entry::Vacant(v) => Ok(v.insert(resolve_chain(self.ctx, self.bridge, t)?)),
        }
    }

    /// Derive every entry the model FORCES on the declared base arrays, and
    /// check functional consistency (C1) while doing it.
    ///
    /// A read is attributed to the BASE of its chain, not to the chain term
    /// (ruling R8). If `select(chain, j)` has index value `jv` and NO frame of
    /// that chain writes `jv`, then `chain[jv] == base[jv]` by the store axiom,
    /// so the model's read value forces `base[jv]`. Without this, two reads
    /// through DIFFERENT chains over the SAME base at the same index value
    /// would each see an empty pin set and the gate would stay silent on a
    /// definite violation — a hole `check.rs::functional_consistency` does not
    /// cover either, since it skips pairs whose syntactic arrays differ.
    ///
    /// The converse is the fence: a read whose index IS written by a frame is
    /// SHADOWED. It observes the chain's own write, says nothing whatever about
    /// the base, and must NOT be attributed — attributing it would invent a
    /// base pin the model never committed to and turn correct answers into
    /// fenced unknowns.
    ///
    /// This is also why the gate must NOT reuse `crate::model::array_model`:
    /// that function dedups conflicting reads first-wins (`model.rs:136`) and
    /// would silently swallow the conflict detected here.
    fn derive_base_pins(&mut self, abs: &Abstraction) -> Result<(), Rejection> {
        for (&sel, &r) in &abs.read_of {
            let Some((arr, idx)) = select_parts(self.ctx, sel) else {
                continue;
            };
            let idx_val = self.bridge.value_bv(self.ctx, idx);
            let read_val = self.bridge.value_bv(self.ctx, r);
            // Resolve unconditionally: an array term outside the grammar is a
            // reject whether or not this particular read pins anything.
            let ch = self.chain(arr)?;
            let base = ch.base;
            let (Some((_, iv)), Some((_, rv))) = (idx_val, read_val) else {
                // Ruling R9. A read with no index or no value pins nothing, so
                // there is no violation here to detect. Silence is correct;
                // rejecting would be over-rejection on an underdetermined entry.
                continue;
            };
            if ch.overlay.contains_key(&iv) {
                // Shadowed by the chain's own write — says nothing about `base`.
                continue;
            }
            let points = self.base_pins.entry(base).or_default();
            match points.get(&iv) {
                Some(prev) if prev != &rv => {
                    return Err(Rejection::ReadConflict {
                        array: base,
                        index: iv,
                    });
                }
                Some(_) => {}
                None => {
                    points.insert(iv, rv);
                }
            }
        }
        Ok(())
    }

    /// C1 read soundness: a read must agree with whatever its array term is
    /// already pinned to at the read's index — the chain's own write if there
    /// is one, else the base's pin. An unpinned index is FREE, and the check
    /// stays silent there.
    fn check_reads(&mut self, abs: &Abstraction) -> Result<(), Rejection> {
        for (&sel, &r) in &abs.read_of {
            let Some((arr, idx)) = select_parts(self.ctx, sel) else {
                continue;
            };
            let idx_val = self.bridge.value_bv(self.ctx, idx);
            let read_val = self.bridge.value_bv(self.ctx, r);
            let ch = self.chain(arr)?;
            let base = ch.base;
            let (Some((_, iv)), Some((_, rv))) = (idx_val, read_val) else {
                continue;
            };
            let pinned = ch.overlay.get(&iv).cloned();
            let pinned =
                pinned.or_else(|| self.base_pins.get(&base).and_then(|p| p.get(&iv)).cloned());
            if let Some(p) = pinned {
                if p != rv {
                    return Err(Rejection::ReadMismatch { select: sel });
                }
            }
        }
        Ok(())
    }

    /// The full pin map of an array term: the base's derived pins with the
    /// chain's writes laid over them.
    fn pins(&mut self, t: TermId) -> Result<Pins, Rejection> {
        let ch = self.chain(t)?;
        let base = ch.base;
        let overlay = ch.overlay.clone();
        let mut points = self.base_pins.get(&base).cloned().unwrap_or_default();
        points.extend(overlay);
        Ok(Pins { base, points })
    }

    /// C2 / C3 over the array equality atoms.
    fn check_array_eqs(&mut self, abs: &Abstraction, c: &Collected) -> Result<(), Rejection> {
        for &atom in &c.array_eqs {
            let (a, b) = array_pair(self.ctx, atom)?;
            let Some(&proxy) = abs.eq_proxy.get(&atom) else {
                continue;
            };
            // §3.4: mismatched or non-BV index/element sorts are outside the
            // grammar — the gate reasons about BV index VALUES, and a sort with
            // no bit width has none.
            match (array_widths(self.ctx, a), array_widths(self.ctx, b)) {
                (Some(wa), Some(wb)) if wa == wb => {}
                _ => {
                    return Err(Rejection::Unsupported {
                        term: atom,
                        why: "array-eq operands have mismatched or non-BV index/element widths",
                    })
                }
            }

            // C3 — proxy totality.
            let Some(pv) = self.bridge.value_bool(proxy) else {
                return Err(Rejection::ProxyUnassigned { atom });
            };

            let pa = self.pins(a)?;
            let pb = self.pins(b)?;

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
                // sets is pinned on both sides with equal values. A one-sided
                // pin leaves that entry free on the other side, so the
                // disequality is still satisfiable and the gate must stay silent.
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

/// Index/element widths of an array-sorted term. `None` when either component
/// sort is not a bitvector (a nested array index, say), which §3.4 excludes.
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
    let mut gate = Gate::new(ctx, bridge);
    // Derive first, check second. Every check below reads the base pin set, and
    // reads through a store chain contribute to it, so no check may run until
    // the whole set exists.
    gate.derive_base_pins(abs)?;
    gate.check_reads(abs)?;
    gate.check_array_eqs(abs, c)
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

    /// §3.4: an array-sorted uninterpreted application with arity > 0 is
    /// outside the grammar — its extension is not determined by the model's BV
    /// assignments the way a declared constant's is (ruling R10: a NULLARY one
    /// is a declared array constant and must keep being accepted).
    #[test]
    fn unsupported_array_sorted_uninterpreted_application_is_rejected() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let i = uconst(&mut ctx, "i", s8);
        let g = ctx.declare_fun("g", &[s8], a_s);
        let ga = ctx.mk_app(Op::Uninterpreted(g), &[i]).unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[ga, i])
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

    /// §3.4: the gate reasons about BV index VALUES, so an array whose index
    /// sort has no bit width — here a nested `(Array (Array _ _) _)` — is
    /// outside the grammar. This is the "non-BV" half of `array_widths`.
    #[test]
    fn unsupported_non_bv_array_index_sort_is_rejected() {
        let mut ctx = Context::new();
        let inner = arr_sort(&mut ctx);
        let e = ctx.bv_sort(8);
        let nested = ctx.array_sort(inner, e); // (Array (Array (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        let a = uconst(&mut ctx, "a", nested);
        let b_arr = uconst(&mut ctx, "b", nested);
        let atom = ctx.mk_eq(a, b_arr).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);
        assert_eq!(c.array_eqs, vec![atom]);

        let mut b = FakeBridge::default();
        // Assigned, so `ProxyUnassigned` cannot be what fires.
        b.boolv.insert(abs.eq_proxy[&atom], true);

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::Unsupported { .. })
        ));
    }

    /// §3.4 / ruling R9: a STORE whose element has no value in the model must
    /// reject. Dropping the pin silently would corrupt the pin set that
    /// C2-neg's definiteness argument reads, so under-pinning here would turn
    /// into OVER-rejection there. Contrast `c1_silent_when_a_read_is_unassigned`.
    #[test]
    fn unsupported_store_element_with_no_model_value_is_rejected() {
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
        // `e` is deliberately left with no value.
        b.bv.insert(abs.read_of[&sel], bv(4));
        b.bv.insert(other, bv(4));

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::Unsupported { .. })
        ));
    }

    /// §3.4: a store chain that BOTTOMS OUT in something other than a declared
    /// constant is rejected. Distinct from `unsupported_array_ite_is_rejected`,
    /// where the `ite` sits at the select's array position rather than under a
    /// store.
    #[test]
    fn unsupported_store_chain_bottoming_out_in_an_ite_is_rejected() {
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
        let e = uconst(&mut ctx, "e", s8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[ite, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        let other = uconst(&mut ctx, "o", s8);
        let atom = ctx.mk_eq(sel, other).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(2));
        b.bv.insert(abs.read_of[&sel], bv(2));
        b.bv.insert(other, bv(2));

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::Unsupported { .. })
        ));
    }

    /// Ruling R8: two reads through DIFFERENT store chains over the SAME base,
    /// at the same index value, with neither chain writing that index. Both
    /// reads see `base[jv]`, so different read values are a definite functional
    /// -consistency violation. Before R8 both reads saw an empty pin set and the
    /// gate stayed silent — and `check.rs::functional_consistency` misses this
    /// shape too, because it skips pairs whose syntactic arrays differ.
    #[test]
    fn c1_rejects_reads_through_different_chains_over_one_base() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let i2 = uconst(&mut ctx, "i2", s8);
        let e2 = uconst(&mut ctx, "e2", s8);
        let j = uconst(&mut ctx, "j", s8);
        let k = uconst(&mut ctx, "k", s8);
        let st1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let st2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i2, e2])
            .unwrap();
        let sel1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st1, j])
            .unwrap();
        let sel2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st2, k])
            .unwrap();
        let atom = ctx.mk_eq(sel1, sel2).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(1));
        b.bv.insert(e, bv(5));
        b.bv.insert(i2, bv(2));
        b.bv.insert(e2, bv(6));
        b.bv.insert(j, bv(7)); // neither chain writes 7 ...
        b.bv.insert(k, bv(7)); // ... so both reads see a[7]
        b.bv.insert(abs.read_of[&sel1], bv(1));
        b.bv.insert(abs.read_of[&sel2], bv(2)); // a[7] cannot be both

        assert!(matches!(
            validate(&ctx, &abs, &c, &b),
            Err(Rejection::ReadConflict { .. })
        ));
    }

    /// Ruling R8's fence, and the way that fix could have become an
    /// over-rejection. A read whose index IS written by its own chain is
    /// SHADOWED: it observes the chain's write, not the base, and must NOT be
    /// attributed to the base. Here `select(store(a,5,9), 5) = 9` coexists with
    /// `select(a, 5) = 3`, which is perfectly consistent — `a[5]` is 3 and the
    /// store overwrites it with 9. Attributing the shadowed read to `a` would
    /// invent the pin `a[5] = 9` and fire a spurious `ReadConflict`.
    #[test]
    fn c1_silent_when_a_chain_read_is_shadowed_by_its_own_write() {
        let mut ctx = Context::new();
        let a_s = arr_sort(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", a_s);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let m = uconst(&mut ctx, "m", s8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let shadowed = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        let direct = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, m]).unwrap();
        let atom = ctx.mk_eq(shadowed, direct).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);

        let mut b = FakeBridge::default();
        b.bv.insert(i, bv(5));
        b.bv.insert(e, bv(9));
        b.bv.insert(m, bv(5)); // the SAME index value as the store writes
        b.bv.insert(abs.read_of[&shadowed], bv(9)); // sees the store's write
        b.bv.insert(abs.read_of[&direct], bv(3)); // sees the base, freely

        assert!(validate(&ctx, &abs, &c, &b).is_ok());
    }
}
