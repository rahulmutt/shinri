//! Canonical linear combinations and normalised atoms.
//!
//! `LinComb` is a sorted, zero-free vec of `(ArithVar, Rational)` pairs.
//! `Rel` records the inequality direction after normalisation (Ge/Gt are
//! converted to Le/Lt by negating the combination).
//! `Normalized` bundles a `LinComb` with its relation and right-hand-side
//! constant.
//!
//! The functions `normalize_atom` / `linearize` / `canonicalize` are added in
//! Task 4; this file only provides the type definitions so that `vars.rs` can
//! compile.

use crate::vars::{ArithVar, VarStore};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_num::{Integer, Rational};

/// Canonical linear combination: sorted ascending by `ArithVar`, no zero
/// coefficients, constant term moved to `rhs` during normalisation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LinComb(pub Vec<(ArithVar, Rational)>);

/// The relation after normalisation.  `Ge`/`Gt` are mapped to `Le`/`Lt` by
/// negating the combination, so only these three appear in `Normalized`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rel {
    Le,
    Lt,
    Eq,
}

/// A normalised linear atom: `comb rel rhs`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Normalized {
    pub comb: LinComb,
    pub rel: Rel,
    pub rhs: Rational,
}

// ---------------------------------------------------------------------------
// Manual Hash for LinComb
// ---------------------------------------------------------------------------
//
// `Rational` does not derive `Hash` (its internal `Repr` is private and uses
// `Integer`, which also has no `Hash` impl).  We synthesise a hash by
// serialising each coefficient as its canonical `(numer, denom)` pair of
// `Integer`s; each `Integer` is in turn serialised as `(is_negative, digits)`
// where `digits` is a little-endian sequence of `u64` chunks extracted via
// repeated `div_rem`.  This is consistent with `PartialEq` because the
// representation is canonical.
//
// In practice every LRA coefficient fits in i128 (`Integer::to_i128()` is
// `Some`), so the loop body runs at most twice.

fn hash_integer<H: std::hash::Hasher>(n: Integer, state: &mut H) {
    use std::hash::Hash;
    Hash::hash(&n.is_negative(), state);
    let mut remaining = n.abs();
    // Fix 2: assert the invariant that abs() is non-negative so a future edit
    // removing `.abs()` can't silently produce a negative remainder.
    debug_assert!(!remaining.is_negative());
    // Fix 3: 2^64 = 18446744073709551616 fits in i128 (max ~1.7e38); avoids runtime add.
    // Fix 1: collect chunks into a Vec first so we can hash their count as a
    // length prefix, making each integer's encoding self-delimiting and keeping
    // the numer/denom boundary unambiguous for multi-limb Big integers.
    let chunk = Integer::from((u64::MAX as i128) + 1); // 2^64
    let mut chunks: Vec<u64> = Vec::new();
    loop {
        let (q, r) = remaining.div_rem(&chunk);
        // r is always in [0, 2^64) because chunk = 2^64
        let digit = r.to_i128().expect("remainder < 2^64 always fits i128") as u64;
        chunks.push(digit);
        if q.is_zero() {
            break;
        }
        remaining = q;
    }
    // Hash the length prefix before the digits so each integer's encoding is
    // self-delimiting (prefix-free).
    Hash::hash(&chunks.len(), state);
    for digit in &chunks {
        Hash::hash(digit, state);
    }
}

fn hash_rational<H: std::hash::Hasher>(r: &Rational, state: &mut H) {
    hash_integer(r.numer(), state);
    hash_integer(r.denom(), state);
}

impl std::hash::Hash for LinComb {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        use std::hash::Hash;
        Hash::hash(&self.0.len(), state);
        for (var, coeff) in &self.0 {
            Hash::hash(var, state);
            hash_rational(coeff, state);
        }
    }
}

// ---------------------------------------------------------------------------
// Normalization functions
// ---------------------------------------------------------------------------

/// Accumulate `t` into (variable part, constant part). Assumes linear, Real input.
fn linearize(
    terms: &Context,
    vars: &mut VarStore,
    t: TermId,
) -> (Vec<(ArithVar, Rational)>, Rational) {
    if let Some(r) = terms.numeral_value(t) {
        return (Vec::new(), r.clone());
    }
    match terms.term_node(t) {
        TermNode::App { op, args, .. } => {
            let kids: Vec<TermId> = terms.children(*args).to_vec();
            match op {
                Op::Builtin(BuiltinOp::Add) => {
                    let mut acc = (Vec::new(), Rational::zero());
                    for k in kids {
                        let (v, c) = linearize(terms, vars, k);
                        acc.0.extend(v);
                        acc.1 = acc.1 + c;
                    }
                    acc
                }
                Op::Builtin(BuiltinOp::Sub) => {
                    // (- a b ...) = a - b - ...   (binary in practice)
                    let mut it = kids.into_iter();
                    let (mut v, mut c) = linearize(terms, vars, it.next().unwrap());
                    for k in it {
                        let (vk, ck) = linearize(terms, vars, k);
                        v.extend(vk.into_iter().map(|(x, q)| (x, -q)));
                        c = c - ck;
                    }
                    (v, c)
                }
                Op::Builtin(BuiltinOp::Neg) => {
                    let (v, c) = linearize(terms, vars, kids[0]);
                    (v.into_iter().map(|(x, q)| (x, -q)).collect(), -c)
                }
                Op::Builtin(BuiltinOp::Mul) => {
                    // Linear: exactly one non-constant factor (classify rejected the rest).
                    let mut coeff = Rational::one();
                    let mut nonconst: Option<TermId> = None;
                    for k in &kids {
                        match terms.numeral_value(*k) {
                            Some(r) => coeff = coeff * r.clone(),
                            None => {
                                debug_assert!(nonconst.is_none(), "nonlinear reached normalize");
                                nonconst = Some(*k);
                            }
                        }
                    }
                    match nonconst {
                        None => (Vec::new(), coeff), // all-constant product
                        Some(inner) => {
                            let (v, c) = linearize(terms, vars, inner);
                            (
                                v.into_iter().map(|(x, q)| (x, q * coeff.clone())).collect(),
                                c * coeff,
                            )
                        }
                    }
                }
                Op::Uninterpreted(_) => {
                    // A leaf arithmetic variable (Real-sorted constant symbol).
                    (
                        vec![(vars.problem_var(t), Rational::one())],
                        Rational::zero(),
                    )
                }
                _ => {
                    debug_assert!(false, "unexpected op in arith term");
                    (
                        vec![(vars.problem_var(t), Rational::one())],
                        Rational::zero(),
                    )
                }
            }
        }
        TermNode::Const { .. } => {
            // Bool const cannot appear in an arith term; numerals handled above.
            (Vec::new(), Rational::zero())
        }
    }
}

/// Collapse a raw variable list into a canonical `LinComb` (sum duplicates,
/// drop zero coeffs, sort by var).
fn canonicalize(mut raw: Vec<(ArithVar, Rational)>) -> LinComb {
    raw.sort_by_key(|p| p.0);
    let mut out: Vec<(ArithVar, Rational)> = Vec::with_capacity(raw.len());
    for (v, c) in raw {
        if let Some(last) = out.last_mut() {
            if last.0 == v {
                last.1 = last.1.clone() + c;
                continue;
            }
        }
        out.push((v, c));
    }
    out.retain(|(_, c)| !c.is_zero());
    LinComb(out)
}

/// `atom` is `(rel lhs rhs)`. Produce `comb (rel') rhs'` with Ge/Gt flipped to Le/Lt.
pub fn normalize_atom(terms: &Context, vars: &mut VarStore, atom: TermId) -> Normalized {
    let (op, kids) = match terms.term_node(atom) {
        TermNode::App { op, args, .. } => (*op, terms.children(*args).to_vec()),
        _ => unreachable!("non-app arith atom"),
    };
    debug_assert_eq!(kids.len(), 2, "binary arith relation expected");
    // lhs - rhs as (vars, const).
    let (lv, lc) = linearize(terms, vars, kids[0]);
    let (rv, rc) = linearize(terms, vars, kids[1]);
    let mut both = lv;
    both.extend(rv.into_iter().map(|(x, q)| (x, -q)));
    // (lhs - rhs) = comb_vars + comb_const  =>  comb_vars (rel) -comb_const
    let comb_const = lc - rc;
    let comb = canonicalize(both);
    let rhs = -comb_const;
    match op {
        Op::Builtin(BuiltinOp::Le) => Normalized {
            comb,
            rel: Rel::Le,
            rhs,
        },
        Op::Builtin(BuiltinOp::Lt) => Normalized {
            comb,
            rel: Rel::Lt,
            rhs,
        },
        Op::Builtin(BuiltinOp::Ge) => Normalized {
            comb: negate(comb),
            rel: Rel::Le,
            rhs: -rhs,
        },
        Op::Builtin(BuiltinOp::Gt) => Normalized {
            comb: negate(comb),
            rel: Rel::Lt,
            rhs: -rhs,
        },
        Op::Builtin(BuiltinOp::Eq) => Normalized {
            comb,
            rel: Rel::Eq,
            rhs,
        },
        _ => unreachable!("normalize_atom on non-relation"),
    }
}

fn negate(c: LinComb) -> LinComb {
    LinComb(c.0.into_iter().map(|(v, q)| (v, -q)).collect())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let sym = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }
    fn num(ctx: &mut Context, n: i128) -> TermId {
        let real = ctx.real_sort();
        ctx.mk_numeral(Rational::from_int(n.into()), real)
    }

    #[test]
    fn le_with_constant_folds_to_rhs() {
        // (<= (+ x 1) 3)  ==>  comb {x:1}, Le, rhs 2
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let one = num(&mut ctx, 1);
        let three = num(&mut ctx, 3);
        let lhs = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, one]).unwrap();
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[lhs, three])
            .unwrap();
        let mut vs = VarStore::default();
        let n = normalize_atom(&ctx, &mut vs, le);
        let xv = vs.problem_var(x);
        assert_eq!(n.rel, Rel::Le);
        assert_eq!(n.comb.0, vec![(xv, Rational::one())]);
        assert_eq!(n.rhs, Rational::from_int(2i128.into()));
    }

    #[test]
    fn ge_is_flipped_to_le() {
        // (>= x 5)  ==>  comb {x:-1}, Le, rhs -5
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let five = num(&mut ctx, 5);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, five]).unwrap();
        let mut vs = VarStore::default();
        let n = normalize_atom(&ctx, &mut vs, ge);
        let xv = vs.problem_var(x);
        assert_eq!(n.rel, Rel::Le);
        assert_eq!(n.comb.0, vec![(xv, -Rational::one())]);
        assert_eq!(n.rhs, Rational::from_int((-5i128).into()));
    }

    #[test]
    fn sub_negates_second_term() {
        // (<= (- x y) 1)  ==>  comb {x:1, y:-1}, Le, rhs 1
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let one = num(&mut ctx, 1);
        let sub = ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[x, y]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[sub, one]).unwrap();
        let mut vs = VarStore::default();
        let n = normalize_atom(&ctx, &mut vs, le);
        let xv = vs.problem_var(x);
        let yv = vs.problem_var(y);
        assert_eq!(n.rel, Rel::Le);
        let mut got = n.comb.0.clone();
        got.sort_by_key(|p| p.0);
        assert_eq!(got, vec![(xv, Rational::one()), (yv, -Rational::one())]);
        assert_eq!(n.rhs, Rational::one());
    }

    #[test]
    fn neg_inverts_coefficients() {
        // (<= (- x) 0)  i.e. Neg(x)  ==>  comb {x:-1}, Le, rhs 0
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let zero = num(&mut ctx, 0);
        let negx = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[x]).unwrap();
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[negx, zero])
            .unwrap();
        let mut vs = VarStore::default();
        let n = normalize_atom(&ctx, &mut vs, le);
        let xv = vs.problem_var(x);
        assert_eq!(n.comb.0, vec![(xv, -Rational::one())]);
        assert_eq!(n.rel, Rel::Le);
        assert_eq!(n.rhs, Rational::zero());
    }

    #[test]
    fn eq_subtracts_sides() {
        // (= (* 2 x) y)  ==>  comb {x:2, y:-1}, Eq, rhs 0
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let two = num(&mut ctx, 2);
        let twox = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[twox, y]).unwrap();
        let mut vs = VarStore::default();
        let n = normalize_atom(&ctx, &mut vs, eq);
        let xv = vs.problem_var(x);
        let yv = vs.problem_var(y);
        assert_eq!(n.rel, Rel::Eq);
        let mut got = n.comb.0.clone();
        got.sort_by_key(|p| p.0);
        assert_eq!(
            got,
            vec![
                (xv, Rational::from_int(2i128.into())),
                (yv, -Rational::one())
            ]
        );
        assert_eq!(n.rhs, Rational::zero());
    }
}
