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

use shinri_num::{Integer, Rational};

use crate::vars::ArithVar;

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
    let chunk = Integer::from(u64::MAX as i128) + Integer::one();
    loop {
        let (q, r) = remaining.div_rem(&chunk);
        // r is always in [0, 2^64) because chunk = 2^64
        let digit = r.to_i128().expect("remainder < 2^64 always fits i128") as u64;
        Hash::hash(&digit, state);
        if q.is_zero() {
            break;
        }
        remaining = q;
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
