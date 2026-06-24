//! Model construction for the string theory (Task 17).
//!
//! On a SAT result the solver assembles a candidate model; this module fills in
//! `ModelVal::String(...)` for each string-sorted term:
//!
//! - **String literals** get their exact value from the context.
//! - **Already-assigned** terms are skipped (another theory may have set them).
//! - **Free variables** get a word of `len` `FILL` characters, where `len` is
//!   read from the arith model as `ModelVal::Num(r)` for the `(str.len t)` term.
//!   If no length is present, length 0 is assumed (empty string).
//!
//! # Approximation (v1 — per implementation plan)
//!
//! Individual character positions within partially-constrained variables are
//! *not* yet overlaid with constant atoms from the equality-engine normal forms.
//! Instead, free positions are filled uniformly with `FILL` (`'A'`, U+0041).
//! Task 19's witness check (substitute model, re-verify with z3) validates
//! correctness; if a witness failure is caused by a constant char not being
//! pinned, extend `assign` to walk `eq_true` normal forms and overlay constant
//! atoms at their offsets — but only if Task 19 surfaces such a failure.

use shinri_core::{BuiltinOp, Context, Op, TermId};
use shinri_theory::types::ModelVal;
use shinri_theory::{EqualityEngine, ModelBuilder};

/// Default fill character for free (unconstrained) positions in string variables.
const FILL: char = 'A'; // U+0041

/// Read the length of term `t` from the model, via its `(str.len t)` term.
///
/// Builds `(str.len t)`, looks up `m.get(...)` for `ModelVal::Num(r)`.
/// Converts the rational to a non-negative `usize`; clamps negatives to 0.
/// Returns 0 if the length is absent from the model.
pub fn len_of_in_model(terms: &mut Context, m: &ModelBuilder, t: TermId) -> usize {
    let lt = terms
        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[t])
        .expect("str.len application must succeed for a string-sorted term");
    match m.get(lt) {
        Some(ModelVal::Num(r)) => {
            // A str.len value is always a non-negative integer.
            // Extract numerator (denominator is 1 for integers); clamp negatives to 0.
            if r.is_negative() || r.is_zero() {
                0
            } else {
                // r is positive; denom = 1 for integer-valued rationals.
                // numer() returns Integer; use to_i128() -> Option<i128>.
                r.numer()
                    .to_i128()
                    .map(|v| v.max(0) as usize)
                    .unwrap_or(0)
            }
        }
        _ => 0,
    }
}

/// Assign each string term a concrete `ModelVal::String` value.
///
/// - Literal terms → exact string value.
/// - Already assigned → skip.
/// - Free variables → `FILL` repeated `len` times, where `len` comes from the
///   arith model's assignment to `(str.len t)`.
pub fn assign(
    terms: &mut Context,
    _eq: &mut EqualityEngine,
    str_terms: &[TermId],
    m: &mut ModelBuilder,
) {
    for &t in str_terms {
        // Case 1: string literal — use its exact value.
        if let Some(v) = terms.string_const_value(t) {
            let s = v.to_owned();
            m.assign(t, ModelVal::String(s));
            continue;
        }
        // Case 2: already assigned by another theory pass — skip.
        if m.get(t).is_some() {
            continue;
        }
        // Case 3: free variable — fill with FILL to the arith-model length.
        let n = len_of_in_model(terms, m, t);
        let word: String = std::iter::repeat(FILL).take(n).collect();
        m.assign(t, ModelVal::String(word));
    }
}
