use rustc_hash::FxHashMap;
use shinri_core::TermId;
use shinri_num::Rational;
use shinri_theory::types::ModelVal;

/// The outcome of `check_sat`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SolveOutcome {
    Sat,
    Unsat,
    Unknown,
}

/// A satisfying assignment, keyed by term.
#[derive(Default, Debug)]
pub struct Model {
    pub(crate) values: FxHashMap<TermId, ModelVal>,
}

impl Model {
    pub fn get(&self, t: TermId) -> Option<&ModelVal> {
        self.values.get(&t)
    }
}

/// Format a `Rational` as SMT-LIB: `n` if integral, else `(/ n d)`; negatives
/// as `(- …)`.
pub(crate) fn format_rational(r: &Rational) -> String {
    let n = r.numer();
    let d = r.denom();
    if d == shinri_num::Integer::one() {
        if n.is_negative() {
            format!("(- {})", n.abs())
        } else {
            n.to_string()
        }
    } else if n.is_negative() {
        format!("(- (/ {} {}))", n.abs(), d)
    } else {
        format!("(/ {n} {d})")
    }
}

/// Format a single `ModelVal` as SMT-LIB text.
pub(crate) fn format_modelval(v: &ModelVal) -> String {
    match v {
        ModelVal::Bool(b) => {
            if *b {
                "true".into()
            } else {
                "false".into()
            }
        }
        ModelVal::Num(r) => format_rational(r),
        ModelVal::Elem(_, idx) => format!("@elem{idx}"),
    }
}
