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

/// Format a `shinri_num::Integer` as fixed-width hexadecimal with exactly
/// `digits` hex digits (zero-padded, no prefix).
fn format_hex_fixed(val: &shinri_num::Integer, digits: usize) -> String {
    // Extract hex digits using repeated division by 16.
    let sixteen = shinri_num::Integer::from(16u64);
    let mut remaining = val.clone();
    let mut nibbles: Vec<u8> = Vec::with_capacity(digits);
    for _ in 0..digits {
        let (q, r) = remaining.div_rem(&sixteen);
        // r is in [0,15]; extract as u8 via i128.
        let nibble = r.to_i128().unwrap_or(0) as u8;
        nibbles.push(nibble);
        remaining = q;
    }
    // nibbles is LSB-first; reverse to get MSB-first.
    nibbles.reverse();
    nibbles
        .iter()
        .map(|&n| format!("{:x}", n))
        .collect::<String>()
}

/// Format a `shinri_num::Integer` as a binary string with exactly `width` bits
/// (MSB first, zero-padded).
fn format_bin_fixed(val: &shinri_num::Integer, width: u32) -> String {
    let two = shinri_num::Integer::from(2u64);
    let mut remaining = val.clone();
    let mut bits: Vec<u8> = Vec::with_capacity(width as usize);
    for _ in 0..width {
        let (q, r) = remaining.div_rem(&two);
        bits.push(r.to_i128().unwrap_or(0) as u8);
        remaining = q;
    }
    // bits is LSB-first; reverse to get MSB-first.
    bits.reverse();
    bits.iter().map(|&b| if b == 1 { '1' } else { '0' }).collect()
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
        ModelVal::BitVec(width, val) => {
            if width % 4 == 0 {
                // Format as #x with width/4 hex digits.
                let digits = (width / 4) as usize;
                format!("#x{}", format_hex_fixed(val, digits))
            } else {
                // Format as #b with width binary digits (MSB first).
                format!("#b{}", format_bin_fixed(val, *width))
            }
        }
    }
}
