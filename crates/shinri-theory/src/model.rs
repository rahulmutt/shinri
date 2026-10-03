//! Combined model assembly (spec §7.3). The skeleton (this task) is the storage
//! map; the cross-theory assembly + self-check live in the Combiner (Task 14).

use crate::types::ModelVal;
use rustc_hash::FxHashMap;
use shinri_core::TermId;
use shinri_core::{Integer, Rational};

/// Each theory writes its term values here; the Combiner reconciles them.
#[derive(Default)]
pub struct ModelBuilder {
    values: FxHashMap<TermId, ModelVal>,
    /// Slice 57: set by a theory whose values the solver must confirm with
    /// the strict model gate (every assertion definitely true).
    strict_check: bool,
}

impl ModelBuilder {
    #[inline]
    pub fn assign(&mut self, t: TermId, v: ModelVal) {
        self.values.insert(t, v);
    }
    #[inline]
    pub fn get(&self, t: TermId) -> Option<&ModelVal> {
        self.values.get(&t)
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Slice 57: ask the solver to confirm this model with the strict gate.
    #[inline]
    pub fn require_strict_check(&mut self) {
        self.strict_check = true;
    }
    /// Slice 57: whether some theory asked for the strict gate.
    #[inline]
    pub fn strict_check_required(&self) -> bool {
        self.strict_check
    }

    /// First term that `self` and `other` assign different values to, if any.
    pub fn merge_check(&self, other: &ModelBuilder) -> Option<TermId> {
        for (t, v) in self.values.iter() {
            if let Some(ov) = other.values.get(t) {
                if v != ov {
                    return Some(*t);
                }
            }
        }
        None
    }

    /// Fold another builder's assignments into this one (other wins ties; the
    /// caller has already verified agreement via `merge_check`). The strict
    /// flag is kept if either builder set it.
    pub fn absorb(&mut self, other: ModelBuilder) {
        let ModelBuilder {
            values,
            strict_check,
        } = other;
        for (t, v) in values {
            self.values.insert(t, v);
        }
        self.strict_check |= strict_check;
    }

    /// Iterate all assigned `(TermId, ModelVal)` pairs.
    pub fn iter(&self) -> impl Iterator<Item = (shinri_core::TermId, crate::types::ModelVal)> + '_ {
        self.values.iter().map(|(t, v)| (*t, v.clone()))
    }
}

/// Format a `Rational` as SMT-LIB: `n` if integral, else `(/ n d)`; negatives
/// as `(- …)`.
pub fn format_rational(r: &Rational) -> String {
    let n = r.numer();
    let d = r.denom();
    if d == Integer::one() {
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

/// Format an `Integer` as fixed-width hexadecimal with exactly `digits` hex
/// digits (zero-padded, no prefix).
fn format_hex_fixed(val: &Integer, digits: usize) -> String {
    // Extract hex digits using repeated division by 16.
    let sixteen = Integer::from(16u64);
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

/// Format an `Integer` as a binary string with exactly `width` bits (MSB first,
/// zero-padded).
fn format_bin_fixed(val: &Integer, width: u32) -> String {
    let two = Integer::from(2u64);
    let mut remaining = val.clone();
    let mut bits: Vec<u8> = Vec::with_capacity(width as usize);
    for _ in 0..width {
        let (q, r) = remaining.div_rem(&two);
        bits.push(r.to_i128().unwrap_or(0) as u8);
        remaining = q;
    }
    // bits is LSB-first; reverse to get MSB-first.
    bits.reverse();
    bits.iter()
        .map(|&b| if b == 1 { '1' } else { '0' })
        .collect()
}

/// Format a single `ModelVal` as SMT-LIB text.
pub fn format_modelval(v: &ModelVal) -> String {
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
        ModelVal::String(s) => shinri_core::smtlib_string::encode_literal(s),
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
        ModelVal::Float { eb, sb, bits } => {
            // Split bits MSB→LSB into sign(1) | exp(eb) | trailing-sig(sb-1).
            let two = Integer::from(2u64);
            // sign = top bit; exp = next eb bits; sig = low sb-1 bits.
            // Extract low (sb-1) bits.
            let mut modulus = Integer::one();
            for _ in 0..(sb - 1) {
                modulus *= two.clone();
            }
            let sig = bits.div_rem(&modulus).1;
            // shift right by (sb-1) to get exp|sign
            let mut hi = bits.clone();
            for _ in 0..(sb - 1) {
                hi = hi.div_rem(&two).0;
            }
            let mut exp_mod = Integer::one();
            for _ in 0..*eb {
                exp_mod *= two.clone();
            }
            let exp = hi.div_rem(&exp_mod).1;
            let mut sign = hi.clone();
            for _ in 0..*eb {
                sign = sign.div_rem(&two).0;
            }
            format!(
                "(fp #b{} #b{} #b{})",
                format_bin_fixed(&sign, 1),
                format_bin_fixed(&exp, *eb),
                format_bin_fixed(&sig, sb - 1),
            )
        }
        ModelVal::Rm(rm) => {
            use shinri_core::RoundingMode::*;
            match rm {
                Rne => "RNE",
                Rna => "RNA",
                Rtp => "RTP",
                Rtn => "RTN",
                Rtz => "RTZ",
            }
            .to_string()
        }
        ModelVal::Datatype(s) => s.clone(),
    }
}

#[cfg(test)]
mod format_tests {
    use super::*;

    #[test]
    fn format_string_modelval_escapes_quotes() {
        assert_eq!(format_modelval(&ModelVal::String("ab".into())), "\"ab\"");
        assert_eq!(
            format_modelval(&ModelVal::String("a\"b".into())),
            "\"a\"\"b\""
        );
        assert_eq!(
            format_modelval(&ModelVal::String("\n\\\u{0}".into())),
            r#""\u{a}\u{5c}\u{0}""#
        );
    }

    #[test]
    fn format_float_modelval_as_fp_triple() {
        // Float32 +zero: sign 0, exp 00000000, sig 0*23
        let pz = ModelVal::Float {
            eb: 8,
            sb: 24,
            bits: Integer::from(0u64),
        };
        assert_eq!(
            format_modelval(&pz),
            "(fp #b0 #b00000000 #b00000000000000000000000)"
        );
        // Float32 -0: sign bit set (2^31)
        let nz = ModelVal::Float {
            eb: 8,
            sb: 24,
            bits: Integer::from(1u64 << 31),
        };
        assert_eq!(
            format_modelval(&nz),
            "(fp #b1 #b00000000 #b00000000000000000000000)"
        );
        // Float32 +inf = 0x7F800000: sign 0, exp 11111111, sig 0
        let inf = ModelVal::Float {
            eb: 8,
            sb: 24,
            bits: Integer::from(0x7F80_0000u64),
        };
        assert_eq!(
            format_modelval(&inf),
            "(fp #b0 #b11111111 #b00000000000000000000000)"
        );
    }

    #[test]
    fn format_rational_renders_integral_negative_and_fraction() {
        assert_eq!(format_rational(&Rational::from_int(3i128.into())), "3");
        assert_eq!(
            format_rational(&Rational::from_int((-3i128).into())),
            "(- 3)"
        );
    }
}

#[cfg(test)]
mod strict_check_tests {
    use super::*;

    #[test]
    fn strict_check_defaults_off_and_survives_absorb() {
        let mut a = ModelBuilder::default();
        assert!(!a.strict_check_required());
        let mut b = ModelBuilder::default();
        b.require_strict_check();
        assert!(b.strict_check_required());
        a.absorb(b);
        assert!(a.strict_check_required(), "absorb must keep the flag");
    }
}
