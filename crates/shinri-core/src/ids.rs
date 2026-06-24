use std::num::NonZeroU32;

/// Index into `Context.nodes`. 1-based (`NonZeroU32`) so `Option<TermId>` is 4 bytes.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TermId(NonZeroU32);

impl TermId {
    #[inline]
    pub fn new(raw: u32) -> Option<TermId> {
        NonZeroU32::new(raw).map(TermId)
    }
    /// 0-based arena index (`raw - 1`).
    #[inline]
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
    /// Construct from a 0-based arena index.
    #[inline]
    pub(crate) fn from_index(idx: usize) -> TermId {
        TermId(NonZeroU32::new(idx as u32 + 1).expect("term index overflow"))
    }
}

/// Index into `Context.sorts`. 1-based like `TermId`.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SortId(NonZeroU32);

impl SortId {
    #[inline]
    pub fn new(raw: u32) -> Option<SortId> {
        NonZeroU32::new(raw).map(SortId)
    }
    #[inline]
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
    #[inline]
    pub(crate) fn from_index(idx: usize) -> SortId {
        SortId(NonZeroU32::new(idx as u32 + 1).expect("sort index overflow"))
    }
}

macro_rules! u32_id {
    ($name:ident) => {
        #[repr(transparent)]
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        pub struct $name(u32);
        impl $name {
            #[inline]
            pub fn new(raw: u32) -> $name {
                $name(raw)
            }
            #[inline]
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

u32_id!(SymbolId);
u32_id!(RatId);
// Index into `Context.bvs` (the BV literal table), analogous to `RatId`.
u32_id!(BvId);
// Index into `Context.str_lits` (the string literal table), analogous to `BvId`.
u32_id!(StringId);
u32_id!(ClauseId);
u32_id!(Var);

/// A Boolean literal: a `Var` plus a polarity, packed as `var << 1 | sign`.
/// `sign` bit 0 = positive, 1 = negative.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Lit(u32);

impl Lit {
    #[inline]
    pub fn new(var: Var, positive: bool) -> Lit {
        Lit((var.0 << 1) | (!positive as u32))
    }
    #[inline]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }
    #[inline]
    pub fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }
    #[inline]
    pub fn negate(self) -> Lit {
        Lit(self.0 ^ 1)
    }
    /// The raw packed code (`var << 1 | sign`). Lets the SAT layer pack
    /// literals into the clause arena and index watch lists by `code as usize`.
    #[inline]
    pub fn code(self) -> u32 {
        self.0
    }
    /// Reconstruct a literal from its raw packed code.
    #[inline]
    pub fn from_code(code: u32) -> Lit {
        Lit(code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn option_id_is_four_bytes() {
        assert_eq!(size_of::<Option<TermId>>(), 4);
        assert_eq!(size_of::<Option<SortId>>(), 4);
    }

    #[test]
    fn termid_roundtrips_and_rejects_zero() {
        assert!(TermId::new(0).is_none());
        let id = TermId::new(7).unwrap();
        assert_eq!(id.index(), 6); // 1-based NonZero -> 0-based index
    }

    #[test]
    fn lit_packs_var_and_sign() {
        let v = Var::new(5);
        let pos = Lit::new(v, true);
        let neg = Lit::new(v, false);
        assert_eq!(pos.var(), v);
        assert_eq!(neg.var(), v);
        assert!(pos.is_positive());
        assert!(!neg.is_positive());
        assert_eq!(pos.negate(), neg);
        assert_eq!(neg.negate(), pos);
    }

    #[test]
    fn lit_code_roundtrips() {
        let v = Var::new(9);
        let l = Lit::new(v, false);
        assert_eq!(Lit::from_code(l.code()), l);
        assert_eq!(Lit::new(v, true).code() ^ 1, l.code()); // sign bit toggles
        assert_eq!(Lit::from_code(Lit::new(v, true).code()), Lit::new(v, true));
    }
}
