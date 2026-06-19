use shinri_core::{ClauseId, Lit};

/// A reference to a clause: an offset into the `ClauseDb` arena (Task 4).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ClauseRef(pub u32);

impl ClauseRef {
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

const HEADER_WORDS: usize = 3;
const LEARNT_BIT: u32 = 1 << 31;
const LBD_MASK: u32 = 0x7FFF_FFFF;

/// The clause database: one flat `u32` arena. Binary clauses are NOT stored
/// here — they live implicitly in the watch lists (Task 6).
pub struct ClauseDb {
    arena: Vec<u32>,
    /// `id_to_ref[id.index()]` = the live `ClauseRef` for stable `ClauseId`.
    /// Updated on relocation (Task 11) so `ClauseId` stays stable for proofs.
    id_to_ref: Vec<ClauseRef>,
}

impl Default for ClauseDb {
    fn default() -> Self {
        ClauseDb::new()
    }
}

impl ClauseDb {
    pub fn new() -> ClauseDb {
        ClauseDb { arena: Vec::new(), id_to_ref: Vec::new() }
    }

    pub fn add_clause(&mut self, lits: &[Lit], learnt: bool) -> (ClauseId, ClauseRef) {
        let off = self.arena.len() as u32;
        let r = ClauseRef(off);
        let id = ClauseId::new(self.id_to_ref.len() as u32);
        self.id_to_ref.push(r);

        self.arena.push(id.index() as u32); // [id]
        self.arena.push(if learnt { LEARNT_BIT } else { 0 }); // [meta]
        self.arena.push(lits.len() as u32); // [len]
        for &l in lits {
            self.arena.push(l.code());
        }
        (id, r)
    }

    #[inline]
    fn off(&self, r: ClauseRef) -> usize {
        r.index()
    }

    #[inline]
    pub fn len_of(&self, r: ClauseRef) -> usize {
        self.arena[self.off(r) + 2] as usize
    }

    #[inline]
    pub fn lits(&self, r: ClauseRef) -> &[Lit] {
        let off = self.off(r);
        let len = self.arena[off + 2] as usize;
        let start = off + HEADER_WORDS;
        let codes = &self.arena[start..start + len];
        // SAFETY: `Lit` is `#[repr(transparent)]` over `u32` (verified in
        // shinri-core), so a slice of literal codes is layout-identical to a
        // slice of `Lit`. This is a zero-copy view, not a transmute of owned
        // data. The single justified `unsafe` block in the clause module.
        unsafe { std::slice::from_raw_parts(codes.as_ptr() as *const Lit, len) }
    }

    #[inline]
    pub fn is_learnt(&self, r: ClauseRef) -> bool {
        self.arena[self.off(r) + 1] & LEARNT_BIT != 0
    }

    #[inline]
    pub fn lbd(&self, r: ClauseRef) -> u32 {
        self.arena[self.off(r) + 1] & LBD_MASK
    }

    #[inline]
    pub fn set_lbd(&mut self, r: ClauseRef, lbd: u32) {
        let off = self.off(r);
        let learnt = self.arena[off + 1] & LEARNT_BIT;
        self.arena[off + 1] = learnt | (lbd & LBD_MASK);
    }

    #[inline]
    pub fn clause_id(&self, r: ClauseRef) -> ClauseId {
        ClauseId::new(self.arena[self.off(r)])
    }

    #[inline]
    pub fn ref_of(&self, id: ClauseId) -> ClauseRef {
        self.id_to_ref[id.index()]
    }

    #[inline]
    pub fn num_clauses(&self) -> usize {
        self.id_to_ref.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Var;

    fn lit(n: u32, pos: bool) -> Lit {
        Lit::new(Var::new(n), pos)
    }

    #[test]
    fn add_then_read_back_lits_flags_and_stable_id() {
        let mut db = ClauseDb::new();
        let ls = [lit(0, true), lit(1, false), lit(2, true)];
        let (id0, r0) = db.add_clause(&ls, false);
        let (id1, r1) = db.add_clause(&[lit(3, true), lit(4, true)], true);

        assert_eq!(db.lits(r0), &ls);
        assert_eq!(db.len_of(r0), 3);
        assert_eq!(db.is_learnt(r0), false);
        assert_eq!(db.is_learnt(r1), true);

        db.set_lbd(r1, 2);
        assert_eq!(db.lbd(r1), 2);

        // Stable ids map to current refs.
        assert_eq!(db.clause_id(r0), id0);
        assert_eq!(db.ref_of(id0), r0);
        assert_eq!(db.ref_of(id1), r1);
        assert_eq!(db.num_clauses(), 2);
    }
}
