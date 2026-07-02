use crate::ids::SymbolId;
use rustc_hash::FxHashMap;

/// Interns symbol text to a `SymbolId` and back. Equal text always yields the
/// same id (maximal sharing); SipHash is never used (uses `FxHashMap`).
#[derive(Clone, Default)]
pub struct StringInterner {
    map: FxHashMap<Box<str>, SymbolId>,
    texts: Vec<Box<str>>,
}

impl StringInterner {
    pub fn intern(&mut self, text: &str) -> SymbolId {
        if let Some(&id) = self.map.get(text) {
            return id;
        }
        let id = SymbolId::new(self.texts.len() as u32);
        let boxed: Box<str> = text.into();
        self.texts.push(boxed.clone());
        self.map.insert(boxed, id);
        id
    }

    pub fn resolve(&self, id: SymbolId) -> &str {
        &self.texts[id.index()]
    }

    /// Look up already-interned text without interning it.
    pub fn lookup(&self, text: &str) -> Option<SymbolId> {
        self.map.get(text).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns_idempotently() {
        let mut si = StringInterner::default();
        let a = si.intern("foo");
        let b = si.intern("bar");
        let a2 = si.intern("foo");
        assert_eq!(a, a2);
        assert_ne!(a, b);
        assert_eq!(si.resolve(a), "foo");
        assert_eq!(si.resolve(b), "bar");
    }

    #[test]
    fn lookup_finds_interned_and_misses_unknown() {
        let mut i = StringInterner::default();
        let id = i.intern("foo");
        assert_eq!(i.lookup("foo"), Some(id));
        assert_eq!(i.lookup("bar"), None);
    }
}
