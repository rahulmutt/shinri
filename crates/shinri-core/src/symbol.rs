use crate::ids::SymbolId;
use rustc_hash::FxHashMap;

/// Interns symbol text to a `SymbolId` and back. Equal text always yields the
/// same id (maximal sharing); SipHash is never used (uses `FxHashMap`).
#[derive(Default)]
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
}
