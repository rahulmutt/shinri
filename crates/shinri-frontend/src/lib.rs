//! The neutral SMT-LIB command IR. Constructed by `shinri-parser`, executed by
//! `shinri-solver`; neither depends on the other (design §2, §3.1).

use shinri_core::{SortId, SymbolId, TermId};

/// The value of a `set-option` / `set-info` attribute, kept as raw token text
/// (Phase 1 does not interpret most options).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AttrValue {
    /// No value (e.g. a bare flag), or an opaque token captured verbatim.
    Token(Option<String>),
}

/// One top-level SMT-LIB command, with terms already interned to `TermId`.
/// `#[non_exhaustive]` so Phase-2 commands (BV/array/quantifier) extend it
/// without breaking consumers.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum Command {
    SetLogic(String),
    DeclareSort {
        name: String,
        arity: u32,
    },
    DeclareFun {
        name: String,
        sym: SymbolId,
        params: Vec<SortId>,
        result: SortId,
    },
    /// One `declare-datatype`/`declare-datatypes` command. Carries the declared
    /// sorts by name; the constructor/selector/tester symbols and their roles
    /// live in the `Context` datatype registry.
    DeclareDatatypes {
        sorts: Vec<(String, SortId)>,
    },
    Assert(TermId),
    CheckSat,
    CheckSatAssuming(Vec<TermId>),
    Push(u32),
    Pop(u32),
    GetModel,
    GetValue(Vec<TermId>),
    GetUnsatCore,
    SetOption {
        keyword: String,
        value: AttrValue,
    },
    SetInfo {
        keyword: String,
        value: AttrValue,
    },
    GetInfo(String),
    Echo(String),
    Reset,
    Exit,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructs_and_clones() {
        let c = Command::Push(2);
        assert_eq!(c.clone(), Command::Push(2));
        assert_eq!(
            Command::SetLogic("QF_LRA".into()),
            Command::SetLogic("QF_LRA".into())
        );
    }
}
