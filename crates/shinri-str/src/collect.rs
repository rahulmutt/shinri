use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

pub(crate) fn is_string_sorted(terms: &Context, t: TermId) -> bool {
    matches!(
        terms.sort_node(terms.sort_of(t)),
        shinri_core::SortNode::String
    )
}

/// Record every str.len application and string-sorted subterm into the given sets.
pub fn collect(
    terms: &Context,
    t: TermId,
    len_terms: &mut FxHashSet<TermId>,
    str_terms: &mut FxHashSet<TermId>,
    seen: &mut FxHashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    if is_string_sorted(terms, t) {
        str_terms.insert(t);
    }
    if let TermNode::App { op, args, .. } = terms.term_node(t) {
        if matches!(op, Op::Builtin(BuiltinOp::StrLen)) {
            len_terms.insert(t);
        }
        for k in terms.children(*args).to_vec() {
            collect(terms, k, len_terms, str_terms, seen);
        }
    }
}
