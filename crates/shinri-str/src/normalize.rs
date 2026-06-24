use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::ENodeId;
use shinri_theory::EqualityEngine;

/// Return the representative `TermId` of `t`'s equivalence class.
///
/// The `EqualityEngine` maintains a `TermId → ENodeId` map (via `intern`) and a
/// union-find over `ENodeId`s (via `find`), but has no reverse `ENodeId → TermId`
/// map.  We thread our own `node_of: FxHashMap<ENodeId, TermId>` — one entry per
/// distinct interned term — so we can resolve a representative node back to a term.
///
/// If `t` was never interned, it is its own representative.
pub(crate) fn rep(
    eq: &mut EqualityEngine,
    node_of: &mut FxHashMap<ENodeId, TermId>,
    t: TermId,
) -> TermId {
    let n = eq.intern(t);
    node_of.entry(n).or_insert(t);
    let r = eq.find(n);
    // If the representative node was never explicitly inserted (e.g. it was
    // created by a merge that happened after our intern), it defaults to `t`
    // itself — which is a sound conservative choice: two terms in the same class
    // but neither was inserted here will each keep their own value, and literal
    // folding will still fold them once the class rep appears.
    *node_of.get(&r).unwrap_or(&t)
}

/// Flatten `str.++` into a sequence; map each atom to its class representative;
/// fold adjacent string-literal atoms; drop empty-string `""` atoms.
pub fn normal_form(terms: &mut Context, eq: &mut EqualityEngine, t: TermId) -> Vec<TermId> {
    let mut flat = Vec::new();
    flatten(terms, t, &mut flat);

    // Build a local node_of map so we can translate ENodeId reps back to TermIds.
    let mut node_of: FxHashMap<ENodeId, TermId> = FxHashMap::default();
    // Pre-populate with each atom we flattened, in order (so the first term
    // interned at a given node "owns" that node slot for rep resolution).
    for &a in &flat {
        let n = eq.intern(a);
        node_of.entry(n).or_insert(a);
    }

    let mut out: Vec<TermId> = Vec::new();
    for a in flat {
        let r = rep(eq, &mut node_of, a);
        if let Some(s) = terms.string_const_value(r) {
            let s = s.to_owned();
            if s.is_empty() {
                continue; // drop ""
            }
            // Try to fold into the preceding literal.
            if let Some(&last) = out.last() {
                if let Some(ls) = terms.string_const_value(last) {
                    let merged = format!("{ls}{s}");
                    let m = terms.mk_string_const(&merged);
                    *out.last_mut().unwrap() = m;
                    continue;
                }
            }
        }
        out.push(r);
    }
    out
}

/// Recursively flatten a (possibly nested) `str.++` into its atom leaves.
fn flatten(terms: &Context, t: TermId, out: &mut Vec<TermId>) {
    match terms.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => {
            let kids: Vec<TermId> = terms.children(*args).to_vec();
            for k in kids {
                flatten(terms, k, out);
            }
        }
        _ => out.push(t),
    }
}

#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_theory::EqualityEngine;

    use crate::normalize::normal_form;

    #[test]
    fn flattens_nested_concat_and_folds_literals() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let ab = ctx.mk_string_const("ab");
        let cd = ctx.mk_string_const("cd");
        let inner = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ab, cd])
            .unwrap();
        let outer = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, inner])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let nf = normal_form(&mut ctx, &mut eq, outer);
        // x ++ "ab" ++ "cd"  ==  x ++ "abcd"  (literals folded)
        assert_eq!(nf.len(), 2);
        assert_eq!(ctx.string_const_value(nf[1]), Some("abcd"));
    }
}
