//! Var↔atom mapping and the owning-theory classification that drives the
//! Combiner's enum routing (spec §3). Unsupported atoms are refused here so
//! soundness stays existential (spec §9).

use crate::types::Owner;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode, Var};

/// An atom this solver cannot handle exactly (e.g. nonlinear). Refusing it at
/// registration makes the whole query return `unknown` upstream.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Unsupported(pub TermId);

/// Classify a Boolean atom by its top operator and argument sorts. Returns the
/// owning theory, or `Unsupported` for constructs outside QF_UFLRA.
pub fn classify(terms: &Context, atom: TermId) -> Result<Owner, Unsupported> {
    // Reject any nonlinear product anywhere in the atom first (spec §9).
    if contains_nonlinear_mul(terms, atom) {
        return Err(Unsupported(atom));
    }
    // QF_LIA is out of scope this milestone: an LRA simplex solves only the real
    // relaxation, which is unsound for integers. Fence Int-sorted arithmetic to
    // `unknown` (spec §1.1). Real-sorted arithmetic is unaffected.
    if contains_int_arith(terms, atom) {
        return Err(Unsupported(atom));
    }
    match terms.term_node(atom) {
        TermNode::App { op, args, .. } => {
            let children = terms.children(*args);
            match op {
                Op::Builtin(BuiltinOp::Le | BuiltinOp::Lt | BuiltinOp::Ge | BuiltinOp::Gt) => {
                    Ok(Owner::Arith)
                }
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) => {
                    Ok(classify_equality(terms, children))
                }
                // An uninterpreted predicate application is an EUF atom.
                Op::Uninterpreted(_) => Ok(Owner::Euf),
                // Boolean connectives are handled by the SAT layer, not a theory.
                _ => Err(Unsupported(atom)),
            }
        }
        TermNode::Const { .. } => Err(Unsupported(atom)),
    }
}

/// Equality routing: by the argument sort.
///
/// Equalities (`Eq`) are always routed to EUF so the congruence closure can
/// observe them for congruence propagation (x=y → f(x)=f(y)). The solver's
/// `lower()` pass ALSO emits `Le`/`Ge` atoms for Real-sorted equalities so the
/// Arith theory can reason about the bound constraint; those atoms route to
/// `Owner::Arith` separately. This dual-route approach enables QF_UFLRA:
///   EUF handles congruence, Arith handles linear arithmetic, they share terms.
///
/// Disequalities (`Distinct`) whose arguments are of a non-arithmetic sort route
/// to EUF. Real-sorted `Distinct` atoms only reach classify if `lower()` kept
/// them as-is (i.e., an arg contains a function application like f(x)); in that
/// case EUF handles it via diseq assertion. Pure-arith `Distinct` is lowered to
/// `(or Lt Gt)` before reaching here.
///
/// A mix of arith and non-arith argument sorts (rare after purification) → Shared.
fn classify_equality(terms: &Context, args: &[TermId]) -> Owner {
    let int_s = terms.int_sort();
    let real_s = terms.real_sort();
    let is_arith = |t: TermId| {
        let s = terms.sort_of(t);
        s == int_s || s == real_s
    };
    let none_arith = args.iter().all(|&a| !is_arith(a));
    if none_arith {
        Owner::Euf
    } else {
        // All-arith or mixed: route to EUF. For Eq atoms, lower() will have
        // emitted companion Le/Ge atoms that go to Arith separately, so both
        // theories see the constraint. For Distinct atoms that reached here,
        // lower() decided they need EUF (function-application args).
        Owner::Euf
    }
}

/// True if `t` contains a `Mul` whose operands are not all numeric constants.
fn contains_nonlinear_mul(terms: &Context, t: TermId) -> bool {
    match terms.term_node(t) {
        TermNode::Const { .. } => false,
        TermNode::App { op, args, .. } => {
            let children = terms.children(*args);
            if let Op::Builtin(BuiltinOp::Mul) = op {
                let non_const = children
                    .iter()
                    .filter(|&&c| !matches!(terms.term_node(c), TermNode::Const { .. }))
                    .count();
                if non_const >= 2 {
                    return true;
                }
            }
            children.iter().any(|&c| contains_nonlinear_mul(terms, c))
        }
    }
}

/// True if `atom` is an arithmetic relation/equality with an Int-sorted operand.
fn contains_int_arith(terms: &Context, atom: TermId) -> bool {
    let int_s = terms.int_sort();
    if let TermNode::App { op, args, .. } = terms.term_node(atom) {
        let children = terms.children(*args);
        let touches_int = children.iter().any(|&c| terms.sort_of(c) == int_s);
        match op {
            Op::Builtin(BuiltinOp::Le | BuiltinOp::Lt | BuiltinOp::Ge | BuiltinOp::Gt) => {
                return touches_int;
            }
            Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) => {
                return touches_int;
            }
            _ => {}
        }
    }
    false
}

/// `Var`-indexed routing table. Append-only across a solve (atoms are never
/// un-registered on backtrack — spec §6.5).
#[derive(Default)]
pub struct AtomRegistry {
    by_var: Vec<Option<(TermId, Owner)>>,
}

impl AtomRegistry {
    pub fn register(&mut self, v: Var, atom: TermId, owner: Owner) {
        let idx = v.index();
        if idx >= self.by_var.len() {
            self.by_var.resize(idx + 1, None);
        }
        self.by_var[idx] = Some((atom, owner));
    }

    #[inline]
    pub fn owner(&self, v: Var) -> Owner {
        self.by_var
            .get(v.index())
            .and_then(|e| *e)
            .expect("owner() on unregistered var")
            .1
    }

    #[inline]
    pub fn atom(&self, v: Var) -> TermId {
        self.by_var
            .get(v.index())
            .and_then(|e| *e)
            .expect("atom() on unregistered var")
            .0
    }

    #[inline]
    pub fn is_registered(&self, v: Var) -> bool {
        self.by_var.get(v.index()).is_some_and(|e| e.is_some())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Op};

    // Build `(<= x y)` over Real and `(= x y)` etc. via a Context.
    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let sym = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn arith_relations_go_to_arith() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
        assert_eq!(classify(&ctx, le), Ok(Owner::Arith));
    }

    #[test]
    fn uninterpreted_equality_goes_to_euf() {
        let mut ctx = Context::new();
        let s = ctx.declare_sort("U");
        let a = {
            let f = ctx.declare_fun("a", &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let b = {
            let f = ctx.declare_fun("b", &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let eq = ctx.mk_eq(a, b).unwrap();
        assert_eq!(classify(&ctx, eq), Ok(Owner::Euf));
    }

    #[test]
    fn nonlinear_mul_is_refused() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[x, y]).unwrap();
        // An atom *containing* a nonlinear product is unsupported.
        let z = real_var(&mut ctx, "z");
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, z]).unwrap();
        assert_eq!(classify(&ctx, le), Err(Unsupported(le)));
    }

    #[test]
    fn registry_routes_by_var() {
        let mut reg = AtomRegistry::default();
        let v = Var::new(2);
        let atom = TermId::new(5).unwrap();
        reg.register(v, atom, Owner::Euf);
        assert_eq!(reg.owner(v), Owner::Euf);
        assert_eq!(reg.atom(v), atom);
    }

    #[test]
    fn linear_scaling_is_allowed() {
        // 2*x is linear (one constant operand) -> the relation classifies as Arith,
        // NOT refused as nonlinear.
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let two = ctx.mk_numeral(shinri_core::Rational::from_int(2i128.into()), real);
        let two_x = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[two_x, y]).unwrap();
        assert_eq!(classify(&ctx, le), Ok(Owner::Arith));
    }

    #[test]
    fn const_atom_is_refused() {
        // A bare constant term is not a theory atom -> Unsupported.
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let k = ctx.mk_numeral(shinri_core::Rational::from_int(3i128.into()), real);
        assert_eq!(classify(&ctx, k), Err(Unsupported(k)));
    }

    #[test]
    fn int_sorted_arith_is_fenced_to_unsupported() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xi = ctx.declare_fun("xi", &[], int);
        let yi = ctx.declare_fun("yi", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yi), &[]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
        assert_eq!(classify(&ctx, le), Err(Unsupported(le)));
        // Real-sorted still arith.
        let real = ctx.real_sort();
        let xr = ctx.declare_fun("xr", &[], real);
        let yr = ctx.declare_fun("yr", &[], real);
        let xrt = ctx.mk_app(Op::Uninterpreted(xr), &[]).unwrap();
        let yrt = ctx.mk_app(Op::Uninterpreted(yr), &[]).unwrap();
        let ler = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xrt, yrt]).unwrap();
        assert_eq!(classify(&ctx, ler), Ok(Owner::Arith));
    }
}
