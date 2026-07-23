//! Var↔atom mapping and the owning-theory classification that drives the
//! Combiner's enum routing (spec §3). Unsupported atoms are refused here so
//! soundness stays existential (spec §9).

use crate::types::Owner;
use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, DtRole, Op, SortId, SortNode, TermId, TermNode, Var};

/// An atom this solver cannot handle exactly (e.g. nonlinear). Refusing it at
/// registration makes the whole query return `unknown` upstream.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Unsupported(pub TermId);

/// Classify a Boolean atom by its top operator and argument sorts. Returns the
/// owning theory, or `Unsupported` for constructs outside QF_UFLRA/QF_LIA.
pub fn classify(terms: &Context, atom: TermId) -> Result<Owner, Unsupported> {
    // Reject atoms not interned in this context (e.g. synthetic split TermIds
    // from a sub-theory that are not real terms). The defensive caller uses
    // `unwrap_or(Owner::Arith)` in such cases.
    if !terms.contains_term(atom) {
        return Err(Unsupported(atom));
    }
    // Reject any nonlinear product anywhere in the atom first (spec §9).
    if contains_nonlinear_mul(terms, atom) {
        return Err(Unsupported(atom));
    }
    // Extensionality fence: array-to-array (dis)equality is out of scope.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
        args,
        ..
    } = terms.term_node(atom)
    {
        if terms
            .children(*args)
            .iter()
            .any(|&c| is_array_sorted(terms, c))
        {
            return Err(Unsupported(atom));
        }
    }
    // QF_ALIA fence: arrays over arith index/element sorts are out of scope.
    if array_touches_arith(terms, atom) {
        return Err(Unsupported(atom));
    }
    // QF_AX: any remaining atom mentioning select/store is owned by Arrays
    // (EUF still interns the terms for congruence — see the Owner::Arrays
    // routing in the Combiner).
    if contains_array_op(terms, atom) {
        return Ok(Owner::Arrays);
    }
    // String fence: an uninterpreted function (arity >= 1) applied to or
    // returning a String-sorted term is out of scope for QF_S core v1.
    if string_under_uf(terms, atom) {
        return Err(Unsupported(atom));
    }
    // String routing: a (dis)equality whose arguments are String-sorted belongs
    // to the String theory.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
        args,
        ..
    } = terms.term_node(atom)
    {
        if terms
            .children(*args)
            .iter()
            .any(|&c| is_string_sorted(terms, c))
        {
            return Ok(Owner::String);
        }
    }
    // String routing (slice 21): a `str.in_re` membership atom belongs to the
    // String theory. Routing is unconditional — the solver-seam fence
    // (`has_unsupported_regex`) guarantees any membership that survives to SAT
    // is engine-eligible (constant regex side, in-alphabet string side), and
    // engine-minted membership atoms are eligible by construction.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrInRe),
        ..
    } = terms.term_node(atom)
    {
        return Ok(Owner::String);
    }
    // String routing: a surviving str.< / str.<= order atom (both operands
    // symbolic — the constant-side cases are rewritten away in preprocessing)
    // belongs to the String theory's word-equation engine.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq),
        ..
    } = terms.term_node(atom)
    {
        return Ok(Owner::String);
    }
    // Datatype routing: a tester application, or a (dis)equality over
    // datatype-sorted operands, belongs to the DT theory. EUF still interns the
    // terms for congruence (see the Owner::Datatypes routing in the Combiner).
    if let TermNode::App {
        op: Op::Uninterpreted(sym),
        ..
    } = terms.term_node(atom)
    {
        if matches!(terms.dt_role(*sym), Some(DtRole::Tester { .. })) {
            return Ok(Owner::Datatypes);
        }
    }
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
        args,
        ..
    } = terms.term_node(atom)
    {
        if terms
            .children(*args)
            .iter()
            .any(|&c| terms.is_datatype_sort(terms.sort_of(c)))
        {
            return Ok(Owner::Datatypes);
        }
    }
    // Datatype routing (deep): a constructor/selector/tester application
    // ANYWHERE in the atom, even nested under a non-datatype-sorted top level
    // (e.g. `(distinct (head (cons 1 nil)) 1)`, where `head` returns Int).
    // The two checks above only see datatype-sorted top-level structure, so a
    // selector buried under arithmetic would otherwise fall through to
    // `Owner::Euf`/`Owner::Arith` and DtSolver would never learn about it —
    // silently losing selector-collapse/injectivity/clash for that atom.
    // Mirrors `contains_array_op`'s unconditional deep-walk routing for
    // Arrays; the Combiner's `Owner::Datatypes` arm still notifies EUF too, so
    // congruence over the buried applications is unaffected.
    if contains_dt_op(terms, atom) {
        return Ok(Owner::Datatypes);
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

fn is_string_sorted(terms: &Context, t: TermId) -> bool {
    matches!(terms.sort_node(terms.sort_of(t)), SortNode::String)
}

/// True if `atom` applies an uninterpreted function (arity >= 1) to, or
/// returns, a String-sorted term — out of scope in QF_S core v1.
fn string_under_uf(terms: &Context, atom: TermId) -> bool {
    fn walk(terms: &Context, t: TermId, seen: &mut FxHashSet<TermId>) -> bool {
        if !seen.insert(t) {
            return false;
        }
        if let TermNode::App { op, args, .. } = terms.term_node(t) {
            let kids = terms.children(*args);
            if let Op::Uninterpreted(_) = op {
                if !kids.is_empty()
                    && (is_string_sorted(terms, t)
                        || kids.iter().any(|&k| is_string_sorted(terms, k)))
                {
                    return true;
                }
            }
            kids.iter().any(|&k| walk(terms, k, seen))
        } else {
            false
        }
    }
    let mut seen = FxHashSet::default();
    walk(terms, atom, &mut seen)
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

/// True if any subterm of `t` is a select/store application.
fn contains_array_op(terms: &Context, t: TermId) -> bool {
    match terms.term_node(t) {
        TermNode::App { op, args, .. } => {
            if matches!(op, Op::Builtin(BuiltinOp::Select | BuiltinOp::Store)) {
                return true;
            }
            terms
                .children(*args)
                .iter()
                .any(|&c| contains_array_op(terms, c))
        }
        TermNode::Const { .. } => false,
    }
}

fn is_array_sorted(terms: &Context, t: TermId) -> bool {
    matches!(terms.sort_node(terms.sort_of(t)), SortNode::Array(_, _))
}

/// True if any subterm of `t` is a constructor, selector, or tester
/// application — see the deep-DT-routing comment at its call site.
///
/// The walk is memoized with a `seen` set: on a shared term DAG (nested
/// lists/trees, `let`-shared subtrees) an unguarded recursion is exponential
/// in sharing depth, the exact hazard `DtSolver::collect` (Task 5) and
/// `string_under_uf` guard against. (`contains_array_op` / `array_touches_arith`
/// in this file are NOT guarded — a pre-existing latent issue for QF_A inputs,
/// left untouched here; this function is guarded regardless.)
fn contains_dt_op(terms: &Context, t: TermId) -> bool {
    fn walk(terms: &Context, t: TermId, seen: &mut FxHashSet<TermId>) -> bool {
        if !seen.insert(t) {
            return false;
        }
        match terms.term_node(t) {
            TermNode::App { op, args, .. } => {
                if let Op::Uninterpreted(sym) = op {
                    if matches!(
                        terms.dt_role(*sym),
                        Some(
                            DtRole::Constructor { .. }
                                | DtRole::Selector { .. }
                                | DtRole::Tester { .. }
                        )
                    ) {
                        return true;
                    }
                }
                terms.children(*args).iter().any(|&c| walk(terms, c, seen))
            }
            TermNode::Const { .. } => false,
        }
    }
    let mut seen = FxHashSet::default();
    walk(terms, t, &mut seen)
}

/// True if any select/store subterm touches an arith (Int/Real) index or element
/// sort — that is QF_ALIA, out of scope for this baseline → fence.
fn array_touches_arith(terms: &Context, t: TermId) -> bool {
    let int_s = terms.int_sort();
    let real_s = terms.real_sort();
    fn walk(terms: &Context, t: TermId, int_s: SortId, real_s: SortId) -> bool {
        match terms.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids = terms.children(*args);
                if matches!(op, Op::Builtin(BuiltinOp::Select | BuiltinOp::Store)) {
                    let s = terms.sort_of(t);
                    if s == int_s || s == real_s {
                        return true;
                    }
                    // index sort and element sort of the array operand
                    if let SortNode::Array(idx, elem) = terms.sort_node(terms.sort_of(kids[0])) {
                        if *idx == int_s || *idx == real_s || *elem == int_s || *elem == real_s {
                            return true;
                        }
                    }
                }
                kids.iter().any(|&c| walk(terms, c, int_s, real_s))
            }
            TermNode::Const { .. } => false,
        }
    }
    walk(terms, t, int_s, real_s)
}

/// `Var`-indexed routing table. Append-only across a solve (atoms are never
/// un-registered on backtrack — spec §6.5).
///
/// Carries a reverse `atom → var` map (`by_atom`) so the SAT layer can REUSE the
/// existing SAT var when a theory re-emits an already-registered atom as a split
/// atom. Without this, the two-phase split protocol minted a SECOND, unlinked
/// var for an atom that already had one (the theory then held both the atom and
/// its negation in different vars → spurious UNSAT / non-termination). The first
/// var registered for an atom is authoritative (atoms are append-only).
#[derive(Default)]
pub struct AtomRegistry {
    by_var: Vec<Option<(TermId, Owner)>>,
    by_atom: FxHashMap<TermId, Var>,
}

impl AtomRegistry {
    pub fn register(&mut self, v: Var, atom: TermId, owner: Owner) {
        let idx = v.index();
        if idx >= self.by_var.len() {
            self.by_var.resize(idx + 1, None);
        }
        self.by_var[idx] = Some((atom, owner));
        // First registration wins (atoms are never un-registered). Keep the
        // earliest var so a re-emitted split atom resolves to its original var.
        self.by_atom.entry(atom).or_insert(v);
    }

    /// The SAT var previously registered for `atom`, if any. Used by the SAT
    /// layer's split-atom protocol to reuse an existing var instead of minting a
    /// fresh, unlinked one (the duplicate-var hazard).
    #[inline]
    pub fn var_of_atom(&self, atom: TermId) -> Option<Var> {
        self.by_atom.get(&atom).copied()
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
    use shinri_core::{BuiltinOp, Op, SortId};

    // Build `(<= x y)` over Real and `(= x y)` etc. via a Context.
    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let sym = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    /// Build an uninterpreted 0-arity function (constant) of the given sort.
    fn uconst(ctx: &mut Context, name: &str, sort: SortId) -> TermId {
        let sym = ctx.declare_fun(name, &[], sort);
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
    fn str_order_atoms_route_to_string_owner() {
        let mut terms = Context::new();
        let ss = terms.string_sort();
        let s_sym = terms.declare_fun("s", &[], ss);
        let s = terms.mk_app(Op::Uninterpreted(s_sym), &[]).unwrap();
        let u_sym = terms.declare_fun("u", &[], ss);
        let u = terms.mk_app(Op::Uninterpreted(u_sym), &[]).unwrap();
        let lt = terms
            .mk_app(Op::Builtin(BuiltinOp::StrLt), &[s, u])
            .unwrap();
        let leq = terms
            .mk_app(Op::Builtin(BuiltinOp::StrLeq), &[s, u])
            .unwrap();
        assert_eq!(classify(&terms, lt), Ok(Owner::String));
        assert_eq!(classify(&terms, leq), Ok(Owner::String));
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
    fn classify_array_read_is_arrays() {
        let mut ctx = Context::new();
        let i_s = ctx.declare_sort("I");
        let e_s = ctx.declare_sort("E");
        let arr_s = ctx.array_sort(i_s, e_s);
        let a = uconst(&mut ctx, "a", arr_s);
        let i = uconst(&mut ctx, "i", i_s);
        let e = uconst(&mut ctx, "e", e_s);
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        assert_eq!(classify(&ctx, atom), Ok(Owner::Arrays));
    }

    #[test]
    fn classify_array_equality_is_fenced() {
        let mut ctx = Context::new();
        let i_s = ctx.declare_sort("I");
        let e_s = ctx.declare_sort("E");
        let arr_s = ctx.array_sort(i_s, e_s);
        let a = uconst(&mut ctx, "a", arr_s);
        let b = uconst(&mut ctx, "b", arr_s);
        let atom = ctx.mk_eq(a, b).unwrap();
        assert!(
            classify(&ctx, atom).is_err(),
            "extensionality must be fenced"
        );
    }

    #[test]
    fn classify_string_equality_is_owned_by_string() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");
        let atom = ctx.mk_eq(x, y).unwrap();
        assert!(matches!(classify(&ctx, atom), Ok(Owner::String)));
    }

    #[test]
    fn classify_fences_string_under_uninterpreted_function() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let f = ctx.declare_fun("f", &[str_s], str_s); // f : String -> String
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let atom = ctx.mk_eq(fx, x).unwrap();
        assert!(
            classify(&ctx, atom).is_err(),
            "string under a UF is out of scope in v1"
        );
    }

    #[test]
    fn datatype_equality_and_tester_route_to_datatypes() {
        let mut ctx = Context::new();
        let list = ctx.declare_datatype_sort("List");
        let b = ctx.bool_sort();
        let nil = ctx.declare_fun("nil", &[], list);
        let is_nil = ctx.declare_fun("is-nil", &[list], b);
        ctx.dt_add_constructor(list, nil, &[], is_nil);
        let xs = ctx.declare_fun("x", &[], list);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();

        let eq_atom = ctx.mk_eq(x, nil_t).unwrap();
        assert_eq!(classify(&ctx, eq_atom), Ok(Owner::Datatypes));

        let tester = ctx.mk_app(Op::Uninterpreted(is_nil), &[x]).unwrap();
        assert_eq!(classify(&ctx, tester), Ok(Owner::Datatypes));
    }

    #[test]
    fn pure_int_arith_is_admitted_to_owner_arith() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xi = ctx.declare_fun("xi", &[], int);
        let yi = ctx.declare_fun("yi", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yi), &[]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
        assert_eq!(classify(&ctx, le), Ok(Owner::Arith));
        // Real still arith.
        let real = ctx.real_sort();
        let xr = ctx.declare_fun("xr", &[], real);
        let yr = ctx.declare_fun("yr", &[], real);
        let xrt = ctx.mk_app(Op::Uninterpreted(xr), &[]).unwrap();
        let yrt = ctx.mk_app(Op::Uninterpreted(yr), &[]).unwrap();
        let ler = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xrt, yrt]).unwrap();
        assert_eq!(classify(&ctx, ler), Ok(Owner::Arith));
    }
}
