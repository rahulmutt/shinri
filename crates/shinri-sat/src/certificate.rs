use shinri_core::Lit;

/// Reverse Unit Propagation: `candidate` is RUP w.r.t. `clauses` iff assuming
/// every literal of `candidate` false and unit-propagating yields a conflict.
fn rup(clauses: &[Vec<Lit>], candidate: &[Lit], num_vars: usize) -> bool {
    let mut val: Vec<Option<bool>> = vec![None; num_vars];
    for &l in candidate {
        let v = l.var().index();
        let b = !l.is_positive(); // assign so that `l` is false
        if val[v] == Some(!b) {
            return true; // contradictory assumptions => trivially conflicting
        }
        val[v] = Some(b);
    }
    loop {
        let mut changed = false;
        for cl in clauses {
            let mut sat = false;
            let mut unassigned: Option<Lit> = None;
            let mut count = 0;
            for &l in cl {
                let v = l.var().index();
                match val[v] {
                    Some(b) => {
                        if b == l.is_positive() {
                            sat = true;
                            break;
                        }
                    }
                    None => {
                        count += 1;
                        unassigned = Some(l);
                    }
                }
            }
            if sat {
                continue;
            }
            if count == 0 {
                return true; // conflict
            }
            if count == 1 {
                let l = unassigned.unwrap();
                val[l.var().index()] = Some(l.is_positive());
                changed = true;
            }
        }
        if !changed {
            return false;
        }
    }
}

/// Check a DRAT-style proof: each added clause must be RUP w.r.t. the clauses
/// so far, and the final clause set must propagate to a conflict (empty-clause
/// RUP). Sound for the RUP-only proofs a CDCL solver emits.
pub fn check_drat(num_vars: usize, original: &[Vec<Lit>], proof: &[Vec<Lit>]) -> bool {
    let mut clauses = original.to_vec();
    for c in proof {
        if !rup(&clauses, c, num_vars) {
            return false;
        }
        clauses.push(c.clone());
    }
    rup(&clauses, &[], num_vars)
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Lit, Var};

    fn cl(spec: &[(u32, bool)]) -> Vec<Lit> {
        spec.iter()
            .map(|&(n, p)| Lit::new(Var::new(n), p))
            .collect()
    }

    #[test]
    fn rup_certifies_simple_unsat() {
        // (x0) ∧ (¬x0) is UNSAT with an empty proof (RUP of the empty clause).
        let original = vec![cl(&[(0, true)]), cl(&[(0, false)])];
        assert!(check_drat(1, &original, &[]));
    }

    #[test]
    fn rup_rejects_unsound_addition() {
        // Adding (x0) to just (x0 ∨ x1) is NOT RUP -> checker must reject.
        let original = vec![cl(&[(0, true), (1, true)])];
        let bad_proof = vec![cl(&[(0, true)])];
        assert!(!check_drat(2, &original, &bad_proof));
    }
}
