use shinri_core::{Lit, Var};

/// A parsed CNF formula.
pub struct Cnf {
    pub num_vars: usize,
    pub clauses: Vec<Vec<Lit>>,
}

/// Parse DIMACS CNF. Returns `Err(msg)` on malformed input — never panics
/// (spec §9). Variables are 1-based in DIMACS, 0-based as `Var`.
pub fn parse_dimacs(src: &str) -> Result<Cnf, String> {
    let mut num_vars = 0usize;
    let mut clauses = Vec::new();
    let mut cur: Vec<Lit> = Vec::new();
    let mut saw_header = false;

    for line in src.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("p cnf") {
            let mut it = rest.split_whitespace();
            num_vars = it
                .next()
                .ok_or("missing var count")?
                .parse()
                .map_err(|_| "bad var count")?;
            saw_header = true;
            continue;
        }
        for tok in line.split_whitespace() {
            let n: i64 = tok.parse().map_err(|_| format!("bad literal {tok}"))?;
            if n == 0 {
                clauses.push(std::mem::take(&mut cur));
            } else {
                let var0 = n.unsigned_abs() - 1;
                if var0 as usize >= num_vars {
                    return Err(format!("variable {} out of range", n.abs()));
                }
                cur.push(Lit::new(Var::new(var0 as u32), n > 0));
            }
        }
    }
    if !saw_header {
        return Err("missing p cnf header".into());
    }
    if !cur.is_empty() {
        clauses.push(cur);
    }
    Ok(Cnf { num_vars, clauses })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_comments_header_and_clauses() {
        let src = "c example\np cnf 3 2\n1 -2 0\n2 3 0\n";
        let cnf = parse_dimacs(src).unwrap();
        assert_eq!(cnf.num_vars, 3);
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.clauses[0], vec![Lit::new(Var::new(0), true), Lit::new(Var::new(1), false)]);
        assert_eq!(cnf.clauses[1], vec![Lit::new(Var::new(1), true), Lit::new(Var::new(2), true)]);
    }

    #[test]
    fn rejects_var_out_of_range() {
        let src = "p cnf 1 1\n2 0\n";
        assert!(parse_dimacs(src).is_err());
    }
}
