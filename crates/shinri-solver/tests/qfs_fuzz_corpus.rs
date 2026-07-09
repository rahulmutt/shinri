//! Enumeration fuzzer for the QF_S word-equation / predicate / length fragment
//! (Task E1). Differential vs z3, with delta-debug MINIMIZATION and shape DEDUP,
//! so it enumerates the *class* of soundness bugs, not a single repro.
//!
//! Run:
//!   cargo test -p shinri-solver --features oracle --test qfs_fuzz_corpus \
//!       -- --nocapture --ignored e1_enumerate_wrong_verdicts
//!
//! Requires `z3` on PATH. It is `#[ignore]`d so a normal `cargo test` run does
//! not spend minutes on it; invoke explicitly with `--ignored`.
//!
//! ## What it does
//! For each of `N_ITERS` random instances (declarations + a small assertion
//! list drawn from the fragment: var/concat/literal word (dis)equations,
//! `str.len` atoms over vars AND concats, positive prefixof/suffixof/contains,
//! self-referential equations, and small `(or ...)` combinations):
//!   1. classify the shinri-vs-z3 outcome as WRONG-SAT / WRONG-UNSAT / BAD-MODEL
//!      (shinri Sat but its model fails in z3) / tolerated (either side Unknown);
//!   2. delta-debug MINIMIZE each disagreement (drop assertions while the same
//!      disagreement class persists) to a small repro;
//!   3. DEDUP minimized repros by a canonical shape (vars renamed in order of
//!      appearance, literals collapsed to a length-tag) so the printed corpus is
//!      one entry per distinct mechanism.
//! The printed corpus — counts by class + the minimized shapes — is the artifact.
//!
//! ## WARNING
//! This harness runs the solver with no built-in memory bound; a single
//! pathological solve can allocate many GiB. It self-caps its address space
//! via `RLIMIT_AS` (default 20 GiB, override with `E1_MEM_GIB`) so a runaway
//! aborts the test process rather than OOM-killing the container.

#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};
use std::collections::BTreeSet;

/// Bound THIS test process's virtual address space so a single pathological
/// solve aborts the process (allocation failure) instead of OOM-killing the
/// whole container. Child z3 processes inherit the limit too. Default 20 GiB;
/// override with `E1_MEM_GIB`. No-op off Unix.
#[cfg(unix)]
fn cap_address_space() {
    let gib: u64 = std::env::var("E1_MEM_GIB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20);
    let bytes = gib.saturating_mul(1024 * 1024 * 1024);
    let lim = libc::rlimit {
        rlim_cur: bytes as libc::rlim_t,
        rlim_max: bytes as libc::rlim_t,
    };
    // SAFETY: RLIMIT_AS is a valid resource; `&lim` is a valid rlimit pointer.
    // Lowering only the soft limit within the inherited hard limit always
    // succeeds; ignore the (unreachable) error path.
    unsafe {
        libc::setrlimit(libc::RLIMIT_AS, &lim);
    }
}
#[cfg(not(unix))]
fn cap_address_space() {}

// ── Deterministic PRNG ───────────────────────────────────────────────────────
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0 >> 16
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const N_VARS: usize = 3;
const ALPHABET: &[&str] = &["a", "b", "c"];

// ── Verdict ──────────────────────────────────────────────────────────────────
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Class {
    WrongSat,
    WrongUnsat,
    BadModel,
}

// ── shinri / z3 drivers ──────────────────────────────────────────────────────

/// Full script → response lines (verdict, model, …), tolerating guard bailouts.
fn shinri_lines(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

fn shinri_verdict(src: &str) -> Verdict {
    match shinri_lines(src).first().map(String::as_str) {
        Some("sat") => Verdict::Sat,
        Some("unsat") => Verdict::Unsat,
        _ => Verdict::Unknown,
    }
}

fn z3_run(script: &str) -> String {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new("z3")
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("z3 not on PATH");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(script.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn z3_verdict(script: &str) -> Verdict {
    match z3_run(script)
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("unknown")
    {
        "sat" => Verdict::Sat,
        "unsat" => Verdict::Unsat,
        _ => Verdict::Unknown,
    }
}

// ── Instance = declarations + assertion list ─────────────────────────────────
// Assertions are SMT-LIB strings over a fixed var pool, so minimization is
// simply dropping elements of the list.
#[derive(Clone)]
struct Instance {
    assertions: Vec<String>,
}

impl Instance {
    fn decls() -> String {
        let mut s = String::from("(set-logic QF_S)\n");
        for k in 0..N_VARS {
            s.push_str(&format!("(declare-fun s{k} () String)\n"));
        }
        s
    }
    fn body(&self) -> String {
        let mut s = Self::decls();
        for a in &self.assertions {
            s.push_str(&format!("(assert {a})\n"));
        }
        s
    }
    fn check_script(&self) -> String {
        format!("{}(check-sat)\n", self.body())
    }
}

// ── Generator ────────────────────────────────────────────────────────────────
struct Gen {
    rng: Lcg,
}
impl Gen {
    fn var(&mut self) -> String {
        format!("s{}", self.rng.below(N_VARS as u64))
    }
    fn lit(&mut self) -> String {
        let n = 1 + self.rng.below(2);
        let mut s = String::new();
        for _ in 0..n {
            s.push_str(ALPHABET[self.rng.below(ALPHABET.len() as u64) as usize]);
        }
        format!("\"{s}\"")
    }
    fn atom_term(&mut self) -> String {
        if self.rng.below(2) == 0 {
            self.var()
        } else {
            self.lit()
        }
    }
    fn concat(&mut self) -> String {
        let n = 2 + self.rng.below(2);
        let parts: Vec<String> = (0..n).map(|_| self.atom_term()).collect();
        format!("(str.++ {})", parts.join(" "))
    }
    fn word_term(&mut self) -> String {
        match self.rng.below(3) {
            0 => self.var(),
            1 => self.lit(),
            _ => self.concat(),
        }
    }
    fn len_arg(&mut self) -> String {
        if self.rng.below(2) == 0 {
            self.var()
        } else {
            self.concat()
        }
    }
    fn predicate(&mut self) -> String {
        let needle = self.atom_term();
        let hay = if self.rng.below(2) == 0 {
            self.var()
        } else {
            self.concat()
        };
        match self.rng.below(3) {
            0 => format!("(str.prefixof {needle} {hay})"),
            1 => format!("(str.suffixof {needle} {hay})"),
            _ => format!("(str.contains {hay} {needle})"),
        }
    }
    fn self_ref(&mut self) -> String {
        let x = self.var();
        let pre = self.atom_term();
        if self.rng.below(2) == 0 {
            let post = self.atom_term();
            format!("(= {x} (str.++ {pre} {x} {post}))")
        } else {
            format!("(= {x} (str.++ {pre} {x}))")
        }
    }
    /// One assertion drawn from the whole fragment. Positive predicates only
    /// (negative/mixed fence to Unknown by design, so are non-disagreements).
    fn assertion(&mut self) -> String {
        match self.rng.below(8) {
            0 => format!("(= {} {})", self.word_term(), self.word_term()),
            1 => format!("(distinct {} {})", self.word_term(), self.word_term()),
            2 => {
                let k = self.rng.below(4);
                let op = ["=", "<=", ">=", "<"][self.rng.below(4) as usize];
                format!("({op} (str.len {}) {k})", self.len_arg())
            }
            3 => {
                let op = ["=", "<=", ">="][self.rng.below(3) as usize];
                format!("({op} (str.len {}) (str.len {}))", self.len_arg(), self.len_arg())
            }
            4 | 5 => self.predicate(),
            6 => self.self_ref(),
            // small positive Boolean combination of two word (dis)equations
            _ => {
                let a = format!("(= {} {})", self.word_term(), self.word_term());
                let b = format!("(= {} {})", self.word_term(), self.word_term());
                if self.rng.below(2) == 0 {
                    format!("(or {a} {b})")
                } else {
                    format!("(and {a} {b})")
                }
            }
        }
    }
    fn instance(&mut self) -> Instance {
        let n = 2 + self.rng.below(3); // 2..=4 assertions
        Instance {
            assertions: (0..n).map(|_| self.assertion()).collect(),
        }
    }
}

// ── Classification + witness ─────────────────────────────────────────────────

fn parse_string_values(resp: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let bytes: Vec<char> = resp.chars().collect();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == '(' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_alphabetic() {
            let mut j = i + 1;
            let mut name = String::new();
            while j < bytes.len() && !bytes[j].is_whitespace() && bytes[j] != '(' && bytes[j] != ')' {
                name.push(bytes[j]);
                j += 1;
            }
            while j < bytes.len() && bytes[j].is_whitespace() {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == '"' {
                j += 1;
                let mut val = String::new();
                while j < bytes.len() {
                    if bytes[j] == '"' {
                        if j + 1 < bytes.len() && bytes[j + 1] == '"' {
                            val.push('"');
                            j += 2;
                            continue;
                        }
                        j += 1;
                        break;
                    }
                    val.push(bytes[j]);
                    j += 1;
                }
                let userlevel = !name.starts_with('!') && !name.starts_with('@');
                if userlevel {
                    out.push((name, val));
                }
            }
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

fn smt_escape(s: &str) -> String {
    format!("\"{}\"", s.replace('"', "\"\""))
}

/// Classify one instance. Returns `Some(class)` for a genuine disagreement.
fn classify(inst: &Instance) -> Option<Class> {
    let ours = shinri_verdict(&inst.check_script());
    if ours == Verdict::Unknown {
        return None; // sound incompleteness
    }
    let theirs = z3_verdict(&inst.check_script());
    if theirs == Verdict::Unknown {
        return None;
    }
    if ours != theirs {
        return Some(if ours == Verdict::Sat {
            Class::WrongSat
        } else {
            Class::WrongUnsat
        });
    }
    // Agree. If SAT, witness-check shinri's model against z3.
    if ours == Verdict::Sat {
        let get = format!(
            "{}(check-sat)\n(get-value ({}))\n",
            inst.body(),
            (0..N_VARS).map(|k| format!("s{k}")).collect::<Vec<_>>().join(" ")
        );
        let lines = shinri_lines(&get);
        if let Some(resp) = lines.get(1) {
            let model = parse_string_values(resp);
            if !model.is_empty() {
                let mut script = inst.body();
                for (name, val) in &model {
                    script.push_str(&format!("(assert (= {name} {}))\n", smt_escape(val)));
                }
                script.push_str("(check-sat)\n");
                if z3_verdict(&script) == Verdict::Unsat {
                    return Some(Class::BadModel);
                }
            }
        }
    }
    None
}

// ── Delta-debug minimization ─────────────────────────────────────────────────
/// Shrink the assertion list while the SAME disagreement class persists.
fn minimize(inst: &Instance, class: Class) -> Instance {
    let mut cur = inst.clone();
    let mut changed = true;
    while changed {
        changed = false;
        // try dropping each assertion
        let mut i = 0;
        while i < cur.assertions.len() {
            if cur.assertions.len() == 1 {
                break;
            }
            let mut cand = cur.clone();
            cand.assertions.remove(i);
            if classify(&cand) == Some(class) {
                cur = cand;
                changed = true;
            } else {
                i += 1;
            }
        }
    }
    cur
}

// ── Shape canonicalization for dedup ─────────────────────────────────────────
/// Canonical shape: rename user vars s0.. and internal skolems in order of
/// appearance to v0,v1,…, and collapse each string literal to `L<len>`. Groups
/// repros that share a mechanism regardless of which variables/letters appear.
fn shape(inst: &Instance) -> String {
    let joined = inst.assertions.join(" ; ");
    let mut out = String::new();
    let mut chars = joined.chars().peekable();
    let mut rename: Vec<(String, String)> = Vec::new();
    while let Some(c) = chars.next() {
        if c == '"' {
            // literal: consume to closing quote, emit L<len>
            let mut n = 0usize;
            while let Some(&d) = chars.peek() {
                chars.next();
                if d == '"' {
                    break;
                }
                n += 1;
            }
            out.push_str(&format!("L{n}"));
        } else if c == 's' && chars.peek().map(|d| d.is_ascii_digit()).unwrap_or(false) {
            let mut name = String::from("s");
            while let Some(&d) = chars.peek() {
                if d.is_ascii_digit() {
                    name.push(d);
                    chars.next();
                } else {
                    break;
                }
            }
            let canon = match rename.iter().find(|(k, _)| *k == name) {
                Some((_, v)) => v.clone(),
                None => {
                    let v = format!("v{}", rename.len());
                    rename.push((name, v.clone()));
                    v
                }
            };
            out.push_str(&canon);
        } else {
            out.push(c);
        }
    }
    out
}

// ── Main enumeration ─────────────────────────────────────────────────────────
#[test]
#[ignore = "long differential fuzz; run explicitly with --ignored"]
fn e1_enumerate_wrong_verdicts() {
    cap_address_space();
    let n_iters: usize = std::env::var("E1_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4000);
    let seed: u64 = std::env::var("E1_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0xE1_0000_0001);
    let mut rng = Lcg(seed);

    let (mut n_ws, mut n_wu, mut n_bm) = (0usize, 0usize, 0usize);
    // shape -> (class, minimized body, first-seen raw body)
    let mut corpus: std::collections::BTreeMap<String, (Class, String)> =
        std::collections::BTreeMap::new();
    let mut seen_shapes: BTreeSet<String> = BTreeSet::new();

    for it in 0..n_iters {
        let inst = Gen { rng: Lcg(rng.next()) }.instance();
        if let Some(class) = classify(&inst) {
            let mini = minimize(&inst, class);
            let sh = shape(&mini);
            match class {
                Class::WrongSat => n_ws += 1,
                Class::WrongUnsat => n_wu += 1,
                Class::BadModel => n_bm += 1,
            }
            if seen_shapes.insert(sh.clone()) {
                corpus.insert(sh.clone(), (class, mini.body()));
                eprintln!(
                    "[E1 corpus] iter={it} NEW {:?} shape={sh}\n----\n{}----",
                    class,
                    mini.body()
                );
            }
        }
    }

    eprintln!(
        "\n==== E1 CORPUS SUMMARY ====\n\
         iters={n_iters} seed={seed:#x}\n\
         raw disagreements: wrong-sat={n_ws} wrong-unsat={n_wu} bad-model={n_bm}\n\
         distinct minimized shapes: {}\n",
        corpus.len()
    );
    let (mut cs, mut cu, mut cb) = (0, 0, 0);
    for (sh, (class, _)) in &corpus {
        match class {
            Class::WrongSat => cs += 1,
            Class::WrongUnsat => cu += 1,
            Class::BadModel => cb += 1,
        }
        eprintln!("  {:?}  {sh}", class);
    }
    eprintln!(
        "distinct-by-class: wrong-sat={cs} wrong-unsat={cu} bad-model={cb}\n\
         (corpus empty = engine sound over this fragment/sample)"
    );
}
