//! Verdict classification: turn an observed solver run (exit code, parsed
//! answers, stderr, `:status`, oracle answers) into a `Verdict` per the
//! precedence rules in the slice 46 spec §5.

/// A decided or undecided SMT-LIB answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Answer {
    Sat,
    Unsat,
    Unknown,
    Timeout,
}

impl Answer {
    pub fn parse(s: &str) -> Option<Answer> {
        match s {
            "sat" => Some(Answer::Sat),
            "unsat" => Some(Answer::Unsat),
            "unknown" => Some(Answer::Unknown),
            "timeout" => Some(Answer::Timeout),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Answer::Sat => "sat",
            Answer::Unsat => "unsat",
            Answer::Unknown => "unknown",
            Answer::Timeout => "timeout",
        }
    }
}

/// The two reference-oracle answers, when the runner consulted them.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct OracleAnswers {
    pub z3: Option<Answer>,
    pub cvc5: Option<Answer>,
}

/// The classification of one benchmark run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    Correct,
    Wrong,
    StatusSuspect,
    ParseError,
    Panic,
    Oom,
    Timeout,
    Unknown(String),
    Unverified,
    Malformed(String),
    /// Not final: the runner must consult the oracle and classify again.
    NeedsOracle,
}

impl Verdict {
    pub fn key(&self) -> String {
        match self {
            Verdict::Correct => "correct".to_string(),
            Verdict::Wrong => "wrong".to_string(),
            Verdict::StatusSuspect => "status-suspect".to_string(),
            Verdict::ParseError => "parse-error".to_string(),
            Verdict::Panic => "panic".to_string(),
            Verdict::Oom => "oom".to_string(),
            Verdict::Timeout => "timeout".to_string(),
            Verdict::Unknown(tag) => format!("unknown:{tag}"),
            Verdict::Unverified => "unverified".to_string(),
            Verdict::Malformed(reason) => format!("malformed:{reason}"),
            Verdict::NeedsOracle => "needs-oracle".to_string(),
        }
    }

    pub fn parse(key: &str) -> Verdict {
        if let Some(tag) = key.strip_prefix("unknown:") {
            return Verdict::Unknown(tag.to_string());
        }
        if let Some(reason) = key.strip_prefix("malformed:") {
            return Verdict::Malformed(reason.to_string());
        }
        match key {
            "correct" => Verdict::Correct,
            "wrong" => Verdict::Wrong,
            "status-suspect" => Verdict::StatusSuspect,
            "parse-error" => Verdict::ParseError,
            "panic" => Verdict::Panic,
            "oom" => Verdict::Oom,
            "timeout" => Verdict::Timeout,
            "unverified" => Verdict::Unverified,
            "needs-oracle" => Verdict::NeedsOracle,
            other => Verdict::Malformed(format!("unrecognized-key:{other}")),
        }
    }
}

/// What the runner observed about one solver invocation.
pub struct Observed<'a> {
    pub rc: Option<i32>,
    /// process.rs sets this from rc 124/137 + elapsed.
    pub killed_by_timeout: bool,
    /// stdout sat/unsat/unknown lines, in order.
    pub answers: &'a [Answer],
    pub stderr: &'a str,
    pub fence: Option<&'a str>,
    /// `:status`; `None` = absent.
    pub status: Option<Answer>,
    pub oracle: Option<&'a OracleAnswers>,
    /// Count of `(error` lines on stdout seen before the first answer.
    pub stdout_errors: usize,
}

pub fn classify(o: &Observed) -> Verdict {
    // 1. Timeout.
    if o.killed_by_timeout {
        return Verdict::Timeout;
    }
    // 2. Panic.
    if o.rc == Some(101) || o.stderr.contains("panicked at") {
        return Verdict::Panic;
    }
    // 3. Oom.
    if (o.stderr.contains("memory allocation of") && o.stderr.contains("failed"))
        || o.rc == Some(134)
        || o.rc.is_none()
    {
        return Verdict::Oom;
    }
    // 4. ParseError.
    if (o.stdout_errors > 0 && o.answers.is_empty()) || o.rc == Some(2) {
        return Verdict::ParseError;
    }
    // 5. Malformed answer count.
    if o.answers.len() != 1 {
        return Verdict::Malformed(format!("answers={}", o.answers.len()));
    }
    let a = o.answers[0];
    // 6. Unknown answer.
    if a == Answer::Unknown {
        return Verdict::Unknown(o.fence.unwrap_or("-").to_string());
    }
    // 7. Decided answer.
    match o.status {
        None | Some(Answer::Unknown) => classify_decided_no_status(a, o.oracle),
        Some(s) if s == a => Verdict::Correct,
        Some(_) => classify_decided_status_contradiction(a, o.oracle),
    }
}

fn classify_decided_no_status(a: Answer, oracle: Option<&OracleAnswers>) -> Verdict {
    let Some(oracle) = oracle else {
        return Verdict::NeedsOracle;
    };
    match oracle.z3 {
        Some(z) if z == a => Verdict::Correct,
        Some(Answer::Unknown) | Some(Answer::Timeout) => Verdict::Unverified,
        Some(_) => Verdict::Wrong,
        None => Verdict::NeedsOracle,
    }
}

fn classify_decided_status_contradiction(a: Answer, oracle: Option<&OracleAnswers>) -> Verdict {
    let Some(oracle) = oracle else {
        return Verdict::NeedsOracle;
    };
    match oracle.z3 {
        None => Verdict::NeedsOracle,
        Some(Answer::Unknown) | Some(Answer::Timeout) => Verdict::Wrong,
        Some(z) if z != a => Verdict::Wrong,
        Some(_) => match oracle.cvc5 {
            None => Verdict::NeedsOracle,
            Some(c) if c == a => Verdict::StatusSuspect,
            Some(_) => Verdict::Wrong,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Answer::*;

    fn obs<'a>(
        rc: Option<i32>,
        answers: &'a [Answer],
        stderr: &'a str,
        status: Option<Answer>,
    ) -> Observed<'a> {
        Observed {
            rc,
            killed_by_timeout: false,
            answers,
            stderr,
            fence: None,
            status,
            oracle: None,
            stdout_errors: 0,
        }
    }

    #[test]
    fn correct_matches_status() {
        assert_eq!(
            classify(&obs(Some(0), &[Unsat], "", Some(Unsat))),
            Verdict::Correct
        );
    }
    #[test]
    fn decided_without_status_needs_oracle() {
        assert_eq!(
            classify(&obs(Some(0), &[Sat], "", None)),
            Verdict::NeedsOracle
        );
        assert_eq!(
            classify(&obs(Some(0), &[Sat], "", Some(Unknown))),
            Verdict::NeedsOracle
        );
    }
    #[test]
    fn oracle_agreement_is_correct() {
        let o = OracleAnswers {
            z3: Some(Sat),
            cvc5: None,
        };
        let mut ob = obs(Some(0), &[Sat], "", None);
        ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Correct);
    }
    #[test]
    fn oracle_disagreement_without_status_is_wrong() {
        let o = OracleAnswers {
            z3: Some(Unsat),
            cvc5: None,
        };
        let mut ob = obs(Some(0), &[Sat], "", None);
        ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Wrong);
    }
    #[test]
    fn oracle_unknown_or_timeout_is_unverified() {
        for z in [Unknown, Timeout] {
            let o = OracleAnswers {
                z3: Some(z),
                cvc5: Some(Timeout),
            };
            let mut ob = obs(Some(0), &[Sat], "", None);
            ob.oracle = Some(&o);
            assert_eq!(classify(&ob), Verdict::Unverified);
        }
    }
    #[test]
    fn contradicting_status_needs_oracle_first() {
        assert_eq!(
            classify(&obs(Some(0), &[Sat], "", Some(Unsat))),
            Verdict::NeedsOracle
        );
    }
    #[test]
    fn contradicting_status_with_oracle_on_status_side_is_wrong() {
        let o = OracleAnswers {
            z3: Some(Unsat),
            cvc5: None,
        };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat));
        ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Wrong);
    }
    #[test]
    fn contradicting_status_z3_agrees_needs_cvc5() {
        let o = OracleAnswers {
            z3: Some(Sat),
            cvc5: None,
        };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat));
        ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::NeedsOracle);
    }
    #[test]
    fn both_oracles_agree_with_shinri_is_status_suspect() {
        let o = OracleAnswers {
            z3: Some(Sat),
            cvc5: Some(Sat),
        };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat));
        ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::StatusSuspect);
    }
    #[test]
    fn cvc5_sides_with_status_is_wrong() {
        let o = OracleAnswers {
            z3: Some(Sat),
            cvc5: Some(Unsat),
        };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat));
        ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Wrong);
    }
    #[test]
    fn oracle_timeout_on_contradiction_is_still_wrong() {
        // :status is an independent claim; an oracle that cannot decide does
        // not rescue a contradiction of it.
        let o = OracleAnswers {
            z3: Some(Timeout),
            cvc5: Some(Unknown),
        };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat));
        ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Wrong);
    }
    #[test]
    fn unknown_answer_keys_on_fence() {
        let mut ob = obs(Some(0), &[Unknown], "", Some(Sat));
        ob.fence = Some("str-order");
        assert_eq!(classify(&ob), Verdict::Unknown("str-order".into()));
        let ob2 = obs(Some(0), &[Unknown], "", Some(Sat));
        assert_eq!(classify(&ob2), Verdict::Unknown("-".into()));
    }
    #[test]
    fn error_before_answer_is_parse_error() {
        let mut ob = obs(Some(0), &[], "", None);
        ob.stdout_errors = 1;
        assert_eq!(classify(&ob), Verdict::ParseError);
    }
    #[test]
    fn panic_is_panic() {
        assert_eq!(
            classify(&obs(
                Some(101),
                &[],
                "thread 'main' panicked at ...",
                Some(Sat)
            )),
            Verdict::Panic
        );
    }
    #[test]
    fn allocation_failure_is_oom() {
        assert_eq!(
            classify(&obs(
                Some(134),
                &[],
                "memory allocation of 4294967296 bytes failed",
                None
            )),
            Verdict::Oom
        );
        assert_eq!(classify(&obs(None, &[], "", None)), Verdict::Oom); // SIGKILL before the limit
    }
    #[test]
    fn timeout_is_timeout() {
        let mut ob = obs(Some(124), &[], "", Some(Sat));
        ob.killed_by_timeout = true;
        assert_eq!(classify(&ob), Verdict::Timeout);
        let mut ob2 = obs(None, &[], "", None);
        ob2.killed_by_timeout = true;
        assert_eq!(classify(&ob2), Verdict::Timeout);
    }
    #[test]
    fn two_answers_is_malformed() {
        assert!(matches!(
            classify(&obs(Some(0), &[Sat, Sat], "", Some(Sat))),
            Verdict::Malformed(_)
        ));
    }
    #[test]
    fn no_answer_clean_exit_is_malformed() {
        assert!(matches!(
            classify(&obs(Some(0), &[], "", Some(Sat))),
            Verdict::Malformed(_)
        ));
    }
    #[test]
    fn keys_round_trip() {
        for v in [
            Verdict::Correct,
            Verdict::Wrong,
            Verdict::StatusSuspect,
            Verdict::ParseError,
            Verdict::Panic,
            Verdict::Oom,
            Verdict::Timeout,
            Verdict::Unknown("x-y".into()),
            Verdict::Unverified,
            Verdict::Malformed("spawn".into()),
            Verdict::NeedsOracle,
        ] {
            assert_eq!(Verdict::parse(&v.key()), v);
        }
    }
}
